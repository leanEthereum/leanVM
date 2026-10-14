//! WHIR opening.

use crate::field::{E, K, ONE, ZERO, powers};
use crate::hash::Digest;
use crate::layout::{MAX_STACKED_LOG, MIN_STACKED_LOG};
use crate::multilinear::{dot, eq_eval, eq_kernel, log2_strict, multilinear_eval, poly_eval};
use crate::transcript::Transcript;
use crate::{VerifierError, require};

const INITIAL_FOLDING_FACTOR: usize = 6;
const SUBSEQUENT_FOLDING_FACTOR: usize = 4;
const RS_DOMAIN_INITIAL_REDUCTION_FACTOR: usize = 3;
const RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR: usize = 1;
const RESIDUAL_MAX_LOG: usize = 5;
const QUERY_GRINDING_BITS: u32 = 17;

#[rustfmt::skip]
const WHIR_QUERIES: [[&[usize]; 14]; 4] = [
    [&[222,55], &[223,56,30], &[223,56,31], &[223,56,32], &[223,56,32], &[223,56,32,22], &[223,56,32,22], &[224,56,32,23], &[224,56,32,23], &[224,56,32,23,17], &[224,56,32,23,17], &[224,56,32,23,18], &[225,56,32,23,18], &[225,56,32,23,18,14]],
    [&[111,45], &[112,45,27], &[112,45,28], &[112,45,28], &[112,45,28], &[112,45,28,20], &[112,45,28,20], &[112,45,28,21], &[112,45,28,21], &[112,45,28,21,16], &[112,45,28,21,16], &[112,45,28,21,16], &[112,45,28,21,16], &[112,45,28,21,16,13]],
    [&[75,37], &[75,37,24], &[75,37,25], &[75,38,25], &[75,38,25], &[75,38,25,18], &[75,38,25,19], &[75,38,25,19], &[75,38,25,19], &[75,38,25,19,15], &[75,38,25,19,15], &[75,38,25,19,15], &[75,38,25,19,15], &[75,38,25,19,15,13]],
    [&[56,32], &[56,32,22], &[56,32,22], &[56,32,23], &[56,32,23], &[56,32,23,17], &[56,32,23,17], &[56,32,23,18], &[56,32,23,18], &[56,32,23,18,14], &[56,32,23,18,14], &[56,32,23,18,14], &[56,32,23,18,15], &[56,32,23,18,15,12]],
];

struct WhirConfig {
    log_inv_rates: Vec<usize>,
    folds: Vec<usize>,
    queries: &'static [usize],
}

/// The opening shape at this size and rate: the ladder geometry, then the tabulated query counts.
fn derive_config(log_n: usize, log_inv_rate: usize) -> Result<WhirConfig, VerifierError> {
    require(
        (MIN_STACKED_LOG..=MAX_STACKED_LOG).contains(&log_n) && (1..=4).contains(&log_inv_rate),
        VerifierError::WhirShape,
    )?;
    let mut folds = vec![INITIAL_FOLDING_FACTOR];
    let mut log_inv_rates = vec![log_inv_rate];
    let mut remaining = log_n - INITIAL_FOLDING_FACTOR;
    while remaining > RESIDUAL_MAX_LOG {
        let reduction = if folds.len() == 1 {
            RS_DOMAIN_INITIAL_REDUCTION_FACTOR
        } else {
            RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR
        };
        log_inv_rates.push(log_inv_rates[log_inv_rates.len() - 1] + folds[folds.len() - 1] - reduction);
        let fold = SUBSEQUENT_FOLDING_FACTOR.min(remaining);
        remaining -= fold;
        folds.push(fold);
    }
    let queries = WHIR_QUERIES[log_inv_rate - 1][log_n - MIN_STACKED_LOG];
    require(queries.len() == folds.len(), VerifierError::QueryCountLadder)?;
    Ok(WhirConfig {
        log_inv_rates,
        folds,
        queries,
    })
}

/// Regroup a level's leaf words into the E values they encode, three per lane.
fn ext_row(words: &[K]) -> Vec<E> {
    words
        .as_chunks()
        .0
        .iter()
        .map(|&[c0, c1, c2]| E::new(c0.0, c1.0, c2.0))
        .collect()
}

fn sample_queries(transcript: &mut Transcript, block_length: u64, count: usize) -> Result<Vec<u64>, VerifierError> {
    let depth = log2_strict(block_length)?;
    let per_word = 192 / depth;
    let mut result = Vec::with_capacity(count);
    while result.len() < count {
        let sample = transcript.sample();
        let bits = [sample.c0, sample.c1, sample.c2, 0];
        for chunk in 0..per_word.min(count - result.len()) {
            // The `depth` bits at `chunk * depth` of the 192-bit integer, which may straddle two limbs.
            let (limb, shift) = (chunk * depth / 64, chunk * depth % 64);
            let window = (bits[limb] as u128 | (bits[limb + 1] as u128) << 64) >> shift;
            result.push(window as u64 & (block_length - 1));
        }
    }
    Ok(result)
}

/// The subspace polynomials' normalizers. The subspaces are spanned by powers of x, so every one lies in K.
fn subspace_roots(log_n: usize) -> Vec<K> {
    let mut roots = vec![K(1)];
    let mut layer: Vec<K> = (1..=log_n).map(|i| K(1 << i)).collect();
    for _ in 0..log_n {
        let root = roots[roots.len() - 1];
        for value in &mut layer {
            *value = value.square() + root * *value;
        }
        roots.push(layer.remove(0));
    }
    roots
}

/// The level's batched query claims, as one weight at `point`.
///
/// Each query contributes the novel-basis column weight of doc annex B, Lemma
/// lem:colweight, `prod_k (1 + p_k (1 + W-hat_k(x_q)))`, scaled by its power of
/// the level's batching challenge.
fn induced_weight(message_log: usize, queries: &[u64], query_weights: &[E], point: &[E]) -> Result<E, VerifierError> {
    require(point.len() == message_log, VerifierError::InducedBasisDimensions)?;
    let roots = subspace_roots(message_log);
    let inverses: Vec<K> = roots.iter().map(|value| value.inv()).collect();
    let mut total = ZERO;
    for (&weight, &query) in query_weights.iter().zip(queries) {
        let mut basis = K(query);
        let mut product = weight;
        for (coordinate, &challenge) in point.iter().enumerate() {
            product *= ONE + challenge * (K(1) + basis * inverses[coordinate]);
            basis = basis.square() + roots[coordinate] * basis;
        }
        total += product;
    }
    Ok(total)
}

type WeightAt = Box<dyn Fn(&[E]) -> Result<E, VerifierError>>;

/// One claim folded into the running sumcheck, and the weight it owes back.
///
/// A level's batched queries and an out-of-domain claim differ only in that
/// weight: both are a power of the level's lambda times a function of the
/// terminal point, restricted to the level's own message coordinates.
struct GluedClaim {
    scalar: E,         // the power of lambda it was glued with
    fold_start: usize, // how many fold challenges preceded the level
    weight_at: WeightAt,
}

/// Verify the base-field multilevel opening with a one-point terminal check.
///
/// `placed` is how many words of the witness the columns fill. The zero tail past them is whole lanes of the
/// level-0 commitment, which the pruned proof leaves out of every row.
pub fn verify_whir(
    transcript: &mut Transcript,
    log_n: usize,
    placed: u64,
    log_inv_rate: usize,
    target: E,
    root: Digest,
    evaluate_basis: &dyn Fn(&[E]) -> E,
) -> Result<(), VerifierError> {
    let config = derive_config(log_n, log_inv_rate)?;
    let levels = config.folds.len();

    let mut running_quad = transcript.sumcheck_round_poly(3, target, None)?;
    let mut folds: Vec<E> = Vec::new();
    let mut glued: Vec<GluedClaim> = Vec::new();
    let mut current_root = root;

    for (level, (&fold_count, &level_rate)) in config.folds.iter().zip(&config.log_inv_rates).enumerate() {
        let mut level_folds = Vec::new();
        for _ in 0..fold_count {
            let challenge = transcript.sample();
            folds.push(challenge);
            level_folds.push(challenge);
            running_quad = transcript.sumcheck_round_poly(3, poly_eval(&running_quad, challenge), None)?;
        }

        let message_log = log_n - folds.len();
        let final_level = level == levels - 1;
        // The level's claims, held until its batching challenge is drawn: the
        // OOD claims first, then the query batch (Annex B, Protocol 1 step 1).
        let mut pending: Vec<(Vec<E>, WeightAt)> = Vec::new();
        let mut residual = Vec::new();
        let mut next_root = current_root;
        if final_level {
            residual = transcript.next_scalars(1 << message_log)?;
        } else {
            let halves = transcript.next_scalars(2)?;
            next_root = Digest::from_halves(halves[0], halves[1])?;
            let ood_point = transcript.samples(message_log);
            let ood_value = transcript.next_scalar()?;
            let intro = transcript.sumcheck_round_poly(3, ood_value, None)?;
            pending.push((intro, Box::new(move |x| Ok(eq_eval(&ood_point, x)))));
        }

        transcript.grind_check(QUERY_GRINDING_BITS)?;
        let block_length = 1 << (message_log + level_rate);
        let queries = sample_queries(transcript, block_length, config.queries[level])?;
        // One batching challenge per level, drawn once every claim it batches is
        // fixed: the OOD claims above and these query positions.
        let lam = transcript.sample();
        let query_weights = powers(lam, queries.len());
        // Level 0 committed the K witness, one leaf word per lane; every deeper
        // level a folded E one, three words per lane.
        let lanes = 1 << fold_count;
        let leaf_words = if level == 0 { lanes } else { 3 * lanes };
        let row_words = if level == 0 {
            placed.div_ceil(1 << message_log) as usize
        } else {
            leaf_words
        };
        let words = transcript.merkle(current_root, block_length, &queries, row_words, leaf_words)?;
        let lane_weights = eq_kernel(&level_folds);
        let row_values: Vec<E> = if level == 0 {
            let base_dot = |row: &Vec<K>| {
                assert_eq!(row.len(), lane_weights.len());
                E::sum(
                    row.iter()
                        .rev()
                        .zip(&lane_weights)
                        .map(|(&word, &weight)| weight * word),
                )
            };
            words.iter().map(base_dot).collect()
        } else {
            words.iter().map(|row| dot(&ext_row(row), &lane_weights)).collect()
        };
        let enforced = dot(&row_values, &query_weights);

        // Every commitment, including the last one, enters through an intro
        // message; the level's claims are then batched with powers of `lam`,
        // the running claim keeping lam^0 = 1.
        let intro = transcript.sumcheck_round_poly(3, enforced, None)?;
        pending.push((
            intro,
            Box::new(move |x| induced_weight(message_log, &queries, &query_weights, x)),
        ));
        let mut scalar = ONE;
        for (intro, weight_at) in pending {
            scalar *= lam;
            for (q, i) in running_quad.iter_mut().zip(intro) {
                *q += scalar * i;
            }
            glued.push(GluedClaim {
                scalar,
                fold_start: folds.len(),
                weight_at,
            });
        }

        if final_level {
            // Finish the remaining sumcheck rounds and close on one evaluation
            // of every basis at the resulting point.
            let mut tail_folds = Vec::new();
            let mut running_target = ZERO;
            for round_index in 0..message_log {
                let challenge = transcript.sample();
                running_target = poly_eval(&running_quad, challenge);
                tail_folds.push(challenge);
                if round_index + 1 < message_log {
                    running_quad = transcript.sumcheck_round_poly(3, running_target, None)?;
                }
            }
            if !transcript.checked() {
                return Ok(());
            }
            // Each glued claim is rebound at the terminal point: the fold
            // challenges its level fixed after it was made, then the tail.
            let point = [&folds[..], &tail_folds].concat();
            let lane_folds = config.folds[0];
            let mut weight = evaluate_basis(&[&point[lane_folds..], &point[..lane_folds]].concat());
            for claim in &glued {
                weight += claim.scalar * (claim.weight_at)(&point[claim.fold_start..])?;
            }
            let terminal = weight * multilinear_eval(&residual, &tail_folds)?;
            return require(terminal == running_target, VerifierError::WhirTerminal);
        }
        current_root = next_root;
    }

    Err(VerifierError::WhirNoTerminalLevel)
}
