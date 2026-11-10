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
/// A Canopy message carries each forest root as `2^CANOPY_DIGEST_WORDS_LOG` words.
const CANOPY_DIGEST_WORDS_LOG: usize = 2;
const CANOPY_DIGEST_WORDS: usize = 1 << CANOPY_DIGEST_WORDS_LOG;

/// The Canopy forest height `R0 + 2` at L0 rate `2^-R0`, `None` at a rate without Canopy.
fn canopy_height(log_inv_rate: usize) -> Option<usize> {
    matches!(log_inv_rate, 1 | 2).then_some(log_inv_rate + CANOPY_DIGEST_WORDS_LOG)
}

/// The commitment to the stack: the root of the L0 tree, or under Canopy (the PCS annex, "Canopy commitment") the
/// root of the Canopy codeword's tree, with the out-of-domain point drawn right after it and the claimed value of the
/// Canopy message there.
pub struct Commitment {
    root: Digest,
    canopy: Option<(Vec<E>, E)>,
}

/// Read the commitment to a stack of `2^log_n` words at L0 rate `2^-log_inv_rate`, the first thing the proof binds.
pub fn read_commitment(
    transcript: &mut Transcript,
    log_n: usize,
    log_inv_rate: usize,
) -> Result<Commitment, VerifierError> {
    let halves = transcript.next_scalars(2)?;
    let root = Digest::from_halves(halves[0], halves[1])?;
    let canopy = match canopy_height(log_inv_rate) {
        Some(_) => {
            let point = transcript.samples(log_n - INITIAL_FOLDING_FACTOR);
            Some((point, transcript.next_scalar()?))
        }
        None => None,
    };
    Ok(Commitment { root, canopy })
}

#[rustfmt::skip]
const WHIR_QUERIES: [[&[usize]; MAX_STACKED_LOG - MIN_STACKED_LOG + 1]; 4] = [
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

/// The tabulated query counts at stacked size `log_n` and rate, `None` outside the admitted shapes.
#[doc(hidden)]
pub fn whir_queries(log_n: usize, log_inv_rate: usize) -> Option<&'static [usize]> {
    WHIR_QUERIES
        .get(log_inv_rate.checked_sub(1)?)?
        .get(log_n.checked_sub(MIN_STACKED_LOG)?)
        .copied()
}

/// The opening shape at this size and rate: the ladder geometry, then the tabulated query counts.
fn derive_config(log_n: usize, log_inv_rate: usize) -> Result<WhirConfig, VerifierError> {
    let queries = whir_queries(log_n, log_inv_rate).ok_or(VerifierError::WhirShape)?;
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

/// The batched claims on the Canopy message as one weight at `point`, its coordinates in round order: the
/// commit-time OOD claim at `ood_point`, then the four words of each L0 query's subtree root (`subtrees`, root `j` is
/// words `4 j ..= 4 j + 3`), weighted by `scales`, the powers of the batching challenge, the OOD claim's first.
fn canopy_weight(ood_point: &[E], subtrees: &[u64], scales: &[E], point: &[E]) -> E {
    let (low, high) = point.split_at(CANOPY_DIGEST_WORDS_LOG);
    let word_weights = eq_kernel(low);
    let mut total = eq_eval(ood_point, point);
    for (&subtree, scales) in subtrees.iter().zip(scales[1..].as_chunks::<CANOPY_DIGEST_WORDS>().0) {
        let mut at_subtree = ONE;
        for (bit, &coordinate) in high.iter().enumerate() {
            at_subtree *= if subtree >> bit & 1 == 1 {
                coordinate
            } else {
                ONE + coordinate
            };
        }
        total += at_subtree * dot(scales, &word_weights);
    }
    total
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
pub fn verify_whir(
    transcript: &mut Transcript,
    log_n: usize,
    log_inv_rate: usize,
    target: E,
    commitment: Commitment,
    evaluate_basis: &dyn Fn(&[E]) -> E,
) -> Result<(), VerifierError> {
    let config = derive_config(log_n, log_inv_rate)?;
    let levels = config.folds.len();
    let canopy_levels = canopy_height(log_inv_rate);
    let Commitment { root, mut canopy } = commitment;
    require(canopy.is_some() == canopy_levels.is_some(), VerifierError::WhirShape)?;

    let mut running_quad = transcript.sumcheck_round_poly(3, target, None)?;
    let mut folds: Vec<E> = Vec::new();
    let mut glued: Vec<GluedClaim> = Vec::new();
    let mut current_root = root;
    // Under Canopy, the vector batch's challenge, which L1 opens the Canopy codeword with.
    let mut canopy_beta = None;

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
        // Level 0 committed the K witness, one leaf word per lane; every deeper
        // level a folded E one, three words per lane.
        let lanes = 1 << fold_count;
        let leaf_words = if level == 0 { lanes } else { 3 * lanes };
        // Under Canopy, L0 opens a forest: its roots are claims on the Canopy message, observed before anything they
        // are batched with is drawn.
        let (words, forest_roots) = match canopy_levels.filter(|_| level == 0) {
            Some(forest_levels) => {
                let (words, roots) = transcript.forest(forest_levels, &queries, leaf_words)?;
                roots.iter().for_each(|root| transcript.observe_digest(root));
                (words, roots)
            }
            None => (
                transcript.merkle(current_root, block_length, &queries, leaf_words)?,
                Vec::new(),
            ),
        };
        // One batching challenge per level, drawn once every claim it batches is
        // fixed: the OOD claims above, these query positions and any forest roots,
        // whose claims on the Canopy message it batches too.
        let lam = transcript.sample();
        let query_weights = powers(lam, queries.len());
        let lane_weights = eq_kernel(&level_folds);
        let row_values: Vec<E> = if level == 0 {
            let base_dot = |row: &[K]| {
                E::sum(
                    row.iter()
                        .rev()
                        .zip(&lane_weights)
                        .map(|(&word, &weight)| weight * word),
                )
            };
            words.iter().map(|&row| base_dot(row)).collect()
        } else if let Some(beta) = canopy_beta.take() {
            // L1 under Canopy: the rows of `f1 + beta c`, the Canopy codeword's opened at the same positions after.
            let c_words = transcript.merkle(root, block_length, &queries, lanes)?;
            let c_dot = |row: &[K]| E::sum(row.iter().zip(&lane_weights).map(|(&word, &weight)| weight * word));
            let row_value = |(row, c_row): (&&[K], &&[K])| dot(&ext_row(row), &lane_weights) + beta * c_dot(c_row);
            words.iter().zip(&c_words).map(row_value).collect()
        } else {
            words.iter().map(|&row| dot(&ext_row(row), &lane_weights)).collect()
        };
        let enforced = dot(&row_values, &query_weights);
        let subtrees: Vec<u64> = match canopy_levels.filter(|_| level == 0) {
            Some(forest_levels) => queries.iter().map(|&query| query >> forest_levels).collect(),
            None => Vec::new(),
        };

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

        // Under Canopy, after L0's claims: the claims on the Canopy message batched with powers of the level's `lam`,
        // the OOD claim's the first, then their two-vector batch with the folded witness at `beta`. The prover sends
        // the batched claim's intro and the cross polynomial's three coefficients.
        if let Some((ood_point, ood_value)) = canopy.take().filter(|_| level == 0) {
            let scales = powers(lam, 1 + (forest_roots.len() << CANOPY_DIGEST_WORDS_LOG));
            let mut claim = ood_value;
            for (forest_root, scales) in forest_roots
                .iter()
                .zip(scales[1..].as_chunks::<CANOPY_DIGEST_WORDS>().0)
            {
                for (&word, &scale) in forest_root.words().iter().zip(scales) {
                    claim += scale * K(word);
                }
            }
            let intro = transcript.sumcheck_round_poly(3, claim, None)?;
            let cross = transcript.next_scalars(3)?;
            let beta = transcript.sample();
            for ((q, x), c) in running_quad.iter_mut().zip(&cross).zip(&intro) {
                *q += beta * *x + beta * beta * *c;
            }
            glued.push(GluedClaim {
                scalar: beta,
                fold_start: folds.len(),
                weight_at: Box::new(move |x| Ok(canopy_weight(&ood_point, &subtrees, &scales, x))),
            });
            canopy_beta = Some(beta);
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
