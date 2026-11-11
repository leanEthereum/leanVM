//! WHIR opening.

use crate::field::{E, K, ONE, ZERO, powers};
use crate::hash::Digest;
use crate::layout::{MAX_STACKED_LOG, MIN_STACKED_LOG};
use crate::multilinear::{eq_eval, log2_strict, multilinear_eval};
use crate::transcript::{Transcript, sumcheck};
use crate::{VerifierError, require};

pub(crate) const INITIAL_FOLDING_FACTOR: usize = 6;
const SUBSEQUENT_FOLDING_FACTOR: usize = 4;
const RS_DOMAIN_INITIAL_REDUCTION_FACTOR: usize = 3;
const RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR: usize = 1;
const RESIDUAL_MAX_LOG: usize = 5;
pub const QUERY_GRINDING_BITS: u32 = 17;
/// Before each fold round's `(gamma, alpha, beta)`.
pub const FOLD_GRINDING_BITS: u32 = 9;
/// Before every batching challenge: each level's lambda, and the stacked opening's map challenges and lambda.
pub const BATCH_GRINDING_BITS: u32 = 14;
/// Before the level-0 OOD sample.
pub const OOD_GRINDING_BITS: u32 = 15;
/// Out-of-domain points after each non-final level's commitment, drawn together with no grind.
pub const OOD_SAMPLES: usize = 2;

#[rustfmt::skip]
const WHIR_QUERIES: [[&[usize]; MAX_STACKED_LOG - MIN_STACKED_LOG + 1]; 4] = [
    [&[238,63], &[230,60,42], &[225,58,38], &[222,57,35], &[220,56,34], &[219,55,33,27], &[218,55,32,25], &[218,55,32,24], &[217,55,32,23], &[217,55,32,23,20], &[217,55,32,23,19], &[217,55,32,22,18], &[217,55,31,22,18], &[217,55,31,22,18,16]],
    [&[114,49], &[112,47,35], &[111,46,32], &[110,45,31], &[110,45,29], &[109,44,29,24], &[109,44,28,23], &[109,44,28,22], &[109,44,28,21], &[109,44,28,21,18], &[109,44,28,21,17], &[109,44,28,20,17], &[109,44,28,20,17], &[109,44,28,20,16,15]],
    [&[75,40], &[74,39,30], &[74,38,28], &[73,37,27], &[73,37,26], &[73,37,25,22], &[73,37,25,20], &[73,37,25,20], &[73,37,25,19], &[73,37,25,19,17], &[73,37,25,19,16], &[73,37,25,19,16], &[73,37,25,19,15], &[73,37,25,19,15,14]],
    [&[56,34], &[56,33,27], &[55,32,25], &[55,32,24], &[55,32,23], &[55,32,23,20], &[55,32,23,19], &[55,32,22,18], &[55,31,22,18], &[55,31,22,18,16], &[55,31,22,17,15], &[55,31,22,17,15], &[55,31,22,17,14], &[55,31,22,17,14,13]],
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

/// Regroup a level's leaf words into the E values they encode, two per lane.
fn ext_row(words: &[K]) -> Vec<E> {
    words.as_chunks().0.iter().map(|&[c0, c1]| E::new(c0.0, c1.0)).collect()
}

fn sample_queries(transcript: &mut Transcript, block_length: u64, count: usize) -> Result<Vec<u64>, VerifierError> {
    let depth = log2_strict(block_length)?;
    let per_word = 128 / depth;
    let mut result = Vec::with_capacity(count);
    while result.len() < count {
        let sample = transcript.sample();
        let word = sample.c0 as u128 | (sample.c1 as u128) << 64;
        for chunk in 0..per_word.min(count - result.len()) {
            result.push((word >> (chunk * depth)) as u64 & (block_length - 1));
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

/// The normalized subspace polynomials `What_i = W_i / W_i(beta_i)` for `i <= mu`, at points of the RS domain.
struct Subspace {
    roots: Vec<K>,
    inverses: Vec<K>,
}

impl Subspace {
    fn new(mu: usize) -> Self {
        let roots = subspace_roots(mu);
        let inverses = roots.iter().map(|value| value.inv()).collect();
        Self { roots, inverses }
    }

    /// `What_i(x)` for `i <= mu`, by `W_(i+1) = W_i^2 + W_i(beta_i) W_i`.
    fn at(&self, x: K) -> Vec<K> {
        let mut basis = x;
        let mut values = Vec::with_capacity(self.roots.len());
        for (&root, &inverse) in self.roots.iter().zip(&self.inverses) {
            values.push(basis * inverse);
            basis = basis.square() + root * basis;
        }
        values
    }
}

/// `X_c(x) = prod_{i: c_i = 1} What_i(x)` for every `c < count`, from `What_i(x)` (Annex D's novel basis).
fn novel_basis(what: &[K], count: usize) -> Vec<K> {
    let mut basis = vec![K(1)];
    for &value in what {
        if basis.len() >= count {
            break;
        }
        let doubled: Vec<K> = basis.iter().map(|&b| b * value).collect();
        basis.extend(doubled);
    }
    assert!(
        basis.len() >= count,
        "the novel basis needs What_i for every bit of its indices"
    );
    basis.truncate(count);
    basis
}

/// `P(x) = sum_c p_c X_c(x)`, `p` the coefficients in the novel basis.
fn novel_eval(coefficients: &[E], what: &[K]) -> E {
    let basis = novel_basis(what, coefficients.len());
    E::sum(coefficients.iter().zip(basis).map(|(&p, b)| p * b))
}

/// The challenges of one fold round that act on the oracle: `P = G + (alpha + beta X) F`.
#[derive(Clone, Copy)]
struct FoldRound {
    alpha: E,
    beta: E,
}

/// One opened row, its lanes in eq_kernel order, folded at its domain point `x` round by round as the prover folds
/// the lanes, `F` and `G` the lanes `2m` and `2m + 1` ([CYWZ26, preprint], Corollary 5.2).
fn fold_row(mut values: Vec<E>, x: K, rounds: &[FoldRound]) -> E {
    for round in rounds {
        let affine = round.alpha + round.beta * x;
        values = values.as_chunks::<2>().0.iter().map(|&[f, g]| g + affine * f).collect();
    }
    assert_eq!(values.len(), 1, "one round per lane variable");
    values[0]
}

/// The level's batched query claims, as one weight at `point`.
///
/// Each query contributes the novel-basis column weight of doc annex D, Lemma
/// lem:colweight, `prod_k (1 + p_k (1 + W-hat_k(x_q)))`, scaled by its power of
/// the level's batching challenge.
fn induced_weight(message_log: usize, queries: &[u64], query_weights: &[E], point: &[E]) -> Result<E, VerifierError> {
    require(point.len() == message_log, VerifierError::InducedBasisDimensions)?;
    let subspace = Subspace::new(message_log);
    let mut total = ZERO;
    for (&weight, &query) in query_weights.iter().zip(queries) {
        let what = subspace.at(K(query));
        let mut product = weight;
        for (&challenge, &value) in point.iter().zip(&what) {
            product *= ONE + challenge * (K(1) + value);
        }
        total += product;
    }
    Ok(total)
}

type WeightAt = Box<dyn Fn(&[E]) -> Result<E, VerifierError>>;

/// One claim glued into the running claim, and the weight it owes back.
///
/// A level's batched queries and its out-of-domain claims differ only in that
/// weight: both are a power of the level's lambda times a function of the
/// terminal point, restricted to the level's own message coordinates.
struct GluedClaim {
    scalar: E,         // the power of lambda it was glued with
    fold_start: usize, // how many gammas preceded the level
    weight_at: WeightAt,
}

/// Verify the base-field multilevel opening with a one-point terminal check.
///
/// A level's rounds fold its lanes by the affine combiner `G + (alpha + beta X) F` of [CYWZ26, preprint],
/// the claim carried by five scalars a round and the weight folded by `gamma`, so the gammas are the weight's
/// point. A non-final level then commits the folded lane's low part, sends its high part, and glues its OOD claims
/// and its queries, each opened row folded as the lanes were and corrected by the high part. The final level sends
/// the whole folded lane, checks the queries against it, and closes with a sumcheck over the low part.
pub fn verify_whir(
    transcript: &mut Transcript,
    log_n: usize,
    log_inv_rate: usize,
    target: E,
    root: Digest,
    evaluate_basis: &dyn Fn(&[E]) -> E,
) -> Result<(), VerifierError> {
    let config = derive_config(log_n, log_inv_rate)?;
    let levels = config.folds.len();

    let mut claim = target;
    let mut gammas: Vec<E> = Vec::new();
    let mut glued: Vec<GluedClaim> = Vec::new();
    let mut current_root = root;

    for (level, (&fold_count, &level_rate)) in config.folds.iter().zip(&config.log_inv_rates).enumerate() {
        let mut rounds = Vec::with_capacity(fold_count);
        for _ in 0..fold_count {
            let table = transcript.next_scalars(5)?;
            let (u0, v0, c0, v1, c1) = (table[0], table[1], table[2], table[3], table[4]);
            // The F lanes' share `v0` and the G lanes' `u1` make up the claim.
            let u1 = claim + v0;
            transcript.grind_check(FOLD_GRINDING_BITS)?;
            let gamma = transcript.sample();
            let alpha = transcript.sample();
            let beta = transcript.sample();
            claim = (ONE + gamma) * (u0 + alpha * v0 + beta * c0) + gamma * (u1 + alpha * v1 + beta * c1);
            gammas.push(gamma);
            rounds.push(FoldRound { alpha, beta });
        }

        let mu = log_n - gammas.len();
        let final_level = level == levels - 1;
        let subspace = Subspace::new(mu);
        let block_length = 1 << (mu + level_rate);
        // Level 0 committed the K witness, one leaf word per lane; every deeper
        // level a folded E one, two words per lane.
        let lanes = 1 << fold_count;
        let leaf_words = if level == 0 { lanes } else { 2 * lanes };
        // The opened rows' lanes in eq_kernel order: level 0's leaf image reversed.
        let lanes_of = |row: &[K]| -> Vec<E> {
            if level == 0 {
                row.iter().rev().map(|&word| E::from(word)).collect()
            } else {
                ext_row(row)
            }
        };

        if final_level {
            let folded = transcript.next_scalars((1 << mu) + fold_count)?;
            transcript.grind_check(QUERY_GRINDING_BITS)?;
            let queries = sample_queries(transcript, block_length, config.queries[level])?;
            let words = transcript.merkle(current_root, block_length, &queries, leaf_words)?;
            if transcript.checked() {
                for (&query, row) in queries.iter().zip(words) {
                    let x = K(query);
                    let value = fold_row(lanes_of(row), x, &rounds);
                    require(
                        value == novel_eval(&folded, &subspace.at(x)),
                        VerifierError::WhirFinalQuery,
                    )?;
                }
            }
            let (tail, claim) = sumcheck(transcript, claim, 3, &vec![None; mu])?;
            if !transcript.checked() {
                return Ok(());
            }
            // Each glued claim is rebound at the terminal point: the gammas its
            // level drew after it was made, then the tail.
            let point = [&gammas[..], &tail].concat();
            let lane_folds = config.folds[0];
            let mut weight = evaluate_basis(&[&point[lane_folds..], &point[..lane_folds]].concat());
            for glued_claim in &glued {
                weight += glued_claim.scalar * (glued_claim.weight_at)(&point[glued_claim.fold_start..])?;
            }
            let terminal = weight * multilinear_eval(&folded[..1 << mu], &tail)?;
            return require(terminal == claim, VerifierError::WhirTerminal);
        }

        let halves = transcript.next_scalars(2)?;
        let next_root = Digest::from_halves(halves[0], halves[1]);
        let high = transcript.next_scalars(fold_count)?;
        // The OOD points, one message with no grind, then their values.
        let ood_points: Vec<Vec<E>> = (0..OOD_SAMPLES).map(|_| transcript.samples(mu)).collect();
        let ood_values = transcript.next_scalars(OOD_SAMPLES)?;
        transcript.grind_check(QUERY_GRINDING_BITS)?;
        let queries = sample_queries(transcript, block_length, config.queries[level])?;
        transcript.grind_check(BATCH_GRINDING_BITS)?;
        let lambda = transcript.sample();
        let query_weights = powers(lambda, queries.len());
        let words = transcript.merkle(current_root, block_length, &queries, leaf_words)?;
        // Each row folds to the folded lane at its point; less the high part, `What_mu(x) sum_j p_(2^mu + j) X_j(x)`,
        // it is the low part's value there, which the column weight reads.
        let mut batched = ZERO;
        for ((&query, row), &query_weight) in queries.iter().zip(words).zip(&query_weights) {
            let x = K(query);
            let what = subspace.at(x);
            let correction = novel_eval(&high, &what) * what[mu];
            batched += query_weight * (fold_row(lanes_of(row), x, &rounds) + correction);
        }
        // OOD claim `s` takes lambda^(s + 1), the query batch lambda^(OOD_SAMPLES + 1) times its own powers of lambda.
        let scalars = powers(lambda, OOD_SAMPLES + 2);
        for ((point, value), &scalar) in ood_points.into_iter().zip(ood_values).zip(&scalars[1..]) {
            claim += scalar * value;
            glued.push(GluedClaim {
                scalar,
                fold_start: gammas.len(),
                weight_at: Box::new(move |x| Ok(eq_eval(&point, x))),
            });
        }
        claim += scalars[OOD_SAMPLES + 1] * batched;
        glued.push(GluedClaim {
            scalar: scalars[OOD_SAMPLES + 1],
            fold_start: gammas.len(),
            weight_at: Box::new(move |x| induced_weight(mu, &queries, &query_weights, x)),
        });
        current_root = next_root;
    }

    Err(VerifierError::WhirNoTerminalLevel)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn generator() -> impl FnMut() -> E {
        let mut state = 0x2545_F491_4F6C_DD1Du64;
        move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            E::new(state, state.rotate_left(23))
        }
    }

    /// `W_i(x) = prod_(u in span(1, x, ..., x^(i-1))) (x + u)`, straight from the definition.
    fn vanishing(i: usize, x: K) -> K {
        (0..1u64 << i).fold(K(1), |acc, u| acc * (x + K(u)))
    }

    fn reference_what(i: usize, x: K) -> K {
        vanishing(i, x) * vanishing(i, K(1 << i)).inv()
    }

    /// `X * H` in the novel basis: `X X_c = sum_(j < t) A_j X_(c, bits below j cleared) + A_t X_(c + 1)`, `t` the
    /// trailing ones of `c`, `A_j = a_0 ... a_(j-1)`, `a_i = W_(i+1)(beta_(i+1)) / W_i(beta_i)^2`.
    fn times_x(coefficients: &[E], roots: &[K]) -> Vec<E> {
        let a: Vec<K> = (0..roots.len() - 1)
            .map(|i| roots[i + 1] * roots[i].square().inv())
            .collect();
        let mut out = vec![ZERO; coefficients.len() + 1];
        for (c, &h) in coefficients.iter().enumerate() {
            let t = c.trailing_ones() as usize;
            let mut product = K(1);
            for (j, &a_j) in a.iter().enumerate().take(t) {
                out[c & !((1 << j) - 1)] += h * product;
                product = product * a_j;
            }
            out[c + 1] += h * product;
        }
        out
    }

    fn padded_sum(left: &[E], right: &[E]) -> Vec<E> {
        (0..left.len().max(right.len()))
            .map(|i| *left.get(i).unwrap_or(&ZERO) + *right.get(i).unwrap_or(&ZERO))
            .collect()
    }

    /// `What_i(x)` and `P(x) = sum_c p_c X_c(x)` against the vanishing polynomials multiplied out.
    #[test]
    fn novel_basis_matches_the_vanishing_products() {
        let mut next = generator();
        let mu = 4;
        let subspace = Subspace::new(mu);
        let coefficients: Vec<E> = (0..(1 << mu) + 3).map(|_| next()).collect();
        for x in [K(0), K(5), K(1 << mu), K(next().c0)] {
            let what = subspace.at(x);
            for (i, &value) in what.iter().enumerate() {
                assert_eq!(value, reference_what(i, x), "What_{i}({x:?})");
            }
            let expected = E::sum(coefficients.iter().enumerate().map(|(c, &p)| {
                (0..=mu)
                    .filter(|i| c >> i & 1 == 1)
                    .fold(p, |acc, i| acc * reference_what(i, x))
            }));
            assert_eq!(novel_eval(&coefficients, &what), expected);
        }
    }

    /// The multiplication by X the prover folds with is multiplication by x at every point.
    #[test]
    fn times_x_is_multiplication_by_x() {
        let mut next = generator();
        let mu = 4;
        let subspace = Subspace::new(mu + 1);
        let mut h: Vec<E> = (0..1 << mu).map(|_| next()).collect();
        for _ in 0..3 {
            let product = times_x(&h, &subspace.roots);
            let x = K(next().c0);
            let what = subspace.at(x);
            assert_eq!(novel_eval(&product, &what), novel_eval(&h, &what) * x);
            h = product;
        }
    }

    /// A row of lane values folds to the folded lane's value at its point, and the What_mu correction of the high
    /// part leaves the low part's value.
    #[test]
    fn affine_row_fold_and_high_correction() {
        let mut next = generator();
        let (mu, k) = (4, 3);
        let subspace = Subspace::new(mu + 1);
        let mut lanes: Vec<Vec<E>> = (0..1 << k).map(|_| (0..1 << mu).map(|_| next()).collect()).collect();
        let rounds: Vec<FoldRound> = (0..k)
            .map(|_| FoldRound {
                alpha: next(),
                beta: next(),
            })
            .collect();
        let points: Vec<K> = (0..4).map(|_| K(next().c0)).collect();
        let rows: Vec<Vec<E>> = points
            .iter()
            .map(|&x| lanes.iter().map(|lane| novel_eval(lane, &subspace.at(x))).collect())
            .collect();
        for round in &rounds {
            lanes = lanes
                .as_chunks::<2>()
                .0
                .iter()
                .map(|[f, g]| {
                    let xf = times_x(f, &subspace.roots);
                    let scaled = |values: &[E], s: E| values.iter().map(|&v| s * v).collect::<Vec<_>>();
                    padded_sum(&padded_sum(g, &scaled(f, round.alpha)), &scaled(&xf, round.beta))
                })
                .collect();
        }
        let folded = &lanes[0];
        assert_eq!(folded.len(), (1 << mu) + k);
        let (low, high) = folded.split_at(1 << mu);
        for (&x, row) in points.iter().zip(rows) {
            let what = subspace.at(x);
            let value = fold_row(row, x, &rounds);
            assert_eq!(value, novel_eval(folded, &what));
            assert_eq!(value + novel_eval(high, &what) * what[mu], novel_eval(low, &what));
        }
    }
}
