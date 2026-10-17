//! Flock reduction, then ring switching.

use crate::field::{E, GEN, ONE, Scaled, ZERO};
use crate::hash::{BLAKE2S_G_LANES, BLAKE2S_IV, BLAKE2S_SIGMA};
use crate::layout::{BLAKE2S_CONSTANT_COLUMN, BLAKE2S_R1CS_LOG_SIZE, FLOCK_K_SKIP, FLOCK_NUM_LINCHECK_ROUNDS, K_BITS};
use crate::multilinear::{dot, eq_eval, eq_kernel, multilinear_eval, poly_eval};
use crate::transcript::{Transcript, sumcheck};
use crate::{VerifierError, require};

const PHI_BASIS: [u64; 8] = [
    0x0000000000000001,
    0x033CE8BEDDC8A656,
    0x512620375ED2A108,
    0x0C9E636090AAFC01,
    0xBA4F3CD82801769C,
    0xBA26E7904ADB4A47,
    0x467698598926DC01,
    0x4418AE808B28BDD0,
];

/// `PHI[value]`: the F2-linear image of the byte `value` in the PHI basis.
fn phi(value: usize) -> E {
    let bits = (0..8).filter(|bit| value >> bit & 1 == 1);
    E::new(bits.fold(0, |acc, bit| acc ^ PHI_BASIS[bit]), 0, 0)
}

const MEDIUM_GENERATOR: E = E::new(0x243F6A8885A308D3, 0x13198A2E03707344, 0xA4093822299F31D0);
const N_FIXED_CHALLENGES: usize = 7;

fn fixed_challenges() -> [E; N_FIXED_CHALLENGES] {
    let medium = |power: u32| {
        let value = MEDIUM_GENERATOR.pow(1 << power);
        value * (ONE + value).inv()
    };
    [
        phi(0xF7),
        phi(0x53),
        phi(0xB5),
        medium(0),
        medium(1),
        medium(2),
        medium(3),
    ]
}

/// The one barycentric denominator `PHI[:count]` has: `prod_(k != 0) PHI[k]`, inverted.
///
/// PHI is F2-linear in its index, so `PHI[i] + PHI[j] = PHI[i ^ j]`, and over a power-of-two prefix
/// `j -> i ^ j` only permutes the block. Every node is left the same product.
fn window_denominator(count: usize) -> E {
    (1..count).fold(ONE, |acc, k| acc * phi(k)).inv()
}

/// The barycentric weights of `PHI[:count]` at `point`, by prefix and suffix numerator products.
pub(crate) fn lagrange_weights(count: usize, point: E) -> Vec<E> {
    let differences: Vec<E> = (0..count).map(|node| point + phi(node)).collect();
    let mut prefix = vec![ONE; count + 1];
    let mut suffix = vec![ONE; count + 1];
    for i in 0..count {
        prefix[i + 1] = prefix[i] * differences[i];
        suffix[count - 1 - i] = suffix[count - i] * differences[count - 1 - i];
    }
    let denominator = window_denominator(count);
    (0..count).map(|i| prefix[i] * suffix[i + 1] * denominator).collect()
}

fn lagrange_interpolate(count: usize, values: &[E], point: E) -> E {
    dot(&lagrange_weights(count, point), values)
}

pub(crate) struct ZerocheckResult {
    z_skip: E,
    chi: Vec<E>,
    v_a: E,
    v_b: E,
    v_c: E,
}

/// The zerocheck: one univariate skip round, then nflock quadratic ones.
/// C rides those rounds with AB, so all three claims come out at one point.
pub(crate) fn verify_flock_zerocheck(
    log_n: usize,
    transcript: &mut Transcript,
) -> Result<ZerocheckResult, VerifierError> {
    // The point r: seven fixed coordinates, the rest sampled.
    let mut r: Vec<Option<E>> = fixed_challenges().map(Some).into();
    let sampled = transcript.samples(log_n - FLOCK_K_SKIP - N_FIXED_CHALLENGES);
    r.extend(sampled.into_iter().map(Some));

    // P = P^AB + P^C on the coset, then z_skip; the 64 zeros on Lambda are assumed.
    let p_coset = transcript.next_scalars(K_BITS)?;
    let z_skip = transcript.sample();
    let v_p = lagrange_interpolate(2 * K_BITS, &[vec![ZERO; K_BITS], p_coset].concat(), z_skip);

    // nflock quadratic rounds on P, closed by v_a, v_b.
    let (chi, running) = sumcheck(transcript, v_p, 3, &r)?;
    let (v_a, v_b) = (transcript.next_scalar()?, transcript.next_scalar()?);
    let v_c = running + v_a * v_b;
    Ok(ZerocheckResult {
        z_skip,
        chi,
        v_a,
        v_b,
        v_c,
    })
}

/// What the reduction leaves: the zerocheck's point and its three claims there, then the lincheck's
/// batching challenge, its round challenges in round order, and the 64 slices it closes on.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlockClaims {
    pub z_skip: E,
    pub chi: Vec<E>,
    pub v_a: E,
    pub v_b: E,
    pub v_c: E,
    pub alpha: E,
    pub round_challenges: Vec<E>,
    pub s: Vec<E>,
}

impl FlockClaims {
    /// The point the slices are claims at: the lincheck's challenges in coordinate order, then the rest of chi.
    pub(crate) fn point(&self) -> Vec<E> {
        let rest = self.chi[self.round_challenges.len()..].iter().copied();
        self.chi_in_prime().into_iter().chain(rest).collect()
    }

    /// The row coordinates the lincheck rounds ran over, past the skip.
    pub(crate) fn chi_in(&self) -> &[E] {
        &self.chi[..self.round_challenges.len()]
    }

    /// The lincheck's challenges in coordinate order.
    pub(crate) fn chi_in_prime(&self) -> Vec<E> {
        self.round_challenges.iter().rev().copied().collect()
    }

    /// The terminal's column weights `w_col = eq(chi_in_prime) ⊗ s`, a column of it per slice: each slice multiplies
    /// the whole eq table.
    pub(crate) fn column_weights(&self) -> Vec<E> {
        let high = eq_kernel(&self.chi_in_prime());
        let mut w_col = vec![ZERO; high.len() * K_BITS];
        for (l, &slice) in self.s.iter().enumerate() {
            let slice = Scaled::new(slice);
            for (h, &weight) in high.iter().enumerate() {
                w_col[h * K_BITS + l] = slice.mul(weight);
            }
        }
        w_col
    }

    /// `e_row^T values` for each of `values`, with the row weights `e_row = eq(chi_in) ⊗ skip_weights` (phi8 Lagrange
    /// in the skip coordinate, eq in the slot variables) never built: each block of 64 rows meets the skip weights,
    /// a column at a time, then chi_in folds the blocks.
    pub(crate) fn row_forms<const N: usize>(&self, values: [&[E]; N]) -> Result<[E; N], VerifierError> {
        let blocks = 1 << self.round_challenges.len();
        let mut folded = [(); N].map(|_| vec![ZERO; blocks]);
        for (l, &weight) in lagrange_weights(K_BITS, self.z_skip).iter().enumerate() {
            let weight = Scaled::new(weight);
            for (block, values) in folded.iter_mut().zip(values) {
                for (h, value) in block.iter_mut().enumerate() {
                    *value += weight.mul(values[h * K_BITS + l]);
                }
            }
        }
        let mut forms = [ZERO; N];
        for (form, block) in forms.iter_mut().zip(&folded) {
            *form = multilinear_eval(block, self.chi_in())?;
        }
        Ok(forms)
    }
}

/// Lincheck at the quirky point (z_skip, chi) over `rounds` high column coordinates: its 64 slices s, claims at
/// [`FlockClaims::point`], and the running claim the circuit's terminal identity must meet,
/// `e_row^T (A0 + alpha B0 + alpha^2 C0) w_col + alpha^3 w_col[constant column]` ([`FlockClaims::row_forms`],
/// [`FlockClaims::column_weights`]).
pub(crate) fn verify_lincheck(
    zc: ZerocheckResult,
    rounds: usize,
    transcript: &mut Transcript,
) -> Result<(FlockClaims, E), VerifierError> {
    let alpha = transcript.sample(); // batches the two matrix identities, the c claim and the constant-position claim

    // The rounds that bind the high column coordinates, leaving 64 unfolded.
    let claim = zc.v_a + alpha * zc.v_b + alpha.pow(2) * zc.v_c + alpha.pow(3);
    let (round_challenges, running) = sumcheck(transcript, claim, 3, &vec![None; rounds])?;

    // The residual, which the terminal identity closes on.
    let s = transcript.next_scalars(K_BITS)?;
    let claims = FlockClaims {
        z_skip: zc.z_skip,
        chi: zc.chi,
        v_a: zc.v_a,
        v_b: zc.v_b,
        v_c: zc.v_c,
        alpha,
        round_challenges,
        s,
    };
    Ok((claims, running))
}

/// BLAKE2s's terminal: the forward walk gives `A0 w` and `B0 w`, and `C = I`, so the c weight is e_row itself and,
/// both sides being tensors, collapses to eq(chi_in, chi_in_prime) times a 64-term Lagrange combination.
fn blake2s_terminal(claims: &FlockClaims) -> Result<E, VerifierError> {
    let alpha = claims.alpha;
    let w_col = claims.column_weights();
    let (left_values, right_values) = blake2s_row_values(&w_col);
    let [left, right] = claims.row_forms([&left_values, &right_values])?;
    let skip_weights = lagrange_weights(K_BITS, claims.z_skip);
    Ok(left
        + alpha * right
        + alpha.pow(2) * eq_eval(claims.chi_in(), &claims.chi_in_prime()) * dot(&skip_weights, &claims.s)
        + alpha.pow(3) * w_col[BLAKE2S_CONSTANT_COLUMN])
}

type Word = [E; 32];

/// The forward walk's state: `A0 w` and `B0 w`, filled row by row.
struct RowValues<'a> {
    column_weights: &'a [E],
    left_values: Vec<E>,
    right_values: Vec<E>,
}

impl RowValues<'_> {
    fn slots(&self, base: usize) -> Word {
        std::array::from_fn(|bit| self.column_weights[base + bit])
    }

    fn literal(&self, value: u32) -> Word {
        let constant = self.column_weights[BLAKE2S_CONSTANT_COLUMN];
        std::array::from_fn(|bit| if value >> bit & 1 == 1 { constant } else { ZERO })
    }

    fn add(&mut self, x: Word, y: Word, carry_base: usize) -> Word {
        let mut carry = ZERO;
        let mut output = [ZERO; 32];
        for bit in 0..32 {
            if bit < 31 {
                self.left_values[carry_base + bit] = x[bit] + carry;
                self.right_values[carry_base + bit] = y[bit] + carry;
            }
            output[bit] = x[bit] + y[bit] + carry;
            if bit < 31 {
                carry += self.column_weights[carry_base + bit];
            }
        }
        output
    }

    /// Fused three-operand add: 31 majority rows then 30 ripple rows.
    ///
    /// The majority of bit `i` is `maj_aux[i] + z[i]`, since over GF(2)
    /// `(x+z)(y+z) = xy + xz + yz + z`; then `x + y + z` is the ripple sum of
    /// `p = x^y^z` against `q[i] = maj[i-1]`, whose bit 0 is zero, so the
    /// ripple layer's bit 0 needs no row and slot `base + 31 + i - 1` carries
    /// bit `i`.
    fn add3(&mut self, x: Word, y: Word, z: Word, base: usize) -> Word {
        let mut majority = [ZERO; 31];
        for bit in 0..31 {
            self.left_values[base + bit] = x[bit] + z[bit];
            self.right_values[base + bit] = y[bit] + z[bit];
            majority[bit] = self.column_weights[base + bit] + z[bit];
        }
        let ripple_base = base + 31;
        let mut carry = ZERO;
        let mut output = [ZERO; 32];
        for bit in 0..32 {
            let q = if bit == 0 { ZERO } else { majority[bit - 1] };
            let left = x[bit] + y[bit] + z[bit] + carry;
            output[bit] = left + q;
            if (1..=30).contains(&bit) {
                self.left_values[ripple_base + bit - 1] = left;
                self.right_values[ripple_base + bit - 1] = q + carry;
                carry += self.column_weights[ripple_base + bit - 1];
            }
        }
        output
    }

    fn linear_rows(&mut self, values: Word, base: usize) {
        for bit in 0..32 {
            self.left_values[base + bit] = values[bit];
            self.right_values[base + bit] = self.column_weights[BLAKE2S_CONSTANT_COLUMN];
        }
    }
}

fn xor(x: Word, y: Word) -> Word {
    std::array::from_fn(|bit| x[bit] + y[bit])
}

fn rotate_right(word: Word, amount: usize) -> Word {
    std::array::from_fn(|bit| word[(bit + amount) & 31])
}

/// Compute `A0 w` and `B0 w` by one forward walk of the circuit.
pub fn blake2s_row_values(column_weights: &[E]) -> (Vec<E>, Vec<E>) {
    let size = 1 << BLAKE2S_R1CS_LOG_SIZE;
    let constant = BLAKE2S_CONSTANT_COLUMN;
    let message_base = 640;
    let counter_low = 1152;
    let counter_high = 1184;
    let final_flag = 1216;
    let last_node_flag = 1248;
    let gates_base = 1280;
    let gate_stride = 184;
    let mut rows = RowValues {
        column_weights,
        left_values: vec![ZERO; size],
        right_values: vec![ZERO; size],
    };

    for (base, length) in [(0, 256), (message_base, 512), (counter_low, 128)] {
        for row in base..base + length {
            rows.left_values[row] = column_weights[row];
            rows.right_values[row] = column_weights[constant];
        }
    }

    // v[0..8] = h, v[8..12] = IV[0..4], v[12..16] = IV[4..8] ^ (t_lo, t_hi, f0, f1).
    let mut state = [[ZERO; 32]; 16];
    for word in 0..8 {
        state[word] = rows.slots(32 * word);
    }
    for word in 0..4 {
        state[8 + word] = rows.literal(BLAKE2S_IV[word]);
    }
    for (word, base) in [counter_low, counter_high, final_flag, last_node_flag]
        .into_iter()
        .enumerate()
    {
        state[12 + word] = xor(rows.literal(BLAKE2S_IV[4 + word]), rows.slots(base));
    }

    for (round_index, sigma) in BLAKE2S_SIGMA.iter().enumerate() {
        for (gate_index, &[lane_a, lane_b, lane_c, lane_d]) in BLAKE2S_G_LANES.iter().enumerate() {
            let gate = round_index * 8 + gate_index;
            let gate_base = gates_base + gate_stride * gate;
            let (a, b, c, d) = (state[lane_a], state[lane_b], state[lane_c], state[lane_d]);
            let mx = rows.slots(message_base + 32 * sigma[2 * gate_index]);
            let my = rows.slots(message_base + 32 * sigma[2 * gate_index + 1]);
            let a1 = rows.add3(a, b, mx, gate_base);
            let d1 = rotate_right(xor(d, a1), 16);
            let c1 = rows.add(c, d1, gate_base + 61);
            let b1 = rotate_right(xor(b, c1), 12);
            let a2 = rows.add3(a1, b1, my, gate_base + 92);
            let d2 = rotate_right(xor(d1, a2), 8);
            let c2 = rows.add(c1, d2, gate_base + 153);
            let b2 = rotate_right(xor(b1, c2), 7);
            // Every lane cascades: this encoding materializes no intermediate word.
            state[lane_a] = a2;
            state[lane_b] = b2;
            state[lane_c] = c2;
            state[lane_d] = d2;
        }
    }

    // out[w] = h[w] ^ v[w] ^ v[w+8], the only materialized words.
    for word in 0..8 {
        let out = xor(xor(state[word], state[word + 8]), rows.slots(32 * word));
        rows.linear_rows(out, 256 + 32 * word);
    }

    rows.left_values[constant] = column_weights[constant];
    rows.right_values[constant] = column_weights[constant];
    (rows.left_values, rows.right_values)
}

/// The reduction in protocol order: zerocheck, then lincheck. What it leaves is the
/// point and the 64 claims s\[i\] = z(i, point), i < 64, for ring switching to bind.
pub fn verify_flock(log_n: usize, transcript: &mut Transcript) -> Result<FlockClaims, VerifierError> {
    let zc = verify_flock_zerocheck(log_n, transcript)?;
    let (claims, running) = verify_lincheck(zc, FLOCK_NUM_LINCHECK_ROUNDS, transcript)?;
    if transcript.checked() {
        require(
            blake2s_terminal(&claims)? == running,
            VerifierError::FlockLincheckTerminal,
        )?;
    }
    Ok(claims)
}

// The Frobenius shifts of the six stages composing Phi, one challenge each.
const RING_MAP_SHIFTS: [usize; 6] = [32, 16, 8, 4, 2, 1];

/// The drawn map, stage by stage: `a_p+1 = a_p + f_p a_p^(2^shift)`.
fn ring_map(mut value: E, challenges: &[E]) -> E {
    for (&challenge, shift) in challenges.iter().zip(RING_MAP_SHIFTS) {
        value += challenge * value.pow(1 << shift);
    }
    value
}

/// The weight `W(u) = Phi(eq(r, u))`, extended and evaluated by the opening at
/// `r_prime`: `sum_k c_k prod_n (1 + r_n^(2^k) + r'_n)`.
fn ring_weight(r: &[E], r_prime: &[E], coefficients: &[E]) -> E {
    assert_eq!(r.len(), r_prime.len());
    let mut total = ZERO;
    let mut frobenius = r.to_vec();
    for &c in coefficients {
        let mut product = c;
        for (value, &challenge) in frobenius.iter_mut().zip(r_prime) {
            product *= ONE + *value + challenge;
            *value = value.square();
        }
        total += product;
    }
    total
}

/// The 64 claims s\[i\] = z(i, point) become the one dense claim `sum_u W(u) qflock(u) = target`.
///
/// Draw Phi once they are fixed, then take the target `T = sum_i x^i Phi(s_i)` against the
/// MLE-friendly weight `W(u) = Phi(eq(point, u))`. Returns the target and W as a closure.
pub fn ring_switch(point: Vec<E>, s: &[E], transcript: &mut Transcript) -> (E, impl Fn(&[E]) -> E + use<>) {
    let challenges = transcript.samples(RING_MAP_SHIFTS.len());
    // The same map as a Frobenius sum, `Phi(a) = sum_k c_k a^(2^k)` for k < 64.
    let coefficient = |k: usize| {
        let stages = challenges
            .iter()
            .zip(RING_MAP_SHIFTS)
            .filter(|&(_, shift)| k & shift != 0);
        stages.fold(ONE, |acc, (f, shift)| acc * f.pow(1 << (k % shift)))
    };
    let coefficients: Vec<E> = (0..K_BITS).map(coefficient).collect();
    let images: Vec<E> = s.iter().map(|&value| ring_map(value, &challenges)).collect();
    let target = poly_eval(&images, GEN);
    (target, move |r_prime: &[E]| ring_weight(&point, r_prime, &coefficients))
}
