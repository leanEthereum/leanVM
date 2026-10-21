//! LeanDA's Reed-Solomon membership vector, which the statement of an aggregate binds through its hash.
//!
//! A blob row is a codeword iff it is orthogonal to `L(X) = prod_j (1 + z_j * Vhat_j(X))` over the domain, `Vhat_j`
//! the normalized subspace polynomial of degree `2^j` and `z` drawn from the commitment (doc/leanvm annex D for the basis).

use crate::field::{E, K, ONE, ZERO};
use crate::hash::keccak_hash;
use crate::transcript::Sponge;

const DA_LOG_K: usize = 14; // payload symbols per blob, as a logarithm
const LOG_M: usize = DA_LOG_K + 1; // the rate-1/2 codeword
const DA_LOG_CELL: usize = 8; // entries a column of the vector holds, as a logarithm
const LABEL: &[u8] = b"leanDA/rs-membership/v1";

/// `z_0 .. z_(log k - 1)`, drawn from a transcript of its own that has observed the commitment root.
pub fn membership_challenges(root: &[u8; 32]) -> Vec<E> {
    let word = |index: usize| u64::from_le_bytes(root.as_chunks().0[index]);
    let mut sponge = Sponge::from_label(LABEL);
    sponge.observe(E::new(word(0), word(1), 0));
    sponge.observe(E::new(word(2), word(3), 0));
    (0..DA_LOG_K).map(|_| sponge.sample()).collect()
}

/// Row `i` holds the subspace polynomial `s_i` at the basis elements `x^j`, `j >= i`, scaled so that its first entry is one.
fn subspace_evaluations() -> Vec<Vec<K>> {
    let mut rows = vec![(0..LOG_M).map(|j| K(1 << j)).collect::<Vec<K>>()];
    for i in 1..LOG_M {
        let previous = &rows[i - 1];
        let row = previous[1..]
            .iter()
            .map(|&value| value * (value + previous[0]))
            .collect();
        rows.push(row);
    }
    for row in &mut rows {
        let inverse = row[0].inv();
        for value in row {
            *value = *value * inverse;
        }
    }
    rows
}

/// Encode the novel-basis coefficients in the buffer's first half as their evaluations over the whole domain, in place.
///
/// The additive NTT, a butterfly at a time. Layer `l` works on blocks of `2^(LOG_M - l)` points, each with one twiddle.
/// A butterfly whose bottom input is zero copies its top input, so layer 0 of the zero-padded message is a copy.
fn encode(codeword: &mut [E]) {
    assert_eq!(codeword.len(), 1 << LOG_M);
    let evaluations = subspace_evaluations();
    codeword.copy_within(..1 << DA_LOG_K, 1 << DA_LOG_K);
    for layer in 1..LOG_M {
        let row = &evaluations[LOG_M - layer - 1][1..];
        for (block, points) in codeword.chunks_mut(1 << (LOG_M - layer)).enumerate() {
            // s_i is F2-linear, so the block's twiddle is the subset sum its index picks.
            let bits = (0..layer).filter(|bit| block >> bit & 1 == 1);
            let twiddle = bits.fold(K(0), |acc, bit| acc + row[bit]);
            let (top, bottom) = points.split_at_mut(points.len() / 2);
            for (u, v) in top.iter_mut().zip(bottom) {
                *u += *v * twiddle;
                *v += *u;
            }
        }
    }
}

/// `L` over the whole domain: the tensor of the `(1, z_j)`, encoded as a codeword.
pub fn dual_codeword(z: &[E]) -> Vec<E> {
    assert_eq!(z.len(), DA_LOG_K, "one challenge per novel-basis variable");
    let mut codeword = vec![ZERO; 1 << LOG_M];
    codeword[0] = ONE;
    for (j, &challenge) in z.iter().enumerate() {
        let (low, high) = codeword[..2 << j].split_at_mut(1 << j);
        for (h, &l) in high.iter_mut().zip(low.iter()) {
            *h = l * challenge;
        }
    }
    encode(&mut codeword);
    codeword
}

/// The test vector a commitment root determines.
pub fn membership_vector(root: &[u8; 32]) -> Vec<E> {
    dual_codeword(&membership_challenges(root))
}

/// The hash of the hashes of the vector's columns, `2^DA_LOG_CELL` entries each in domain order, a column hashed as
/// its entries' three little-endian limbs.
pub fn vector_digest(vector: &[E]) -> [u8; 32] {
    assert_eq!(vector.len(), 1 << LOG_M);
    let columns = vector.chunks(1 << DA_LOG_CELL).flat_map(|column| {
        let limbs = column.iter().flat_map(|value| [value.c0, value.c1, value.c2]);
        keccak_hash(&limbs.flat_map(u64::to_le_bytes).collect::<Vec<u8>>()).0
    });
    keccak_hash(&columns.collect::<Vec<u8>>()).0
}

/// The hash of the concatenated `(root, vector digest)` pairs, or of the empty string: what the statement of an aggregate carries for its DA roots.
pub fn list_digest(roots: &[[u8; 32]]) -> [u8; 32] {
    let pairs = roots
        .iter()
        .flat_map(|root| [*root, vector_digest(&membership_vector(root))]);
    keccak_hash(&pairs.flatten().collect::<Vec<u8>>()).0
}
