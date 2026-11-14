//! LeanDA's membership challenge, which the statement of an aggregate binds with its root.
//!
//! A blob row is a codeword iff it is orthogonal to `L(X) = prod_j (1 + z^(2^j) * Vhat_j(X))`, `Vhat_j` the
//! normalized subspace polynomial of degree `2^j` (doc/leanvm annex D). The guest builds `L` from `z`; the verifier
//! derives `z` from the root here, outside the SNARK.

use crate::field::E;
use crate::hash::{Digest, keccak_hash};
use crate::merkle::hash_pair;
use crate::transcript::{Sponge, grinding_bits};

const LABEL: &[u8] = b"leanDA/rs-membership/v1";

/// `log2(k)`, `k` the blob's symbols (`lean_da::LOG_BLOB_SYMBOLS`).
pub const LOG_BLOB_SYMBOLS: usize = 13;

/// A non-codeword passes for at most `k - 1` values of `z`: the error numerator the grind is for.
const MEMBERSHIP_GRINDING_BITS: u32 = grinding_bits((1 << LOG_BLOB_SYMBOLS) - 1);

/// `z`: the VM's transcript seeded with the label's hash as its IV and the root as its public input, then ground with
/// the smallest valid nonce, then squeezed once.
///
/// The nonce search is the grind: anyone trying roots for a bad `z` pays `2^MEMBERSHIP_GRINDING_BITS` permutations a
/// root, and so does the verifier, about that many per blob root.
pub fn membership_challenge(root: &[u8; 32]) -> E {
    let sponge = Sponge::new(keccak_hash(LABEL), Digest(*root));
    let mask = (1u64 << MEMBERSHIP_GRINDING_BITS) - 1;
    (0..)
        .find_map(|nonce| {
            let mut ground = sponge.clone();
            (ground.absorb_nonce(E::new(nonce, 0)) & mask == 0).then(|| ground.sample())
        })
        .expect("a nonce exists")
}

/// What the statement of an aggregate carries for its DA root: `H(root ‖ z)`, `z` as its two little-endian limbs
/// and two zero words, or zeros without a root.
pub fn digest(root: Option<[u8; 32]>) -> [u8; 32] {
    root.map_or([0; 32], |root| {
        let z = membership_challenge(&root);
        hash_pair(&root, [z.c0, z.c1, 0, 0].map(u64::to_le_bytes).as_flattened()).0
    })
}
