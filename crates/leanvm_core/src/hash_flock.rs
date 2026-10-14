//! Bridge to the flock BLAKE2s prover ([`flock::hash`]), single-PCS.
//!
//! `q_flock` (flock's packed BLAKE2s witness, 64 bits per `F64` word) is committed
//! as a column in leanVM's ONE stacked `F64` witness (§sec:stacking), with no separate flock
//! commitment. The VM's `BLAKE2s` table binds to it by point-eval equality (its
//! value columns and `q_flock`'s slots are point-evals of the same committed
//! stack), and flock's R1CS validity is discharged by the same stacked WHIR:
//! the reduction's claim passes through [`ring_switch_open`] and joins the
//! batch-mixed opening ([`::pcs::stack_open`]).
//!
//! ## The mapping
//!
//! The VM's `BLAKE2s(a, b, cv, metadata) -> c` is one standard BLAKE2s
//! compression. `metadata` packs `counter:u64 | f0:u32 | f1:u32` in
//! little-endian order. All inputs are witness values in `q_flock`, and the
//! memory interaction binds every one of them: `a`, `b`, `cv` and `metadata`
//! are cells the instruction reads.
//!
//! ## The layout (aligned re-layout, `MSG_BASE = 640`, 64-bit words)
//!
//! Each compression's `2^K_LOG` bits pack into `2^(K_LOG-6)` `F64` words (the
//! [`SLOT_STRIDE_LOG`] stride); each VM-visible 64-bit word is one whole packed
//! word at a fixed within-instance slot (bit position / 64):
//!
//! ```text
//!   c0..c3 = slots 4..8      a0..a3 = slots 10..14    b0..b3 = slots 14..18
//!   cv0..cv3 = slots 0..4    counter = slot 18        f0‖f1 = slot 19
//! ```
//!
//! All compression inputs are free witness rows; the VM routes claims on all
//! eighteen aligned words directly to these slots.

use crate::transcript::ProverState;
use ::pcs::pack::LOG_PACKING;
use flock::hash::{Blake2sSetup, Compression, K_LOG, blake2s_compress, generate_witness_with_ab_packed_and_lincheck};
use primitives::field::{F64, F192};
use primitives::stream::Stream;

pub use flock::hash::{SliceClaim, min_n_blocks_log as n_blocks_log, qflock_kappa, ring_switch_open};

/// BLAKE2s's final-block flag `f0`, which RFC 7693 sets to all ones on the last
/// block. A hash-shaped compression is one 64-byte final block, so it is always
/// set there.
pub const FINAL_FLAG: u32 = flock::hash::PINNED_F0;
/// The byte counter of the one 64-byte block a hash-shaped compression absorbs.
pub const PINNED_T: u64 = flock::hash::PINNED_T;

/// Flock-native reduction buffers emitted in the same fused pass as the
/// committed, flattened `q_flock`. They stay alive across commit, bus, and
/// constraint proving so reduction needs no second witness pass.
pub(crate) struct PreparedReductionWitness {
    n_blocks: usize,
    z_packed: Vec<u64>,
    a_packed: Vec<u64>,
    b_packed: Vec<u64>,
    z_lincheck: Vec<u8>,
}

impl PreparedReductionWitness {
    pub(crate) fn n_blocks(&self) -> usize {
        self.n_blocks
    }

    pub(crate) fn prove(&self, ps: &mut ProverState) -> SliceClaim {
        Blake2sSetup::new(self.n_blocks).prove_reduction_precomputed(
            &self.z_packed,
            &self.a_packed,
            &self.b_packed,
            &self.z_lincheck,
            ps,
        )
    }
}

// Within-instance packed-word (slot) indices of the VM-visible words, fixed by
// the aligned flock layout (bit bases asserted by `layout_constants` there):
// `CV_BASE = 0` → cv words 0..4, `OUT_BASE = 256` → c words 4..8, `MSG_BASE
// = 640` → a words 10..14 and b words 14..18, metadata (counter, f0‖f1)
// words 18..20.
pub const SLOT_CV0: usize = 0;
pub const SLOT_C0: usize = 4;
pub const SLOT_A0: usize = 10;
pub const SLOT_B0: usize = 14;
pub const SLOT_METADATA: usize = 18;

/// The eighteen within-instance value slots in canonical order
/// `[a0..a3, b0..b3, c0..c3, cv0..cv3, md_lo, md_hi]`, matching
/// `tables::BLAKE2S_VALUE_COLS`.
pub const SLOTS: [usize; 18] = [
    SLOT_A0,
    SLOT_A0 + 1,
    SLOT_A0 + 2,
    SLOT_A0 + 3,
    SLOT_B0,
    SLOT_B0 + 1,
    SLOT_B0 + 2,
    SLOT_B0 + 3,
    SLOT_C0,
    SLOT_C0 + 1,
    SLOT_C0 + 2,
    SLOT_C0 + 3,
    SLOT_CV0,
    SLOT_CV0 + 1,
    SLOT_CV0 + 2,
    SLOT_CV0 + 3,
    SLOT_METADATA,
    SLOT_METADATA + 1,
];

/// Split a 64-bit field element into the two little-endian `u32` words flock's
/// message uses (the VM memory byte order).
fn words_of(x: F64) -> [u32; 2] {
    [x.0 as u32, (x.0 >> 32) as u32]
}

/// Inverse of `words_of`: pack two little-endian `u32` words into the `F64`.
fn pack_words(w: [u32; 2]) -> F64 {
    F64((w[0] as u64) | ((w[1] as u64) << 32))
}

/// Pack BLAKE2s's compression metadata as one little-endian 128-bit value in
/// the two low K-lanes of a 192-bit word (top lane zero).
pub const fn metadata(counter: u64, f0: u32, f1: u32) -> F192 {
    F192::new(counter, (f0 as u64) | ((f1 as u64) << 32), 0)
}

/// Unpack `counter:u64 | f0:u32 | f1:u32` from a 192-bit word (the top lane
/// must be zero).
pub const fn unpack_metadata(x: F192) -> (u64, u32, u32) {
    assert!(x.c2 == 0, "BLAKE2s metadata must have a zero top lane");
    (x.c0, x.c1 as u32, (x.c1 >> 32) as u32)
}

/// BLAKE2s-256's initial chaining value as four flock words (the two
/// chaining-value cells' low lanes, in canonical lane order). This is the IV
/// with the parameter block (digest length 32, unkeyed, fanout and depth 1)
/// folded into word 0, which is what makes a 64-byte compression equal
/// `blake2s` of those 64 bytes.
///
/// Derived from [`flock::hash::param_iv`] rather than written out: the
/// parameter block touches three bytes of word 0, and a hand-copied constant
/// that XORs only the low byte still looks plausible.
pub const IV: [F64; 4] = {
    const fn w(lo: u32, hi: u32) -> F64 {
        F64((lo as u64) | ((hi as u64) << 32))
    }
    let h = flock::hash::param_iv();
    [w(h[0], h[1]), w(h[2], h[3]), w(h[4], h[5]), w(h[6], h[7])]
};

/// The initial chaining value as the two 192-bit VM memory cells a chaining
/// value occupies (canonical 128-bit chunks, top limbs zero).
pub const IV_CELLS: [F192; 2] = [F192::new(IV[0].0, IV[1].0, 0), F192::new(IV[2].0, IV[3].0, 0)];

/// The flock [`Compression`] for one VM instruction.
pub fn compression(a: [F64; 4], b: [F64; 4], cv: [F64; 4], meta: F192) -> Compression {
    let mut m = [0u32; 16];
    for (i, &w) in a.iter().enumerate() {
        m[2 * i..2 * i + 2].copy_from_slice(&words_of(w));
    }
    for (i, &w) in b.iter().enumerate() {
        m[8 + 2 * i..8 + 2 * i + 2].copy_from_slice(&words_of(w));
    }
    let mut cv_words = [0u32; 8];
    for (i, &w) in cv.iter().enumerate() {
        cv_words[2 * i..2 * i + 2].copy_from_slice(&words_of(w));
    }
    let (counter, f0, f1) = unpack_metadata(meta);
    (cv_words, m, counter, f0, f1)
}

/// The 256-bit output chaining value `c = (c0..c3)` of an arbitrary
/// compression. This is `blake2s(a‖b)` only for the parameterized [`IV`] and
/// one-block final metadata (counter 64, `f0` set).
pub fn digest(block: &Compression) -> [F64; 4] {
    let h = blake2s_compress(&block.0, &block.1, block.2, block.3, block.4);
    std::array::from_fn(|k| pack_words([h[2 * k], h[2 * k + 1]]))
}

/// Lift flock's packed witness (64 bits per word, bit `i` at position `i`) into
/// the committed `F64` column: word for word, which is exactly `pcs::pack`'s
/// LSB-first convention on the same bit string.
fn flatten_packed_into(packed: &[u64], out: &mut [F64]) {
    assert_eq!(out.len(), packed.len(), "q_flock's window is the wrong size");
    // Write directly into the committed window and publish it with streaming stores.
    // SAFETY: `F64` is `repr(transparent)` over `u64`, so the two slices are the
    // same bytes.
    let words: &mut [u64] = unsafe { std::slice::from_raw_parts_mut(out.as_mut_ptr().cast(), out.len()) };
    parallel::chunks_mut_zip(words, packed, 1 << 14, |_, dst, src| Stream::new().copy(dst, src));
}

/// Build the committed `q_flock` column (flock's packed witness) for `blocks`, padded
/// to `2^n_blocks_log(max(blocks.len(),1))` instances (the unused ones flock's own
/// `padding_block`), and retain the Flock-native layouts produced by that same fused pass so
/// reduction does not regenerate them later. Deterministic, so it matches what the
/// reduction regenerates. An empty `blocks` yields one padding cube (all instances are
/// padding).
pub(crate) fn build_qflock_prepared(blocks: &[Compression], q_flock: &mut [F64]) -> PreparedReductionWitness {
    let n_blocks = blocks.len().max(1);
    let (z_packed, a_packed, b_packed, z_lincheck) =
        generate_witness_with_ab_packed_and_lincheck(blocks, n_blocks_log(n_blocks));
    flatten_packed_into(&z_packed, q_flock);
    PreparedReductionWitness {
        n_blocks,
        z_packed,
        a_packed,
        b_packed,
        z_lincheck,
    }
}

/// `log2` of the within-instance packed span (`2^8` words): the
/// number of low coords of a `q_flock` point that carry the slot's bits, and the
/// stride between consecutive instances' same-slot words in `q_flock`. A value
/// claim on `q_flock` is thus a boolean-selector (strided) claim with this stride.
pub const SLOT_STRIDE_LOG: usize = K_LOG - LOG_PACKING;

/// `q_flock` on its own, for the tests that only need the committed column.
#[cfg(test)]
fn build_qflock(blocks: &[Compression]) -> Vec<F64> {
    let mut q_flock = vec![F64::ZERO; 1 << qflock_kappa(blocks.len())];
    build_qflock_prepared(blocks, &mut q_flock);
    q_flock
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(x: u64) -> F64 {
        F64(x)
    }

    /// `q_flock`'s aligned packed slots hold the VM's 64-bit words in our field
    /// representation, and the digest matches the `blake2s` crate.
    #[test]
    fn qflock_words_match_layout() {
        let inputs: Vec<([F64; 4], [F64; 4])> = (0..5u64)
            .map(|i| {
                (
                    [f(0x1000 + i), f(0x2000 + i), f(0x3000 + i), f(0x4000 + i)],
                    [f(0x5000 + i), f(0x6000 + i), f(0x7000 + i), f(0x8000 + i)],
                )
            })
            .collect();
        let blocks: Vec<Compression> = inputs
            .iter()
            .map(|&(a, b)| compression(a, b, IV, metadata(PINNED_T, FINAL_FLAG, 0)))
            .collect();
        let q_flock = build_qflock(&blocks);
        assert_eq!(q_flock.len(), 1 << qflock_kappa(blocks.len()));

        let slot = |j: usize, s: usize| q_flock[j * (1 << SLOT_STRIDE_LOG) + s];
        for (j, (&(a, b), blk)) in inputs.iter().zip(&blocks).enumerate() {
            for k in 0..4 {
                assert_eq!(slot(j, SLOT_A0 + k), a[k]);
                assert_eq!(slot(j, SLOT_B0 + k), b[k]);
            }
            let mut input = [0u8; 64];
            for (s, w) in input.as_chunks_mut::<8>().0.iter_mut().zip(a.into_iter().chain(b)) {
                *s = w.0.to_le_bytes();
            }
            let h = primitives::hash::hash(&input);
            let word = |o: usize| F64(u64::from_le_bytes(h[o..o + 8].try_into().unwrap()));
            let d: [F64; 4] = std::array::from_fn(|k| word(8 * k));
            assert_eq!(digest(blk), d);
            for k in 0..4 {
                assert_eq!(slot(j, SLOT_C0 + k), d[k]);
            }
        }
        // Input slots for this one-block hash: the parameterized initial chaining
        // value in slots 0..4, the byte counter in slot 18, and the packed
        // f0‖f1 flag word in slot 19.
        let iv = flock::hash::param_iv();
        for k in 0..4 {
            assert_eq!(slot(0, k), pack_words([iv[2 * k], iv[2 * k + 1]]));
        }
        assert_eq!(slot(0, 18), pack_words([PINNED_T as u32, 0]));
        assert_eq!(slot(0, 19), pack_words([FINAL_FLAG, 0]));
    }
}
