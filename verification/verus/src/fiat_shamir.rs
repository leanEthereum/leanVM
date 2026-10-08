//! The block of a Fiat-Shamir transcript step.
//!
//! The executable functions are `step_block` of `crates/fiat_shamir/src/lib.rs` and the message the circuit's
//! `Builder::step` (`crates/leanvm_core/src/rec/circuit/builder/hash.rs`) hashes for the same step;
//! `tests/equivalence/fiat_shamir.rs` checks the first against production. Where Verus rejects the production form
//! (slice patterns, `Option::map_or` with a closure, the panic on a long slice), the copy spells it out; each such
//! spot says what it replaces.
//!
//! Specification: [`block_word`] is word `i` of the block of a step absorbing `scalars` under `tag`: the last
//! scalar in words 4 to 6, the one before it (if any) in words 0 to 2, their count in word 3, the tag in word 7, and
//! zero in the words no scalar fills. On the steps production takes (at most [`MAX_PENDING`] scalars) the block
//! determines the scalars and the tag ([`lemma_step_block_decodes`]), so two steps with the same block absorb the
//! same scalars under the same tag ([`lemma_step_block_injective`]).
use crate::gf2_64::F64;
use crate::gf2_64x3::F192;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------------------------
/// The scalar in words 0 to 2: the one before the last, or zero.
pub open spec fn first_scalar(scalars: Seq<F192>) -> F192 {
    if scalars.len() == 2 {
        scalars[0]
    } else {
        F192::ZERO
    }
}

/// The scalar in words 4 to 6: the last, or zero.
pub open spec fn last_scalar(scalars: Seq<F192>) -> F192 {
    if scalars.len() >= 1 {
        scalars[scalars.len() - 1]
    } else {
        F192::ZERO
    }
}

/// Word `i` of the block of a step absorbing `scalars` under `tag`.
pub open spec fn block_word(scalars: Seq<F192>, tag: u64, i: int) -> u64 {
    let (a, b) = (first_scalar(scalars), last_scalar(scalars));
    if i == 0 {
        a.c0
    } else if i == 1 {
        a.c1
    } else if i == 2 {
        a.c2
    } else if i == 3 {
        scalars.len() as u64
    } else if i == 4 {
        b.c0
    } else if i == 5 {
        b.c1
    } else if i == 6 {
        b.c2
    } else {
        tag
    }
}

/// The scalars a block names: its word 3 counts them, the last is in words 4 to 6, the one before it in words 0 to 2.
pub open spec fn decode_scalars(w: spec_fn(int) -> u64) -> Seq<F192> {
    let a = F192 { c0: w(0), c1: w(1), c2: w(2) };
    let b = F192 { c0: w(4), c1: w(5), c2: w(6) };
    if w(3) == 0 {
        seq![]
    } else if w(3) == 1 {
        seq![b]
    } else {
        seq![a, b]
    }
}

// ---------------------------------------------------------------------------------------------
// Theorems
// ---------------------------------------------------------------------------------------------
/// A step's block names its scalars and its tag: decoding the block returns them.
pub proof fn lemma_step_block_decodes(scalars: Seq<F192>, tag: u64)
    requires
        scalars.len() <= MAX_PENDING,
    ensures
        decode_scalars(|i: int| block_word(scalars, tag, i)) == scalars,
        block_word(scalars, tag, 7) == tag,
{
    let d = decode_scalars(|i: int| block_word(scalars, tag, i));
    if scalars.len() == 0 {
        assert(d =~= scalars);
    } else if scalars.len() == 1 {
        assert(d =~= scalars);
    } else {
        assert(d =~= scalars);
    }
}

/// Injectivity: two steps of at most [`MAX_PENDING`] scalars with the same block absorb the same scalars (so the
/// same count) under the same tag.
pub proof fn lemma_step_block_injective(s1: Seq<F192>, t1: u64, s2: Seq<F192>, t2: u64)
    requires
        s1.len() <= MAX_PENDING,
        s2.len() <= MAX_PENDING,
        forall|i: int| 0 <= i < 8 ==> #[trigger] block_word(s1, t1, i) == block_word(s2, t2, i),
    ensures
        s1 == s2,
        t1 == t2,
{
    lemma_step_block_decodes(s1, t1);
    lemma_step_block_decodes(s2, t2);
    let (w1, w2) = (|i: int| block_word(s1, t1, i), |i: int| block_word(s2, t2, i));
    assert(w1(0) == w2(0) && w1(1) == w2(1) && w1(2) == w2(2) && w1(3) == w2(3));
    assert(w1(4) == w2(4) && w1(5) == w2(5) && w1(6) == w2(6) && w1(7) == w2(7));
    assert(decode_scalars(w1) == decode_scalars(w2));
}

/// The domain-separation tags are pairwise distinct, so the blocks of two roles never coincide.
pub proof fn lemma_tags_distinct()
    ensures
        DS_OBSERVE.0 != DS_SQUEEZE.0,
        DS_OBSERVE.0 != DS_POW_BASE.0,
        DS_OBSERVE.0 != DS_POW_NONCE.0,
        DS_SQUEEZE.0 != DS_POW_BASE.0,
        DS_SQUEEZE.0 != DS_POW_NONCE.0,
        DS_POW_BASE.0 != DS_POW_NONCE.0,
{
}

// ---------------------------------------------------------------------------------------------
// Executable code
// ---------------------------------------------------------------------------------------------
/// The tag of an absorbed scalar.
pub const DS_OBSERVE: F64 = F64(1);

/// The tag of a challenge.
pub const DS_SQUEEZE: F64 = F64(2);

/// The tag of the proof-of-work base.
pub const DS_POW_BASE: F64 = F64(3);

/// The tag of a grinding nonce.
pub const DS_POW_NONCE: F64 = F64(4);

/// The most scalars one transcript step absorbs.
pub const MAX_PENDING: usize = 2;

/// The 64-byte block of a transcript step absorbing `scalars` (at most [`MAX_PENDING`]) under `tag`.
///
/// Production matches slice patterns and panics on a longer slice; the copy indexes, and the panic is a `requires`.
pub fn step_block(scalars: &[F192], tag: F64) -> (r: [F64; 8])
    requires
        scalars.len() <= MAX_PENDING,
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] r[i].0 == block_word(scalars@, tag.0, i),
{
    let (first, last) = if scalars.len() == 2 {
        (scalars[0], scalars[1])
    } else if scalars.len() == 1 {
        (F192::ZERO, scalars[0])
    } else {
        (F192::ZERO, F192::ZERO)
    };
    let count = F64(scalars.len() as u64);
    [
        F64(first.c0),
        F64(first.c1),
        F64(first.c2),
        count,
        F64(last.c0),
        F64(last.c1),
        F64(last.c2),
        tag,
    ]
}

/// The message `Builder::step` hashes, over the values of its wires: `scalars` are the values of the absorbed
/// wires and `F192::ZERO` the value of the zero wire.
///
/// Production asserts the length, matches slice patterns into an `Option` and reads it with `map_or`; the copy
/// indexes and matches, and the assert is a `requires`. The wire reads `self.e(..)` are the values themselves.
pub fn builder_step_message(scalars: &[F192], tag: u64) -> (m: [u64; 8])
    requires
        scalars.len() <= 2,
    ensures
        forall|i: int| 0 <= i < 8 ==> #[trigger] m[i] == block_word(scalars@, tag, i),
{
    let count = scalars.len() as u64;
    let zero = F192::ZERO;
    let (first, last) = if scalars.len() == 2 {
        (Some(scalars[0]), scalars[1])
    } else if scalars.len() == 1 {
        (None, scalars[0])
    } else {
        (None, zero)
    };
    let a = match first {
        Some(a) => a,
        None => F192::ZERO,
    };
    let b = last;
    [a.c0, a.c1, a.c2, count, b.c0, b.c1, b.c2, tag]
}

} // verus!
