//! Blocks and producers, the fingerprint over their tuples' slots, and where they stack in a side's leaf vector.

use primitives::PrimeCharacteristicRing;

use super::{BusError, Coord, PublicColumn};
use primitives::{F64, F192};

/// A flushing rule: `2^kappa` rows, each a tuple of coordinates. Every one of them is a
/// row the program executed, since a table's height is its row count (§sec:e2e-pad), so a
/// block has no padding rows to divide back out of the product.
#[derive(Clone, Debug)]
pub struct Block {
    pub kappa: usize,
    pub coords: Vec<Coord>,
    /// The table whose block it is, if any. A table's block becomes a form its table
    /// sumcheck settles; a framework block opens its columns at the bus point.
    pub owner: Option<usize>,
}

impl Block {
    /// A block no table owns.
    pub const fn framework(kappa: usize, coords: Vec<Coord>) -> Self {
        Self {
            kappa,
            coords,
            owner: None,
        }
    }

    /// A block of table `owner`.
    pub const fn table(owner: usize, kappa: usize, coords: Vec<Coord>) -> Self {
        Self {
            kappa,
            coords,
            owner: Some(owner),
        }
    }
}

/// A lookup array as its table side pushes it (§sec:lookup): `2^kappa` entries, entry `x`
/// the tuple `coords` at row `x`, pushed `m_x` times, `m_x` being the committed word
/// `col[x]` read as an integer. Bit `i` of it is a push block of its own, whose row `x`
/// is the entry's leaf raised to `2^i` where that bit is set and `1` where it is not, so
/// the bits' blocks together push entry `x` exactly `m_x` times. The bus reads the low
/// `bits` bits; the rest are zero.
#[derive(Clone, Debug)]
pub struct Producer {
    pub kappa: usize,
    pub coords: Vec<Coord>,
    pub col: usize,
    pub bits: usize,
}

/// Placement of each block in the stacked leaf vector (input order).
#[derive(Clone, Debug)]
pub struct Layout {
    pub mu: usize,
    pub offsets: Vec<usize>,
}

/// The fingerprint weights `eq(α⃗, x)` over the `2^N_TUPLE_BITS` slots (§sec:gp).
/// A tuple is fingerprinted as `Σ_x eq(α⃗, x)·σ_x`, a MULTILINEAR combination
/// rather than a power chain: each leaf factor is then of total degree
/// `N_TUPLE_BITS` in the challenges instead of the tuple width, and slot `x`'s
/// weight is an `eq` weight, which is what lets the aligned bytecode polynomial
/// be read off at `α⃗` itself (§sec:e2e-bc).
pub fn fingerprint_weights(alphas: &[F192]) -> Vec<F192> {
    debug_assert_eq!(alphas.len(), N_TUPLE_BITS);
    let mut w = vec![F192::ONE; 1 << N_TUPLE_BITS];
    for (bit, &a) in alphas.iter().enumerate() {
        for (x, wx) in w.iter_mut().enumerate() {
            *wx *= if (x >> bit) & 1 == 1 { a } else { a + F192::ONE };
        }
    }
    w
}

/// Bits indexing a bus tuple's coordinates: every tuple, the bytecode's widest at
/// fourteen, lives in the `2^4` slots of the bytecode encoding (§sec:m3, §sec:e2e-bc).
pub const N_TUPLE_BITS: usize = 4;

/// Bits the bus must clear: the target, plus what the commitment's list costs.
///
/// The fingerprint and the GKR challenges are drawn after the root, which binds the prover only to a list of polynomials.
/// Each challenge must hold against every member, so its error is multiplied by the list size (§sec:e2e-ledger).
pub(super) const BUS_SOUNDNESS_BITS: u32 = crate::SECURITY_BITS + ::pcs::whir::L0_LIST_BITS as u32;

/// Conservative sum of the degree bounds for every random-challenge failure in
/// the bus argument. A side's product has at most `factors` linear factors, counted
/// with multiplicity, each `β - π_α(t)` of total degree `N_TUPLE_BITS` in `(α⃗, β)`:
/// `N_TUPLE_BITS` in `α⃗`, one in `β`, and the total degree of a sum is the larger.
/// The second term covers all radix-four GKR batching and sumcheck challenges.
fn soundness_degree_bound(factors: u128, mu: usize) -> u128 {
    assert!(mu < u128::BITS as usize, "bus layout is too large to bound");
    let fingerprint = N_TUPLE_BITS as u128 * factors;
    let gkr = 8u128 * (mu as u128 + 1).pow(2);
    fingerprint + gkr
}

pub(super) fn soundness_bits(factors: u128, mu: usize) -> u32 {
    let degree = soundness_degree_bound(factors, mu);
    192u32.saturating_sub(u128::BITS - degree.leading_zeros())
}

/// The linear factors a side's product has, counted with multiplicity: one per row
/// of a block, and up to `2^bits - 1` per entry of a producer.
fn factors(blocks: &[Block], producers: &[Producer]) -> u128 {
    let rows: u128 = blocks.iter().map(|b| 1u128 << b.kappa).sum();
    rows + producers
        .iter()
        .map(|p| (1u128 << p.kappa) * ((1u128 << p.bits) - 1))
        .sum::<u128>()
}

/// Check that the 192-bit challenge field and the grinding give the bus its margin.
///
/// # Why grinding counts
///
/// - A proof of work of `g` bits before the fingerprint challenges makes each draw of them cost `2^g` hashes.
/// - So the fingerprint's error counts `g` bits fewer against the margin (§sec:e2e-ledger).
/// - The GKR's own terms are far below the margin, so the grinding before the fingerprint covers the sum.
///
/// # Errors
///
/// A layout whose products have too many factors for the margin.
pub(super) fn check_soundness(
    push_blocks: &[Block],
    pull_blocks: &[Block],
    producers: &[Producer],
    mu: usize,
    grinding: u32,
) -> Result<(), BusError> {
    let widest = push_blocks
        .iter()
        .chain(pull_blocks)
        .map(|block| block.coords.len())
        .chain(producers.iter().map(|p| p.coords.len()))
        .max()
        .unwrap_or(0);
    assert!(widest <= 1 << N_TUPLE_BITS, "a tuple's coordinates index its slots");
    let factors = factors(push_blocks, producers).max(factors(pull_blocks, &[]));
    let bits = soundness_bits(factors, mu);
    if bits + grinding < BUS_SOUNDNESS_BITS {
        return Err(BusError::Soundness {
            bits,
            grinding,
            required: BUS_SOUNDNESS_BITS,
        });
    }
    Ok(())
}

/// Stack blocks largest-first at aligned offsets; `μ = ⌈log2 Σ 2^{κ_b}⌉`. A producer's
/// bits are blocks too, after `blocks`, in order.
pub fn layout(blocks: &[Block], producers: &[Producer]) -> Layout {
    let kappas: Vec<Option<usize>> = blocks
        .iter()
        .map(|b| b.kappa)
        .chain(producers.iter().flat_map(|p| std::iter::repeat_n(p.kappa, p.bits)))
        .map(Some)
        .collect();
    let (offsets, placed) = crate::witness::stack_offsets(&kappas);
    Layout {
        mu: crate::log2_ceil_usize(placed.max(1)),
        offsets,
    }
}

/// Selector bits of the stacked bytecode polynomial: the public encoding
/// columns stack along `2^N_BYTECODE_SELECTORS` slots. A column's slot is its bus
/// tuple coordinate, which is what fixes the width at sixteen rather than at the
/// column count.
pub const N_BYTECODE_SELECTORS: usize = 4;

/// Slot of the first public column: the bytecode tuple leads with two coordinates
/// that are not the program's (the separator and the address), and a column's slot IS
/// its bus tuple coordinate.
pub const BYTECODE_PUBLIC_SLOT: usize = 2;

/// The stacked bytecode polynomial as a dense table: the public encoding columns of a
/// `2^kbc`-entry tuple at their tuple coordinates, padded to sixteen selector slots.
/// The program's digest is taken over it ([`crate::cpu::Program`]).
pub fn stacked_bytecode_table(kbc: usize, coords: &[Coord]) -> Vec<F64> {
    let mut table = vec![F64::ZERO; 1 << (N_BYTECODE_SELECTORS + kbc)];
    for (slot, c) in coords.iter().enumerate() {
        if let Coord::Public(PublicColumn { values: vals, .. }) = c {
            assert!(slot >= BYTECODE_PUBLIC_SLOT, "the program's columns follow the address");
            assert!(slot < 1 << N_BYTECODE_SELECTORS, "a public slot is a tuple coordinate");
            assert_eq!(vals.len(), 1 << kbc);
            table[(slot << kbc)..((slot + 1) << kbc)].copy_from_slice(vals);
        }
    }
    table
}
