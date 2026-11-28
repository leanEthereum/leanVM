//! The guest every node proves, compiled or installed, and what every prover and verifier derives from it once.

use fiat_shamir_prover::merkle::hash_to_scalars;
use isa::Program;
use primitives::field::F128;
use std::sync::OnceLock;

static GUEST: OnceLock<Program> = OnceLock::new();

/// The aggregation bytecode, compiled to a fixed point on its own size: the one fixed program every node proves, and
/// whose stacked bytecode every node's bytecode claims are about. Without the `compile-guest` feature, the one
/// [`set_unified_guest`] installed.
///
/// The recursion placeholders are a function of the inner bytecode's log size,
/// and here the inner bytecode is this one, so the size has to agree with
/// itself. The guess converges in one or two rounds because the map's only
/// size-dependent part is a handful of unrolled sumcheck rounds.
///
/// # Panics
/// Without `compile-guest`, if no guest is installed.
#[inline(never)]
pub fn unified_guest() -> &'static Program {
    #[cfg(feature = "compile-guest")]
    let guest = GUEST.get_or_init(super::placeholders::compile_unified_guest);
    #[cfg(not(feature = "compile-guest"))]
    let guest = GUEST
        .get()
        .expect("no aggregation guest: `set_unified_guest` installs one");
    guest
}

/// Install [`unified_guest`], compiled elsewhere and read back with `Program::from_bytes`, for a build without the
/// compiler: `false`, nothing installed and `program` leaked, if a guest is already in place.
pub fn set_unified_guest(program: Program) -> bool {
    GUEST.set(program).map_err(std::mem::forget).is_ok()
}

/// The guest's Fiat-Shamir IV as the two words a statement carries it in.
pub(super) fn fs_seed() -> [F128; 2] {
    hash_to_scalars(&unified_guest().fiat_shamir_iv())
}
