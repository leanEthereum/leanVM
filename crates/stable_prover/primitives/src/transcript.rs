//! The shared prover transcript ([`fiat_shamir_prover`]) on this tree's field, its long grinds on this tree's pool.

use crate::field::F128;

impl fiat_shamir_prover::Scalar for F128 {
    fn to_limbs(self) -> [u64; 2] {
        F128::to_limbs(self)
    }

    fn from_limbs(limbs: [u64; 2]) -> Self {
        F128::from_limbs(limbs)
    }
}

/// A grind's search on the pool ([`parallel::find_first`]).
pub struct Pool;

impl fiat_shamir_prover::Search for Pool {
    fn find_first(n: usize, f: &(dyn Fn(usize) -> bool + Sync)) -> Option<usize> {
        parallel::find_first(n, f)
    }
}

pub type ProverState = fiat_shamir_prover::ProverState<F128, Pool>;
