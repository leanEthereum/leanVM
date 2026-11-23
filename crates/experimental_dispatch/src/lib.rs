//! The experimental prover, compiled once per CPU tier (`crates/experimental_tiers`), run in the fastest tier this CPU
//! supports.

use isa::{Program, Prover, Stats};
use std::sync::OnceLock;
use verifier::{E, Proof};

/// The experimental prover, dispatched on the CPU.
pub struct ExperimentalProver;

macro_rules! detected {
    ("x86_64", $feature:tt) => {
        std::arch::is_x86_feature_detected!($feature)
    };
    ("aarch64", $feature:tt) => {
        std::arch::is_aarch64_feature_detected!($feature)
    };
}

macro_rules! tiers {
    ($($arch:tt: [$($tier:ident: [$($feature:tt),*],)*])*) => {
        /// A copy of the prover: the build's own (`Base`), or one compiled with a tier's target features.
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        #[allow(non_camel_case_types)]
        pub enum Tier {
            Base,
            $($(#[cfg(target_arch = $arch)] $tier,)*)*
        }

        /// Every tier this build holds, fastest first, with its name and the target features it is compiled with.
        pub const TIERS: &[(Tier, &str, &[&str])] = &[
            $($(#[cfg(target_arch = $arch)] (Tier::$tier, stringify!($tier), &[$($feature),*]),)*)*
            (Tier::Base, "base", &[]),
        ];

        impl Tier {
            /// Whether this CPU runs the tier and it adds a feature the build's own lacks.
            pub fn runs_here(self) -> bool {
                match self {
                    Tier::Base => true,
                    $($(
                        #[cfg(target_arch = $arch)]
                        Tier::$tier => !cfg!(all($(target_feature = $feature),*)) $(&& detected!($arch, $feature))*,
                    )*)*
                }
            }

            fn prove(
                self,
                program: &Program,
                witness: &[(String, Vec<Vec<E>>)],
                public_input: [E; 2],
                log_inv_rate: usize,
            ) -> Result<(Proof, Stats), String> {
                match self {
                    Tier::Base => base::ExperimentalProver::prove(program, witness, public_input, log_inv_rate),
                    $($(
                        #[cfg(target_arch = $arch)]
                        Tier::$tier => $tier::ExperimentalProver::prove(program, witness, public_input, log_inv_rate),
                    )*)*
                }
            }

            fn combine_rows(self, rows: &[u64], weights: &[E]) -> Vec<E> {
                match self {
                    Tier::Base => base::ExperimentalProver::combine_rows(rows, weights),
                    $($(
                        #[cfg(target_arch = $arch)]
                        Tier::$tier => $tier::ExperimentalProver::combine_rows(rows, weights),
                    )*)*
                }
            }

            fn dot_rows(self, rows: &[u64], weights: &[E]) -> Vec<E> {
                match self {
                    Tier::Base => base::ExperimentalProver::dot_rows(rows, weights),
                    $($(
                        #[cfg(target_arch = $arch)]
                        Tier::$tier => $tier::ExperimentalProver::dot_rows(rows, weights),
                    )*)*
                }
            }
        }

        /// Runs `visitor` once per tier this CPU runs, on that tier's prover.
        #[doc(hidden)]
        pub fn __for_each_tier(visitor: &mut impl __TierVisitor) {
            $($(
                #[cfg(target_arch = $arch)]
                if Tier::$tier.runs_here() {
                    visitor.visit::<$tier::ExperimentalProver>(Tier::$tier);
                }
            )*)*
            visitor.visit::<base::ExperimentalProver>(Tier::Base);
        }
    };
}

// The features `crates/experimental_tiers/generate.sh` gives each tier.
tiers! {
    "x86_64": [
        x86v4gfni: ["avx2", "bmi1", "bmi2", "fma", "lzcnt", "movbe", "f16c", "popcnt", "pclmulqdq", "avx512f", "avx512bw",
            "avx512cd", "avx512dq", "avx512vl", "vpclmulqdq", "gfni", "avx512vbmi"],
        x86v4: ["avx2", "bmi1", "bmi2", "fma", "lzcnt", "movbe", "f16c", "popcnt", "pclmulqdq", "avx512f", "avx512bw",
            "avx512cd", "avx512dq", "avx512vl"],
        x86v3gfni: ["avx2", "bmi1", "bmi2", "fma", "lzcnt", "movbe", "f16c", "popcnt", "pclmulqdq", "vpclmulqdq", "gfni"],
        x86v3clmul: ["avx2", "bmi1", "bmi2", "fma", "lzcnt", "movbe", "f16c", "popcnt", "pclmulqdq", "vpclmulqdq"],
        x86v3: ["avx2", "bmi1", "bmi2", "fma", "lzcnt", "movbe", "f16c", "popcnt", "pclmulqdq"],
    ]
    "aarch64": [
        armsha3: ["aes", "sha3"],
        armaes: ["aes"],
    ]
}

/// The tier proving runs in: the fastest this CPU runs, or the one `LEANVM_TIER` names if this CPU runs it.
pub fn tier() -> Tier {
    static TIER: OnceLock<Tier> = OnceLock::new();
    *TIER.get_or_init(|| {
        let forced = std::env::var("LEANVM_TIER").ok();
        let running = || TIERS.iter().filter(|(tier, _, _)| tier.runs_here());
        let named = running().find(|(_, name, _)| forced.as_deref() == Some(*name));
        named
            .or_else(|| running().next())
            .expect("the base tier runs everywhere")
            .0
    })
}

/// Code generic over the prover, run once per tier by [`__for_each_tier`].
#[doc(hidden)]
pub trait __TierVisitor {
    fn visit<P: Prover>(&mut self, tier: Tier);
}

impl Prover for ExperimentalProver {
    const NAME: &'static str = "experimental";

    fn init() {
        parallel::init();
    }

    fn set_num_threads(n: usize) {
        parallel::set_num_threads(n)
    }

    fn prove(
        program: &Program,
        witness: &[(String, Vec<Vec<E>>)],
        public_input: [E; 2],
        log_inv_rate: usize,
    ) -> Result<(Proof, Stats), String> {
        tier().prove(program, witness, public_input, log_inv_rate)
    }

    fn map_collect<T: Send>(n: usize, f: impl Fn(usize) -> T + Sync) -> Vec<T> {
        parallel::map_collect(n, f)
    }

    fn combine_rows(rows: &[u64], weights: &[E]) -> Vec<E> {
        tier().combine_rows(rows, weights)
    }

    fn dot_rows(rows: &[u64], weights: &[E]) -> Vec<E> {
        tier().dot_rows(rows, weights)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each tier's runtime checks are the target features its copies are compiled with.
    #[test]
    fn tiers_check_the_features_they_are_compiled_with() {
        let crates = [
            "keccak256",
            "fiat_shamir_prover",
            "experimental_primitives",
            "experimental_pcs",
            "experimental_keccak_gkr",
            "experimental_lean_vm_core",
        ];
        for &(_, name, features) in TIERS.iter().filter(|(tier, _, _)| *tier != Tier::Base) {
            for krate in crates {
                let path = format!(
                    "{}/../experimental_tiers/{name}/{krate}/Cargo.toml",
                    env!("CARGO_MANIFEST_DIR")
                );
                let manifest = std::fs::read_to_string(&path).unwrap();
                let line = manifest
                    .lines()
                    .find_map(|l| l.strip_prefix("target-features = "))
                    .unwrap();
                let compiled: Vec<&str> = line
                    .trim_matches('"')
                    .split(',')
                    .map(|f| f.trim_start_matches('+'))
                    .collect();
                assert_eq!(compiled, features, "{path}");
            }
        }
    }
}
