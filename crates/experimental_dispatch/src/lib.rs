//! The experimental prover, compiled once more per CPU tier (`crates/experimental_tiers`), run in the fastest tier
//! this CPU supports.

use isa::{Program, Prover, Stats};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock, PoisonError};
use verifier::{E, Proof};

/// The experimental prover, dispatched on the CPU.
pub struct ExperimentalProver;

macro_rules! tiers {
    ($(#[$cfg:meta] $tier:ident => $detected:expr, [$($feature:literal),*],)*) => {
        /// A copy of the prover: one compiled with a CPU tier's target features, or the build's own.
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        #[allow(non_camel_case_types)]
        #[non_exhaustive]
        pub enum Tier {
            $(#[$cfg] $tier,)*
            base,
        }

        impl Tier {
            /// The tiers this build holds, fastest first: those with a feature the build's own lacks.
            pub const ALL: &[Tier] = &[$(#[$cfg] Tier::$tier,)* Tier::base];

            /// Whether `scripts/tier-rustc` compiled the tier with its features, and this CPU has them.
            fn runs_here(self) -> bool {
                match self {
                    $(#[$cfg] Tier::$tier => $tier::__TIER && $detected,)*
                    Tier::base => true,
                }
            }

            /// Whether `scripts/tier-rustc` compiled the tier with its features.
            fn compiled(self) -> bool {
                match self {
                    $(#[$cfg] Tier::$tier => $tier::__TIER,)*
                    Tier::base => true,
                }
            }

            /// The features the tier adds to the build's own.
            fn features(self) -> &'static [&'static str] {
                match self {
                    $(#[$cfg] Tier::$tier => &[$($feature),*],)*
                    Tier::base => &[],
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
                    $(#[$cfg] Tier::$tier => $tier::ExperimentalProver::prove(program, witness, public_input, log_inv_rate),)*
                    Tier::base => base::ExperimentalProver::prove(program, witness, public_input, log_inv_rate),
                }
            }

            fn combine_rows(self, rows: &[u64], weights: &[E]) -> Vec<E> {
                match self {
                    $(#[$cfg] Tier::$tier => $tier::ExperimentalProver::combine_rows(rows, weights),)*
                    Tier::base => base::ExperimentalProver::combine_rows(rows, weights),
                }
            }

            fn dot_rows(self, rows: &[u64], weights: &[E]) -> Vec<E> {
                match self {
                    $(#[$cfg] Tier::$tier => $tier::ExperimentalProver::dot_rows(rows, weights),)*
                    Tier::base => base::ExperimentalProver::dot_rows(rows, weights),
                }
            }
        }
    };
}

include!("tiers.rs");

/// `__with_tier`'s tier, as its index in `Tier::ALL`, or `usize::MAX`.
static FORCED: AtomicUsize = AtomicUsize::new(usize::MAX);

/// The tier proving runs in: the fastest this CPU runs, or the one `LEANVM_TIER` names.
///
/// # Panics
/// If `LEANVM_TIER` names no tier this build runs on this CPU.
pub fn tier() -> Tier {
    static TIER: OnceLock<Tier> = OnceLock::new();
    if let Some(&forced) = Tier::ALL.get(FORCED.load(Ordering::Relaxed)) {
        return forced;
    }
    *TIER.get_or_init(|| match std::env::var("LEANVM_TIER") {
        Ok(name) if !name.is_empty() => *__tiers_here()
            .iter()
            .find(|tier| format!("{tier:?}") == name)
            .unwrap_or_else(|| panic!("LEANVM_TIER={name}: this build runs {:?} on this CPU", __tiers_here())),
        _ => {
            let fastest = __tiers_here()[0];
            warn_unused_features(fastest);
            fastest
        }
    })
}

/// Warns on stderr when this CPU has features the prover selects code on that `tier`'s code does not use.
fn warn_unused_features(tier: Tier) {
    let unused: Vec<&str> = selected()
        .into_iter()
        .filter(|&(feature, on_cpu, in_build)| on_cpu && !in_build && !tier.features().contains(&feature))
        .map(|(feature, ..)| feature)
        .collect();
    if unused.is_empty() {
        return;
    }
    let why = if Tier::ALL.iter().any(|&tier| tier != Tier::base && tier.compiled()) {
        "no CPU tier of this build fits this CPU: please report it at https://github.com/leanEthereum/leanVM/issues"
    } else {
        "this build has no CPU tiers: build it with RUSTC_WRAPPER set to leanVM's scripts/tier-rustc and the \
         `cpu_tiers` feature, or with RUSTFLAGS=\"-C target-cpu=native\""
    };
    let rule = "=".repeat(100);
    eprintln!(
        "{rule}\nleanVM: this CPU is not fully supported, so proving runs slower than it could.\n\
         It has {}, which the prover in this build does not use: {why}.\n{rule}",
        unused.join(", ")
    );
}

/// The tiers this CPU runs, fastest first.
#[doc(hidden)]
pub fn __tiers_here() -> Vec<Tier> {
    Tier::ALL.iter().copied().filter(|tier| tier.runs_here()).collect()
}

/// Runs `f` with proving in `tier`, which this CPU must run; one call at a time.
#[doc(hidden)]
pub fn __with_tier<R>(tier: Tier, f: impl FnOnce() -> R) -> R {
    static ONE: Mutex<()> = Mutex::new(());
    struct Unforce;
    impl Drop for Unforce {
        fn drop(&mut self) {
            FORCED.store(usize::MAX, Ordering::Relaxed);
        }
    }
    let _one = ONE.lock().unwrap_or_else(PoisonError::into_inner);
    assert!(tier.runs_here(), "{tier:?} does not run on this CPU");
    FORCED.store(Tier::ALL.iter().position(|&t| t == tier).unwrap(), Ordering::Relaxed);
    let _unforce = Unforce;
    f()
}

impl Prover for ExperimentalProver {
    const NAME: &'static str = "experimental";

    fn init() {
        base::ExperimentalProver::init();
    }

    fn set_num_threads(n: usize) {
        base::ExperimentalProver::set_num_threads(n)
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
        base::ExperimentalProver::map_collect(n, f)
    }

    fn combine_rows(rows: &[u64], weights: &[E]) -> Vec<E> {
        tier().combine_rows(rows, weights)
    }

    fn dot_rows(rows: &[u64], weights: &[E]) -> Vec<E> {
        tier().dot_rows(rows, weights)
    }
}
