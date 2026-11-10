//! The targets, one module per group, each group a feature of this crate.

use crate::Target;

#[cfg(feature = "aggregation")]
pub mod aggregation;
#[cfg(feature = "decoders")]
pub mod decoders;
#[cfg(feature = "dsl")]
pub mod dsl;
#[cfg(feature = "isa")]
pub mod isa;
#[cfg(feature = "kernels")]
pub mod kernels;
#[cfg(feature = "soundness")]
pub mod soundness;

pub fn all() -> Vec<&'static Target> {
    let mut all: Vec<&'static Target> = Vec::new();
    #[cfg(feature = "kernels")]
    all.extend(kernels::TARGETS);
    #[cfg(feature = "decoders")]
    all.extend(decoders::TARGETS);
    #[cfg(feature = "dsl")]
    all.extend(dsl::TARGETS);
    #[cfg(feature = "isa")]
    all.extend(isa::TARGETS);
    #[cfg(feature = "soundness")]
    all.extend(soundness::TARGETS);
    #[cfg(feature = "aggregation")]
    all.extend(aggregation::TARGETS);
    all
}

/// Drop every hook a case armed and no prover took, so it cannot fire in the next case.
pub fn disarm_all() {
    leanvm_core::cpu::tamper::disarm();
    leanvm_core::cpu::tamper::transcript::disarm();
    #[cfg(feature = "aggregation")]
    rec_aggregation::fuzzing::disarm_forgery();
}
