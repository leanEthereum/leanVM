//! Fill blocks (`lean_compiler::filler`): extra real rows so a table's height needs no
//! padding.
//!
//! What has to hold, and is checked here end to end:
//!
//! - every table comes out an exact power of two, whatever the program's row mix, so
//!   nothing is ever padded;
//! - the fill costs exactly what the solver says, a traversal being its block's rows
//!   plus one jump and nothing else;
//! - the filled trace proves and verifies.
//!
//! The second is what lets the interpreter solve once the chain has halted, in one
//! interpretation of the program, so it is worth pinning rather than assuming.

use lean_compiler::{compile, parse};
use leanvm_core::cpu::filler;
use leanvm_core::cpu::{prove, verify};
use primitives::field::F192;

const PROGRAMS: [&str; 5] = [
    // Folds to nothing, so the fill is all there is.
    "def main():\n    x = GEN ** 5\n    y = x * x\n    return\n",
    "def main():\n    b = HeapBuf(4)\n    b[1] = GEN\n    y = b[1] * b[1]\n    return\n",
    "def main():\n    for i in mul_range(1, GEN ** 20):\n        z = i * i\n    return\n",
    // A hash, so SHA3 is non-empty too.
    "def main():\n    a = StackBuf(2)\n    a[0] = 5\n    a[1] = 7\n    c = StackBuf(2)\n    sha3(a, a, c)\n    return\n",
    "def main():\n    for i in mul_range(1, GEN ** 300):\n        z = i + GEN\n    return\n",
];

#[test]
fn every_table_lands_on_a_power_of_two() {
    for src in PROGRAMS {
        let program = compile(&parse(src).expect("parse"));
        let pi = [F192::ZERO, F192::ZERO];
        let (proof, stats) = prove(&program, pi, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
        assert!(filler::is_filled(stats.counts), "{:?} for {src:?}", stats.counts);
        verify(&program, &pi, &proof).expect("a filled program verifies");
    }
}

/// The solver's cost model is the whole reason one pass suffices, so check it against
/// what the machine did: from the program's own rows, the plan the interpreter solved
/// must predict the proven counts exactly.
#[test]
fn the_cost_model_is_exact() {
    for src in PROGRAMS {
        let program = compile(&parse(src).expect("parse"));
        let stats = prove(&program, [F192::ZERO, F192::ZERO], leanvm_core::pcs::TEST_LOG_INV_RATE)
            .unwrap()
            .1;
        let plan = filler::solve(stats.base_counts, filler::NO_FLOORS).expect("solvable");
        assert_eq!(
            filler::filled(stats.base_counts, &plan),
            stats.counts,
            "predicted against actual for {src:?}"
        );
    }
}
