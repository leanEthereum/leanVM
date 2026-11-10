//! The `dsl` group: the zkDSL front end, compiler and runtime.

use crate::{Cost, Target};

mod ast;
pub mod corpus;
mod generate;
mod metamorphic;
mod mutate;
mod parse;
mod print;
mod synth;

pub static TARGETS: &[&Target] = &[
    &Target {
        name: "dsl-corpus",
        about: "every hand-written program meets its annotated expectation, its honest proof verifies, and only for its own public input",
        cost: Cost::Medium,
        run: corpus::run,
    },
    &Target {
        name: "dsl-gen",
        about: "generated self-checking programs compile, run to the public input the generator computed, and prove",
        cost: Cost::Medium,
        run: generate::run,
    },
    &Target {
        name: "dsl-metamorphic",
        about: "two spellings of one generated program (inlined, unrolled, routed through buffers, constants refolded) publish the same public input, and a source compiles to one bytecode",
        cost: Cost::Medium,
        run: metamorphic::run,
    },
    &Target {
        name: "dsl-mutate",
        about: "line and token mutations of the corpus and the recursion guest: parse never panics, compile panics are triaged, a mutant that compiles runs or errors, and one that runs proves",
        cost: Cost::Medium,
        run: mutate::run,
    },
    &Target {
        name: "dsl-parse",
        about: "raw bytes and grammar-shaped garbage (deep nesting, ** towers, huge literals, NUL, tabs) into parse and parse_const: no panic, hang or stack overflow",
        cost: Cost::Cheap,
        run: parse::run,
    },
];
