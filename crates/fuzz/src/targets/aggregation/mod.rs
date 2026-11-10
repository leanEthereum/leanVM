//! The `aggregation` group: a malicious aggregator against the recursion guest (`lean_ethereum.py`) and the public
//! aggregation API. Every target builds on [`fixtures`], real aggregates proven once per campaign.

use crate::{Cost, Target};

mod api;
mod child;
mod common;
pub mod fixtures;
mod forge;
mod scenarios;

pub static TARGETS: &[&Target] = &[
    &Target {
        name: "guest-forge",
        about: "a node's hint streams edited (a cell, an entry, a count, a slot, the claim lists): the guest refuses any witness but the honest one for its statement, and every statement nothing backs",
        cost: Cost::Medium,
        run: forge::run,
    },
    &Target {
        name: "guest-child",
        about: "a forged child (mutated proof, deferred claim, claims, DA root): whatever EthereumProof::verify rejects, the guest refuses, and the other way round",
        cost: Cost::Medium,
        run: child::run,
    },
    &Target {
        name: "aggregate-api",
        about: "adversarial aggregate calls: an error of the documented kind, never a panic, never a run that publishes an unbacked claim; sampled valid nodes proven and verified",
        cost: Cost::Medium,
        run: api::run,
    },
    &Target {
        name: "aggregation-scenarios",
        about: "hand-written aggregation attacks, each with its expected outcome",
        cost: Cost::Medium,
        run: scenarios::run,
    },
];
