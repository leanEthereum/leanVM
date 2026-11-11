module

public import Refinement.Lib
public import Refinement.Spec
public import Refinement.Proofs
public import Refinement.Claims

/-!
# Refinement of the statement by the Rust

The hand-written half of the project.
The other half, under `crates/`, is the model of the Rust.

* Claims: each extracted function computes what its statement definition computes.
* Spec: how a model's values read as the statement's values.
* Proofs: why the claims hold.
* Lib: lemmas shared by the proofs.

Organized by property, not by crate: one claim can span several crates.
-/
