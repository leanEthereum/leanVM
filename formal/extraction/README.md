# extraction

The Lean model of leanVM's crates, and the claims that it refines the statement. Laid out after [Plonky3-lean](https://github.com/Plonky3/Plonky3-lean).

The statement (`../Statement`) transcribes the Rust by hand, and differential tests pin the two together. Here that pin becomes a theorem: [hax](https://github.com/cryspen/hax) extracts each crate to Lean (through [Charon](https://github.com/AeneasVerif/charon) and [Aeneas](https://github.com/AeneasVerif/aeneas)), and each claim says an extracted function computes what its statement definition computes.

Nothing is extracted yet. Each crate is an empty stub that fixes its library's name and imports.

## Layout

```
toolchain.toml        the extractor's pins: hax, charon, aeneas, Rust toolchain, target
lakefile.toml         one workspace: the statement, Aeneas, CoreModels, one library per crate
crates/               the model: one directory per workspace crate (crates/README.md)
HaxExt.lean           what Aeneas and CoreModels lack, shared by every crate
Refinement/           hand-written, by property
  Claims.lean           what is asserted
  Spec.lean             how a model's values read as the statement's
  Proofs.lean           why the claims hold
  Lib.lean              lemmas shared by the proofs
claims.toml           the axioms each claim may use
known-warnings.txt    the warnings generated code may print
TRUST.md              what is trusted
tools/                layout and claims checks, the extraction driver
docs/extracting.md    installing and running the extractor
```

## Plan

1. `verifier`: no dependencies, no `unsafe`, no `cfg(target_arch)`, written to be read beside `Statement/LeanVmVerifier.lean`. The first claim: the extracted verifier accepts exactly the proofs the statement's verifier accepts. Knowledge soundness (`../lean_vm`) is then about the Rust that runs.
2. `signatures`: leanXMSS and leanSPHINCS verification, against `Statement/LeanXmss.lean` and `Statement/LeanSphincs.lean`.
3. `primitives`, `fiat_shamir`, `pcs`, `keccak_gkr`, `leanvm_core`: the prover, against `Statement/Prover/`, for completeness. Portable arms only (`TRUST.md`).

`lean_compiler`, `rec_aggregation` and `leanvm` come last, if at all: the guest's bytecode enters the statement as generated data. Each `crate.toml` names its statement modules (`spec`).

## Build

```sh
lake exe cache get
lake build
python3 -I tools/check-layout.py    # crates/, lakefile.toml and Cargo agree
python3 -I tools/check-claims.py    # each claim has exactly its claims.toml axioms
```

`../check-all.sh extraction` runs all of it, as CI does.
