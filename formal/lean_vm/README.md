# lean_vm

A Lean 4 proof that leanVM's verifier is knowledge sound and complete in the random-oracle model, for the verifier, the instruction set and the arithmetization of the containing commit.

## What is proved

The statements are in [`LeanVM/Spec/`](LeanVM/Spec/README.md), which imports nothing else from this project (CI checks it): the rest is proof. Read in this order:

| File | What it is |
| --- | --- |
| [`Field.lean`](LeanVM/Spec/Field.lean) | the fields `K = GF(2^64)`, `E = GF(2^192)` and the generator `g` |
| [`Blake2s.lean`](LeanVM/Spec/Blake2s.lean) | BLAKE2s: the compression function and the hash of bytes |
| [`Isa.lean`](LeanVM/Spec/Isa.lean) | leanISA: memory, the six instructions, programs, one step, `ValidExecution`, `Trace.count` |
| [`Verifier.lean`](LeanVM/Spec/Verifier.lean) | the verifier, `python-verifier/verifier.py` transcribed section by section, for any hash function |
| [`Statement.lean`](LeanVM/Spec/Statement.lean) | `KnowledgeSoundness` and `Completeness` |
| [`Da.lean`](LeanVM/Spec/Da.lean), [`Node.lean`](LeanVM/Spec/Node.lean) | the DA claim, on LeanDA as [`formal/lean_da`](../lean_da) defines it, and what a node of the aggregation guest establishes (`NodeSpec`): stated, not proved |

The proofs are `LeanVM.knowledgeSoundness_holds` and `LeanVM.completeness_holds` ([`LeanVM/Protocol/LeanVM.lean`](LeanVM/Protocol/LeanVM.lean)). [`LeanVM.lean`](LeanVM.lean) fails the build if their axioms grow beyond `propext`, `Classical.choice` and `Quot.sound`.

BLAKE2s is modelled as a random oracle. A proof is the Python verifier's format (full Merkle paths); the Rust verifier's expansion of the pruned wire paths is not formalized. That the Lean verifier is the Rust and Python ones is test evidence: it accepts the Rust prover's proofs, and gives the Rust verifier's verdict on mutated ones.

`Completeness` covers every valid execution within the verifier's size cap: its committed size (`Trace.committedSize`, the cells the prover commits to, set by the memory, the bytecode and how many instructions of each opcode it executes) at most `2^28`. Open: `NodeSpec` is not proved.

## Layout

| Path | Contents |
| --- | --- |
| `LeanVM/Spec/` | the statements |
| `LeanVM/Parameters/`, `LeanVM/Semantics/` | constants and encodings; lemmas about the ISA and an executable interpreter |
| `LeanVM/Arithmetization/` | the tables, the bus and the constraints, sound and complete for valid executions |
| `LeanVM/Protocol/` | the proof system and the end-to-end proofs; `To{ArkLib,Clean,CompPoly,VCVio}/` hold lemmas meant for those libraries |
| `LeanVM/Guest/` | the aggregation guest: its compiled bytecode (`Data/Bytecode*`, generated) as a `Program` and the program logic for its runs (`Code`, `Bytecode`, `Logic`); its mirror, the source AST (`Source`, the generated `Data/Source`), the core IR and its relational semantics (`Core`, `CoreLemmas`), the renumbering of a function's values (`Renumber`) and the guest's core IR as data (`CoreData`, the generated `Data/Core*`), the zkDSL expansion (`Expand`, `ExpandLemmas`) and an interpreter (`Interp`); the honest hint generator (`Hints`); the value lemmas (`Value/`); the honest memory of an evaluation for completeness (`Memory`, `Memory/`) |
| `tests/` | `#guard`s and `example`s, checked by `lake test`; `fixtures/verifier/` are proofs of the Rust prover |
| `cli/` | `leanvm-verify`, the compiled verifier on a proof's files, `node-vectors`, the costly checks of the Rust vectors, `guest-core`, the writer of the guest's core IR data, and `guest-diff`, the guest's mirror and hint generator against Rust aggregations |
| `scripts/` | the Rust-vs-Lean fuzz, its Rust verifier CLI, the fixture exporter, and the WHIR parameter table generator |

## Building and testing

```sh
lake exe cache get
lake build
lake test
lake exe node-vectors
```

The Rust-vs-Lean differential, as CI runs it:

```sh
lake build leanvm-verify
cargo build --release --manifest-path scripts/rust-verifier-cli/Cargo.toml
python3 -I scripts/fuzz-verifier.py tests/fixtures/verifier --jobs 4
```

The guest's mirror and hint generator against Rust aggregations, as CI runs it: the Rust test writes each case (a leaf of both schemes with a blob, a leaf whose list is longer than a digest window, a node over them), and `guest-diff` checks that the witness holds the statement, that `Hints.honestStreams` is the streams the Rust installed, that the public input is the statement's digest, and that the interpreter runs the guest's core IR on them, printing the first divergence:

```sh
lake build guest-diff
LEANVM_GUEST_DIFF=/tmp/guest-diff cargo test --release -p rec_aggregation guest_diff -- --ignored
.lake/build/bin/guest-diff /tmp/guest-diff/*.txt
```

After a protocol change, regenerate the fixtures with `scripts/export-verifier-fixtures-rust.sh tests/fixtures/verifier`, and the node vectors with `LEANVM_WRITE_NODE_VECTORS=1 cargo test --release -p rec_aggregation node_spec_vectors`. After a change to the guest, its compiler or the compiler's test programs, regenerate the guest data with `LEANVM_WRITE_GUEST=1 cargo test --release -p rec_aggregation guest_`. After that, or a change to the expansion (`Guest/Expand.lean`) or the core IR (`Guest/Core.lean`), regenerate the guest's core IR (`LeanVM/Guest/Data/Core*`, the expansion of the source as data, its values renumbered) with `lake exe guest-core`; `lake exe guest-core --check`, which CI runs, fails when it is stale, and `lake exe guest-core --values f` prints the expansion's name of each value of the function `f`.

## Credits

The formalization was started in `Verified-zkEVM/leanerVM`, by scaraven, aryaethn, Alexander Hicks, Elias Judin, Stefano Rocca and Aristotle (Harmonic). Modules derived from the earlier leanth formalization say so in their docstrings.
