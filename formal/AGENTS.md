# formal

What is proved is [`statement.tex`](statement.tex), the one document a reviewer reads; this file is for contributors and agents. Each project's root module and its modules' docstrings say how its proof goes.

## The repository

- Six Lake projects, each built in its own directory: `Statement` (the statement: definitions and end statements only), and the proofs, `common`, `lean_vm`, `lean_xmss`, `lean_sphincs` and `lean_da`; the root is no Lean project. `lake build` at the root (`check-all.sh`) is the full gate, as `.github/workflows/lean.yml` runs it.
- Name a project `lean_*` (or a library `Lean*`) only for a deployed object (leanVM, leanXMSS, leanSPHINCS, LeanDA); infrastructure is named for what it is (`common`, `Statement`).
- This tree is leanVM's `formal/`: `lean_vm` is about the Rust in this repository (`../crates`), and `leanvm-rev` names the commit its citations and generated data's headers were last checked against; bump it when the formalization follows a change to the Rust.
- Generated data (`Statement/Data/`, `lean_vm/LeanVM/Guest/Data/`, `lean_vm/LeanVM/Cost/Decoder/GuestTables.lean`, the decoder tables' chunks (`lean_vm/LeanVM/Cost/Decoder/GuestTablesCheck.lean` and `GuestTablesCheck/`, `lean_vm/LeanVM/Cost/DecoderSize/`, `lean_vm/LeanVM/Cost/DecoderTablesFirewall.lean`), `lean_vm/tests/LeanVMTests/Spec/NodeVectors.lean`, `lean_vm/tests/LeanVMTests/Guest/{Programs,Manifest}.lean`, the fold rounds' table in `lean_vm/LeanVM/Protocol/ToArkLib/Whir/AffineCombinerDeployedTable.lean`, by `lean_vm/scripts/whir-fold-table`) is regenerated, not edited: by `lean_vm/scripts/guest-export` from leanVM's sources at the pin, by `lake exe guest-core` / `lake exe guest-cert`, or, for the decoder's tables, by `lean_vm/scripts/decoder-tables` from the guest's generated data, and their chunks by `lean_vm/scripts/decoder-table-chunks`.
- No `sorry`, `axiom`, `admit`, `native_decide`, `implemented_by` or `unsafe`, and no local overrides of a lakefile's options (one exception: `lake-build.py --dev`, below); every warning is an error, deprecations included. The axiom footprint of every end theorem is Lean's three.
- Builds are heavy: run them on a large machine, after `lake exe cache get`. Cap `lean` and compiled executables with `ulimit -v`, not `lake` (it reserves about 1 GB of address space per job).
- An edit rebuilds what imports it, directly or not (in the module system only when what it exports changes: a statement, an exposed body, a declaration added or removed). Keep a slow module, such as kernel-checked certificates, importing only the functions it evaluates and their facts, in modules of their own, never the proofs that use the certificates; `tools/NeededImports.lean` lists a module's needless imports and the modules to split, and `tools/deps.py cone FILE` what an edit of `FILE` rebuilds (Tools, below). Guard such a split with a check in the build, as `lean_vm/LeanVM/Guest/B2C/CertFirewall.lean` does.
- A proof that needs more than the default `maxHeartbeats` is slow for a reason: profile it (`python3 -I tools/profile.py FILE`, which names the costly steps and their usual fixes) before raising the budget, and raise it on that declaration alone (`set_option maxHeartbeats N in`), never on a file. Tactics that try every hypothesis (`tauto`, `contradiction`, `aesop`, `congr`, `decide` on a goal with a large context) run slow where the context holds a kernel check of large data: clear it first (`clear * - h`). A long chain of `++` over lists of constructors elaborates as one `binop%` tree, slowly (half a minute for `lean_vm/LeanVM/Guest/B1/Gkr/Layer.lean`'s `lyBody`): write a new one `List.flatten [a, b, …]`, unless its proofs read the `++` shape (`holdsList_append`).
- Since Lean 4.35 `Fin.foldl`, `Fin.foldr`, `List.ofFn` and `Array.ofFn` are structural, so the elaborator (`isDefEq`, `whnf`, `rfl` after `rw`/`unfold`, `congr`, `decide`, `exact` against an expected type, linters reading a local's type) evaluates concrete Keccak-f, `GF(2^64)` products (CompPoly's `carryLessMul`), large `ofFn` literals and whole protocol runs (`runI`, `shapedI`) where it used to stop: a recursion-depth error or a `whnf` timeout. Never raise `maxRecDepth` or `maxHeartbeats` for it, and making those definitions irreducible only turns the error into a failed unification. Instead keep the elaborator off the heavy term: an algebraic lemma for what it would compute (`addressOfIndex 1 = g` is `pow_one`, not an evaluation), a concrete equation decided by the kernel and rewritten (`rw [show channelSep MemPush.toRaw = g by decide +kernel]`, `decide +kernel` for a closed goal), `congrArg f` or `Finset.sum_congr` instead of `congr`, `dsimp only [d]` to expose both sides before a `refine`, `have h := e; exact h` to elaborate `e` before matching it, `generalize` on a concrete heavy subterm, `with_reducible exact` on the alternatives of a `first`, and arguments given explicitly rather than unified.
- The Rust code (Rust verifier, prover, guests) is test evidence, not proof; a proof claim cites leanVM sources at a named commit.
- `lean_da` is Benedikt Wagner's work (framework, theorems and proofs, from `b-wagn/fv-pq-da`), ported and instantiated with LeanDA: credit him in its files and in every commit that touches it.

## Statement

- `Statement/` is the trusted statement: seventeen files (`statement.tex`, the reviewer's document, lists them in reading order; keep it in step with every change to `Statement/`), the generated guest bytecode (`Statement/Data/`), the honest prover the completeness statements name (`Statement/Prover/`, its executable `LeanVM.Prover.prove`, fourteen files: a reviewer checks only that it is a genuine prover, its correctness proved in `lean_vm/LeanVM/Prover/`), and proved `@[csimp]` lemmas for speed only (`Statement/Fast/`, not part of what a reviewer reads). It imports only Mathlib, VCVio, CompPoly and its own files (CI checks it), and every change to it changes what is proved. No file beyond the seventeen without asking. Definitions and end statements only: a proof belongs to the proof projects, unless a definition needs it (a structure's law, a decidability instance).
- Keep the leanVM definitions a faithful transcription of the leanVM sources they cite (`*.rs:N`, `doc/leanvm` sections), at the commit they name.
- Only statements in the random-permutation model are end statements; the random-oracle model and the sponge's indifferentiability are proof steps, in the proof projects.
- Each proof project's root module is its end file: it checks each end theorem against its `Statement` proposition and pins its axioms.
- `lake build` in `Statement/` builds the seventeen files, `Data/`, `Fast/` and `Prover/`; the data's modules are heavy, so build them as CI does, `python3 -I ../lake-build.py .`.

## lean_vm

- Speed comes from proved `@[csimp]` lemmas (`Statement/Fast/`: a `@[csimp]` lemma acts where a definition is compiled, so the statement's own definitions must see them); lemmas about the statement's definitions are in `LeanVM/Facts/`.
- A word of `E` has two limbs (`E.limb : Fin 2 → K`), and a numeral index wraps: `x.limb 2` elaborates and reads limb `0`. Write limbs `0` and `1` only.
- `leanvm-prove` runs the prover recompiled with `E`'s arithmetic on machine words (`LeanVM/Prover/Fast/`: every prover and verifier definition that multiplies in `E` copied, `@[csimp]` by `rfl`). A recursive prover definition is copied by hand there, its text with `mulE` and proved equal by induction; when the prover gains one, the build of `LeanVM.Prover.Fast.Prover` names it.
- `lake build` builds every module under `LeanVM/` (the lakefile's globs), and `LeanVM.lean` pins the end theorems' axioms. `lake test` builds every module under `tests/LeanVMTests/`. Use `lake build <Module>` to check one module, not `lake env lean`.
- Lake has no job limit, so a cold parallel `lake build` can exceed a 16 GB machine. `python3 -I ../lake-build.py . LeanVM LeanVMTests` runs one `lake build` whose modules, the statement package's included, it admits by their recorded memory, the cores busy (CI uses it; `lake-build.tsv` holds the heavy modules, `--seed` rewrites it). Keep a new module under about 3.5 GB.
- `lake-build.py --dev` is for development only: it builds into `.lake/build-dev` with the kernel skipped (`debug.skipKernelTC`) on `LeanVM` (its dependencies, `Statement` among them, are built as usual), about 10x faster. Elaboration still checks ordinary proofs, but a false `decide +kernel` passes and `#print axioms` does not show it. Never use it for CI, a gate, a push or a claim: those run the build above, kernel included.
- `Statement/LeanVmVerifier.lean` is the readable reference of the verifier. Differential tests compare it with the Rust verifier, `scripts/fuzz-verifier.py` on `tests/fixtures/verifier` (Commands, below; its mutation positions come from the Lean verifier's own traced run, `leanvm-verify --events`), and pin values of the verifier at its pins (`tests/LeanVMTests/Protocol/Verifier/Helpers.lean`, `Compiled.lean`). A protocol change in the Rust verifier fails CI until `Statement/LeanVmVerifier.lean` and the proofs follow; regenerate the fixtures (Commands, below).
- The guest's kernel-checked certificates (`Guest/Checked`, `Guest/B2C/Shared`, `Guest/B2C/Cplw`, their data `Guest/Data/`) are written together by `lake exe guest-cert` (`--check` fails when one is stale), and the completeness budget's static certificates by `python3 -I scripts/count/gen.py . all`. A certificate module imports only its bases, never B1's, the protocol's or the schemes' proofs (`Guest/B2C/CertFirewall.lean` fails the build otherwise); independent kernel checks that take minutes go in modules of their own.

## Commands

Run from the project's directory. `./check-all.sh lean` and `./check-all.sh vectors` at the root are the gate, as CI runs it; read `check-all.sh` for every step.

```sh
# any project
lake exe cache get
python3 -I ../lake-build.py .                     # lean_vm: python3 -I ../lake-build.py . LeanVM LeanVMTests
python3 -I ../lake-build.py . LeanVM --dev        # lean_vm, kernel skipped, never a gate

# lean_vm, against this repository's Rust
lake test && lake exe node-vectors
python3 -I scripts/fuzz-verifier.py tests/fixtures/verifier --jobs 4     # after lake build leanvm-verify and cargo build of scripts/rust-verifier-cli
python3 -I scripts/wire-diff.py tests/fixtures/verifier --jobs 8         # after lake build wire-diff and cargo build of scripts/wire-diff
scripts/export-prover-traces-rust.sh /tmp/p && python3 -I scripts/prover-diff.py /tmp/p --mutations 40 --jobs 4 --identical --expected tests/fixtures/verifier
scripts/export-verifier-fixtures-rust.sh tests/fixtures/verifier          # after a protocol change
scripts/guest-export/target/release/guest-export . [--check]             # the guest's data, after a change to the guest or leanvm-rev
cargo run --release --manifest-path scripts/whir-fold-table/Cargo.toml -- LeanVM/Protocol/ToArkLib/Whir/AffineCombinerDeployedTable.lean [--check]   # the fold rounds' certificate, after a change to whir_config.rs
LEANVM_GUEST_DIFF=/tmp/g cargo test --release --manifest-path scripts/guest-export/Cargo.toml --lib guest_diff -- --ignored && lake exe guest-diff /tmp/g/*.txt

# lean_sphincs: the crates' known answers on the compiled statement
lake exe signature-kat ../../crates/signatures/tests/signatures/ethlib ../../crates/signatures/src/lean_sphincs/known_answer.hex
```

## Tools

- `python3 -I tools/deps.py cone FILE`: what an edit of `FILE`'s interface rebuilds, its CPU time and longest chain; `deps.py slow`, `deps.py path`.
- `python3 -I tools/profile.py FILE`: where a slow file's time goes, by declaration and step; its docstring lists the usual fixes.
- `lake env lean --run ../tools/NeededImports.lean MODULE`: the imports `MODULE` does not need, and the modules to split.
- `lake env lean --run ../tools/Unused.lean ROOT... --prefix P`: declarations under `P` that no root uses; read before deleting.
- `python3 -I tools/escape-scan.py DIR...`: fails on a proof escape outside comments (the gate runs it).
- `python3 -I tools/docnames.py`: names `statement.tex` and the docs cite that no Lean file has.
