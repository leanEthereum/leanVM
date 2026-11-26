# rv64mc: the RV64IM image of the verifier, decompiled into Lean

An experiment: compile `crates/verifier` (a `no_std` copy) to an RV64IM guest, lift every function of the binary into Lean with [machine-checked](https://github.com/Verified-zkEVM/machine-checked)'s proved decompiler, and prove the lifted code implements the statement's verifier (`../Statement/LeanVmVerifier.lean`), one function at a time over relocatable templates, so that a change to the Rust re-proves only the functions it touches. The end theorem is `Rv64mc.rv64_sound` (`Rv64mc/Final/End.lean`): every code word decodes, and a run that halts with `a0 = 0` read an input the statement's verifier accepts, with `main`'s contract as its one hypothesis. Results, costs and the comparison with PR #738 are in [report/REPORT.md](report/REPORT.md).

## Trusted

`Rv64mc/EndStatement.lean` is the statement: the machine, the loader, `Sound`, `AllDecode`, `HaltsSafely` and the headline `SafeVerdict` (with its target `BoolVerdict`); its docstring says where it is weaker than intended. Also trusted: `Rv64mc/ImageOfElf.lean` (the ELF reader that defines `image`), riscv-zkvm's decoder, and the statement's verifier. Everything else is checked by the kernel, on the standard axioms only.

## Layout

* `guest/`: the RV64IM guest crate (`src/main.rs` decodes the input and calls the verifier); `ADAPTATIONS.md` says how it differs from #738's guest.
* `scripts/`: `nostd-verifier.sh` (the `no_std` copy, with the inline attributes `boundaries.txt` asks for), `regen.sh` (build, lift, write `Rv64mc/Gen/`), `gen.py` (templates and link modules), `type-layouts.sh` (rustc's type layouts, named in `layouts.txt`), `iterate.sh` (the iteration benchmark over `bench/patches/`).
* `Rv64mc/EndStatement.lean`: the trusted statement. `StepMeet.lean`, `Bridge.lean`: from its machine to machine-checked's `SafeN`.
* `Rv64mc/Final/`: the end theorem (`End.lean`), `Sound` from `main`'s contract, `_start`, `main`'s contract, the kernel's checks on the image, and how `Sound` composes with the knowledge-soundness theorem (`LeanVm.lean`). The termination end theorem (`EndT.lean`): `HaltsSafely` from `main`'s total contract (`MainSpecT.lean`), through `_start` (`StartT.lean`) and the transfer to the statement's machine (`Transfer.lean`); what `HaltsSafely` says of the runs (`HaltsSafely.lean`). The headline (`Headline.lean`): `SafeVerdict`, `Sound` and `HaltsSafely` together, and its target `BoolVerdict` from `main`'s total contract with abort only on malformed input (`MainSpecB.lean`). Guards that `HoldsT` is satisfiable by functions that touch memory and excludes a system call other than the halt (`HoldsTWitness.lean`). `HoldsT.of_holds_post` at the image: `Input::word`'s safety-only total contract and its partial one give its total contract with the partial one's postcondition and memory frame (`HoldsTOfHoldsUse.lean`).
* `Rv64mc/Total/`: total correctness at Lprog (`Ascent.Total`, `Isa.TContract`), for any instruction set, on machine-checked's `lprog` alone, and what the judgement excludes: a trap, `wrong`, no step, a run that never ends (`Excludes.lean`). A total contract and a partial one give a total contract with both postconditions (`Combine.lean`). A total contract with no stopping state gives the partial one (`ToContract.lean`).
* `Rv64mc/Core/`: contracts (`Holds`, and the total `HoldsT` with `Windows`, where the windows lie relative to the stack, the heap, `NEXT`, the static data and the code; `HoldsT.of_holds`, a `HoldsT` and a `Holds` of the same function combined; `HoldsT.holds`, the `Holds` a `HoldsT` gives; `LocalRun.lean`, a function body run as a function the kernel evaluates), the environment, memory representation predicates and their lemmas.
* `Rv64mc/Link/`: what a relocatable template knows of its callees and call sites.
* `Rv64mc/Tactic/`: `rv_sym`/`rv_auto`, the symbolic executor the proofs use (its header documents it); `rv_symT`/`rv_autoT` (`SymT.lean`, over `StepsT.lean`'s rules), the same executor for total (`HoldsT`) goals; `TStep.lean`, the rules and macros (`tsteps`, `tcond`) that step total goals by hand.
* `Rv64mc/Model/`: Lean mirrors of the Rust verifier's functions, each proved equal to the statement's.
* `Rv64mc/Spec/`: each function's contract over its Model mirror.
* `Rv64mc/Proof/`: each contract proved over the function's template, from its callees' contracts. Total contracts sit next to the partial ones with a `T` suffix (`Proof/Runtime/HaltT`, `AllocT`, `Proof/Field/ESquareT`, ...; `notes/total-status.md` lists them); `Proof/Runtime/WinT.lean` holds the window lemmas they share, `Proof/Runtime/VecReprT.lean` the representation of a vector's header and buffer (`BufT`, `RawVecT`, `VecT`) that the growth chain (`TryAllocateInT`, `GrowAmortizedT`, `GrowOneT`, `DoReserveT`, `ReserveT`) takes and gives.
* `Rv64mc/Table/`: the proofs instantiated at the image's function indices and composed; the total contracts' instances in the `T` modules (`RuntimeT`, `FieldT`, `AllocT`, `LayoutT`, ...); `CopyScratch.lean`, concrete runs of `memcpy` and `memmove` showing that a copy contract keeping their stack slot, or with a range on it, is false, and guards of the corrected contracts.
* `Rv64mc/Gen/`, `Rv64mc/Gen.lean`: generated by `regen.sh` and `type-layouts.sh` (gitignored): templates, link modules (named in `link-batches.txt`), the image's words and layouts.
* `RunImage.lean`, `RunModel.lean`: executables that run the statement's machine on the image and the Model on an input (`notes/non-vacuity.md`).
* `notes/`: design notes, `how-to-prove-a-function.md`, the proof and iteration logs, `status.md` and `total-status.md`.

## Building

The Lake workspace requires `../Statement`, machine-checked at a pinned commit, and Mathlib v4.36.0, listed last so that the workspace takes Statement's Mathlib rather than machine-checked's.

`.lake/packages` was populated as a hard-link copy of another v4.36.0 workspace with the same requirements (Statement and machine-checked), so that nothing was rebuilt. To recreate it from scratch: `lake update` (with Mathlib last in `lakefile.toml`, as it is), then `lake exe cache get` for Mathlib's build; the other packages build once. `lake build decompile` builds machine-checked's lifter, which `regen.sh` runs.

Then, from this directory:

```bash
scripts/regen.sh          # builds the guest, lifts it, writes Rv64mc/Gen/ and out/canon.elf; --check verifies image.sha256
scripts/type-layouts.sh   # writes Rv64mc/Gen/Layouts.lean
lake build Rv64mc
```

The guest builds with the nightly `guest/rust-toolchain.toml` names and its `rust-src` (`build-std`); `guest/.cargo/config.toml` sets the target and the codegen flags the lift relies on. `report/REPORT.md` gives the build costs.

## Status

`notes/status.md`: which functions are proved and linked at the image, which have only a contract, and which have neither. [`notes/total-status.md`](notes/total-status.md): which have a total contract (`HoldsT`) and its `Table` instance at the image (`Rv64mc/Table/*T.lean`), toward `main`'s `MainSpecT`.
