# Status of the top of the call graph (family G)

What `rv64_sound` (`Rv64mc/Final/End.lean`) still assumes, function by function. `Table/Walk.lean`'s `rv64_sound_of_main` takes `main`'s contract at the stack `main` needs (`MainSpec env (liftProg fns) Idx.Main Needs.Main`); every other hypothesis below sits under it.

| function | instr | status | hypotheses remaining |
| --- | --- | --- | --- |
| `verify_execution` | 2 | proved (`Proof/Walk/VerifyExecution.lean`, `Table/Walk.verifyExecution`) | `walk`'s contract (`Spec/Walk/Execution.lean`) |
| Model to `Verdict` | - | proved (`Proof/Walk/Verdict.lean`: `decodeInput_leafIndex`, `verdict_of_accept`) | none |
| `rv64_sound` from `main` | - | proved (`Table/Walk.rv64_sound_of_main`) | `MainSpec` at `Needs.Main` |
| `main` | 287 | in progress: the stream loop proved (`Proof/Walk/MainStream.lean`, `loopS`), its entry's callee preconditions proved (exploration `out/main/E2.lean`, lemmas in `Proof/Walk/MainEntry.lean`); the rest not proved | its proof (below); callee contracts: `Bytecode::new` (`Spec/Bytecode/New.lean`), `Input::digest` (`InputDigestSpec`), the guest's `try_allocate_in` (`TryAllocRv64Spec`, not `TryAllocSpec`), `memcpy` (`MemcpySpec`, at the image from `compiler_builtins`' `memcpy`), `walk` (`Spec/Walk/Execution.lean`, `verify_execution` proved from it), `handle_error` and `halt` (proved, `Table/Runtime`) |
| `walk` | 762 | specified (`Spec/Walk/Execution.lean`), not proved | its proof; 36 callees, among them `Transcript::new`, `next_scalars`, `grind_check`, `Sponge::sample`, `finish`, `grinding_bits`, `build_layout`, `verify_bus_balance`, `table_sumcheck`, `powers`, `verify_keccak`, `ring_switch`, `read_ood`, `verify_stacked_opening`, `Digest::halves`, `Digest::from_halves`, `Layout::committed`, `dot`, `multilinear_eval_k`, and the runtime's allocation, growth, clone, drop and panic functions |

## `main`, where it stands

**The end theorem's hypotheses, once `main` is proved.** `Table/Walk` would instantiate `main`'s `ok` at `liftProg fns` with every callee at `Needs.Verifier.VerifyExecution` (the deepest; `416 + 35504 = Needs.Main`) by `Holds.mono_need`, `halt` and `handle_error` from `Table/Runtime`, and the image's environment fact `0x20000000 + 32 ≤ env.stackLimit` (`Input::digest`'s reader bound; `Final/End`'s environment has it). The hypotheses left are the five unproved callee contracts, each at its own index and `Needs`:

1. `Spec.Bytecode.New.spec env (liftProg fns) Idx.Verifier.Bytecode.Bytecode.New Needs.Verifier.Bytecode.Bytecode.New` (`Bytecode::new`);
2. `InputDigestSpec env (liftProg fns) Idx.VerifierRv64.Input.Digest Needs.VerifierRv64.Input.Digest` (`Input::digest`);
3. `TryAllocRv64Spec env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.TryAllocateInInVerifierRv64 Needs.Alloc.RawVec.RawVecInner.TryAllocateInInVerifierRv64` (the guest's `try_allocate_in`);
4. `MemcpySpec env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy` (under `Table/Runtime.memcpy`);
5. `Spec.Walk.Execution.spec env (liftProg fns) Idx.Verifier.Walk Needs.Verifier.Walk` (`walk`, under `Table/Walk.verifyExecution`).

**A wrong callee contract fixed.** `main` calls the guest crate's instance of `try_allocate_in` (`TryAllocateInInVerifierRv64`, 48 instructions), whose arguments are `(sret, capacity, align, size)`: LLVM dropped `init`. `TryAllocSpec` is the verifier crate's instance (`init`, `align`, `size` in `a2`..`a4`), so a proof of `main` from it was unsound in intent (`a4` is garbage at main's calls). `Spec/Runtime/TryAllocateInRv64.lean` states the right one, and the dangling pointer (the alignment) for no bytes, which `LiveVecAt` of an empty `Vec` needs (`ptr ≤ NEXT`).

**What is proved.** `Proof/Walk/MainBase.lean`: `Base`, what every cut point keeps (the frame from the entry, `env.Static`, the 13 saved registers, the `Bytecode` and public input in `[sp + 88, sp + 184)` and the heap below `NEXT` as at the snapshot `M1` after `Input::digest`), kept by any store or call that writes only `Writable` words (`Base.store`, `Base.call`), and input words read through it (`Base.input`). `Proof/Walk/MainStream.lean`: the stream loop (instruction 74, `loopS`) against its continuation at instruction 93 (`InvA`): `k` scalars copied (`EListAt` of `scal words p`), by induction on the scalars left, 8 s. `Model/Extra/Main.lean`: the reader a word at a time (`readWord_drop`, `readMany_snoc`, `readMany_readK`, `readOpening_of`, `decodeInput_of_runs`). `Proof/Walk/MainEntry.lean`: the entry's callee preconditions from `MainPre` (`Bytecode::new`'s slice as `with` facts, its length, `Input::digest`'s reader bound).

**What remains**, as cut points (instruction, label address) with a lemma each, continuation-passing, each `rv_sym` run 8 to 30 s:

* the entry (`rv_auto … stop [148, 186]`, 77 s, its callee preconditions closed in `out/main/E2.lean` but for `Bytecode::new`'s slice `WordsAt`, below): `Base` at `M1 = m4` (the frame through the 13 prologue stores, `Bytecode::new`, the 8-word copy and `Input::digest`), then `InvS 0` at 148 or `InvA` at 186 from the readers' slots (`DigestPost`);
* 93 (`0x45c`): the phases' count, the `Vec<Vec<MerklePath>>` block, to 474 (none) or 131;
* 131 (`0x4f4`, phase head), 168 (`0x588`, path head), 193 (`0x5ec`, leaf copy), 198 (`0x600`), 219 (`0x654`, sibling: `Input::digest` then `memcpy` of 32 bytes), 154 (`0x550`, path tail: the `MerklePath`'s 7 words), 117 (`0x4bc`, phase tail: the `Vec` header): the nested loops, each a lemma taking its exit's continuation, the phase and path loops by induction on what is left;
* 237 (`0x69c`): the input exhausted (else `halt(2)`), the `Proof`'s header stored at `sp + 184`, `verify_execution`, `ResultOkAt` to `mainVerdictRust … = true` (`newRust` of the bytecode's words), `decodeInput_of_runs`, `verdict_of_accept`.

The nested buffers are written after the arrays that hold their headers were allocated, so `HeapKept`-style keeps (everything below `NEXT`) do not carry them: the plan is region predicates, a path's or phase's buffers in `[lo, hi)` (`lo` the `NEXT` after the enclosing array, `hi` the current `NEXT`), kept by `Keeps` on the headers and on `[lo, hi)`, and turned into `PathAt`/`PhaseAt` (`LiveVecAt`) at the end.

**Tactic gaps met** (for track T4): `rv_mem` and the heap transport do not resolve a load at a literal base plus a symbolic offset (`268435464#64 + BitVec.ofNat 64 (8 * k)`) through the prologue's stack stores, even with `268435464 + 8 * k + 424 ≤ top.toNat` in the context, so a `WordsAt` given in `with` is not carried to `Bytecode::new`'s precondition; `rv_close` does not re-establish an invariant's memory facts (the frame, `Static`, saved slots, `Keeps`) after stores into fresh memory at a back edge (hence `Base.store`); `simp only [BitVec.toNat_add, BitVec.toNat_ofNat]` on a goal with a literal such as `18446744073709551608#64` grows past 8 GB (use `BitVec.add_assoc` and a literal sum by `decide`).
