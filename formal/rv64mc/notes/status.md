# Status of the top of the call graph (family G)

What `rv64_sound` (`Rv64mc/Final/End.lean`) still assumes, function by function. `Table/Walk.lean`'s `rv64_sound_of_main` takes `main`'s contract at the stack `main` needs (`MainSpec env (liftProg fns) Idx.Main Needs.Main`); every other hypothesis below sits under it.

| function | instr | status | hypotheses remaining |
| --- | --- | --- | --- |
| `verify_execution` | 2 | proved (`Proof/Walk/VerifyExecution.lean`, `Table/Walk.verifyExecution`) | `walk`'s contract (`Spec/Walk/Execution.lean`) |
| Model to `Verdict` | - | proved (`Proof/Walk/Verdict.lean`: `decodeInput_leafIndex`, `verdict_of_accept`) | none |
| `rv64_sound` from `main` | - | proved (`Table/Walk.rv64_sound_of_main`) | `MainSpec` at `Needs.Main` |
| `main` | 287 | specified (`Final/MainSpec.lean`), not proved | its proof; callee contracts: `Bytecode::new` (`Spec/Bytecode/New.lean`), `Input::digest` (`InputDigestSpec`), `try_allocate_in` (`TryAllocSpec`), `memcpy` (`MemcpySpec`), `verify_execution` (proved from `walk`), `handle_error` and `halt` (`NoReturn`) |
| `walk` | 762 | specified (`Spec/Walk/Execution.lean`), not proved | its proof; 36 callees, among them `Transcript::new`, `next_scalars`, `grind_check`, `Sponge::sample`, `finish`, `grinding_bits`, `build_layout`, `verify_bus_balance`, `table_sumcheck`, `powers`, `verify_keccak`, `ring_switch`, `read_ood`, `verify_stacked_opening`, `Digest::halves`, `Digest::from_halves`, `Layout::committed`, `dot`, `multilinear_eval_k`, and the runtime's allocation, growth, clone, drop and panic functions |

## `main`, where it stands

`rv_auto` over `main` with stops at the five loop heads (labels 74, 117, 154, 193, 219; the stream, phase, path, leaf-copy and sibling loops) and `Bytecode::new`'s ghost words given as `(words.drop 1).take (words.headD 0).toNat`:

* without `rv_sym.heap`, it steps every path to the loop heads and leaves 82 goals: the callees' functional preconditions (the result slots `Owned` and aligned, the input slice's `WordsAt` and `Live` from `MainPre`), `main`'s saved registers across `Bytecode::new` (its `Out` is its result slot, so they are `Frame.getMem_above` facts), the Err path's `1 = 0 → Verdict` (vacuous), and the loop entries;
* with `rv_sym.heap`, it stops at the calls of `Bytecode::new` and `Input::digest` with their `Holds.pre` whole (69 s, 3 GB): the result slots in `main`'s frame and the input region below the heap are not among the objects it places.

What remains is the five loop invariants against `decodeInput`'s `readMany` (the stream's `E`s from word pairs, each phase's `Vec<MerklePath>`, each path's leaf `Vec<K>` and siblings `Vec<Digest>` filled by `Input::digest` then `memcpy`), the `Bytecode` moved from the result slot to `sp + 0x58` (`BytecodeAt` through an 8-word copy), and the end: the input exhausted (else `halt(2)`), `verify_execution`'s `Ok` giving `mainVerdictRust … = true`, then `verdict_of_accept`.
