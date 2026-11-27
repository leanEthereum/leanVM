# Proving one function total

Read first, in this order: `formal/rv64mc/notes/total-correctness.md` (what `HoldsT` is, "Proving a function total", "Stepping total goals: `rv_symT`, `rv_autoT`", "Porting a partial proof to total"), `notes/how-to-prove-a-function.md` (the partial proofs' recipe, whose executor the total one reuses), `Rv64mc/Tactic/SymT.lean`'s header. Then read two or three finished total proofs close to your function: the module named in its callees' rows of `notes/total-status.md`, and the examples below.

## What a contract is

A function is a template in `Rv64mc/Gen/Tmpl/<path>.lean` (its instructions, generated) with a `Link` structure in `Rv64mc/Gen/Link/` naming its callees' indices. Its total contract is

```lean
HoldsT env p i need Pre Post Out (Stop := AbortStop)
```

- `Pre regs m`: what holds at entry (arguments in registers `x10` to `x17`, memory `m`). `HoldsT` adds `Windows` (stack, heap, static data bounds) and the calling convention.
- `Post regs m r' m'`: what holds at return. `Out regs m a`: the memory frame, which bytes it may change.
- `Stop`: where the function may end the whole run instead of returning. `AbortStop` (`a0 = 2`, `Core/AbortStop.lean`) for anything that may panic or run out of heap; the default `False` for a function that never aborts. Weaken a finer callee stop with `HoldsT.mono_stop`.
- `MainSpecT` needs only safety and termination, so a function's total contract states only what its callers need: its result's representation (a vector's pointer, capacity and length in a window and aligned, `VecT`; a `Form`'s, `FormT`), what it leaves unchanged (`Out`), and, where a caller's later safety depends on them, values.

The proof is a `theorem total … : SpecT env p i need` over the template, plus a `Table` instance at the binary:

```lean
-- Rv64mc/Table/FormT6g.lean, verbatim in substance:
variable (env : Env) (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
  (hend : env.heapEnd = 0x78000000#64)
include hnext hend

theorem sumArr3 (hd : FieldT.ClmulTable env) :
    SumArr3T.SpecT env (liftProg fns) Idx.Verifier.Layout.Form.SumArrFormN3 Needs.Verifier.Layout.Form.SumArrFormN3 :=
  SumArr3T.total env _ _ _ Verifier.Layout.Form.SumArrFormN3.tmpl_eq Verifier.Layout.Form.SumArrFormN3.wf
    (by decide) (FormT6e.formAdd env hnext hend hd)

/-- info: 'Rv64mc.Table.FormT6g.sumArr3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FormT6g.sumArr3
```

`hnext`, `hend` (the allocator's two facts, `env`) and `hd` (a static-data table) are the environment facts; the last arguments are the callees' `Table` theorems. Copy the shape from an existing `Table/*T6*.lean`. A `Table` theorem's only hypotheses may be environment facts (static data words, `env`'s facts), each listed in the legend at the top of `notes/total-status.md`.

## Choosing the contract

1. Look up the function's row in `notes/total-status.md` and its class in `campaign/waves.md`: **A** (a partial proof `Holds` exists at the binary), **C** (a functional spec in `Rv64mc/Spec/`, no proof), **D** (nothing).
2. **Class A**: keep the partial postcondition. Either port the partial proof (`rv_auto` to `rv_autoT`, recipe in `total-correctness.md`), or prove a safety-only `HoldsT` and combine it with the partial proof by `HoldsT.of_holds_post` (`Proof/Field/KInvT.lean` does this for a 291-instruction function).
3. **Class C**: use the spec's contract with window facts where cheap; otherwise a safety contract, and record the functional one under "Owed by contracts already total".
4. **Class D**: a safety contract.
5. **Every conjunct of `Pre` must hold at every call site in the binary**, or the contract is vacuous where it is used. `python3 campaign/scripts/sites2.py <name>` (from `formal/rv64mc`) prints each call site with the instructions before it; check what each argument is there (a frame slot, a heap vector, an empty vector with a dangling pointer, a static table). This has failed four times: heap-only slices where callers pass stack slices or empty vectors (`Proof/Multilinear/OwnSliceT.lean` is the fix), and similar.
6. **Every `Post` must give what each caller needs afterwards**, especially inside the caller's loops. This has failed five times (a missing freshness fact, a missing length, a footprint not apart from a later allocation). Before proving, read each caller's template and its row's obligations, and write in the defence which caller uses which conjunct.
7. Earlier contracts' preconditions that were argued, not proved, are listed under "Obligations": when your proof calls such a callee, it proves the precondition at the call. If it cannot, that is a finding against the callee's contract: write it in the defence with the call site and propose a corrected contract in a new module (`…OwnT`, `…AlT`, `…SafeT`), proved over the template or from the old one. Never weaken your own statement to dodge it.

## Shared representations (use them, do not redefine)

| module | what |
| --- | --- |
| `Proof/Runtime/VecReprT.lean` | `BufT`, `RawVecT`, `VecT`: a `Vec`'s header and buffer |
| `Proof/Runtime/SavedT.lean` | `Saved`, `MemOk`: callee-saved registers' slots for any slot count, kept across calls and stores |
| `Proof/Runtime/WinT.lean`, `MemsetT.InWin` | window lemmas; `InWin env a n` |
| `Proof/Multilinear/OwnSliceT.lean` | `OwnSlice`: a slice empty, or owned by the caller, in a window and aligned |
| `Proof/Layout/FormReprT.lean`, `FromElemVecFormT.lean` | `FormT`, `FormsT`, `VecFormT`: a `Form` and a `Vec<Form>` |
| `Proof/Layout/PairFormT.lean`, `FlushesMoveT.lean` | `FlushesFormT`: a `Flushes` of `Form`s; its move into another slot |
| `Proof/Transcript/TranscriptReprT.lean` | `TranscriptAtT`, `OwnedT`: the transcript |
| `Proof/Field/ESumWinT.lean` | the `E::sum` closures' table predicate and loop continuation |
| `Proof/Runtime/HaltT.lean`, `PanicsT.lean` | `Aborts`: a function that never returns |

## Mechanics that worked

- `rv_autoT hp stop [pcs] with [facts] using [callee contracts]` opens the contract and steps to the listed program counters; `rv_symT` continues from a state; `rv_introT`, `rv_closeT` as in `total-correctness.md`.
- Loops: `Total.loop` at the head with a `Nat` measure that strictly decreases (`Proof/Runtime/MemcmpT.lean`, `MemsetT.lean`); the induction hypothesis where the executor stops at the head again.
- Long bodies: cut into parts at program counters, each a lemma that starts from a state with only a frame invariant (`Proof/Hash/KeccakFT.lean`). One executor run costs more than linearly in its calls: keep a part to about twelve calls (`Proof/Field/KInvT.lean`: twelve calls about 96k heartbeats; 18 calls exceed the default 200k).
- Large facts in a part's context slow every `omega` the executor runs: hide them as `True → P`, and seal a callee's pre and post as `@[irreducible]` definitions read by lemmas (`Proof/Layout/StateDerivedT.lean`).
- After a branch on a bit-vector equation (`hc : x + c = y`), `clear hc` before the next `rv_symT`: every later `omega` splits on it (minutes to seconds).
- Avoid blanket `simp` and `simp only [BitVec.toNat_add, BitVec.toNat_ofNat]` over register files and memory after a call: they run out of memory. Read registers by `rf_get_<r>` and memory by lemmas on the addresses.
- A `local macro` with `hygiene false` shares one closing script across parts of the same shape (`DropSliceT`, `KeccakFT.round_part`).
- The executor's own source (`Tactic/`) is shared by every proof: editing it rebuilds everything. Report an executor bug in the defence instead; if a fix is unavoidable, make it behaviour-preserving, add a check to `Tactic/SymTest.lean`, and run the full build once.

## Iterating

- Check one file: `cd formal/rv64mc && timeout 1800 lake env lean Rv64mc/Proof/<path>.lean`. It re-elaborates the whole file: 20 to 35 s typically, minutes for large ones. In the last waves about half of all wall-clock time went to these checks.
- Much faster: the Lean language server re-elaborates only from the first edited declaration, and inside a tactic proof from the edited step. Through an MCP server (`lean-lsp-mcp`): `lean_diagnostic_messages` after each edit, `lean_goal` for the state at a line, and `lean_multi_attempt` to try several tactics at one position without editing (the fastest way to close the executor's leftover side goals). Each open file is a Lean process holding the file's imports (several GB): close files you are done with. If several worktrees share one MCP server, check it handles several Lake projects before relying on it.
- Before each commit: `lake build <the new modules>` (with `LEAN_ABORT_ON_PANIC=1`) and the axioms pin.
- Give every Lean command a `timeout`.

## Per function, the commit contains

1. `Rv64mc/Proof/<Area>/<Name>T.lean`: the contract (`PreT`, `PostT`, `SpecT`) and `total`, with a module docstring (what it proves, main definitions, main results).
2. Its `Table` instance in a new file `Rv64mc/Table/<Family>T<batch>.lean` (check `git ls-files formal/rv64mc/Rv64mc/Table` for free names), or appended to the batch's file.
3. Its row in `notes/total-status.md` set to `yes` with module, `Table` theorem and open hypotheses; any obligation struck or added; any new open hypothesis added to the legend with what it is. Leave the summary counts to the merge.
4. `README.md`'s `Proof/` bullet and `Table/` list (in `formal/rv64mc/README.md`, "Layout") extended with the new modules.
