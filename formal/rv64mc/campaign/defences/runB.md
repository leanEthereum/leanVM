# Defence: rv_symT / rv_autoT, the symbolic executor for total (HoldsT) goals, with evidence on real functions

Base: f8a3acbbe6. Head: cf55f641fb (5 commits: 82da82fe75 tactic, 40353a0ea5 ports + InputWordT, c411697b60 MemcmpT, e9d0265f93 AllocT, cf55f641fb docs).
Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Tactic.StepsT Rv64mc.Tactic.SymT Rv64mc.Proof.Field.ReduceT Rv64mc.Proof.Field.SpreadT Rv64mc.Proof.Field.ESquareT Rv64mc.Proof.Hash.DigestFromHalvesT Rv64mc.Proof.Runtime.InputWordT Rv64mc.Proof.Runtime.AllocT Rv64mc.Proof.Runtime.MemcmpT` -> `Build completed successfully (4473 jobs)` (warm; each module was built cold once earlier in the run, e.g. DigestFromHalvesT 29 s, the others 4 to 10 s). `warningAsError = true` in the lakefile, so these modules have no warnings.

No full `lake build Rv64mc`: `Sym.lean` and `Steps.lean` are untouched, and no existing module imports a changed one (see Invariants).

## Decisions

### D1. New `Tactic/SymT.lean` (and `Tactic/StepsT.lean`) instead of generalizing `Sym.lean`
- **Why**: `Sym.lean` is imported by every proof module; editing it costs a full rebuild and puts `rv_sym`'s `SafeN` behaviour at risk. The task prefers a new file.
- **Rejected**: parametrizing `Sym.lean`'s `run`, `parseAt`, `absorbFacts`, `finish` over the judgement's head constant and rule names. It is the better long-term design (no duplication), but needs the full rebuild and a behaviour-preservation argument for 94 proofs.
- **Claims**: `SymT.lean` reuses `Sym.lean`'s functions (`evalE`, `writeReg`, `readMem`, `readByte`, `dataRead`, `dataLoad`, `splitFact`, `addFacts`, `afterCall`, `closeSideSafe`, `arithProve`, `calleeProof`, `targetIdx`, `mkCfg`/`elabArgs`, `nameApart`, `labelIdx?`, `dropAt`, `rvSymArgs` syntax). It duplicates, with the Total head (`Lprog.Isa.Total`, 7 args) and `StepsT` rule names: `parseAtT` (copy of `parseAt`), `absorbFactsT` (of `absorbFacts`), `finishT` (of `finish`), `runT` (of `run`, about 260 lines; the load/store/call/tail cases add side goals), `openContractT`, `rv_autoT`, `rv_introT`. A reviewer should diff `runT` against `run` (Sym.lean lines 2254 to 2513): the label/goto/set/skip/cmp/ret cases and the value computations are meant to be identical apart from rule names.
- **Evidence**: `git diff f8a3acbbe6 -- formal/rv64mc/Rv64mc/Tactic/Sym.lean formal/rv64mc/Rv64mc/Tactic/Steps.lean` is empty.

### D2. `StepsT.lean`: rules with `Steps.lean`'s binder names, `G` fixed to `WinOk p`, `c` general
- **Why**: the executor builds rule applications by binder name (`appN`), so equal names let `runT` be `run` with renamed constants. `c` is left general (only `HoldsT` fixes `stmtCtx`), `G` is `WinOk p` because each rule discharges it.
- **Rejected**: reusing `TStep.lean`'s `TotalRv.ld8`/`sd8`/`sb` (address as `a.eval regs`, only three widths, no computed-result form).
- **Claims**: `stepT_ld`, `stepT_loadw`, `stepT_sd`, `stepT_storew` take the address facts as `inWindow x w.bytes = true`, `x.toNat % w.bytes = 0` and (stores) `noCodeAt m x w.bytes = true`, all four widths; `stepT_call`/`stepT_tail` are `Total.call_contract`/`tail_contract` with `WinOk.of_ne`. `parseAtT` refuses a goal whose `G` is not syntactically `WinOk _`.
- **Evidence**: `lake env lean Rv64mc/Tactic/StepsT.lean` -> no output (6.8 s).

### D3. Side goals closed by `omega` with `rv_sym.heap` forced on, only for the new side goals
- **Why**: windows and alignment are linear facts over the stack bound, `Windows`' fields, the layout and `Pre`; `arithProve` already gathers them but is gated by `rv_sym.heap`. Forcing the option only inside `winProof`, `alignProof`, `windowsGoal` (`withArith`) keeps every other behaviour (memory reads, frames, literal branches) as the user's option says, so a ported partial proof sees the goals it saw before.
- **Rejected**: forcing heap mode for the whole of `rv_symT` (changes the leftover goals of ported proofs); dedicated lemma-based closers per window kind (`Windows.stack`, `heapObj`, ...) (more code, omega covers all of them).
- **Claims**: a window goal is proved as `inWindow_iff.mpr` of an omega proof; an unproved one is left as `inWindow x n = true`; alignment of a byte access is `Nat.mod_one`, never omega.
- **Evidence**: in every port below no window, alignment or noCodeAt goal is left except InputWordT's slice word (its bound is under an implication in `WordPreT`, which `arithProp` does not read).

### D4. `noCodeAt` and `Windows` at a callee from the entry's `Windows` and the code map kept (`codeWalk`, `noCodeAt_of_windows`, `windowsGoal`)
- **Why**: `noCodeAt` depends only on `code`; every store and every `HoldsT` callee keeps `code`, so the entry's `Windows` suffices.
- **Claims**: `codeWalk M T` proves `M.code = T.code` through `setMem/setByte/setHalfword/setWord32` and hypotheses `M.code = X.code` (from `HoldsT.post` via `afterCall`'s `hret` facts, or a loop invariant). `windowsGoal` builds `Windows.callee (Windows.after hw hc hn) hle`, skipping `after` when the memory is the entry's and `callee` when the top is the same; `hn` (NEXT not lowered) and `hle` are omega side goals left if unproved.
- **Evidence**: ESquareT (two calls, stack stores and loads) leaves only the two value goals: `rv_autoT hp with [hL] using [hsp, hrd]` followed by the partial proof's `simp only` closes the module.

### D5. `Q` at a callee's stopping states by the caller's `hstop` (`closeStop`)
- **Why**: `HoldsT.call` adds this goal; for the usual caller whose `Stop` contains the callee's it is the caller's `hstop`.
- **Claims**: after intro of `fr st r' m' hs ha`: closed by `False.elim` if `hs : False`; else by a local of shape `∀ 6 binders, ... → Q ...` whose conclusion unifies with the goal and whose 6th binder's type with `ha`'s, leaving the caller's stopping condition, which is closed by a hypothesis (including `hs`'s split conjuncts `hs_k`) or `closeSideT`, or left. If no such local exists, the whole goal is left. The match only selects which proof term to build; the kernel checks it.
- **Evidence**: InputWordT: the abort through `Aborts` leaves exactly `m.getMem (inputLenAt (regs .x10)) = 0` (the second conjunct of `WordStop`), closed by `rw [inputLenAt_eq]; exact hc`. AllocT: leaves `env.heapEnd.toNat < ...` likewise.

### D6. `afterCallT` reuses `Sym.afterCall` and recovers its `hret<k>_j` facts by name
- **Why**: `afterCall`'s last step, `absorbFacts`, is a no-op on a Total goal (it checks for `SafeN`); everything else it does is wanted. Reusing it avoids copying 50 lines.
- **Rejected**: copying `afterCall` with `absorbFactsT`.
- **Claims**: the facts are the locals whose user name starts with `hret<k>_`. An older shadowed `hret<k>_j` from an earlier `rv_symT` call in the same proof may be included; `absorbFactsT` only uses facts `R0 r = v` for the goal's own register file `R0` (the fresh `r<k>`), so an older fact is ignored. Reviewer: this name dependence is the most fragile piece; it relies on `addFacts` naming with `appendIndexAfter`.

### D7. Ports: `ReduceT`, `SpreadT`, `ESquareT`, `DigestFromHalvesT`, `MemcmpT` (new modules, partial postconditions kept)
- **Claims**: each `specT`/`MemcmpSpecT` is `HoldsT env p i need Pre' Post Out` with the partial spec's `Post` and `Out` constants (`Reduce.Post`, `Spread.Post`, `ESquare.Post`, `DigestFromHalves.Post`/`Out`, `CmpPost`), `Stop` the default `False`. Pre: `reduce`, `spread`, `E::square`: `fun _ _ => True` as the partial. `from_halves`: `PreT := Pre env regs m ∧ InWin env (regs .x10) Layouts.Digest.byteSize`. `memcmp`: `CmpPreT := (regs .x12).toNat = 0 ∨ (InWin env (regs .x10) n ∧ InWin env (regs .x11) n)`.
- **Call sites (argued from the templates, not proved)**:
  - `from_halves` (callers per `cg.json`: `walk`, `verify_whir`'s closure 1): `walk` passes `a0 = sp + 0x380` with frame `0x4f0` (`Walk.lean` lines 111, 341); the closure `a0 = sp + 0x1c8` with frame `0x2c0` (line 125, 685). Both slots plus 32 bytes lie below the caller's stack top, so `stackLimit ≤ a0` (caller's stack bound) and `a0 + 32 ≤ top ≤ 0xc0000000` (`Windows.top_le`): `InWin`'s stack disjunct. I did not check that `sp` is not moved between the prologue and the call.
  - `memcmp` (callers `Transcript::merkle`, `Form::add_scaled`): merkle passes `a0 = sp + 0` (frame `0x50`, 32 bytes, in its frame: stack disjunct) and `a1 = x8`, the `root` it is passed, which is in a window only if merkle's own (future) total contract says so; `add_scaled` passes two vectors' buffers (`x20+8`, `x19+8` loads) and `n = len << 3`: heap objects (heap disjunct, given `0x10000000 ≤` allocated pointers and their end `≤ NEXT ≤ heapEnd`), and when `len = 0` the dangling pointer is covered by the `n = 0` disjunct. None of this is proved; the callers have no total contracts yet.
- **Rejected**: a stack-only window for `from_halves` (both sites are stack slots, but `InWin` is weaker for callers and already exists in `MemsetT.lean`); a new `Core` predicate for pointer windows (would duplicate `MemsetT.InWin`). Consequence: `DigestFromHalvesT` and `MemcmpT` import `Proof/Runtime/MemsetT`.
- **Evidence**: each file elaborates with its `#guard_msgs in #print axioms` block pinning `[propext, Classical.choice, Quot.sound]` (no output from `lake env lean`). The partial proofs' closing scripts are reused verbatim for Reduce, Spread, ESquare, DigestFromHalves (with `hpre_1` to `hpre_7` the same names; the added `InWin` is `hpre_8`).

### D8. `DigestFromHalvesT` clears `hpre_8` (InWin) and `hpre_10` (Windows) after `rv_autoT`
- **Why**: the partial closing script calls `omega` many times; the extra disjunction doubled its case split. Measured 43.5 s without the `clear`, 30.0 s with.
- **Claims**: neither is needed after `rv_autoT` (the windows are already closed).

### D9. `InputWordT.total` and `AllocT.total` re-proved in place by `rv_autoT`
- **Claims**: statements byte-identical; only the proof bodies, the import (`TStep` -> `SymT`), one sentence of each header and `roundUp_toNat`'s docstring changed. `AllocT` passes the link fact `hd : L.d_NEXT.hi + L.d_NEXT.lo = env.nextAddr` in `with` and as a local `have`, from which omega gets the NEXT access's window and alignment.
- **Evidence**: `diff <(git show f8a3acbbe6:formal/rv64mc/Rv64mc/Proof/Runtime/$f.lean | sed -n '/^theorem total/,/:= by/p') <(sed -n '/^theorem total/,/:= by/p' .../$f.lean)` empty for both; `git diff f8a3acbbe6 -- .../InputWordT.lean .../AllocT.lean | grep -E '^[-+].*(theorem|def )'` empty.

## Measurements (method: `lake env lean <module>` with imports built, wall time, best of two, this machine, another agent building in a sibling worktree; script `runB/measure.py`, output `runB/measure.txt`; old versions from `git show f8a3acbbe6:...` timed the same way)

| function | before (file lines / theorem lines / s) | after |
| --- | --- | --- |
| reduce (partial) | 22 / 5 / 7.2 | ReduceT 39 / 5 / 7.3 |
| spread (partial) | 23 / 5 / 5.3 | SpreadT 39 / 5 / 5.3 |
| E::square (partial) | 26 / 7 / 5.6 | ESquareT 45 / 7 / 6.7 |
| from_halves (partial) | 83 / 25 / 25.0 | DigestFromHalvesT 68 / 26 / 29.4 |
| memcmp (partial, lsym, loop lemma + ok) | 116 / 61 / 6.9 | MemcmpT 92 / 47 / 6.0 |
| Input::word (total, TStep) | 139 / 60 / 7.1 | 110 / 31 / 5.9 |
| alloc (total, TStep) | 114 / 51 / 7.5 | 93 / 29 / 6.2 |

"Theorem lines" = non-blank lines from the main theorem (and for memcmp the loop lemma / `LoopInv`) to the namespace's `end`. About 3 to 4 s of each time is import loading. T files reuse the partial files' lemmas, so their file line counts are not self-contained.

## Invariants of the whole change
- No existing statement changed: the only modified Lean files are `InputWordT.lean` and `AllocT.lean` (D9); all other Lean files are new. `git diff f8a3acbbe6 --stat` lists 11 files, all under `Tactic/`, `Proof/`, `README.md`, `notes/total-correctness.md`.
- `rv_sym` on `SafeN` unchanged: `Sym.lean`, `Steps.lean` untouched (D1).
- No dependent rebuilt beyond the listed modules: `grep -rln "Proof.Runtime.AllocT\|Proof.Runtime.InputWordT" Rv64mc` lists only the files themselves.
- No `sorry`/`admit`/`axiom`/`native_decide`/`bv_decide`/`implemented_by`/`maxHeartbeats` in changed files: `grep -nE "sorry|admit|native_decide|bv_decide|^axiom|implemented_by|maxHeartbeats" $(git diff f8a3acbbe6 --name-only | grep lean$)` is empty. (`cheapDefEq`'s heartbeat budget is in `Sym.lean`, untouched.)
- No em/en-dashes in changed files (grep count 0).

## Not done
- MemsetT not re-proved: it already uses `TStep`'s macros and custom `Kept`/`Base` frame reasoning; a port would save some `TotalRv.sb/sd8` lines only. Stopped there as marginal.
- No `ECALL` rule in `rv_symT` (`Total.ext_done` by hand, as `HaltT.lean`); no `rv_sweepT`.
- `grow_one`/`finish_grow` not ported (they call memcpy, which has no total contract).
- Call-site truth of `PreT`/`CmpPreT` argued from templates, not proved (D7).
- No `#guard_msgs` axiom blocks for the `StepsT` rules themselves (their axioms flow into the guarded `total` theorems).
- No full `lake build Rv64mc` (not required: Sym/Steps unchanged).

## Known risks
- `runT` is a copy of `run`: a later fix to `run` will not reach it (D1). Look for divergences other than rule names.
- `afterCallT`'s name-based recovery of `hret<k>_*` (D6).
- `closeStop`'s use of `forallMetaTelescopeReducing` on every local: whnf of contract hypotheses (e.g. `hhalt : Aborts ...`) on each call; cost not measured on a function with many calls.
- `DigestFromHalvesT` is 4.4 s slower than its partial even with the `clear` (D8): 32 window omega calls; on larger functions with many pointer stores this cost grows linearly.
- `hpre_k` numbering is part of the ported scripts (`hpre_10`, `hI_19`, `hc_2` in MemcmpT): fragile under changes to the Pre or the executor's naming, as in the partial proofs.

## Golf

Commit 9bc7e3c352 on cf55f641fb (`refactor(formal): golf rv_symT and its rules`). 3 files, +74 / -116: `SymT.lean` 719 -> 687 lines, `StepsT.lean` 179 -> 172, `InputWordT.lean` 110 -> 107. No statement changed (every `theorem` and `def` signature is byte-identical; `git diff cf55f641fb | grep -E '^[-+](theorem|def )'` lists only the moved `stepT_ld`/`stepT_sd` headers, removed and re-added unchanged). `Sym.lean`/`Steps.lean` untouched. Skills: `lean4:golf` and `lean4:refactor` loaded.

Check (after the last change): `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Tactic.StepsT Rv64mc.Tactic.SymT Rv64mc.Proof.Field.ReduceT Rv64mc.Proof.Field.SpreadT Rv64mc.Proof.Field.ESquareT Rv64mc.Proof.Hash.DigestFromHalvesT Rv64mc.Proof.Runtime.InputWordT Rv64mc.Proof.Runtime.AllocT Rv64mc.Proof.Runtime.MemcmpT` -> `Build completed successfully (4473 jobs)`, every module rebuilt (SymT 8.6 s, DigestFromHalvesT 29 s, others 3 to 5 s). Since every port's closing script is unchanged and still closes, the executor leaves the same goals on them. `#guard_msgs` axiom blocks unchanged and passing.

### G1. `stepT_ld` := `stepT_loadw (w := .b8) (s := false)`, `stepT_sd` := `stepT_storew (w := .b8)` (StepsT.lean)
- **Why equivalent**: same statements; only the proofs change, to a term. `loadVal .b8 m x` is `m.getMem x` and `storeMem .b8 m x v` is `m.setMem x v` by `Steps.lean`'s definitions (match on a constructor), `if false = true then _ else t` reduces to `t`, and `Width.b8.bytes` to `8`, so each hypothesis has the general rule's type up to definitional unfolding; the kernel accepts it. The two theorems moved below the general ones (they now cite them); `runT` names rules, not positions.
- **Check**: `lake env lean Rv64mc/Tactic/StepsT.lean` no output; the build above.

### G2. `noCodeAt_of_windows`: `have := ...; simpa ... using this` -> `simpa ... using hw.noCodeAt hx hn` (StepsT.lean)
- **Why equivalent**: the same term given to the same `simpa only` set. Statement unchanged.

### G3. `runT`: local helpers `fall`, `load`, `viaContract` (SymT.lean)
- **What**: `fall c R' M' xs side` is the block every fall-through step repeated (`newGoal` at `a.goal (a.pc + 1) R' M'`, `g.assign (appN c (base ++ xs ++ [(h, h)]))`, `some (side ++ [h])`); used by label, set, both stores, skip and every load. `load c v hv xs` adds `writeReg` and the load's common arguments; the three `stepT_loadw` arms (data, byte, generic) now compute `(val, hv)` and share one `load`. `sext`/`pick`/`choose` name the sign extension, the value `if s then sext t else t` and the `ite` term each arm built inline. `viaContract c pre side` is the shared tail of the call and tail call (`hstop`, `hk` by `nextBinder`, the rule applied, the side goals, `hstop` closed, `afterCallT`).
- **Why equivalent**: `appN` matches arguments by binder name (`args.lookup n`), so the order of the list does not change the term built. Each arm passes the same named arguments as before (checked line by line in the diff: ld `rd a x v R' ha hv hR` ++ acc; loadw the same plus `w s`; sd `a e x v ha hv` ++ acc; storew the same plus `w`; set `rd e v R' hv hR`; label `kd l`; skip none). The goals returned are in the same order (`side ++ [h]`; calls `side ++ hstop's leftovers ++ afterCallT`). Effects run in the same order: `accessFacts`, then the value, then `writeReg`, then `newGoal`; for calls, the side-goal closing is passed as an unevaluated `MetaM` action and run after `g.assign`, as before (for the tail call as an explicit `do` block, so its `←` do not lift out of it). The byte arm's `f` is `lam word choose`, the same lambda as the inline `fun t => mkAppM ite #[s = true, sext t, t]`; `pick lv` is the old `val`; `choose lvM` the old `ite`.
- **Not exercised**: no ported template has an `Ltail`, so the tail branch's equivalence rests on reading (above); its first version (`(return (← ...) ++ ...)`, which would have lifted the closers before `viaContract`) was caught on reading and replaced by `(do return ...)` before the commit.
- **Cost to D1**: `runT` no longer diffs line for line against `Sym.run`; it is `run` with these three helpers factored out, the rule names, and the side goals.

### G4. `codeWalk`'s store chain as a table; `closeSideT`'s `Windows` branch with `Option.getD` (SymT.lean)
- **Why equivalent**: `stores.find? (M.isAppOfArity ·.1 3)` tests the same four heads in the same order with the same arity and yields the same `code_*` lemma. `return (← windowsGoal g ty).getD [g]` is `if let some l ← windowsGoal g ty then return l; return [g]`.

### G5. InputWordT: the static-region case `exact Env.static_setMem (Env.static_setMem hpre_4 (by omega)) (by omega)` (was two `have ... := by omega` and the same `exact`)
- **Why equivalent**: the two `omega` goals are the `have`s' types, fixed by `Env.static_setMem`'s argument types after unification with the goal; the proof body is the change's (D9 rewrote it), the statement untouched. Elaboration 6.1 s (`lake env lean`, was 5.9 s in the measurement table: within noise).

### Tried and not kept
- `widthBytes` as a `List.lookup` table: no shorter (3 lines either way), less direct.
- Further proof golfs in the ports (DigestFromHalvesT's `all_goals have` chain, MemcmpT's `InWin` steps): no line saving without `;` or would cost a 30 s rebuild per attempt for one line; stopped as marginal.
- `absorbFactsT`, `parseAtT`, `finishT` stay copies of `Sym.lean`'s: sharing them needs an edit to `Sym.lean` (full rebuild, D1).

## Amendments, round 1

Head after this round: 447b74b80c (one commit on 9bc7e3c352: `fix(formal): end rv_symT's code walk on a cycle of code facts; notes' claims`). The header's "Head: cf55f641fb (5 commits)" is stale: the reviewed head was 9bc7e3c352 (6 commits, the sixth the golf), and the head is now 447b74b80c (7 commits). Skill `lean4:prove` loaded.

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Tactic.SymT Rv64mc.Tactic.StepsT Rv64mc.Proof.Field.ReduceT Rv64mc.Proof.Field.SpreadT Rv64mc.Proof.Field.ESquareT Rv64mc.Proof.Hash.DigestFromHalvesT Rv64mc.Proof.Runtime.AllocT Rv64mc.Proof.Runtime.InputWordT Rv64mc.Proof.Runtime.MemcmpT` -> `Build completed successfully (4473 jobs)`, SymT and every module importing it rebuilt (SymT 8.9 s, DigestFromHalvesT 29 s, others 3.5 to 5.3 s), 41.6 s wall. `Sym.lean`/`Steps.lean` untouched, so no full build.

### R1-1 (codeWalk cycle): fixed
- **What changed**: `codeWalk M T (seen : List Expr := [])` returns `none` when `M` is already in `seen` and passes `M :: seen` to both recursive calls (the store arm and the context arm). Callers unchanged (default argument). The set is per path, so a memory blocked on one path is still tried on another; a path never repeats a memory, so the walk ends (the context and the store chain are finite).
- **Evidence**: `runB/rev1/CycleProbe.lean` (the reviewer's probe, `h1 : m.code = m1.code`, `h2 : m1.code = m.code`, then `rv_symT`) under `timeout 600 systemd-run --user --scope -q -p MemoryMax=16G lake env lean` now prints only `warning: declaration uses 'sorry'` (the probe's own sorries), exit 0; before, a deep-recursion abort with exit 141. The ports' closing scripts all still close (build above), so the walk finds the same proofs on acyclic contexts.
- **D4 amended**: D4's claim holds, now also on a context with a cycle of code facts, where the walk fails over that edge instead of aborting.

### R1-2 (stale counts and head): fixed
- **What changed**: `notes/total-correctness.md`'s row is now `by rv_autoT: 107, 28, 6.1 s`. The defence's Measurements row (line 68, `110 / 31 / 5.9`) and header (line 3) are earlier entries and stay as written; this amendment supersedes them: Input::word after is 107 / 28 / 6.1, head 447b74b80c.
- **Evidence**: `wc -l InputWordT.lean` 107; the theorem's non-blank lines from `theorem total` through `end Rv64mc.Proof.Runtime.InputWordT` 28 (the same count gives AllocT 29, the table's). Time: `lake env lean Rv64mc/Proof/Runtime/InputWordT.lean`, five runs this session 6.38, 6.12, 6.67, 6.17, 6.36 s, best 6.1 s (G5 had already measured 6.1 s). AllocT in the same session 6.96, 6.51, 6.37 s against the table's 6.2 s, so the machine is about 0.2 s slower than at the first measurement; InputWordT's 5.9 -> 6.1 is within that noise and is not a slowdown of the golf. The other rows were not re-measured.

### R1-3 (notes overstate): fixed
- **What changed**: line 22 now reads "(`rv_symT` does each but a loop's or a recursive function's measure and `Total.ext_done`, below)", consistent with line 39. The closing sentence now says the proofs are the partial ones "except `memcmp`'s loop, a new `Total.loop` proof in place of the partial loop lemma, and `DigestFromHalvesT`'s `clear` of two window facts".
- **Evidence**: `grep -n clear DigestFromHalvesT.lean` -> line 40 `all_goals clear hpre_8 hpre_10`, none in `DigestFromHalves.lean`. No em/en-dashes in the edited files (grep for U+2013/U+2014 empty).

### R1-4 (D9 overstates the header change): fixed (in this amendment)
- **What changed**: D9's "one sentence of each header" is wrong; it should read "one sentence of AllocT's header". InputWordT's header is unchanged.
- **Evidence**: `git diff f8a3acbbe6..9bc7e3c352 -- InputWordT.lean` hunks at lines 24 (the import) and 70 (the proof body) only; AllocT's at 6 (header), 19, 37 and 59.
