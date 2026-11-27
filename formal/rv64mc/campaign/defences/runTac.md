# Defence: the executor's `appArg!` panic and its ignored `through`

Base: 45d46c4730. Head: 37968c5021 (four commits, not pushed: 7ea05b09b0 the fixes, the test and docs; d45a63af7f a repair of `FromElemT.tail`; c7c4b0ea25 its revert; 37968c5021 the fixes made behaviour-preserving, see D5). Read the net diff `git diff 45d46c4730..37968c5021`; the middle two commits cancel. Worktree /home/devops/leanEthereum/leanVM-t-symt; logs and scratch files in this run directory.

Check: `cd formal/rv64mc && LEAN_ABORT_ON_PANIC=1 timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G --setenv=LEAN_ABORT_ON_PANIC=1 lake build Rv64mc.Tactic.SymT Rv64mc.Proof.Bus.TryMapT`
- at base: `✖ Building Rv64mc.Proof.Bus.TryMapT`, `PANIC at Lean.Expr.appArg! Lean.Expr:935:15: application expected`, `error: build failed` (check0.log);
- at 37968c5021: `Build completed successfully (4541 jobs).`, exit 0, 7 min 2 s, `grep -c PANIC check3.log` -> 0.

Full build (`lake build Rv64mc`, `LEAN_ABORT_ON_PANIC=1`, MemoryMax=20G, `timeout 7200`, after `free -g` showed 25 GB available) at 37968c5021: `Build completed successfully (6071 jobs).`, exit 0, 11 min 25 s, `grep -c PANIC full.log` -> 0. It rebuilt every module importing Tactic/Sym, including FromElemT, FromElemOptT, TryFromFnT and Tactic/SymTest.

Skills: lean4:prove, lean4:refactor, writing-lean-proofs loaded.

## Decisions

### D1. The panic's cause: `alignGoal` (Tactic/Sym.lean), a `(← …)` hoisted out of an `&&` guard
- **Finding**: `alignGoal` read `unless lhs.isAppOfArity ``HMod.hMod 6 && (← natVal? lhs.appArg!) == some 16 && (← natVal? ty.appArg!) == some 0 do return none`. `do` notation lifts each `(← …)` to a bind before the statement, so both `natVal?` calls run before `isAppOfArity` is tested. In `TryMapT.fin`, after the return, `closeSide` meets the postcondition's conjunct `vecLen M' (regs .x10) = m.getMem (regs .x11 + 16#64)`, `memTy` reads the `vecLen` through the stores to the stored `n`, and `alignGoal` gets `n = m.getMem (regs .x11 + 16#64)` with `lhs` the free variable `n`: `lhs.appArg!` panics.
- **How it was located**: (1) bisecting `fin`'s script on a scratch copy under `LEAN_ABORT_ON_PANIC=1`: `rv_introT hR` alone is clean, `rv_symT hp` aborts (scratch/vA, vB); (2) `rv_symT hp stop [151|161|187|189]` are all clean, so the panic is at or after the return at 189 (scratch/s*.out); (3) temporary probes in `closeSide` and `runT` appending to a file (a command's stdout/stderr is captured into messages and lost on abort): stages 0 to 10 of `closeSide` printed and stage 11 (`arithProve`) did not; (4) a probe at `alignGoal`'s entry printed `lhs ctor=fvar isApp=false: n  rhs: m.getMem (regs Reg.x11 + 16#64)` (scratch/dbg.txt). All probes were removed: `git diff 45d46c4730 | grep -c 'RVDBG\|dbgLog'` -> 0.
- **Fix** (final form, 37968c5021): `let lv ← if lhs.isApp then natVal? lhs.appArg! else pure none`, `let rv ← natVal? ty.appArg!`, then the same `unless lhs.isAppOfArity … && lv == some 16 && rv == some 0`. A comment says why the evaluation stays before the test (D5).
- **Rejected**: catching the panic (not an exception, and out of scope); testing the shape first and skipping the evaluation (7ea05b09b0's form: it changed what the closer closes, D5).
- **Claims**: (a) where `lhs` is an application, the new code runs the same two `natVal?` calls in the same order on the same terms and decides as the old did; (b) where it is not, the old code ran `natVal?` on the panic's default `Expr`, `const _inhabitedExprDummy []`, which returns `none` without throwing (scratch/Dflt.lean), then the same `natVal? ty.appArg!`; the new code takes `none` directly. The only difference is that `whnf` of the dummy constant, which leaves at most a cache entry.

### D2. The same hoisting in `calleeProof` and `neByHyp`'s `offK` (Tactic/Sym.lean)
- `calleeProof`: `if g.isAppOf ``GetElem?.getElem? && (← withReducible (isDefEq g.appArg! f)) then` is now `let same ← if g.isApp then withReducible (isDefEq g.appArg! f) else pure false` and `if g.isAppOf … && same then`.
- `offK`: `unless n.isAppOfArity ``HMul.hMul 6 && (← natVal? n.appFn!.appArg!) == some 8 do return` is now `let k ← if n.isApp && n.appFn!.isApp then natVal? n.appFn!.appArg! else pure none` and `unless n.isAppOfArity … && k == some 8 do return`.
- **Why**: the same panic for a term not an application (a fact `o.map f = some e` with `o` a variable; an offset `BitVec.ofNat 64 k` with `k` a raw literal). Neither fired in any build here.
- **Claims**: where the old code did not panic, the same calls run in the same order. Where it panicked: `offK` evaluated `natVal?` of the dummy (`none`), as now; `calleeProof` ran `isDefEq` of the dummy constant against `f` at reducible transparency, now `false` without the call. I did not check what that `isDefEq` returns or whether it throws; it matters only on inputs that printed a PANIC, and none did.

### D3. Two cheap hardenings (Tactic/Sym.lean)
- `arithProp`'s `Not` arm: `unless n == 1 do return none` before `ty.appArg!`, as its other arms check `n`. A proposition headed by `Not` has one argument, so no change on well-typed input.
- `dataLoad` (the module header calls it `dataRead`): `unless ws.isApp do return none` after `let ws ← inferType hw` (the declared type; the loop tested only its `consumeMData` form). The code is otherwise the old one.
- **The sweep**: every `appArg!`/`appFn!` in `Tactic/` (194 lines in Sym.lean, 21 in SymT.lean, none elsewhere) whose receiver was not tested a few lines above was read; those left are tested at their only call site or by a function's contract (`addV` from `affine`'s result, `roomParam` from its caller's `HAdd`/`toNat` test, `frame_next`'s `Env.next 2`, `lengthMaps`, `opndProof` after `opnd`, `closeSide`'s `∀ a, lo ≤ a → …` case under tests of the binder types, every SymT.lean site). `grep -nE '&& \(←|\|\| \(←' Rv64mc/Tactic/*.lean` lists the other hoisted binds: none reads into an unchecked term.

### D4. `through` (Tactic/Sym.lean `elabArgs`, new `throughHeads`)
- **Finding**: `through` was parsed but read from the wrong nodes. `rvThrough := "*" <|> ("[" num,* "]")` gives a node with one child: `token.«*»[atom "*"]` for `*`, `group["[", null[nums…], "]"]` for a list. `t[0].isToken "*"` is false for the first (`t[0]` is the `token.«*»` node) and `t[1]` is `missing` for the second, so both gave `some []`: nothing removed from `cfg.heads`, every loop head a stop, as wave 4a observed. scratch/Parse.lean (same syntax, the old code, `repr` of the node) prints `thr = some ([])` for `through *`, `through [86, 96]`, and with `stop`/`with` around it.
- **Fix**: `throughHeads` matches by quotation, `` `(rvThrough| *) `` and `` `(rvThrough| [$ks,*]) ``, and throws on another shape (the silent default is what hid this). scratch/Parse2.lean: `*` -> `none`, `[86, 96]` -> `some [86, 96]`, `[]` -> `some []`, mixed with `stop`/`with` -> `some [86, 96]`, absent -> `some []`.
- **Both judgements**: `rv_symT`, `rv_autoT` (SymT.lean) and `rv_sym`, `rv_auto`, `rv_sweep` (Sym.lean) all go through `elabArgs`; `run` and `runT` use `cfg.heads` in the same test (`((cfg.stops.contains a.pc || cfg.heads.contains a.pc) && g != g0) || seen.contains a.pc`).
- **Semantics, now documented** (headers of Sym.lean and SymT.lean, docstrings of `rv_sym`, `rv_symT`, `rv_autoT`): `through` removes heads from the backward-jump stops; a path still stops where it returns to a program counter it has passed (`seen`), so a real loop still stops. No proof uses `through` (`grep -rnE 'through (\*|\[)' Rv64mc --include=*.lean` outside Tactic/ is empty), so no existing proof is affected.
- **Test**: Tactic/SymTest.lean, body `[goto 1, label 0, skip, label 1, goto 0]` (label 0 at 1 is the head): without `through` the goal left is at 1; `through [1]` and `through *` leave it at 3 (where the path returns to a pc it passed); `through [2]` leaves it at 1. Each closes by `exact h1`/`exact h3`, so a wrong stop fails the build. Against the base tactic (Sym/SymT checked out from 45d46c4730): `SymTest.lean:36:2: error: Type mismatch` and `:42:2` (the `through [1]` and `through *` examples); the other two pass (test_base_noabort2.log).
- **Rejected**: indexing `args[1][1][0]` and testing both node kinds by hand (the same fragility); deleting `through` (unused, but the task asks for it to work).

### D5. Why the fixes keep the old evaluation (commits 2 to 4)
- 7ea05b09b0 tested each shape first and skipped the formerly hoisted calls. Its check passed, but the full build (full1.log) failed in `FromElemT.tail`: `No goals to be solved` at its last step `rw [hx12]; omega`, because `all_goals try rv_closeT` now closed a goal it used to leave. d45a63af7f deleted that step; the next full build (full2.log) failed in `FromElemOptT` (`there are no goals left for all_goals rw [hx15]; omega`) and `TryFromFnT` (a `rewrite` whose pattern was gone, then `No goals`); their dependents were not built.
- Bisection on a scratch copy of FromElemT up to `tail` (scratch/fe.lean): base tactic passes; 7ea05b09b0 fails; 7ea05b09b0 with only `calleeProof` reverted fails; with only `alignGoal` reverted passes. Not a heartbeat budget: base with `set_option maxHeartbeats 2000000` on `tail` still leaves the goal (fe_hb.base.out). Not an exception from the eager `natVal?`: a probe running both calls in a `try … catch` that logs and rethrows logged nothing, and `tail` passed with it (no scratch/dbg2.txt; fe.dbg2.out). So the effect is a side effect of the evaluation (metavariable assignment, caches) that I did not identify.
- **Decision**: keep every formerly hoisted call where it ran (D1, D2) and revert FromElemT (c7c4b0ea25). **Rejected**: keeping the stronger closer and repairing proofs one full build at a time (three modules so far, an unknown number of unbuilt dependents, and the task asks that behaviour elsewhere be unchanged).
- **Evidence**: at 37968c5021, scratch/fe.lean (FromElemT's original `tail`) under abort-on-panic -> exit 0; the check passes; the full build above.

### D6. Notes and README
- notes/total-correctness.md, end of the executor section: one bullet per fix (the `through` bullet; the `alignGoal` bullet, which also says why the evaluation stays and names `calleeProof`, `neByHyp`). README: `SymTest.lean` in the `Tactic/` sentence.

## Invariants of the whole change
- Files: `git diff 45d46c4730..37968c5021 --stat` -> README.md, Rv64mc/Tactic/Sym.lean, Rv64mc/Tactic/SymT.lean (docstrings only), Rv64mc/Tactic/SymTest.lean (new), notes/total-correctness.md. No proof outside Tactic/ changes (FromElemT's change is reverted).
- No theorem statement changed: `git diff 45d46c4730 -- '*.lean' | grep -E '^[-+](theorem|lemma)'` is empty.
- No `sorry`, `admit`, `axiom`, `native_decide`, `maxHeartbeats` added: `git diff 45d46c4730 | grep -E '^\+.*\b(sorry|admit|axiom|native_decide|maxHeartbeats)\b'` is empty.
- No em or en dash added: `git diff 45d46c4730 | grep '^+' | grep -cP '[\x{2013}\x{2014}]'` -> 0.
- SymT.lean's code is unchanged: its diff touches only docstring lines.

## Not done
- What side effect of the eager `natVal?` those proofs depend on. Finding it would let the closer skip that `whnf` (cheaper, and it closes more) with those proofs repaired; out of scope.
- `closeSide`'s `if a == b || (ba == bb && ca == cb) || (← cheapDefEq a b) then` runs `cheapDefEq` eagerly too; it cannot panic and is left as it is, for the same reason.
- `TryMapT`'s cut at 96/134 (wave 4a) is not revisited with `through`. `through` should now pass those joins (86 and 96 are reached from 85, and again from 195/197 only after 71's jump to 190, so no path reaches them twice), but continuing past them ran out of heartbeats in wave 4a.
- `rv_sweep` also reads `cfg.heads`; with `through` it now sweeps fewer heads. Untested (no caller).
- A regression test for `calleeProof`'s and `neByHyp`'s panics: not written (neither fired).

## Known risks
- D1/D2's preservation of behaviour rests on reasoning about evaluation order plus the full build; read the three hunks against the old one-line guards, in particular `neByHyp`'s `n.isApp && n.appFn!.isApp` before `n.appFn!.appArg!`.
- In the first check run (check1.log) `Rv64mc.Proof.Runtime.GrowOneT` ran 16 min (13 CPU-min, 0.9 GB) inside `lake build` and I killed it; alone it took 21 s (`lake env lean`) and 7.6 s (`lake build`, growone.log), and it built in every later run. Not reproduced, cause unknown.
- `SymTest`'s `rv_close` example catches the `alignGoal` panic only with `LEAN_ABORT_ON_PANIC=1` (commit 27c11b3a39 on branch `ci/lean-abort-on-panic` of the main checkout sets it in CI; that commit is not in this worktree's history). Without it the panic is a message and the example passes. Against the base tactic with the variable set, the test aborts (test_base_abort2.log, 1 PANIC).

## Amendments, round 1

Head: d067505500, one commit on 45d46c4730 (R1-5). The earlier commits 7ea05b09b0, d45a63af7f, c7c4b0ea25 and 37968c5021 are no longer on the branch; `git diff 37968c5021 d067505500` is the round's change (4 files, 15+/10-: comments, docstrings, the trace message, notes). Logs and scratch files in this run directory.

Check at d067505500's tree (before the squash, the same tree), with `Rv64mc.Tactic.SymTest` added to the targets: `Build completed successfully (4543 jobs).`, exit 0, 7 min 59 s, `grep -c PANIC check4.log` -> 0.

### R1-1 (fixed: D5's explanation and its "Not done" entry were wrong)
- **Contradicts D5**: D5 said the effect was "not an exception from the eager `natVal?`" and a side effect I did not identify. That is wrong. My probe used a plain `try … catch`, which rethrows runtime exceptions (recursion depth, heartbeats) without running its handler, so it could not see them. The reviewer's mechanism is confirmed on FromElemT's `tail` (scratch/fe.lean, FromElemT's original `tail`):
  - Probe A: in `alignGoal`, each `natVal?` wrapped in `tryCatchRuntimeEx` that appends the exception and the term to scratch/dbg3.txt and rethrows (only `Rv64mc.Tactic.Sym` rebuilt, then `lake env lean scratch/fe.lean` under `LEAN_ABORT_ON_PANIC=1`): exit 0, no output (`tail` passes as before); scratch/dbg3.rethrow.txt holds exactly one entry, `RT true: maximum recursion depth has been reached … ON (regs Reg.x12 <<< 4 + q + 18446744073709551600#64).toNat`, the term `hx12` rewrites.
  - Probe B: the same with the handler returning `none` instead of rethrowing: exit 1, `fe.lean:182:8: error: No goals to be solved` (scratch/fe.swallow.out), the failure 7ea05b09b0 had. So the eager `natVal?` throws on that term, `closeSideSafe` (or `part` under `split`) catches it with `tryCatchRuntimeEx` and leaves the whole goal, and `tail`'s `rw [hx12]; omega` closes it. Both probes were removed: `Sym.lean` was restored from a copy taken before them (scratch/Sym.head) and the check above rebuilt it.
- I did not check that FromElemOptT's and TryFromFnT's breakage under 7ea05b09b0 has the same cause (the bisection was on FromElemT alone); the commit message says only that they break too.
- **Changed**: `alignGoal`'s comment now names the mechanism (`natVal?` can run out of recursion depth on `(x <<< 4 + q + 18446744073709551600#64).toNat`, `closeSideSafe` then leaves the whole goal, which `FromElemT.tail` closes by hand) and drops the history wording. notes/total-correctness.md's `alignGoal` bullet says the same. The "Not done" entry "What side effect of the eager `natVal?` those proofs depend on" is answered: an exception, caught. Skipping the evaluation would still need those proofs repaired, so the code stays as it was.

### R1-2 (fixed)
- The notes line now reads "`Tactic/SymTest.lean` checks both, the second only under `LEAN_ABORT_ON_PANIC=1`", and SymTest's header says the `rv_close` check fails only where a panic aborts, a panic going to the process's standard error, not to Lean's messages. The CI change that sets the variable (27c11b3a39, branch `ci/lean-abort-on-panic`) is not in this worktree's history and stays out of scope.

### R1-3 (fixed)
- `rv_auto`'s docstring and the notes' `rv_symT` signature now include `through [heads]`; `grep -rn 'stop \[pcs\]' Rv64mc/Tactic notes README.md | grep -v through` is empty.
- The trace in `run` (Sym.lean) and `runT` (SymT.lean) now says why a path stopped: "a program counter it has passed" (tested first, as it applies at `g0` too), else "a stop", else "a loop's head". The stopping test itself is unchanged. Evidence: SymTest.lean with `set_option trace.rv_sym true` (scratch/Trace.lean) prints `left at 1: a loop's head` (no `through`, and `through [2]`) and `left at 3: a program counter it has passed` (`through [1]`, `through *`).

### R1-4 (fixed)
- SymTest's header describes the checks as they are now (see R1-2); no history.

### R1-5 (fixed)
- The four commits are squashed (`git reset --soft 45d46c4730`, one commit) into d067505500, `fix(formal): rv_sym's closer panic and its ignored `through``, whose message describes the head: the argument read only of an application, the evaluation kept before the test and why, `through` matched by quotation, the docstrings and trace, the test. Not pushed.

### Full build at d067505500
- Not run this round. A waiter polled `free -g` every 20 s for 90 min and never saw 24 GB available (between 9 and 25 GB, at 13 GB when it gave up: other sessions' Lean servers and a sibling build), so it exited without building (bd70rbep0, `gave up: memory below 24 GB for 90 min`). A single sample of 25 GB fell between polls.
- What stands: the full build at 37968c5021 (full.log, 6071 jobs, 0 PANIC). This round's diff from that commit changes no tactic behaviour: comments, docstrings, notes, and in `run`/`runT` a pure `let why := …` string read only by `trace[rv_sym]`; the stopping test is the same expression. The check (4543 jobs, including every module from `Tactic/Sym` up to TryMapT and SymTest) passed with 0 PANIC at this tree.
- To run it: `cd formal/rv64mc && LEAN_ABORT_ON_PANIC=1 timeout 7200 systemd-run --user --scope -q -p MemoryMax=20G --setenv=LEAN_ABORT_ON_PANIC=1 lake build Rv64mc`, once `free -g` shows 24 GB available; expected `Build completed successfully`, `grep -c PANIC` -> 0.
