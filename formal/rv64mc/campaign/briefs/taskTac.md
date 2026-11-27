# Two bugs in the symbolic executor (`Rv64mc/Tactic/`)

Worktree: /home/devops/leanEthereum/leanVM-t-symt (branch formal/rv64mc-tactic-fixes, head 45d46c4730 = draft PR #878's branch after waves 1a to 5b). Lake project formal/rv64mc, warm. Read formal/rv64mc/README.md, Rv64mc/Tactic/Sym.lean's and SymT.lean's headers first.

## 1. `PANIC at Lean.Expr.appArg!`

Building `Rv64mc.Proof.Bus.TryMapT` prints `info: Rv64mc/Proof/Bus/TryMapT.lean:118:0: PANIC at Lean.Expr.appArg! Lean.Expr:935:15: application expected` (inside `TryMapT.fin`). The build succeeds and the axioms are standard: a panic in tactic code returns a default `Expr` and carries on. It is a bug: some tactic code took `appArg!`/`appFn!` of a term that is not an application. `Rv64mc/Tactic/SymT.lean` has a dozen unchecked uses (lines 85, 90, 129 to 141, 263, ...), and `Sym.lean` may have more.

- Find the one that fires: run the module with `LEAN_ABORT_ON_PANIC=1` (Lean's runtime then aborts on the panic; a backtrace or the last trace line places it), or bisect `fin`'s script with `lake env lean` on a scratch copy under a `timeout`.
- Fix it at its cause: match the shape (`e.isAppOfArity`, `match_expr`, `e.getAppFn`/`getAppArgs` with a length check) and skip or fail cleanly on a term of another shape. Then make every other unchecked `!` accessor in `Tactic/` on a term the tactic did not build itself safe the same way, where it is cheap.
- Evidence: the module builds with `LEAN_ABORT_ON_PANIC=1` and prints no `PANIC`.

## 2. `rv_autoT`'s `through` had no effect

Wave 4a (formal/rv64mc/campaign/defences/runW4a.md D4 and R2; its scratch output runW4a/scratch/tm2.txt if present) saw `rv_autoT ... through *` and `through [86, 96, 124, 134]` stop at those labels alike ("left at 86/96: a stop or a loop's head"), in the proof that became `Proof/Bus/TryMapT.lean` (whose template's joins 86, 96, 124, 134 are backward-jump targets). `Sym.lean:2562` has `syntax rvThrough := "*" <|> ("[" num,* "]")` and `rvSymArgs`. Find whether `through` is parsed and honoured by `rv_autoT` and `rv_symT` (both judgements), or what it is meant to do (it may be correct that a loop's head stops regardless: then the bug is the documentation, and say so). Fix the bug, or the docstrings, with a minimal test in a new `Rv64mc/Tactic/` test module or an `example` in an existing test location showing `through` taking effect.

## 3. Then

- One full `lake build Rv64mc` at the end: `cd formal/rv64mc && timeout 7200 systemd-run --user --scope -q -p MemoryMax=20G lake build Rv64mc 2>&1 | tee <runDir>/full.log`, with `LEAN_ABORT_ON_PANIC=1` set, after checking `free -g` shows at least 24 GB available (another worktree builds at 16G; wait if not). It must pass with no `PANIC` line anywhere in the log (`grep -c PANIC` -> 0).
- Do not change any theorem statement or any proof outside `Tactic/` unless a fix breaks a proof; then repair that proof minimally and list it.
- Notes: add one line to `notes/total-correctness.md`'s executor section for each fix.

## Constraints

- Build what you changed first (`lake build Rv64mc.Tactic.SymT Rv64mc.Proof.Bus.TryMapT`, MemoryMax=16G), the full build once at the end. Never `lake clean`, never delete `.lake` or `Rv64mc/Gen`. A `timeout` on every Lean command.
- No `sorry`, `admit`, `axiom`, `native_decide`; no raised `maxHeartbeats` without a stated reason. No em-dashes or en-dashes. Header docstrings per module; comments only where necessary.
- Commit with conventional messages (`fix(formal): ...`) ending with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`; do not push.
