# Defence: a partial contract and a total one give a total contract with both postconditions

Base: f8a3acbbe6. Head: f6f09d0cab (two commits: 8f45b14e13 feat, f6f09d0cab docs). Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=14G lake build Rv64mc.Total.Combine Rv64mc.Core.HoldsTOfHolds Rv64mc.Final.HoldsTOfHoldsUse` -> "Build completed successfully (4936 jobs)", exit 0 (with `warningAsError = true` from the lakefile; each module elaborates in under 4 s).

Skills: lean4:prove, lean4:refactor and writing-lean-proofs were loaded with the Skill tool. Their interactive prompts (ask before each commit, planning prompts) were not followed, since this is a non-interactive subagent run; commits were made as the task asked.

## Decisions

### D1. Generic combinator `Lprog.Isa.TContract.and_contract` (Rv64mc/Total/Combine.lean)
- **Statement**: from `ht : I.TContract p c G f Pre Post Stop` and `hp : I.Contract p c' f Pre' Post'` (contexts `c : Context I E`, `c' : Context I E'`, event types may differ), with
  - `hstep : ∀ s t es, G s → I.step p c s (.ok (t, es)) → ∃ es', I.step p c' s (.ok (t, es'))`,
  - `hG0 : ∀ regs m, G ⟨[], regs, m⟩`,
  - `hG : ∀ fr st rest regs m, G ⟨fr :: st, regs, m⟩ → G ⟨fr :: st ++ rest, regs, m⟩`,
  it gives `I.TContract p c G f (Pre ∧ Pre') (Post ∧ Post') Stop` (pointwise).
- **Why**: the brief's deliverable 1. The route is the brief's: `TContract.total` at the one-frame stack, the partial contract at the one-frame stack with `G := True` and `Q := stack = [] → Post'`, combined by induction on `Total` (D2), then lifted to any `rest` (D3).
- **Rejected**: (a) a hypothesis "every ok step of `c` is one of `c'`" without the `G s` guard: the guard costs nothing at the instance and is strictly weaker. (b) A determinism hypothesis: not needed. `SafeN` speaks of every run, and `Total`'s `next` ranges over every successor, so every successor under `c` (being a successor under `c'`) inherits `SafeN n` from `SafeN (n+1)`. The brief said "the run is deterministic off the ECALLs"; the proof does not use it. (c) Instantiating the two contracts directly at `rest` with clever `Q`s: the run from the entry with `rest` below continues past the return, so a `Q` cannot tell "this call's return" from later states without a frame argument; I did not find a way around `Total.append`.
- **Claims**: `hstep`, `hG0` and `hG` are the only hypotheses relating the contexts; `Stop` is the total contract's unchanged; the partial contract is used with guard `fun _ => True` only, so no assumption on the partial side leaks into `G`.
- **Evidence**: build above; `#guard_msgs in #print axioms Lprog.Isa.TContract.and_contract` pins `[propext, Classical.choice, Quot.sound]` in the file.

### D2. `Lprog.Ascent.Total.and_safeN` (Combine.lean)
- **Statement**: `Total R accept G Q s → (∀ n, SafeN R' accept' G' n Q' s) → (∀ s t, G s → R s (.ok t) → R' s (.ok t)) → (∀ s, G s → G' s) → Total R accept G (fun t => Q t ∧ (accept' t → Q' t)) s`.
- **Why**: the core induction, stated at `Ascent` (any machine), so it is reusable beyond Lprog.
- **Rejected**: conclusion `Q t ∧ Q' t`: false in general, since `SafeN` only constrains accepting states of `accept'`, and `accept` and `accept'` differ at RV64 (`stmtCtx` accepts at `t0 = 0` whatever `a0`; `sp1Ctx` needs `a0 = 0` too). The implication `accept' t → Q' t` is what is true; at a returned state (empty stack) `accept'` holds for every context, which is how D1 extracts `Post'`.
- **Claims**: axioms `[propext, Quot.sound]` (pinned).
- **Evidence**: `#guard_msgs` block in Combine.lean.

### D3. Frame extension: `Lprog.State.append`, `Isa.step_append_ok`, `step_append_ok_inv`, `step_append_of_not_ok`, `accept_append`, `Total.append` (+ the `stepI_*` versions)
- **Why**: lifting the one-frame run to `fr :: rest`. `Total.append` takes `hG` (obligation survives a longer stack), `hret` (from a return to `rest` with `Q'`, total for `Q`), `hstop` (`Q` under the longer stack where the short run accepts with a nonempty stack) and gives `Total Q (s.append rest)`. There is no `s.stack ≠ []` hypothesis: at an empty stack `Total` can only be `done` (no step exists), handled by `hret`.
- **Rejected**: a general "simulation" lemma; more machinery than one use needs.
- **Claims**: `State.append` is a new definition (`⟨s.stack ++ rest, s.regs, s.m⟩`); no name clash with machine-checked (the build would fail). The `stepI` lemmas are proved by `cases i <;> simp only [Isa.stepI] ... <;> (repeat' split at h) <;> simp_all`, with the `Lext` case of the inverse done by hand. This is case-bash, sensitive to `stepI`'s definition upstream; it rebuilds in under 2 s.
- **Evidence**: `#print axioms Lprog.Total.append` pinned to the standard three.

### D4. `Isa.step_ok_of_ext_not_ok` (Combine.lean)
- **Statement**: if `∀ k regs m x, ¬ c.ext k regs m (.ok x)`, then `I.step p c s (.ok (t, es)) → I.step p c' s (.ok (t, []))` for any `c' : Context I E'`.
- **Why**: discharges `hstep` at any context whose external calls never continue, `stmtCtx` among them, against any other context, `sp1Ctx` among them. Generic, so it can move upstream with D1.
- **Claims**: non-`Lext` instructions step identically in every context with no events; `Lext` has no `ok` step under `c`.

### D5. RV64: `Rv64mc.HoldsT.of_holds` and `HoldsT.of_holds_post` (Rv64mc/Core/HoldsTOfHolds.lean)
- **Statements**:
  - `of_holds (ht : HoldsT env p f need Pre Post Out Stop) (hp : Holds env p f need Pre' Post' Out') : HoldsT env p f need (fun regs m => Pre regs m ∧ Pre' regs m) (fun regs m r' m' => Post regs m r' m' ∧ Post' regs m r' m') Out Stop`.
  - `of_holds_post (ht : HoldsT env p f need Pre Post Out Stop) (hp : Holds env p f need Pre' Post' Out') (hpre : ∀ regs m, Pre regs m → Pre' regs m) : HoldsT env p f need Pre Post' Out Stop`. This is the corollary "safety-only total + partial": `Post` is arbitrary and dropped, so it covers `fun _ _ _ _ => True`.
- **Why**: deliverable 2. The stmtCtx/sp1Ctx discharge is inside the proof, with no hypothesis left to callers: `hstep` by D4 (`stmtCtx.ext _ _ _ o := o = .trap`, closed by `by cases h`), `hG0 := WinOk.nil`, `hG := fun _ _ _ _ _ h => h` (`WinOk` reads `fetch`, which matches only the head frame, so the two sides are definitionally equal).
- **Rejected**: (a) taking `Out ∩ Out'` for the frame: would need `env.Frame` reasoning about two frames; the total's `Out` is what the brief's signature asks for. (b) Requiring `Pre = Pre'` in `of_holds_post`: callers' total preconditions add window facts (`WordPreT` vs `WordPre`), so an implication is needed.
- **Claims**: no existing statement changed (`Holds`, `HoldsT`, `TContract`, `Total`, `MainSpec*`, `EndStatement.lean`, end theorems are untouched; see invariants). A caller uses the combined contract through `HoldsT.call` without unfolding: checked by a scratch file (`runA/calltest.lean`, not committed) that calls `(ht.of_holds hp).call hf hi hc hstack hst hnext ⟨h1, h2⟩ halign hwin (fun _ _ _ _ h => h.elim) fun r' m' _ _ _ _ hq => hk r' m' hq.2`; `lake env lean` on it exits 0.
- **Evidence**: `#guard_msgs` blocks for both theorems pin `[propext, Classical.choice, Quot.sound]`.

### D6. The image use: `Rv64mc.Final.HoldsTOfHoldsUse.inputWord_safe`, `inputWord_total` (Rv64mc/Final/HoldsTOfHoldsUse.lean)
- **What**: `inputWord_safe env` is `InputWordT.total` (at the image's link, template and `halt_aborts`), `mono_need`'d from 0 to `Needs.VerifierRv64.Input.Word` and weakened by `TContract.mono` to postcondition `True`. `inputWord_total env : InputWordSpecT env (liftProg fns) Idx.VerifierRv64.Input.Word Needs.VerifierRv64.Input.Word` is `(inputWord_safe env).of_holds_post (Table.Runtime.inputWord env) fun _ _ h => h.1`.
- **Why**: deliverable 3. `InputWordT.total` already proves `WordPost`, so combining it directly would hide whether the combinator contributes anything. Weakening it to `True` first makes `WordPost` in `inputWord_total` come only from the partial contract `Table.Runtime.inputWord`, so the use is not circular. `inputWord_total` has no hypotheses beyond `env`.
- **Rejected**: `AllocT` with `Alloc`: same shape (its total already has `AllocPost`), plus two environment hypotheses; one example is what the brief asks. A function whose only total proof is safety-only and whose partial proof exists would be the ideal witness, but none exists yet: `MemsetSafeT` is safety-only and `memset`'s partial contract is not proved (`notes/status.md`).
- **Claims**: `inputWord_total`'s type is literally `InputWordSpecT` at the image, so it could replace a later `InputWordT.total` instantiation. Axioms pinned.

### D7. Docs: README.md layout (Total/, Core/, Final/ bullets) and notes/total-correctness.md ("The pieces" bullet; a recipe paragraph at the head of "Proving a function total").
- **Claims**: no em- or en-dashes added (`grep -nP "[\x{2013}\x{2014}]"` on the three new Lean files is empty; the doc edits were typed without them).

## Invariants of the whole change
- Only new Lean files; no existing Lean file modified: `git diff --diff-filter=M --name-only f8a3acbbe6 HEAD` lists only `formal/rv64mc/README.md` and `formal/rv64mc/notes/total-correctness.md`.
- No `sorry`/`admit`/`axiom`/`native_decide`/`bv_decide`/`implemented_by`/`maxHeartbeats` added: `git diff f8a3acbbe6 HEAD | grep -cE '^\+.*\b(sorry|admit|axiom|native_decide|bv_decide|implemented_by|maxHeartbeats)\b'` -> 0.
- Every new theorem a later proof will cite has a `#guard_msgs in #print axioms` block: `and_contract`, `Total.append`, `Ascent.Total.and_safeN`, `step_ok_of_ext_not_ok`, `HoldsT.of_holds`, `HoldsT.of_holds_post`, `inputWord_total`. The `step_append_*`/`stepI_*` helpers are not pinned (they are only used inside Combine.lean, and `and_contract`'s pin covers them transitively).
- `Total/Combine.lean` imports only `Rv64mc.Total.Contract` and `Lprog.Contract` (lprog alone), in namespace `Lprog`.
- Changed files are all within the allowed set (`Total/`, `Core/`, `Final/`, README.md, notes/total-correctness.md).

## Not done
- No whole-project `lake build` (only the three new modules and their dependencies, which were already built; nothing imports the new modules yet, so nothing else can break).
- Not wired into any existing proof or into `notes/status.md` (no function's total status changed).
- `of_holds` keeps the total contract's `Out`; it does not intersect it with the partial one's `Out'`.
- No `HoldsT.mono` for pre/postconditions was added; D6 weakens through `Isa.TContract.mono` directly.

## Known risks
- `of_holds_post`'s `Post` is unconstrained and discarded. A reviewer should confirm this is not a vacuity: `Post` is any predicate, including `True`, and the result's postcondition is the partial one's, which the run genuinely reaches because the total contract guarantees a return (or a stop in `Stop`) and the partial contract covers every run under `sp1Ctx` that the `stmtCtx` run is (D4).
- The partial side's guard is `True` and its accepting set is `sp1Ctx.accept`, which differs from `stmtCtx.accept`. Only the empty-stack case of `accept' t → Q' t` is used, where acceptance is context-independent. Check D1's proof (`hq' (.inl rfl) rfl`) for this.
- The `stepI` case-bash proofs (`simp_all` after `split`) depend on `Isa.stepI`'s exact definition in the pinned machine-checked; a machine-checked bump that changes `stepI` may break them.
- `hG` in `and_contract` (obligation survives a longer stack) is fine for `WinOk` but would rule out an obligation that looks below the top frame; the docstring says so.

## Golf

Commit 3c2be3e4ed on f6f09d0cab; only `formal/rv64mc/Rv64mc/Total/Combine.lean` changes (73 lines touched, 34 added, 39 removed). No statement changed. The proofs are the only change, apart from one new lemma and a header line naming it.

- **G1, new `Isa.step_congr`** (generic, in `Lprog.Isa`): a step from `⟨fr :: st, regs, m⟩` under `c` to `o` gives one from `⟨fr :: st', regs, m⟩` under `c'` to `o'`, if `o = .wrong → o' = .wrong` (the no-function and no-instruction cases of `Isa.step`) and the instruction's `stepI` transports. Its proof is the `cases hf : p[fr.fn]?` / `cases hi : fd.body[fr.pc]?` / `SafeN.step_eq` split that `step_append_ok`, `step_append_of_not_ok` and `step_ok_of_ext_not_ok` each repeated. It is a new lemma, so it changes no existing meaning. Its conclusion follows from its hypotheses by `Isa.step`'s definition, so the three callers keep their statements. `h` is its first explicit argument, so `o` is known before `nofun` elaborates (with `h` last, `nofun` failed on an unknown `o`).
- **G2, `step_append_ok`** is now `step_congr h nofun fun _ _ => stepI_append_ok`: `hw` is vacuous because `o = .ok _`. The old proof closed the two fetch-failure cases by `simp ... at h` for the same reason (`.ok _ = .wrong` is false), and its `some i` case is exactly `hI`.
- **G3, `step_append_of_not_ok`** is now `step_congr h id fun _ _ => stepI_append_of_not_ok ho`. The old fetch-failure cases were `simpa ... using h` on `o = .wrong`, which is `hw := id` with `o' = o`.
- **G4, `step_ok_of_ext_not_ok`**: the same split replaced by `refine step_congr h nofun fun _ i h' => ?_`. The per-instruction tactic block (`cases i`, the `Lext` case by `hc`, the rest by `simp only [Isa.stepI]`, `split`, `simp_all`) is unchanged; only its hypothesis is now `step_congr`'s `stepI` premise instead of a `have h' := (SafeN.step_eq hf hi _).1 h`.
- **G5, `accept_append`** is now `h.imp nofun id`. `Isa.accept` is `stack = [] ∨ ∃ n, fetch .. = some (.Lext n) ∧ c.accept ..`. The left disjunct `fr :: st = []` is empty (`nofun`). On the right, `Isa.fetch` matches on the stack, and `(fr :: st) ++ rest` reduces to `fr :: (st ++ rest)`, so both fetches unfold to the same `(p[fr.fn]?).bind ..`: the two sides are definitionally equal and `id` checks. The old `simpa [Isa.fetch]` proved that same equality.
- **G6, `Total.append`, `next` case at the empty stack**: `obtain ⟨_, _, h⟩ := hex; exact h.elim` became `obtain ⟨_, _, ⟨⟩⟩ := hex`. `Isa.step` at `[]` is `False` by definition, and `rcases` eliminates it the same way `h.elim` did.
- **G7, `and_contract`'s last step**: the `refine Total.append ... ?_ ?_` with two `rcases` blocks became one `exact Total.append ...` term. The case split is the same: on return (`stack = []`), `hq.resolve_right (·.1 rfl)` discards the `Stop` disjunct, whose `[] ≠ []` was the old `absurd rfl hne`, then takes `.2`. At a stop (`fr :: st`), `hq.resolve_left (nomatch ·.1)` discards the return disjunct, whose `fr :: st = []` was the old `cases hne`. The arguments passed to `hk` and `hstop` are unchanged.
- **Header**: `Isa.step_congr` added to "Main results".
- **Tried and reverted**: in `Core/HoldsTOfHolds.lean`, `fun _ _ _ _ h => by cases h` → `fun _ _ _ _ => nofun` fails ("Missing cases"), because `nofun` does not unfold `stmtCtx.ext` to its `Eq`. The file is unchanged. `step_append_ok_inv` keeps its own split because its conclusion is existential and does not fit `step_congr`'s shape. `Final/HoldsTOfHoldsUse.lean` has nothing left to simplify.
- **Check**: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=14G lake build Rv64mc.Total.Combine Rv64mc.Core.HoldsTOfHolds Rv64mc.Final.HoldsTOfHoldsUse` → `✔ Built Rv64mc.Total.Combine`, `✔ Built Rv64mc.Core.HoldsTOfHolds`, `✔ Built Rv64mc.Final.HoldsTOfHoldsUse`, `Build completed successfully (4936 jobs).` No warnings (grep of the build output for warn/error is empty). All seven `#guard_msgs in #print axioms` pins still match unchanged: `[propext, Classical.choice, Quot.sound]`, and `[propext, Quot.sound]` for `and_safeN`. No sorry, axiom, native_decide or dashes added.

## Amendments, round 1

Head: f1dbbb77a6 (four commits on f8a3acbbe6: 8f45b14e13 feat, f6f09d0cab docs, 3c2be3e4ed golf refactor, f1dbbb77a6 fix). Check after the fix: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=14G lake build Rv64mc.Total.Combine Rv64mc.Core.HoldsTOfHolds Rv64mc.Final.HoldsTOfHoldsUse` -> `✔ Built Rv64mc.Total.Combine (1.4s)`, `✔ Built Rv64mc.Core.HoldsTOfHolds (3.3s)`, `✔ Built Rv64mc.Final.HoldsTOfHoldsUse (3.4s)`, `Build completed successfully (4936 jobs).`, exit 0. All eight `#guard_msgs in #print axioms` pins match.

### R1-1 (important): fixed
- **Disposition**: the reviewer is right. `of_holds_post` returned the total contract's `Out` and threw away the partial contract's `AbiRegs`, frame and `Static`, so a "safety-only" total proof still had to prove the exact write set its `Holds` had proved. This contradicts D5's statement of `of_holds_post`, D5 Rejected (a) (which considered only `Out ∩ Out'`, not `Out'` alone) and D6's "What" (`inputWord_safe` kept `WordOut`). Those earlier entries are superseded by this one.
- **What changed** (commit f1dbbb77a6):
  - `HoldsT.of_holds_post (ht : HoldsT env p f need Pre Post Out Stop) (hp : Holds env p f need Pre' Post' Out') (hpre) : HoldsT env p f need Pre Post' Out' Stop`. The whole `Holds.post` (`AbiRegs`, `env.Frame top (Out' regs m)`, `env.Static`, `Post'`) comes from the partial contract. Only `m'.code = m.code` comes from the total one. The proof is the reviewer's probe: `and_contract` plus `mono` with `⟨⟨_, hc⟩, hq'⟩ => ⟨hq', hc⟩`. This is a statement introduced by this change (absent at f8a3acbbe6), so no existing statement changed. `of_holds` is unchanged: it keeps both postconditions and the total contract's frame.
  - The image example: `inputWord_safe` now also weakens the memory frame to `Out := fun _ _ _ => True` (the frame's `∀ a, ¬ MayWrite .. a → ..` clause becomes vacuous: `MayWrite`'s last disjunct is `out a = True`). So `inputWord_total`'s `WordOut` now comes only from `Table.Runtime.inputWord`, as `WordPost` already did. `inputWord_total`'s type is still literally `InputWordSpecT env (liftProg fns) Idx.VerifierRv64.Input.Word Needs.VerifierRv64.Input.Word`, so the non-vacuity check now covers the frame as well.
  - Header of `Core/HoldsTOfHolds.lean`, notes/total-correctness.md's recipe and the README's `Final/` bullet now say exactly what the total proof owes. It owes safety, termination, the postcondition its callers need, `AbiRegs`, `env.Static` and the code map kept. Its frame may be `fun _ _ _ => True`. `AbiRegs` and `env.Static` cannot be dropped from `ht` without changing `HoldsT`, which is out of scope. They are part of every `HoldsT` postcondition, and a lighter total-side contract would need a new definition.
- **Evidence**: the build above. `inputWord_safe` checks with `(fun _ _ _ _ => True) (fun _ _ _ => True) WordStop`, and `inputWord_total` checks against `InputWordSpecT` (whose `Out` is `WordOut`) through the new `of_holds_post`.

### R1-2 (nit): fixed here
- The original header's "Head: f6f09d0cab (two commits ...)" was stale after Golf. Earlier entries are not edited. The head and the commit list are now stated at the top of this amendment: f1dbbb77a6, four commits.

### R1-3 (nit): fixed here
- The original header's "each module elaborates in under 4 s" was lake's per-module build time, as printed in `✔ Built ... (Ns)`. That time excludes loading the imports. It was not wall time. Now measured both ways. Lake's build times are 1.4 s, 3.3 s and 3.4 s (above). Wall time is `/usr/bin/time -f %e timeout 600 lake env lean <file>`, which includes loading the imports: Combine 3.71 s, HoldsTOfHolds 5.68 s, HoldsTOfHoldsUse 5.79 s. These match the reviewer's figures.

### R1-4 (nit): fixed
- `Isa.step_congr` now has `#guard_msgs in #print axioms Lprog.Isa.step_congr` pinned to `[propext, Classical.choice, Quot.sound]` at the end of `Total/Combine.lean`. A scratch probe (`runA/fix1-axprobe.lean`, `lake env lean`) printed exactly that before the pin was added. It stays under "Main results" because it is generic and a later proof can cite it.

## Amendments, round 2

Head: fd8d34ea46 (five commits on f8a3acbbe6: 8f45b14e13 feat, f6f09d0cab docs, 3c2be3e4ed golf refactor, f1dbbb77a6 fix, fd8d34ea46 feat). Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=14G lake build Rv64mc.Core.HoldsTOfHolds Rv64mc.Final.HoldsTOfHoldsUse` -> `✔ Built Rv64mc.Core.HoldsTOfHolds (3.4s)`, `✔ Built Rv64mc.Final.HoldsTOfHoldsUse (3.4s)`, `Build completed successfully (4936 jobs).`, exit 0. `Total/Combine.lean` is unchanged since round 1. The `#guard_msgs` pins all match, including the new one for `of_holds_code`.

### R2-1 (nit): fixed
- **Disposition**: the reviewer is right. Round 1's last bullet under R1-1 "What changed" was wrong. It said "`AbiRegs` and `env.Static` cannot be dropped from `ht` without changing `HoldsT` ... a lighter total-side contract would need a new definition". This entry corrects that claim. The total side of `of_holds_post` keeps `AbiRegs` and `env.Static` only because the brief's corollary takes a `HoldsT`. Neither a change to `HoldsT` nor a new definition is needed: a bare `rvIsa.TContract` whose postcondition is only the code map kept already does the job. That is the reviewer's probe `runA/review2-lightprobe.lean`.
- **What changed** (commit fd8d34ea46):
  - A new theorem, `HoldsT.of_holds_code (ht : rvIsa.TContract p stmtCtx (WinOk p) f (HoldsT.pre env need Pre) (fun _ _ _ m _ m' => m'.code = m.code) fun _ _ regs m r' m' => Stop regs m r' m') (hp : Holds env p f need Pre' Post' Out') (hpre : ∀ regs m, Pre regs m → Pre' regs m) : HoldsT env p f need Pre Post' Out' Stop`. Its proof is the probe's (`and_contract` plus `mono` with `⟨hc, hq'⟩ => ⟨hq', hc⟩`). It takes the precondition and the stopping set in `HoldsT`'s own form, so the only thing it lightens is the total side's postcondition.
  - `of_holds_post` keeps its statement. Its proof is now `of_holds_code (ht.contract.mono (fun _ _ _ _ h => h) (fun _ _ _ _ _ _ _ h => h.2) fun _ _ _ _ _ _ _ h => h) hp hpre`. `HoldsT.post` is `Holds.post .. ∧ m'.code = m.code`, so `.2` is the code map kept. The image example `inputWord_total` goes through `of_holds_post`, so it now exercises `of_holds_code` too. Instantiating `of_holds_code` at the image is a non-vacuity check: `inputWord_safe`'s `HoldsT` contract, with its postcondition dropped, satisfies `ht`.
  - `#guard_msgs in #print axioms Rv64mc.HoldsT.of_holds_code` is pinned to `[propext, Classical.choice, Quot.sound]`.
  - The module header and "Main results" now describe both entry points. In notes/total-correctness.md, the recipe paragraph now gives `of_holds_code` as the route that does not re-prove `AbiRegs` or `env.Static`, and "The pieces" bullet names it. README.md is unchanged: its `Core/` bullet names only `HoldsT.of_holds` as the representative, and its `Final/` bullet still describes the example correctly.
- **Evidence**: the build above. `git diff f8a3acbbe6 HEAD | grep -cE '^\+.*\b(sorry|admit|axiom|native_decide)\b'` -> 0. No dashes (`grep -nP "[\x{2013}\x{2014}]"` on both changed files is empty).

### R2-2 (nit): fixed
- The module header's second paragraph was rewritten for R2-1 and rewrapped at about 105 characters. `awk 'length > 115'` on `Core/HoldsTOfHolds.lean` prints nothing.
