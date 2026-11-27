# Defence: memcpy/memmove partial contracts were false; witness, corrected statements, users re-proved, total-to-partial bridge (deliverable 3 only partly achievable)

Base: 1773e6c8c5. Head: cee37e7c60 (3 commits: c68b9e224e witness, 5554ceab82 statement fix, cee37e7c60 bridge). Worktree /home/devops/leanEthereum/leanVM-t-comb, not pushed.

Check (changed modules and their dependents, after the last edit): `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Core.LocalRun Rv64mc.Core.HoldsOfHoldsT Rv64mc.Total.ToContract Rv64mc.Spec.Runtime.Mem Rv64mc.Spec.Runtime.MemT Rv64mc.Spec.Hash.DigestWords Rv64mc.Proof.Runtime.MemWrappers Rv64mc.Proof.Runtime.FinishGrow Rv64mc.Proof.Transcript.Duplex Rv64mc.Proof.Hash.DigestWords Rv64mc.Proof.Hash.DigestHalves Rv64mc.Proof.Runtime.MemcpyT Rv64mc.Table.CopyScratch Rv64mc.Table.MemT Rv64mc.Table.Runtime Rv64mc.Table.Hash Rv64mc.Table.Transcript Rv64mc.Final.End` -> `Build completed successfully (5156 jobs)`.

Full build (once, `free -g` showed 37 GB available): `timeout 3600 systemd-run --user --scope -q -p MemoryMax=24G lake build Rv64mc` -> `Build completed successfully (5885 jobs)`, real 3m7s, exit 0 (log: runFixCopy/fullbuild.log; its only warnings are the pre-existing `Proof/Field/Reverse.lean` module-system notes). After it, only `Table/CopyScratch.lean` changed (two lemmas added, D4); it has no dependents and was rebuilt by the check above.

Skills: `lean-spec-authoring` and `lean4:prove` loaded.

## Decisions

### D1. The defect is confirmed by machine-checked witnesses (Core/LocalRun.lean, Table/CopyScratch.lean; commit c68b9e224e, before any statement changed)
- **Why**: the task requires confirmation before a statement change. At c68b9e224e, `memcpy_byteFrame_false : ¬ MemcpySpec env (liftProg Gen.fns) Gen.Idx.CompilerBuiltins.Mem.Memcpy need` and `memmove_byteFrame_false : ¬ MemmoveSpec env … Memmove need` were proved against the then-current definitions, for `env = Rv64mc.env` (the end theorem's environment) and every `need` with `stackLimit.toNat + need ≤ stackTop.toNat` (the generator's need, 16, included).
- **How**: `Isa.lstep`/`lrun` (Core/LocalRun.lean) run one activation's body as a function (operations, labels, gotos, branches, return; anything else gives `none`). `lstep_sound` proves each such step is an `Isa.step` with no events, for any context. `safeN_of_lrun` carries a `SafeN` from the entry to the returned state. `Contract.not_of_lrun` refutes a contract: instantiate it with `G := True`, budget `1 + k`, `Q := returned → Post`, continuation `SafeN.returned`. Then walk the concrete run and use `SafeN.of_accept` at the returned state. The concrete run is checked by `decide` on `lrunReturns … = true`, a closed Bool.
- **The witness state**: regs `ra = 0x1000`, `sp = stackTop = 0xbffffff0`. Memory: the image's data words on `[heapEnd, nextAddr]` (by `find?` over `image.data`), and a witness function elsewhere; no code. `env.Static` holds by `static_region` and `Image.wf_of_check wf_check` (distinct addresses). `env.next = heapStart ≤ heapEnd` by `next_check`. memcpy: dst `0x20000000`, src `0x20000104` (4 past a doubleword), n 16, slot doubleword `stackTop - 8` all ones: the run returns with the slot's byte changed. memmove: n 0, same slot: it saves `s0` (0) there.
- **Rejected**: a custom `env` with `Static := True`. That only shows the spec is not valid for every env, not that it fails at the image's. A `rv_auto`-based partial "slot changed" contract combined with `MemcpyT.total`: more machinery, and it needs `Windows` at a concrete state.
- **Claims**: no `sorry`, `native_decide` or extra axioms; `#guard_msgs` pins `[propext, Classical.choice, Quot.sound]` for all three witnesses. The witness uses `liftProg Gen.fns` through `tmpl_eq`, so it is about the image's code.
- **Evidence**: `git show c68b9e224e --stat` (only the two new files); the commit's tree builds (`lake build Rv64mc.Core.LocalRun Rv64mc.Table.CopyScratch` -> success, 4744 jobs, at that commit).

### D2. `CopyPost` takes `env` and the restricted frame; `MemcpySpec`/`MemmoveSpec` add `CopyApart` to the precondition (Spec/Runtime/Mem.lean)
- **New statements**:
  - `CopyPost env regs m r' m'` = `r' .x10 = regs .x10` ∧ the old copied-bytes conjunct (unchanged) ∧ `∀ b, ¬ InRange dst n b → OffStack env (regs .x2) b 1 → m'.getByte b = m.getByte b`. This is `CopyPostT`'s body verbatim.
  - `CopyApart env regs m := n = 0 ∨ (env.Owned m (regs .x2) dst n ∧ OffStack env (regs .x2) src n)`.
  - `MemcpySpec := Holds … (fun regs m => CopyPre false regs m ∧ CopyApart env regs m) (CopyPost env) CopyOut`, and likewise `MemmoveSpec` with `CopyPre true`.
- **Old-to-new relation**: old ⇒ new, the new spec is weaker. The precondition gains a conjunct and the frame conjunct is weakened; `Out` is unchanged. Machine-checked as `memcpySpec_of_keepAll`/`memmoveSpec_of_keepAll` (Table/CopyScratch.lean), with the old postcondition restated as `KeepAllPost` (the old `CopyPost` text exactly).
- **Why the frame**: D1.
- **Why the precondition change was not optional** (the task asked only for the frame): the frame fix alone leaves the spec false. `memcpy_srcOnStack_false : ¬ Holds env (liftProg fns) Memcpy need (CopyPre false) (CopyPost env) CopyOut` is the new post under the old pre. Its run has the source at `stackTop - 12`, overlapping the slot, and the copy returns with a wrong destination byte. The destination conditions (apart from the slot, the static data and `NEXT`) are argued, not machine-checked:
  - a destination in the slot breaks the copied-bytes conjunct;
  - one in the static data breaks `Holds.post`'s `env.Static m'`;
  - one at `NEXT` breaks `Env.Frame`'s `next m ≤ next m' ≤ heapEnd`.
  `Env.Owned` (below `NEXT` or at/above `sp`, no wrap) excludes all three, and every partial caller already reasons in `Owned`/`Live`.
- **Rejected**:
  - Keeping the old precondition (still false, by the witness above).
  - Using `CopyPreT` as the partial precondition. Partial callers cannot discharge its windows (`0x10000000 ≤ dst` needs `next ≥ 0x10000000`, a `Windows` fact).
  - `dst + n ≤ heapEnd ∨ sp ≤ dst` instead of `Owned`. It is weaker and also sufficient by my argument, but it is a new concept; `Owned` already exists and every caller satisfies it.
  - Defining `CopyPostT := CopyPost` in MemT.lean. That changes a total statement's text, and risks the 80 s `MemcpyT` proof and the `simpa [CopyPostT]` in MemWrappersT. Instead `CopyPostT` is left byte-identical and is definitionally `CopyPost env` (used by `memcpyHolds`, which closes by unification).
- **Claims**:
  - `OffStack` moved verbatim from MemT.lean to Mem.lean, same namespace `Rv64mc.Spec.Runtime`, so its full name is unchanged and `CopyPreT`/`CopyPostT`/`MemcpySpecT`/`MemmoveSpecT` mean exactly what they meant.
  - No `Holds`, `HoldsT`, `TContract`, `Total`, `MainSpec*`, end-theorem or `EndStatement.lean` text changed: `git diff 1773e6c8c5 --name-only` lists none of Core/Holds.lean, Core/HoldsT.lean, Total/Contract.lean, Total/Judgement.lean, Final/*, EndStatement.lean.
  - The new spec is, I believe, true of the code. Not machine-checked: there is no partial proof of `memcpy` or `memmove`; it stays class C, an open hypothesis as before. My argument: the only writes outside the destination's bytes are to `[top-16, top)`, which `CopyApart` keeps apart from source and destination (doubleword-wise too, since `top` is 16-aligned and `Owned`/`OffStack` regions sit below `stackLimit` or at/above `top`). `MemcpyT.total` proves the same post under a stronger pre with `Windows`.
- **Evidence**: build above; `git diff 1773e6c8c5 -- formal/rv64mc/Rv64mc/Spec/Runtime/Mem.lean`.

### D3. Users re-proved, per file
- `Proof/Runtime/MemWrappers.lean`: `simpa` set gains `CopyApart` (the tail call keeps `sp`; `x6 ≠ x2`). `CopyPost` now mentions `regs .x2`, handled by the same `updReg_apply`.
- `Proof/Runtime/FinishGrow.lean`: one new bullet for the `CopyApart` side goal.
  - dst = fresh block: `Owned` via `dst + n ≤ next m2` (from `hret2_18` and `hle`) and `next m2 ≤ heapEnd < 2^64`.
  - src = old block: `OffStack` via `Live` (`src + n ≤ next m ≤ heapEnd ≤ … < stackLimit`).
  - The frame conjunct of `CopyPost` was never used (the file builds without change there).
- `Proof/Transcript/Duplex.lean`: one `all_goals try (refine .inr ⟨⟨.inr ?_, ?_⟩, .inr ?_⟩ <;> (try simp only [BitVec.toNat_ofNat]) <;> omega)` line in each of `tail` and `ok_at`. Both copies are between the sponge (at or above duplex's `top`, `InFrame`) and duplex's buffer at its own `sp` = memcpy's `sp`, so `Owned`/`OffStack` by the `sp ≤ a` disjunct. Build time of the module: 40 s in `lake build` (no base measurement under the same load; the extra `all_goals try` runs on every remaining goal, so look at whether it costs time).
- `Proof/Hash/DigestWords.lean`: **unchanged text**, rebuilt: `rv_auto` closes the new `CopyApart` goal from the new spec conjunct (D5) and `Pre`'s `Owned` slot.
- `Proof/Hash/DigestHalves.lean`: unchanged text, rebuilt; `rv_auto` discharges `DigestWords.spec`'s new `OffStack` conjunct from its `Owned` digest.
- `Table/Runtime.lean`, `Table/Hash.lean`, `Table/Transcript.lean`: unchanged; they take `MemcpySpec`/`MemmoveSpec` as hypotheses and pass them on.
- **Claims**: the only uses of the old `ByteFrame` conjunct were none: no proof needed the restricted frame to be weakened further. Every file in `grep -rln "MemcpySpec\|MemmoveSpec\|CopyPost" Rv64mc --include=*.lean | grep -v Gen/` builds.

### D4. `KeepAllPost`, `memcpySpec_of_keepAll`, `memmoveSpec_of_keepAll` (Table/CopyScratch.lean, commit 5554ceab82)
- **Why**: after D2 the names `MemcpySpec`/`MemmoveSpec` mean the corrected statements. So the witnesses are restated against the old statement written out (`Holds … (CopyPre o) KeepAllPost CopyOut`), and the old-to-new implication is a theorem, not a sentence.
- **Claims**: `KeepAllPost` is the base's `CopyPost` body character for character (`git show 1773e6c8c5:formal/rv64mc/Rv64mc/Spec/Runtime/Mem.lean`).

### D5. `Spec/Hash/DigestWords.lean`'s partial `spec` asks `OffStack env (regs .x2) (regs .x11) 32` (file outside the allowed list)
- **Why**: `Digest::words` tail-calls `memcpy` with its digest as source, and its `Pre` constrains the digest's location not at all. So by the same mechanism as `memcpy_srcOnStack_false`, its partial spec is false for a digest overlapping `[top-16, top)` (argued, not machine-checked). And its proof cannot discharge the new `CopyApart`.
- **Rejected**:
  - Adding the conjunct to `Pre`. `DigestWordsT.PreT` is `Pre ∧ …` and already has this `OffStack`, so changing `Pre` would change a total statement's text and its `hpre_*` numbering.
  - Leaving `DigestWords` on the old `MemcpySpec`: impossible, there is one `MemcpySpec`.
- **Claims**: only `spec` changed (its precondition gains a conjunct: weaker spec). `Pre`, `Post`, `Out` are unchanged. The one user, `DigestHalves.ok`, builds unchanged. `DigestWordsT`/`Table/DigestT` do not mention `spec`'s precondition and rebuild unchanged in the full build.

### D6. Deliverable 3, total-to-partial: `TContract.contract` (Total/ToContract.lean), `HoldsT.holds` (Core/HoldsOfHoldsT.lean), `Table/MemT.memcpyHolds`; `MemcpySpec` is NOT discharged
- **What is proved**: `TContract.contract`, for any `Isa`, contexts `c` (total) and `c'` (partial). If `ht : TContract p c G f Pre Post Stop`, every `c.ext k regs m .trap` holds, `G` holds at returned programs, and `Stop` is empty under `Pre`, then `Contract p c' f Pre Post`.
- **Soundness argument (stmtCtx vs sp1Ctx)**: a state the total judgement steps from (`next`) has `¬ step c s .trap`. At an `Lext` the step under `c` can trap (`step_trap_of_ext`), so a `next` state is not at an `Lext`. A `done` state is accepting with `Q`, and `Q` (from `TContract.total`) is "stack empty ∧ Post" or "stack nonempty ∧ Stop"; the second is excluded. Away from `Lext`, `step p c' s o` implies `step p c s (forget o)` (`step_of_not_ext`, case analysis on `stepI`). So a `c'`-successor is a `c`-successor, and `wrong` under `c'` is `wrong` under `c`, which `next` excludes. The caller's stack is handled as in `Combine.lean` (`step_append_ok_inv`, `step_append_of_not_ok`). Budget: `safeN_append` proves `∀ k ≤ n, SafeN k` from `SafeN n` at returns.
- **`HoldsT.holds`**: `HoldsT … Pre Post Out` (Stop default False) gives `Holds … (fun regs m => Pre regs m ∧ Windows env (regs .x2) m) Post Out`. Here `hc` is `rfl` because `stmtCtx.ext _ _ _ o := o = .trap`, `hG0` is `WinOk.nil`, and `Entry` rewrites `regs .x2` to `top`.
- **Why `MemcpySpec` is not discharged**: `HoldsT`'s precondition includes `Windows` (`code_within m`, `next_ge`, `top_le`), and `CopyPreT` adds windows on dst/src. The total contract says nothing about states without them, so no partial contract whose precondition lacks them follows from it. The partial callers (FinishGrow, Duplex, DigestWords, and transitively `MainSpec`, whose statement may not change) have no `Windows` in their preconditions, so putting `Windows` into `MemcpySpec` would break every partial user. `Table/Runtime`'s instances therefore keep `memcpy (223)`, and `notes/status.md`'s rows and counts are unchanged (a sentence added says why).
- **Rejected**: a partial contract with `Windows`-conditional post (`Holds.post`'s frame and `Static` are unconditional, so still not derivable); strengthening every partial spec up to `MainSpec` with `Windows` (forbidden).
- **Claims**: `memcpyHolds : Holds env (liftProg fns) Memcpy Needs.Memcpy (fun regs m => CopyPreT false env regs m ∧ Windows env (regs .x2) m) (CopyPost env) CopyOut := (memcpyT env).holds`. It is true and machine-checked but has no user. I kept it as the derivation the task asked for, and as a check that `CopyPostT` and `CopyPost env` agree.

### D7. Notes and README
- `notes/total-correctness.md`: the "not machine-checked" sentence replaced by the witness and the fix; one bullet for D6.
- `notes/status.md`: one bullet (defect, fix, why 223 stays).
- `README.md`: one clause each for `ToContract.lean`, `HoldsT.holds`, `LocalRun.lean`.
- No audit issue numbers anywhere: `git diff 1773e6c8c5 | grep -iE "^\+.*(issue|#[0-9]{2,})"` matches only BitVec literals such as `0x1000#64`, no issue reference.

## Invariants of the whole change
- No `sorry`/`admit`/`axiom`/`native_decide`/`bv_decide`/`maxHeartbeats`/`implemented_by` added: `git diff 1773e6c8c5 | grep -cE '^\+.*(sorry|admit|axiom |native_decide|bv_decide|maxHeartbeats|implemented_by)'` -> 0.
- `set_option maxRecDepth 100000 in` added three times, on the three witness theorems only (kernel evaluation of the concrete runs by `decide`).
- No em or en dash added: `git diff 1773e6c8c5 | grep -cP "^\+.*(\x{2014}|\x{2013})"` -> 0.
- Changed `def`s (`git diff 1773e6c8c5 -- '*.lean' | grep -E '^[-+](theorem|def|abbrev)'`): `CopyPost` (D2), `OffStack` (moved), and new ones; `MemcpySpec`/`MemmoveSpec`/`DigestWords.spec` bodies changed on non-header lines (D2, D5).
- Axioms pinned by `#guard_msgs` to `[propext, Classical.choice, Quot.sound]` for `memcpy_byteFrame_false`, `memmove_byteFrame_false`, `memcpy_srcOnStack_false`, `TContract.contract`, `HoldsT.holds`, `memcpyHolds`.
- Lines at most 120 characters in new code, except the generated `#guard_msgs` info strings (121/122 characters, three in CopyScratch).

## Not done
- `MemcpySpec`/`MemmoveSpec` are not proved; they remain open class-C hypotheses, now (I believe) true. A partial proof would be the `MemcpyT` proof replayed without `Windows`/`WinOk`.
- Deliverable 3 in the task's form (Table/Runtime losing `memcpy (223)`) is not achievable without `Windows` in the partial chain: see D6.
- The destination half of `CopyApart` (static data, `NEXT`, slot) is justified by argument, not by a witness; only the source half has one (`memcpy_srcOnStack_false`).
- No witness for `memmove` with the new statements; and no non-vacuity guard that the new `MemcpySpec` precondition is satisfiable. The `memcpy_byteFrame_false` state satisfies `CopyPre`; with dst moved below `NEXT` it would satisfy `CopyApart` too, but this is not pinned.

## Known risks
- **D2 truth of the new spec** is argued. The reviewer should check whether `memcpy`'s aligned-doubleword loads in the misaligned loop can read a doubleword that straddles into `[top-16, top)` when `src + n ≤ stackLimit` (they cannot: `stackLimit ≤ top - 16` by `need ≥ 16`, and the last doubleword touched is below `stackLimit`), and whether `memmove`'s backward path writes anything else on the stack.
- **D5** is a statement change to a spec outside the allowed list; its users are `Proof/Hash/DigestHalves.lean` (hypothesis) and `Table/Hash.lean` (the instance, by `DigestWords.ok`), per `grep -rn "DigestWords.spec\|DigestWords.ok" Rv64mc --include=*.lean | grep -v Gen/`; both build.
- **Duplex's `all_goals try (refine .inr ⟨⟨.inr ?_, ?_⟩, .inr ?_⟩ …)`** could in principle close a goal other than `CopyApart` if one has the same shape and omega proves it: harmless for soundness, but look at whether it changes which goals later `all_goals try` lines see. The file builds and the later bullets still match.
- **`step_of_not_ext`'s proof** is a `simp_all` over `stepI` cases; it is general over `Isa`, so check its statement (the outcome map `forget` drops events and keeps `trap`/`wrong`).
- `Core/LocalRun.lean` defines `Isa.Local` as an `abbrev` of a product: an inductive with the same role made the compiler panic (`ExplicitBoxing`), so it is a tuple.

## Amendments, round 1

Head: 92d1d72c59 (one commit on cee37e7c60). Files: `Table/CopyScratch.lean`, `Table/MemT.lean`, `Spec/Runtime/Mem.lean` (docstrings only), `notes/status.md`, `notes/total-correctness.md`, `README.md`; all in the allowed list.

Check after the last edit: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Core.LocalRun Rv64mc.Core.HoldsOfHoldsT Rv64mc.Total.ToContract Rv64mc.Spec.Runtime.Mem Rv64mc.Spec.Runtime.MemT Rv64mc.Spec.Hash.DigestWords Rv64mc.Proof.Runtime.MemWrappers Rv64mc.Proof.Runtime.FinishGrow Rv64mc.Proof.Transcript.Duplex Rv64mc.Proof.Hash.DigestWords Rv64mc.Proof.Hash.DigestHalves Rv64mc.Proof.Runtime.MemcpyT Rv64mc.Table.CopyScratch Rv64mc.Table.MemT Rv64mc.Table.Runtime Rv64mc.Table.Hash Rv64mc.Table.Transcript Rv64mc.Final.End` -> `Build completed successfully (5156 jobs)`, 1m57s (log runFixCopy/check-r1.log). Since `Spec/Runtime/Mem.lean` changed (docstrings), the full build again, `free -g` 32 GB available: `timeout 3600 systemd-run --user --scope -q -p MemoryMax=24G lake build Rv64mc` -> `Build completed successfully (5885 jobs)`, real 2m51s, exit 0, no warning outside `Proof/Field/Reverse.lean` (log runFixCopy/fullbuild-r1.log). No `sorry`/`axiom`/`native_decide`/`bv_decide`/`maxHeartbeats` added (`git diff cee37e7c60 | grep -cE ...` -> 0); no em or en dash added.

### R1-1: deferred (agreed; nothing a fixer can remove on this branch)
- Same as R1-2-1 below. What changed: `notes/status.md`'s bullet now says what removing `memcpy (223)` takes (a partial proof of `MemcpySpec`: `MemcpyT`'s, replayed without `Windows`/`WinOk`), and that `MemcpySpec`/`MemmoveSpec` stay class C, now with a precondition shown inhabited (R1-2 (c)) and no run refuting them.

### R1-2: (a) fixed for the slot, (b) deferred, (c) fixed
- (a) `memcpy_dstOnStack_false : ¬ Holds env (liftProg Gen.fns) Memcpy need (fun regs m => CopyPre false regs m ∧ OffStack env (regs .x2) (regs .x11) (regs .x12).toNat) (CopyPost env) CopyOut`: from `stackTop`, 24 bytes to `stackTop - 16` (on the slot) from `0x20000104` (4 past a doubleword, below `stackLimit`), memory `entryM id`; the kernel-evaluated run returns with a destination byte other than the source's at entry. So the destination half of `CopyApart` is forced at least off the slot, as the source half was. Probing first: with 16 bytes to `stackTop - 16`, `-12`, `-20`, or 8 to `-8`, the run happened to copy right (the slot is assembled before the destination's last doubleword is written), so the witness uses 24 bytes; 32 bytes to `stackTop - 24` also fails. The static-data and `NEXT` destinations stay argued, not witnessed (each needs a check over `image.data` in the kernel); `CopyApart`'s docstring and the notes now say `Owned` asks more than the code needs (R1-2-2).
- (b) `DigestWords.spec`'s `OffStack` stays argued: `Core/LocalRun.lean` runs a body whose every instruction is an operation, label, goto, branch or return, and `Digest::words` ends in its call of `memcpy`. A witness would need `lrun` extended with calls through a contract, which is more than this finding is worth. The change only strengthens the precondition of a class-A partial instance (`Table/Hash`), which `notes/status.md` now names (R1-2-4).
- (c) `copySpec_pre_inhabited (st) : Holds.pre env Needs.Memcpy (fun regs m => CopyPre false regs m ∧ CopyApart env regs m) 0x1000#64 stackTop (entryRegs 0x1fffff00#64 0x1fffff84#64 16#64) (entryM st) ∧` the same for `MemmoveSpec`'s (`CopyPre true`, `Needs.Memmove`): the destination's 16 bytes below `NEXT = heapStart`, the source 4 bytes past a doubleword below `stackLimit`. And `memcpy_copies`: from that state with `st = id`, `lrunReturns` of the template's body is `true` for: `a0` returned as `dst`, the 16 bytes copied, and the 8 bytes on either side of the destination kept. Both pinned; `#guard_msgs` on `copySpec_pre_inhabited` and `memcpy_dstOnStack_false` gives `[propext, Classical.choice, Quot.sound]` (`memcpy_copies` is a closed `decide`).

### R1-3: fixed
- The `notes/total-correctness.md` bullet now states the present: `CopyPostT` is `CopyPost` (`copyPostT_eq`); a frame keeping every byte outside the destination (`CopyPost` as it was) is false, `memmove` on every call (it saves `s0`), `memcpy` on its misaligned path; then the witnesses, `CopyApart` and the guards.

### R1-4: fixed
- `Table/MemT.lean`: `theorem copyPostT_eq : Spec.Runtime.CopyPostT = Spec.Runtime.CopyPost := rfl`, listed in the header. The duplicate definition stays (a total statement's text is not changed), now pinned directly. `memcpyHolds` stays: it is the derivation the task asked for; it has no user, as D6 said.

### R1-5 and R1-2-6: fixed by measurement; not restricted
- Measured with `set_option trace.profiler true` and threshold 50 ms on a scratch copy of the module (runFixCopy/probe/DuplexP.lean, DuplexP2.lean, `lake env lean` under MemoryMax=16G). In `tail`, the added line is below 50 ms (not reported); its neighbours `all_goals try (simp only [Spec.Hash.KeccakF.stateBytes]; omega)` and `all_goals try (simp only [BitVec.toNat_ofNat]; omega)` took 100 ms and 133 ms. In `ok_at`, also below 50 ms (its neighbour line 157 took 195 ms). The module takes 40 to 43 s by `lake env lean` (two runs each). So the line's cost is under 0.1 s of the module's time. Caveat: the `ok_at` profile run hit a heartbeat timeout at the declaration under the profiler's overhead, after the traced steps past line 158; the timings are of a run that elaborated those steps.
- Restricting it was tried: `all_goals try (show CopyApart _ _ _; refine …)` leaves the goals open (14 errors), because `rv_auto` has unfolded `CopyApart` by then, so a `show` on the folded form does not match. A match on the unfolded shape is what the `refine` already does. Kept as it was.

### R1-6: fixed (placement kept)
- `README.md`'s `Rv64mc/Table/` line names `CopyScratch.lean`: concrete runs showing a copy contract that keeps the slot, or has a range on it, is false, and guards of the corrected contracts. It stays in `Table/`: it instantiates at the image's indices (`Gen.Idx.*`, `tmpl_eq`), and `Final/` is not in this task's allowed list. It builds through the lib's glob (in the full build above).

### R1-2-1: deferred, with the guards the finding asks for
- The task's deliverable 3 in its form (Table/Runtime losing `memcpy (223)`) needs a partial proof of `MemcpySpec`. D6's argument stands, and both reviewers agree with it: no partial caller up to `MainSpec` has `Windows`, and `HoldsT.holds` cannot drop it. What it would take: `Proof/Runtime/MemcpyT.lean` (864 lines) and the parts of `CopyT.lean` it uses, replayed with `rv_sym` against `Holds` (partial loops by induction on the bytes left, as `Memcmp.lean`'s `loop`), with the `Windows`/`WinOk`/`InWin`/`inWindow` facts (31 mentions in `MemcpyT.lean`, 5 in `CopyT.lean`) removed; then `Table/Runtime`'s instances take it and `notes/status.md`'s rows and counts change. That is a proof campaign of its own, not a fix round; I did not start it. The decision whether to accept the deferral is the task owner's.
- Done instead, as the finding asks if deferred: the non-vacuity guard `copySpec_pre_inhabited` and the positive run `memcpy_copies` at a `CopyApart` state with a misaligned source (R1-2 (c)); and the destination witness (R1-2 (a)).

### R1-2-2: fixed
- `CopyApart`'s docstring: "`memcpy` copies a range on its slot wrong (`Table/CopyScratch.lean`); `Owned` asks more than that (not `[NEXT, heapEnd)`), and every caller has it." The notes say the same. Plus the slot witness for the destination (R1-2 (a)).

### R1-2-3: fixed (header softened, follow-up recorded)
- `Spec/Runtime/Mem.lean`'s header: "`memcpy` and `memmove` do not keep it" instead of "are the exception". `notes/status.md` gains a "To check" bullet: `DigestPost` (`Spec/Hash/Keccak.lean`, used by `keccak_hash`, `Spec/Merkle/Merkle.lean`, `Spec/Runtime/Input.lean`) keeps a full `ByteFrame` for functions that may keep scratch below their stack pointer; `LocalRun` runs a body without calls, so testing those needs more. Not checked by a run here. `Digest::from_halves`'s `ByteFrame` is proved (class A, a leaf without a frame), and `memset`'s template never mentions `sp`, so `SetPost` is not in the list.

### R1-2-4: fixed
- `notes/status.md`'s bullet names `Digest::words`' partial `spec` and says `Table/Hash`'s instance of it states a contract with the added precondition.

### R1-2-5: fixed
- As R1-4: `copyPostT_eq`.

### R1-2-7: fixed
- `## Golf` below, and these amendments.

### Corrections to earlier claims
- D2 said the destination conditions were "argued, not machine-checked" for the slot, the static data and `NEXT`: the slot is now machine-checked (`memcpy_dstOnStack_false`); the other two remain argued.
- "Not done" said no non-vacuity guard was pinned: it is now (`copySpec_pre_inhabited`, `memcpy_copies`).
- D3 said the Duplex line's cost was unmeasured: measured above.

## Golf

No golf pass was run on this change. The new code is a witness (`memcpy_dstOnStack_false`, the same shape as `memcpy_srcOnStack_false`), a guard, a closed `decide` and a `rfl`.

## Amendments, round 2

Head: a46b3a0470 (one commit on 92d1d72c59). Files: `Table/CopyScratch.lean`, `Spec/Runtime/Mem.lean` (one docstring word), `notes/status.md`, `notes/total-correctness.md`; all in the allowed list.

Check after the last edit: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Core.LocalRun Rv64mc.Core.HoldsOfHoldsT Rv64mc.Total.ToContract Rv64mc.Spec.Runtime.Mem Rv64mc.Spec.Runtime.MemT Rv64mc.Spec.Hash.DigestWords Rv64mc.Proof.Runtime.MemWrappers Rv64mc.Proof.Runtime.FinishGrow Rv64mc.Proof.Transcript.Duplex Rv64mc.Proof.Hash.DigestWords Rv64mc.Proof.Hash.DigestHalves Rv64mc.Proof.Runtime.MemcpyT Rv64mc.Table.CopyScratch Rv64mc.Table.MemT Rv64mc.Table.Runtime Rv64mc.Table.Hash Rv64mc.Table.Transcript Rv64mc.Final.End` -> `Build completed successfully (5156 jobs)`, exit 0, 1m40s (log runFixCopy/check-r2.log). Since `Spec/Runtime/Mem.lean` changed, the full build once more, `free -g` showing 37 GB available: `timeout 3600 systemd-run --user --scope -q -p MemoryMax=24G lake build Rv64mc` -> `Build completed successfully (5885 jobs)`, exit 0, real 2m37s, no warning outside `Proof/Field/Reverse.lean` (log runFixCopy/fullbuild-r2.log). `git diff 92d1d72c59 a46b3a0470 | grep -cE '^\+.*(sorry|admit|axiom |native_decide|bv_decide|maxHeartbeats|implemented_by)'` -> 0; no em or en dash added.

### R2-2 and R2-2-4: fixed
- `Table/CopyScratch.lean`'s guards section now has `CopiedRight dst src n r' m'` (a Bool: `a0 = dst`, the `n` bytes copied from `src` at entry, the 8 bytes on either side of the destination kept) and `memcpyRight`/`memmoveRight dst src n` (the template's body run by `Isa.lrunReturns` from `stackTop` and `entryM id`, budget 2000, checked with `CopiedRight`). Pinned, each by `decide`:
  - `copies : memcpyRight 0x1fffff00 0x1fffff84 16 = true ∧ memmoveRight 0x1fffff00 0x1fffff84 16 = true`: both from the `copySpec_pre_inhabited` state. Replaces `memcpy_copies` (same memcpy run and same checks, budget 1000 -> 2000), so memmove now has a positive run with bytes to copy under its corrected precondition.
  - `memcpy_copies_aboveTop : memcpyRight (stackTop + 8) 0x1fffff84 24 = true`: the `top ≤ dst` disjunct of `Owned`. I used `stackTop + 8` rather than the reviewer's `stackTop`, so the 8 bytes below the destination checked are the caller's (`stackTop`), not the slot, which `CopyPost` does not keep.
  - `memmove_copies_overlap`: `0x1fffff00 <- 0x1fffff04` and `0x1fffff04 <- 0x1fffff00`, 24 bytes each (the reviewer's overlapping cases).
- All three are pinned by `#guard_msgs` to `[propext, Classical.choice, Quot.sound]` (not empty: `entryM`, `dataAt` are `noncomputable` over `List.find?` and the closed `decide` goes through them; first try pinned `[propext]` and the build showed the three).
- The module header and `notes/total-correctness.md` now say what the runs check: `a0`, the copied bytes and the 8 bytes on either side, not the rest of `Holds`' postcondition (R2-2's second point).
- Module build: `lake build Rv64mc.Table.CopyScratch` -> success, the module 25 s (as before the change: the five runs together take a few seconds).

### R2-2-2: fixed
- "copies ... wrong" claims softened to what a run shows: `CopyApart`'s docstring "`memcpy` can copy a range on its slot wrong"; the CopyScratch header "Nor are the bytes always copied right when the source or the destination overlaps the slot"; the docstrings of `memcpy_srcOnStack_false` ("can copy a source that overlaps its slot wrong") and `memcpy_dstOnStack_false` ("can copy into its slot wrong"); `notes/total-correctness.md` "A source or a destination on the slot can be copied wrong", naming each witness's shape (16 bytes from `stackTop - 12`; 24 bytes to `stackTop - 16`). The theorem statements are unchanged: each is a `¬ Holds ...`, which one run refutes.

### R2-4 and R2-2-3: fixed
- `notes/status.md`: "`MemcpySpec` and `MemmoveSpec` stay class C, with a precondition met with bytes to copy (`copySpec_pre_inhabited`) and no run found refuting them (the pinned runs: `copies`, `memcpy_copies_aboveTop`, `memmove_copies_overlap`)."
- The pre-existing "the 35 committed `#guard_msgs` guards agree" (already off at base) now reads "the committed `#guard_msgs` guards agree": no count to go stale.

### R2-3: fixed in this text (no new measurement)
- The caveat in full: both profile runs (runFixCopy/probe/DuplexP.out, DuplexP2.out) contain errors. DuplexP.out has a parse error at 134:63 and a whnf heartbeat timeout at 137:0; DuplexP2.out a whnf heartbeat timeout at 134:0. The traced steps before those errors include the added lines' neighbours (100 ms, 133 ms, 195 ms). The added line does not appear as a traced node, so "below 50 ms" is inferred from its absence under a 50 ms threshold, not measured as a number. probe/DuplexT.time (the run meant to time the module with the line) exited 1. No base-against-head timing of the module exists: the base `Duplex.lean` does not build against head's `Spec/Runtime/Mem.lean` (it leaves the `CopyApart` goal open), and timing it at base needs a base build of its dependency cone. What stands: the module at head takes 43.31 s by `lake env lean` (probe/DuplexHead.time), 40 s in `lake build`. This corrects R1-5's "fixed by measurement": the cost is estimated, not measured. It has no bearing on soundness.

### R1-2-1: deferred (unchanged; owner's decision)
- As in round 1: `Table/Runtime.lean` still takes `MemcpySpec`/`MemmoveSpec` as hypotheses, `memcpyHolds` has no user, `notes/status.md`'s rows and counts are unchanged. Removing `memcpy (223)` takes a partial proof of `MemcpySpec` (`Proof/Runtime/MemcpyT.lean`, 864 lines, replayed against `Holds` without `Windows`/`WinOk`), and of `MemmoveSpec` from scratch, since `MemmoveSpecT` is not proved either. That is a task of its own for the owner to open or not; this round adds only the guards above.

### R2-1 and R2-2-1: fixed (corrections below)

### Corrections to earlier claims
- Invariants, "`set_option maxRecDepth 100000 in` added three times, on the three witness theorems only": at a46b3a0470 it is added seven times (`git diff 1773e6c8c5 | grep -c '^+.*maxRecDepth'` -> 7): on the four witnesses (`memcpy_byteFrame_false`, `memmove_byteFrame_false`, `memcpy_srcOnStack_false`, `memcpy_dstOnStack_false`) and the three guard runs (`copies`, `memcpy_copies_aboveTop`, `memmove_copies_overlap`), each for the kernel's evaluation of a concrete run by `decide`.
- Invariants, "the generated `#guard_msgs` info strings (121/122 characters, three in CopyScratch)": seven such lines are over 120 characters (121 or 122), all `#guard_msgs` info strings, which must match the generated message.
- Invariants, the `#guard_msgs` axiom pins: now `memcpy_byteFrame_false`, `memmove_byteFrame_false`, `memcpy_srcOnStack_false`, `memcpy_dstOnStack_false`, `copySpec_pre_inhabited`, `copies`, `memcpy_copies_aboveTop`, `memmove_copies_overlap`, `TContract.contract`, `HoldsT.holds`, `memcpyHolds` (eleven; `copyPostT_eq`, a `rfl`, is not pinned).
- Round 1, R1-2 (c), "`memcpy_copies` is a closed `decide`" (unpinned): `memcpy_copies` is now `copies`' first conjunct, pinned, and its axioms are `[propext, Classical.choice, Quot.sound]`, not none.
- The header's "Head: cee37e7c60 (3 commits ...)" and round 1's "Head: 92d1d72c59": the head is a46b3a0470, 5 commits on 1773e6c8c5.
- Round 1's R1-5 "fixed by measurement": see R2-3, the line's cost is estimated, not measured.
- Round 1's "no run refuting them" and "Both stay class C" in `notes/status.md`: rewritten as above.

## Golf

Skill `lean4:golf` loaded. Range golfed: 1773e6c8c5..a46b3a0470. One commit, 77ac3f75d9, touching only `Table/CopyScratch.lean` (a file the change introduced; it has no dependents). 58 insertions, 68 deletions. No statement of a named result changed: the statements of `memcpy_byteFrame_false`, `memmove_byteFrame_false`, `memcpy_srcOnStack_false`, `memcpy_dstOnStack_false`, `copySpec_pre_inhabited`, `copies`, `memcpy_copies_aboveTop`, `memmove_copies_overlap`, `memcpySpec_of_keepAll`, `memmoveSpec_of_keepAll` are byte for byte as before (only `:= by` became `:=` where a proof became a term), and their `#guard_msgs` axiom checks still pass.

- G1. `entry_noWrap` replaced by `entry_copyPre`. The old helper gave the two `NoWrap` conjuncts and each of the five call sites rebuilt `CopyPre` from it, calling it twice (`.1`, `.2`) and proving the disjointness conjunct inline with `simp only [InRange, entryRegs]; simp; omega`. `entry_copyPre` gives all of `CopyPre o (entryRegs dst src n) (entryM st)` from `dst.toNat + n.toNat < 2^64`, `src.toNat + n.toNat < 2^64` and, when `o = false`, `dst.toNat + n.toNat ≤ src.toNat ∨ src.toNat + n.toNat ≤ dst.toNat` (the disjointness then follows by `omega` on `InRange`). It is a proof helper only: the sites discharge its numeric hypotheses by `decide` on the same literals as before, and `memmove`'s by `nofun` (`true = false`), as `fun h => nomatch h` did. Meaning preserved: it proves the same `CopyPre` terms the sites built by hand.
- G2. `not_holds`: the four refutations shared one shape (`lrunReturns_spec` on a `show ... by decide` run, then `Contract.not_of_lrun` with `entry_pre`). The helper takes the template equation, `hn`, the entry's `dst src n st`, the copy precondition, the Boolean `P`, the run's `lrunReturns ... = true` and a proof that `P` excludes `Post`, and gives `¬ Holds env (liftProg Gen.fns) f need Pre Post CopyOut`. Its proof is the old sites' two steps verbatim. Each witness is now one application with the same run (same body, return address `0x1000`, `stackTop`, fuel 1000, entry state, `P`) evaluated by the same `decide`, so the kernel check is the same evaluation; the witnesses' statements and the facts they rest on are unchanged.
- G3. `not_copied`: the two "copied wrong" witnesses read a wrong destination byte by the same three lines (`List.any_eq_true`, `bne_iff_ne`, `hc k`). The helper does this once; `List.mem_range.1` replaces `by simpa [entryRegs] using hk` (the bound `(entryRegs dst src n .x12).toNat` is `n.toNat` by definition). The byte-frame witnesses' `simp only [bne_iff_ne, ne_eq] at hb; exact hb ...` became `bne_iff_ne.1 hb ...`, the same lemma applied directly.

Not changed (considered): `memcpySpec_of_keepAll`/`memmoveSpec_of_keepAll` share a proof, but a generic lemma over the overlap flag plus the two named instances is no shorter; no `Holds` consequence lemma exists to use instead. `Core/LocalRun.lean`, `Core/HoldsOfHoldsT.lean`, `Total/ToContract.lean`, `Table/MemT.lean` and the re-proved users are already direct; `copyPostT_eq` stays as the stated old-to-new relation.

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Table.CopyScratch` (no module imports it) -> `✔ [4743/4744] Built Rv64mc.Table.CopyScratch (24s)`, `Build completed successfully (4744 jobs).` No `sorry`, `axiom` or `native_decide`; no em or en dashes in the diff.

## Amendments, round 4

Final head: bf098e69b2, 7 commits on 1773e6c8c5 (c68b9e224e witness, 5554ceab82 statement fix, cee37e7c60 bridge, 92d1d72c59 guards, a46b3a0470 runs, 77ac3f75d9 golf, bf098e69b2 this round). This line supersedes the header's "Head: cee37e7c60 (3 commits ...)" and every later head named in this file. This round changes `Table/CopyScratch.lean` and `notes/total-correctness.md` only, both in the allowed list. No statement of an existing definition or theorem changed: the round adds `guards_pre_inhabited` and `scrambled`, makes three proof helpers `private`, and changes the memory the guard runs (`CopiedRight`, `memcpyRight`, `memmoveRight`, all introduced by this change) start from. `MemcpySpec`, `MemmoveSpec`, `CopyPost`, `Holds`, `HoldsT`, `TContract`, `Total`, `MainSpec*` and `EndStatement.lean` are untouched.

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Table.CopyScratch` (no module imports it) -> `✔ [4743/4744] Built Rv64mc.Table.CopyScratch (34s)`, `Build completed successfully (4744 jobs).`, exit 0 (log runFixCopy/check-r4.log). Full build at bf098e69b2, `free -g` showing 28 GB available: `timeout 3600 systemd-run --user --scope -q -p MemoryMax=24G lake build Rv64mc` -> `Build completed successfully (5885 jobs).`, exit 0, only the pre-existing `Proof/Field/Reverse.lean` warnings (log runFixCopy/fullbuild-r4.log; it replays, since the check had just built the one changed module, which the `Rv64mc.+` glob includes). `git diff 1773e6c8c5 | grep -cP '[\x{2013}\x{2014}]'` -> 0; no `sorry`, `axiom`, `native_decide` added; `maxRecDepth` still added 7 times (no new kernel run). New `#guard_msgs` pin: `guards_pre_inhabited` -> `[propext, Classical.choice, Quot.sound]` (twelve pins now).

### R1-2-1 (both reviewers): deferred (unchanged; owner's decision)
- Both reviewers accept the deferral. `Table/Runtime.lean` still takes `MemcpySpec`/`MemmoveSpec` as hypotheses and `memcpyHolds` has no user. What it takes is as in rounds 1 and 2: a partial proof of `MemcpySpec` (replaying `Proof/Runtime/MemcpyT.lean` against `Holds` without `Windows`) and of `MemmoveSpec` from scratch; a task of its own.

### R3-2-2 and R4-2-1 (wording part): fixed
- CopyScratch header: "so do `memcpy` to a destination above the stack pointer and `memmove` with overlapping ranges, from states meeting the same precondition (`guards_pre_inhabited`)". `notes/total-correctness.md`: "pin a destination above the stack pointer and overlapping ranges, from states meeting the same precondition (`guards_pre_inhabited`)".
- `copies`' docstring: "**`memcpy` and `memmove` copy from `copySpec_pre_inhabited`'s state**, with `scrambled` memory."

### R3-2 and R4-2-1 (R3-2 part): fixed
- New `guards_pre_inhabited (st)`: `Holds.pre` at `env` with `CopyPre o ∧ CopyApart env` for the three other guard runs' registers: `memcpy` `(stackTop + 8, 0x1fffff84, 24)` (`Owned` by `top ≤ dst`, source `OffStack` below the stack's limit), `memmove` `(0x1fffff00, 0x1fffff04, 24)` and `(0x1fffff04, 0x1fffff00, 24)` (`Owned` below `NEXT` by `entryM_next`). Proved with `entry_pre`, `entry_copyPre` and `decide` on the literals, as `copySpec_pre_inhabited`. Every guard run's start now meets the corrected precondition by a checked theorem, not by a reader's arithmetic. Like `copySpec_pre_inhabited` it holds for any `st`, so for the `scrambled` state below too.

### R3-1 and R4-2-1 (R3-1 part): fixed
- The guard runs started from `entryM id`, where each doubleword holds its own address, so neighbouring doublewords differ in byte 0 only and a copy reading the right byte of the wrong neighbouring doubleword could pass at offsets 1 to 7. They now start from `entryM scrambled`, `scrambled a = a * 0x9E3779B97F4A7C15 + 0x0123456789abcdef` (an odd multiplier), which `CopiedRight` reads too. All three guard theorems (`copies`, `memcpy_copies_aboveTop`, `memmove_copies_overlap`) still `decide` to `true` with unchanged statements; the module builds in 34 s (24 s before). Round 3's reviewer probe (runFixCopy/probe/R3.lean) ran the same five runs from this state and showed a source 8 bytes off decides to `false`, so the check discriminates.

### R4-2: fixed
- `entry_copyPre`, `not_holds`, `not_copied` are `private`; `not_holds`' docstring has no bold headline. `entry_pre` stays public: it is not one of the three named and `copySpec_pre_inhabited` is stated over `Holds.pre`, which it builds.

### R4-1 and R4-2-2: fixed in this text
- The first `## Golf` section ("No golf pass was run on this change") was true when written (round 1, head 92d1d72c59) and is superseded by the second `## Golf` section, the golf pass of 77ac3f75d9. Read the first as "Golf, round 1" and the second as "Golf, after round 2". Earlier entries are not edited, so the correction stands here.
- Head and commit count: as at the top of this round (bf098e69b2, 7 commits).
- G1's "calling it twice" held of the four witnesses only; `copySpec_pre_inhabited` called `entry_noWrap` once (`have hw`). The code was right either way.
- Round 3's four nits (R3-1, R3-2, R3-2-1 as carried into R3-2, R3-2-2) had no disposition in this file; they have one now, above.

### R4-2-3: fixed
- The full build was rerun at the final head bf098e69b2, after the golf commit and this round's: success, 5885 jobs, as above. The previous full build (fullbuild-r2.log) was of a46b3a0470, before the golf; the golf's check covered its one module, which has no importer.
