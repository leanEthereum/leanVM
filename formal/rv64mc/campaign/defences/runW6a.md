# Defence: wave 6a, pass 1: `memmove` (225) total, its `Table` instances, the C wrapper (228) re-instantiated

Base: 9e5e456cca. Head: 2d23011d83 after pass 3 (see "## Pass 3"; after pass 2 it was d55dd25d3a; pass 1: b9aa247108 wip, df9e69f18a feat, ab9f60823b docs, head ab9f60823b; pass 2: see "## Pass 2").
Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Runtime.MoveT Rv64mc.Proof.Runtime.MemmoveFwdT Rv64mc.Proof.Runtime.MemmoveBwdT Rv64mc.Proof.Runtime.MemmoveProofT Rv64mc.Table.MemT6a` -> `Build completed successfully (4958 jobs)`; per module MoveT 8.7 s, MemmoveFwdT 80 s, MemmoveBwdT 139 s, MemmoveProofT 23 s, MemT6a 5.8 s (wall 3 m 3 s, `warningAsError = true` in the lakefile, so no warnings). Run after the last Lean change (df9e69f18a); ab9f60823b changes only `notes/total-status.md`.

Of the wave's list only item 1 (`memmove`) is done. Items 2 to 5 are not started (see Not done).

## Decisions

### D1. `memmove`'s proof split into four new modules, `MemmoveT.lean` untouched
`Proof/Runtime/MoveT.lean` (shared definitions and lemmas, the return), `MemmoveFwdT.lean` (forward copy, `fwd_ok` at pc 128), `MemmoveBwdT.lean` (backward copy, `bwd_ok` at pc 8), `MemmoveProofT.lean` (`total : MemmoveSpecT env p i 16` for `p[i]? = some (tmpl L)`).
- **Why**: the statement's file must stay unchanged; the forward and backward halves are each a few hundred lines and build separately (80 s, 139 s), so an edit to one does not rebuild the other.
- **Rejected**: one file (a 2000-line module rebuilt for every change); a restated contract (the brief forbids a weakened restatement).
- **Claims**: `total` proves `Rv64mc.Proof.Runtime.MemmoveT.MemmoveSpecT` itself: its type is `MemmoveSpecT env p i 16`, the definition is imported unchanged (`git diff 9e5e456cca -- formal/rv64mc/Rv64mc/Proof/Runtime/MemmoveT.lean` is empty). Its axioms are `[propext, Classical.choice, Quot.sound]` (`#guard_msgs` at the end of `MemmoveProofT.lean`).
- **Evidence**: the build above; `#print axioms` pinned in `MemmoveProofT.lean` and `Table/MemT6a.lean`.

### D2. `MoveT.Regs` leaves `s0` out; the invariants carry the saved word
`Regs ret top regs r := r .x1 = ret ∧ r .x2 = top - 16 ∧ AbiRegs (top - 16) regs (updReg r .x8 (regs .x8)) ∧ r .x10 = regs .x10`; `FInv = CopyT.Inv ∧ M.getMem (top - 8) = s0`, `BInv = InvB ∧ M.getMem (top - 8) = s0`.
- **Why**: `memmove` saves `s0` at `sp + 8` (pc 2) and uses `x8` as scratch in the misaligned backward loop (pc 110, `x8 = x17 + x5`); `ret_ok'` reloads it at pc 450, so the saved doubleword must be tracked through every store. `getMem_saved` shows a store aligned for its width below `top - 8` or at or above `top` keeps it; destination stores are at or above `top` or below `stackLimit` (`OffStack`, `Fx.dtop`), scratch stores in `[top - 16, top - 8)`.
- **Rejected**: `memcpy`'s `Regs` (AbiRegs over `r`), false here once `x8` is written.
- **Claims**: `Regs.upd` holds for writes of `x5..x8, x11..x17, x28..x31`; the return gives `AbiRegs top regs r'` with `x8` restored (`ret_ok'`).

### D3. The forward copy is `MemcpyT`'s proof transported, with a weaker apartness
`MemmoveFwdT` is `MemcpyT.lean` lines 110 to 803 rewritten by a script (pcs mapped L -> L+63 / L+74 / L+128 by the template's blocks; `Inv` -> `FInv`; scratch slot `top - 8` -> `top - 16`; `r .x2 + 8#64` -> `r .x2`), then fixed by hand where goals differed (in `endPartial_ok` the closer now discharges the halfword stores' windows itself, so those two bullets were deleted).
- **Why**: from pc 128 the forward path is `memcpy`'s code instruction for instruction except the slot offset and the return.
- **Claims**: `FxF.disj : ∀ k k', k ≤ k' → k' < n → dst + k ≠ src + k'` replaces `memcpy`'s full disjointness; every source read of the forward copy is at an index at or after the bytes copied (`FxF.src` takes `src + j ≤ a`), which holds at each use (`loopD`, `loopC`, `lastByte`, `partial`, `loopB`, `endWord`, `endPartial`, `loopA` read at `src + j + t` or `src + j - o + 8 + t` with `o < 8`). `total` derives `FxF.disj` from the branch at pc 6 (`dst - src` wrapping at least `n`) with `NoWrap` of both ranges.

### D4. The backward copy: a new invariant `InvB` (bytes from `j` on copied) and parts mirroring the code
Parts, each from a program counter: `loopS_ok` 438 (suffix loop), `sfx_ok` 432, `after_ok` 426, `loopG_ok` 296 (aligned words), `alB_ok` 288, `lastB_ok` 412, `endWordB_ok` 404, `endBit2B_ok` 400, `endB_ok` 376 (`load_aligned_end_partial`), `loopH_ok` 100 (misaligned words), `prevB_ok` 84, `lastByteB_ok` 74, `bit0B_ok` 70, `misB_ok` 56 (`load_aligned_partial`), `mid_ok` 42, `loopE_ok` 30 (prefix loop), `bwd_ok` 8.
- **Claims**: `FxB.disj : ∀ k k', k' < k → k < n → dst + k ≠ src + k'`, derived in `total` from `dst - src` (wrapping) below `n` (so `src ≤ dst < src + n`); every backward read is at a source index below the current `j` (`FxB.src` takes `a < src + j`). The reassembled doubleword uses `CopyT.extractByte_shr_or_shl` with `p` the lower source doubleword and `c` the upper; `Mid` carries the registers `x13..x16` the doublewords' parts keep.
- **Evidence**: the build; each part's statement names its pc, and the template's labels give pc = 2 x label.

### D5. Loops and measures
- **Claims**: eight loops, each `Total.loop` with a `Nat` measure strictly decreasing at the back edge: forward `DInv c` (c-1), `CInv k` (k-8), `BInv k` (k-8), `AInv c` (c-1) (as in `MemcpyT`); backward `SInv c` (c-1), `GInv j` (j-8), `HInv j` (j-8), `EInv j` (j-1). Each `ih` application has `by omega` for the decrease from the branch outcome. The template has twenty back edges counting the partial loads' joins; the others are forward jumps between the parts (no part calls itself except through `ih`).

### D6. Raised budgets in `MemmoveBwdT`
`endWordB_ok` 400000, `endB_ok` 1000000, `loopH_ok` 1000000, `misB_ok` 1000000, each with a one-line reason above it (`rv_symT` over the part's paths runs past the default budget).
- **Why**: measured: each fails at 200000 (`loopH_ok` and `endWordB_ok` also tried with the budget removed: deterministic timeout). For `loopH_ok`, `rv_symT` stepping the doubleword load at `x29 + x5 - 8` alone did not finish within 5000000; stepping it by hand (`TotalRv.label`, `TotalRv.ld8` with the window and alignment facts `hwA`, `hA8`) and `rv_symT` from pc 106 fits in 1000000. I did not find why `rv_symT`'s load handling is slow there (two register symbols in the address); see Known risks.
- **Rejected**: splitting the parts further: possible, not tried, for time.

### D7. Hiding facts from `rv_symT`'s closer
In several parts `Regs`, `Mid`, the loop invariant and a register equation are held as `True → P` (`hR'`, `hM''`, `h5`, `hcur'`) or `clear`ed before `rv_symT`, and some `omega` calls take `clear * - ...` first.
- **Why**: the closer's `arithFacts` unfolds every hypothesis (Sym.lean, `arithFacts`), and with `AbiRegs` over `updReg r .x8 _`, `Mid`'s word equation `r .x16 = 0 - ofNat _` and the window disjunctions, `omega` ran out of heartbeats or recursion depth. `True → P` is a fact `arithFacts` does not read; each is reopened by `hR' trivial` after the step.
- **Claims**: nothing proved changes: the hidden facts are re-obtained unchanged.

### D8. `Table/MemT6a.lean`: `memmoveT` and `memmoveWrapT`
`memmoveT : MemmoveSpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memmove Needs.CompilerBuiltins.Mem.Memmove` (by `HoldsT.mono_need`, `Needs` is 16); `memmoveWrapT : MemmoveSpecT env (liftProg fns) Idx.Memmove Needs.Memmove := RuntimeT.memmove env (memmoveT env)`.
- **Claims**: the only `Table` theorem that took `MemmoveSpecT (225)` as a hypothesis is `RuntimeT.memmove` (`grep -rn MemmoveSpecT formal/rv64mc/Rv64mc/Table` at base lists only `RuntimeT.lean`); `memmoveWrapT` is it with the hypothesis discharged, so no `Table` theorem of 228 needs it; `RuntimeT.memmove` is left untouched (superseded, said in the legend). Status rows 225 and 228 now say `yes ... none`; the legend no longer lists `MemmoveSpecT (225)`.

### D9. A new obligation recorded, not discharged
`notes/total-status.md` "Obligations": `Form::add_scaled` (163) and `subspace_roots` (126) call the C `memmove` and must give `CopyPreT true` at those calls (163, template line 269: `dst = x21 + 40`, `src = x21`, `n = 40 * (x25 - x27)`, the overlapping case; 126, line 305: `dst = x20`, source and length from `sp + 8`, `sp + 16`).
- **Claims**: read from the templates only; not proved; whether both ranges are inside the vector's heap block (so `BufT` gives the windows) is argued, not checked against the callers' Rust.

## Invariants of the whole change
- No existing file's Lean changed: `git diff 9e5e456cca --name-status` lists only added `.lean` files (`MoveT`, `MemmoveFwdT`, `MemmoveBwdT`, `MemmoveProofT`, `Table/MemT6a`) and modified `README.md`, `notes/total-correctness.md`, `notes/total-status.md`.
- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `implemented_by` added: `git diff 9e5e456cca | grep -E '^\+.*\b(sorry|admit|axiom|native_decide|bv_decide|implemented_by)\b' | grep -v "axioms"` is empty.
- No `Tactic/` change; `rv_symT` used as is.
- No line over 120 characters in the new files; no em or en dashes (`grep -n "—\|–"` on them is empty).

## Not done
- Items 2 to 5 of the brief (`Form::add_scaled` 163, `from_elem` 159 and 160, `spec_extend` 202, `extend_trusted` 176; `eq_above` 101, `state_derived` 194, the two `concat`s 87 and 110; `stack` 182, `bus_layout` 150, `group_by_word` 218, `Table::constraints` 145, the drops 71 and 70, toward `build_layout` 45): not started; `memmove` (268 instructions, 20 back edges, no partial proof) took the pass's budget. Every callee of these is total at the image (checked against `notes/total-status.md`: 163's 166, 165, 226, 228, 25; 159's 8, 169, 165, 6; 160's 8, 168, 73, 6; 202's 8, 169, 165, 6; 176's 178, 168; 101's 15, 98, 102; 194's 17, 179, 162, 200, 6; 87's and 110's 8, 106, 6), so each is unblocked; `add_scaled` now has `memmove` total too.
- No golf of the forward file: it keeps `MemcpyT`'s structure and some of its now-unneeded generality (e.g. the local `tlit` macro and `slot_addr` naming).
- The summary counts of `notes/total-status.md` are left to the merge, as the brief says.

## Known risks
- `MemmoveFwdT` is a mechanical transport of `MemcpyT`: a reviewer should check the pc map (`fwd.py` in the run directory: 20->146, 32->158, 44->170, 64->190, 68->194, 76->202, 90->216, 110->236, 124->250, 128->254, 138->264, 166->314, 176->324, 184->332, 196->450) against the template, though a wrong pc would not build.
- `FxF.disj` with `k ≤ k'` (not `k < k'`): stronger than needed; `total` derives it, so it is not an assumption, but check the derivation (`omega` over `BitVec.toNat_sub` of the branch at pc 6 and `NoWrap`).
- D6's raised budgets: the `rv_symT` slowness on a load at a two-register address is unexplained; a later wave hitting the same pattern may want the by-hand `TotalRv.ld8` step (`loopH_ok`) rather than a budget.
- D9's caller obligation for 163 and 126 is an argument from the templates, not a proof; `CopyPreT true` asks the destination in the heap window up to `heapEnd`, which a vector's spare capacity has only if the block was allocated with it.
- The `wip` commit message (b9aa247108) does not follow the conventional form `feat(formal): ...`; the later commits do.

## Pass 2: `Form::add_scaled` (163) total, its `Table` instance

Head: d55dd25d3a (commits b8312f5a05, a7b94ae073, f91ed14edd wip; d55dd25d3a feat). Skills `lean4:prove`, `lean4:refactor`, `writing-lean-proofs` loaded.
Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Layout.AddScaledSearchT Rv64mc.Proof.Layout.AddScaledT Rv64mc.Table.FormT6a` -> `Build completed successfully (5282 jobs)`; per module AddScaledSearchT 16 s, AddScaledT 109 s, FormT6a a few seconds (`warningAsError`, so no warnings). Run on d55dd25d3a's tree; a rerun replays all three.

Of the list, item 2's first function (`add_scaled`) is done; the rest of item 2 (159, 160, 202, 176) and items 3 to 5 are not started.

### D10. The contract: `AddScaledT.SpecT`
`PreT`: `self` (`a0`) `FormT` and `Owned` at the stack pointer (`grow_one`'s `GrowPreT` needs `Owned`); `other`'s terms (`a1`, `a2`, the slice LLVM passes for `&Form`) `BufT` (the length for the capacity) and `TermsT`; `self`'s header apart from its buffer (unless the capacity is `0`); `other`'s terms apart from `self`'s header and buffer (unless empty), as `PairT.Apart`. `PostT`: `FormT` of `self` and `PairT.KeptOrFresh` of its buffer. `OutT`: `self`'s 24 bytes and its buffer at the entry (`40 * cap` bytes). `Stop := AbortStop` (`clone`, `grow_one`).
- **Why**: class D, no spec: safety only, as `CloneFormsT`. The apartness is Rust's `&mut self` against `&Form`; without it a length store or a term store could change `other`'s terms' monomial headers, whose windows later loads need. `other`'s monomial buffers need no apartness: only their headers (in `other`'s terms block) decide the windows, and nothing writes the buffers.
- **Post for the callers' loops** (wave 5a's lesson): `verify_bus_balance` (48) calls it in a loop on the same `self` (`sp + 0x3d0`) with `other` each `Form` of a vector. The next call's `PreT` needs `FormT` again (given), the header apart from the buffer (from `KeptOrFresh` and `Owned`, as `AddScaledT.hdr_apart` derives it), and the next `other` apart from `self`'s buffer (the buffer is `constant`'s fresh one or a fresh one from `grow_one`, both allocated after the vector's `Form`s); `OutT` keeps those `Form`s. Recorded as an obligation on 48 and 193 in `notes/total-status.md`.
- **Claims**: `total` is axiom-clean (`#guard_msgs` at the end of `AddScaledT.lean` and `Table/FormT6a.lean`: `[propext, Classical.choice, Quot.sound]`).

### D11. The body cut into parts, each from a program counter (pc = 2 x label)
`AddScaledSearchT`: `search` (pc 50, the outer loop's head, to pc 108), `bsearch` (270, binary search, `Total.loop` on the candidates left `x13`), `loopB` (296, word comparison inside it, `Total.loop` on the words left), `final` (62) and `loopA` (82, the last comparison, `Total.loop` on the words left). The search only loads, so its parts take the memory as fixed and conclude at pc 108 with `x27` at most the length and the registers the body reads (`SKeep`).
`AddScaledT`: `outer` (50, `Total.loop` on `other`'s terms left, `OInv`), `at108` (54: the index at the length goes to the insertion), `at116` (58: a term there; `memcmp`, then `E::mul` and the coefficient's two stores, or the insertion), `ins` (174, label 87: `clone` into `sp + 16`, `E::mul`, `grow_one` when full), `move` (208, label 104: `memmove` of the later terms one up), `store` (232, label 116: the new term's five words and the length), `exit` (324), and the entry in `total`.
- **Why**: each `rv_symT` run fits the default heartbeats; `at108` and `at116` were one part, which ran out of heartbeats (the limit is per declaration), so they were split rather than a budget raised. No `maxHeartbeats` option in either file.
- **Claims**: every loop has a measure strictly decreasing at its back edge: `outer` `k` (the back edge needs `x26 ≠ x22`, so `k > 0`, `ih (k - 1)`), `bsearch` `k - k / 2 < k` from `2 ≤ k`, `loopA`/`loopB` `c - 1` from the counter not `0`.

### D12. Memory invariants
`MemOk` (thirteen slots, `env.Frame top OutT m M`, `env.Static`, the code) with `FormT env M a` and `KeptOrFresh env m M a`. `other`'s terms are not carried: `oth_kept` derives them kept from the frame alone (below `NEXT` at the entry, apart from `OutT` by `PreT`), so `oth_terms` gives their `TermsT` in every memory the parts reach. Helper lemmas: `buf_store` (a store into `self`'s current buffer is in `OutT` when the buffer is the entry's, fresh otherwise), `hdr_store`, `call_keep`, `call0` (a callee writing nothing), `after_cm` (`clone` then `E::mul`), `after_grow` (the terms' headers in the new buffer from `Grown`'s copied bytes, by `Transcript.getMem_of_bytes` and `CloneFormsT.vecT_copy`), `move_mem` (`memmove`'s bytes: the terms after `j` moved one up, `GapT` the terms but `j`), `term_mem` (the six stores give `FormT` of `n + 1` terms), `coef_mem` (the coefficient's two stores keep `FormT`).
- **Claims**: `GapT env M P n j` (every term `t ≤ n`, `t ≠ j`, a monomial `VecT`) is what `move` gives and `store` takes; `term_mem` fills `j` from the clone's header at `top - 128`.

### D13. Hiding facts from `rv_symT`'s closer (as pass 1's D7)
In `store`, `move`, `ins`, `at116`, `at108` the facts with disjunctions or definitions the closer unfolds (`MemOk`, `FormT`, `Args`, `BufT`, `InWin`) are held as `True → P` before `rv_symT` and reopened after; without it `move` and `at116` ran out of heartbeats. Window facts the closer does not find (`inWindow (o + 8) 8 = true` and the like) are proved before the run (`inWin_word`) and closed by `exact` where the closer leaves them.

### D14. Callees' preconditions discharged at their calls
`memcmp` (`CmpPreT`: both monomials' `len * 8` bytes in windows, from their `BufT`, the lengths equal by the branch), `Vec<usize>::clone` (`ClonePreT`: `sp + 16` `Owned`, in the stack window, aligned; `other`'s monomial `BufT`), `grow_one` (`GrowPreT 8 40`: `Owned` at `sp`, `RawVecT`), `E::mul` (`True`), the C `memmove` (`CopyPreT true`: `NoWrap`, destination and source in the heap window up to `P + 40 cap ≤ NEXT ≤ heapEnd`, both `OffStack`). The last is pass 1's D9 obligation for 163, now discharged (struck in `notes/total-status.md`'s entry, 126's half left).
- **Evidence**: each is a goal `rv_symT` leaves or closes at the call in `at116`, `ins`, `move`; the build.

### D15. `Table/FormT6a.addScaled`
`AddScaledT.SpecT env (liftProg fns) Idx.Verifier.Layout.Form.AddScaled Needs.Verifier.Layout.Form.AddScaled` from `RuntimeT.memcmp`, `FieldT.eMul` (`clmul table`), `VecT.cloneUsize` (`env`), `AllocT.growOneVecUsizeE` (`env`; its `byteAlign`, `byteSize` are `8`, `40` by `rfl`), `MemT6a.memmoveWrapT`. Open hypotheses: `env` and `clmul table`, both in the status legend already. Status row 163 updated; README's layout names `AddScaledT`, `AddScaledSearchT`, `FormT6a`.

### Invariants of pass 2
- No existing file's Lean changed: pass 2 adds `Proof/Layout/AddScaledSearchT.lean`, `Proof/Layout/AddScaledT.lean`, `Table/FormT6a.lean` and edits `README.md` and `notes/total-status.md` only (`git diff ab9f60823b --name-status`).
- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `implemented_by`, `maxHeartbeats` in the new files; no em or en dashes; no line over 120 characters.

### Not done (pass 2)
- Item 2's rest: `Form`'s `from_elem` (159, 188 instructions: `vec![form; 3]`, allocates three `Form` headers, `reserve`, clones the `Form` twice term by term (`Vec<usize>::clone` per term, two copies of the term loop) and moves it into the last slot), `Vec<Form>`'s `from_elem` (160), `spec_extend` (202), `extend_trusted` (176). Not started, for budget: `add_scaled` took the pass. Every callee of these is total (pass 1's list); 159's shape is `CloneFormsT`'s inner loop twice.
- Items 3 to 5: not started.
- The obligation on `add_scaled`'s callers (48, 193) is argued from the templates, not proved.

### Where to look hardest (pass 2)
- `PreT`'s apartness against the call sites in 48 (template labels 725 and 740) and 193 (label 13): the `self` at 740 is a `Form` in a heap block (`*(sp + 0xf8) + 8 x9 + *(sp + 0x100)`), read from the template only.
- `OutT` names the entry's buffer; a write into a buffer `grow_one` returned is in the frame as fresh memory (`buf_store`'s second case). A caller relying on `OutT` for blocks allocated during the call gets nothing from it; `KeptOrFresh` is what tells it where the buffer went.
- `search`'s `SKeep` fixes `x25` as `M.getMem (a + 16)`, the length loaded at label 25 each iteration; `ins` re-reads the capacity after `clone` and `E::mul` (`after_cm` keeps the header).
- I first checked the parts with `lake env lean`, which does not take the lakefile's `autoImplicit false`; `move`'s `X22`, `X26` were auto-bound there and the `lake build` caught it (fixed before the feat commit). The final check is the `lake build` above.

## Pass 3: `from_elem::<Form>` (159), `from_elem::<Vec<Form>>` (160), `Vec<Form>::clone` with fresh terms' blocks

Head: 2d23011d83 (commits 91562b3b15 feat 159; 2d23011d83 feat 160 and `CloneFormsFreshT`). Skills `lean4:prove`, `lean4:refactor`, `writing-lean-proofs` loaded.
Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Layout.CloneFormsFreshT Rv64mc.Proof.Layout.FromElemVecFormT Rv64mc.Proof.Layout.FromElemFormT Rv64mc.Table.FormT6a` -> `Build completed successfully (5290 jobs)` (wall 1 m 7 s on a warm tree; `CloneFormsFreshT` alone rebuilt in 1 m 33 s, `FromElemFormT` in 42 s, `FromElemVecFormT` about 45 s by `lake env lean`; `warningAsError`, so no warnings). Run on 2d23011d83's tree.

Of the list, item 2's `from_elem`s (159, 160) are done; `spec_extend` (202) and `extend_trusted` (176) and items 3 to 5 are not (see "Not done (pass 3)").

### D16. 159's contract asks the element empty
`FromElemFormT.PreT`: `sret` `SretPre`, `InWin`, 8-aligned; the element (`a1`) `Owned`, `VecT` of 40-byte terms and `vecLen = 0`. `PostT`: `VecT` of the result, length `3`, the buffer `Fresh` (72 bytes), `FormsT` of its three `Form`s. `Out`: `SretVecOut`; `Stop := AbortStop`.
- **Why**: the function is `vec![form; 3]` specialised (the count `3` is folded into the code). Its one call site (`verify_bus_balance` (48), template label 421; `cg.json` lists 48 as the only caller, and 48's template has one call to it) passes `sp + 0x3d0`, which 48 stores as `(0, 8, 0)` at labels 415 to 417 just before. With the element empty the two term-clone loops (labels 69, 114) are never entered, so the proof is straight-line: the path into them (label 47's `40 len != 0` branch) is refuted in `tail` from `vecLen = 0`. `Vec<usize>::clone` is then never called, so `total` does not take its contract.
- **Rejected**: a contract for any `FormT` element: it needs both term loops (`CloneFormsT`'s inner loop twice, about 600 lines) for a case the image never runs.
- **Claims**: every conjunct of `PreT` holds at label 421 from 48's frame facts and those three stores (recorded in `notes/total-status.md`'s "Obligations"); `PostT` is what 160 needs of its element (`VecFormT` = `VecT` and `FormsT`).
- **Evidence**: `FromElemFormT.total`, `#guard_msgs` axioms `[propext, Classical.choice, Quot.sound]`.

### D17. 159's proof structure
`rv_autoT` to `reserve`'s return (pc 56); `hdr_kept` (the frame's words after `reserve`, from its `GrowOut` frame and the spare-capacity branch of `ReservePost`, `hdr_spare`), `memOk_of` (the thirteen slots and the header's `3`, `q` from those words), `tail` (pc 56: the bound's word load, the refuted branch, the first `Form` `(0, 8, 0)` at `q`), `fin` (pc 286: the two other headers, the result's, to the epilogue), `fin_mem` (the nine stores' frame and the postcondition, by `CloneFormsT.heap_store`, `CloneFormsT.hdr3`, `CloneFormsT.new_form`, `CloneFormsT.vecT_copy`), `exit` (pc 316, the epilogue: the executor reads the slots from `Slots`, `AbiRegs` closed by hand).
- **Why**: running `rv_symT` through the nine stores and the thirteen slot loads in one go ran out of heartbeats; stopping at 316 and giving `exit` an abstract memory with `Slots` fits (no raised `maxHeartbeats` in this pass). It reuses `CloneFormsT`'s `Slots`/`MemOk` (the same thirteen saved registers at `top - 8` to `top - 104`).
- **Environment fact**: the bound's word (`isize::MAX / 40` at `d_c8_51ab739d`) is loaded, so `total` takes `DataRef.InData` for it (`Form from_elem bound (InData)`, added to the status legend); its value does not matter for safety.

### D18. A finding against 168's contract, and `CloneFormsFreshT`
`CloneFormsT.PostT` (wave 5a) gives the clone's buffer fresh but places the clones' `Form`s' terms' blocks only below `NEXT` (`FormT.foot`). `from_elem::<Vec<Form>>` stores each clone's header into its result's block, allocated before the clones, then reads all of them at the end: `FormsT` reads each `Form`'s terms' block, which the contract allows to lie in that block. So 160's loop cannot keep the earlier clones from the contract as stated (wave 5a's lesson: a Post must give what a caller's loop needs). `CloneFormsFreshT.PostT := CloneFormsT.PostT ∧ FreshTermsT` (each clone's `Form` has no terms or its terms' block in `[NEXT at entry, NEXT at return)`).
- **Why this way**: no existing statement changes. `CloneFormsFreshT` imports `CloneFormsT` and restates only the declarations whose statements mention `PostT` (`exit`, `join`, `back`, `after`, `inner`, `outer`, `total`, copied verbatim, `open CloneFormsT hiding` those), changing only `exit`'s `hPost`: `FreshTermsT` follows from the invariant `CloneFormsT.DoneT` it already holds (`D + 24 n ≤ ptr`, `ptr + 40 len ≤ H ≤ NEXT`, `NEXT at entry ≤ D` by `Blk`). `SpecT.weaken` shows the new contract gives the old one.
- **Rejected**: editing `CloneFormsT` (an existing statement); deriving freshness from the frame (impossible: the old Post does not say where the blocks are).
- **Claims**: `CloneFormsFreshT.total` has `CloneFormsT.total`'s hypotheses exactly; `Table/FormT6a.cloneFormsFresh` instantiates it like `FormT5a.cloneForms`. 176 will need the same (it stores clones into the vector's buffer): recorded in "Obligations".

### D19. 160's contract
`FromElemVecFormT.PreT`: `sret` `SretPre`, at or above the stack pointer (`regs .x2 ≤ sret`), `InWin`, 8-aligned; the element `Owned` and `VecFormT` (`VecT` of 24-byte headers and `FormsT` of its buffer); `n * 24 < 2^63`. `PostT`: `VecT` of the result, length `n`, buffer fresh unless `n = 0`, each element `VecFormT`. `Out`: `SretVecOut`; `Stop := AbortStop`.
- **Why `sret` on the stack**: the last element is the element moved (its header copied), whose buffer and `Form`s are the caller's old heap blocks; `sret`'s stores must not touch them. At the one call site `sret = sp + 0x298` (48, label 427). A heap `sret` would need an apartness conjunct instead.
- **Why `n * 24 < 2^63`**: the code computes `24 n` without a check and passes it to `alloc` (`AllocPre`: below `2^63`); a wrapped size would make the loop's stores leave the block. At 48 `n = *(x23 + 0x10)`, `x23` 48's second argument: argued to be a vector's length (its bytes below the heap's end), not checked further; 48's proof discharges it.
- **Claims**: at 48 the element `sp + 0x2b0` is 159's result: `FromElemFormT.PostT` gives `VecFormT` (its `vecLen = 3` and `FormsT ... 3`), and labels 422 to 426 write only `sp + 0xc0`. Recorded in "Obligations".

### D20. 160's proof structure and invariants
Parts by pc (= 2 x label): `total` (entry to 60, 86 or 114: `n = 0` drops the element (`DropSpecT`, writes nothing) and goes to 114 with `(0, 8, 0)`; `n = 1` goes to the move; else the loop), `loop` (60, `Total.loop` on the clones left `k`, `LInv`; steps to after the clone's return and hands over to `after`), `after` (70: the clone's three words stored at `D + 24 j`, then 60 with `ih (k - 1)` when `x23 + 24 != x22`, i.e. `k != 0`, or the move), `move` (86: the element's three words into the last slot, then 114), `fin` (114: the result's header, then 120), `exit` (120, the epilogue).
- `DoneV env M D n j H`: the first `j` slots are `VecFormT`, each lying (buffer, and each `Form`'s terms' block, unless empty: `FootV`) in `[D + 24 n, H)`. `vecForm_keep` keeps one from agreement on its header and on that range; `step_mem` gives `DoneV ... (j + 1) (NEXT)` after the clone's frame (writing its slot at `top - 96` and fresh memory) and the three stores (in `[D + 24 j, D + 24 j + 24)`, below `D + 24 n`). The new slot's footprint is fresh from `ClonePostT` and `FreshTermsT` (D18).
- `move_mem`: the element's header and `FormsT` are kept from the entry (all writes are at or above `NEXT` at the entry or on the stack below the stack pointer: `Frame.getMem_below_next`, `ReserveT.getMem_owned`).
- `fin_mem` (`Res`): the result's header `(n, D, n)` or `(0, 8, 0)`; every element `VecFormT` kept by the stores at `sret` (above `NEXT`: `VecFormT.keep_below`).
- **Measure**: `loop`'s `k` strictly decreases (`ih (k - 1)` under `k != 0`, from the branch).
- **Why the split at 70**: `loop` with the clone's call and the stores in one declaration ran past the default heartbeats; with `after` separate both fit. Facts the closer would unfold (`DoneV`, `MemOk`, `Blk`) are held as `True → P` across `rv_symT` in `loop` (as pass 1's D7).

### D21. Callees' preconditions discharged
- 159: `alloc` (`72 < 2^63`), `reserve` (`ReservePre` and `VecT` of the frame header `(3, q, 0)`, closed by the executor after `simp only [rvCapAt, ...]`), `handle_error`.
- 160: `alloc` (`24 n < 2^63` from `PreT`), `Vec<Form>::clone` through `CloneFormsFreshT` (`CloneFormsT.PreT`: the slot `sp` `Owned` at the callee's stack pointer, in the stack window, aligned; the element's buffer `BufT` (`vecT_buf`, `.mono`) and `FormsT` kept from the entry (`FormsT.keep_below`)), the drop (`True`), `handle_error`. Each is a goal `rv_symT`/`rv_autoT` closes from these facts at the call.
- The obligation "168's callers" in `notes/total-status.md`: its 160 part is now discharged (edited there); 176 and 45 remain.

### Invariants of pass 3
- No existing file's Lean changed: `git diff d55dd25d3a --name-status` adds `Proof/Layout/FromElemFormT.lean`, `Proof/Layout/FromElemVecFormT.lean`, `Proof/Layout/CloneFormsFreshT.lean` and modifies `Table/FormT6a.lean` (this wave's file: `fromElemForm`, `cloneFormsFresh`, `fromElemVecForm` added, `addScaled` untouched), `README.md`, `notes/total-status.md`.
- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `implemented_by`, `maxHeartbeats` added (`git diff d55dd25d3a | grep -E '^\+.*\b(sorry|admit|axiom|native_decide|bv_decide|implemented_by|maxHeartbeats)\b' | grep -v axioms` is empty); no line over 120 characters, no em or en dashes in the new files.
- Status rows 159, 160 (`yes`), 168 (both instances), the legend (`Form from_elem bound (InData)`), two new "Obligations" bullets (48's calls of 159 and 160; `CloneFormsFreshT` for 176), README's layout.

### Not done (pass 3)
- `spec_extend` for `Vec<Form>` (202, 127 instructions): not started. Its body is `reserve` then `CloneFormsT`'s two loops (each source `Form` cloned term by term, `Vec<usize>::clone` per monomial) with the clones written into `self`'s buffer; `CloneFormsT`'s lemmas are tied to its frame (176 bytes, its slots), so it is a proof of `CloneFormsT`'s size (about 1000 lines), beyond the pass's remaining budget. It also needs a contract for `self`'s buffer apart from the sources (Rust's `&mut self` against `&[Form]`) and the result's `Form`s' blocks fresh, as D18.
- `extend_trusted` over `BusBlock`s (176): not started. Read from its template: `reserve(self, (end - begin) / 24)`, then per source `Vec<Form>` a clone (`CloneFormsFreshT` needed, D18) and a 48-byte `BusBlock` stored at `self`'s buffer (the clone's header and three words read through the closure's captured pointers, the third at `C + 0x48`); the contract needs the source slice `VecFormT`, the captures readable, and `self`'s buffer apart from all of them.
- Items 3 to 5 (`eq_above` 101, `state_derived` 194, the two `concat`s, the layout chain): not started. `eq_above` is short (34 instructions, no loop, tail call to `eq_eval`) and class C: its partial `Post` follows from `PlacementRust.eqAbove`'s definition (which matches the code: `eq_eval(selector_point(index >> (variables % 64), len - variables), point[variables..])`) and the callees' `Post`s, but needs the slice suffix's `SliceArgs`/`EListAt` and the selector vector's `FreshVecE` in the memory after `selector_point`; a next pass can start there.
- The summary counts of `notes/total-status.md` are left to the merge.

### Where to look hardest (pass 3)
- D16: `vecLen = 0` in 159's `PreT`. It is narrower than the function; check that 48's call at label 421 is the image's only one and that labels 415 to 417 store `(0, 8, 0)` at `sp + 0x3d0` (template `Gen/Tmpl/Verifier/Bus/VerifyBusBalance.lean`).
- D19: `n * 24 < 2^63` at 48 (label 427, `n = *(x23 + 0x10)`): argued, not checked against what `x23` points to.
- D18: `CloneFormsFreshT` copies seven declarations of `CloneFormsT`; diff them against the originals (only `exit`'s `hPost` and the closing lines after its `rv_symT` differ, plus `clear hd2` before the window facts: with `hd2` in context one `omega` produced an ill-typed proof term).
- `FootV`'s lower bound `D + 24 n` for the clones: it holds because `D` is allocated before every clone (`Blk`: `D + 24 n ≤ NEXT` at the loop's head, and `FreshTermsT`'s blocks start at that `NEXT`).


## Golf

Commit 9e376d575c on 2d23011d83 (8 files, 38 insertions, 80 deletions). Only files the change added are touched; no statement, `Pre`, `Post`, `Out`, contract or `Table` theorem changes, and no definition a statement mentions changes. Skills: `lean4:golf` and `lean4:refactor` loaded.

Check (both runs on 9e376d575c's tree, `warningAsError`, so no warnings):
- `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Runtime.MoveT Rv64mc.Proof.Runtime.MemmoveFwdT Rv64mc.Proof.Runtime.MemmoveBwdT Rv64mc.Proof.Runtime.MemmoveProofT Rv64mc.Table.MemT6a` -> `Build completed successfully (4958 jobs)` (MoveT 9.5 s, MemmoveFwdT 78 s, MemmoveBwdT 137 s, MemmoveProofT 8.0 s, MemT6a 6.0 s).
- `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Layout.AddScaledSearchT Rv64mc.Proof.Layout.AddScaledT Rv64mc.Proof.Layout.FromElemFormT Rv64mc.Proof.Layout.FromElemVecFormT Rv64mc.Table.FormT6a` -> `Build completed successfully (5290 jobs)` (AddScaledSearchT 27 s, FromElemFormT 56 s, FromElemVecFormT 66 s, AddScaledT 109 s, FormT6a 14 s; `CloneFormsFreshT` unchanged, replayed).
- The `#guard_msgs in #print axioms` blocks of `MemmoveProofT.total`, `AddScaledT.total` and the `Table` theorems are unchanged and pass, so each still depends on `[propext, Classical.choice, Quot.sound]` only. No `sorry`, `axiom`, `native_decide`, `maxHeartbeats` or dash added; no added line over 120 characters.

Entries:
- G1. `regs_ok` and `tlit` were the same `local macro` text in `MemmoveFwdT`, `MemmoveBwdT` (both) and `MemmoveProofT` (`regs_ok`); now one `scoped macro` each in `MoveT`, active where the three modules `open ... MoveT` (all do). Same expansion: `regs_ok` names `Regs.upd`, which already resolved to `MoveT.Regs.upd` in each module, and `tlit`'s lemma list is unchanged. `MemcpyT`'s own local macros are not touched.
- G2. `slot_addr` was the same theorem in `MemmoveFwdT` and `MemmoveBwdT` (same statement, same proof); now one in `MoveT`, which both open. Every call site (`slot_addr hx2 (by omega)`) is unchanged.
- G3. `MoveT.BInv.byte`: removed `rw [show Tactic.storeMem .b1 M x v = Tactic.storeMem .b1 M x v from rfl, ...]`'s first entry, a rewrite of a term to itself; the remaining `getMem_saved` rewrite is unchanged.
- G4. `MemmoveProofT.total`: the forward and backward branches each rebuilt the same `Fx` from `hwin0.resolve_left hn0`; now one local `hFx : (regs .x12).toNat ≠ 0 → Fx ...` before `rv_symT`, applied in both branches, the same seven fields. It is an implication, which the closer's `arithFacts` does not read (as wave 6a's D7 `True → P`).
- G5. `AddScaledT.Slots` was, word for word, `CloneFormsT.Slots` (the thirteen saved words at `top - 8` to `top - 104`, the same registers), and `AddScaledT` already imports `CloneFormsT`; now `open Rv64mc.Proof.Layout.CloneFormsT (Slots)` and the local definition deleted. `MemOk`, `slots_keep` and `saved_ok` (`simp only [saved, Slots]`) read the same proposition; neither `Slots` is in a statement outside the proof. `MemOk`'s docstring names where the slots are; the header's "Main definitions" drops `Slots`.
- G6. `AddScaledSearchT` (pc 82 and pc 296): each `rv_symT` left two branches with the same proof after a `rw [BitVec.lt_def] at hc` or `rw [BitVec.le_def] at hc`; now `all_goals` with `simp only [BitVec.lt_def, BitVec.le_def] at hc`, which rewrites each branch's `hc` by the lemma its `rw` used, then the shared proof.
- G7. `FromElemFormT.fin`, `FromElemVecFormT.fin`: the local `hw` (a word at `regs .x10 + k`, `k ≤ 16`, `k % 8 = 0`, in a window and aligned, proved by hand) replaced by `WinT`'s `InWin.dword` (for `w0`) and `InWin.dword_add` (for `w8`, `w16`), from the same `hwin : InWin env (regs .x10) 24`, `hal` and `hW`. `w8` and `w16` have the same types as before (`inWindow (regs .x10 + BitVec.ofNat 64 k) 8 = true ∧ ...`); `w0` keeps its stated type.
- G8. `FromElemFormT.fin_mem`'s `F0`: `:= by exact t` to `:= t`.

Considered, not done: `MoveT`'s `ofNat_add_toNat`, `toNat_dec`, `extractByte_zext_getByte` copy `MemcpyT`'s; using those means importing `MemcpyT`'s whole proof into `MoveT` for three short lemmas. `AddScaledT`'s four `hsrc'` blocks: a helper saves about one line net. `CloneFormsFreshT`'s two identical joins to pc 194 would need a `hygiene false` macro about as long as the code it replaces.

## Amendments, round 1

Head after this round: 1f9c1fffe5 (one commit on 9e376d575c). Skill `lean4:prove` loaded.
Check, run on 1f9c1fffe5's tree: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Layout.CloneFormsFreshT Rv64mc.Proof.Layout.FromElemFormT Rv64mc.Proof.Layout.FromElemVecFormT Rv64mc.Table.FormT6a` -> `Build completed successfully (5290 jobs)` (wall 210 s: CloneFormsFreshT 107 s, FromElemVecFormT 86 s, FromElemFormT 45 s, FormT6a 10 s; `warningAsError`, so no warnings). The `#guard_msgs in #print axioms` blocks of `CloneFormsFreshT.total`, `FromElemFormT.total`, `FromElemVecFormT.total` and `Table/FormT6a`'s theorems are unchanged and pass: `[propext, Classical.choice, Quot.sound]`. `git diff 9e376d575c 1f9c1fffe5 | grep -E '^\+.*\b(sorry|admit|axiom|native_decide|bv_decide|implemented_by|maxHeartbeats)\b' | grep -v axioms` is empty; no added line over 120 characters, no em or en dashes. Files changed: the three `Proof/Layout` modules this wave added and `notes/total-status.md`; no existing statement changes.

### R1-1 (important, spec): fixed

The finding is right: `FromElemVecFormT.PostT` gave only `VecFormT` per element and `FromElemFormT.PostT` only `FormsT`, which admit the counter-model (a `Form` with capacity `1` whose header is its own buffer; two elements sharing a buffer). 48's loop at label 740 could not discharge `AddScaledT.PreT`'s header-apart-from-buffer conjunct, nor keep the other `Form`s through `add_scaled`'s `OutT`, from them.

What changed (the three Posts are this wave's; each proof proves the strengthened statement, no weakened restatement):
- `CloneFormsFreshT.PostT := CloneFormsT.PostT ∧ FreshTermsT ∧ CapsT m m' (regs .x11) (vecPtr m' (regs .x10)) n`, `CapsT`: each clone's capacity and length are its source `Form`'s length in `m`. **This contradicts D18's claim** that "only `exit`'s `hPost` and the closing lines after its `rv_symT` differ" from `CloneFormsT`: the capacity the join stores is not in `CloneFormsT.DoneT`, so the restated parts now carry it in new invariants `OInvC := OInv ∧ CapsT .. (n - (k + 1))`, `IInvC := IInv ∧ CapsT .. j`, `TInvC := TInv ∧ CapsT .. j`. `join` takes the stored length's source (`R .x26 = vecLen m (src + 24 j)`, given at its four callers from `IInv`'s `R .x26 = vecLen m a` or `outer`'s `ag16`) and adds the new clone by `CapsT.join` (the code's `hnew`: the capacity equals the length, or both are `0`); every memory change keeps `CapsT` by the same header agreement `DoneT.keep` already uses (`CapsT.keep`), and `after`'s seven stores by `CapsT.setMem` (stack slots above the heap, term stores at or above `H ≥ D + 24 n`). `exit` gives the new conjunct from `hdr3`'s agreement apart from `sret`. `SpecT.weaken` is unchanged (`hp.1`).
- `FromElemFormT.PostT` adds `vecCap m' P = 0`, `vecCap m' (P + 24) = 0`, `vecCap m' (P + 48) = vecCap m (regs .x11)` (`P` the result's buffer): the two stored `(0, 8, 0)` `Form`s and the moved element. I did not narrow `PreT` to `vecCap = 0`; at 48's one call site the element is `(0, 8, 0)` (labels 415 to 417), so all three are `0` there.
- `FromElemVecFormT.PostT`'s last conjunct is now `ElemsT env (EmptyFormsT m (regs .x11)) m' P n`: each element `VecFormT` and its buffer (unless empty) `Apart` from `[P, P + 24 n)`; every two elements' buffers apart (`BufApart`, each unless empty, `PairT.Apart` as `AddScaledT.PreT` uses it); and, if the element's `Form`s all have capacity `0` (`EmptyFormsT m a1`), every element's do. Proof: `DoneV` gains the pairwise part and the `E →` part (`E` a parameter). `step_mem`: clone `j`'s buffer is fresh (`ClonePostT`: at or above `NEXT` before the call) and the earlier ones lie below it (`FootV` with `H = NEXT`), so `ptr_i + 24 len_i ≤ ptr_j`; its `Form`s' capacities are the element's `Form`s' lengths (`CapsT`), and `loop` derives (`hEsrc`) that those lengths are `0` when the capacities are (`VecT`'s `len ≤ cap`, read below `NEXT` at the entry). `move_mem`: the moved element's buffer lies below `NEXT` at the entry `≤ D`, the clones' at or above `D + 24 n` (`FootV`'s lower bound), so it is apart from both; its `Form`s are the entry's, kept below `NEXT` (`hbelow`). `Res` carries `ElemsT`; `fin_mem` keeps it through the stores at `sret` (`ElemsT.keep_below`).

What 48 uses at 740 (recorded in `notes/total-status.md`'s 163 obligation, and the 159, 160 and `CloneFormsFreshT` bullets updated): the element `from_elem::<Form>` returns has three `Form`s of capacity `0`, so `EmptyFormsT m (sp + 0x2b0)` holds at label 427 and every `Form` of every element of the result starts with capacity `0`; `AddScaledT.PreT`'s `vecCap = 0 ∨ Apart self 24 ...` holds by the first disjunct until a call grows that `Form`, and after by `KeptOrFresh`; distinct `Form`s are distinct 24-byte slots of pairwise apart buffers, apart from the result's block, so `OutT` (the header and the buffer at the entry, `40 cap` bytes) misses the others. Still argued, not proved: 48 is not total; its proof discharges it.

Not given, and why: `ElemsT` says nothing about the terms' blocks of `Form`s that are not empty (the moved element's `Form`s' blocks against its own buffer would need a new `PreT` conjunct on the element); with the element empty, as at the one call site, there are none.

Evidence: the build above; `FromElemVecFormT.total : SpecT env p i need` with `PostT` as stated (`#print axioms` pinned); the counter-model is excluded: under `EmptyFormsT`, every `Form`'s capacity is `0`, and two elements of nonzero length sharing a buffer contradict `BufApart`.

### R1-2 (nit, claim-not-in-code): fixed here

The header line of the defence (line 3) names 2d23011d83, the head after pass 3; the head the review saw was the golf commit 9e376d575c (named only in "## Golf"). The lifecycle forbids editing earlier entries, so the correction is this line: the head reviewed in round 1 was 9e376d575c, and the head after this round is 1f9c1fffe5.

### R1-3 (nit, quality): deferred to the merge

The brief leaves `notes/total-status.md`'s summary counts to the merge, and other waves edit the same table, so a recount here would conflict there. For the merge, the counts this branch's table gives (`awk` commands of the note's own line 18, run on 1f9c1fffe5): total with a `Table` instance 140 functions, 7140 instructions (34.2% of 20878); no open hypothesis 49, 1807; only environment facts open 140, 7140 (228's `MemmoveSpecT (225)` hypothesis is gone); stated, not proved 0; no total contract 89, 13738; reachable 229, 20878. The difference from the base's row: 225, 163, 159, 160 total (136 + 4), 225 and 228 with no open hypothesis (47 + 2).

## Amendments, round 2

- **R2-1 (fixed, 148f68d167).** The reviewer is right: `ElemsT`'s first part and `BufApart` each have a `vecLen = 0` disjunct, so the separations hold only for non-empty buffers. Added "each unless empty" to `FromElemVecFormT`'s module doc and `PostT`'s docstring (the module doc's paragraph reflowed, no line over 120), and "unless empty" to `notes/total-status.md`'s row 160, its 160 obligation (the `ElemsT` parenthesis) and, for the same reason, the `add_scaled` obligation's sentence on 48's loop at label 740 (`BufApart`, `ElemsT`'s first part). Docstrings and notes only; no definition or statement changes. This corrects the wording of Pass 3 and round 1's descriptions of `ElemsT`/`PostT`, which left out the qualifier; the argument at label 740 is unaffected, since an empty element has no `Form` header to write through.
- **R2-2 (fixed, in this entry).** Round 1's Check paragraph said "no added line over 120 characters"; that holds only for the Lean files. `notes/total-status.md`'s Markdown prose is not hard-wrapped, so its added lines run longer, as the project's writing conventions require. Corrected claim: no added Lean line over 120 characters (`git diff 9e5e456cca 148f68d167 -- '*.lean' | grep '^+' | grep -v '^+++' | awk 'length > 121' | wc -l` gives `0`).

Check, run on 148f68d167's tree: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Layout.FromElemVecFormT Rv64mc.Table.FormT6a` -> `Build completed successfully (5290 jobs)` (wall 70 s; `FromElemVecFormT` 56 s, `FormT6a` 9.2 s). No em or en dashes in the two changed files.
