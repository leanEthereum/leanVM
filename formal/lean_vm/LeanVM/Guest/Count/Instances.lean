/-
  LeanVM.Guest.Count.Instances

  The budget's static hypotheses at the deployed frame sizes, from the certificate families: the
  words of `main`'s statically bounded callees and of its non-static callees' static callees
  (`mainStatics`). `main`'s callees' instruction counts (`mainCounts`) are `Budget/MvCount`'s;
  `open_stacked`'s callees' words (`osLeafBounds`) are `Count/VsOsAll`'s.
-/

module

public import LeanVM.Guest.Count.Words
public import LeanVM.Guest.Budget.MainCount
public import LeanVM.Guest.B1.Main.MainHonestBudgetB

/-!
# The budget's static hypotheses

Words at `B2C.fs` by name (`Count.Words`): `wSB f`, `f`'s constant, and `wSK f`, a loop helper's
words per iteration with its run's phantom frame, which every call site of `main`'s side charges
once (`iterK_totalLeOn`), each function found by `wIdx` (`wIdxL` for `__loop{n}`) and checked by
`decide +kernel`.
-/

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

/-- **A loop helper's run at `B2C.fs`**: `B1.Main.iterK` (`wSKt`) words per iteration and its
phantom frame once. -/
theorem iterK_totalLeOn {j : ℕ} {f : String} (h : wOkK j f = true) :
    TotalLeOn coreProgram B2C.fs f LoopPre
      fun a => logG (a.getD 1 0) * B1.Main.iterK B2C.fs wSK f + B2C.fs f := by
  unfold B1.Main.iterK
  rw [← wSKt_eq]
  exact wSKt_totalLeOn h

/-- **`main`'s statically bounded callees' words.** -/
theorem mainStaticsMain : B1.Main.MainStaticsMain B2C.fs wSB wSK where
  l1 := iterK_totalLeOn (j := wIdxL 0) (by decide +kernel)
  l2 := iterK_totalLeOn (j := wIdxL 1) (by decide +kernel)
  l3 := iterK_totalLeOn (j := wIdxL 2) (by decide +kernel)
  l4 := iterK_totalLeOn (j := wIdxL 3) (by decide +kernel)
  st := wSB_totalLe (j := wIdx "statement_digest") (by decide +kernel)

/-- `da_levels__L{2^k}_L{k}`, `k ≤ 10`, checked. -/
theorem dlNames_ok : (List.range 11).all (fun k => wOkB (wIdx B1.Da.dlNames[k]!) B1.Da.dlNames[k]!) = true := by
  decide +kernel

/-- The column offsets' doubling loops `__loop{26 + b}`, checked. -/
theorem offLoops_ok :
    (List.range 7).all (fun b => wOkK (wIdxL (26 + b)) (B1.Da.offLoopName b)) = true := by
  decide +kernel

/-- **`da_vector`'s words within its static bound**: its frame and buffers, its callees' frames
and buffers, the doublings' iterations and their runs' phantom frames. -/
theorem vec_le : B2C.fs "da_vector" + 30 + (B2C.fs "da_factors__L14_L7_L0" + 256 +
    (B2C.fs "da_expand__L14_L7" + (B2C.fs "da_factors__L7_L8_L128" + 256 +
      (B2C.fs "da_column_offsets" + 1080 +
        ((List.range 7).map fun b => 2 ^ b * B1.Main.iterK B2C.fs wSK (B1.Da.offLoopName b) +
          B2C.fs (B1.Da.offLoopName b)).sum + 0)))) ≤
    wSB "da_vector" := by
  unfold B1.Main.iterK
  decide +kernel

theorem exp_le : B2C.fs "da_expand__L7_L8" ≤ wSB "da_expand__L7_L8" := by decide +kernel

/-- **`da_verify`'s static bounds**, at the deployed frame sizes. -/
theorem dvStatic : B1.Da.DvStaticB B2C.fs wSB wSK where
  l17 := iterK_totalLeOn (j := wIdxL 21) (by decide +kernel)
  l19 := iterK_totalLeOn (j := wIdxL 23) (by decide +kernel)
  l20 := iterK_totalLeOn (j := wIdxL 24) (by decide +kernel)
  l21 := iterK_totalLeOn (j := wIdxL 25) (by decide +kernel)
  off := fun _ hb => iterK_totalLeOn (all_range_get offLoops_ok hb)
  dl := fun _ hk => wSB_totalLe (all_range_get dlNames_ok (Nat.lt_succ_of_le hk))
  vec := vec_le
  exp := exp_le

/-- `claim_list_last__L{k}`, `k < 17`, checked. -/
theorem clNames_ok :
    (List.range 17).all (fun k => wOkB (wIdx B1.Digest.clNames[k]!) B1.Digest.clNames[k]!) = true := by
  decide +kernel

/-- **The words of the static callees of `main`'s non-static callees**, at `B2C.fs`. -/
theorem mainStatics : B1.Main.MainStatics B2C.fs wSB wSK where
  main := mainStaticsMain
  dv := dvStatic
  ls := wSB_totalLe (j := wIdx "list_split") (by decide +kernel)
  l15 := iterK_totalLeOn (j := wIdxL 15) (by decide +kernel)
  l16 := iterK_totalLeOn (j := wIdxL 16) (by decide +kernel)
  cl := fun _ hk => wSB_totalLe (all_range_get clNames_ok hk)
  l25 := iterK_totalLeOn (j := wIdxL 33) (by decide +kernel)
  l26 := iterK_totalLeOn (j := wIdxL 34) (by decide +kernel)
  l27 := iterK_totalLeOn (j := wIdxL 35) (by decide +kernel)
  bs := wSB_totalLe (j := wIdx "batch_sumcheck__L23") (by decide +kernel)
  gr := wSB_totalLe (j := wIdx "grind_check__L2") (by decide +kernel)

end
end LeanVM.Guest.Count
