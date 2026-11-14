/-
  LeanVM.Guest.Count.Instances

  The budget's static hypotheses at the deployed frame sizes, from the certificate families: the
  words of `main`'s statically bounded callees and of its non-static callees' static callees
  (`mainStatics`). `main`'s callees' instruction counts (`mainCounts`) are `Budget/MvCount`'s;
  `open_stacked`'s callees' words (`osLeafBounds`) are `Count/VsOsAll`'s.
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Count.Words
public import LeanVM.Guest.Budget.MainCount
public import LeanVM.Guest.B1.Main.MainHonestBudgetB
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Source

/-!
# The budget's static hypotheses

Words at `B2C.fs` by name (`Count.Words`): `wSB f`, `f`'s constant, and `wSK f`, a loop helper's
words per iteration with its run's phantom frame, which every call site of `main`'s side charges
once (`iterK_totalLeOn`), each function found by `wIdx` (a loop helper by `idx%`) and checked by
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
  l1 := iterK_totalLeOn (j := idx% main_loop0) (by decide +kernel)
  l2 := iterK_totalLeOn (j := idx% main_loop1) (by decide +kernel)
  l3 := iterK_totalLeOn (j := idx% main_loop2) (by decide +kernel)
  l4 := iterK_totalLeOn (j := idx% main_loop3) (by decide +kernel)
  st := wSB_totalLe (j := wIdx "statement_digest") (by decide +kernel)

/-- The tree over the blob roots, `da_levels__L32_L5`, checked. -/
theorem dlTop_ok : wOkB (wIdx B1.Da.dlTop) B1.Da.dlTop = true := by
  decide +kernel

/-- The column offsets' doubling loops `da_column_offsets_loop{b}`, checked. -/
theorem offLoops_ok :
    (List.range 7).all (fun b => wOkK (idx% da_column_offsets_loop0 + b) (B1.Da.offLoopName b)) = true := by
  decide +kernel

/-- **`da_vector`'s words within its static bound**: its frame and buffers, its callees' frames
and buffers, the doublings' iterations and their runs' phantom frames. -/
theorem vec_le : B2C.fs "da_vector" + 28 + (B2C.fs "da_factors__L13_L7_L0" + 128 +
    (B2C.fs "da_expand__L13_L7" + (B2C.fs "da_factors__L6_L7_L128" + 128 +
      (B2C.fs "da_column_offsets" + 945 +
        ((List.range 7).map fun b => 2 ^ b * B1.Main.iterK B2C.fs wSK (B1.Da.offLoopName b) +
          B2C.fs (B1.Da.offLoopName b)).sum + 0)))) ≤
    wSB "da_vector" := by
  unfold B1.Main.iterK
  decide +kernel

theorem exp_le : B2C.fs "da_expand__L6_L7" ≤ wSB "da_expand__L6_L7" := by decide +kernel

/-- **`da_verify`'s static bounds**, at the deployed frame sizes. -/
theorem dvStatic : B1.Da.DvStaticB B2C.fs wSB wSK where
  l17 := iterK_totalLeOn (j := idx% da_verify_loop0) (by decide +kernel)
  l19 := iterK_totalLeOn (j := idx% da_verify_loop2) (by decide +kernel)
  l20 := iterK_totalLeOn (j := idx% da_verify_loop3) (by decide +kernel)
  l21 := iterK_totalLeOn (j := idx% da_verify_column_loop0) (by decide +kernel)
  off := fun _ hb => iterK_totalLeOn (all_range_get offLoops_ok hb)
  dl := wSB_totalLe dlTop_ok
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
  l15 := iterK_totalLeOn (j := idx% claim_list_digest_loop0) (by decide +kernel)
  l16 := iterK_totalLeOn (j := idx% claim_list_digest_loop1) (by decide +kernel)
  cl := fun _ hk => wSB_totalLe (all_range_get clNames_ok hk)
  l25 := iterK_totalLeOn (j := idx% aggregate_claims_loop0) (by decide +kernel)
  l26 := iterK_totalLeOn (j := idx% aggregate_claims_loop1) (by decide +kernel)
  l27 := iterK_totalLeOn (j := idx% aggregate_claims_loop2) (by decide +kernel)
  bs := wSB_totalLe (j := wIdx "batch_sumcheck__L23") (by decide +kernel)
  gr := wSB_totalLe (j := wIdx "grind_check__L2") (by decide +kernel)

end
end LeanVM.Guest.Count
