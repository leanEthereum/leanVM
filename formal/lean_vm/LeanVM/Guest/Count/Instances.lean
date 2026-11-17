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

/-- A certificate of `128` iterations from the first, constant per iteration. -/
def cert128B : Cert → Bool
  | .loop endc pre b _ => endc == some 128 && pre.isEmpty && b.cs.isEmpty
  | _ => false

/-- **A blob's cell loop's words** from its first cell. -/
theorem cell_le : TotalLeOn coreProgram B2C.fs name% «da_verify_blob_loop0» (fun a => a.getD 0 0 = 1)
    (fun _ => B1.Da.cellB B2C.fs wSK) := by
  have hn : (coreProgram[idx% «da_verify_blob_loop0»]?).map Fn.name = some name% «da_verify_blob_loop0» := by
    decide +kernel
  have hb : cert128B (Data.wcertJ idx% «da_verify_blob_loop0») = true := by decide +kernel
  have hc := wcertOf_of_idx hn
  rcases hw : Data.wcertJ idx% «da_verify_blob_loop0» with _ | _ | ⟨endc, pre, ⟨K, cs⟩, ks⟩
  · rw [hw] at hb; cases hb
  · rw [hw] at hb; cases hb
  · rw [hw] at hb
    simp only [cert128B, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hb
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hb
    have hf : wcertOf name% «da_verify_blob_loop0» = .loop (some 128) [] ⟨K, []⟩ ks := hc.trans hw
    have hk : B1.Main.iterK B2C.fs wSK name% «da_verify_blob_loop0» = K := by
      unfold B1.Main.iterK; simp only [wSK, hf]; omega
    intro rd t args rets hnm ha hv hbo
    have := fs_total_le_of_loop hf hnm hv hbo (a := 0) (e := 128)
      (by rw [ha, ← LeanVM.Guest.Value.gen_pow_eq_ofK, pow_zero]) rfl (by norm_num) (by norm_num)
      (fun _ h => (List.not_mem_nil h).elim)
    unfold B1.Da.cellB
    rw [hk]
    simpa [Aff.eval] using this

theorem blob_le : B2C.fs name% «da_verify_loop0» + (B2C.fs "da_verify_blob" + 641 +
    (B1.Da.cellB B2C.fs wSK + wSB "da_levels__L128_L7")) ≤
      B1.Main.iterK B2C.fs wSK name% «da_verify_loop0» := by
  unfold B1.Da.cellB B1.Main.iterK
  decide +kernel

theorem ws_le : B2C.fs "da_weights" + 128 + 128 * B2C.fs "da_expand__L6_L7" ≤ wSB "da_weights" := by
  decide +kernel

/-- **`da_verify`'s static bounds**, at the deployed frame sizes. -/
theorem dvStatic : B1.Da.DvStaticB B2C.fs wSB wSK where
  pad := iterK_totalLeOn (j := idx% da_pad_loop0) (by decide +kernel)
  cell := cell_le
  blob := blob_le
  off := fun _ hb => iterK_totalLeOn (all_range_get offLoops_ok hb)
  dl := wSB_totalLe dlTop_ok
  dl7 := wSB_totalLe (j := wIdx "da_levels__L128_L7") (by decide +kernel)
  vec := vec_le
  exp := exp_le
  ws := ws_le

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
