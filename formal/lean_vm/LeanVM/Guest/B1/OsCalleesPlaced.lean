/-
  LeanVM.Guest.B1.OsCalleesPlaced

  `open_stacked`'s callees from group 1, placed: `OsCalleesAt` under the certificate facts.
-/

module

public import LeanVM.Guest.B1.Whir.OsCallees
public import LeanVM.Guest.B1.PurePlaced
public import LeanVM.Guest.B1.GrindPlaced
public import LeanVM.Guest.B1.OodPlaced
public import LeanVM.Guest.B1.QueryBitsPlaced

/-!
# `open_stacked`'s callees from group 1, placed

`osCalleesAt`: every field of g4's `OsCalleesAt` (`Whir/OsCallees.lean`), from group 1's placed
forms, given the certificate facts `G1Certs` of the two frame runs.
-/

namespace LeanVM.Guest.B1

open LeanVM.Guest.Core

@[expose] public section

/-- **`open_stacked`'s callees from group 1 are complete, placed.** -/
theorem osCalleesAt (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (hc : G1Certs fs cert) :
    OsCalleesAt fs cert k where
  fold := opening_fold_completeRel fs cert k
  canonical := assert_canonical_completeRel fs cert k
  ood := opening_ood_point_completeRel fs cert k
  grind := grind_check_completeRel fs cert k hc.grind
  finalMsg4 := ofm_L4_completeMem fs cert k
  finalMsg8 := ofm_L8_completeMem fs cert k
  finalMsg16 := ofm_L16_completeMem fs cert k
  finalMsg32 := ofm_L32_completeMem fs cert k
  rowWeights4 := orw_L4_L0_completeMem fs cert k
  rowWeights6 := orw_L6_L1_completeMem fs cert k
  foldFinal2 := ffm_L2_completeMem fs cert k
  foldFinal3 := ffm_L3_completeMem fs cert k
  foldFinal4 := ffm_L4_completeMem fs cert k
  foldFinal5 := ffm_L5_completeMem fs cert k
  decode := by
    intro p hp
    simp only [osDqNames, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact dq_completeAt_L14 fs cert k (hc.decode 14 (by decide) (by decide))
    · exact dq_completeAt_L15 fs cert k (hc.decode 15 (by decide) (by decide))
    · exact dq_completeAt_L16 fs cert k (hc.decode 16 (by decide) (by decide))
    · exact dq_completeAt_L17 fs cert k (hc.decode 17 (by decide) (by decide))
    · exact dq_completeAt_L18 fs cert k (hc.decode 18 (by decide) (by decide))
    · exact dq_completeAt_L19 fs cert k (hc.decode 19 (by decide) (by decide))
    · exact dq_completeAt_L20 fs cert k (hc.decode 20 (by decide) (by decide))
    · exact dq_completeAt_L21 fs cert k (hc.decode 21 (by decide) (by decide))
    · exact dq_completeAt_L22 fs cert k (hc.decode 22 (by decide) (by decide))
    · exact dq_completeAt_L23 fs cert k (hc.decode 23 (by decide) (by decide))
    · exact dq_completeAt_L24 fs cert k (hc.decode 24 (by decide) (by decide))
    · exact dq_completeAt_L25 fs cert k (hc.decode 25 (by decide) (by decide))
    · exact dq_completeAt_L26 fs cert k (hc.decode 26 (by decide) (by decide))

end
end LeanVM.Guest.B1
