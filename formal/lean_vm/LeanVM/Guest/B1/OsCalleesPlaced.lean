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

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory

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

/-- **`open_stacked`'s callees from group 1 are complete, placed, on disjoint layouts.** -/
theorem osCalleesAtD (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (hc : G1Certs fs cert) :
    OsCalleesAtD fs cert k where
  fold := opening_fold_completeRelD fs cert k
  canonical := assert_canonical_completeRelD fs cert k
  ood := opening_ood_point_completeRelD fs cert k
  grind := grind_check_completeRelD fs cert k hc.grind
  finalMsg4 := ofm_L4_completeMemD fs cert k
  finalMsg8 := ofm_L8_completeMemD fs cert k
  finalMsg16 := ofm_L16_completeMemD fs cert k
  finalMsg32 := ofm_L32_completeMemD fs cert k
  rowWeights4 := orw_L4_L0_completeMemD fs cert k
  rowWeights6 := orw_L6_L1_completeMemD fs cert k
  foldFinal2 := ffm_L2_completeMemD fs cert k
  foldFinal3 := ffm_L3_completeMemD fs cert k
  foldFinal4 := ffm_L4_completeMemD fs cert k
  foldFinal5 := ffm_L5_completeMemD fs cert k
  decode := by
    intro p hp
    simp only [osDqNames, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact dq_completeAt_L14D fs cert k (hc.decode 14 (by decide) (by decide))
    · exact dq_completeAt_L15D fs cert k (hc.decode 15 (by decide) (by decide))
    · exact dq_completeAt_L16D fs cert k (hc.decode 16 (by decide) (by decide))
    · exact dq_completeAt_L17D fs cert k (hc.decode 17 (by decide) (by decide))
    · exact dq_completeAt_L18D fs cert k (hc.decode 18 (by decide) (by decide))
    · exact dq_completeAt_L19D fs cert k (hc.decode 19 (by decide) (by decide))
    · exact dq_completeAt_L20D fs cert k (hc.decode 20 (by decide) (by decide))
    · exact dq_completeAt_L21D fs cert k (hc.decode 21 (by decide) (by decide))
    · exact dq_completeAt_L22D fs cert k (hc.decode 22 (by decide) (by decide))
    · exact dq_completeAt_L23D fs cert k (hc.decode 23 (by decide) (by decide))
    · exact dq_completeAt_L24D fs cert k (hc.decode 24 (by decide) (by decide))
    · exact dq_completeAt_L25D fs cert k (hc.decode 25 (by decide) (by decide))
    · exact dq_completeAt_L26D fs cert k (hc.decode 26 (by decide) (by decide))


/-- **The tree-size facts of group 1's pure callees**, for the static size tool: each function's bound
on every valid tree, by its arguments (a loop's by its trip count). -/
structure G1Bounds (fs : String → ℕ) : Type where
  foldB : List E → ℕ
  fold : LeanVM.Guest.Memory.TotalLe coreProgram fs "opening_fold" foldB
  canonicalB : List E → ℕ
  canonical : LeanVM.Guest.Memory.TotalLe coreProgram fs "assert_canonical" canonicalB
  loop6B : E → ℕ
  loop6 : LeanVM.Guest.Memory.TotalLeOn coreProgram fs "__loop6" LeanVM.Guest.Memory.LoopPre
    fun a => loop6B (a.getD 1 0)
  loop9B : E → ℕ
  loop9 : LeanVM.Guest.Memory.TotalLeOn coreProgram fs "__loop9" LeanVM.Guest.Memory.LoopPre
    fun a => loop9B (a.getD 1 0)
  finalMsg4B : List E → ℕ
  finalMsg4 : LeanVM.Guest.Memory.TotalLe coreProgram fs "opening_final_message__L4" finalMsg4B
  finalMsg8B : List E → ℕ
  finalMsg8 : LeanVM.Guest.Memory.TotalLe coreProgram fs "opening_final_message__L8" finalMsg8B
  finalMsg16B : List E → ℕ
  finalMsg16 : LeanVM.Guest.Memory.TotalLe coreProgram fs "opening_final_message__L16" finalMsg16B
  finalMsg32B : List E → ℕ
  finalMsg32 : LeanVM.Guest.Memory.TotalLe coreProgram fs "opening_final_message__L32" finalMsg32B
  rowWeights4B : List E → ℕ
  rowWeights4 : LeanVM.Guest.Memory.TotalLe coreProgram fs "opening_row_weights__L4_L0" rowWeights4B
  rowWeights6B : List E → ℕ
  rowWeights6 : LeanVM.Guest.Memory.TotalLe coreProgram fs "opening_row_weights__L6_L1" rowWeights6B
  foldFinal2B : List E → ℕ
  foldFinal2 : LeanVM.Guest.Memory.TotalLe coreProgram fs "fold_final_msg__L2" foldFinal2B
  foldFinal3B : List E → ℕ
  foldFinal3 : LeanVM.Guest.Memory.TotalLe coreProgram fs "fold_final_msg__L3" foldFinal3B
  foldFinal4B : List E → ℕ
  foldFinal4 : LeanVM.Guest.Memory.TotalLe coreProgram fs "fold_final_msg__L4" foldFinal4B
  foldFinal5B : List E → ℕ
  foldFinal5 : LeanVM.Guest.Memory.TotalLe coreProgram fs "fold_final_msg__L5" foldFinal5B

/-- **`open_stacked`'s callees from group 1 are complete by bounded trees**, given the pure callees'
tree sizes. -/
noncomputable def osCalleesAtB (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (hc : G1Certs fs cert)
    (bd : G1Bounds fs) : OsCalleesAtB fs cert k where
  foldB := bd.foldB
  fold := opening_fold_completeRelB fs cert k bd.foldB bd.fold
  canonicalB := bd.canonicalB
  canonical := assert_canonical_completeRelB fs cert k bd.canonicalB bd.canonical
  oodB := fun args => fs "opening_ood_point" + (2 * logG (args.getD 3 0) + 2) +
    max (bd.loop9B (args.getD 3 0)) (fs "__loop9")
  ood := opening_ood_point_completeRelB fs cert k bd.loop9B bd.loop9
  grindB := fun args => fs "grind_check" + max (bd.loop6B (args.getD 3 0)) (fs "__loop6")
  grind := grind_check_completeRelB fs cert k hc.grind bd.loop6B bd.loop6
  finalMsg4B := bd.finalMsg4B
  finalMsg4 := ofm_L4_completeMemB fs cert k bd.finalMsg4B bd.finalMsg4
  finalMsg8B := bd.finalMsg8B
  finalMsg8 := ofm_L8_completeMemB fs cert k bd.finalMsg8B bd.finalMsg8
  finalMsg16B := bd.finalMsg16B
  finalMsg16 := ofm_L16_completeMemB fs cert k bd.finalMsg16B bd.finalMsg16
  finalMsg32B := bd.finalMsg32B
  finalMsg32 := ofm_L32_completeMemB fs cert k bd.finalMsg32B bd.finalMsg32
  rowWeights4B := bd.rowWeights4B
  rowWeights4 := orw_L4_L0_completeMemB fs cert k bd.rowWeights4B bd.rowWeights4
  rowWeights6B := bd.rowWeights6B
  rowWeights6 := orw_L6_L1_completeMemB fs cert k bd.rowWeights6B bd.rowWeights6
  foldFinal2B := bd.foldFinal2B
  foldFinal2 := ffm_L2_completeMemB fs cert k bd.foldFinal2B bd.foldFinal2
  foldFinal3B := bd.foldFinal3B
  foldFinal3 := ffm_L3_completeMemB fs cert k bd.foldFinal3B bd.foldFinal3
  foldFinal4B := bd.foldFinal4B
  foldFinal4 := ffm_L4_completeMemB fs cert k bd.foldFinal4B bd.foldFinal4
  foldFinal5B := bd.foldFinal5B
  foldFinal5 := ffm_L5_completeMemB fs cert k bd.foldFinal5B bd.foldFinal5
  decode := (osCalleesAtD fs cert k hc).decode

end
end LeanVM.Guest.B1
