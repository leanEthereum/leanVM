/-
  LeanVM.Guest.B1.Whir.Data22

  `open_stacked__L22` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 22

`osData_22 : OsData 22`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_22_0 : stmtsEqb ((Data.core324.body.drop 0).take 1100)
    (((osBody (osCfg 22)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_22_1 : stmtsEqb ((Data.core324.body.drop 1100).take 1100)
    (((osBody (osCfg 22)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_22_2 : stmtsEqb ((Data.core324.body.drop 2200).take 1100)
    (((osBody (osCfg 22)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_22_0 : FnIs ((osCfg 22).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 22 0) ((osCfg 22).sqLoop 0)) ∧
    FnIs ((osCfg 22).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 22 0) ((osCfg 22).resLoop 0)) :=
  ⟨⟨Data.core721, Program.find?_of_indexOf? (j := 721) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core726, Program.find?_of_indexOf? (j := 726) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_22_1 : FnIs ((osCfg 22).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 22 1) ((osCfg 22).sqLoop 1)) ∧
    FnIs ((osCfg 22).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 22 1) ((osCfg 22).resLoop 1)) :=
  ⟨⟨Data.core723, Program.find?_of_indexOf? (j := 723) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core727, Program.find?_of_indexOf? (j := 727) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_22_2 : FnIs ((osCfg 22).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 22 2) ((osCfg 22).sqLoop 2)) ∧
    FnIs ((osCfg 22).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 22 2) ((osCfg 22).resLoop 2)) :=
  ⟨⟨Data.core724, Program.find?_of_indexOf? (j := 724) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core728, Program.find?_of_indexOf? (j := 728) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_22_3 : FnIs ((osCfg 22).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 22 3) ((osCfg 22).sqLoop 3)) ∧
    FnIs ((osCfg 22).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 22 3) ((osCfg 22).resLoop 3)) :=
  ⟨⟨Data.core725, Program.find?_of_indexOf? (j := 725) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core729, Program.find?_of_indexOf? (j := 729) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_22 : OsData 22 := by
  have hl : (osCfg 22).levels.length = 4 := by decide +kernel
  have hb : Data.core324.body.drop 0 = (osBody (osCfg 22)).drop 0 :=
    run_step 1100 0 os_run_22_0 <|
    run_step 1100 1100 os_run_22_1 <|
    run_step 1100 2200 os_run_22_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core324, Program.find?_of_indexOf? (j := 324) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_22_0
  · exact osLv_22_1
  · exact osLv_22_2
  · exact osLv_22_3

end
end LeanVM.Guest.B1.Whir
