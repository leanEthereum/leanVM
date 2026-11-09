/-
  LeanVM.Guest.B1.Whir.Data16

  `open_stacked__L16` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 16

`osData_16 : OsData 16`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_16_0 : stmtsEqb ((Data.core318.body.drop 0).take 1100)
    (((osBody (osCfg 16)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_16_1 : stmtsEqb ((Data.core318.body.drop 1100).take 1100)
    (((osBody (osCfg 16)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_16_2 : stmtsEqb ((Data.core318.body.drop 2200).take 1100)
    (((osBody (osCfg 16)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_16_0 : FnIs ((osCfg 16).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 16 0) ((osCfg 16).sqLoop 0)) ∧
    FnIs ((osCfg 16).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 16 0) ((osCfg 16).resLoop 0)) :=
  ⟨⟨Data.core652, Program.find?_of_indexOf? (j := 652) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core658, Program.find?_of_indexOf? (j := 658) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_16_1 : FnIs ((osCfg 16).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 16 1) ((osCfg 16).sqLoop 1)) ∧
    FnIs ((osCfg 16).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 16 1) ((osCfg 16).resLoop 1)) :=
  ⟨⟨Data.core654, Program.find?_of_indexOf? (j := 654) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core659, Program.find?_of_indexOf? (j := 659) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_16_2 : FnIs ((osCfg 16).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 16 2) ((osCfg 16).sqLoop 2)) ∧
    FnIs ((osCfg 16).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 16 2) ((osCfg 16).resLoop 2)) :=
  ⟨⟨Data.core655, Program.find?_of_indexOf? (j := 655) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core660, Program.find?_of_indexOf? (j := 660) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_16_3 : FnIs ((osCfg 16).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 16 3) ((osCfg 16).sqLoop 3)) ∧
    FnIs ((osCfg 16).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 16 3) ((osCfg 16).resLoop 3)) :=
  ⟨⟨Data.core656, Program.find?_of_indexOf? (j := 656) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core661, Program.find?_of_indexOf? (j := 661) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_16_4 : FnIs ((osCfg 16).sqLoop 4) (osParams 6)
      (sqLoopBody (osLv 16 4) ((osCfg 16).sqLoop 4)) ∧
    FnIs ((osCfg 16).resLoop 4) (osParams 6)
      (resLoopBody 4 (osLv 16 4) ((osCfg 16).resLoop 4)) :=
  ⟨⟨Data.core657, Program.find?_of_indexOf? (j := 657) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core662, Program.find?_of_indexOf? (j := 662) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_16 : OsData 16 := by
  have hl : (osCfg 16).levels.length = 5 := by decide +kernel
  have hb : Data.core318.body.drop 0 = (osBody (osCfg 16)).drop 0 :=
    run_step 1100 0 os_run_16_0 <|
    run_step 1100 1100 os_run_16_1 <|
    run_step 1100 2200 os_run_16_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core318, Program.find?_of_indexOf? (j := 318) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_16_0
  · exact osLv_16_1
  · exact osLv_16_2
  · exact osLv_16_3
  · exact osLv_16_4

end
end LeanVM.Guest.B1.Whir
