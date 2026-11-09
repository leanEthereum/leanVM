/-
  LeanVM.Guest.B1.Whir.Data17

  `open_stacked__L17` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 17

`osData_17 : OsData 17`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_17_0 : stmtsEqb ((Data.core319.body.drop 0).take 1100)
    (((osBody (osCfg 17)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_17_1 : stmtsEqb ((Data.core319.body.drop 1100).take 1100)
    (((osBody (osCfg 17)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_17_2 : stmtsEqb ((Data.core319.body.drop 2200).take 1100)
    (((osBody (osCfg 17)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_17_3 : stmtsEqb ((Data.core319.body.drop 3300).take 1100)
    (((osBody (osCfg 17)).drop 3300).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_17_0 : FnIs ((osCfg 17).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 17 0) ((osCfg 17).sqLoop 0)) ∧
    FnIs ((osCfg 17).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 17 0) ((osCfg 17).resLoop 0)) :=
  ⟨⟨Data.core663, Program.find?_of_indexOf? (j := 663) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core669, Program.find?_of_indexOf? (j := 669) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_17_1 : FnIs ((osCfg 17).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 17 1) ((osCfg 17).sqLoop 1)) ∧
    FnIs ((osCfg 17).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 17 1) ((osCfg 17).resLoop 1)) :=
  ⟨⟨Data.core665, Program.find?_of_indexOf? (j := 665) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core670, Program.find?_of_indexOf? (j := 670) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_17_2 : FnIs ((osCfg 17).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 17 2) ((osCfg 17).sqLoop 2)) ∧
    FnIs ((osCfg 17).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 17 2) ((osCfg 17).resLoop 2)) :=
  ⟨⟨Data.core666, Program.find?_of_indexOf? (j := 666) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core671, Program.find?_of_indexOf? (j := 671) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_17_3 : FnIs ((osCfg 17).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 17 3) ((osCfg 17).sqLoop 3)) ∧
    FnIs ((osCfg 17).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 17 3) ((osCfg 17).resLoop 3)) :=
  ⟨⟨Data.core667, Program.find?_of_indexOf? (j := 667) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core672, Program.find?_of_indexOf? (j := 672) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_17_4 : FnIs ((osCfg 17).sqLoop 4) (osParams 6)
      (sqLoopBody (osLv 17 4) ((osCfg 17).sqLoop 4)) ∧
    FnIs ((osCfg 17).resLoop 4) (osParams 6)
      (resLoopBody 4 (osLv 17 4) ((osCfg 17).resLoop 4)) :=
  ⟨⟨Data.core668, Program.find?_of_indexOf? (j := 668) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core673, Program.find?_of_indexOf? (j := 673) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_17 : OsData 17 := by
  have hl : (osCfg 17).levels.length = 5 := by decide +kernel
  have hb : Data.core319.body.drop 0 = (osBody (osCfg 17)).drop 0 :=
    run_step 1100 0 os_run_17_0 <|
    run_step 1100 1100 os_run_17_1 <|
    run_step 1100 2200 os_run_17_2 <|
    run_step 1100 3300 os_run_17_3 <|
    drop_end (o := 4400) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core319, Program.find?_of_indexOf? (j := 319) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_17_0
  · exact osLv_17_1
  · exact osLv_17_2
  · exact osLv_17_3
  · exact osLv_17_4

end
end LeanVM.Guest.B1.Whir
