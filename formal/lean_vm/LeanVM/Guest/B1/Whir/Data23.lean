/-
  LeanVM.Guest.B1.Whir.Data23

  `open_stacked__L23` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 23

`osData_23 : OsData 23`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_23_0 : stmtsEqb ((Data.core325.body.drop 0).take 1100)
    (((osBody (osCfg 23)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_23_1 : stmtsEqb ((Data.core325.body.drop 1100).take 1100)
    (((osBody (osCfg 23)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_23_2 : stmtsEqb ((Data.core325.body.drop 2200).take 1100)
    (((osBody (osCfg 23)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_23_0 : FnIs ((osCfg 23).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 23 0) ((osCfg 23).sqLoop 0)) ∧
    FnIs ((osCfg 23).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 23 0) ((osCfg 23).resLoop 0)) :=
  ⟨⟨Data.core730, Program.find?_of_indexOf? (j := 730) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core736, Program.find?_of_indexOf? (j := 736) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_23_1 : FnIs ((osCfg 23).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 23 1) ((osCfg 23).sqLoop 1)) ∧
    FnIs ((osCfg 23).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 23 1) ((osCfg 23).resLoop 1)) :=
  ⟨⟨Data.core732, Program.find?_of_indexOf? (j := 732) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core737, Program.find?_of_indexOf? (j := 737) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_23_2 : FnIs ((osCfg 23).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 23 2) ((osCfg 23).sqLoop 2)) ∧
    FnIs ((osCfg 23).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 23 2) ((osCfg 23).resLoop 2)) :=
  ⟨⟨Data.core733, Program.find?_of_indexOf? (j := 733) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core738, Program.find?_of_indexOf? (j := 738) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_23_3 : FnIs ((osCfg 23).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 23 3) ((osCfg 23).sqLoop 3)) ∧
    FnIs ((osCfg 23).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 23 3) ((osCfg 23).resLoop 3)) :=
  ⟨⟨Data.core734, Program.find?_of_indexOf? (j := 734) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core739, Program.find?_of_indexOf? (j := 739) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_23_4 : FnIs ((osCfg 23).sqLoop 4) (osParams 6)
      (sqLoopBody (osLv 23 4) ((osCfg 23).sqLoop 4)) ∧
    FnIs ((osCfg 23).resLoop 4) (osParams 6)
      (resLoopBody 4 (osLv 23 4) ((osCfg 23).resLoop 4)) :=
  ⟨⟨Data.core735, Program.find?_of_indexOf? (j := 735) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core740, Program.find?_of_indexOf? (j := 740) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_23 : OsData 23 := by
  have hl : (osCfg 23).levels.length = 5 := by decide +kernel
  have hb : Data.core325.body.drop 0 = (osBody (osCfg 23)).drop 0 :=
    run_step 1100 0 os_run_23_0 <|
    run_step 1100 1100 os_run_23_1 <|
    run_step 1100 2200 os_run_23_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core325, Program.find?_of_indexOf? (j := 325) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_23_0
  · exact osLv_23_1
  · exact osLv_23_2
  · exact osLv_23_3
  · exact osLv_23_4

end
end LeanVM.Guest.B1.Whir
