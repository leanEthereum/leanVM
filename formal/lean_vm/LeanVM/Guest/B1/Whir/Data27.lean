/-
  LeanVM.Guest.B1.Whir.Data27

  `open_stacked__L27` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 27

`osData_27 : OsData 27`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_27_0 : stmtsEqb ((Data.core329.body.drop 0).take 1100)
    (((osBody (osCfg 27)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_27_1 : stmtsEqb ((Data.core329.body.drop 1100).take 1100)
    (((osBody (osCfg 27)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_27_2 : stmtsEqb ((Data.core329.body.drop 2200).take 1100)
    (((osBody (osCfg 27)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_27_3 : stmtsEqb ((Data.core329.body.drop 3300).take 1100)
    (((osBody (osCfg 27)).drop 3300).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_27_0 : FnIs ((osCfg 27).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 27 0) ((osCfg 27).sqLoop 0)) ∧
    FnIs ((osCfg 27).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 27 0) ((osCfg 27).resLoop 0)) :=
  ⟨⟨Data.core775, Program.find?_of_indexOf? (j := 775) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core784, Program.find?_of_indexOf? (j := 784) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_27_1 : FnIs ((osCfg 27).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 27 1) ((osCfg 27).sqLoop 1)) ∧
    FnIs ((osCfg 27).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 27 1) ((osCfg 27).resLoop 1)) :=
  ⟨⟨Data.core777, Program.find?_of_indexOf? (j := 777) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core785, Program.find?_of_indexOf? (j := 785) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_27_2 : FnIs ((osCfg 27).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 27 2) ((osCfg 27).sqLoop 2)) ∧
    FnIs ((osCfg 27).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 27 2) ((osCfg 27).resLoop 2)) :=
  ⟨⟨Data.core779, Program.find?_of_indexOf? (j := 779) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core786, Program.find?_of_indexOf? (j := 786) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_27_3 : FnIs ((osCfg 27).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 27 3) ((osCfg 27).sqLoop 3)) ∧
    FnIs ((osCfg 27).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 27 3) ((osCfg 27).resLoop 3)) :=
  ⟨⟨Data.core780, Program.find?_of_indexOf? (j := 780) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core787, Program.find?_of_indexOf? (j := 787) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_27_4 : FnIs ((osCfg 27).sqLoop 4) (osParams 6)
      (sqLoopBody (osLv 27 4) ((osCfg 27).sqLoop 4)) ∧
    FnIs ((osCfg 27).resLoop 4) (osParams 6)
      (resLoopBody 4 (osLv 27 4) ((osCfg 27).resLoop 4)) :=
  ⟨⟨Data.core781, Program.find?_of_indexOf? (j := 781) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core788, Program.find?_of_indexOf? (j := 788) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_27_5 : FnIs ((osCfg 27).sqLoop 5) (osParams 6)
      (sqLoopBody (osLv 27 5) ((osCfg 27).sqLoop 5)) ∧
    FnIs ((osCfg 27).resLoop 5) (osParams 6)
      (resLoopBody 5 (osLv 27 5) ((osCfg 27).resLoop 5)) :=
  ⟨⟨Data.core783, Program.find?_of_indexOf? (j := 783) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core789, Program.find?_of_indexOf? (j := 789) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_27 : OsData 27 := by
  have hl : (osCfg 27).levels.length = 6 := by decide +kernel
  have hb : Data.core329.body.drop 0 = (osBody (osCfg 27)).drop 0 :=
    run_step 1100 0 os_run_27_0 <|
    run_step 1100 1100 os_run_27_1 <|
    run_step 1100 2200 os_run_27_2 <|
    run_step 1100 3300 os_run_27_3 <|
    drop_end (o := 4400) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core329, Program.find?_of_indexOf? (j := 329) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_27_0
  · exact osLv_27_1
  · exact osLv_27_2
  · exact osLv_27_3
  · exact osLv_27_4
  · exact osLv_27_5

end
end LeanVM.Guest.B1.Whir
