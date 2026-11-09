/-
  LeanVM.Guest.B1.Whir.Data2

  `open_stacked__L2` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 2

`osData_2 : OsData 2`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_2_0 : stmtsEqb ((Data.core304.body.drop 0).take 1100)
    (((osBody (osCfg 2)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_2_1 : stmtsEqb ((Data.core304.body.drop 1100).take 1100)
    (((osBody (osCfg 2)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_2_2 : stmtsEqb ((Data.core304.body.drop 2200).take 1100)
    (((osBody (osCfg 2)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_2_0 : FnIs ((osCfg 2).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 2 0) ((osCfg 2).sqLoop 0)) ∧
    FnIs ((osCfg 2).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 2 0) ((osCfg 2).resLoop 0)) :=
  ⟨⟨Data.core469, Program.find?_of_indexOf? (j := 469) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core482, Program.find?_of_indexOf? (j := 482) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_2_1 : FnIs ((osCfg 2).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 2 1) ((osCfg 2).sqLoop 1)) ∧
    FnIs ((osCfg 2).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 2 1) ((osCfg 2).resLoop 1)) :=
  ⟨⟨Data.core472, Program.find?_of_indexOf? (j := 472) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core483, Program.find?_of_indexOf? (j := 483) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_2_2 : FnIs ((osCfg 2).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 2 2) ((osCfg 2).sqLoop 2)) ∧
    FnIs ((osCfg 2).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 2 2) ((osCfg 2).resLoop 2)) :=
  ⟨⟨Data.core475, Program.find?_of_indexOf? (j := 475) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core484, Program.find?_of_indexOf? (j := 484) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_2_3 : FnIs ((osCfg 2).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 2 3) ((osCfg 2).sqLoop 3)) ∧
    FnIs ((osCfg 2).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 2 3) ((osCfg 2).resLoop 3)) :=
  ⟨⟨Data.core478, Program.find?_of_indexOf? (j := 478) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core485, Program.find?_of_indexOf? (j := 485) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_2_4 : FnIs ((osCfg 2).sqLoop 4) (osParams 6)
      (sqLoopBody (osLv 2 4) ((osCfg 2).sqLoop 4)) ∧
    FnIs ((osCfg 2).resLoop 4) (osParams 6)
      (resLoopBody 4 (osLv 2 4) ((osCfg 2).resLoop 4)) :=
  ⟨⟨Data.core480, Program.find?_of_indexOf? (j := 480) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core486, Program.find?_of_indexOf? (j := 486) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_2 : OsData 2 := by
  have hl : (osCfg 2).levels.length = 5 := by decide +kernel
  have hb : Data.core304.body.drop 0 = (osBody (osCfg 2)).drop 0 :=
    run_step 1100 0 os_run_2_0 <|
    run_step 1100 1100 os_run_2_1 <|
    run_step 1100 2200 os_run_2_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core304, Program.find?_of_indexOf? (j := 304) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_2_0
  · exact osLv_2_1
  · exact osLv_2_2
  · exact osLv_2_3
  · exact osLv_2_4

end
end LeanVM.Guest.B1.Whir
