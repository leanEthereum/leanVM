/-
  LeanVM.Guest.B1.Whir.Data12

  `open_stacked__L12` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 12

`osData_12 : OsData 12`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_12_0 : stmtsEqb ((Data.core322.body.drop 0).take 1100)
    (((osBody (osCfg 12)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_12_1 : stmtsEqb ((Data.core322.body.drop 1100).take 1100)
    (((osBody (osCfg 12)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_12_2 : stmtsEqb ((Data.core322.body.drop 2200).take 1100)
    (((osBody (osCfg 12)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_12_3 : stmtsEqb ((Data.core322.body.drop 3300).take 1100)
    (((osBody (osCfg 12)).drop 3300).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_12_0 : FnIs ((osCfg 12).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 12 0) ((osCfg 12).sqLoop 0)) ∧
    FnIs ((osCfg 12).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 12 0) ((osCfg 12).resLoop 0)) :=
  ⟨⟨Data.core606, Program.find?_of_indexOf? (j := 606) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core613, Program.find?_of_indexOf? (j := 613) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_12_1 : FnIs ((osCfg 12).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 12 1) ((osCfg 12).sqLoop 1)) ∧
    FnIs ((osCfg 12).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 12 1) ((osCfg 12).resLoop 1)) :=
  ⟨⟨Data.core608, Program.find?_of_indexOf? (j := 608) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core614, Program.find?_of_indexOf? (j := 614) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_12_2 : FnIs ((osCfg 12).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 12 2) ((osCfg 12).sqLoop 2)) ∧
    FnIs ((osCfg 12).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 12 2) ((osCfg 12).resLoop 2)) :=
  ⟨⟨Data.core609, Program.find?_of_indexOf? (j := 609) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core615, Program.find?_of_indexOf? (j := 615) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_12_3 : FnIs ((osCfg 12).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 12 3) ((osCfg 12).sqLoop 3)) ∧
    FnIs ((osCfg 12).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 12 3) ((osCfg 12).resLoop 3)) :=
  ⟨⟨Data.core610, Program.find?_of_indexOf? (j := 610) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core616, Program.find?_of_indexOf? (j := 616) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_12_4 : FnIs ((osCfg 12).sqLoop 4) (osParams 6)
      (sqLoopBody (osLv 12 4) ((osCfg 12).sqLoop 4)) ∧
    FnIs ((osCfg 12).resLoop 4) (osParams 6)
      (resLoopBody 4 (osLv 12 4) ((osCfg 12).resLoop 4)) :=
  ⟨⟨Data.core611, Program.find?_of_indexOf? (j := 611) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core617, Program.find?_of_indexOf? (j := 617) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_12 : OsData 12 := by
  have hl : (osCfg 12).levels.length = 5 := by decide +kernel
  have hb : Data.core322.body.drop 0 = (osBody (osCfg 12)).drop 0 :=
    run_step 1100 0 os_run_12_0 <|
    run_step 1100 1100 os_run_12_1 <|
    run_step 1100 2200 os_run_12_2 <|
    run_step 1100 3300 os_run_12_3 <|
    drop_end (o := 4400) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core322, Program.find?_of_indexOf? (j := 322) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_12_0
  · exact osLv_12_1
  · exact osLv_12_2
  · exact osLv_12_3
  · exact osLv_12_4

end
end LeanVM.Guest.B1.Whir
