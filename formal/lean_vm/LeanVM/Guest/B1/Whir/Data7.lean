/-
  LeanVM.Guest.B1.Whir.Data7

  `open_stacked__L7` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 7

`osData_7 : OsData 7`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_7_0 : stmtsEqb ((Data.core317.body.drop 0).take 1100)
    (((osBody (osCfg 7)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_7_1 : stmtsEqb ((Data.core317.body.drop 1100).take 1100)
    (((osBody (osCfg 7)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_7_2 : stmtsEqb ((Data.core317.body.drop 2200).take 1100)
    (((osBody (osCfg 7)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_7_0 : FnIs ((osCfg 7).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 7 0) ((osCfg 7).sqLoop 0)) ∧
    FnIs ((osCfg 7).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 7 0) ((osCfg 7).resLoop 0)) :=
  ⟨⟨Data.core552, Program.find?_of_indexOf? (j := 552) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core558, Program.find?_of_indexOf? (j := 558) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_7_1 : FnIs ((osCfg 7).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 7 1) ((osCfg 7).sqLoop 1)) ∧
    FnIs ((osCfg 7).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 7 1) ((osCfg 7).resLoop 1)) :=
  ⟨⟨Data.core555, Program.find?_of_indexOf? (j := 555) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core559, Program.find?_of_indexOf? (j := 559) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_7_2 : FnIs ((osCfg 7).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 7 2) ((osCfg 7).sqLoop 2)) ∧
    FnIs ((osCfg 7).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 7 2) ((osCfg 7).resLoop 2)) :=
  ⟨⟨Data.core556, Program.find?_of_indexOf? (j := 556) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core560, Program.find?_of_indexOf? (j := 560) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_7_3 : FnIs ((osCfg 7).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 7 3) ((osCfg 7).sqLoop 3)) ∧
    FnIs ((osCfg 7).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 7 3) ((osCfg 7).resLoop 3)) :=
  ⟨⟨Data.core557, Program.find?_of_indexOf? (j := 557) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core561, Program.find?_of_indexOf? (j := 561) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_7 : OsData 7 := by
  have hl : (osCfg 7).levels.length = 4 := by decide +kernel
  have hb : Data.core317.body.drop 0 = (osBody (osCfg 7)).drop 0 :=
    run_step 1100 0 os_run_7_0 <|
    run_step 1100 1100 os_run_7_1 <|
    run_step 1100 2200 os_run_7_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core317, Program.find?_of_indexOf? (j := 317) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_7_0
  · exact osLv_7_1
  · exact osLv_7_2
  · exact osLv_7_3

end
end LeanVM.Guest.B1.Whir
