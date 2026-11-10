/-
  LeanVM.Guest.B1.Whir.Data1

  `open_stacked__L1` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 1

`osData_1 : OsData 1`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_1_0 : stmtsEqb ((Data.core311.body.drop 0).take 1100)
    (((osBody (osCfg 1)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_1_1 : stmtsEqb ((Data.core311.body.drop 1100).take 1100)
    (((osBody (osCfg 1)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_1_0 : FnIs ((osCfg 1).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 1 0) ((osCfg 1).sqLoop 0)) ∧
    FnIs ((osCfg 1).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 1 0) ((osCfg 1).resLoop 0)) :=
  ⟨⟨Data.core453, Program.find?_of_indexOf? (j := 453) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core464, Program.find?_of_indexOf? (j := 464) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_1_1 : FnIs ((osCfg 1).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 1 1) ((osCfg 1).sqLoop 1)) ∧
    FnIs ((osCfg 1).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 1 1) ((osCfg 1).resLoop 1)) :=
  ⟨⟨Data.core456, Program.find?_of_indexOf? (j := 456) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core465, Program.find?_of_indexOf? (j := 465) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_1_2 : FnIs ((osCfg 1).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 1 2) ((osCfg 1).sqLoop 2)) ∧
    FnIs ((osCfg 1).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 1 2) ((osCfg 1).resLoop 2)) :=
  ⟨⟨Data.core459, Program.find?_of_indexOf? (j := 459) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core466, Program.find?_of_indexOf? (j := 466) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_1_3 : FnIs ((osCfg 1).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 1 3) ((osCfg 1).sqLoop 3)) ∧
    FnIs ((osCfg 1).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 1 3) ((osCfg 1).resLoop 3)) :=
  ⟨⟨Data.core462, Program.find?_of_indexOf? (j := 462) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core467, Program.find?_of_indexOf? (j := 467) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_1 : OsData 1 := by
  have hl : (osCfg 1).levels.length = 4 := by decide +kernel
  have hb : Data.core311.body.drop 0 = (osBody (osCfg 1)).drop 0 :=
    run_step 1100 0 os_run_1_0 <|
    run_step 1100 1100 os_run_1_1 <|
    drop_end (o := 2200) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core311, Program.find?_of_indexOf? (j := 311) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_1_0
  · exact osLv_1_1
  · exact osLv_1_2
  · exact osLv_1_3

end
end LeanVM.Guest.B1.Whir
