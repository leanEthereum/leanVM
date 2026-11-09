/-
  LeanVM.Guest.B1.Whir.Data19

  `open_stacked__L19` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 19

`osData_19 : OsData 19`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_19_0 : stmtsEqb ((Data.core321.body.drop 0).take 1100)
    (((osBody (osCfg 19)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_19_1 : stmtsEqb ((Data.core321.body.drop 1100).take 1100)
    (((osBody (osCfg 19)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_19_2 : stmtsEqb ((Data.core321.body.drop 2200).take 1100)
    (((osBody (osCfg 19)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_19_3 : stmtsEqb ((Data.core321.body.drop 3300).take 1100)
    (((osBody (osCfg 19)).drop 3300).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_19_0 : FnIs ((osCfg 19).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 19 0) ((osCfg 19).sqLoop 0)) ∧
    FnIs ((osCfg 19).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 19 0) ((osCfg 19).resLoop 0)) :=
  ⟨⟨Data.core685, Program.find?_of_indexOf? (j := 685) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core691, Program.find?_of_indexOf? (j := 691) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_19_1 : FnIs ((osCfg 19).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 19 1) ((osCfg 19).sqLoop 1)) ∧
    FnIs ((osCfg 19).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 19 1) ((osCfg 19).resLoop 1)) :=
  ⟨⟨Data.core687, Program.find?_of_indexOf? (j := 687) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core692, Program.find?_of_indexOf? (j := 692) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_19_2 : FnIs ((osCfg 19).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 19 2) ((osCfg 19).sqLoop 2)) ∧
    FnIs ((osCfg 19).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 19 2) ((osCfg 19).resLoop 2)) :=
  ⟨⟨Data.core688, Program.find?_of_indexOf? (j := 688) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core693, Program.find?_of_indexOf? (j := 693) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_19_3 : FnIs ((osCfg 19).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 19 3) ((osCfg 19).sqLoop 3)) ∧
    FnIs ((osCfg 19).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 19 3) ((osCfg 19).resLoop 3)) :=
  ⟨⟨Data.core689, Program.find?_of_indexOf? (j := 689) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core694, Program.find?_of_indexOf? (j := 694) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_19_4 : FnIs ((osCfg 19).sqLoop 4) (osParams 6)
      (sqLoopBody (osLv 19 4) ((osCfg 19).sqLoop 4)) ∧
    FnIs ((osCfg 19).resLoop 4) (osParams 6)
      (resLoopBody 4 (osLv 19 4) ((osCfg 19).resLoop 4)) :=
  ⟨⟨Data.core690, Program.find?_of_indexOf? (j := 690) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core695, Program.find?_of_indexOf? (j := 695) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_19 : OsData 19 := by
  have hl : (osCfg 19).levels.length = 5 := by decide +kernel
  have hb : Data.core321.body.drop 0 = (osBody (osCfg 19)).drop 0 :=
    run_step 1100 0 os_run_19_0 <|
    run_step 1100 1100 os_run_19_1 <|
    run_step 1100 2200 os_run_19_2 <|
    run_step 1100 3300 os_run_19_3 <|
    drop_end (o := 4400) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core321, Program.find?_of_indexOf? (j := 321) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_19_0
  · exact osLv_19_1
  · exact osLv_19_2
  · exact osLv_19_3
  · exact osLv_19_4

end
end LeanVM.Guest.B1.Whir
