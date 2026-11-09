/-
  LeanVM.Guest.B1.Whir.Data18

  `open_stacked__L18` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 18

`osData_18 : OsData 18`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_18_0 : stmtsEqb ((Data.core320.body.drop 0).take 1100)
    (((osBody (osCfg 18)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_18_1 : stmtsEqb ((Data.core320.body.drop 1100).take 1100)
    (((osBody (osCfg 18)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_18_2 : stmtsEqb ((Data.core320.body.drop 2200).take 1100)
    (((osBody (osCfg 18)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_18_3 : stmtsEqb ((Data.core320.body.drop 3300).take 1100)
    (((osBody (osCfg 18)).drop 3300).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_18_0 : FnIs ((osCfg 18).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 18 0) ((osCfg 18).sqLoop 0)) ∧
    FnIs ((osCfg 18).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 18 0) ((osCfg 18).resLoop 0)) :=
  ⟨⟨Data.core674, Program.find?_of_indexOf? (j := 674) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core680, Program.find?_of_indexOf? (j := 680) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_18_1 : FnIs ((osCfg 18).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 18 1) ((osCfg 18).sqLoop 1)) ∧
    FnIs ((osCfg 18).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 18 1) ((osCfg 18).resLoop 1)) :=
  ⟨⟨Data.core676, Program.find?_of_indexOf? (j := 676) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core681, Program.find?_of_indexOf? (j := 681) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_18_2 : FnIs ((osCfg 18).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 18 2) ((osCfg 18).sqLoop 2)) ∧
    FnIs ((osCfg 18).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 18 2) ((osCfg 18).resLoop 2)) :=
  ⟨⟨Data.core677, Program.find?_of_indexOf? (j := 677) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core682, Program.find?_of_indexOf? (j := 682) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_18_3 : FnIs ((osCfg 18).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 18 3) ((osCfg 18).sqLoop 3)) ∧
    FnIs ((osCfg 18).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 18 3) ((osCfg 18).resLoop 3)) :=
  ⟨⟨Data.core678, Program.find?_of_indexOf? (j := 678) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core683, Program.find?_of_indexOf? (j := 683) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_18_4 : FnIs ((osCfg 18).sqLoop 4) (osParams 6)
      (sqLoopBody (osLv 18 4) ((osCfg 18).sqLoop 4)) ∧
    FnIs ((osCfg 18).resLoop 4) (osParams 6)
      (resLoopBody 4 (osLv 18 4) ((osCfg 18).resLoop 4)) :=
  ⟨⟨Data.core679, Program.find?_of_indexOf? (j := 679) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core684, Program.find?_of_indexOf? (j := 684) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_18 : OsData 18 := by
  have hl : (osCfg 18).levels.length = 5 := by decide +kernel
  have hb : Data.core320.body.drop 0 = (osBody (osCfg 18)).drop 0 :=
    run_step 1100 0 os_run_18_0 <|
    run_step 1100 1100 os_run_18_1 <|
    run_step 1100 2200 os_run_18_2 <|
    run_step 1100 3300 os_run_18_3 <|
    drop_end (o := 4400) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core320, Program.find?_of_indexOf? (j := 320) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_18_0
  · exact osLv_18_1
  · exact osLv_18_2
  · exact osLv_18_3
  · exact osLv_18_4

end
end LeanVM.Guest.B1.Whir
