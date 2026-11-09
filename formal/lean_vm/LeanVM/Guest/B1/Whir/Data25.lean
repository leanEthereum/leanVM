/-
  LeanVM.Guest.B1.Whir.Data25

  `open_stacked__L25` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 25

`osData_25 : OsData 25`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_25_0 : stmtsEqb ((Data.core327.body.drop 0).take 1100)
    (((osBody (osCfg 25)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_25_1 : stmtsEqb ((Data.core327.body.drop 1100).take 1100)
    (((osBody (osCfg 25)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_25_2 : stmtsEqb ((Data.core327.body.drop 2200).take 1100)
    (((osBody (osCfg 25)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_25_0 : FnIs ((osCfg 25).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 25 0) ((osCfg 25).sqLoop 0)) ∧
    FnIs ((osCfg 25).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 25 0) ((osCfg 25).resLoop 0)) :=
  ⟨⟨Data.core752, Program.find?_of_indexOf? (j := 752) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core758, Program.find?_of_indexOf? (j := 758) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_25_1 : FnIs ((osCfg 25).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 25 1) ((osCfg 25).sqLoop 1)) ∧
    FnIs ((osCfg 25).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 25 1) ((osCfg 25).resLoop 1)) :=
  ⟨⟨Data.core754, Program.find?_of_indexOf? (j := 754) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core759, Program.find?_of_indexOf? (j := 759) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_25_2 : FnIs ((osCfg 25).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 25 2) ((osCfg 25).sqLoop 2)) ∧
    FnIs ((osCfg 25).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 25 2) ((osCfg 25).resLoop 2)) :=
  ⟨⟨Data.core755, Program.find?_of_indexOf? (j := 755) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core760, Program.find?_of_indexOf? (j := 760) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_25_3 : FnIs ((osCfg 25).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 25 3) ((osCfg 25).sqLoop 3)) ∧
    FnIs ((osCfg 25).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 25 3) ((osCfg 25).resLoop 3)) :=
  ⟨⟨Data.core756, Program.find?_of_indexOf? (j := 756) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core761, Program.find?_of_indexOf? (j := 761) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_25_4 : FnIs ((osCfg 25).sqLoop 4) (osParams 6)
      (sqLoopBody (osLv 25 4) ((osCfg 25).sqLoop 4)) ∧
    FnIs ((osCfg 25).resLoop 4) (osParams 6)
      (resLoopBody 4 (osLv 25 4) ((osCfg 25).resLoop 4)) :=
  ⟨⟨Data.core757, Program.find?_of_indexOf? (j := 757) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core762, Program.find?_of_indexOf? (j := 762) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_25 : OsData 25 := by
  have hl : (osCfg 25).levels.length = 5 := by decide +kernel
  have hb : Data.core327.body.drop 0 = (osBody (osCfg 25)).drop 0 :=
    run_step 1100 0 os_run_25_0 <|
    run_step 1100 1100 os_run_25_1 <|
    run_step 1100 2200 os_run_25_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core327, Program.find?_of_indexOf? (j := 327) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_25_0
  · exact osLv_25_1
  · exact osLv_25_2
  · exact osLv_25_3
  · exact osLv_25_4

end
end LeanVM.Guest.B1.Whir
