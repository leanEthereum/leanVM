/-
  LeanVM.Guest.B1.Whir.Data14

  `open_stacked__L14` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 14

`osData_14 : OsData 14`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_14_0 : stmtsEqb ((Data.core316.body.drop 0).take 1100)
    (((osBody (osCfg 14)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_14_1 : stmtsEqb ((Data.core316.body.drop 1100).take 1100)
    (((osBody (osCfg 14)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_14_2 : stmtsEqb ((Data.core316.body.drop 2200).take 1100)
    (((osBody (osCfg 14)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_14_0 : FnIs ((osCfg 14).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 14 0) ((osCfg 14).sqLoop 0)) ∧
    FnIs ((osCfg 14).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 14 0) ((osCfg 14).resLoop 0)) :=
  ⟨⟨Data.core634, Program.find?_of_indexOf? (j := 634) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core639, Program.find?_of_indexOf? (j := 639) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_14_1 : FnIs ((osCfg 14).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 14 1) ((osCfg 14).sqLoop 1)) ∧
    FnIs ((osCfg 14).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 14 1) ((osCfg 14).resLoop 1)) :=
  ⟨⟨Data.core636, Program.find?_of_indexOf? (j := 636) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core640, Program.find?_of_indexOf? (j := 640) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_14_2 : FnIs ((osCfg 14).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 14 2) ((osCfg 14).sqLoop 2)) ∧
    FnIs ((osCfg 14).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 14 2) ((osCfg 14).resLoop 2)) :=
  ⟨⟨Data.core637, Program.find?_of_indexOf? (j := 637) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core641, Program.find?_of_indexOf? (j := 641) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_14_3 : FnIs ((osCfg 14).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 14 3) ((osCfg 14).sqLoop 3)) ∧
    FnIs ((osCfg 14).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 14 3) ((osCfg 14).resLoop 3)) :=
  ⟨⟨Data.core638, Program.find?_of_indexOf? (j := 638) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core642, Program.find?_of_indexOf? (j := 642) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_14 : OsData 14 := by
  have hl : (osCfg 14).levels.length = 4 := by decide +kernel
  have hb : Data.core316.body.drop 0 = (osBody (osCfg 14)).drop 0 :=
    run_step 1100 0 os_run_14_0 <|
    run_step 1100 1100 os_run_14_1 <|
    run_step 1100 2200 os_run_14_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core316, Program.find?_of_indexOf? (j := 316) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_14_0
  · exact osLv_14_1
  · exact osLv_14_2
  · exact osLv_14_3

end
end LeanVM.Guest.B1.Whir
