/-
  LeanVM.Guest.B1.Whir.Data24

  `open_stacked__L24` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 24

`osData_24 : OsData 24`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_24_0 : stmtsEqb ((Data.core326.body.drop 0).take 1100)
    (((osBody (osCfg 24)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_24_1 : stmtsEqb ((Data.core326.body.drop 1100).take 1100)
    (((osBody (osCfg 24)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_24_2 : stmtsEqb ((Data.core326.body.drop 2200).take 1100)
    (((osBody (osCfg 24)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_24_0 : FnIs ((osCfg 24).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 24 0) ((osCfg 24).sqLoop 0)) ∧
    FnIs ((osCfg 24).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 24 0) ((osCfg 24).resLoop 0)) :=
  ⟨⟨Data.core741, Program.find?_of_indexOf? (j := 741) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core747, Program.find?_of_indexOf? (j := 747) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_24_1 : FnIs ((osCfg 24).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 24 1) ((osCfg 24).sqLoop 1)) ∧
    FnIs ((osCfg 24).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 24 1) ((osCfg 24).resLoop 1)) :=
  ⟨⟨Data.core743, Program.find?_of_indexOf? (j := 743) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core748, Program.find?_of_indexOf? (j := 748) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_24_2 : FnIs ((osCfg 24).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 24 2) ((osCfg 24).sqLoop 2)) ∧
    FnIs ((osCfg 24).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 24 2) ((osCfg 24).resLoop 2)) :=
  ⟨⟨Data.core744, Program.find?_of_indexOf? (j := 744) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core749, Program.find?_of_indexOf? (j := 749) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_24_3 : FnIs ((osCfg 24).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 24 3) ((osCfg 24).sqLoop 3)) ∧
    FnIs ((osCfg 24).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 24 3) ((osCfg 24).resLoop 3)) :=
  ⟨⟨Data.core745, Program.find?_of_indexOf? (j := 745) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core750, Program.find?_of_indexOf? (j := 750) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_24_4 : FnIs ((osCfg 24).sqLoop 4) (osParams 6)
      (sqLoopBody (osLv 24 4) ((osCfg 24).sqLoop 4)) ∧
    FnIs ((osCfg 24).resLoop 4) (osParams 6)
      (resLoopBody 4 (osLv 24 4) ((osCfg 24).resLoop 4)) :=
  ⟨⟨Data.core746, Program.find?_of_indexOf? (j := 746) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core751, Program.find?_of_indexOf? (j := 751) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_24 : OsData 24 := by
  have hl : (osCfg 24).levels.length = 5 := by decide +kernel
  have hb : Data.core326.body.drop 0 = (osBody (osCfg 24)).drop 0 :=
    run_step 1100 0 os_run_24_0 <|
    run_step 1100 1100 os_run_24_1 <|
    run_step 1100 2200 os_run_24_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core326, Program.find?_of_indexOf? (j := 326) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_24_0
  · exact osLv_24_1
  · exact osLv_24_2
  · exact osLv_24_3
  · exact osLv_24_4

end
end LeanVM.Guest.B1.Whir
