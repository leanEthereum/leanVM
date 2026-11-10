/-
  LeanVM.Guest.B1.Whir.Data5

  `open_stacked__L5` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 5

`osData_5 : OsData 5`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_5_0 : stmtsEqb ((Data.core315.body.drop 0).take 1100)
    (((osBody (osCfg 5)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_5_1 : stmtsEqb ((Data.core315.body.drop 1100).take 1100)
    (((osBody (osCfg 5)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_5_2 : stmtsEqb ((Data.core315.body.drop 2200).take 1100)
    (((osBody (osCfg 5)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_5_0 : FnIs ((osCfg 5).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 5 0) ((osCfg 5).sqLoop 0)) ∧
    FnIs ((osCfg 5).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 5 0) ((osCfg 5).resLoop 0)) :=
  ⟨⟨Data.core521, Program.find?_of_indexOf? (j := 521) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core529, Program.find?_of_indexOf? (j := 529) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_5_1 : FnIs ((osCfg 5).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 5 1) ((osCfg 5).sqLoop 1)) ∧
    FnIs ((osCfg 5).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 5 1) ((osCfg 5).resLoop 1)) :=
  ⟨⟨Data.core523, Program.find?_of_indexOf? (j := 523) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core530, Program.find?_of_indexOf? (j := 530) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_5_2 : FnIs ((osCfg 5).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 5 2) ((osCfg 5).sqLoop 2)) ∧
    FnIs ((osCfg 5).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 5 2) ((osCfg 5).resLoop 2)) :=
  ⟨⟨Data.core525, Program.find?_of_indexOf? (j := 525) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core531, Program.find?_of_indexOf? (j := 531) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_5_3 : FnIs ((osCfg 5).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 5 3) ((osCfg 5).sqLoop 3)) ∧
    FnIs ((osCfg 5).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 5 3) ((osCfg 5).resLoop 3)) :=
  ⟨⟨Data.core527, Program.find?_of_indexOf? (j := 527) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core532, Program.find?_of_indexOf? (j := 532) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_5_4 : FnIs ((osCfg 5).sqLoop 4) (osParams 6)
      (sqLoopBody (osLv 5 4) ((osCfg 5).sqLoop 4)) ∧
    FnIs ((osCfg 5).resLoop 4) (osParams 6)
      (resLoopBody 4 (osLv 5 4) ((osCfg 5).resLoop 4)) :=
  ⟨⟨Data.core528, Program.find?_of_indexOf? (j := 528) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core533, Program.find?_of_indexOf? (j := 533) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_5 : OsData 5 := by
  have hl : (osCfg 5).levels.length = 5 := by decide +kernel
  have hb : Data.core315.body.drop 0 = (osBody (osCfg 5)).drop 0 :=
    run_step 1100 0 os_run_5_0 <|
    run_step 1100 1100 os_run_5_1 <|
    run_step 1100 2200 os_run_5_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core315, Program.find?_of_indexOf? (j := 315) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_5_0
  · exact osLv_5_1
  · exact osLv_5_2
  · exact osLv_5_3
  · exact osLv_5_4

end
end LeanVM.Guest.B1.Whir
