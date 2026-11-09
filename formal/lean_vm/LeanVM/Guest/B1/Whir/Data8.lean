/-
  LeanVM.Guest.B1.Whir.Data8

  `open_stacked__L8` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 8

`osData_8 : OsData 8`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_8_0 : stmtsEqb ((Data.core310.body.drop 0).take 1100)
    (((osBody (osCfg 8)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_8_1 : stmtsEqb ((Data.core310.body.drop 1100).take 1100)
    (((osBody (osCfg 8)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_8_2 : stmtsEqb ((Data.core310.body.drop 2200).take 1100)
    (((osBody (osCfg 8)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_8_0 : FnIs ((osCfg 8).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 8 0) ((osCfg 8).sqLoop 0)) ∧
    FnIs ((osCfg 8).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 8 0) ((osCfg 8).resLoop 0)) :=
  ⟨⟨Data.core562, Program.find?_of_indexOf? (j := 562) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core567, Program.find?_of_indexOf? (j := 567) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_8_1 : FnIs ((osCfg 8).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 8 1) ((osCfg 8).sqLoop 1)) ∧
    FnIs ((osCfg 8).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 8 1) ((osCfg 8).resLoop 1)) :=
  ⟨⟨Data.core564, Program.find?_of_indexOf? (j := 564) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core568, Program.find?_of_indexOf? (j := 568) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_8_2 : FnIs ((osCfg 8).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 8 2) ((osCfg 8).sqLoop 2)) ∧
    FnIs ((osCfg 8).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 8 2) ((osCfg 8).resLoop 2)) :=
  ⟨⟨Data.core565, Program.find?_of_indexOf? (j := 565) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core569, Program.find?_of_indexOf? (j := 569) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_8_3 : FnIs ((osCfg 8).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 8 3) ((osCfg 8).sqLoop 3)) ∧
    FnIs ((osCfg 8).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 8 3) ((osCfg 8).resLoop 3)) :=
  ⟨⟨Data.core566, Program.find?_of_indexOf? (j := 566) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core570, Program.find?_of_indexOf? (j := 570) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_8 : OsData 8 := by
  have hl : (osCfg 8).levels.length = 4 := by decide +kernel
  have hb : Data.core310.body.drop 0 = (osBody (osCfg 8)).drop 0 :=
    run_step 1100 0 os_run_8_0 <|
    run_step 1100 1100 os_run_8_1 <|
    run_step 1100 2200 os_run_8_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core310, Program.find?_of_indexOf? (j := 310) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_8_0
  · exact osLv_8_1
  · exact osLv_8_2
  · exact osLv_8_3

end
end LeanVM.Guest.B1.Whir
