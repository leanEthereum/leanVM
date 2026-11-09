/-
  LeanVM.Guest.B1.Whir.Data11

  `open_stacked__L11` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 11

`osData_11 : OsData 11`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_11_0 : stmtsEqb ((Data.core313.body.drop 0).take 1100)
    (((osBody (osCfg 11)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_11_1 : stmtsEqb ((Data.core313.body.drop 1100).take 1100)
    (((osBody (osCfg 11)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_11_2 : stmtsEqb ((Data.core313.body.drop 2200).take 1100)
    (((osBody (osCfg 11)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_11_3 : stmtsEqb ((Data.core313.body.drop 3300).take 1100)
    (((osBody (osCfg 11)).drop 3300).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_11_0 : FnIs ((osCfg 11).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 11 0) ((osCfg 11).sqLoop 0)) ∧
    FnIs ((osCfg 11).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 11 0) ((osCfg 11).resLoop 0)) :=
  ⟨⟨Data.core595, Program.find?_of_indexOf? (j := 595) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core601, Program.find?_of_indexOf? (j := 601) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_11_1 : FnIs ((osCfg 11).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 11 1) ((osCfg 11).sqLoop 1)) ∧
    FnIs ((osCfg 11).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 11 1) ((osCfg 11).resLoop 1)) :=
  ⟨⟨Data.core597, Program.find?_of_indexOf? (j := 597) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core602, Program.find?_of_indexOf? (j := 602) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_11_2 : FnIs ((osCfg 11).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 11 2) ((osCfg 11).sqLoop 2)) ∧
    FnIs ((osCfg 11).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 11 2) ((osCfg 11).resLoop 2)) :=
  ⟨⟨Data.core598, Program.find?_of_indexOf? (j := 598) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core603, Program.find?_of_indexOf? (j := 603) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_11_3 : FnIs ((osCfg 11).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 11 3) ((osCfg 11).sqLoop 3)) ∧
    FnIs ((osCfg 11).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 11 3) ((osCfg 11).resLoop 3)) :=
  ⟨⟨Data.core599, Program.find?_of_indexOf? (j := 599) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core604, Program.find?_of_indexOf? (j := 604) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_11_4 : FnIs ((osCfg 11).sqLoop 4) (osParams 6)
      (sqLoopBody (osLv 11 4) ((osCfg 11).sqLoop 4)) ∧
    FnIs ((osCfg 11).resLoop 4) (osParams 6)
      (resLoopBody 4 (osLv 11 4) ((osCfg 11).resLoop 4)) :=
  ⟨⟨Data.core600, Program.find?_of_indexOf? (j := 600) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core605, Program.find?_of_indexOf? (j := 605) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_11 : OsData 11 := by
  have hl : (osCfg 11).levels.length = 5 := by decide +kernel
  have hb : Data.core313.body.drop 0 = (osBody (osCfg 11)).drop 0 :=
    run_step 1100 0 os_run_11_0 <|
    run_step 1100 1100 os_run_11_1 <|
    run_step 1100 2200 os_run_11_2 <|
    run_step 1100 3300 os_run_11_3 <|
    drop_end (o := 4400) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core313, Program.find?_of_indexOf? (j := 313) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_11_0
  · exact osLv_11_1
  · exact osLv_11_2
  · exact osLv_11_3
  · exact osLv_11_4

end
end LeanVM.Guest.B1.Whir
