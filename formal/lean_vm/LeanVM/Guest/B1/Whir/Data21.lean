/-
  LeanVM.Guest.B1.Whir.Data21

  `open_stacked__L21` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 21

`osData_21 : OsData 21`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_21_0 : stmtsEqb ((Data.core323.body.drop 0).take 1100)
    (((osBody (osCfg 21)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_21_1 : stmtsEqb ((Data.core323.body.drop 1100).take 1100)
    (((osBody (osCfg 21)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_21_2 : stmtsEqb ((Data.core323.body.drop 2200).take 1100)
    (((osBody (osCfg 21)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_21_0 : FnIs ((osCfg 21).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 21 0) ((osCfg 21).sqLoop 0)) ∧
    FnIs ((osCfg 21).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 21 0) ((osCfg 21).resLoop 0)) :=
  ⟨⟨Data.core712, Program.find?_of_indexOf? (j := 712) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core717, Program.find?_of_indexOf? (j := 717) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_21_1 : FnIs ((osCfg 21).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 21 1) ((osCfg 21).sqLoop 1)) ∧
    FnIs ((osCfg 21).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 21 1) ((osCfg 21).resLoop 1)) :=
  ⟨⟨Data.core714, Program.find?_of_indexOf? (j := 714) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core718, Program.find?_of_indexOf? (j := 718) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_21_2 : FnIs ((osCfg 21).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 21 2) ((osCfg 21).sqLoop 2)) ∧
    FnIs ((osCfg 21).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 21 2) ((osCfg 21).resLoop 2)) :=
  ⟨⟨Data.core715, Program.find?_of_indexOf? (j := 715) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core719, Program.find?_of_indexOf? (j := 719) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_21_3 : FnIs ((osCfg 21).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 21 3) ((osCfg 21).sqLoop 3)) ∧
    FnIs ((osCfg 21).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 21 3) ((osCfg 21).resLoop 3)) :=
  ⟨⟨Data.core716, Program.find?_of_indexOf? (j := 716) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core720, Program.find?_of_indexOf? (j := 720) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_21 : OsData 21 := by
  have hl : (osCfg 21).levels.length = 4 := by decide +kernel
  have hb : Data.core323.body.drop 0 = (osBody (osCfg 21)).drop 0 :=
    run_step 1100 0 os_run_21_0 <|
    run_step 1100 1100 os_run_21_1 <|
    run_step 1100 2200 os_run_21_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core323, Program.find?_of_indexOf? (j := 323) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_21_0
  · exact osLv_21_1
  · exact osLv_21_2
  · exact osLv_21_3

end
end LeanVM.Guest.B1.Whir
