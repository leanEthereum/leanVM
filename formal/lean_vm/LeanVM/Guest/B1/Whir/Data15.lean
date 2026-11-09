/-
  LeanVM.Guest.B1.Whir.Data15

  `open_stacked__L15` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 15

`osData_15 : OsData 15`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_15_0 : stmtsEqb ((Data.core317.body.drop 0).take 1100)
    (((osBody (osCfg 15)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_15_1 : stmtsEqb ((Data.core317.body.drop 1100).take 1100)
    (((osBody (osCfg 15)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_15_2 : stmtsEqb ((Data.core317.body.drop 2200).take 1100)
    (((osBody (osCfg 15)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_15_0 : FnIs ((osCfg 15).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 15 0) ((osCfg 15).sqLoop 0)) ∧
    FnIs ((osCfg 15).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 15 0) ((osCfg 15).resLoop 0)) :=
  ⟨⟨Data.core643, Program.find?_of_indexOf? (j := 643) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core648, Program.find?_of_indexOf? (j := 648) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_15_1 : FnIs ((osCfg 15).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 15 1) ((osCfg 15).sqLoop 1)) ∧
    FnIs ((osCfg 15).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 15 1) ((osCfg 15).resLoop 1)) :=
  ⟨⟨Data.core645, Program.find?_of_indexOf? (j := 645) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core649, Program.find?_of_indexOf? (j := 649) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_15_2 : FnIs ((osCfg 15).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 15 2) ((osCfg 15).sqLoop 2)) ∧
    FnIs ((osCfg 15).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 15 2) ((osCfg 15).resLoop 2)) :=
  ⟨⟨Data.core646, Program.find?_of_indexOf? (j := 646) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core650, Program.find?_of_indexOf? (j := 650) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_15_3 : FnIs ((osCfg 15).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 15 3) ((osCfg 15).sqLoop 3)) ∧
    FnIs ((osCfg 15).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 15 3) ((osCfg 15).resLoop 3)) :=
  ⟨⟨Data.core647, Program.find?_of_indexOf? (j := 647) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core651, Program.find?_of_indexOf? (j := 651) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_15 : OsData 15 := by
  have hl : (osCfg 15).levels.length = 4 := by decide +kernel
  have hb : Data.core317.body.drop 0 = (osBody (osCfg 15)).drop 0 :=
    run_step 1100 0 os_run_15_0 <|
    run_step 1100 1100 os_run_15_1 <|
    run_step 1100 2200 os_run_15_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core317, Program.find?_of_indexOf? (j := 317) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_15_0
  · exact osLv_15_1
  · exact osLv_15_2
  · exact osLv_15_3

end
end LeanVM.Guest.B1.Whir
