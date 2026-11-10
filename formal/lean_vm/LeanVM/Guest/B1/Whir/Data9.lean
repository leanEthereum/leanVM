/-
  LeanVM.Guest.B1.Whir.Data9

  `open_stacked__L9` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 9

`osData_9 : OsData 9`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_9_0 : stmtsEqb ((Data.core319.body.drop 0).take 1100)
    (((osBody (osCfg 9)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_9_1 : stmtsEqb ((Data.core319.body.drop 1100).take 1100)
    (((osBody (osCfg 9)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_9_2 : stmtsEqb ((Data.core319.body.drop 2200).take 1100)
    (((osBody (osCfg 9)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_9_0 : FnIs ((osCfg 9).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 9 0) ((osCfg 9).sqLoop 0)) ∧
    FnIs ((osCfg 9).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 9 0) ((osCfg 9).resLoop 0)) :=
  ⟨⟨Data.core571, Program.find?_of_indexOf? (j := 571) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core578, Program.find?_of_indexOf? (j := 578) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_9_1 : FnIs ((osCfg 9).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 9 1) ((osCfg 9).sqLoop 1)) ∧
    FnIs ((osCfg 9).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 9 1) ((osCfg 9).resLoop 1)) :=
  ⟨⟨Data.core573, Program.find?_of_indexOf? (j := 573) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core579, Program.find?_of_indexOf? (j := 579) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_9_2 : FnIs ((osCfg 9).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 9 2) ((osCfg 9).sqLoop 2)) ∧
    FnIs ((osCfg 9).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 9 2) ((osCfg 9).resLoop 2)) :=
  ⟨⟨Data.core574, Program.find?_of_indexOf? (j := 574) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core580, Program.find?_of_indexOf? (j := 580) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_9_3 : FnIs ((osCfg 9).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 9 3) ((osCfg 9).sqLoop 3)) ∧
    FnIs ((osCfg 9).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 9 3) ((osCfg 9).resLoop 3)) :=
  ⟨⟨Data.core575, Program.find?_of_indexOf? (j := 575) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core581, Program.find?_of_indexOf? (j := 581) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_9_4 : FnIs ((osCfg 9).sqLoop 4) (osParams 6)
      (sqLoopBody (osLv 9 4) ((osCfg 9).sqLoop 4)) ∧
    FnIs ((osCfg 9).resLoop 4) (osParams 6)
      (resLoopBody 4 (osLv 9 4) ((osCfg 9).resLoop 4)) :=
  ⟨⟨Data.core576, Program.find?_of_indexOf? (j := 576) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core582, Program.find?_of_indexOf? (j := 582) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_9 : OsData 9 := by
  have hl : (osCfg 9).levels.length = 5 := by decide +kernel
  have hb : Data.core319.body.drop 0 = (osBody (osCfg 9)).drop 0 :=
    run_step 1100 0 os_run_9_0 <|
    run_step 1100 1100 os_run_9_1 <|
    run_step 1100 2200 os_run_9_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core319, Program.find?_of_indexOf? (j := 319) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_9_0
  · exact osLv_9_1
  · exact osLv_9_2
  · exact osLv_9_3
  · exact osLv_9_4

end
end LeanVM.Guest.B1.Whir
