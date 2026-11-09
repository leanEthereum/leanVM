/-
  LeanVM.Guest.B1.Whir.Data10

  `open_stacked__L10` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 10

`osData_10 : OsData 10`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_10_0 : stmtsEqb ((Data.core312.body.drop 0).take 1100)
    (((osBody (osCfg 10)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_10_1 : stmtsEqb ((Data.core312.body.drop 1100).take 1100)
    (((osBody (osCfg 10)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_10_2 : stmtsEqb ((Data.core312.body.drop 2200).take 1100)
    (((osBody (osCfg 10)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_10_0 : FnIs ((osCfg 10).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 10 0) ((osCfg 10).sqLoop 0)) ∧
    FnIs ((osCfg 10).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 10 0) ((osCfg 10).resLoop 0)) :=
  ⟨⟨Data.core583, Program.find?_of_indexOf? (j := 583) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core590, Program.find?_of_indexOf? (j := 590) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_10_1 : FnIs ((osCfg 10).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 10 1) ((osCfg 10).sqLoop 1)) ∧
    FnIs ((osCfg 10).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 10 1) ((osCfg 10).resLoop 1)) :=
  ⟨⟨Data.core585, Program.find?_of_indexOf? (j := 585) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core591, Program.find?_of_indexOf? (j := 591) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_10_2 : FnIs ((osCfg 10).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 10 2) ((osCfg 10).sqLoop 2)) ∧
    FnIs ((osCfg 10).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 10 2) ((osCfg 10).resLoop 2)) :=
  ⟨⟨Data.core586, Program.find?_of_indexOf? (j := 586) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core592, Program.find?_of_indexOf? (j := 592) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_10_3 : FnIs ((osCfg 10).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 10 3) ((osCfg 10).sqLoop 3)) ∧
    FnIs ((osCfg 10).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 10 3) ((osCfg 10).resLoop 3)) :=
  ⟨⟨Data.core587, Program.find?_of_indexOf? (j := 587) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core593, Program.find?_of_indexOf? (j := 593) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_10_4 : FnIs ((osCfg 10).sqLoop 4) (osParams 6)
      (sqLoopBody (osLv 10 4) ((osCfg 10).sqLoop 4)) ∧
    FnIs ((osCfg 10).resLoop 4) (osParams 6)
      (resLoopBody 4 (osLv 10 4) ((osCfg 10).resLoop 4)) :=
  ⟨⟨Data.core588, Program.find?_of_indexOf? (j := 588) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core594, Program.find?_of_indexOf? (j := 594) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_10 : OsData 10 := by
  have hl : (osCfg 10).levels.length = 5 := by decide +kernel
  have hb : Data.core312.body.drop 0 = (osBody (osCfg 10)).drop 0 :=
    run_step 1100 0 os_run_10_0 <|
    run_step 1100 1100 os_run_10_1 <|
    run_step 1100 2200 os_run_10_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core312, Program.find?_of_indexOf? (j := 312) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_10_0
  · exact osLv_10_1
  · exact osLv_10_2
  · exact osLv_10_3
  · exact osLv_10_4

end
end LeanVM.Guest.B1.Whir
