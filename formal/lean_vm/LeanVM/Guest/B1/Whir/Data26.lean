/-
  LeanVM.Guest.B1.Whir.Data26

  `open_stacked__L26` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 26

`osData_26 : OsData 26`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_26_0 : stmtsEqb ((Data.core328.body.drop 0).take 1100)
    (((osBody (osCfg 26)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_26_1 : stmtsEqb ((Data.core328.body.drop 1100).take 1100)
    (((osBody (osCfg 26)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_26_2 : stmtsEqb ((Data.core328.body.drop 2200).take 1100)
    (((osBody (osCfg 26)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_26_0 : FnIs ((osCfg 26).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 26 0) ((osCfg 26).sqLoop 0)) ∧
    FnIs ((osCfg 26).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 26 0) ((osCfg 26).resLoop 0)) :=
  ⟨⟨Data.core763, Program.find?_of_indexOf? (j := 763) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core770, Program.find?_of_indexOf? (j := 770) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_26_1 : FnIs ((osCfg 26).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 26 1) ((osCfg 26).sqLoop 1)) ∧
    FnIs ((osCfg 26).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 26 1) ((osCfg 26).resLoop 1)) :=
  ⟨⟨Data.core765, Program.find?_of_indexOf? (j := 765) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core771, Program.find?_of_indexOf? (j := 771) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_26_2 : FnIs ((osCfg 26).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 26 2) ((osCfg 26).sqLoop 2)) ∧
    FnIs ((osCfg 26).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 26 2) ((osCfg 26).resLoop 2)) :=
  ⟨⟨Data.core767, Program.find?_of_indexOf? (j := 767) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core772, Program.find?_of_indexOf? (j := 772) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_26_3 : FnIs ((osCfg 26).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 26 3) ((osCfg 26).sqLoop 3)) ∧
    FnIs ((osCfg 26).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 26 3) ((osCfg 26).resLoop 3)) :=
  ⟨⟨Data.core768, Program.find?_of_indexOf? (j := 768) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core773, Program.find?_of_indexOf? (j := 773) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_26_4 : FnIs ((osCfg 26).sqLoop 4) (osParams 6)
      (sqLoopBody (osLv 26 4) ((osCfg 26).sqLoop 4)) ∧
    FnIs ((osCfg 26).resLoop 4) (osParams 6)
      (resLoopBody 4 (osLv 26 4) ((osCfg 26).resLoop 4)) :=
  ⟨⟨Data.core769, Program.find?_of_indexOf? (j := 769) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core774, Program.find?_of_indexOf? (j := 774) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_26 : OsData 26 := by
  have hl : (osCfg 26).levels.length = 5 := by decide +kernel
  have hb : Data.core328.body.drop 0 = (osBody (osCfg 26)).drop 0 :=
    run_step 1100 0 os_run_26_0 <|
    run_step 1100 1100 os_run_26_1 <|
    run_step 1100 2200 os_run_26_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core328, Program.find?_of_indexOf? (j := 328) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_26_0
  · exact osLv_26_1
  · exact osLv_26_2
  · exact osLv_26_3
  · exact osLv_26_4

end
end LeanVM.Guest.B1.Whir
