/-
  LeanVM.Guest.B1.Whir.Data0

  `open_stacked__L0` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 0

`osData_0 : OsData 0`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_0_0 : stmtsEqb ((Data.core310.body.drop 0).take 1100)
    (((osBody (osCfg 0)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_0_1 : stmtsEqb ((Data.core310.body.drop 1100).take 1100)
    (((osBody (osCfg 0)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_0_0 : FnIs ((osCfg 0).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 0 0) ((osCfg 0).sqLoop 0)) ∧
    FnIs ((osCfg 0).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 0 0) ((osCfg 0).resLoop 0)) :=
  ⟨⟨Data.core431, Program.find?_of_indexOf? (j := 431) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core448, Program.find?_of_indexOf? (j := 448) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_0_1 : FnIs ((osCfg 0).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 0 1) ((osCfg 0).sqLoop 1)) ∧
    FnIs ((osCfg 0).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 0 1) ((osCfg 0).resLoop 1)) :=
  ⟨⟨Data.core436, Program.find?_of_indexOf? (j := 436) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core449, Program.find?_of_indexOf? (j := 449) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_0_2 : FnIs ((osCfg 0).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 0 2) ((osCfg 0).sqLoop 2)) ∧
    FnIs ((osCfg 0).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 0 2) ((osCfg 0).resLoop 2)) :=
  ⟨⟨Data.core441, Program.find?_of_indexOf? (j := 441) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core450, Program.find?_of_indexOf? (j := 450) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_0_3 : FnIs ((osCfg 0).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 0 3) ((osCfg 0).sqLoop 3)) ∧
    FnIs ((osCfg 0).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 0 3) ((osCfg 0).resLoop 3)) :=
  ⟨⟨Data.core445, Program.find?_of_indexOf? (j := 445) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core451, Program.find?_of_indexOf? (j := 451) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_0 : OsData 0 := by
  have hl : (osCfg 0).levels.length = 4 := by decide +kernel
  have hb : Data.core310.body.drop 0 = (osBody (osCfg 0)).drop 0 :=
    run_step 1100 0 os_run_0_0 <|
    run_step 1100 1100 os_run_0_1 <|
    drop_end (o := 2200) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core310, Program.find?_of_indexOf? (j := 310) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_0_0
  · exact osLv_0_1
  · exact osLv_0_2
  · exact osLv_0_3

end
end LeanVM.Guest.B1.Whir
