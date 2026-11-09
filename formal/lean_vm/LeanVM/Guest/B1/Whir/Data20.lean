/-
  LeanVM.Guest.B1.Whir.Data20

  `open_stacked__L20` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 20

`osData_20 : OsData 20`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_20_0 : stmtsEqb ((Data.core322.body.drop 0).take 1100)
    (((osBody (osCfg 20)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_20_1 : stmtsEqb ((Data.core322.body.drop 1100).take 1100)
    (((osBody (osCfg 20)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_20_2 : stmtsEqb ((Data.core322.body.drop 2200).take 1100)
    (((osBody (osCfg 20)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_20_3 : stmtsEqb ((Data.core322.body.drop 3300).take 1100)
    (((osBody (osCfg 20)).drop 3300).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_20_0 : FnIs ((osCfg 20).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 20 0) ((osCfg 20).sqLoop 0)) ∧
    FnIs ((osCfg 20).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 20 0) ((osCfg 20).resLoop 0)) :=
  ⟨⟨Data.core696, Program.find?_of_indexOf? (j := 696) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core706, Program.find?_of_indexOf? (j := 706) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_20_1 : FnIs ((osCfg 20).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 20 1) ((osCfg 20).sqLoop 1)) ∧
    FnIs ((osCfg 20).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 20 1) ((osCfg 20).resLoop 1)) :=
  ⟨⟨Data.core698, Program.find?_of_indexOf? (j := 698) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core707, Program.find?_of_indexOf? (j := 707) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_20_2 : FnIs ((osCfg 20).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 20 2) ((osCfg 20).sqLoop 2)) ∧
    FnIs ((osCfg 20).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 20 2) ((osCfg 20).resLoop 2)) :=
  ⟨⟨Data.core700, Program.find?_of_indexOf? (j := 700) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core708, Program.find?_of_indexOf? (j := 708) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_20_3 : FnIs ((osCfg 20).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 20 3) ((osCfg 20).sqLoop 3)) ∧
    FnIs ((osCfg 20).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 20 3) ((osCfg 20).resLoop 3)) :=
  ⟨⟨Data.core702, Program.find?_of_indexOf? (j := 702) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core709, Program.find?_of_indexOf? (j := 709) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_20_4 : FnIs ((osCfg 20).sqLoop 4) (osParams 6)
      (sqLoopBody (osLv 20 4) ((osCfg 20).sqLoop 4)) ∧
    FnIs ((osCfg 20).resLoop 4) (osParams 6)
      (resLoopBody 4 (osLv 20 4) ((osCfg 20).resLoop 4)) :=
  ⟨⟨Data.core703, Program.find?_of_indexOf? (j := 703) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core710, Program.find?_of_indexOf? (j := 710) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_20_5 : FnIs ((osCfg 20).sqLoop 5) (osParams 6)
      (sqLoopBody (osLv 20 5) ((osCfg 20).sqLoop 5)) ∧
    FnIs ((osCfg 20).resLoop 5) (osParams 6)
      (resLoopBody 5 (osLv 20 5) ((osCfg 20).resLoop 5)) :=
  ⟨⟨Data.core705, Program.find?_of_indexOf? (j := 705) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core711, Program.find?_of_indexOf? (j := 711) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_20 : OsData 20 := by
  have hl : (osCfg 20).levels.length = 6 := by decide +kernel
  have hb : Data.core322.body.drop 0 = (osBody (osCfg 20)).drop 0 :=
    run_step 1100 0 os_run_20_0 <|
    run_step 1100 1100 os_run_20_1 <|
    run_step 1100 2200 os_run_20_2 <|
    run_step 1100 3300 os_run_20_3 <|
    drop_end (o := 4400) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core322, Program.find?_of_indexOf? (j := 322) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_20_0
  · exact osLv_20_1
  · exact osLv_20_2
  · exact osLv_20_3
  · exact osLv_20_4
  · exact osLv_20_5

end
end LeanVM.Guest.B1.Whir
