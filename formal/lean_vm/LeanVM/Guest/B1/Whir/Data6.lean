/-
  LeanVM.Guest.B1.Whir.Data6

  `open_stacked__L6` and its loop helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Candidate 6

`osData_6 : OsData 6`: the function and its loops found by name (their indices in the core IR
checked by the kernel), their bodies equal to the templates (`stmtsEqb_sound`), the body in runs of
1100 statements, each its own kernel evaluation (`eq_of_runs`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_6_0 : stmtsEqb ((Data.core308.body.drop 0).take 1100)
    (((osBody (osCfg 6)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_6_1 : stmtsEqb ((Data.core308.body.drop 1100).take 1100)
    (((osBody (osCfg 6)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_6_2 : stmtsEqb ((Data.core308.body.drop 2200).take 1100)
    (((osBody (osCfg 6)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_6_3 : stmtsEqb ((Data.core308.body.drop 3300).take 1100)
    (((osBody (osCfg 6)).drop 3300).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osLv_6_0 : FnIs ((osCfg 6).sqLoop 0) (osParams 6)
      (sqLoopBody (osLv 6 0) ((osCfg 6).sqLoop 0)) ∧
    FnIs ((osCfg 6).resLoop 0) (osParams 6)
      (resLoopBody 0 (osLv 6 0) ((osCfg 6).resLoop 0)) :=
  ⟨⟨Data.core535, Program.find?_of_indexOf? (j := 535) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core546, Program.find?_of_indexOf? (j := 546) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_6_1 : FnIs ((osCfg 6).sqLoop 1) (osParams 6)
      (sqLoopBody (osLv 6 1) ((osCfg 6).sqLoop 1)) ∧
    FnIs ((osCfg 6).resLoop 1) (osParams 6)
      (resLoopBody 1 (osLv 6 1) ((osCfg 6).resLoop 1)) :=
  ⟨⟨Data.core537, Program.find?_of_indexOf? (j := 537) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core547, Program.find?_of_indexOf? (j := 547) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_6_2 : FnIs ((osCfg 6).sqLoop 2) (osParams 6)
      (sqLoopBody (osLv 6 2) ((osCfg 6).sqLoop 2)) ∧
    FnIs ((osCfg 6).resLoop 2) (osParams 6)
      (resLoopBody 2 (osLv 6 2) ((osCfg 6).resLoop 2)) :=
  ⟨⟨Data.core539, Program.find?_of_indexOf? (j := 539) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core548, Program.find?_of_indexOf? (j := 548) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_6_3 : FnIs ((osCfg 6).sqLoop 3) (osParams 6)
      (sqLoopBody (osLv 6 3) ((osCfg 6).sqLoop 3)) ∧
    FnIs ((osCfg 6).resLoop 3) (osParams 6)
      (resLoopBody 3 (osLv 6 3) ((osCfg 6).resLoop 3)) :=
  ⟨⟨Data.core541, Program.find?_of_indexOf? (j := 541) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core549, Program.find?_of_indexOf? (j := 549) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_6_4 : FnIs ((osCfg 6).sqLoop 4) (osParams 6)
      (sqLoopBody (osLv 6 4) ((osCfg 6).sqLoop 4)) ∧
    FnIs ((osCfg 6).resLoop 4) (osParams 6)
      (resLoopBody 4 (osLv 6 4) ((osCfg 6).resLoop 4)) :=
  ⟨⟨Data.core542, Program.find?_of_indexOf? (j := 542) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core550, Program.find?_of_indexOf? (j := 550) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osLv_6_5 : FnIs ((osCfg 6).sqLoop 5) (osParams 6)
      (sqLoopBody (osLv 6 5) ((osCfg 6).sqLoop 5)) ∧
    FnIs ((osCfg 6).resLoop 5) (osParams 6)
      (resLoopBody 5 (osLv 6 5) ((osCfg 6).resLoop 5)) :=
  ⟨⟨Data.core543, Program.find?_of_indexOf? (j := 543) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨Data.core551, Program.find?_of_indexOf? (j := 551) (by decide +kernel) rfl,
    by decide +kernel, stmtsEqb_sound (by decide +kernel)⟩⟩

set_option maxRecDepth 100000 in
theorem osData_6 : OsData 6 := by
  have hl : (osCfg 6).levels.length = 6 := by decide +kernel
  have hb : Data.core308.body.drop 0 = (osBody (osCfg 6)).drop 0 :=
    run_step 1100 0 os_run_6_0 <|
    run_step 1100 1100 os_run_6_1 <|
    run_step 1100 2200 os_run_6_2 <|
    run_step 1100 3300 os_run_6_3 <|
    drop_end (o := 4400) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  refine ⟨⟨Data.core308, Program.find?_of_indexOf? (j := 308) (by decide +kernel) rfl,
    by decide +kernel, hb⟩, fun lvl h => ?_⟩
  rw [hl] at h
  interval_cases lvl
  · exact osLv_6_0
  · exact osLv_6_1
  · exact osLv_6_2
  · exact osLv_6_3
  · exact osLv_6_4
  · exact osLv_6_5

end
end LeanVM.Guest.B1.Whir
