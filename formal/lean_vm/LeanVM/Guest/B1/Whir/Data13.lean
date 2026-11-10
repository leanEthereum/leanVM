/-
  LeanVM.Guest.B1.Whir.Data13

  `open_stacked__L13` is its template, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Size 13

`osData_13 : OsData 13`: the function found by name (its index in the core IR checked by the
kernel), its body equal to the template (`stmtsEqb_sound`), the body in runs of 1100 statements,
each its own kernel evaluation (`run_step`), to bound the kernel's memory.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem os_run_13_0 : stmtsEqb ((Data.core323.body.drop 0).take 1100)
    (((osBody (osCfg 13)).drop 0).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_13_1 : stmtsEqb ((Data.core323.body.drop 1100).take 1100)
    (((osBody (osCfg 13)).drop 1100).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem os_run_13_2 : stmtsEqb ((Data.core323.body.drop 2200).take 1100)
    (((osBody (osCfg 13)).drop 2200).take 1100) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osData_13 : OsData 13 := by
  have hb : Data.core323.body.drop 0 = (osBody (osCfg 13)).drop 0 :=
    run_step 1100 0 os_run_13_0 <|
    run_step 1100 1100 os_run_13_1 <|
    run_step 1100 2200 os_run_13_2 <|
    drop_end (o := 3300) (by decide +kernel) (by decide +kernel)
  rw [List.drop_zero, List.drop_zero] at hb
  exact ⟨Data.core323, Program.find?_of_indexOf? (j := 323) (by decide +kernel) rfl, by decide +kernel, hb⟩

end
end LeanVM.Guest.B1.Whir
