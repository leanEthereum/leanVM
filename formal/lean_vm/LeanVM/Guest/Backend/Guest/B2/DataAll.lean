/-
  LeanVM.Guest.Backend.Guest.B2.DataAll

  Every function's certificate data agree with the back end's (`dataOk`, `B2/Eval/D*`).
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Eval.D00
public import LeanVM.Guest.Backend.Guest.B2.Eval.D01
public import LeanVM.Guest.Backend.Guest.B2.Eval.D02
public import LeanVM.Guest.Backend.Guest.B2.Eval.D03
public import LeanVM.Guest.Backend.Guest.B2.Eval.D04
public import LeanVM.Guest.Backend.Guest.B2.Eval.D05
public import LeanVM.Guest.Backend.Guest.B2.Eval.D06
public import LeanVM.Guest.Backend.Guest.B2.Eval.D07
public import LeanVM.Guest.Backend.Guest.B2.Eval.D08
public import LeanVM.Guest.Backend.Guest.B2.Eval.D09
public import LeanVM.Guest.Backend.Guest.B2.Eval.D10
public import LeanVM.Guest.Backend.Guest.B2.Eval.D11
public import LeanVM.Guest.Backend.Guest.B2.Eval.D12
public import LeanVM.Guest.Backend.Guest.B2.Eval.D13
public import LeanVM.Guest.Backend.Guest.B2.Eval.D14
public import LeanVM.Guest.Backend.Guest.B2.Eval.D15
public import LeanVM.Guest.Backend.Guest.B2.Eval.D16
public import LeanVM.Guest.Backend.Guest.B2.Eval.D17
public import LeanVM.Guest.Backend.Guest.B2.Eval.D18
public import LeanVM.Guest.Backend.Guest.B2.Eval.D19
public import LeanVM.Guest.Backend.Sound.Obl.Guest

namespace LeanVM.Guest.Backend.B2

open LeanVM.Guest LeanVM.Guest.Backend.Obl

@[expose] public section

/-- **Every function's certificate data agree with the back end's**: `dataOk j` for
`1 ≤ j < nFns`. -/
theorem dataOk_all {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) : dataOk j = true := by
  have h := dataOk_19
  have h := range_step dataOk_18 (rfl : 1459 + 81 = 1540) h (rfl : 81 + 62 = 143)
  have h := range_step dataOk_17 (rfl : 1378 + 81 = 1459) h (rfl : 81 + 143 = 224)
  have h := range_step dataOk_16 (rfl : 1297 + 81 = 1378) h (rfl : 81 + 224 = 305)
  have h := range_step dataOk_15 (rfl : 1216 + 81 = 1297) h (rfl : 81 + 305 = 386)
  have h := range_step dataOk_14 (rfl : 1135 + 81 = 1216) h (rfl : 81 + 386 = 467)
  have h := range_step dataOk_13 (rfl : 1054 + 81 = 1135) h (rfl : 81 + 467 = 548)
  have h := range_step dataOk_12 (rfl : 973 + 81 = 1054) h (rfl : 81 + 548 = 629)
  have h := range_step dataOk_11 (rfl : 892 + 81 = 973) h (rfl : 81 + 629 = 710)
  have h := range_step dataOk_10 (rfl : 811 + 81 = 892) h (rfl : 81 + 710 = 791)
  have h := range_step dataOk_09 (rfl : 730 + 81 = 811) h (rfl : 81 + 791 = 872)
  have h := range_step dataOk_08 (rfl : 649 + 81 = 730) h (rfl : 81 + 872 = 953)
  have h := range_step dataOk_07 (rfl : 568 + 81 = 649) h (rfl : 81 + 953 = 1034)
  have h := range_step dataOk_06 (rfl : 487 + 81 = 568) h (rfl : 81 + 1034 = 1115)
  have h := range_step dataOk_05 (rfl : 406 + 81 = 487) h (rfl : 81 + 1115 = 1196)
  have h := range_step dataOk_04 (rfl : 325 + 81 = 406) h (rfl : 81 + 1196 = 1277)
  have h := range_step dataOk_03 (rfl : 244 + 81 = 325) h (rfl : 81 + 1277 = 1358)
  have h := range_step dataOk_02 (rfl : 163 + 81 = 244) h (rfl : 81 + 1358 = 1439)
  have h := range_step dataOk_01 (rfl : 82 + 81 = 163) h (rfl : 81 + 1439 = 1520)
  have h := range_step dataOk_00 (rfl : 1 + 81 = 82) h (rfl : 81 + 1520 = 1601)
  exact List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨h1, by simpa [nFns] using h2⟩)

end
end LeanVM.Guest.Backend.B2
