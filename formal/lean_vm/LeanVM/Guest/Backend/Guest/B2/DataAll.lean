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
  have h := dataOk_19b
  have h := range_step dataOk_19a (rfl : 1540 + 31 = 1571) h (rfl : 31 + 31 = 62)
  have h := range_step dataOk_18b (rfl : 1500 + 40 = 1540) h (rfl : 40 + 62 = 102)
  have h := range_step dataOk_18a (rfl : 1459 + 41 = 1500) h (rfl : 41 + 102 = 143)
  have h := range_step dataOk_17b (rfl : 1419 + 40 = 1459) h (rfl : 40 + 143 = 183)
  have h := range_step dataOk_17a (rfl : 1378 + 41 = 1419) h (rfl : 41 + 183 = 224)
  have h := range_step dataOk_16b (rfl : 1338 + 40 = 1378) h (rfl : 40 + 224 = 264)
  have h := range_step dataOk_16a (rfl : 1297 + 41 = 1338) h (rfl : 41 + 264 = 305)
  have h := range_step dataOk_15b (rfl : 1257 + 40 = 1297) h (rfl : 40 + 305 = 345)
  have h := range_step dataOk_15a (rfl : 1216 + 41 = 1257) h (rfl : 41 + 345 = 386)
  have h := range_step dataOk_14b (rfl : 1176 + 40 = 1216) h (rfl : 40 + 386 = 426)
  have h := range_step dataOk_14a (rfl : 1135 + 41 = 1176) h (rfl : 41 + 426 = 467)
  have h := range_step dataOk_13b (rfl : 1095 + 40 = 1135) h (rfl : 40 + 467 = 507)
  have h := range_step dataOk_13a (rfl : 1054 + 41 = 1095) h (rfl : 41 + 507 = 548)
  have h := range_step dataOk_12b (rfl : 1014 + 40 = 1054) h (rfl : 40 + 548 = 588)
  have h := range_step dataOk_12a (rfl : 973 + 41 = 1014) h (rfl : 41 + 588 = 629)
  have h := range_step dataOk_11b (rfl : 933 + 40 = 973) h (rfl : 40 + 629 = 669)
  have h := range_step dataOk_11a (rfl : 892 + 41 = 933) h (rfl : 41 + 669 = 710)
  have h := range_step dataOk_10b (rfl : 852 + 40 = 892) h (rfl : 40 + 710 = 750)
  have h := range_step dataOk_10a (rfl : 811 + 41 = 852) h (rfl : 41 + 750 = 791)
  have h := range_step dataOk_09b (rfl : 771 + 40 = 811) h (rfl : 40 + 791 = 831)
  have h := range_step dataOk_09a (rfl : 730 + 41 = 771) h (rfl : 41 + 831 = 872)
  have h := range_step dataOk_08b (rfl : 690 + 40 = 730) h (rfl : 40 + 872 = 912)
  have h := range_step dataOk_08a (rfl : 649 + 41 = 690) h (rfl : 41 + 912 = 953)
  have h := range_step dataOk_07b (rfl : 609 + 40 = 649) h (rfl : 40 + 953 = 993)
  have h := range_step dataOk_07a (rfl : 568 + 41 = 609) h (rfl : 41 + 993 = 1034)
  have h := range_step dataOk_06b (rfl : 528 + 40 = 568) h (rfl : 40 + 1034 = 1074)
  have h := range_step dataOk_06a (rfl : 487 + 41 = 528) h (rfl : 41 + 1074 = 1115)
  have h := range_step dataOk_05b (rfl : 447 + 40 = 487) h (rfl : 40 + 1115 = 1155)
  have h := range_step dataOk_05a (rfl : 406 + 41 = 447) h (rfl : 41 + 1155 = 1196)
  have h := range_step dataOk_04b (rfl : 366 + 40 = 406) h (rfl : 40 + 1196 = 1236)
  have h := range_step dataOk_04a (rfl : 325 + 41 = 366) h (rfl : 41 + 1236 = 1277)
  have h := range_step dataOk_03b (rfl : 285 + 40 = 325) h (rfl : 40 + 1277 = 1317)
  have h := range_step dataOk_03a (rfl : 244 + 41 = 285) h (rfl : 41 + 1317 = 1358)
  have h := range_step dataOk_02b (rfl : 204 + 40 = 244) h (rfl : 40 + 1358 = 1398)
  have h := range_step dataOk_02a (rfl : 163 + 41 = 204) h (rfl : 41 + 1398 = 1439)
  have h := range_step dataOk_01b (rfl : 123 + 40 = 163) h (rfl : 40 + 1439 = 1479)
  have h := range_step dataOk_01a (rfl : 82 + 41 = 123) h (rfl : 41 + 1479 = 1520)
  have h := range_step dataOk_00b (rfl : 42 + 40 = 82) h (rfl : 40 + 1520 = 1560)
  have h := range_step dataOk_00a (rfl : 1 + 41 = 42) h (rfl : 41 + 1560 = 1601)
  exact List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨h1, by simpa [nFns] using h2⟩)

end
end LeanVM.Guest.Backend.B2
