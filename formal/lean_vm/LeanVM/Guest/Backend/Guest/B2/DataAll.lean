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
  have h := range_step dataOk_19a (rfl : 1474 + 38 = 1512) h (rfl : 38 + 38 = 76)
  have h := range_step dataOk_18b (rfl : 1436 + 38 = 1474) h (rfl : 38 + 76 = 114)
  have h := range_step dataOk_18a (rfl : 1398 + 38 = 1436) h (rfl : 38 + 114 = 152)
  have h := range_step dataOk_17b (rfl : 1360 + 38 = 1398) h (rfl : 38 + 152 = 190)
  have h := range_step dataOk_17a (rfl : 1322 + 38 = 1360) h (rfl : 38 + 190 = 228)
  have h := range_step dataOk_16b (rfl : 1284 + 38 = 1322) h (rfl : 38 + 228 = 266)
  have h := range_step dataOk_16a (rfl : 1246 + 38 = 1284) h (rfl : 38 + 266 = 304)
  have h := range_step dataOk_15b (rfl : 1208 + 38 = 1246) h (rfl : 38 + 304 = 342)
  have h := range_step dataOk_15a (rfl : 1170 + 38 = 1208) h (rfl : 38 + 342 = 380)
  have h := range_step dataOk_14b (rfl : 1132 + 38 = 1170) h (rfl : 38 + 380 = 418)
  have h := range_step dataOk_14a (rfl : 1093 + 39 = 1132) h (rfl : 39 + 418 = 457)
  have h := range_step dataOk_13b (rfl : 1054 + 39 = 1093) h (rfl : 39 + 457 = 496)
  have h := range_step dataOk_13a (rfl : 1015 + 39 = 1054) h (rfl : 39 + 496 = 535)
  have h := range_step dataOk_12b (rfl : 976 + 39 = 1015) h (rfl : 39 + 535 = 574)
  have h := range_step dataOk_12a (rfl : 937 + 39 = 976) h (rfl : 39 + 574 = 613)
  have h := range_step dataOk_11b (rfl : 898 + 39 = 937) h (rfl : 39 + 613 = 652)
  have h := range_step dataOk_11a (rfl : 859 + 39 = 898) h (rfl : 39 + 652 = 691)
  have h := range_step dataOk_10b (rfl : 820 + 39 = 859) h (rfl : 39 + 691 = 730)
  have h := range_step dataOk_10a (rfl : 781 + 39 = 820) h (rfl : 39 + 730 = 769)
  have h := range_step dataOk_09b (rfl : 742 + 39 = 781) h (rfl : 39 + 769 = 808)
  have h := range_step dataOk_09a (rfl : 703 + 39 = 742) h (rfl : 39 + 808 = 847)
  have h := range_step dataOk_08b (rfl : 664 + 39 = 703) h (rfl : 39 + 847 = 886)
  have h := range_step dataOk_08a (rfl : 625 + 39 = 664) h (rfl : 39 + 886 = 925)
  have h := range_step dataOk_07b (rfl : 586 + 39 = 625) h (rfl : 39 + 925 = 964)
  have h := range_step dataOk_07a (rfl : 547 + 39 = 586) h (rfl : 39 + 964 = 1003)
  have h := range_step dataOk_06b (rfl : 508 + 39 = 547) h (rfl : 39 + 1003 = 1042)
  have h := range_step dataOk_06a (rfl : 469 + 39 = 508) h (rfl : 39 + 1042 = 1081)
  have h := range_step dataOk_05b (rfl : 430 + 39 = 469) h (rfl : 39 + 1081 = 1120)
  have h := range_step dataOk_05a (rfl : 391 + 39 = 430) h (rfl : 39 + 1120 = 1159)
  have h := range_step dataOk_04b (rfl : 352 + 39 = 391) h (rfl : 39 + 1159 = 1198)
  have h := range_step dataOk_04a (rfl : 313 + 39 = 352) h (rfl : 39 + 1198 = 1237)
  have h := range_step dataOk_03b (rfl : 274 + 39 = 313) h (rfl : 39 + 1237 = 1276)
  have h := range_step dataOk_03a (rfl : 235 + 39 = 274) h (rfl : 39 + 1276 = 1315)
  have h := range_step dataOk_02b (rfl : 196 + 39 = 235) h (rfl : 39 + 1315 = 1354)
  have h := range_step dataOk_02a (rfl : 157 + 39 = 196) h (rfl : 39 + 1354 = 1393)
  have h := range_step dataOk_01b (rfl : 118 + 39 = 157) h (rfl : 39 + 1393 = 1432)
  have h := range_step dataOk_01a (rfl : 79 + 39 = 118) h (rfl : 39 + 1432 = 1471)
  have h := range_step dataOk_00b (rfl : 40 + 39 = 79) h (rfl : 39 + 1471 = 1510)
  have h := range_step dataOk_00a (rfl : 1 + 39 = 40) h (rfl : 39 + 1510 = 1549)
  exact List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨h1, by simpa [nFns] using h2⟩)

end
end LeanVM.Guest.Backend.B2
