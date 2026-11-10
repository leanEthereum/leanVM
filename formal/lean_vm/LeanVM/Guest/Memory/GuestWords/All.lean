/-
  LeanVM.Guest.Memory.GuestWords.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestWords.Part00
public import LeanVM.Guest.Memory.GuestWords.Part01
public import LeanVM.Guest.Memory.GuestWords.Part02
public import LeanVM.Guest.Memory.GuestWords.Part03
public import LeanVM.Guest.Memory.GuestWords.Part04
public import LeanVM.Guest.Memory.GuestWords.Part05
public import LeanVM.Guest.Memory.GuestWords.Part06
public import LeanVM.Guest.Memory.GuestWords.Part07
public import LeanVM.Guest.Memory.GuestWords.Part08
public import LeanVM.Guest.Memory.GuestWords.Part09
public import LeanVM.Guest.Memory.GuestWords.Part10
public import LeanVM.Guest.Memory.GuestWords.Part11
public import LeanVM.Guest.Memory.GuestWords.Part12
public import LeanVM.Guest.Memory.GuestWords.Part13
public import LeanVM.Guest.Memory.GuestWords.Part14
public import LeanVM.Guest.Memory.GuestWords.Part15
public import LeanVM.Guest.Memory.GuestWords.Part16
public import LeanVM.Guest.Memory.GuestWords.Part17
public import LeanVM.Guest.Memory.GuestWords.Part18
public import LeanVM.Guest.Memory.GuestWords.Part19
public import LeanVM.Guest.Memory.GuestWords.Part20
public import LeanVM.Guest.Memory.GuestWords.Part21
public import LeanVM.Guest.Memory.GuestWords.Part22
public import LeanVM.Guest.Memory.GuestWords.Part23
public import LeanVM.Guest.Memory.GuestWords.Part24
public import LeanVM.Guest.Memory.GuestWords.Part25
public import LeanVM.Guest.Memory.GuestWords.Part26
public import LeanVM.Guest.Memory.GuestWords.Part27
public import LeanVM.Guest.Memory.GuestWords.Part28
public import LeanVM.Guest.Memory.GuestWords.Part29
public import LeanVM.Guest.Memory.GuestWords.Part30
public import LeanVM.Guest.Memory.GuestWords.Part31
public import LeanVM.Guest.Memory.GuestWords.Part32
public import LeanVM.Guest.Memory.GuestWords.Part33
public import LeanVM.Guest.Memory.GuestWords.Part34
public import LeanVM.Guest.Memory.GuestWords.Part35
public import LeanVM.Guest.Memory.GuestWords.Part36
public import LeanVM.Guest.Memory.GuestWords.Part37
public import LeanVM.Guest.Memory.GuestWords.Part38
public import LeanVM.Guest.Memory.GuestWords.Part39
public import LeanVM.Guest.Memory.GuestWords.Part40
public import LeanVM.Guest.Memory.GuestWords.Part41
public import LeanVM.Guest.Memory.GuestWords.Part42
public import LeanVM.Guest.Memory.GuestWords.Part43
public import LeanVM.Guest.Memory.GuestWords.Part44
public import LeanVM.Guest.Memory.GuestWords.Part45
public import LeanVM.Guest.Memory.GuestWords.Part46
public import LeanVM.Guest.Memory.GuestWords.Part47
public import LeanVM.Guest.Memory.GuestWords.Part48
public import LeanVM.Guest.Memory.GuestWords.Part49
public import LeanVM.Guest.Memory.GuestWords.Part50
public import LeanVM.Guest.Memory.GuestWords.Part51
public import LeanVM.Guest.Memory.GuestWords.Part52
public import LeanVM.Guest.Memory.GuestWords.Part53
public import LeanVM.Guest.Memory.GuestWords.Part54
public import LeanVM.Guest.Memory.GuestWords.Part55
public import LeanVM.Guest.Memory.GuestWords.Part56
public import LeanVM.Guest.Memory.GuestWords.Part57
public import LeanVM.Guest.Memory.GuestWords.Part58
public import LeanVM.Guest.Memory.GuestWords.Part59
public import LeanVM.Guest.Memory.GuestWords.Part60
public import LeanVM.Guest.Memory.GuestWords.Part61
public import LeanVM.Guest.Memory.GuestWords.Part62

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wchkIdx_19 : wchkIdx 19 = true := by
  have hb : blockB (wlookJ 19) (womLookJ 19) true [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 96 96 wsplit_19_0.1 rfl wsplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 96), wsplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 96), wsplit_19_96]
    rfl
  exact wchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_331 : wchkIdx 331 = true := by
  have hb : blockB (wlookJ 331) (womLookJ 331) true [(.n 10, 1536), (.n 12, 384), (.n 14, 20), (.n 16, 8), (.n 18, 18), (.n 20, 54), (.n 22, 4), (.n 24, 4), (.n 26, 32), (.n 28, 176), (.n 30, 8), (.n 32, 339), (.n 34, 339), (.n 98, 8), (.n 155, 165), (.n 160, 1), (.n 161, 32), (.n 213, 109), (.n 281, 6), (.n 338, 165), (.n 347, 1), (.n 348, 7), (.n 405, 55), (.n 471, 6), (.n 528, 165), (.n 537, 1), (.n 538, 4), (.n 595, 32), (.n 665, 165), (.n 674, 1), (.n 675, 3), (.n 689, 20), (.n 758, 24), (.n 760, 5), (.n 922, 88), (.n 924, 4), (.n 926, 4), (.n 1210, 8), (.n 1214, 56), (.n 1221, 0), (.n 1222, 27), (.n 1474, 14), (.n 1481, 0), (.n 1482, 6), (.n 2112, 10), (.n 2119, 0), (.n 2120, 4)] Data.core331.params Data.core331.name ([], []) Data.core331.body = some (⟨211659, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core331.body)]
    rw [blockB_dropE _ _ _ 0 721 721 wsplit_331_0.1 rfl wsplit_331_0.2.2,
      ← blockR_eq ((Data.core331.body.drop 0).take 721), wsplit_331_0.2.1]
    rw [blockB_dropE _ _ _ 721 721 1442 wsplit_331_721.1 rfl wsplit_331_721.2.2,
      ← blockR_eq ((Data.core331.body.drop 721).take 721), wsplit_331_721.2.1]
    rw [blockB_dropE _ _ _ 1442 721 2163 wsplit_331_1442.1 rfl wsplit_331_1442.2.2,
      ← blockR_eq ((Data.core331.body.drop 1442).take 721), wsplit_331_1442.2.1]
    rw [← blockR_eq (Data.core331.body.drop 2163), wsplit_331_2163]
    rfl
  exact wchkIdx_of_split (fn := Data.core331) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_332 : wchkIdx 332 = true := by
  have hb : blockB (wlookJ 332) (womLookJ 332) true [(.n 10, 1536), (.n 12, 384), (.n 14, 36), (.n 16, 8), (.n 18, 18), (.n 20, 54), (.n 22, 4), (.n 24, 4), (.n 26, 32), (.n 28, 176), (.n 30, 8), (.n 32, 329), (.n 34, 329), (.n 98, 8), (.n 155, 160), (.n 160, 1), (.n 161, 31), (.n 213, 108), (.n 281, 6), (.n 338, 160), (.n 347, 1), (.n 348, 8), (.n 405, 55), (.n 471, 6), (.n 528, 160), (.n 537, 1), (.n 538, 4), (.n 595, 32), (.n 665, 160), (.n 674, 1), (.n 675, 3), (.n 689, 36), (.n 806, 23), (.n 808, 5), (.n 979, 88), (.n 981, 4), (.n 983, 4), (.n 1291, 8), (.n 1295, 56), (.n 1302, 0), (.n 1303, 27), (.n 1442, 14), (.n 1449, 0), (.n 1450, 6), (.n 2122, 10), (.n 2129, 0), (.n 2130, 4)] Data.core332.params Data.core332.name ([], []) Data.core332.body = some (⟨214813, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core332.body)]
    rw [blockB_dropE _ _ _ 0 721 721 wsplit_332_0.1 rfl wsplit_332_0.2.2,
      ← blockR_eq ((Data.core332.body.drop 0).take 721), wsplit_332_0.2.1]
    rw [blockB_dropE _ _ _ 721 721 1442 wsplit_332_721.1 rfl wsplit_332_721.2.2,
      ← blockR_eq ((Data.core332.body.drop 721).take 721), wsplit_332_721.2.1]
    rw [blockB_dropE _ _ _ 1442 721 2163 wsplit_332_1442.1 rfl wsplit_332_1442.2.2,
      ← blockR_eq ((Data.core332.body.drop 1442).take 721), wsplit_332_1442.2.1]
    rw [← blockR_eq (Data.core332.body.drop 2163), wsplit_332_2163]
    rfl
  exact wchkIdx_of_split (fn := Data.core332) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_333 : wchkIdx 333 = true := by
  have hb : blockB (wlookJ 333) (womLookJ 333) true [(.n 10, 1664), (.n 12, 416), (.n 14, 8), (.n 16, 10), (.n 18, 22), (.n 20, 66), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 220), (.n 30, 10), (.n 32, 361), (.n 34, 361), (.n 98, 8), (.n 155, 190), (.n 160, 1), (.n 161, 37), (.n 213, 108), (.n 281, 6), (.n 338, 190), (.n 347, 1), (.n 348, 8), (.n 405, 55), (.n 471, 6), (.n 528, 190), (.n 537, 1), (.n 538, 5), (.n 595, 32), (.n 657, 6), (.n 714, 190), (.n 723, 1), (.n 724, 3), (.n 781, 23), (.n 853, 190), (.n 862, 1), (.n 863, 3), (.n 877, 8), (.n 910, 20), (.n 912, 5), (.n 1064, 110), (.n 1066, 5), (.n 1068, 5), (.n 1446, 10), (.n 1450, 56), (.n 1457, 0), (.n 1458, 27), (.n 1603, 14), (.n 1610, 0), (.n 1611, 6), (.n 2325, 10), (.n 2332, 0), (.n 2333, 4), (.n 2347, 6), (.n 2354, 0), (.n 2355, 2)] Data.core333.params Data.core333.name ([], []) Data.core333.body = some (⟨224917, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core333.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_333_0.1 rfl wsplit_333_0.2.2,
      ← blockR_eq ((Data.core333.body.drop 0).take 619), wsplit_333_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_333_619.1 rfl wsplit_333_619.2.2,
      ← blockR_eq ((Data.core333.body.drop 619).take 619), wsplit_333_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_333_1238.1 rfl wsplit_333_1238.2.2,
      ← blockR_eq ((Data.core333.body.drop 1238).take 619), wsplit_333_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_333_1857.1 rfl wsplit_333_1857.2.2,
      ← blockR_eq ((Data.core333.body.drop 1857).take 619), wsplit_333_1857.2.1]
    rw [blockB_dropE _ _ _ 2476 619 3095 wsplit_333_2476.1 rfl wsplit_333_2476.2.2,
      ← blockR_eq ((Data.core333.body.drop 2476).take 619), wsplit_333_2476.2.1]
    rw [← blockR_eq (Data.core333.body.drop 3095), wsplit_333_3095]
    rfl
  exact wchkIdx_of_split (fn := Data.core333) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_334 : wchkIdx 334 = true := by
  have hb : blockB (wlookJ 334) (womLookJ 334) true [(.n 10, 1664), (.n 12, 416), (.n 14, 12), (.n 16, 10), (.n 18, 22), (.n 20, 66), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 220), (.n 30, 10), (.n 32, 369), (.n 34, 369), (.n 98, 8), (.n 155, 190), (.n 160, 1), (.n 161, 37), (.n 213, 108), (.n 281, 6), (.n 338, 190), (.n 347, 1), (.n 348, 10), (.n 405, 55), (.n 471, 6), (.n 528, 190), (.n 537, 1), (.n 538, 5), (.n 595, 32), (.n 657, 6), (.n 714, 190), (.n 723, 1), (.n 724, 4), (.n 781, 23), (.n 853, 190), (.n 862, 1), (.n 863, 3), (.n 877, 12), (.n 922, 19), (.n 924, 5), (.n 1085, 110), (.n 1087, 5), (.n 1089, 5), (.n 1499, 10), (.n 1503, 56), (.n 1510, 0), (.n 1511, 27), (.n 1662, 14), (.n 1669, 0), (.n 1670, 6), (.n 2426, 10), (.n 2433, 0), (.n 2434, 4), (.n 2448, 6), (.n 2455, 0), (.n 2456, 2)] Data.core334.params Data.core334.name ([], []) Data.core334.body = some (⟨229721, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core334.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_334_0.1 rfl wsplit_334_0.2.2,
      ← blockR_eq ((Data.core334.body.drop 0).take 619), wsplit_334_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_334_619.1 rfl wsplit_334_619.2.2,
      ← blockR_eq ((Data.core334.body.drop 619).take 619), wsplit_334_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_334_1238.1 rfl wsplit_334_1238.2.2,
      ← blockR_eq ((Data.core334.body.drop 1238).take 619), wsplit_334_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_334_1857.1 rfl wsplit_334_1857.2.2,
      ← blockR_eq ((Data.core334.body.drop 1857).take 619), wsplit_334_1857.2.1]
    rw [blockB_dropE _ _ _ 2476 619 3095 wsplit_334_2476.1 rfl wsplit_334_2476.2.2,
      ← blockR_eq ((Data.core334.body.drop 2476).take 619), wsplit_334_2476.2.1]
    rw [← blockR_eq (Data.core334.body.drop 3095), wsplit_334_3095]
    rfl
  exact wchkIdx_of_split (fn := Data.core334) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_335 : wchkIdx 335 = true := by
  have hb : blockB (wlookJ 335) (womLookJ 335) true [(.n 10, 1664), (.n 12, 416), (.n 14, 20), (.n 16, 10), (.n 18, 22), (.n 20, 66), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 220), (.n 30, 10), (.n 32, 367), (.n 34, 367), (.n 98, 8), (.n 155, 190), (.n 160, 1), (.n 161, 37), (.n 213, 108), (.n 281, 6), (.n 338, 190), (.n 347, 1), (.n 348, 10), (.n 405, 55), (.n 471, 6), (.n 528, 190), (.n 537, 1), (.n 538, 6), (.n 595, 32), (.n 657, 6), (.n 714, 190), (.n 723, 1), (.n 724, 4), (.n 781, 22), (.n 852, 190), (.n 861, 1), (.n 862, 3), (.n 876, 20), (.n 945, 18), (.n 947, 5), (.n 1117, 110), (.n 1119, 5), (.n 1121, 5), (.n 1563, 10), (.n 1567, 56), (.n 1574, 0), (.n 1575, 27), (.n 1732, 14), (.n 1739, 0), (.n 1740, 6), (.n 2538, 10), (.n 2545, 0), (.n 2546, 4), (.n 2560, 6), (.n 2567, 0), (.n 2568, 2)] Data.core335.params Data.core335.name ([], []) Data.core335.body = some (⟨235443, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core335.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_335_0.1 rfl wsplit_335_0.2.2,
      ← blockR_eq ((Data.core335.body.drop 0).take 619), wsplit_335_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_335_619.1 rfl wsplit_335_619.2.2,
      ← blockR_eq ((Data.core335.body.drop 619).take 619), wsplit_335_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_335_1238.1 rfl wsplit_335_1238.2.2,
      ← blockR_eq ((Data.core335.body.drop 1238).take 619), wsplit_335_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_335_1857.1 rfl wsplit_335_1857.2.2,
      ← blockR_eq ((Data.core335.body.drop 1857).take 619), wsplit_335_1857.2.1]
    rw [blockB_dropE _ _ _ 2476 619 3095 wsplit_335_2476.1 rfl wsplit_335_2476.2.2,
      ← blockR_eq ((Data.core335.body.drop 2476).take 619), wsplit_335_2476.2.1]
    rw [← blockR_eq (Data.core335.body.drop 3095), wsplit_335_3095]
    rfl
  exact wchkIdx_of_split (fn := Data.core335) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_336 : wchkIdx 336 = true := by
  have hb : blockB (wlookJ 336) (womLookJ 336) true [(.n 10, 1664), (.n 12, 416), (.n 14, 36), (.n 16, 10), (.n 18, 22), (.n 20, 66), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 220), (.n 30, 10), (.n 32, 361), (.n 34, 361), (.n 98, 8), (.n 155, 225), (.n 160, 1), (.n 161, 44), (.n 213, 108), (.n 281, 6), (.n 338, 225), (.n 347, 1), (.n 348, 10), (.n 405, 55), (.n 471, 6), (.n 528, 225), (.n 537, 1), (.n 538, 6), (.n 595, 31), (.n 660, 6), (.n 717, 225), (.n 726, 1), (.n 727, 4), (.n 784, 22), (.n 855, 225), (.n 864, 1), (.n 865, 3), (.n 879, 36), (.n 996, 18), (.n 998, 5), (.n 1177, 110), (.n 1179, 5), (.n 1181, 5), (.n 1655, 10), (.n 1659, 56), (.n 1666, 0), (.n 1667, 27), (.n 1830, 14), (.n 1837, 0), (.n 1838, 6), (.n 2678, 8), (.n 2685, 0), (.n 2686, 3), (.n 3358, 6), (.n 3365, 0), (.n 3366, 2)] Data.core336.params Data.core336.name ([], []) Data.core336.body = some (⟨241053, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core336.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_336_0.1 rfl wsplit_336_0.2.2,
      ← blockR_eq ((Data.core336.body.drop 0).take 619), wsplit_336_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_336_619.1 rfl wsplit_336_619.2.2,
      ← blockR_eq ((Data.core336.body.drop 619).take 619), wsplit_336_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_336_1238.1 rfl wsplit_336_1238.2.2,
      ← blockR_eq ((Data.core336.body.drop 1238).take 619), wsplit_336_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_336_1857.1 rfl wsplit_336_1857.2.2,
      ← blockR_eq ((Data.core336.body.drop 1857).take 619), wsplit_336_1857.2.1]
    rw [blockB_dropE _ _ _ 2476 619 3095 wsplit_336_2476.1 rfl wsplit_336_2476.2.2,
      ← blockR_eq ((Data.core336.body.drop 2476).take 619), wsplit_336_2476.2.1]
    rw [blockB_dropE _ _ _ 3095 619 3714 wsplit_336_3095.1 rfl wsplit_336_3095.2.2,
      ← blockR_eq ((Data.core336.body.drop 3095).take 619), wsplit_336_3095.2.1]
    rw [blockB_dropE _ _ _ 3714 619 4333 wsplit_336_3714.1 rfl wsplit_336_3714.2.2,
      ← blockR_eq ((Data.core336.body.drop 3714).take 619), wsplit_336_3714.2.1]
    rw [← blockR_eq (Data.core336.body.drop 4333), wsplit_336_4333]
    rfl
  exact wchkIdx_of_split (fn := Data.core336) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_337 : wchkIdx 337 = true := by
  have hb : blockB (wlookJ 337) (womLookJ 337) true [(.n 10, 1728), (.n 12, 432), (.n 14, 8), (.n 16, 12), (.n 18, 26), (.n 20, 78), (.n 22, 6), (.n 24, 6), (.n 26, 48), (.n 28, 264), (.n 30, 12), (.n 32, 374), (.n 34, 374), (.n 98, 8), (.n 155, 225), (.n 160, 1), (.n 161, 44), (.n 213, 108), (.n 281, 6), (.n 338, 225), (.n 347, 1), (.n 348, 11), (.n 405, 55), (.n 471, 6), (.n 528, 225), (.n 537, 1), (.n 538, 6), (.n 595, 31), (.n 660, 6), (.n 717, 225), (.n 726, 1), (.n 727, 4), (.n 784, 22), (.n 847, 6), (.n 904, 225), (.n 913, 1), (.n 914, 3), (.n 971, 18), (.n 1041, 225), (.n 1050, 1), (.n 1051, 3), (.n 1065, 8), (.n 1098, 16), (.n 1100, 5), (.n 1260, 132), (.n 1262, 6), (.n 1264, 6), (.n 1816, 12), (.n 1820, 56), (.n 1827, 0), (.n 1828, 27), (.n 1997, 14), (.n 2004, 0), (.n 2005, 6), (.n 2887, 8), (.n 2894, 0), (.n 2895, 3), (.n 3609, 6), (.n 3616, 0), (.n 3617, 2), (.n 4087, 6), (.n 4094, 0), (.n 4095, 2)] Data.core337.params Data.core337.name ([], []) Data.core337.body = some (⟨248808, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core337.body)]
    rw [blockB_dropE _ _ _ 0 542 542 wsplit_337_0.1 rfl wsplit_337_0.2.2,
      ← blockR_eq ((Data.core337.body.drop 0).take 542), wsplit_337_0.2.1]
    rw [blockB_dropE _ _ _ 542 542 1084 wsplit_337_542.1 rfl wsplit_337_542.2.2,
      ← blockR_eq ((Data.core337.body.drop 542).take 542), wsplit_337_542.2.1]
    rw [blockB_dropE _ _ _ 1084 542 1626 wsplit_337_1084.1 rfl wsplit_337_1084.2.2,
      ← blockR_eq ((Data.core337.body.drop 1084).take 542), wsplit_337_1084.2.1]
    rw [blockB_dropE _ _ _ 1626 542 2168 wsplit_337_1626.1 rfl wsplit_337_1626.2.2,
      ← blockR_eq ((Data.core337.body.drop 1626).take 542), wsplit_337_1626.2.1]
    rw [blockB_dropE _ _ _ 2168 542 2710 wsplit_337_2168.1 rfl wsplit_337_2168.2.2,
      ← blockR_eq ((Data.core337.body.drop 2168).take 542), wsplit_337_2168.2.1]
    rw [blockB_dropE _ _ _ 2710 542 3252 wsplit_337_2710.1 rfl wsplit_337_2710.2.2,
      ← blockR_eq ((Data.core337.body.drop 2710).take 542), wsplit_337_2710.2.1]
    rw [blockB_dropE _ _ _ 3252 542 3794 wsplit_337_3252.1 rfl wsplit_337_3252.2.2,
      ← blockR_eq ((Data.core337.body.drop 3252).take 542), wsplit_337_3252.2.1]
    rw [blockB_dropE _ _ _ 3794 542 4336 wsplit_337_3794.1 rfl wsplit_337_3794.2.2,
      ← blockR_eq ((Data.core337.body.drop 3794).take 542), wsplit_337_3794.2.1]
    rw [blockB_dropE _ _ _ 4336 542 4878 wsplit_337_4336.1 rfl wsplit_337_4336.2.2,
      ← blockR_eq ((Data.core337.body.drop 4336).take 542), wsplit_337_4336.2.1]
    rw [← blockR_eq (Data.core337.body.drop 4878), wsplit_337_4878]
    rfl
  exact wchkIdx_of_split (fn := Data.core337) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_338 : wchkIdx 338 = true := by
  have hb : blockB (wlookJ 338) (womLookJ 338) true [(.n 10, 1024), (.n 12, 256), (.n 14, 20), (.n 16, 8), (.n 18, 18), (.n 20, 54), (.n 22, 4), (.n 24, 4), (.n 26, 32), (.n 28, 176), (.n 30, 8), (.n 32, 217), (.n 34, 217), (.n 98, 8), (.n 155, 85), (.n 160, 1), (.n 161, 16), (.n 213, 54), (.n 280, 6), (.n 337, 85), (.n 346, 1), (.n 347, 7), (.n 404, 44), (.n 468, 6), (.n 525, 85), (.n 534, 1), (.n 535, 4), (.n 592, 28), (.n 663, 85), (.n 672, 1), (.n 673, 3), (.n 687, 20), (.n 756, 22), (.n 758, 5), (.n 920, 88), (.n 922, 4), (.n 924, 4), (.n 1208, 8), (.n 1212, 28), (.n 1219, 0), (.n 1220, 13), (.n 1829, 12), (.n 1836, 0), (.n 1837, 5), (.n 2203, 8), (.n 2210, 0), (.n 2211, 3)] Data.core338.params Data.core338.name ([], []) Data.core338.body = some (⟨130305, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core338.body)]
    rw [blockB_dropE _ _ _ 0 721 721 wsplit_338_0.1 rfl wsplit_338_0.2.2,
      ← blockR_eq ((Data.core338.body.drop 0).take 721), wsplit_338_0.2.1]
    rw [blockB_dropE _ _ _ 721 721 1442 wsplit_338_721.1 rfl wsplit_338_721.2.2,
      ← blockR_eq ((Data.core338.body.drop 721).take 721), wsplit_338_721.2.1]
    rw [blockB_dropE _ _ _ 1442 721 2163 wsplit_338_1442.1 rfl wsplit_338_1442.2.2,
      ← blockR_eq ((Data.core338.body.drop 1442).take 721), wsplit_338_1442.2.1]
    rw [blockB_dropE _ _ _ 2163 721 2884 wsplit_338_2163.1 rfl wsplit_338_2163.2.2,
      ← blockR_eq ((Data.core338.body.drop 2163).take 721), wsplit_338_2163.2.1]
    rw [← blockR_eq (Data.core338.body.drop 2884), wsplit_338_2884]
    rfl
  exact wchkIdx_of_split (fn := Data.core338) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_339 : wchkIdx 339 = true := by
  have hb : blockB (wlookJ 339) (womLookJ 339) true [(.n 10, 1024), (.n 12, 256), (.n 14, 36), (.n 16, 8), (.n 18, 18), (.n 20, 54), (.n 22, 4), (.n 24, 4), (.n 26, 32), (.n 28, 176), (.n 30, 8), (.n 32, 215), (.n 34, 215), (.n 98, 8), (.n 155, 100), (.n 160, 1), (.n 161, 19), (.n 213, 54), (.n 280, 6), (.n 337, 100), (.n 346, 1), (.n 347, 7), (.n 404, 44), (.n 468, 6), (.n 525, 100), (.n 534, 1), (.n 535, 4), (.n 592, 28), (.n 663, 100), (.n 672, 1), (.n 673, 3), (.n 687, 36), (.n 804, 21), (.n 806, 5), (.n 977, 88), (.n 979, 4), (.n 981, 4), (.n 1289, 8), (.n 1293, 28), (.n 1300, 0), (.n 1301, 13), (.n 1940, 12), (.n 1947, 0), (.n 1948, 5), (.n 2338, 8), (.n 2345, 0), (.n 2346, 3)] Data.core339.params Data.core339.name ([], []) Data.core339.body = some (⟨134356, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core339.body)]
    rw [blockB_dropE _ _ _ 0 721 721 wsplit_339_0.1 rfl wsplit_339_0.2.2,
      ← blockR_eq ((Data.core339.body.drop 0).take 721), wsplit_339_0.2.1]
    rw [blockB_dropE _ _ _ 721 721 1442 wsplit_339_721.1 rfl wsplit_339_721.2.2,
      ← blockR_eq ((Data.core339.body.drop 721).take 721), wsplit_339_721.2.1]
    rw [blockB_dropE _ _ _ 1442 721 2163 wsplit_339_1442.1 rfl wsplit_339_1442.2.2,
      ← blockR_eq ((Data.core339.body.drop 1442).take 721), wsplit_339_1442.2.1]
    rw [blockB_dropE _ _ _ 2163 721 2884 wsplit_339_2163.1 rfl wsplit_339_2163.2.2,
      ← blockR_eq ((Data.core339.body.drop 2163).take 721), wsplit_339_2163.2.1]
    rw [← blockR_eq (Data.core339.body.drop 2884), wsplit_339_2884]
    rfl
  exact wchkIdx_of_split (fn := Data.core339) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_340 : wchkIdx 340 = true := by
  have hb : blockB (wlookJ 340) (womLookJ 340) true [(.n 10, 1152), (.n 12, 288), (.n 14, 8), (.n 16, 10), (.n 18, 22), (.n 20, 66), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 220), (.n 30, 10), (.n 32, 235), (.n 34, 235), (.n 98, 8), (.n 155, 100), (.n 160, 1), (.n 161, 19), (.n 213, 54), (.n 280, 6), (.n 337, 100), (.n 346, 1), (.n 347, 8), (.n 404, 44), (.n 468, 6), (.n 525, 100), (.n 534, 1), (.n 535, 4), (.n 592, 28), (.n 655, 6), (.n 712, 100), (.n 721, 1), (.n 722, 3), (.n 779, 21), (.n 850, 100), (.n 859, 1), (.n 860, 3), (.n 874, 8), (.n 907, 18), (.n 909, 5), (.n 1061, 110), (.n 1063, 5), (.n 1065, 5), (.n 1443, 10), (.n 1447, 28), (.n 1454, 0), (.n 1455, 13), (.n 2124, 12), (.n 2131, 0), (.n 2132, 5), (.n 2546, 8), (.n 2553, 0), (.n 2554, 3), (.n 2872, 6), (.n 2879, 0), (.n 2880, 2)] Data.core340.params Data.core340.name ([], []) Data.core340.body = some (⟨143949, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core340.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_340_0.1 rfl wsplit_340_0.2.2,
      ← blockR_eq ((Data.core340.body.drop 0).take 619), wsplit_340_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_340_619.1 rfl wsplit_340_619.2.2,
      ← blockR_eq ((Data.core340.body.drop 619).take 619), wsplit_340_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_340_1238.1 rfl wsplit_340_1238.2.2,
      ← blockR_eq ((Data.core340.body.drop 1238).take 619), wsplit_340_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_340_1857.1 rfl wsplit_340_1857.2.2,
      ← blockR_eq ((Data.core340.body.drop 1857).take 619), wsplit_340_1857.2.1]
    rw [blockB_dropE _ _ _ 2476 619 3095 wsplit_340_2476.1 rfl wsplit_340_2476.2.2,
      ← blockR_eq ((Data.core340.body.drop 2476).take 619), wsplit_340_2476.2.1]
    rw [← blockR_eq (Data.core340.body.drop 3095), wsplit_340_3095]
    rfl
  exact wchkIdx_of_split (fn := Data.core340) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_341 : wchkIdx 341 = true := by
  have hb : blockB (wlookJ 341) (womLookJ 341) true [(.n 10, 1152), (.n 12, 288), (.n 14, 12), (.n 16, 10), (.n 18, 22), (.n 20, 66), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 220), (.n 30, 10), (.n 32, 234), (.n 34, 234), (.n 98, 8), (.n 155, 100), (.n 160, 1), (.n 161, 19), (.n 213, 54), (.n 280, 6), (.n 337, 100), (.n 346, 1), (.n 347, 8), (.n 404, 44), (.n 468, 6), (.n 525, 100), (.n 534, 1), (.n 535, 5), (.n 592, 28), (.n 655, 6), (.n 712, 100), (.n 721, 1), (.n 722, 3), (.n 779, 21), (.n 850, 100), (.n 859, 1), (.n 860, 3), (.n 874, 12), (.n 919, 17), (.n 921, 5), (.n 1082, 110), (.n 1084, 5), (.n 1086, 5), (.n 1496, 10), (.n 1500, 28), (.n 1507, 0), (.n 1508, 13), (.n 2207, 12), (.n 2214, 0), (.n 2215, 5), (.n 2653, 8), (.n 2660, 0), (.n 2661, 3), (.n 3003, 6), (.n 3010, 0), (.n 3011, 2)] Data.core341.params Data.core341.name ([], []) Data.core341.body = some (⟨146155, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core341.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_341_0.1 rfl wsplit_341_0.2.2,
      ← blockR_eq ((Data.core341.body.drop 0).take 619), wsplit_341_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_341_619.1 rfl wsplit_341_619.2.2,
      ← blockR_eq ((Data.core341.body.drop 619).take 619), wsplit_341_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_341_1238.1 rfl wsplit_341_1238.2.2,
      ← blockR_eq ((Data.core341.body.drop 1238).take 619), wsplit_341_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_341_1857.1 rfl wsplit_341_1857.2.2,
      ← blockR_eq ((Data.core341.body.drop 1857).take 619), wsplit_341_1857.2.1]
    rw [blockB_dropE _ _ _ 2476 619 3095 wsplit_341_2476.1 rfl wsplit_341_2476.2.2,
      ← blockR_eq ((Data.core341.body.drop 2476).take 619), wsplit_341_2476.2.1]
    rw [blockB_dropE _ _ _ 3095 619 3714 wsplit_341_3095.1 rfl wsplit_341_3095.2.2,
      ← blockR_eq ((Data.core341.body.drop 3095).take 619), wsplit_341_3095.2.1]
    rw [← blockR_eq (Data.core341.body.drop 3714), wsplit_341_3714]
    rfl
  exact wchkIdx_of_split (fn := Data.core341) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_342 : wchkIdx 342 = true := by
  have hb : blockB (wlookJ 342) (womLookJ 342) true [(.n 10, 1152), (.n 12, 288), (.n 14, 20), (.n 16, 10), (.n 18, 22), (.n 20, 66), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 220), (.n 30, 10), (.n 32, 233), (.n 34, 233), (.n 98, 8), (.n 155, 115), (.n 160, 1), (.n 161, 22), (.n 213, 54), (.n 280, 6), (.n 337, 115), (.n 346, 1), (.n 347, 8), (.n 404, 44), (.n 468, 6), (.n 525, 115), (.n 534, 1), (.n 535, 5), (.n 592, 28), (.n 655, 6), (.n 712, 115), (.n 721, 1), (.n 722, 4), (.n 779, 20), (.n 849, 115), (.n 858, 1), (.n 859, 3), (.n 873, 20), (.n 942, 17), (.n 944, 5), (.n 1114, 110), (.n 1116, 5), (.n 1118, 5), (.n 1560, 10), (.n 1564, 28), (.n 1571, 0), (.n 1572, 13), (.n 2301, 12), (.n 2308, 0), (.n 2309, 5), (.n 2771, 8), (.n 2778, 0), (.n 2779, 3), (.n 3145, 6), (.n 3152, 0), (.n 3153, 2)] Data.core342.params Data.core342.name ([], []) Data.core342.body = some (⟨149793, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core342.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_342_0.1 rfl wsplit_342_0.2.2,
      ← blockR_eq ((Data.core342.body.drop 0).take 619), wsplit_342_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_342_619.1 rfl wsplit_342_619.2.2,
      ← blockR_eq ((Data.core342.body.drop 619).take 619), wsplit_342_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_342_1238.1 rfl wsplit_342_1238.2.2,
      ← blockR_eq ((Data.core342.body.drop 1238).take 619), wsplit_342_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_342_1857.1 rfl wsplit_342_1857.2.2,
      ← blockR_eq ((Data.core342.body.drop 1857).take 619), wsplit_342_1857.2.1]
    rw [blockB_dropE _ _ _ 2476 619 3095 wsplit_342_2476.1 rfl wsplit_342_2476.2.2,
      ← blockR_eq ((Data.core342.body.drop 2476).take 619), wsplit_342_2476.2.1]
    rw [blockB_dropE _ _ _ 3095 619 3714 wsplit_342_3095.1 rfl wsplit_342_3095.2.2,
      ← blockR_eq ((Data.core342.body.drop 3095).take 619), wsplit_342_3095.2.1]
    rw [← blockR_eq (Data.core342.body.drop 3714), wsplit_342_3714]
    rfl
  exact wchkIdx_of_split (fn := Data.core342) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_343 : wchkIdx 343 = true := by
  have hb : blockB (wlookJ 343) (womLookJ 343) true [(.n 10, 1152), (.n 12, 288), (.n 14, 36), (.n 16, 10), (.n 18, 22), (.n 20, 66), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 220), (.n 30, 10), (.n 32, 227), (.n 34, 227), (.n 98, 8), (.n 155, 115), (.n 160, 1), (.n 161, 22), (.n 213, 54), (.n 280, 6), (.n 337, 115), (.n 346, 1), (.n 347, 9), (.n 404, 44), (.n 468, 6), (.n 525, 115), (.n 534, 1), (.n 535, 5), (.n 592, 28), (.n 655, 6), (.n 712, 115), (.n 721, 1), (.n 722, 4), (.n 779, 20), (.n 849, 115), (.n 858, 1), (.n 859, 3), (.n 873, 36), (.n 990, 17), (.n 992, 5), (.n 1171, 110), (.n 1173, 5), (.n 1175, 5), (.n 1649, 10), (.n 1653, 28), (.n 1660, 0), (.n 1661, 13), (.n 2420, 12), (.n 2427, 0), (.n 2428, 5), (.n 2914, 8), (.n 2921, 0), (.n 2922, 3), (.n 3312, 6), (.n 3319, 0), (.n 3320, 2)] Data.core343.params Data.core343.name ([], []) Data.core343.body = some (⟨153375, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core343.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_343_0.1 rfl wsplit_343_0.2.2,
      ← blockR_eq ((Data.core343.body.drop 0).take 619), wsplit_343_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_343_619.1 rfl wsplit_343_619.2.2,
      ← blockR_eq ((Data.core343.body.drop 619).take 619), wsplit_343_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_343_1238.1 rfl wsplit_343_1238.2.2,
      ← blockR_eq ((Data.core343.body.drop 1238).take 619), wsplit_343_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_343_1857.1 rfl wsplit_343_1857.2.2,
      ← blockR_eq ((Data.core343.body.drop 1857).take 619), wsplit_343_1857.2.1]
    rw [blockB_dropE _ _ _ 2476 619 3095 wsplit_343_2476.1 rfl wsplit_343_2476.2.2,
      ← blockR_eq ((Data.core343.body.drop 2476).take 619), wsplit_343_2476.2.1]
    rw [blockB_dropE _ _ _ 3095 619 3714 wsplit_343_3095.1 rfl wsplit_343_3095.2.2,
      ← blockR_eq ((Data.core343.body.drop 3095).take 619), wsplit_343_3095.2.1]
    rw [← blockR_eq (Data.core343.body.drop 3714), wsplit_343_3714]
    rfl
  exact wchkIdx_of_split (fn := Data.core343) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_344 : wchkIdx 344 = true := by
  have hb : blockB (wlookJ 344) (womLookJ 344) true [(.n 10, 1152), (.n 12, 288), (.n 14, 8), (.n 16, 12), (.n 18, 26), (.n 20, 78), (.n 22, 6), (.n 24, 6), (.n 26, 48), (.n 28, 264), (.n 30, 12), (.n 32, 245), (.n 34, 245), (.n 98, 8), (.n 155, 115), (.n 160, 1), (.n 161, 22), (.n 213, 54), (.n 280, 6), (.n 337, 115), (.n 346, 1), (.n 347, 9), (.n 404, 44), (.n 468, 6), (.n 525, 115), (.n 534, 1), (.n 535, 6), (.n 592, 28), (.n 655, 6), (.n 712, 115), (.n 721, 1), (.n 722, 4), (.n 779, 20), (.n 841, 6), (.n 898, 115), (.n 907, 1), (.n 908, 3), (.n 965, 16), (.n 1034, 115), (.n 1043, 1), (.n 1044, 3), (.n 1058, 8), (.n 1091, 15), (.n 1093, 5), (.n 1253, 132), (.n 1255, 6), (.n 1257, 6), (.n 1809, 12), (.n 1813, 28), (.n 1820, 0), (.n 1821, 13), (.n 2610, 12), (.n 2617, 0), (.n 2618, 5), (.n 3128, 8), (.n 3135, 0), (.n 3136, 3), (.n 3550, 6), (.n 3557, 0), (.n 3558, 2), (.n 3876, 6), (.n 3883, 0), (.n 3884, 2)] Data.core344.params Data.core344.name ([], []) Data.core344.body = some (⟨160243, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core344.body)]
    rw [blockB_dropE _ _ _ 0 542 542 wsplit_344_0.1 rfl wsplit_344_0.2.2,
      ← blockR_eq ((Data.core344.body.drop 0).take 542), wsplit_344_0.2.1]
    rw [blockB_dropE _ _ _ 542 542 1084 wsplit_344_542.1 rfl wsplit_344_542.2.2,
      ← blockR_eq ((Data.core344.body.drop 542).take 542), wsplit_344_542.2.1]
    rw [blockB_dropE _ _ _ 1084 542 1626 wsplit_344_1084.1 rfl wsplit_344_1084.2.2,
      ← blockR_eq ((Data.core344.body.drop 1084).take 542), wsplit_344_1084.2.1]
    rw [blockB_dropE _ _ _ 1626 542 2168 wsplit_344_1626.1 rfl wsplit_344_1626.2.2,
      ← blockR_eq ((Data.core344.body.drop 1626).take 542), wsplit_344_1626.2.1]
    rw [blockB_dropE _ _ _ 2168 542 2710 wsplit_344_2168.1 rfl wsplit_344_2168.2.2,
      ← blockR_eq ((Data.core344.body.drop 2168).take 542), wsplit_344_2168.2.1]
    rw [blockB_dropE _ _ _ 2710 542 3252 wsplit_344_2710.1 rfl wsplit_344_2710.2.2,
      ← blockR_eq ((Data.core344.body.drop 2710).take 542), wsplit_344_2710.2.1]
    rw [blockB_dropE _ _ _ 3252 542 3794 wsplit_344_3252.1 rfl wsplit_344_3252.2.2,
      ← blockR_eq ((Data.core344.body.drop 3252).take 542), wsplit_344_3252.2.1]
    rw [blockB_dropE _ _ _ 3794 542 4336 wsplit_344_3794.1 rfl wsplit_344_3794.2.2,
      ← blockR_eq ((Data.core344.body.drop 3794).take 542), wsplit_344_3794.2.1]
    rw [← blockR_eq (Data.core344.body.drop 4336), wsplit_344_4336]
    rfl
  exact wchkIdx_of_split (fn := Data.core344) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_345 : wchkIdx 345 = true := by
  have hb : blockB (wlookJ 345) (womLookJ 345) true [(.n 10, 1024), (.n 12, 256), (.n 14, 20), (.n 16, 8), (.n 18, 18), (.n 20, 54), (.n 22, 4), (.n 24, 4), (.n 26, 32), (.n 28, 176), (.n 30, 8), (.n 32, 172), (.n 34, 172), (.n 98, 8), (.n 155, 70), (.n 160, 1), (.n 161, 13), (.n 213, 36), (.n 278, 6), (.n 335, 70), (.n 344, 1), (.n 345, 6), (.n 402, 37), (.n 466, 6), (.n 523, 70), (.n 532, 1), (.n 533, 4), (.n 590, 25), (.n 661, 70), (.n 670, 1), (.n 671, 3), (.n 685, 20), (.n 754, 20), (.n 756, 5), (.n 918, 88), (.n 920, 4), (.n 922, 4), (.n 1206, 8), (.n 1210, 20), (.n 1217, 0), (.n 1218, 9), (.n 1351, 10), (.n 1358, 0), (.n 1359, 4), (.n 1813, 8), (.n 1820, 0), (.n 1821, 3)] Data.core345.params Data.core345.name ([], []) Data.core345.body = some (⟨102368, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core345.body)]
    rw [blockB_dropE _ _ _ 0 721 721 wsplit_345_0.1 rfl wsplit_345_0.2.2,
      ← blockR_eq ((Data.core345.body.drop 0).take 721), wsplit_345_0.2.1]
    rw [blockB_dropE _ _ _ 721 721 1442 wsplit_345_721.1 rfl wsplit_345_721.2.2,
      ← blockR_eq ((Data.core345.body.drop 721).take 721), wsplit_345_721.2.1]
    rw [blockB_dropE _ _ _ 1442 721 2163 wsplit_345_1442.1 rfl wsplit_345_1442.2.2,
      ← blockR_eq ((Data.core345.body.drop 1442).take 721), wsplit_345_1442.2.1]
    rw [← blockR_eq (Data.core345.body.drop 2163), wsplit_345_2163]
    rfl
  exact wchkIdx_of_split (fn := Data.core345) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_346 : wchkIdx 346 = true := by
  have hb : blockB (wlookJ 346) (womLookJ 346) true [(.n 10, 1024), (.n 12, 256), (.n 14, 36), (.n 16, 8), (.n 18, 18), (.n 20, 54), (.n 22, 4), (.n 24, 4), (.n 26, 32), (.n 28, 176), (.n 30, 8), (.n 32, 169), (.n 34, 169), (.n 98, 8), (.n 155, 70), (.n 160, 1), (.n 161, 13), (.n 213, 36), (.n 278, 6), (.n 335, 70), (.n 344, 1), (.n 345, 7), (.n 402, 37), (.n 466, 6), (.n 523, 70), (.n 532, 1), (.n 533, 4), (.n 590, 25), (.n 661, 70), (.n 670, 1), (.n 671, 3), (.n 685, 36), (.n 802, 19), (.n 804, 5), (.n 975, 88), (.n 977, 4), (.n 979, 4), (.n 1287, 8), (.n 1291, 20), (.n 1298, 0), (.n 1299, 9), (.n 1438, 10), (.n 1445, 0), (.n 1446, 4), (.n 1930, 8), (.n 1937, 0), (.n 1938, 3)] Data.core346.params Data.core346.name ([], []) Data.core346.body = some (⟨107511, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core346.body)]
    rw [blockB_dropE _ _ _ 0 721 721 wsplit_346_0.1 rfl wsplit_346_0.2.2,
      ← blockR_eq ((Data.core346.body.drop 0).take 721), wsplit_346_0.2.1]
    rw [blockB_dropE _ _ _ 721 721 1442 wsplit_346_721.1 rfl wsplit_346_721.2.2,
      ← blockR_eq ((Data.core346.body.drop 721).take 721), wsplit_346_721.2.1]
    rw [blockB_dropE _ _ _ 1442 721 2163 wsplit_346_1442.1 rfl wsplit_346_1442.2.2,
      ← blockR_eq ((Data.core346.body.drop 1442).take 721), wsplit_346_1442.2.1]
    rw [← blockR_eq (Data.core346.body.drop 2163), wsplit_346_2163]
    rfl
  exact wchkIdx_of_split (fn := Data.core346) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_347 : wchkIdx 347 = true := by
  have hb : blockB (wlookJ 347) (womLookJ 347) true [(.n 10, 1152), (.n 12, 288), (.n 14, 8), (.n 16, 10), (.n 18, 22), (.n 20, 66), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 220), (.n 30, 10), (.n 32, 192), (.n 34, 192), (.n 98, 8), (.n 155, 70), (.n 160, 1), (.n 161, 13), (.n 213, 36), (.n 278, 6), (.n 335, 70), (.n 344, 1), (.n 345, 7), (.n 402, 37), (.n 466, 6), (.n 523, 70), (.n 532, 1), (.n 533, 5), (.n 590, 25), (.n 653, 6), (.n 710, 70), (.n 719, 1), (.n 720, 3), (.n 777, 19), (.n 848, 70), (.n 857, 1), (.n 858, 3), (.n 872, 8), (.n 905, 17), (.n 907, 5), (.n 1059, 110), (.n 1061, 5), (.n 1063, 5), (.n 1441, 10), (.n 1445, 20), (.n 1452, 0), (.n 1453, 9), (.n 1598, 10), (.n 1605, 0), (.n 1606, 4), (.n 2120, 8), (.n 2127, 0), (.n 2128, 3), (.n 2218, 6), (.n 2225, 0), (.n 2226, 2)] Data.core347.params Data.core347.name ([], []) Data.core347.body = some (⟨114730, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core347.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_347_0.1 rfl wsplit_347_0.2.2,
      ← blockR_eq ((Data.core347.body.drop 0).take 619), wsplit_347_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_347_619.1 rfl wsplit_347_619.2.2,
      ← blockR_eq ((Data.core347.body.drop 619).take 619), wsplit_347_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_347_1238.1 rfl wsplit_347_1238.2.2,
      ← blockR_eq ((Data.core347.body.drop 1238).take 619), wsplit_347_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_347_1857.1 rfl wsplit_347_1857.2.2,
      ← blockR_eq ((Data.core347.body.drop 1857).take 619), wsplit_347_1857.2.1]
    rw [← blockR_eq (Data.core347.body.drop 2476), wsplit_347_2476]
    rfl
  exact wchkIdx_of_split (fn := Data.core347) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_348 : wchkIdx 348 = true := by
  have hb : blockB (wlookJ 348) (womLookJ 348) true [(.n 10, 1088), (.n 12, 272), (.n 14, 12), (.n 16, 10), (.n 18, 22), (.n 20, 66), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 220), (.n 30, 10), (.n 32, 192), (.n 34, 192), (.n 98, 8), (.n 155, 80), (.n 160, 1), (.n 161, 15), (.n 213, 36), (.n 278, 6), (.n 335, 80), (.n 344, 1), (.n 345, 7), (.n 402, 37), (.n 466, 6), (.n 523, 80), (.n 532, 1), (.n 533, 5), (.n 590, 25), (.n 653, 6), (.n 710, 80), (.n 719, 1), (.n 720, 4), (.n 777, 19), (.n 848, 80), (.n 857, 1), (.n 858, 3), (.n 872, 12), (.n 917, 16), (.n 919, 5), (.n 1080, 110), (.n 1082, 5), (.n 1084, 5), (.n 1494, 10), (.n 1498, 20), (.n 1505, 0), (.n 1506, 9), (.n 1657, 10), (.n 1664, 0), (.n 1665, 4), (.n 2209, 8), (.n 2216, 0), (.n 2217, 3), (.n 2313, 6), (.n 2320, 0), (.n 2321, 2)] Data.core348.params Data.core348.name ([], []) Data.core348.body = some (⟨117145, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core348.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_348_0.1 rfl wsplit_348_0.2.2,
      ← blockR_eq ((Data.core348.body.drop 0).take 619), wsplit_348_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_348_619.1 rfl wsplit_348_619.2.2,
      ← blockR_eq ((Data.core348.body.drop 619).take 619), wsplit_348_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_348_1238.1 rfl wsplit_348_1238.2.2,
      ← blockR_eq ((Data.core348.body.drop 1238).take 619), wsplit_348_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_348_1857.1 rfl wsplit_348_1857.2.2,
      ← blockR_eq ((Data.core348.body.drop 1857).take 619), wsplit_348_1857.2.1]
    rw [blockB_dropE _ _ _ 2476 619 3095 wsplit_348_2476.1 rfl wsplit_348_2476.2.2,
      ← blockR_eq ((Data.core348.body.drop 2476).take 619), wsplit_348_2476.2.1]
    rw [← blockR_eq (Data.core348.body.drop 3095), wsplit_348_3095]
    rfl
  exact wchkIdx_of_split (fn := Data.core348) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_349 : wchkIdx 349 = true := by
  have hb : blockB (wlookJ 349) (womLookJ 349) true [(.n 10, 1088), (.n 12, 272), (.n 14, 20), (.n 16, 10), (.n 18, 22), (.n 20, 66), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 220), (.n 30, 10), (.n 32, 187), (.n 34, 187), (.n 98, 8), (.n 155, 80), (.n 160, 1), (.n 161, 15), (.n 213, 36), (.n 278, 6), (.n 335, 80), (.n 344, 1), (.n 345, 8), (.n 402, 37), (.n 466, 6), (.n 523, 80), (.n 532, 1), (.n 533, 5), (.n 590, 25), (.n 653, 6), (.n 710, 80), (.n 719, 1), (.n 720, 4), (.n 777, 19), (.n 848, 80), (.n 857, 1), (.n 858, 3), (.n 872, 20), (.n 941, 16), (.n 943, 5), (.n 1113, 110), (.n 1115, 5), (.n 1117, 5), (.n 1559, 10), (.n 1563, 20), (.n 1570, 0), (.n 1571, 9), (.n 1728, 10), (.n 1735, 0), (.n 1736, 4), (.n 2310, 8), (.n 2317, 0), (.n 2318, 3), (.n 2420, 6), (.n 2427, 0), (.n 2428, 2)] Data.core349.params Data.core349.name ([], []) Data.core349.body = some (⟨119483, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core349.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_349_0.1 rfl wsplit_349_0.2.2,
      ← blockR_eq ((Data.core349.body.drop 0).take 619), wsplit_349_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_349_619.1 rfl wsplit_349_619.2.2,
      ← blockR_eq ((Data.core349.body.drop 619).take 619), wsplit_349_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_349_1238.1 rfl wsplit_349_1238.2.2,
      ← blockR_eq ((Data.core349.body.drop 1238).take 619), wsplit_349_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_349_1857.1 rfl wsplit_349_1857.2.2,
      ← blockR_eq ((Data.core349.body.drop 1857).take 619), wsplit_349_1857.2.1]
    rw [blockB_dropE _ _ _ 2476 619 3095 wsplit_349_2476.1 rfl wsplit_349_2476.2.2,
      ← blockR_eq ((Data.core349.body.drop 2476).take 619), wsplit_349_2476.2.1]
    rw [← blockR_eq (Data.core349.body.drop 3095), wsplit_349_3095]
    rfl
  exact wchkIdx_of_split (fn := Data.core349) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_350 : wchkIdx 350 = true := by
  have hb : blockB (wlookJ 350) (womLookJ 350) true [(.n 10, 1088), (.n 12, 272), (.n 14, 36), (.n 16, 10), (.n 18, 22), (.n 20, 66), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 220), (.n 30, 10), (.n 32, 182), (.n 34, 182), (.n 98, 8), (.n 155, 80), (.n 160, 1), (.n 161, 15), (.n 213, 36), (.n 278, 6), (.n 335, 80), (.n 344, 1), (.n 345, 8), (.n 402, 37), (.n 466, 6), (.n 523, 80), (.n 532, 1), (.n 533, 5), (.n 590, 25), (.n 653, 6), (.n 710, 80), (.n 719, 1), (.n 720, 4), (.n 777, 19), (.n 848, 80), (.n 857, 1), (.n 858, 3), (.n 872, 36), (.n 989, 15), (.n 991, 5), (.n 1170, 110), (.n 1172, 5), (.n 1174, 5), (.n 1648, 10), (.n 1652, 20), (.n 1659, 0), (.n 1660, 9), (.n 1823, 10), (.n 1830, 0), (.n 1831, 4), (.n 2435, 8), (.n 2442, 0), (.n 2443, 3), (.n 2551, 6), (.n 2558, 0), (.n 2559, 2)] Data.core350.params Data.core350.name ([], []) Data.core350.body = some (⟨122166, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core350.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_350_0.1 rfl wsplit_350_0.2.2,
      ← blockR_eq ((Data.core350.body.drop 0).take 619), wsplit_350_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_350_619.1 rfl wsplit_350_619.2.2,
      ← blockR_eq ((Data.core350.body.drop 619).take 619), wsplit_350_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_350_1238.1 rfl wsplit_350_1238.2.2,
      ← blockR_eq ((Data.core350.body.drop 1238).take 619), wsplit_350_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_350_1857.1 rfl wsplit_350_1857.2.2,
      ← blockR_eq ((Data.core350.body.drop 1857).take 619), wsplit_350_1857.2.1]
    rw [blockB_dropE _ _ _ 2476 619 3095 wsplit_350_2476.1 rfl wsplit_350_2476.2.2,
      ← blockR_eq ((Data.core350.body.drop 2476).take 619), wsplit_350_2476.2.1]
    rw [← blockR_eq (Data.core350.body.drop 3095), wsplit_350_3095]
    rfl
  exact wchkIdx_of_split (fn := Data.core350) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_351 : wchkIdx 351 = true := by
  have hb : blockB (wlookJ 351) (womLookJ 351) true [(.n 10, 1152), (.n 12, 288), (.n 14, 8), (.n 16, 12), (.n 18, 26), (.n 20, 78), (.n 22, 6), (.n 24, 6), (.n 26, 48), (.n 28, 264), (.n 30, 12), (.n 32, 196), (.n 34, 196), (.n 98, 8), (.n 155, 80), (.n 160, 1), (.n 161, 15), (.n 213, 36), (.n 278, 6), (.n 335, 80), (.n 344, 1), (.n 345, 8), (.n 402, 37), (.n 466, 6), (.n 523, 80), (.n 532, 1), (.n 533, 5), (.n 590, 25), (.n 653, 6), (.n 710, 80), (.n 719, 1), (.n 720, 4), (.n 777, 19), (.n 840, 6), (.n 897, 80), (.n 906, 1), (.n 907, 3), (.n 964, 15), (.n 1035, 80), (.n 1044, 1), (.n 1045, 3), (.n 1059, 8), (.n 1092, 14), (.n 1094, 5), (.n 1254, 132), (.n 1256, 6), (.n 1258, 6), (.n 1810, 12), (.n 1814, 20), (.n 1821, 0), (.n 1822, 9), (.n 1991, 10), (.n 1998, 0), (.n 1999, 4), (.n 2633, 8), (.n 2640, 0), (.n 2641, 3), (.n 2755, 6), (.n 2762, 0), (.n 2763, 2), (.n 3005, 4), (.n 3012, 0), (.n 3013, 1)] Data.core351.params Data.core351.name ([], []) Data.core351.body = some (⟨128501, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core351.body)]
    rw [blockB_dropE _ _ _ 0 542 542 wsplit_351_0.1 rfl wsplit_351_0.2.2,
      ← blockR_eq ((Data.core351.body.drop 0).take 542), wsplit_351_0.2.1]
    rw [blockB_dropE _ _ _ 542 542 1084 wsplit_351_542.1 rfl wsplit_351_542.2.2,
      ← blockR_eq ((Data.core351.body.drop 542).take 542), wsplit_351_542.2.1]
    rw [blockB_dropE _ _ _ 1084 542 1626 wsplit_351_1084.1 rfl wsplit_351_1084.2.2,
      ← blockR_eq ((Data.core351.body.drop 1084).take 542), wsplit_351_1084.2.1]
    rw [blockB_dropE _ _ _ 1626 542 2168 wsplit_351_1626.1 rfl wsplit_351_1626.2.2,
      ← blockR_eq ((Data.core351.body.drop 1626).take 542), wsplit_351_1626.2.1]
    rw [blockB_dropE _ _ _ 2168 542 2710 wsplit_351_2168.1 rfl wsplit_351_2168.2.2,
      ← blockR_eq ((Data.core351.body.drop 2168).take 542), wsplit_351_2168.2.1]
    rw [blockB_dropE _ _ _ 2710 542 3252 wsplit_351_2710.1 rfl wsplit_351_2710.2.2,
      ← blockR_eq ((Data.core351.body.drop 2710).take 542), wsplit_351_2710.2.1]
    rw [blockB_dropE _ _ _ 3252 542 3794 wsplit_351_3252.1 rfl wsplit_351_3252.2.2,
      ← blockR_eq ((Data.core351.body.drop 3252).take 542), wsplit_351_3252.2.1]
    rw [← blockR_eq (Data.core351.body.drop 3794), wsplit_351_3794]
    rfl
  exact wchkIdx_of_split (fn := Data.core351) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_352 : wchkIdx 352 = true := by
  have hb : blockB (wlookJ 352) (womLookJ 352) true [(.n 10, 640), (.n 12, 160), (.n 14, 20), (.n 16, 8), (.n 18, 18), (.n 20, 54), (.n 22, 4), (.n 24, 4), (.n 26, 32), (.n 28, 176), (.n 30, 8), (.n 32, 145), (.n 34, 145), (.n 98, 8), (.n 155, 55), (.n 160, 1), (.n 161, 10), (.n 213, 27), (.n 279, 6), (.n 336, 55), (.n 345, 1), (.n 346, 6), (.n 403, 32), (.n 465, 6), (.n 522, 55), (.n 531, 1), (.n 532, 4), (.n 589, 22), (.n 660, 55), (.n 669, 1), (.n 670, 3), (.n 684, 20), (.n 753, 18), (.n 755, 5), (.n 917, 88), (.n 919, 4), (.n 921, 4), (.n 1205, 8), (.n 1209, 14), (.n 1216, 0), (.n 1217, 6), (.n 2064, 10), (.n 2071, 0), (.n 2072, 4), (.n 2086, 6), (.n 2093, 0), (.n 2094, 2)] Data.core352.params Data.core352.name ([], []) Data.core352.body = some (⟨86553, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core352.body)]
    rw [blockB_dropE _ _ _ 0 721 721 wsplit_352_0.1 rfl wsplit_352_0.2.2,
      ← blockR_eq ((Data.core352.body.drop 0).take 721), wsplit_352_0.2.1]
    rw [blockB_dropE _ _ _ 721 721 1442 wsplit_352_721.1 rfl wsplit_352_721.2.2,
      ← blockR_eq ((Data.core352.body.drop 721).take 721), wsplit_352_721.2.1]
    rw [blockB_dropE _ _ _ 1442 721 2163 wsplit_352_1442.1 rfl wsplit_352_1442.2.2,
      ← blockR_eq ((Data.core352.body.drop 1442).take 721), wsplit_352_1442.2.1]
    rw [blockB_dropE _ _ _ 2163 721 2884 wsplit_352_2163.1 rfl wsplit_352_2163.2.2,
      ← blockR_eq ((Data.core352.body.drop 2163).take 721), wsplit_352_2163.2.1]
    rw [← blockR_eq (Data.core352.body.drop 2884), wsplit_352_2884]
    rfl
  exact wchkIdx_of_split (fn := Data.core352) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_353 : wchkIdx 353 = true := by
  have hb : blockB (wlookJ 353) (womLookJ 353) true [(.n 10, 640), (.n 12, 160), (.n 14, 36), (.n 16, 8), (.n 18, 18), (.n 20, 54), (.n 22, 4), (.n 24, 4), (.n 26, 32), (.n 28, 176), (.n 30, 8), (.n 32, 141), (.n 34, 141), (.n 98, 8), (.n 155, 55), (.n 160, 1), (.n 161, 10), (.n 213, 27), (.n 279, 6), (.n 336, 55), (.n 345, 1), (.n 346, 6), (.n 403, 31), (.n 468, 6), (.n 525, 55), (.n 534, 1), (.n 535, 4), (.n 592, 22), (.n 663, 55), (.n 672, 1), (.n 673, 3), (.n 687, 36), (.n 804, 18), (.n 806, 5), (.n 977, 88), (.n 979, 4), (.n 981, 4), (.n 1289, 8), (.n 1293, 14), (.n 1300, 0), (.n 1301, 6), (.n 2190, 8), (.n 2197, 0), (.n 2198, 3), (.n 2870, 6), (.n 2877, 0), (.n 2878, 2)] Data.core353.params Data.core353.name ([], []) Data.core353.body = some (⟨88805, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core353.body)]
    rw [blockB_dropE _ _ _ 0 721 721 wsplit_353_0.1 rfl wsplit_353_0.2.2,
      ← blockR_eq ((Data.core353.body.drop 0).take 721), wsplit_353_0.2.1]
    rw [blockB_dropE _ _ _ 721 721 1442 wsplit_353_721.1 rfl wsplit_353_721.2.2,
      ← blockR_eq ((Data.core353.body.drop 721).take 721), wsplit_353_721.2.1]
    rw [blockB_dropE _ _ _ 1442 721 2163 wsplit_353_1442.1 rfl wsplit_353_1442.2.2,
      ← blockR_eq ((Data.core353.body.drop 1442).take 721), wsplit_353_1442.2.1]
    rw [blockB_dropE _ _ _ 2163 721 2884 wsplit_353_2163.1 rfl wsplit_353_2163.2.2,
      ← blockR_eq ((Data.core353.body.drop 2163).take 721), wsplit_353_2163.2.1]
    rw [blockB_dropE _ _ _ 2884 721 3605 wsplit_353_2884.1 rfl wsplit_353_2884.2.2,
      ← blockR_eq ((Data.core353.body.drop 2884).take 721), wsplit_353_2884.2.1]
    rw [← blockR_eq (Data.core353.body.drop 3605), wsplit_353_3605]
    rfl
  exact wchkIdx_of_split (fn := Data.core353) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_354 : wchkIdx 354 = true := by
  have hb : blockB (wlookJ 354) (womLookJ 354) true [(.n 10, 704), (.n 12, 176), (.n 14, 8), (.n 16, 10), (.n 18, 22), (.n 20, 66), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 220), (.n 30, 10), (.n 32, 154), (.n 34, 154), (.n 98, 8), (.n 155, 60), (.n 160, 1), (.n 161, 11), (.n 213, 27), (.n 279, 6), (.n 336, 60), (.n 345, 1), (.n 346, 6), (.n 403, 31), (.n 468, 6), (.n 525, 60), (.n 534, 1), (.n 535, 4), (.n 592, 22), (.n 655, 6), (.n 712, 60), (.n 721, 1), (.n 722, 3), (.n 779, 18), (.n 849, 60), (.n 858, 1), (.n 859, 3), (.n 873, 8), (.n 906, 16), (.n 908, 5), (.n 1060, 110), (.n 1062, 5), (.n 1064, 5), (.n 1442, 10), (.n 1446, 14), (.n 1453, 0), (.n 1454, 6), (.n 2385, 8), (.n 2392, 0), (.n 2393, 3), (.n 3107, 6), (.n 3114, 0), (.n 3115, 2), (.n 3585, 6), (.n 3592, 0), (.n 3593, 2)] Data.core354.params Data.core354.name ([], []) Data.core354.body = some (⟨95442, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core354.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_354_0.1 rfl wsplit_354_0.2.2,
      ← blockR_eq ((Data.core354.body.drop 0).take 619), wsplit_354_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_354_619.1 rfl wsplit_354_619.2.2,
      ← blockR_eq ((Data.core354.body.drop 619).take 619), wsplit_354_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_354_1238.1 rfl wsplit_354_1238.2.2,
      ← blockR_eq ((Data.core354.body.drop 1238).take 619), wsplit_354_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_354_1857.1 rfl wsplit_354_1857.2.2,
      ← blockR_eq ((Data.core354.body.drop 1857).take 619), wsplit_354_1857.2.1]
    rw [blockB_dropE _ _ _ 2476 619 3095 wsplit_354_2476.1 rfl wsplit_354_2476.2.2,
      ← blockR_eq ((Data.core354.body.drop 2476).take 619), wsplit_354_2476.2.1]
    rw [blockB_dropE _ _ _ 3095 619 3714 wsplit_354_3095.1 rfl wsplit_354_3095.2.2,
      ← blockR_eq ((Data.core354.body.drop 3095).take 619), wsplit_354_3095.2.1]
    rw [← blockR_eq (Data.core354.body.drop 3714), wsplit_354_3714]
    rfl
  exact wchkIdx_of_split (fn := Data.core354) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_355 : wchkIdx 355 = true := by
  have hb : blockB (wlookJ 355) (womLookJ 355) true [(.n 10, 704), (.n 12, 176), (.n 14, 12), (.n 16, 10), (.n 18, 22), (.n 20, 66), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 220), (.n 30, 10), (.n 32, 150), (.n 34, 150), (.n 98, 8), (.n 155, 60), (.n 160, 1), (.n 161, 11), (.n 213, 27), (.n 279, 6), (.n 336, 60), (.n 345, 1), (.n 346, 7), (.n 403, 31), (.n 468, 6), (.n 525, 60), (.n 534, 1), (.n 535, 4), (.n 592, 22), (.n 655, 6), (.n 712, 60), (.n 721, 1), (.n 722, 3), (.n 779, 17), (.n 849, 60), (.n 858, 1), (.n 859, 3), (.n 873, 12), (.n 918, 15), (.n 920, 5), (.n 1081, 110), (.n 1083, 5), (.n 1085, 5), (.n 1495, 10), (.n 1499, 14), (.n 1506, 0), (.n 1507, 6), (.n 2480, 8), (.n 2487, 0), (.n 2488, 3), (.n 3244, 6), (.n 3251, 0), (.n 3252, 2), (.n 3758, 6), (.n 3765, 0), (.n 3766, 2)] Data.core355.params Data.core355.name ([], []) Data.core355.body = some (⟨96395, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core355.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_355_0.1 rfl wsplit_355_0.2.2,
      ← blockR_eq ((Data.core355.body.drop 0).take 619), wsplit_355_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_355_619.1 rfl wsplit_355_619.2.2,
      ← blockR_eq ((Data.core355.body.drop 619).take 619), wsplit_355_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_355_1238.1 rfl wsplit_355_1238.2.2,
      ← blockR_eq ((Data.core355.body.drop 1238).take 619), wsplit_355_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_355_1857.1 rfl wsplit_355_1857.2.2,
      ← blockR_eq ((Data.core355.body.drop 1857).take 619), wsplit_355_1857.2.1]
    rw [blockB_dropE _ _ _ 2476 619 3095 wsplit_355_2476.1 rfl wsplit_355_2476.2.2,
      ← blockR_eq ((Data.core355.body.drop 2476).take 619), wsplit_355_2476.2.1]
    rw [blockB_dropE _ _ _ 3095 619 3714 wsplit_355_3095.1 rfl wsplit_355_3095.2.2,
      ← blockR_eq ((Data.core355.body.drop 3095).take 619), wsplit_355_3095.2.1]
    rw [blockB_dropE _ _ _ 3714 619 4333 wsplit_355_3714.1 rfl wsplit_355_3714.2.2,
      ← blockR_eq ((Data.core355.body.drop 3714).take 619), wsplit_355_3714.2.1]
    rw [← blockR_eq (Data.core355.body.drop 4333), wsplit_355_4333]
    rfl
  exact wchkIdx_of_split (fn := Data.core355) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_356 : wchkIdx 356 = true := by
  have hb : blockB (wlookJ 356) (womLookJ 356) true [(.n 10, 704), (.n 12, 176), (.n 14, 20), (.n 16, 10), (.n 18, 22), (.n 20, 66), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 220), (.n 30, 10), (.n 32, 151), (.n 34, 151), (.n 98, 8), (.n 155, 60), (.n 160, 1), (.n 161, 11), (.n 213, 27), (.n 279, 6), (.n 336, 60), (.n 345, 1), (.n 346, 7), (.n 403, 31), (.n 468, 6), (.n 525, 60), (.n 534, 1), (.n 535, 5), (.n 592, 22), (.n 655, 6), (.n 712, 60), (.n 721, 1), (.n 722, 3), (.n 779, 17), (.n 849, 60), (.n 858, 1), (.n 859, 3), (.n 873, 20), (.n 942, 15), (.n 944, 5), (.n 1114, 110), (.n 1116, 5), (.n 1118, 5), (.n 1560, 10), (.n 1564, 14), (.n 1571, 0), (.n 1572, 6), (.n 2587, 8), (.n 2594, 0), (.n 2595, 3), (.n 3393, 6), (.n 3400, 0), (.n 3401, 2), (.n 3943, 6), (.n 3950, 0), (.n 3951, 2)] Data.core356.params Data.core356.name ([], []) Data.core356.body = some (⟨98824, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core356.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_356_0.1 rfl wsplit_356_0.2.2,
      ← blockR_eq ((Data.core356.body.drop 0).take 619), wsplit_356_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_356_619.1 rfl wsplit_356_619.2.2,
      ← blockR_eq ((Data.core356.body.drop 619).take 619), wsplit_356_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_356_1238.1 rfl wsplit_356_1238.2.2,
      ← blockR_eq ((Data.core356.body.drop 1238).take 619), wsplit_356_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_356_1857.1 rfl wsplit_356_1857.2.2,
      ← blockR_eq ((Data.core356.body.drop 1857).take 619), wsplit_356_1857.2.1]
    rw [blockB_dropE _ _ _ 2476 619 3095 wsplit_356_2476.1 rfl wsplit_356_2476.2.2,
      ← blockR_eq ((Data.core356.body.drop 2476).take 619), wsplit_356_2476.2.1]
    rw [blockB_dropE _ _ _ 3095 619 3714 wsplit_356_3095.1 rfl wsplit_356_3095.2.2,
      ← blockR_eq ((Data.core356.body.drop 3095).take 619), wsplit_356_3095.2.1]
    rw [blockB_dropE _ _ _ 3714 619 4333 wsplit_356_3714.1 rfl wsplit_356_3714.2.2,
      ← blockR_eq ((Data.core356.body.drop 3714).take 619), wsplit_356_3714.2.1]
    rw [← blockR_eq (Data.core356.body.drop 4333), wsplit_356_4333]
    rfl
  exact wchkIdx_of_split (fn := Data.core356) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_357 : wchkIdx 357 = true := by
  have hb : blockB (wlookJ 357) (womLookJ 357) true [(.n 10, 704), (.n 12, 176), (.n 14, 36), (.n 16, 10), (.n 18, 22), (.n 20, 66), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 220), (.n 30, 10), (.n 32, 153), (.n 34, 153), (.n 98, 8), (.n 155, 60), (.n 160, 1), (.n 161, 11), (.n 213, 27), (.n 279, 6), (.n 336, 60), (.n 345, 1), (.n 346, 7), (.n 403, 31), (.n 468, 6), (.n 525, 60), (.n 534, 1), (.n 535, 5), (.n 592, 22), (.n 655, 6), (.n 712, 60), (.n 721, 1), (.n 722, 4), (.n 779, 17), (.n 849, 60), (.n 858, 1), (.n 859, 3), (.n 873, 36), (.n 990, 14), (.n 992, 5), (.n 1171, 110), (.n 1173, 5), (.n 1175, 5), (.n 1649, 10), (.n 1653, 14), (.n 1660, 0), (.n 1661, 6), (.n 2718, 8), (.n 2725, 0), (.n 2726, 3), (.n 3566, 6), (.n 3573, 0), (.n 3574, 2), (.n 4152, 6), (.n 4159, 0), (.n 4160, 2)] Data.core357.params Data.core357.name ([], []) Data.core357.body = some (⟨102640, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core357.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_357_0.1 rfl wsplit_357_0.2.2,
      ← blockR_eq ((Data.core357.body.drop 0).take 619), wsplit_357_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_357_619.1 rfl wsplit_357_619.2.2,
      ← blockR_eq ((Data.core357.body.drop 619).take 619), wsplit_357_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_357_1238.1 rfl wsplit_357_1238.2.2,
      ← blockR_eq ((Data.core357.body.drop 1238).take 619), wsplit_357_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_357_1857.1 rfl wsplit_357_1857.2.2,
      ← blockR_eq ((Data.core357.body.drop 1857).take 619), wsplit_357_1857.2.1]
    rw [blockB_dropE _ _ _ 2476 619 3095 wsplit_357_2476.1 rfl wsplit_357_2476.2.2,
      ← blockR_eq ((Data.core357.body.drop 2476).take 619), wsplit_357_2476.2.1]
    rw [blockB_dropE _ _ _ 3095 619 3714 wsplit_357_3095.1 rfl wsplit_357_3095.2.2,
      ← blockR_eq ((Data.core357.body.drop 3095).take 619), wsplit_357_3095.2.1]
    rw [blockB_dropE _ _ _ 3714 619 4333 wsplit_357_3714.1 rfl wsplit_357_3714.2.2,
      ← blockR_eq ((Data.core357.body.drop 3714).take 619), wsplit_357_3714.2.1]
    rw [← blockR_eq (Data.core357.body.drop 4333), wsplit_357_4333]
    rfl
  exact wchkIdx_of_split (fn := Data.core357) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_358 : wchkIdx 358 = true := by
  have hb : blockB (wlookJ 358) (womLookJ 358) true [(.n 10, 768), (.n 12, 192), (.n 14, 8), (.n 16, 12), (.n 18, 26), (.n 20, 78), (.n 22, 6), (.n 24, 6), (.n 26, 48), (.n 28, 264), (.n 30, 12), (.n 32, 169), (.n 34, 169), (.n 98, 8), (.n 155, 75), (.n 160, 1), (.n 161, 14), (.n 213, 27), (.n 279, 6), (.n 336, 75), (.n 345, 1), (.n 346, 7), (.n 403, 31), (.n 468, 6), (.n 525, 75), (.n 534, 1), (.n 535, 5), (.n 592, 22), (.n 655, 6), (.n 712, 75), (.n 721, 1), (.n 722, 4), (.n 779, 17), (.n 841, 6), (.n 898, 75), (.n 907, 1), (.n 908, 3), (.n 965, 14), (.n 1035, 75), (.n 1044, 1), (.n 1045, 3), (.n 1059, 8), (.n 1092, 13), (.n 1094, 5), (.n 1254, 132), (.n 1256, 6), (.n 1258, 6), (.n 1810, 12), (.n 1814, 14), (.n 1821, 0), (.n 1822, 6), (.n 2921, 8), (.n 2928, 0), (.n 2929, 3), (.n 3811, 6), (.n 3818, 0), (.n 3819, 2), (.n 4433, 6), (.n 4440, 0), (.n 4441, 2), (.n 4531, 4), (.n 4538, 0), (.n 4539, 1)] Data.core358.params Data.core358.name ([], []) Data.core358.body = some (⟨109713, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core358.body)]
    rw [blockB_dropE _ _ _ 0 542 542 wsplit_358_0.1 rfl wsplit_358_0.2.2,
      ← blockR_eq ((Data.core358.body.drop 0).take 542), wsplit_358_0.2.1]
    rw [blockB_dropE _ _ _ 542 542 1084 wsplit_358_542.1 rfl wsplit_358_542.2.2,
      ← blockR_eq ((Data.core358.body.drop 542).take 542), wsplit_358_542.2.1]
    rw [blockB_dropE _ _ _ 1084 542 1626 wsplit_358_1084.1 rfl wsplit_358_1084.2.2,
      ← blockR_eq ((Data.core358.body.drop 1084).take 542), wsplit_358_1084.2.1]
    rw [blockB_dropE _ _ _ 1626 542 2168 wsplit_358_1626.1 rfl wsplit_358_1626.2.2,
      ← blockR_eq ((Data.core358.body.drop 1626).take 542), wsplit_358_1626.2.1]
    rw [blockB_dropE _ _ _ 2168 542 2710 wsplit_358_2168.1 rfl wsplit_358_2168.2.2,
      ← blockR_eq ((Data.core358.body.drop 2168).take 542), wsplit_358_2168.2.1]
    rw [blockB_dropE _ _ _ 2710 542 3252 wsplit_358_2710.1 rfl wsplit_358_2710.2.2,
      ← blockR_eq ((Data.core358.body.drop 2710).take 542), wsplit_358_2710.2.1]
    rw [blockB_dropE _ _ _ 3252 542 3794 wsplit_358_3252.1 rfl wsplit_358_3252.2.2,
      ← blockR_eq ((Data.core358.body.drop 3252).take 542), wsplit_358_3252.2.1]
    rw [blockB_dropE _ _ _ 3794 542 4336 wsplit_358_3794.1 rfl wsplit_358_3794.2.2,
      ← blockR_eq ((Data.core358.body.drop 3794).take 542), wsplit_358_3794.2.1]
    rw [blockB_dropE _ _ _ 4336 542 4878 wsplit_358_4336.1 rfl wsplit_358_4336.2.2,
      ← blockR_eq ((Data.core358.body.drop 4336).take 542), wsplit_358_4336.2.1]
    rw [blockB_dropE _ _ _ 4878 542 5420 wsplit_358_4878.1 rfl wsplit_358_4878.2.2,
      ← blockR_eq ((Data.core358.body.drop 4878).take 542), wsplit_358_4878.2.1]
    rw [← blockR_eq (Data.core358.body.drop 5420), wsplit_358_5420]
    rfl
  exact wchkIdx_of_split (fn := Data.core358) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem wchkIdx_all : ∀ j < 1055, wchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact wchkIdx_19
  by_cases h1001 : j = 331
  · subst h1001; exact wchkIdx_331
  by_cases h1002 : j = 332
  · subst h1002; exact wchkIdx_332
  by_cases h1003 : j = 333
  · subst h1003; exact wchkIdx_333
  by_cases h1004 : j = 334
  · subst h1004; exact wchkIdx_334
  by_cases h1005 : j = 335
  · subst h1005; exact wchkIdx_335
  by_cases h1006 : j = 336
  · subst h1006; exact wchkIdx_336
  by_cases h1007 : j = 337
  · subst h1007; exact wchkIdx_337
  by_cases h1008 : j = 338
  · subst h1008; exact wchkIdx_338
  by_cases h1009 : j = 339
  · subst h1009; exact wchkIdx_339
  by_cases h1010 : j = 340
  · subst h1010; exact wchkIdx_340
  by_cases h1011 : j = 341
  · subst h1011; exact wchkIdx_341
  by_cases h1012 : j = 342
  · subst h1012; exact wchkIdx_342
  by_cases h1013 : j = 343
  · subst h1013; exact wchkIdx_343
  by_cases h1014 : j = 344
  · subst h1014; exact wchkIdx_344
  by_cases h1015 : j = 345
  · subst h1015; exact wchkIdx_345
  by_cases h1016 : j = 346
  · subst h1016; exact wchkIdx_346
  by_cases h1017 : j = 347
  · subst h1017; exact wchkIdx_347
  by_cases h1018 : j = 348
  · subst h1018; exact wchkIdx_348
  by_cases h1019 : j = 349
  · subst h1019; exact wchkIdx_349
  by_cases h1020 : j = 350
  · subst h1020; exact wchkIdx_350
  by_cases h1021 : j = 351
  · subst h1021; exact wchkIdx_351
  by_cases h1022 : j = 352
  · subst h1022; exact wchkIdx_352
  by_cases h1023 : j = 353
  · subst h1023; exact wchkIdx_353
  by_cases h1024 : j = 354
  · subst h1024; exact wchkIdx_354
  by_cases h1025 : j = 355
  · subst h1025; exact wchkIdx_355
  by_cases h1026 : j = 356
  · subst h1026; exact wchkIdx_356
  by_cases h1027 : j = 357
  · subst h1027; exact wchkIdx_357
  by_cases h1028 : j = 358
  · subst h1028; exact wchkIdx_358
  by_cases h0 : j < 11
  · exact wstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact wstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact wstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 36
  · exact wstaticRange_20.get (by omega) (by omega)
  by_cases h4 : j < 37
  · exact wstaticRange_36.get (by omega) (by omega)
  by_cases h5 : j < 65
  · exact wstaticRange_37.get (by omega) (by omega)
  by_cases h6 : j < 86
  · exact wstaticRange_65.get (by omega) (by omega)
  by_cases h7 : j < 110
  · exact wstaticRange_86.get (by omega) (by omega)
  by_cases h8 : j < 135
  · exact wstaticRange_110.get (by omega) (by omega)
  by_cases h9 : j < 162
  · exact wstaticRange_135.get (by omega) (by omega)
  by_cases h10 : j < 187
  · exact wstaticRange_162.get (by omega) (by omega)
  by_cases h11 : j < 212
  · exact wstaticRange_187.get (by omega) (by omega)
  by_cases h12 : j < 238
  · exact wstaticRange_212.get (by omega) (by omega)
  by_cases h13 : j < 264
  · exact wstaticRange_238.get (by omega) (by omega)
  by_cases h14 : j < 285
  · exact wstaticRange_264.get (by omega) (by omega)
  by_cases h15 : j < 312
  · exact wstaticRange_285.get (by omega) (by omega)
  by_cases h16 : j < 331
  · exact wstaticRange_312.get (by omega) (by omega)
  by_cases h17 : j < 380
  · exact wstaticRange_359.get (by omega) (by omega)
  by_cases h18 : j < 402
  · exact wstaticRange_380.get (by omega) (by omega)
  by_cases h19 : j < 425
  · exact wstaticRange_402.get (by omega) (by omega)
  by_cases h20 : j < 439
  · exact wstaticRange_425.get (by omega) (by omega)
  by_cases h21 : j < 461
  · exact wstaticRange_439.get (by omega) (by omega)
  by_cases h22 : j < 485
  · exact wstaticRange_461.get (by omega) (by omega)
  by_cases h23 : j < 506
  · exact wstaticRange_485.get (by omega) (by omega)
  by_cases h24 : j < 527
  · exact wstaticRange_506.get (by omega) (by omega)
  by_cases h25 : j < 549
  · exact wstaticRange_527.get (by omega) (by omega)
  by_cases h26 : j < 571
  · exact wstaticRange_549.get (by omega) (by omega)
  by_cases h27 : j < 590
  · exact wstaticRange_571.get (by omega) (by omega)
  by_cases h28 : j < 609
  · exact wstaticRange_590.get (by omega) (by omega)
  by_cases h29 : j < 628
  · exact wstaticRange_609.get (by omega) (by omega)
  by_cases h30 : j < 644
  · exact wstaticRange_628.get (by omega) (by omega)
  by_cases h31 : j < 662
  · exact wstaticRange_644.get (by omega) (by omega)
  by_cases h32 : j < 678
  · exact wstaticRange_662.get (by omega) (by omega)
  by_cases h33 : j < 695
  · exact wstaticRange_678.get (by omega) (by omega)
  by_cases h34 : j < 713
  · exact wstaticRange_695.get (by omega) (by omega)
  by_cases h35 : j < 730
  · exact wstaticRange_713.get (by omega) (by omega)
  by_cases h36 : j < 747
  · exact wstaticRange_730.get (by omega) (by omega)
  by_cases h37 : j < 760
  · exact wstaticRange_747.get (by omega) (by omega)
  by_cases h38 : j < 777
  · exact wstaticRange_760.get (by omega) (by omega)
  by_cases h39 : j < 796
  · exact wstaticRange_777.get (by omega) (by omega)
  by_cases h40 : j < 808
  · exact wstaticRange_796.get (by omega) (by omega)
  by_cases h41 : j < 826
  · exact wstaticRange_808.get (by omega) (by omega)
  by_cases h42 : j < 839
  · exact wstaticRange_826.get (by omega) (by omega)
  by_cases h43 : j < 856
  · exact wstaticRange_839.get (by omega) (by omega)
  by_cases h44 : j < 874
  · exact wstaticRange_856.get (by omega) (by omega)
  by_cases h45 : j < 893
  · exact wstaticRange_874.get (by omega) (by omega)
  by_cases h46 : j < 917
  · exact wstaticRange_893.get (by omega) (by omega)
  by_cases h47 : j < 940
  · exact wstaticRange_917.get (by omega) (by omega)
  by_cases h48 : j < 955
  · exact wstaticRange_940.get (by omega) (by omega)
  by_cases h49 : j < 969
  · exact wstaticRange_955.get (by omega) (by omega)
  by_cases h50 : j < 982
  · exact wstaticRange_969.get (by omega) (by omega)
  by_cases h51 : j < 993
  · exact wstaticRange_982.get (by omega) (by omega)
  by_cases h52 : j < 1009
  · exact wstaticRange_993.get (by omega) (by omega)
  by_cases h53 : j < 1020
  · exact wstaticRange_1009.get (by omega) (by omega)
  by_cases h54 : j < 1031
  · exact wstaticRange_1020.get (by omega) (by omega)
  by_cases h55 : j < 1042
  · exact wstaticRange_1031.get (by omega) (by omega)
  by_cases h56 : j < 1050
  · exact wstaticRange_1042.get (by omega) (by omega)
  exact wstaticRange_1050.get (by omega) (by omega)

end
end LeanVM.Guest
