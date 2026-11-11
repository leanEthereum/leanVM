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
  have hb : blockB (wlookJ 331) (womLookJ 331) true [(.n 10, 1536), (.n 12, 384), (.n 14, 20), (.n 16, 8), (.n 18, 18), (.n 20, 36), (.n 22, 4), (.n 24, 4), (.n 26, 32), (.n 28, 88), (.n 30, 4), (.n 32, 339), (.n 34, 339), (.n 98, 8), (.n 146, 165), (.n 151, 1), (.n 152, 32), (.n 196, 109), (.n 261, 6), (.n 304, 165), (.n 313, 1), (.n 314, 7), (.n 368, 55), (.n 431, 6), (.n 474, 165), (.n 483, 1), (.n 484, 4), (.n 538, 32), (.n 605, 165), (.n 614, 1), (.n 615, 3), (.n 629, 20), (.n 698, 24), (.n 700, 5), (.n 862, 88), (.n 864, 4), (.n 866, 4), (.n 1150, 8), (.n 1154, 56), (.n 1161, 0), (.n 1162, 27), (.n 1414, 14), (.n 1421, 0), (.n 1422, 6), (.n 2052, 10), (.n 2059, 0), (.n 2060, 4)] Data.core331.params Data.core331.name ([], []) Data.core331.body = some (⟨202728, []⟩, []) := by
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
  have hb : blockB (wlookJ 332) (womLookJ 332) true [(.n 10, 1536), (.n 12, 384), (.n 14, 36), (.n 16, 8), (.n 18, 18), (.n 20, 36), (.n 22, 4), (.n 24, 4), (.n 26, 32), (.n 28, 88), (.n 30, 4), (.n 32, 336), (.n 34, 336), (.n 98, 8), (.n 146, 165), (.n 151, 1), (.n 152, 32), (.n 196, 109), (.n 261, 6), (.n 304, 165), (.n 313, 1), (.n 314, 8), (.n 368, 55), (.n 431, 6), (.n 474, 165), (.n 483, 1), (.n 484, 4), (.n 538, 32), (.n 605, 165), (.n 614, 1), (.n 615, 3), (.n 629, 36), (.n 746, 23), (.n 748, 5), (.n 919, 88), (.n 921, 4), (.n 923, 4), (.n 1231, 8), (.n 1235, 56), (.n 1242, 0), (.n 1243, 27), (.n 1507, 14), (.n 1514, 0), (.n 1515, 6), (.n 2187, 10), (.n 2194, 0), (.n 2195, 4)] Data.core332.params Data.core332.name ([], []) Data.core332.body = some (⟨206744, []⟩, []) := by
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
  have hb : blockB (wlookJ 333) (womLookJ 333) true [(.n 10, 1664), (.n 12, 416), (.n 14, 8), (.n 16, 10), (.n 18, 22), (.n 20, 44), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 110), (.n 30, 5), (.n 32, 361), (.n 34, 361), (.n 98, 8), (.n 146, 190), (.n 151, 1), (.n 152, 37), (.n 196, 109), (.n 261, 6), (.n 304, 190), (.n 313, 1), (.n 314, 8), (.n 368, 55), (.n 431, 6), (.n 474, 190), (.n 483, 1), (.n 484, 5), (.n 538, 32), (.n 597, 6), (.n 640, 190), (.n 649, 1), (.n 650, 3), (.n 704, 23), (.n 773, 190), (.n 782, 1), (.n 783, 3), (.n 797, 8), (.n 830, 20), (.n 832, 5), (.n 984, 110), (.n 986, 5), (.n 988, 5), (.n 1366, 10), (.n 1370, 56), (.n 1377, 0), (.n 1378, 27), (.n 1654, 14), (.n 1661, 0), (.n 1662, 6), (.n 2376, 10), (.n 2383, 0), (.n 2384, 4), (.n 2398, 6), (.n 2405, 0), (.n 2406, 2)] Data.core333.params Data.core333.name ([], []) Data.core333.body = some (⟨215550, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core333.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_333_0.1 rfl wsplit_333_0.2.2,
      ← blockR_eq ((Data.core333.body.drop 0).take 619), wsplit_333_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_333_619.1 rfl wsplit_333_619.2.2,
      ← blockR_eq ((Data.core333.body.drop 619).take 619), wsplit_333_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_333_1238.1 rfl wsplit_333_1238.2.2,
      ← blockR_eq ((Data.core333.body.drop 1238).take 619), wsplit_333_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_333_1857.1 rfl wsplit_333_1857.2.2,
      ← blockR_eq ((Data.core333.body.drop 1857).take 619), wsplit_333_1857.2.1]
    rw [← blockR_eq (Data.core333.body.drop 2476), wsplit_333_2476]
    rfl
  exact wchkIdx_of_split (fn := Data.core333) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_334 : wchkIdx 334 = true := by
  have hb : blockB (wlookJ 334) (womLookJ 334) true [(.n 10, 1664), (.n 12, 416), (.n 14, 12), (.n 16, 10), (.n 18, 22), (.n 20, 44), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 110), (.n 30, 5), (.n 32, 369), (.n 34, 369), (.n 98, 8), (.n 146, 190), (.n 151, 1), (.n 152, 37), (.n 196, 109), (.n 261, 6), (.n 304, 190), (.n 313, 1), (.n 314, 10), (.n 368, 55), (.n 431, 6), (.n 474, 190), (.n 483, 1), (.n 484, 5), (.n 538, 32), (.n 597, 6), (.n 640, 190), (.n 649, 1), (.n 650, 4), (.n 704, 23), (.n 773, 190), (.n 782, 1), (.n 783, 3), (.n 797, 12), (.n 842, 19), (.n 844, 5), (.n 1005, 110), (.n 1007, 5), (.n 1009, 5), (.n 1419, 10), (.n 1423, 56), (.n 1430, 0), (.n 1431, 27), (.n 1719, 14), (.n 1726, 0), (.n 1727, 6), (.n 2483, 10), (.n 2490, 0), (.n 2491, 4), (.n 2505, 6), (.n 2512, 0), (.n 2513, 2)] Data.core334.params Data.core334.name ([], []) Data.core334.body = some (⟨220304, []⟩, []) := by
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
  have hb : blockB (wlookJ 335) (womLookJ 335) true [(.n 10, 1664), (.n 12, 416), (.n 14, 20), (.n 16, 10), (.n 18, 22), (.n 20, 44), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 110), (.n 30, 5), (.n 32, 367), (.n 34, 367), (.n 98, 8), (.n 146, 190), (.n 151, 1), (.n 152, 37), (.n 196, 109), (.n 261, 6), (.n 304, 190), (.n 313, 1), (.n 314, 10), (.n 368, 55), (.n 431, 6), (.n 474, 190), (.n 483, 1), (.n 484, 6), (.n 538, 32), (.n 597, 6), (.n 640, 190), (.n 649, 1), (.n 650, 4), (.n 704, 23), (.n 773, 190), (.n 782, 1), (.n 783, 3), (.n 797, 20), (.n 866, 18), (.n 868, 5), (.n 1038, 110), (.n 1040, 5), (.n 1042, 5), (.n 1484, 10), (.n 1488, 56), (.n 1495, 0), (.n 1496, 27), (.n 1796, 14), (.n 1803, 0), (.n 1804, 6), (.n 2602, 10), (.n 2609, 0), (.n 2610, 4), (.n 2624, 6), (.n 2631, 0), (.n 2632, 2)] Data.core335.params Data.core335.name ([], []) Data.core335.body = some (⟨226265, []⟩, []) := by
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
  have hb : blockB (wlookJ 336) (womLookJ 336) true [(.n 10, 1664), (.n 12, 416), (.n 14, 36), (.n 16, 10), (.n 18, 22), (.n 20, 44), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 110), (.n 30, 5), (.n 32, 361), (.n 34, 361), (.n 98, 8), (.n 146, 225), (.n 151, 1), (.n 152, 44), (.n 196, 109), (.n 261, 6), (.n 304, 225), (.n 313, 1), (.n 314, 10), (.n 368, 55), (.n 431, 6), (.n 474, 225), (.n 483, 1), (.n 484, 6), (.n 538, 32), (.n 597, 6), (.n 640, 225), (.n 649, 1), (.n 650, 4), (.n 704, 23), (.n 773, 225), (.n 782, 1), (.n 783, 3), (.n 797, 36), (.n 914, 18), (.n 916, 5), (.n 1095, 110), (.n 1097, 5), (.n 1099, 5), (.n 1573, 10), (.n 1577, 56), (.n 1584, 0), (.n 1585, 27), (.n 1897, 14), (.n 1904, 0), (.n 1905, 6), (.n 2745, 10), (.n 2752, 0), (.n 2753, 4), (.n 2767, 6), (.n 2774, 0), (.n 2775, 2)] Data.core336.params Data.core336.name ([], []) Data.core336.body = some (⟨232789, []⟩, []) := by
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
    rw [← blockR_eq (Data.core336.body.drop 3095), wsplit_336_3095]
    rfl
  exact wchkIdx_of_split (fn := Data.core336) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_337 : wchkIdx 337 = true := by
  have hb : blockB (wlookJ 337) (womLookJ 337) true [(.n 10, 1728), (.n 12, 432), (.n 14, 8), (.n 16, 12), (.n 18, 26), (.n 20, 52), (.n 22, 6), (.n 24, 6), (.n 26, 48), (.n 28, 132), (.n 30, 6), (.n 32, 374), (.n 34, 374), (.n 98, 8), (.n 146, 225), (.n 151, 1), (.n 152, 44), (.n 196, 109), (.n 261, 6), (.n 304, 225), (.n 313, 1), (.n 314, 11), (.n 368, 55), (.n 431, 6), (.n 474, 225), (.n 483, 1), (.n 484, 6), (.n 538, 32), (.n 597, 6), (.n 640, 225), (.n 649, 1), (.n 650, 4), (.n 704, 23), (.n 765, 6), (.n 808, 225), (.n 817, 1), (.n 818, 3), (.n 872, 18), (.n 939, 225), (.n 948, 1), (.n 949, 3), (.n 963, 8), (.n 996, 16), (.n 998, 5), (.n 1158, 132), (.n 1160, 6), (.n 1162, 6), (.n 1714, 12), (.n 1718, 56), (.n 1725, 0), (.n 1726, 27), (.n 2050, 14), (.n 2057, 0), (.n 2058, 6), (.n 2940, 10), (.n 2947, 0), (.n 2948, 4), (.n 2962, 6), (.n 2969, 0), (.n 2970, 2), (.n 3516, 6), (.n 3523, 0), (.n 3524, 2)] Data.core337.params Data.core337.name ([], []) Data.core337.body = some (⟨239706, []⟩, []) := by
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
    rw [← blockR_eq (Data.core337.body.drop 3794), wsplit_337_3794]
    rfl
  exact wchkIdx_of_split (fn := Data.core337) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_338 : wchkIdx 338 = true := by
  have hb : blockB (wlookJ 338) (womLookJ 338) true [(.n 10, 1024), (.n 12, 256), (.n 14, 20), (.n 16, 8), (.n 18, 18), (.n 20, 36), (.n 22, 4), (.n 24, 4), (.n 26, 32), (.n 28, 88), (.n 30, 4), (.n 32, 217), (.n 34, 217), (.n 98, 8), (.n 146, 85), (.n 151, 1), (.n 152, 16), (.n 196, 54), (.n 260, 6), (.n 303, 85), (.n 312, 1), (.n 313, 7), (.n 367, 44), (.n 428, 6), (.n 471, 85), (.n 480, 1), (.n 481, 4), (.n 535, 28), (.n 603, 85), (.n 612, 1), (.n 613, 3), (.n 627, 20), (.n 696, 22), (.n 698, 5), (.n 860, 88), (.n 862, 4), (.n 864, 4), (.n 1148, 8), (.n 1152, 28), (.n 1159, 0), (.n 1160, 13), (.n 1769, 12), (.n 1776, 0), (.n 1777, 5), (.n 2143, 8), (.n 2150, 0), (.n 2151, 3)] Data.core338.params Data.core338.name ([], []) Data.core338.body = some (⟨123932, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core338.body)]
    rw [blockB_dropE _ _ _ 0 721 721 wsplit_338_0.1 rfl wsplit_338_0.2.2,
      ← blockR_eq ((Data.core338.body.drop 0).take 721), wsplit_338_0.2.1]
    rw [blockB_dropE _ _ _ 721 721 1442 wsplit_338_721.1 rfl wsplit_338_721.2.2,
      ← blockR_eq ((Data.core338.body.drop 721).take 721), wsplit_338_721.2.1]
    rw [blockB_dropE _ _ _ 1442 721 2163 wsplit_338_1442.1 rfl wsplit_338_1442.2.2,
      ← blockR_eq ((Data.core338.body.drop 1442).take 721), wsplit_338_1442.2.1]
    rw [← blockR_eq (Data.core338.body.drop 2163), wsplit_338_2163]
    rfl
  exact wchkIdx_of_split (fn := Data.core338) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_339 : wchkIdx 339 = true := by
  have hb : blockB (wlookJ 339) (womLookJ 339) true [(.n 10, 1024), (.n 12, 256), (.n 14, 36), (.n 16, 8), (.n 18, 18), (.n 20, 36), (.n 22, 4), (.n 24, 4), (.n 26, 32), (.n 28, 88), (.n 30, 4), (.n 32, 215), (.n 34, 215), (.n 98, 8), (.n 146, 100), (.n 151, 1), (.n 152, 19), (.n 196, 54), (.n 260, 6), (.n 303, 100), (.n 312, 1), (.n 313, 7), (.n 367, 44), (.n 428, 6), (.n 471, 100), (.n 480, 1), (.n 481, 4), (.n 535, 28), (.n 603, 100), (.n 612, 1), (.n 613, 3), (.n 627, 36), (.n 744, 21), (.n 746, 5), (.n 917, 88), (.n 919, 4), (.n 921, 4), (.n 1229, 8), (.n 1233, 28), (.n 1240, 0), (.n 1241, 13), (.n 1880, 12), (.n 1887, 0), (.n 1888, 5), (.n 2278, 8), (.n 2285, 0), (.n 2286, 3)] Data.core339.params Data.core339.name ([], []) Data.core339.body = some (⟨127948, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core339.body)]
    rw [blockB_dropE _ _ _ 0 721 721 wsplit_339_0.1 rfl wsplit_339_0.2.2,
      ← blockR_eq ((Data.core339.body.drop 0).take 721), wsplit_339_0.2.1]
    rw [blockB_dropE _ _ _ 721 721 1442 wsplit_339_721.1 rfl wsplit_339_721.2.2,
      ← blockR_eq ((Data.core339.body.drop 721).take 721), wsplit_339_721.2.1]
    rw [blockB_dropE _ _ _ 1442 721 2163 wsplit_339_1442.1 rfl wsplit_339_1442.2.2,
      ← blockR_eq ((Data.core339.body.drop 1442).take 721), wsplit_339_1442.2.1]
    rw [← blockR_eq (Data.core339.body.drop 2163), wsplit_339_2163]
    rfl
  exact wchkIdx_of_split (fn := Data.core339) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_340 : wchkIdx 340 = true := by
  have hb : blockB (wlookJ 340) (womLookJ 340) true [(.n 10, 1152), (.n 12, 288), (.n 14, 8), (.n 16, 10), (.n 18, 22), (.n 20, 44), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 110), (.n 30, 5), (.n 32, 235), (.n 34, 235), (.n 98, 8), (.n 146, 100), (.n 151, 1), (.n 152, 19), (.n 196, 54), (.n 260, 6), (.n 303, 100), (.n 312, 1), (.n 313, 8), (.n 367, 44), (.n 428, 6), (.n 471, 100), (.n 480, 1), (.n 481, 4), (.n 535, 28), (.n 595, 6), (.n 638, 100), (.n 647, 1), (.n 648, 3), (.n 702, 21), (.n 770, 100), (.n 779, 1), (.n 780, 3), (.n 794, 8), (.n 827, 18), (.n 829, 5), (.n 981, 110), (.n 983, 5), (.n 985, 5), (.n 1363, 10), (.n 1367, 28), (.n 1374, 0), (.n 1375, 13), (.n 2044, 12), (.n 2051, 0), (.n 2052, 5), (.n 2466, 8), (.n 2473, 0), (.n 2474, 3), (.n 2792, 6), (.n 2799, 0), (.n 2800, 2)] Data.core340.params Data.core340.name ([], []) Data.core340.body = some (⟨136648, []⟩, []) := by
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
  have hb : blockB (wlookJ 341) (womLookJ 341) true [(.n 10, 1152), (.n 12, 288), (.n 14, 12), (.n 16, 10), (.n 18, 22), (.n 20, 44), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 110), (.n 30, 5), (.n 32, 234), (.n 34, 234), (.n 98, 8), (.n 146, 100), (.n 151, 1), (.n 152, 19), (.n 196, 54), (.n 260, 6), (.n 303, 100), (.n 312, 1), (.n 313, 8), (.n 367, 44), (.n 428, 6), (.n 471, 100), (.n 480, 1), (.n 481, 5), (.n 535, 28), (.n 595, 6), (.n 638, 100), (.n 647, 1), (.n 648, 3), (.n 702, 21), (.n 770, 100), (.n 779, 1), (.n 780, 3), (.n 794, 12), (.n 839, 17), (.n 841, 5), (.n 1002, 110), (.n 1004, 5), (.n 1006, 5), (.n 1416, 10), (.n 1420, 28), (.n 1427, 0), (.n 1428, 13), (.n 2127, 12), (.n 2134, 0), (.n 2135, 5), (.n 2573, 8), (.n 2580, 0), (.n 2581, 3), (.n 2923, 6), (.n 2930, 0), (.n 2931, 2)] Data.core341.params Data.core341.name ([], []) Data.core341.body = some (⟨138802, []⟩, []) := by
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
    rw [← blockR_eq (Data.core341.body.drop 3095), wsplit_341_3095]
    rfl
  exact wchkIdx_of_split (fn := Data.core341) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_342 : wchkIdx 342 = true := by
  have hb : blockB (wlookJ 342) (womLookJ 342) true [(.n 10, 1152), (.n 12, 288), (.n 14, 20), (.n 16, 10), (.n 18, 22), (.n 20, 44), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 110), (.n 30, 5), (.n 32, 233), (.n 34, 233), (.n 98, 8), (.n 146, 115), (.n 151, 1), (.n 152, 22), (.n 196, 54), (.n 260, 6), (.n 303, 115), (.n 312, 1), (.n 313, 8), (.n 367, 44), (.n 428, 6), (.n 471, 115), (.n 480, 1), (.n 481, 5), (.n 535, 28), (.n 595, 6), (.n 638, 115), (.n 647, 1), (.n 648, 4), (.n 702, 21), (.n 770, 115), (.n 779, 1), (.n 780, 3), (.n 794, 20), (.n 863, 17), (.n 865, 5), (.n 1035, 110), (.n 1037, 5), (.n 1039, 5), (.n 1481, 10), (.n 1485, 28), (.n 1492, 0), (.n 1493, 13), (.n 2222, 12), (.n 2229, 0), (.n 2230, 5), (.n 2692, 8), (.n 2699, 0), (.n 2700, 3), (.n 3066, 6), (.n 3073, 0), (.n 3074, 2)] Data.core342.params Data.core342.name ([], []) Data.core342.body = some (⟨142658, []⟩, []) := by
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
  have hb : blockB (wlookJ 343) (womLookJ 343) true [(.n 10, 1152), (.n 12, 288), (.n 14, 36), (.n 16, 10), (.n 18, 22), (.n 20, 44), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 110), (.n 30, 5), (.n 32, 227), (.n 34, 227), (.n 98, 8), (.n 146, 115), (.n 151, 1), (.n 152, 22), (.n 196, 54), (.n 260, 6), (.n 303, 115), (.n 312, 1), (.n 313, 9), (.n 367, 44), (.n 428, 6), (.n 471, 115), (.n 480, 1), (.n 481, 5), (.n 535, 28), (.n 595, 6), (.n 638, 115), (.n 647, 1), (.n 648, 4), (.n 702, 21), (.n 770, 115), (.n 779, 1), (.n 780, 3), (.n 794, 36), (.n 911, 17), (.n 913, 5), (.n 1092, 110), (.n 1094, 5), (.n 1096, 5), (.n 1570, 10), (.n 1574, 28), (.n 1581, 0), (.n 1582, 13), (.n 2341, 12), (.n 2348, 0), (.n 2349, 5), (.n 2835, 8), (.n 2842, 0), (.n 2843, 3), (.n 3233, 6), (.n 3240, 0), (.n 3241, 2)] Data.core343.params Data.core343.name ([], []) Data.core343.body = some (⟨146174, []⟩, []) := by
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
  have hb : blockB (wlookJ 344) (womLookJ 344) true [(.n 10, 1216), (.n 12, 304), (.n 14, 8), (.n 16, 12), (.n 18, 26), (.n 20, 52), (.n 22, 6), (.n 24, 6), (.n 26, 48), (.n 28, 132), (.n 30, 6), (.n 32, 245), (.n 34, 245), (.n 98, 8), (.n 146, 115), (.n 151, 1), (.n 152, 22), (.n 196, 54), (.n 260, 6), (.n 303, 115), (.n 312, 1), (.n 313, 9), (.n 367, 44), (.n 428, 6), (.n 471, 115), (.n 480, 1), (.n 481, 6), (.n 535, 28), (.n 595, 6), (.n 638, 115), (.n 647, 1), (.n 648, 4), (.n 702, 21), (.n 762, 6), (.n 805, 115), (.n 814, 1), (.n 815, 3), (.n 869, 17), (.n 936, 115), (.n 945, 1), (.n 946, 3), (.n 960, 8), (.n 993, 15), (.n 995, 5), (.n 1155, 132), (.n 1157, 6), (.n 1159, 6), (.n 1711, 12), (.n 1715, 28), (.n 1722, 0), (.n 1723, 13), (.n 2512, 12), (.n 2519, 0), (.n 2520, 5), (.n 3030, 8), (.n 3037, 0), (.n 3038, 3), (.n 3452, 6), (.n 3459, 0), (.n 3460, 2), (.n 3854, 6), (.n 3861, 0), (.n 3862, 2)] Data.core344.params Data.core344.name ([], []) Data.core344.body = some (⟨152624, []⟩, []) := by
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
    rw [← blockR_eq (Data.core344.body.drop 3794), wsplit_344_3794]
    rfl
  exact wchkIdx_of_split (fn := Data.core344) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_345 : wchkIdx 345 = true := by
  have hb : blockB (wlookJ 345) (womLookJ 345) true [(.n 10, 1024), (.n 12, 256), (.n 14, 20), (.n 16, 8), (.n 18, 18), (.n 20, 36), (.n 22, 4), (.n 24, 4), (.n 26, 32), (.n 28, 88), (.n 30, 4), (.n 32, 172), (.n 34, 172), (.n 98, 8), (.n 146, 70), (.n 151, 1), (.n 152, 13), (.n 196, 36), (.n 258, 6), (.n 301, 70), (.n 310, 1), (.n 311, 6), (.n 365, 37), (.n 426, 6), (.n 469, 70), (.n 478, 1), (.n 479, 4), (.n 533, 25), (.n 601, 70), (.n 610, 1), (.n 611, 3), (.n 625, 20), (.n 694, 20), (.n 696, 5), (.n 858, 88), (.n 860, 4), (.n 862, 4), (.n 1146, 8), (.n 1150, 20), (.n 1157, 0), (.n 1158, 9), (.n 1291, 10), (.n 1298, 0), (.n 1299, 4), (.n 1753, 8), (.n 1760, 0), (.n 1761, 3)] Data.core345.params Data.core345.name ([], []) Data.core345.body = some (⟨96943, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core345.body)]
    rw [blockB_dropE _ _ _ 0 721 721 wsplit_345_0.1 rfl wsplit_345_0.2.2,
      ← blockR_eq ((Data.core345.body.drop 0).take 721), wsplit_345_0.2.1]
    rw [blockB_dropE _ _ _ 721 721 1442 wsplit_345_721.1 rfl wsplit_345_721.2.2,
      ← blockR_eq ((Data.core345.body.drop 721).take 721), wsplit_345_721.2.1]
    rw [← blockR_eq (Data.core345.body.drop 1442), wsplit_345_1442]
    rfl
  exact wchkIdx_of_split (fn := Data.core345) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_346 : wchkIdx 346 = true := by
  have hb : blockB (wlookJ 346) (womLookJ 346) true [(.n 10, 1024), (.n 12, 256), (.n 14, 36), (.n 16, 8), (.n 18, 18), (.n 20, 36), (.n 22, 4), (.n 24, 4), (.n 26, 32), (.n 28, 88), (.n 30, 4), (.n 32, 169), (.n 34, 169), (.n 98, 8), (.n 146, 70), (.n 151, 1), (.n 152, 13), (.n 196, 36), (.n 258, 6), (.n 301, 70), (.n 310, 1), (.n 311, 7), (.n 365, 37), (.n 426, 6), (.n 469, 70), (.n 478, 1), (.n 479, 4), (.n 533, 25), (.n 601, 70), (.n 610, 1), (.n 611, 3), (.n 625, 36), (.n 742, 19), (.n 744, 5), (.n 915, 88), (.n 917, 4), (.n 919, 4), (.n 1227, 8), (.n 1231, 20), (.n 1238, 0), (.n 1239, 9), (.n 1378, 10), (.n 1385, 0), (.n 1386, 4), (.n 1870, 8), (.n 1877, 0), (.n 1878, 3)] Data.core346.params Data.core346.name ([], []) Data.core346.body = some (⟨102051, []⟩, []) := by
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
  have hb : blockB (wlookJ 347) (womLookJ 347) true [(.n 10, 1152), (.n 12, 288), (.n 14, 8), (.n 16, 10), (.n 18, 22), (.n 20, 44), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 110), (.n 30, 5), (.n 32, 192), (.n 34, 192), (.n 98, 8), (.n 146, 70), (.n 151, 1), (.n 152, 13), (.n 196, 36), (.n 258, 6), (.n 301, 70), (.n 310, 1), (.n 311, 7), (.n 365, 37), (.n 426, 6), (.n 469, 70), (.n 478, 1), (.n 479, 5), (.n 533, 25), (.n 593, 6), (.n 636, 70), (.n 645, 1), (.n 646, 3), (.n 700, 19), (.n 768, 70), (.n 777, 1), (.n 778, 3), (.n 792, 8), (.n 825, 17), (.n 827, 5), (.n 979, 110), (.n 981, 5), (.n 983, 5), (.n 1361, 10), (.n 1365, 20), (.n 1372, 0), (.n 1373, 9), (.n 1518, 10), (.n 1525, 0), (.n 1526, 4), (.n 2040, 8), (.n 2047, 0), (.n 2048, 3), (.n 2138, 6), (.n 2145, 0), (.n 2146, 2)] Data.core347.params Data.core347.name ([], []) Data.core347.body = some (⟨108393, []⟩, []) := by
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
  have hb : blockB (wlookJ 348) (womLookJ 348) true [(.n 10, 1088), (.n 12, 272), (.n 14, 12), (.n 16, 10), (.n 18, 22), (.n 20, 44), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 110), (.n 30, 5), (.n 32, 192), (.n 34, 192), (.n 98, 8), (.n 146, 80), (.n 151, 1), (.n 152, 15), (.n 196, 36), (.n 258, 6), (.n 301, 80), (.n 310, 1), (.n 311, 7), (.n 365, 37), (.n 426, 6), (.n 469, 80), (.n 478, 1), (.n 479, 5), (.n 533, 25), (.n 593, 6), (.n 636, 80), (.n 645, 1), (.n 646, 4), (.n 700, 19), (.n 768, 80), (.n 777, 1), (.n 778, 3), (.n 792, 12), (.n 837, 16), (.n 839, 5), (.n 1000, 110), (.n 1002, 5), (.n 1004, 5), (.n 1414, 10), (.n 1418, 20), (.n 1425, 0), (.n 1426, 9), (.n 1577, 10), (.n 1584, 0), (.n 1585, 4), (.n 2129, 8), (.n 2136, 0), (.n 2137, 3), (.n 2233, 6), (.n 2240, 0), (.n 2241, 2)] Data.core348.params Data.core348.name ([], []) Data.core348.body = some (⟨110756, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core348.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_348_0.1 rfl wsplit_348_0.2.2,
      ← blockR_eq ((Data.core348.body.drop 0).take 619), wsplit_348_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_348_619.1 rfl wsplit_348_619.2.2,
      ← blockR_eq ((Data.core348.body.drop 619).take 619), wsplit_348_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_348_1238.1 rfl wsplit_348_1238.2.2,
      ← blockR_eq ((Data.core348.body.drop 1238).take 619), wsplit_348_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_348_1857.1 rfl wsplit_348_1857.2.2,
      ← blockR_eq ((Data.core348.body.drop 1857).take 619), wsplit_348_1857.2.1]
    rw [← blockR_eq (Data.core348.body.drop 2476), wsplit_348_2476]
    rfl
  exact wchkIdx_of_split (fn := Data.core348) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_349 : wchkIdx 349 = true := by
  have hb : blockB (wlookJ 349) (womLookJ 349) true [(.n 10, 1088), (.n 12, 272), (.n 14, 20), (.n 16, 10), (.n 18, 22), (.n 20, 44), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 110), (.n 30, 5), (.n 32, 187), (.n 34, 187), (.n 98, 8), (.n 146, 80), (.n 151, 1), (.n 152, 15), (.n 196, 36), (.n 258, 6), (.n 301, 80), (.n 310, 1), (.n 311, 8), (.n 365, 37), (.n 426, 6), (.n 469, 80), (.n 478, 1), (.n 479, 5), (.n 533, 25), (.n 593, 6), (.n 636, 80), (.n 645, 1), (.n 646, 4), (.n 700, 19), (.n 768, 80), (.n 777, 1), (.n 778, 3), (.n 792, 20), (.n 861, 16), (.n 863, 5), (.n 1033, 110), (.n 1035, 5), (.n 1037, 5), (.n 1479, 10), (.n 1483, 20), (.n 1490, 0), (.n 1491, 9), (.n 1648, 10), (.n 1655, 0), (.n 1656, 4), (.n 2230, 8), (.n 2237, 0), (.n 2238, 3), (.n 2340, 6), (.n 2347, 0), (.n 2348, 2)] Data.core349.params Data.core349.name ([], []) Data.core349.body = some (⟨113026, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core349.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_349_0.1 rfl wsplit_349_0.2.2,
      ← blockR_eq ((Data.core349.body.drop 0).take 619), wsplit_349_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_349_619.1 rfl wsplit_349_619.2.2,
      ← blockR_eq ((Data.core349.body.drop 619).take 619), wsplit_349_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_349_1238.1 rfl wsplit_349_1238.2.2,
      ← blockR_eq ((Data.core349.body.drop 1238).take 619), wsplit_349_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_349_1857.1 rfl wsplit_349_1857.2.2,
      ← blockR_eq ((Data.core349.body.drop 1857).take 619), wsplit_349_1857.2.1]
    rw [← blockR_eq (Data.core349.body.drop 2476), wsplit_349_2476]
    rfl
  exact wchkIdx_of_split (fn := Data.core349) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_350 : wchkIdx 350 = true := by
  have hb : blockB (wlookJ 350) (womLookJ 350) true [(.n 10, 1088), (.n 12, 272), (.n 14, 36), (.n 16, 10), (.n 18, 22), (.n 20, 44), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 110), (.n 30, 5), (.n 32, 182), (.n 34, 182), (.n 98, 8), (.n 146, 80), (.n 151, 1), (.n 152, 15), (.n 196, 36), (.n 258, 6), (.n 301, 80), (.n 310, 1), (.n 311, 8), (.n 365, 37), (.n 426, 6), (.n 469, 80), (.n 478, 1), (.n 479, 5), (.n 533, 25), (.n 593, 6), (.n 636, 80), (.n 645, 1), (.n 646, 4), (.n 700, 19), (.n 768, 80), (.n 777, 1), (.n 778, 3), (.n 792, 36), (.n 909, 16), (.n 911, 5), (.n 1090, 110), (.n 1092, 5), (.n 1094, 5), (.n 1568, 10), (.n 1572, 20), (.n 1579, 0), (.n 1580, 9), (.n 1743, 10), (.n 1750, 0), (.n 1751, 4), (.n 2355, 8), (.n 2362, 0), (.n 2363, 3), (.n 2471, 6), (.n 2478, 0), (.n 2479, 2)] Data.core350.params Data.core350.name ([], []) Data.core350.body = some (⟨116142, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core350.body)]
    rw [blockB_dropE _ _ _ 0 619 619 wsplit_350_0.1 rfl wsplit_350_0.2.2,
      ← blockR_eq ((Data.core350.body.drop 0).take 619), wsplit_350_0.2.1]
    rw [blockB_dropE _ _ _ 619 619 1238 wsplit_350_619.1 rfl wsplit_350_619.2.2,
      ← blockR_eq ((Data.core350.body.drop 619).take 619), wsplit_350_619.2.1]
    rw [blockB_dropE _ _ _ 1238 619 1857 wsplit_350_1238.1 rfl wsplit_350_1238.2.2,
      ← blockR_eq ((Data.core350.body.drop 1238).take 619), wsplit_350_1238.2.1]
    rw [blockB_dropE _ _ _ 1857 619 2476 wsplit_350_1857.1 rfl wsplit_350_1857.2.2,
      ← blockR_eq ((Data.core350.body.drop 1857).take 619), wsplit_350_1857.2.1]
    rw [← blockR_eq (Data.core350.body.drop 2476), wsplit_350_2476]
    rfl
  exact wchkIdx_of_split (fn := Data.core350) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_351 : wchkIdx 351 = true := by
  have hb : blockB (wlookJ 351) (womLookJ 351) true [(.n 10, 1152), (.n 12, 288), (.n 14, 8), (.n 16, 12), (.n 18, 26), (.n 20, 52), (.n 22, 6), (.n 24, 6), (.n 26, 48), (.n 28, 132), (.n 30, 6), (.n 32, 196), (.n 34, 196), (.n 98, 8), (.n 146, 80), (.n 151, 1), (.n 152, 15), (.n 196, 36), (.n 258, 6), (.n 301, 80), (.n 310, 1), (.n 311, 8), (.n 365, 37), (.n 426, 6), (.n 469, 80), (.n 478, 1), (.n 479, 5), (.n 533, 25), (.n 593, 6), (.n 636, 80), (.n 645, 1), (.n 646, 4), (.n 700, 19), (.n 760, 6), (.n 803, 80), (.n 812, 1), (.n 813, 3), (.n 867, 16), (.n 933, 80), (.n 942, 1), (.n 943, 3), (.n 957, 8), (.n 990, 15), (.n 992, 5), (.n 1152, 132), (.n 1154, 6), (.n 1156, 6), (.n 1708, 12), (.n 1712, 20), (.n 1719, 0), (.n 1720, 9), (.n 1889, 10), (.n 1896, 0), (.n 1897, 4), (.n 2531, 8), (.n 2538, 0), (.n 2539, 3), (.n 2653, 6), (.n 2660, 0), (.n 2661, 2), (.n 2903, 6), (.n 2910, 0), (.n 2911, 2)] Data.core351.params Data.core351.name ([], []) Data.core351.body = some (⟨122185, []⟩, []) := by
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
    rw [← blockR_eq (Data.core351.body.drop 3252), wsplit_351_3252]
    rfl
  exact wchkIdx_of_split (fn := Data.core351) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_352 : wchkIdx 352 = true := by
  have hb : blockB (wlookJ 352) (womLookJ 352) true [(.n 10, 640), (.n 12, 160), (.n 14, 20), (.n 16, 8), (.n 18, 18), (.n 20, 36), (.n 22, 4), (.n 24, 4), (.n 26, 32), (.n 28, 88), (.n 30, 4), (.n 32, 145), (.n 34, 145), (.n 98, 8), (.n 146, 55), (.n 151, 1), (.n 152, 10), (.n 196, 27), (.n 259, 6), (.n 302, 55), (.n 311, 1), (.n 312, 6), (.n 366, 32), (.n 425, 6), (.n 468, 55), (.n 477, 1), (.n 478, 4), (.n 532, 23), (.n 601, 55), (.n 610, 1), (.n 611, 3), (.n 625, 20), (.n 694, 18), (.n 696, 5), (.n 858, 88), (.n 860, 4), (.n 862, 4), (.n 1146, 8), (.n 1150, 14), (.n 1157, 0), (.n 1158, 6), (.n 2005, 10), (.n 2012, 0), (.n 2013, 4), (.n 2027, 6), (.n 2034, 0), (.n 2035, 2)] Data.core352.params Data.core352.name ([], []) Data.core352.body = some (⟨81934, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core352.body)]
    rw [blockB_dropE _ _ _ 0 721 721 wsplit_352_0.1 rfl wsplit_352_0.2.2,
      ← blockR_eq ((Data.core352.body.drop 0).take 721), wsplit_352_0.2.1]
    rw [blockB_dropE _ _ _ 721 721 1442 wsplit_352_721.1 rfl wsplit_352_721.2.2,
      ← blockR_eq ((Data.core352.body.drop 721).take 721), wsplit_352_721.2.1]
    rw [blockB_dropE _ _ _ 1442 721 2163 wsplit_352_1442.1 rfl wsplit_352_1442.2.2,
      ← blockR_eq ((Data.core352.body.drop 1442).take 721), wsplit_352_1442.2.1]
    rw [← blockR_eq (Data.core352.body.drop 2163), wsplit_352_2163]
    rfl
  exact wchkIdx_of_split (fn := Data.core352) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_353 : wchkIdx 353 = true := by
  have hb : blockB (wlookJ 353) (womLookJ 353) true [(.n 10, 640), (.n 12, 160), (.n 14, 36), (.n 16, 8), (.n 18, 18), (.n 20, 36), (.n 22, 4), (.n 24, 4), (.n 26, 32), (.n 28, 88), (.n 30, 4), (.n 32, 141), (.n 34, 141), (.n 98, 8), (.n 146, 55), (.n 151, 1), (.n 152, 10), (.n 196, 27), (.n 259, 6), (.n 302, 55), (.n 311, 1), (.n 312, 6), (.n 366, 32), (.n 425, 6), (.n 468, 55), (.n 477, 1), (.n 478, 4), (.n 532, 23), (.n 601, 55), (.n 610, 1), (.n 611, 3), (.n 625, 36), (.n 742, 18), (.n 744, 5), (.n 915, 88), (.n 917, 4), (.n 919, 4), (.n 1227, 8), (.n 1231, 14), (.n 1238, 0), (.n 1239, 6), (.n 2128, 10), (.n 2135, 0), (.n 2136, 4), (.n 2150, 6), (.n 2157, 0), (.n 2158, 2)] Data.core353.params Data.core353.name ([], []) Data.core353.body = some (⟨85115, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core353.body)]
    rw [blockB_dropE _ _ _ 0 721 721 wsplit_353_0.1 rfl wsplit_353_0.2.2,
      ← blockR_eq ((Data.core353.body.drop 0).take 721), wsplit_353_0.2.1]
    rw [blockB_dropE _ _ _ 721 721 1442 wsplit_353_721.1 rfl wsplit_353_721.2.2,
      ← blockR_eq ((Data.core353.body.drop 721).take 721), wsplit_353_721.2.1]
    rw [blockB_dropE _ _ _ 1442 721 2163 wsplit_353_1442.1 rfl wsplit_353_1442.2.2,
      ← blockR_eq ((Data.core353.body.drop 1442).take 721), wsplit_353_1442.2.1]
    rw [blockB_dropE _ _ _ 2163 721 2884 wsplit_353_2163.1 rfl wsplit_353_2163.2.2,
      ← blockR_eq ((Data.core353.body.drop 2163).take 721), wsplit_353_2163.2.1]
    rw [← blockR_eq (Data.core353.body.drop 2884), wsplit_353_2884]
    rfl
  exact wchkIdx_of_split (fn := Data.core353) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_354 : wchkIdx 354 = true := by
  have hb : blockB (wlookJ 354) (womLookJ 354) true [(.n 10, 704), (.n 12, 176), (.n 14, 8), (.n 16, 10), (.n 18, 22), (.n 20, 44), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 110), (.n 30, 5), (.n 32, 154), (.n 34, 154), (.n 98, 8), (.n 146, 60), (.n 151, 1), (.n 152, 11), (.n 196, 27), (.n 259, 6), (.n 302, 60), (.n 311, 1), (.n 312, 6), (.n 366, 32), (.n 425, 6), (.n 468, 60), (.n 477, 1), (.n 478, 4), (.n 532, 23), (.n 593, 6), (.n 636, 60), (.n 645, 1), (.n 646, 3), (.n 700, 18), (.n 767, 60), (.n 776, 1), (.n 777, 3), (.n 791, 8), (.n 824, 16), (.n 826, 5), (.n 978, 110), (.n 980, 5), (.n 982, 5), (.n 1360, 10), (.n 1364, 14), (.n 1371, 0), (.n 1372, 6), (.n 2303, 10), (.n 2310, 0), (.n 2311, 4), (.n 2325, 6), (.n 2332, 0), (.n 2333, 2), (.n 2879, 6), (.n 2886, 0), (.n 2887, 2)] Data.core354.params Data.core354.name ([], []) Data.core354.body = some (⟨90929, []⟩, []) := by
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
    rw [← blockR_eq (Data.core354.body.drop 3095), wsplit_354_3095]
    rfl
  exact wchkIdx_of_split (fn := Data.core354) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_355 : wchkIdx 355 = true := by
  have hb : blockB (wlookJ 355) (womLookJ 355) true [(.n 10, 704), (.n 12, 176), (.n 14, 12), (.n 16, 10), (.n 18, 22), (.n 20, 44), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 110), (.n 30, 5), (.n 32, 150), (.n 34, 150), (.n 98, 8), (.n 146, 60), (.n 151, 1), (.n 152, 11), (.n 196, 27), (.n 259, 6), (.n 302, 60), (.n 311, 1), (.n 312, 7), (.n 366, 32), (.n 425, 6), (.n 468, 60), (.n 477, 1), (.n 478, 4), (.n 532, 23), (.n 593, 6), (.n 636, 60), (.n 645, 1), (.n 646, 3), (.n 700, 18), (.n 767, 60), (.n 776, 1), (.n 777, 3), (.n 791, 12), (.n 836, 15), (.n 838, 5), (.n 999, 110), (.n 1001, 5), (.n 1003, 5), (.n 1413, 10), (.n 1417, 14), (.n 1424, 0), (.n 1425, 6), (.n 2398, 10), (.n 2405, 0), (.n 2406, 4), (.n 2420, 6), (.n 2427, 0), (.n 2428, 2), (.n 3016, 6), (.n 3023, 0), (.n 3024, 2)] Data.core355.params Data.core355.name ([], []) Data.core355.body = some (⟨92156, []⟩, []) := by
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
    rw [← blockR_eq (Data.core355.body.drop 3095), wsplit_355_3095]
    rfl
  exact wchkIdx_of_split (fn := Data.core355) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_356 : wchkIdx 356 = true := by
  have hb : blockB (wlookJ 356) (womLookJ 356) true [(.n 10, 704), (.n 12, 176), (.n 14, 20), (.n 16, 10), (.n 18, 22), (.n 20, 44), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 110), (.n 30, 5), (.n 32, 151), (.n 34, 151), (.n 98, 8), (.n 146, 60), (.n 151, 1), (.n 152, 11), (.n 196, 27), (.n 259, 6), (.n 302, 60), (.n 311, 1), (.n 312, 7), (.n 366, 32), (.n 425, 6), (.n 468, 60), (.n 477, 1), (.n 478, 5), (.n 532, 23), (.n 593, 6), (.n 636, 60), (.n 645, 1), (.n 646, 3), (.n 700, 18), (.n 767, 60), (.n 776, 1), (.n 777, 3), (.n 791, 20), (.n 860, 15), (.n 862, 5), (.n 1032, 110), (.n 1034, 5), (.n 1036, 5), (.n 1478, 10), (.n 1482, 14), (.n 1489, 0), (.n 1490, 6), (.n 2505, 10), (.n 2512, 0), (.n 2513, 4), (.n 2527, 6), (.n 2534, 0), (.n 2535, 2), (.n 3165, 6), (.n 3172, 0), (.n 3173, 2)] Data.core356.params Data.core356.name ([], []) Data.core356.body = some (⟨94557, []⟩, []) := by
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
    rw [← blockR_eq (Data.core356.body.drop 3095), wsplit_356_3095]
    rfl
  exact wchkIdx_of_split (fn := Data.core356) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_357 : wchkIdx 357 = true := by
  have hb : blockB (wlookJ 357) (womLookJ 357) true [(.n 10, 704), (.n 12, 176), (.n 14, 36), (.n 16, 10), (.n 18, 22), (.n 20, 44), (.n 22, 5), (.n 24, 5), (.n 26, 40), (.n 28, 110), (.n 30, 5), (.n 32, 153), (.n 34, 153), (.n 98, 8), (.n 146, 60), (.n 151, 1), (.n 152, 11), (.n 196, 27), (.n 259, 6), (.n 302, 60), (.n 311, 1), (.n 312, 7), (.n 366, 32), (.n 425, 6), (.n 468, 60), (.n 477, 1), (.n 478, 5), (.n 532, 23), (.n 593, 6), (.n 636, 60), (.n 645, 1), (.n 646, 4), (.n 700, 18), (.n 767, 60), (.n 776, 1), (.n 777, 3), (.n 791, 36), (.n 908, 15), (.n 910, 5), (.n 1089, 110), (.n 1091, 5), (.n 1093, 5), (.n 1567, 10), (.n 1571, 14), (.n 1578, 0), (.n 1579, 6), (.n 2636, 10), (.n 2643, 0), (.n 2644, 4), (.n 2658, 6), (.n 2665, 0), (.n 2666, 2), (.n 3338, 6), (.n 3345, 0), (.n 3346, 2)] Data.core357.params Data.core357.name ([], []) Data.core357.body = some (⟨98853, []⟩, []) := by
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
    rw [← blockR_eq (Data.core357.body.drop 3714), wsplit_357_3714]
    rfl
  exact wchkIdx_of_split (fn := Data.core357) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_358 : wchkIdx 358 = true := by
  have hb : blockB (wlookJ 358) (womLookJ 358) true [(.n 10, 768), (.n 12, 192), (.n 14, 8), (.n 16, 12), (.n 18, 26), (.n 20, 52), (.n 22, 6), (.n 24, 6), (.n 26, 48), (.n 28, 132), (.n 30, 6), (.n 32, 169), (.n 34, 169), (.n 98, 8), (.n 146, 75), (.n 151, 1), (.n 152, 14), (.n 196, 27), (.n 259, 6), (.n 302, 75), (.n 311, 1), (.n 312, 7), (.n 366, 32), (.n 425, 6), (.n 468, 75), (.n 477, 1), (.n 478, 5), (.n 532, 23), (.n 593, 6), (.n 636, 75), (.n 645, 1), (.n 646, 4), (.n 700, 18), (.n 759, 6), (.n 802, 75), (.n 811, 1), (.n 812, 3), (.n 866, 15), (.n 934, 75), (.n 943, 1), (.n 944, 3), (.n 958, 8), (.n 991, 14), (.n 993, 5), (.n 1153, 132), (.n 1155, 6), (.n 1157, 6), (.n 1709, 12), (.n 1713, 14), (.n 1720, 0), (.n 1721, 6), (.n 2820, 10), (.n 2827, 0), (.n 2828, 4), (.n 2842, 6), (.n 2849, 0), (.n 2850, 2), (.n 3564, 6), (.n 3571, 0), (.n 3572, 2), (.n 3738, 4), (.n 3745, 0), (.n 3746, 1)] Data.core358.params Data.core358.name ([], []) Data.core358.body = some (⟨105245, []⟩, []) := by
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
    rw [← blockR_eq (Data.core358.body.drop 4336), wsplit_358_4336]
    rfl
  exact wchkIdx_of_split (fn := Data.core358) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem wchkIdx_all : ∀ j < 1035, wchkIdx j = true := by
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
  by_cases h25 : j < 548
  · exact wstaticRange_527.get (by omega) (by omega)
  by_cases h26 : j < 568
  · exact wstaticRange_548.get (by omega) (by omega)
  by_cases h27 : j < 587
  · exact wstaticRange_568.get (by omega) (by omega)
  by_cases h28 : j < 606
  · exact wstaticRange_587.get (by omega) (by omega)
  by_cases h29 : j < 623
  · exact wstaticRange_606.get (by omega) (by omega)
  by_cases h30 : j < 640
  · exact wstaticRange_623.get (by omega) (by omega)
  by_cases h31 : j < 658
  · exact wstaticRange_640.get (by omega) (by omega)
  by_cases h32 : j < 672
  · exact wstaticRange_658.get (by omega) (by omega)
  by_cases h33 : j < 689
  · exact wstaticRange_672.get (by omega) (by omega)
  by_cases h34 : j < 707
  · exact wstaticRange_689.get (by omega) (by omega)
  by_cases h35 : j < 725
  · exact wstaticRange_707.get (by omega) (by omega)
  by_cases h36 : j < 739
  · exact wstaticRange_725.get (by omega) (by omega)
  by_cases h37 : j < 757
  · exact wstaticRange_739.get (by omega) (by omega)
  by_cases h38 : j < 776
  · exact wstaticRange_757.get (by omega) (by omega)
  by_cases h39 : j < 789
  · exact wstaticRange_776.get (by omega) (by omega)
  by_cases h40 : j < 807
  · exact wstaticRange_789.get (by omega) (by omega)
  by_cases h41 : j < 820
  · exact wstaticRange_807.get (by omega) (by omega)
  by_cases h42 : j < 837
  · exact wstaticRange_820.get (by omega) (by omega)
  by_cases h43 : j < 855
  · exact wstaticRange_837.get (by omega) (by omega)
  by_cases h44 : j < 874
  · exact wstaticRange_855.get (by omega) (by omega)
  by_cases h45 : j < 898
  · exact wstaticRange_874.get (by omega) (by omega)
  by_cases h46 : j < 921
  · exact wstaticRange_898.get (by omega) (by omega)
  by_cases h47 : j < 938
  · exact wstaticRange_921.get (by omega) (by omega)
  by_cases h48 : j < 953
  · exact wstaticRange_938.get (by omega) (by omega)
  by_cases h49 : j < 965
  · exact wstaticRange_953.get (by omega) (by omega)
  by_cases h50 : j < 979
  · exact wstaticRange_965.get (by omega) (by omega)
  by_cases h51 : j < 992
  · exact wstaticRange_979.get (by omega) (by omega)
  by_cases h52 : j < 1002
  · exact wstaticRange_992.get (by omega) (by omega)
  by_cases h53 : j < 1014
  · exact wstaticRange_1002.get (by omega) (by omega)
  by_cases h54 : j < 1023
  · exact wstaticRange_1014.get (by omega) (by omega)
  by_cases h55 : j < 1031
  · exact wstaticRange_1023.get (by omega) (by omega)
  exact wstaticRange_1031.get (by omega) (by omega)

end
end LeanVM.Guest
