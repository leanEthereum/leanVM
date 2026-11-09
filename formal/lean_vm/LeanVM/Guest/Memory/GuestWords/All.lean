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
theorem wchkIdx_302 : wchkIdx 302 = true := by
  have hb : blockB (wlookJ 302) (womLookJ 302) true [(.n 12, 1536), (.n 14, 384), (.n 16, 16), (.n 18, 8), (.n 20, 18), (.n 22, 4), (.n 24, 4), (.n 26, 353), (.n 28, 353), (.n 30, 128), (.n 160, 88), (.n 162, 16), (.n 342, 110), (.n 347, 0), (.n 348, 21), (.n 392, 64), (.n 396, 112), (.n 579, 110), (.n 584, 0), (.n 585, 5), (.n 622, 64), (.n 638, 56), (.n 821, 110), (.n 826, 0), (.n 827, 3), (.n 862, 64), (.n 878, 32), (.n 959, 110), (.n 964, 0), (.n 965, 2), (.n 1002, 64), (.n 1018, 23), (.n 1032, 5), (.n 1245, 88), (.n 1247, 4), (.n 1525, 5), (.n 1529, 29), (.n 1535, 0), (.n 1536, 28), (.n 1543, 8), (.n 1549, 0), (.n 1550, 7), (.n 1557, 5), (.n 1563, 0), (.n 1564, 4), (.n 1571, 3), (.n 1577, 0), (.n 1578, 2)] Data.core302.params Data.core302.name ([], []) Data.core302.body = some (⟨209308, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core302.body)]
    rw [blockB_dropE _ _ _ 0 707 707 wsplit_302_0.1 rfl wsplit_302_0.2.2,
      ← blockR_eq ((Data.core302.body.drop 0).take 707), wsplit_302_0.2.1]
    rw [blockB_dropE _ _ _ 707 707 1414 wsplit_302_707.1 rfl wsplit_302_707.2.2,
      ← blockR_eq ((Data.core302.body.drop 707).take 707), wsplit_302_707.2.1]
    rw [← blockR_eq (Data.core302.body.drop 1414), wsplit_302_1414]
    rfl
  exact wchkIdx_of_split (fn := Data.core302) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_303 : wchkIdx 303 = true := by
  have hb : blockB (wlookJ 303) (womLookJ 303) true [(.n 12, 1536), (.n 14, 384), (.n 16, 32), (.n 18, 8), (.n 20, 18), (.n 22, 4), (.n 24, 4), (.n 26, 356), (.n 28, 356), (.n 30, 128), (.n 160, 88), (.n 162, 16), (.n 342, 120), (.n 347, 0), (.n 348, 23), (.n 392, 64), (.n 396, 112), (.n 579, 120), (.n 584, 0), (.n 585, 6), (.n 622, 64), (.n 638, 56), (.n 821, 120), (.n 826, 0), (.n 827, 3), (.n 862, 64), (.n 878, 32), (.n 959, 120), (.n 964, 0), (.n 965, 2), (.n 1002, 64), (.n 1018, 23), (.n 1032, 5), (.n 1257, 88), (.n 1259, 4), (.n 1565, 5), (.n 1569, 29), (.n 1575, 0), (.n 1576, 28), (.n 1583, 8), (.n 1589, 0), (.n 1590, 7), (.n 1597, 5), (.n 1603, 0), (.n 1604, 4), (.n 1611, 3), (.n 1617, 0), (.n 1618, 2)] Data.core303.params Data.core303.name ([], []) Data.core303.body = some (⟨212923, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core303.body)]
    rw [blockB_dropE _ _ _ 0 707 707 wsplit_303_0.1 rfl wsplit_303_0.2.2,
      ← blockR_eq ((Data.core303.body.drop 0).take 707), wsplit_303_0.2.1]
    rw [blockB_dropE _ _ _ 707 707 1414 wsplit_303_707.1 rfl wsplit_303_707.2.2,
      ← blockR_eq ((Data.core303.body.drop 707).take 707), wsplit_303_707.2.1]
    rw [← blockR_eq (Data.core303.body.drop 1414), wsplit_303_1414]
    rfl
  exact wchkIdx_of_split (fn := Data.core303) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_304 : wchkIdx 304 = true := by
  have hb : blockB (wlookJ 304) (womLookJ 304) true [(.n 12, 1664), (.n 14, 416), (.n 16, 4), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 5), (.n 26, 371), (.n 28, 371), (.n 30, 128), (.n 160, 110), (.n 162, 20), (.n 342, 120), (.n 347, 0), (.n 348, 23), (.n 392, 64), (.n 396, 112), (.n 579, 120), (.n 584, 0), (.n 585, 6), (.n 622, 64), (.n 638, 56), (.n 821, 120), (.n 826, 0), (.n 827, 3), (.n 862, 64), (.n 878, 32), (.n 1061, 120), (.n 1066, 0), (.n 1067, 2), (.n 1104, 64), (.n 1120, 23), (.n 1201, 120), (.n 1206, 0), (.n 1207, 2), (.n 1242, 64), (.n 1258, 17), (.n 1272, 5), (.n 1469, 110), (.n 1471, 5), (.n 1818, 6), (.n 1822, 29), (.n 1828, 0), (.n 1829, 28), (.n 1836, 8), (.n 1842, 0), (.n 1843, 7), (.n 1850, 5), (.n 1856, 0), (.n 1857, 4), (.n 1864, 3), (.n 1870, 0), (.n 1871, 2), (.n 2123, 3), (.n 2129, 0), (.n 2130, 2)] Data.core304.params Data.core304.name ([], []) Data.core304.body = some (⟨224832, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core304.body)]
    rw [blockB_dropE _ _ _ 0 608 608 wsplit_304_0.1 rfl wsplit_304_0.2.2,
      ← blockR_eq ((Data.core304.body.drop 0).take 608), wsplit_304_0.2.1]
    rw [blockB_dropE _ _ _ 608 608 1216 wsplit_304_608.1 rfl wsplit_304_608.2.2,
      ← blockR_eq ((Data.core304.body.drop 608).take 608), wsplit_304_608.2.1]
    rw [blockB_dropE _ _ _ 1216 608 1824 wsplit_304_1216.1 rfl wsplit_304_1216.2.2,
      ← blockR_eq ((Data.core304.body.drop 1216).take 608), wsplit_304_1216.2.1]
    rw [blockB_dropE _ _ _ 1824 608 2432 wsplit_304_1824.1 rfl wsplit_304_1824.2.2,
      ← blockR_eq ((Data.core304.body.drop 1824).take 608), wsplit_304_1824.2.1]
    rw [← blockR_eq (Data.core304.body.drop 2432), wsplit_304_2432]
    rfl
  exact wchkIdx_of_split (fn := Data.core304) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_305 : wchkIdx 305 = true := by
  have hb : blockB (wlookJ 305) (womLookJ 305) true [(.n 12, 1664), (.n 14, 416), (.n 16, 8), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 5), (.n 26, 382), (.n 28, 382), (.n 30, 128), (.n 160, 110), (.n 162, 20), (.n 342, 130), (.n 347, 0), (.n 348, 25), (.n 392, 64), (.n 396, 112), (.n 579, 130), (.n 584, 0), (.n 585, 6), (.n 622, 64), (.n 638, 56), (.n 821, 130), (.n 826, 0), (.n 827, 4), (.n 862, 64), (.n 878, 32), (.n 1061, 130), (.n 1066, 0), (.n 1067, 3), (.n 1104, 64), (.n 1120, 23), (.n 1201, 130), (.n 1206, 0), (.n 1207, 2), (.n 1242, 64), (.n 1258, 17), (.n 1272, 5), (.n 1481, 110), (.n 1483, 5), (.n 1865, 6), (.n 1869, 29), (.n 1875, 0), (.n 1876, 28), (.n 1883, 8), (.n 1889, 0), (.n 1890, 7), (.n 1897, 5), (.n 1903, 0), (.n 1904, 4), (.n 1911, 3), (.n 1917, 0), (.n 1918, 2), (.n 2212, 3), (.n 2218, 0), (.n 2219, 2)] Data.core305.params Data.core305.name ([], []) Data.core305.body = some (⟨230102, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core305.body)]
    rw [blockB_dropE _ _ _ 0 608 608 wsplit_305_0.1 rfl wsplit_305_0.2.2,
      ← blockR_eq ((Data.core305.body.drop 0).take 608), wsplit_305_0.2.1]
    rw [blockB_dropE _ _ _ 608 608 1216 wsplit_305_608.1 rfl wsplit_305_608.2.2,
      ← blockR_eq ((Data.core305.body.drop 608).take 608), wsplit_305_608.2.1]
    rw [blockB_dropE _ _ _ 1216 608 1824 wsplit_305_1216.1 rfl wsplit_305_1216.2.2,
      ← blockR_eq ((Data.core305.body.drop 1216).take 608), wsplit_305_1216.2.1]
    rw [blockB_dropE _ _ _ 1824 608 2432 wsplit_305_1824.1 rfl wsplit_305_1824.2.2,
      ← blockR_eq ((Data.core305.body.drop 1824).take 608), wsplit_305_1824.2.1]
    rw [← blockR_eq (Data.core305.body.drop 2432), wsplit_305_2432]
    rfl
  exact wchkIdx_of_split (fn := Data.core305) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_306 : wchkIdx 306 = true := by
  have hb : blockB (wlookJ 306) (womLookJ 306) true [(.n 12, 1664), (.n 14, 416), (.n 16, 16), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 5), (.n 26, 380), (.n 28, 380), (.n 30, 128), (.n 160, 110), (.n 162, 20), (.n 342, 130), (.n 347, 0), (.n 348, 25), (.n 392, 64), (.n 396, 112), (.n 579, 130), (.n 584, 0), (.n 585, 7), (.n 622, 64), (.n 638, 56), (.n 821, 130), (.n 826, 0), (.n 827, 4), (.n 862, 64), (.n 878, 32), (.n 1061, 130), (.n 1066, 0), (.n 1067, 3), (.n 1104, 64), (.n 1120, 23), (.n 1201, 130), (.n 1206, 0), (.n 1207, 2), (.n 1242, 64), (.n 1258, 18), (.n 1272, 5), (.n 1493, 110), (.n 1495, 5), (.n 1912, 6), (.n 1916, 29), (.n 1922, 0), (.n 1923, 28), (.n 1930, 8), (.n 1936, 0), (.n 1937, 7), (.n 1944, 5), (.n 1950, 0), (.n 1951, 4), (.n 1958, 3), (.n 1964, 0), (.n 1965, 2), (.n 2301, 3), (.n 2307, 0), (.n 2308, 2)] Data.core306.params Data.core306.name ([], []) Data.core306.body = some (⟨236439, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core306.body)]
    rw [blockB_dropE _ _ _ 0 608 608 wsplit_306_0.1 rfl wsplit_306_0.2.2,
      ← blockR_eq ((Data.core306.body.drop 0).take 608), wsplit_306_0.2.1]
    rw [blockB_dropE _ _ _ 608 608 1216 wsplit_306_608.1 rfl wsplit_306_608.2.2,
      ← blockR_eq ((Data.core306.body.drop 608).take 608), wsplit_306_608.2.1]
    rw [blockB_dropE _ _ _ 1216 608 1824 wsplit_306_1216.1 rfl wsplit_306_1216.2.2,
      ← blockR_eq ((Data.core306.body.drop 1216).take 608), wsplit_306_1216.2.1]
    rw [blockB_dropE _ _ _ 1824 608 2432 wsplit_306_1824.1 rfl wsplit_306_1824.2.2,
      ← blockR_eq ((Data.core306.body.drop 1824).take 608), wsplit_306_1824.2.1]
    rw [← blockR_eq (Data.core306.body.drop 2432), wsplit_306_2432]
    rfl
  exact wchkIdx_of_split (fn := Data.core306) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_307 : wchkIdx 307 = true := by
  have hb : blockB (wlookJ 307) (womLookJ 307) true [(.n 12, 1664), (.n 14, 416), (.n 16, 32), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 5), (.n 26, 381), (.n 28, 381), (.n 30, 128), (.n 160, 110), (.n 162, 20), (.n 342, 150), (.n 347, 0), (.n 348, 29), (.n 393, 64), (.n 397, 112), (.n 580, 150), (.n 585, 0), (.n 586, 7), (.n 623, 64), (.n 639, 56), (.n 822, 150), (.n 827, 0), (.n 828, 4), (.n 863, 64), (.n 879, 32), (.n 1062, 150), (.n 1067, 0), (.n 1068, 3), (.n 1105, 64), (.n 1121, 23), (.n 1202, 150), (.n 1207, 0), (.n 1208, 2), (.n 1243, 64), (.n 1259, 18), (.n 1273, 5), (.n 1506, 110), (.n 1508, 5), (.n 1960, 6), (.n 1964, 29), (.n 1970, 0), (.n 1971, 28), (.n 2103, 8), (.n 2109, 0), (.n 2110, 7), (.n 2117, 5), (.n 2123, 0), (.n 2124, 4), (.n 2131, 3), (.n 2137, 0), (.n 2138, 2), (.n 2516, 3), (.n 2522, 0), (.n 2523, 2)] Data.core307.params Data.core307.name ([], []) Data.core307.body = some (⟨241537, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core307.body)]
    rw [blockB_dropE _ _ _ 0 608 608 wsplit_307_0.1 rfl wsplit_307_0.2.2,
      ← blockR_eq ((Data.core307.body.drop 0).take 608), wsplit_307_0.2.1]
    rw [blockB_dropE _ _ _ 608 608 1216 wsplit_307_608.1 rfl wsplit_307_608.2.2,
      ← blockR_eq ((Data.core307.body.drop 608).take 608), wsplit_307_608.2.1]
    rw [blockB_dropE _ _ _ 1216 608 1824 wsplit_307_1216.1 rfl wsplit_307_1216.2.2,
      ← blockR_eq ((Data.core307.body.drop 1216).take 608), wsplit_307_1216.2.1]
    rw [blockB_dropE _ _ _ 1824 608 2432 wsplit_307_1824.1 rfl wsplit_307_1824.2.2,
      ← blockR_eq ((Data.core307.body.drop 1824).take 608), wsplit_307_1824.2.1]
    rw [← blockR_eq (Data.core307.body.drop 2432), wsplit_307_2432]
    rfl
  exact wchkIdx_of_split (fn := Data.core307) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_308 : wchkIdx 308 = true := by
  have hb : blockB (wlookJ 308) (womLookJ 308) true [(.n 12, 1728), (.n 14, 432), (.n 16, 4), (.n 18, 12), (.n 20, 26), (.n 22, 6), (.n 24, 6), (.n 26, 391), (.n 28, 391), (.n 30, 128), (.n 160, 132), (.n 162, 24), (.n 342, 150), (.n 347, 0), (.n 348, 29), (.n 393, 64), (.n 397, 112), (.n 580, 150), (.n 585, 0), (.n 586, 7), (.n 623, 64), (.n 639, 56), (.n 822, 150), (.n 827, 0), (.n 828, 4), (.n 863, 64), (.n 879, 32), (.n 1062, 150), (.n 1067, 0), (.n 1068, 3), (.n 1105, 64), (.n 1121, 23), (.n 1304, 150), (.n 1309, 0), (.n 1310, 2), (.n 1345, 64), (.n 1361, 18), (.n 1442, 150), (.n 1447, 0), (.n 1448, 2), (.n 1483, 64), (.n 1499, 14), (.n 1513, 5), (.n 1718, 132), (.n 1720, 6), (.n 2220, 7), (.n 2224, 29), (.n 2230, 0), (.n 2231, 28), (.n 2369, 8), (.n 2375, 0), (.n 2376, 7), (.n 2383, 5), (.n 2389, 0), (.n 2390, 4), (.n 2397, 3), (.n 2403, 0), (.n 2404, 2), (.n 2824, 3), (.n 2830, 0), (.n 2831, 2), (.n 2908, 2), (.n 2914, 0), (.n 2915, 1)] Data.core308.params Data.core308.name ([], []) Data.core308.body = some (⟨251940, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core308.body)]
    rw [blockB_dropE _ _ _ 0 534 534 wsplit_308_0.1 rfl wsplit_308_0.2.2,
      ← blockR_eq ((Data.core308.body.drop 0).take 534), wsplit_308_0.2.1]
    rw [blockB_dropE _ _ _ 534 534 1068 wsplit_308_534.1 rfl wsplit_308_534.2.2,
      ← blockR_eq ((Data.core308.body.drop 534).take 534), wsplit_308_534.2.1]
    rw [blockB_dropE _ _ _ 1068 534 1602 wsplit_308_1068.1 rfl wsplit_308_1068.2.2,
      ← blockR_eq ((Data.core308.body.drop 1068).take 534), wsplit_308_1068.2.1]
    rw [blockB_dropE _ _ _ 1602 534 2136 wsplit_308_1602.1 rfl wsplit_308_1602.2.2,
      ← blockR_eq ((Data.core308.body.drop 1602).take 534), wsplit_308_1602.2.1]
    rw [blockB_dropE _ _ _ 2136 534 2670 wsplit_308_2136.1 rfl wsplit_308_2136.2.2,
      ← blockR_eq ((Data.core308.body.drop 2136).take 534), wsplit_308_2136.2.1]
    rw [blockB_dropE _ _ _ 2670 534 3204 wsplit_308_2670.1 rfl wsplit_308_2670.2.2,
      ← blockR_eq ((Data.core308.body.drop 2670).take 534), wsplit_308_2670.2.1]
    rw [← blockR_eq (Data.core308.body.drop 3204), wsplit_308_3204]
    rfl
  exact wchkIdx_of_split (fn := Data.core308) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_309 : wchkIdx 309 = true := by
  have hb : blockB (wlookJ 309) (womLookJ 309) true [(.n 12, 1024), (.n 14, 256), (.n 16, 16), (.n 18, 8), (.n 20, 18), (.n 22, 4), (.n 24, 4), (.n 26, 235), (.n 28, 235), (.n 30, 128), (.n 160, 88), (.n 162, 16), (.n 342, 65), (.n 347, 0), (.n 348, 12), (.n 391, 64), (.n 395, 56), (.n 578, 65), (.n 583, 0), (.n 584, 5), (.n 622, 64), (.n 638, 45), (.n 821, 65), (.n 826, 0), (.n 827, 3), (.n 863, 64), (.n 879, 28), (.n 960, 65), (.n 965, 0), (.n 966, 2), (.n 1002, 64), (.n 1018, 21), (.n 1032, 5), (.n 1245, 88), (.n 1247, 4), (.n 1525, 5), (.n 1529, 15), (.n 1535, 0), (.n 1536, 14), (.n 1543, 6), (.n 1549, 0), (.n 1550, 5), (.n 1912, 4), (.n 1918, 0), (.n 1919, 3), (.n 2114, 3), (.n 2120, 0), (.n 2121, 2)] Data.core309.params Data.core309.name ([], []) Data.core309.body = some (⟨131923, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core309.body)]
    rw [blockB_dropE _ _ _ 0 707 707 wsplit_309_0.1 rfl wsplit_309_0.2.2,
      ← blockR_eq ((Data.core309.body.drop 0).take 707), wsplit_309_0.2.1]
    rw [blockB_dropE _ _ _ 707 707 1414 wsplit_309_707.1 rfl wsplit_309_707.2.2,
      ← blockR_eq ((Data.core309.body.drop 707).take 707), wsplit_309_707.2.1]
    rw [blockB_dropE _ _ _ 1414 707 2121 wsplit_309_1414.1 rfl wsplit_309_1414.2.2,
      ← blockR_eq ((Data.core309.body.drop 1414).take 707), wsplit_309_1414.2.1]
    rw [← blockR_eq (Data.core309.body.drop 2121), wsplit_309_2121]
    rfl
  exact wchkIdx_of_split (fn := Data.core309) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_310 : wchkIdx 310 = true := by
  have hb : blockB (wlookJ 310) (womLookJ 310) true [(.n 12, 1024), (.n 14, 256), (.n 16, 32), (.n 18, 8), (.n 20, 18), (.n 22, 4), (.n 24, 4), (.n 26, 227), (.n 28, 227), (.n 30, 128), (.n 160, 88), (.n 162, 16), (.n 342, 65), (.n 347, 0), (.n 348, 12), (.n 391, 64), (.n 395, 56), (.n 578, 65), (.n 583, 0), (.n 584, 5), (.n 622, 64), (.n 638, 45), (.n 821, 65), (.n 826, 0), (.n 827, 3), (.n 863, 64), (.n 879, 28), (.n 960, 65), (.n 965, 0), (.n 966, 2), (.n 1002, 64), (.n 1018, 21), (.n 1032, 5), (.n 1257, 88), (.n 1259, 4), (.n 1565, 5), (.n 1569, 15), (.n 1575, 0), (.n 1576, 14), (.n 1583, 6), (.n 1589, 0), (.n 1590, 5), (.n 1982, 4), (.n 1988, 0), (.n 1989, 3), (.n 2208, 3), (.n 2214, 0), (.n 2215, 2)] Data.core310.params Data.core310.name ([], []) Data.core310.body = some (⟨133456, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core310.body)]
    rw [blockB_dropE _ _ _ 0 707 707 wsplit_310_0.1 rfl wsplit_310_0.2.2,
      ← blockR_eq ((Data.core310.body.drop 0).take 707), wsplit_310_0.2.1]
    rw [blockB_dropE _ _ _ 707 707 1414 wsplit_310_707.1 rfl wsplit_310_707.2.2,
      ← blockR_eq ((Data.core310.body.drop 707).take 707), wsplit_310_707.2.1]
    rw [blockB_dropE _ _ _ 1414 707 2121 wsplit_310_1414.1 rfl wsplit_310_1414.2.2,
      ← blockR_eq ((Data.core310.body.drop 1414).take 707), wsplit_310_1414.2.1]
    rw [← blockR_eq (Data.core310.body.drop 2121), wsplit_310_2121]
    rfl
  exact wchkIdx_of_split (fn := Data.core310) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_311 : wchkIdx 311 = true := by
  have hb : blockB (wlookJ 311) (womLookJ 311) true [(.n 12, 1088), (.n 14, 272), (.n 16, 4), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 5), (.n 26, 243), (.n 28, 243), (.n 30, 128), (.n 160, 110), (.n 162, 20), (.n 342, 70), (.n 347, 0), (.n 348, 13), (.n 391, 64), (.n 395, 56), (.n 578, 70), (.n 583, 0), (.n 584, 5), (.n 622, 64), (.n 638, 45), (.n 821, 70), (.n 826, 0), (.n 827, 3), (.n 863, 64), (.n 879, 28), (.n 1062, 70), (.n 1067, 0), (.n 1068, 2), (.n 1104, 64), (.n 1120, 21), (.n 1201, 70), (.n 1206, 0), (.n 1207, 2), (.n 1241, 64), (.n 1257, 16), (.n 1271, 5), (.n 1468, 110), (.n 1470, 5), (.n 1817, 6), (.n 1821, 15), (.n 1827, 0), (.n 1828, 14), (.n 1835, 6), (.n 1841, 0), (.n 1842, 5), (.n 2264, 4), (.n 2270, 0), (.n 2271, 3), (.n 2514, 3), (.n 2520, 0), (.n 2521, 2), (.n 2703, 3), (.n 2709, 0), (.n 2710, 2)] Data.core311.params Data.core311.name ([], []) Data.core311.body = some (⟨146617, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core311.body)]
    rw [blockB_dropE _ _ _ 0 608 608 wsplit_311_0.1 rfl wsplit_311_0.2.2,
      ← blockR_eq ((Data.core311.body.drop 0).take 608), wsplit_311_0.2.1]
    rw [blockB_dropE _ _ _ 608 608 1216 wsplit_311_608.1 rfl wsplit_311_608.2.2,
      ← blockR_eq ((Data.core311.body.drop 608).take 608), wsplit_311_608.2.1]
    rw [blockB_dropE _ _ _ 1216 608 1824 wsplit_311_1216.1 rfl wsplit_311_1216.2.2,
      ← blockR_eq ((Data.core311.body.drop 1216).take 608), wsplit_311_1216.2.1]
    rw [blockB_dropE _ _ _ 1824 608 2432 wsplit_311_1824.1 rfl wsplit_311_1824.2.2,
      ← blockR_eq ((Data.core311.body.drop 1824).take 608), wsplit_311_1824.2.1]
    rw [← blockR_eq (Data.core311.body.drop 2432), wsplit_311_2432]
    rfl
  exact wchkIdx_of_split (fn := Data.core311) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_312 : wchkIdx 312 = true := by
  have hb : blockB (wlookJ 312) (womLookJ 312) true [(.n 12, 1088), (.n 14, 272), (.n 16, 8), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 5), (.n 26, 244), (.n 28, 244), (.n 30, 128), (.n 160, 110), (.n 162, 20), (.n 342, 70), (.n 347, 0), (.n 348, 13), (.n 391, 64), (.n 395, 56), (.n 578, 70), (.n 583, 0), (.n 584, 5), (.n 622, 64), (.n 638, 45), (.n 821, 70), (.n 826, 0), (.n 827, 3), (.n 863, 64), (.n 879, 28), (.n 1062, 70), (.n 1067, 0), (.n 1068, 3), (.n 1104, 64), (.n 1120, 21), (.n 1201, 70), (.n 1206, 0), (.n 1207, 2), (.n 1241, 64), (.n 1257, 16), (.n 1271, 5), (.n 1480, 110), (.n 1482, 5), (.n 1864, 6), (.n 1868, 15), (.n 1874, 0), (.n 1875, 14), (.n 1882, 6), (.n 1888, 0), (.n 1889, 5), (.n 2341, 4), (.n 2347, 0), (.n 2348, 3), (.n 2615, 3), (.n 2621, 0), (.n 2622, 2), (.n 2834, 3), (.n 2840, 0), (.n 2841, 2)] Data.core312.params Data.core312.name ([], []) Data.core312.body = some (⟨149282, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core312.body)]
    rw [blockB_dropE _ _ _ 0 608 608 wsplit_312_0.1 rfl wsplit_312_0.2.2,
      ← blockR_eq ((Data.core312.body.drop 0).take 608), wsplit_312_0.2.1]
    rw [blockB_dropE _ _ _ 608 608 1216 wsplit_312_608.1 rfl wsplit_312_608.2.2,
      ← blockR_eq ((Data.core312.body.drop 608).take 608), wsplit_312_608.2.1]
    rw [blockB_dropE _ _ _ 1216 608 1824 wsplit_312_1216.1 rfl wsplit_312_1216.2.2,
      ← blockR_eq ((Data.core312.body.drop 1216).take 608), wsplit_312_1216.2.1]
    rw [blockB_dropE _ _ _ 1824 608 2432 wsplit_312_1824.1 rfl wsplit_312_1824.2.2,
      ← blockR_eq ((Data.core312.body.drop 1824).take 608), wsplit_312_1824.2.1]
    rw [blockB_dropE _ _ _ 2432 608 3040 wsplit_312_2432.1 rfl wsplit_312_2432.2.2,
      ← blockR_eq ((Data.core312.body.drop 2432).take 608), wsplit_312_2432.2.1]
    rw [← blockR_eq (Data.core312.body.drop 3040), wsplit_312_3040]
    rfl
  exact wchkIdx_of_split (fn := Data.core312) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_313 : wchkIdx 313 = true := by
  have hb : blockB (wlookJ 313) (womLookJ 313) true [(.n 12, 1088), (.n 14, 272), (.n 16, 16), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 5), (.n 26, 243), (.n 28, 243), (.n 30, 128), (.n 160, 110), (.n 162, 20), (.n 342, 75), (.n 347, 0), (.n 348, 14), (.n 391, 64), (.n 395, 56), (.n 578, 75), (.n 583, 0), (.n 584, 5), (.n 622, 64), (.n 638, 45), (.n 821, 75), (.n 826, 0), (.n 827, 4), (.n 863, 64), (.n 879, 28), (.n 1062, 75), (.n 1067, 0), (.n 1068, 3), (.n 1104, 64), (.n 1120, 21), (.n 1201, 75), (.n 1206, 0), (.n 1207, 2), (.n 1241, 64), (.n 1257, 16), (.n 1271, 5), (.n 1492, 110), (.n 1494, 5), (.n 1911, 6), (.n 1915, 15), (.n 1921, 0), (.n 1922, 14), (.n 1929, 6), (.n 1935, 0), (.n 1936, 5), (.n 2418, 4), (.n 2424, 0), (.n 2425, 3), (.n 2716, 3), (.n 2722, 0), (.n 2723, 2), (.n 2965, 3), (.n 2971, 0), (.n 2972, 2)] Data.core313.params Data.core313.name ([], []) Data.core313.body = some (⟨151833, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core313.body)]
    rw [blockB_dropE _ _ _ 0 608 608 wsplit_313_0.1 rfl wsplit_313_0.2.2,
      ← blockR_eq ((Data.core313.body.drop 0).take 608), wsplit_313_0.2.1]
    rw [blockB_dropE _ _ _ 608 608 1216 wsplit_313_608.1 rfl wsplit_313_608.2.2,
      ← blockR_eq ((Data.core313.body.drop 608).take 608), wsplit_313_608.2.1]
    rw [blockB_dropE _ _ _ 1216 608 1824 wsplit_313_1216.1 rfl wsplit_313_1216.2.2,
      ← blockR_eq ((Data.core313.body.drop 1216).take 608), wsplit_313_1216.2.1]
    rw [blockB_dropE _ _ _ 1824 608 2432 wsplit_313_1824.1 rfl wsplit_313_1824.2.2,
      ← blockR_eq ((Data.core313.body.drop 1824).take 608), wsplit_313_1824.2.1]
    rw [blockB_dropE _ _ _ 2432 608 3040 wsplit_313_2432.1 rfl wsplit_313_2432.2.2,
      ← blockR_eq ((Data.core313.body.drop 2432).take 608), wsplit_313_2432.2.1]
    rw [← blockR_eq (Data.core313.body.drop 3040), wsplit_313_3040]
    rfl
  exact wchkIdx_of_split (fn := Data.core313) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_314 : wchkIdx 314 = true := by
  have hb : blockB (wlookJ 314) (womLookJ 314) true [(.n 12, 1088), (.n 14, 272), (.n 16, 32), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 5), (.n 26, 243), (.n 28, 243), (.n 30, 128), (.n 160, 110), (.n 162, 20), (.n 342, 75), (.n 347, 0), (.n 348, 14), (.n 391, 64), (.n 395, 56), (.n 578, 75), (.n 583, 0), (.n 584, 6), (.n 622, 64), (.n 638, 45), (.n 821, 75), (.n 826, 0), (.n 827, 4), (.n 863, 64), (.n 879, 28), (.n 1062, 75), (.n 1067, 0), (.n 1068, 3), (.n 1104, 64), (.n 1120, 21), (.n 1201, 75), (.n 1206, 0), (.n 1207, 2), (.n 1241, 64), (.n 1257, 16), (.n 1271, 5), (.n 1504, 110), (.n 1506, 5), (.n 1958, 6), (.n 1962, 15), (.n 1968, 0), (.n 1969, 14), (.n 1976, 6), (.n 1982, 0), (.n 1983, 5), (.n 2495, 4), (.n 2501, 0), (.n 2502, 3), (.n 2817, 3), (.n 2823, 0), (.n 2824, 2), (.n 3096, 3), (.n 3102, 0), (.n 3103, 2)] Data.core314.params Data.core314.name ([], []) Data.core314.body = some (⟨154121, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core314.body)]
    rw [blockB_dropE _ _ _ 0 608 608 wsplit_314_0.1 rfl wsplit_314_0.2.2,
      ← blockR_eq ((Data.core314.body.drop 0).take 608), wsplit_314_0.2.1]
    rw [blockB_dropE _ _ _ 608 608 1216 wsplit_314_608.1 rfl wsplit_314_608.2.2,
      ← blockR_eq ((Data.core314.body.drop 608).take 608), wsplit_314_608.2.1]
    rw [blockB_dropE _ _ _ 1216 608 1824 wsplit_314_1216.1 rfl wsplit_314_1216.2.2,
      ← blockR_eq ((Data.core314.body.drop 1216).take 608), wsplit_314_1216.2.1]
    rw [blockB_dropE _ _ _ 1824 608 2432 wsplit_314_1824.1 rfl wsplit_314_1824.2.2,
      ← blockR_eq ((Data.core314.body.drop 1824).take 608), wsplit_314_1824.2.1]
    rw [blockB_dropE _ _ _ 2432 608 3040 wsplit_314_2432.1 rfl wsplit_314_2432.2.2,
      ← blockR_eq ((Data.core314.body.drop 2432).take 608), wsplit_314_2432.2.1]
    rw [← blockR_eq (Data.core314.body.drop 3040), wsplit_314_3040]
    rfl
  exact wchkIdx_of_split (fn := Data.core314) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_315 : wchkIdx 315 = true := by
  have hb : blockB (wlookJ 315) (womLookJ 315) true [(.n 12, 1152), (.n 14, 288), (.n 16, 4), (.n 18, 12), (.n 20, 26), (.n 22, 6), (.n 24, 6), (.n 26, 257), (.n 28, 257), (.n 30, 128), (.n 160, 132), (.n 162, 24), (.n 342, 75), (.n 347, 0), (.n 348, 14), (.n 391, 64), (.n 395, 56), (.n 578, 75), (.n 583, 0), (.n 584, 6), (.n 622, 64), (.n 638, 45), (.n 821, 75), (.n 826, 0), (.n 827, 4), (.n 863, 64), (.n 879, 28), (.n 1062, 75), (.n 1067, 0), (.n 1068, 3), (.n 1104, 64), (.n 1120, 21), (.n 1303, 75), (.n 1308, 0), (.n 1309, 2), (.n 1343, 64), (.n 1359, 16), (.n 1440, 75), (.n 1445, 0), (.n 1446, 2), (.n 1481, 64), (.n 1497, 13), (.n 1511, 5), (.n 1716, 132), (.n 1718, 6), (.n 2218, 7), (.n 2222, 15), (.n 2228, 0), (.n 2229, 14), (.n 2236, 6), (.n 2242, 0), (.n 2243, 5), (.n 2785, 4), (.n 2791, 0), (.n 2792, 3), (.n 3131, 3), (.n 3137, 0), (.n 3138, 2), (.n 3440, 3), (.n 3446, 0), (.n 3447, 2), (.n 3454, 2), (.n 3460, 0), (.n 3461, 1)] Data.core315.params Data.core315.name ([], []) Data.core315.body = some (⟨163376, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core315.body)]
    rw [blockB_dropE _ _ _ 0 534 534 wsplit_315_0.1 rfl wsplit_315_0.2.2,
      ← blockR_eq ((Data.core315.body.drop 0).take 534), wsplit_315_0.2.1]
    rw [blockB_dropE _ _ _ 534 534 1068 wsplit_315_534.1 rfl wsplit_315_534.2.2,
      ← blockR_eq ((Data.core315.body.drop 534).take 534), wsplit_315_534.2.1]
    rw [blockB_dropE _ _ _ 1068 534 1602 wsplit_315_1068.1 rfl wsplit_315_1068.2.2,
      ← blockR_eq ((Data.core315.body.drop 1068).take 534), wsplit_315_1068.2.1]
    rw [blockB_dropE _ _ _ 1602 534 2136 wsplit_315_1602.1 rfl wsplit_315_1602.2.2,
      ← blockR_eq ((Data.core315.body.drop 1602).take 534), wsplit_315_1602.2.1]
    rw [blockB_dropE _ _ _ 2136 534 2670 wsplit_315_2136.1 rfl wsplit_315_2136.2.2,
      ← blockR_eq ((Data.core315.body.drop 2136).take 534), wsplit_315_2136.2.1]
    rw [blockB_dropE _ _ _ 2670 534 3204 wsplit_315_2670.1 rfl wsplit_315_2670.2.2,
      ← blockR_eq ((Data.core315.body.drop 2670).take 534), wsplit_315_2670.2.1]
    rw [blockB_dropE _ _ _ 3204 534 3738 wsplit_315_3204.1 rfl wsplit_315_3204.2.2,
      ← blockR_eq ((Data.core315.body.drop 3204).take 534), wsplit_315_3204.2.1]
    rw [← blockR_eq (Data.core315.body.drop 3738), wsplit_315_3738]
    rfl
  exact wchkIdx_of_split (fn := Data.core315) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_316 : wchkIdx 316 = true := by
  have hb : blockB (wlookJ 316) (womLookJ 316) true [(.n 12, 1024), (.n 14, 256), (.n 16, 16), (.n 18, 8), (.n 20, 18), (.n 22, 4), (.n 24, 4), (.n 26, 177), (.n 28, 177), (.n 30, 128), (.n 160, 88), (.n 162, 16), (.n 342, 45), (.n 347, 0), (.n 348, 8), (.n 392, 64), (.n 396, 37), (.n 579, 45), (.n 584, 0), (.n 585, 4), (.n 622, 64), (.n 638, 38), (.n 821, 45), (.n 826, 0), (.n 827, 3), (.n 863, 64), (.n 879, 25), (.n 960, 45), (.n 965, 0), (.n 966, 2), (.n 1002, 64), (.n 1018, 19), (.n 1032, 5), (.n 1245, 88), (.n 1247, 4), (.n 1525, 5), (.n 1529, 10), (.n 1535, 0), (.n 1536, 9), (.n 1828, 5), (.n 1834, 0), (.n 1835, 4), (.n 2268, 4), (.n 2274, 0), (.n 2275, 3), (.n 2329, 3), (.n 2335, 0), (.n 2336, 2)] Data.core316.params Data.core316.name ([], []) Data.core316.body = some (⟨102684, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core316.body)]
    rw [blockB_dropE _ _ _ 0 707 707 wsplit_316_0.1 rfl wsplit_316_0.2.2,
      ← blockR_eq ((Data.core316.body.drop 0).take 707), wsplit_316_0.2.1]
    rw [blockB_dropE _ _ _ 707 707 1414 wsplit_316_707.1 rfl wsplit_316_707.2.2,
      ← blockR_eq ((Data.core316.body.drop 707).take 707), wsplit_316_707.2.1]
    rw [blockB_dropE _ _ _ 1414 707 2121 wsplit_316_1414.1 rfl wsplit_316_1414.2.2,
      ← blockR_eq ((Data.core316.body.drop 1414).take 707), wsplit_316_1414.2.1]
    rw [← blockR_eq (Data.core316.body.drop 2121), wsplit_316_2121]
    rfl
  exact wchkIdx_of_split (fn := Data.core316) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_317 : wchkIdx 317 = true := by
  have hb : blockB (wlookJ 317) (womLookJ 317) true [(.n 12, 1024), (.n 14, 256), (.n 16, 32), (.n 18, 8), (.n 20, 18), (.n 22, 4), (.n 24, 4), (.n 26, 173), (.n 28, 173), (.n 30, 128), (.n 160, 88), (.n 162, 16), (.n 342, 50), (.n 347, 0), (.n 348, 9), (.n 392, 64), (.n 396, 37), (.n 579, 50), (.n 584, 0), (.n 585, 4), (.n 622, 64), (.n 638, 38), (.n 821, 50), (.n 826, 0), (.n 827, 3), (.n 863, 64), (.n 879, 25), (.n 960, 50), (.n 965, 0), (.n 966, 2), (.n 1002, 64), (.n 1018, 19), (.n 1032, 5), (.n 1257, 88), (.n 1259, 4), (.n 1565, 5), (.n 1569, 10), (.n 1575, 0), (.n 1576, 9), (.n 1886, 5), (.n 1892, 0), (.n 1893, 4), (.n 2362, 4), (.n 2368, 0), (.n 2369, 3), (.n 2429, 3), (.n 2435, 0), (.n 2436, 2)] Data.core317.params Data.core317.name ([], []) Data.core317.body = some (⟨106344, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core317.body)]
    rw [blockB_dropE _ _ _ 0 707 707 wsplit_317_0.1 rfl wsplit_317_0.2.2,
      ← blockR_eq ((Data.core317.body.drop 0).take 707), wsplit_317_0.2.1]
    rw [blockB_dropE _ _ _ 707 707 1414 wsplit_317_707.1 rfl wsplit_317_707.2.2,
      ← blockR_eq ((Data.core317.body.drop 707).take 707), wsplit_317_707.2.1]
    rw [blockB_dropE _ _ _ 1414 707 2121 wsplit_317_1414.1 rfl wsplit_317_1414.2.2,
      ← blockR_eq ((Data.core317.body.drop 1414).take 707), wsplit_317_1414.2.1]
    rw [← blockR_eq (Data.core317.body.drop 2121), wsplit_317_2121]
    rfl
  exact wchkIdx_of_split (fn := Data.core317) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_318 : wchkIdx 318 = true := by
  have hb : blockB (wlookJ 318) (womLookJ 318) true [(.n 12, 1088), (.n 14, 272), (.n 16, 4), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 5), (.n 26, 198), (.n 28, 198), (.n 30, 128), (.n 160, 110), (.n 162, 20), (.n 342, 50), (.n 347, 0), (.n 348, 9), (.n 392, 64), (.n 396, 37), (.n 579, 50), (.n 584, 0), (.n 585, 5), (.n 622, 64), (.n 638, 38), (.n 821, 50), (.n 826, 0), (.n 827, 3), (.n 863, 64), (.n 879, 25), (.n 1062, 50), (.n 1067, 0), (.n 1068, 2), (.n 1104, 64), (.n 1120, 19), (.n 1201, 50), (.n 1206, 0), (.n 1207, 2), (.n 1243, 64), (.n 1259, 15), (.n 1273, 5), (.n 1470, 110), (.n 1472, 5), (.n 1819, 6), (.n 1823, 10), (.n 1829, 0), (.n 1830, 9), (.n 2158, 5), (.n 2164, 0), (.n 2165, 4), (.n 2670, 4), (.n 2676, 0), (.n 2677, 3), (.n 2743, 3), (.n 2749, 0), (.n 2750, 2), (.n 2862, 2), (.n 2868, 0), (.n 2869, 1)] Data.core318.params Data.core318.name ([], []) Data.core318.body = some (⟨116943, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core318.body)]
    rw [blockB_dropE _ _ _ 0 608 608 wsplit_318_0.1 rfl wsplit_318_0.2.2,
      ← blockR_eq ((Data.core318.body.drop 0).take 608), wsplit_318_0.2.1]
    rw [blockB_dropE _ _ _ 608 608 1216 wsplit_318_608.1 rfl wsplit_318_608.2.2,
      ← blockR_eq ((Data.core318.body.drop 608).take 608), wsplit_318_608.2.1]
    rw [blockB_dropE _ _ _ 1216 608 1824 wsplit_318_1216.1 rfl wsplit_318_1216.2.2,
      ← blockR_eq ((Data.core318.body.drop 1216).take 608), wsplit_318_1216.2.1]
    rw [blockB_dropE _ _ _ 1824 608 2432 wsplit_318_1824.1 rfl wsplit_318_1824.2.2,
      ← blockR_eq ((Data.core318.body.drop 1824).take 608), wsplit_318_1824.2.1]
    rw [blockB_dropE _ _ _ 2432 608 3040 wsplit_318_2432.1 rfl wsplit_318_2432.2.2,
      ← blockR_eq ((Data.core318.body.drop 2432).take 608), wsplit_318_2432.2.1]
    rw [← blockR_eq (Data.core318.body.drop 3040), wsplit_318_3040]
    rfl
  exact wchkIdx_of_split (fn := Data.core318) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_319 : wchkIdx 319 = true := by
  have hb : blockB (wlookJ 319) (womLookJ 319) true [(.n 12, 1088), (.n 14, 272), (.n 16, 8), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 5), (.n 26, 192), (.n 28, 192), (.n 30, 128), (.n 160, 110), (.n 162, 20), (.n 342, 55), (.n 347, 0), (.n 348, 10), (.n 392, 64), (.n 396, 37), (.n 579, 55), (.n 584, 0), (.n 585, 5), (.n 622, 64), (.n 638, 38), (.n 821, 55), (.n 826, 0), (.n 827, 3), (.n 863, 64), (.n 879, 25), (.n 1062, 55), (.n 1067, 0), (.n 1068, 2), (.n 1104, 64), (.n 1120, 19), (.n 1201, 55), (.n 1206, 0), (.n 1207, 2), (.n 1243, 64), (.n 1259, 15), (.n 1273, 5), (.n 1482, 110), (.n 1484, 5), (.n 1866, 6), (.n 1870, 10), (.n 1876, 0), (.n 1877, 9), (.n 2223, 5), (.n 2229, 0), (.n 2230, 4), (.n 2771, 4), (.n 2777, 0), (.n 2778, 3), (.n 2850, 3), (.n 2856, 0), (.n 2857, 2), (.n 2987, 2), (.n 2993, 0), (.n 2994, 1)] Data.core319.params Data.core319.name ([], []) Data.core319.body = some (⟨118663, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core319.body)]
    rw [blockB_dropE _ _ _ 0 608 608 wsplit_319_0.1 rfl wsplit_319_0.2.2,
      ← blockR_eq ((Data.core319.body.drop 0).take 608), wsplit_319_0.2.1]
    rw [blockB_dropE _ _ _ 608 608 1216 wsplit_319_608.1 rfl wsplit_319_608.2.2,
      ← blockR_eq ((Data.core319.body.drop 608).take 608), wsplit_319_608.2.1]
    rw [blockB_dropE _ _ _ 1216 608 1824 wsplit_319_1216.1 rfl wsplit_319_1216.2.2,
      ← blockR_eq ((Data.core319.body.drop 1216).take 608), wsplit_319_1216.2.1]
    rw [blockB_dropE _ _ _ 1824 608 2432 wsplit_319_1824.1 rfl wsplit_319_1824.2.2,
      ← blockR_eq ((Data.core319.body.drop 1824).take 608), wsplit_319_1824.2.1]
    rw [blockB_dropE _ _ _ 2432 608 3040 wsplit_319_2432.1 rfl wsplit_319_2432.2.2,
      ← blockR_eq ((Data.core319.body.drop 2432).take 608), wsplit_319_2432.2.1]
    rw [← blockR_eq (Data.core319.body.drop 3040), wsplit_319_3040]
    rfl
  exact wchkIdx_of_split (fn := Data.core319) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_320 : wchkIdx 320 = true := by
  have hb : blockB (wlookJ 320) (womLookJ 320) true [(.n 12, 1088), (.n 14, 272), (.n 16, 16), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 5), (.n 26, 194), (.n 28, 194), (.n 30, 128), (.n 160, 110), (.n 162, 20), (.n 342, 55), (.n 347, 0), (.n 348, 10), (.n 392, 64), (.n 396, 37), (.n 579, 55), (.n 584, 0), (.n 585, 5), (.n 622, 64), (.n 638, 38), (.n 821, 55), (.n 826, 0), (.n 827, 3), (.n 863, 64), (.n 879, 25), (.n 1062, 55), (.n 1067, 0), (.n 1068, 3), (.n 1104, 64), (.n 1120, 19), (.n 1201, 55), (.n 1206, 0), (.n 1207, 2), (.n 1243, 64), (.n 1259, 15), (.n 1273, 5), (.n 1494, 110), (.n 1496, 5), (.n 1913, 6), (.n 1917, 10), (.n 1923, 0), (.n 1924, 9), (.n 2288, 5), (.n 2294, 0), (.n 2295, 4), (.n 2872, 4), (.n 2878, 0), (.n 2879, 3), (.n 2957, 3), (.n 2963, 0), (.n 2964, 2), (.n 3112, 2), (.n 3118, 0), (.n 3119, 1)] Data.core320.params Data.core320.name ([], []) Data.core320.body = some (⟨120576, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core320.body)]
    rw [blockB_dropE _ _ _ 0 608 608 wsplit_320_0.1 rfl wsplit_320_0.2.2,
      ← blockR_eq ((Data.core320.body.drop 0).take 608), wsplit_320_0.2.1]
    rw [blockB_dropE _ _ _ 608 608 1216 wsplit_320_608.1 rfl wsplit_320_608.2.2,
      ← blockR_eq ((Data.core320.body.drop 608).take 608), wsplit_320_608.2.1]
    rw [blockB_dropE _ _ _ 1216 608 1824 wsplit_320_1216.1 rfl wsplit_320_1216.2.2,
      ← blockR_eq ((Data.core320.body.drop 1216).take 608), wsplit_320_1216.2.1]
    rw [blockB_dropE _ _ _ 1824 608 2432 wsplit_320_1824.1 rfl wsplit_320_1824.2.2,
      ← blockR_eq ((Data.core320.body.drop 1824).take 608), wsplit_320_1824.2.1]
    rw [blockB_dropE _ _ _ 2432 608 3040 wsplit_320_2432.1 rfl wsplit_320_2432.2.2,
      ← blockR_eq ((Data.core320.body.drop 2432).take 608), wsplit_320_2432.2.1]
    rw [← blockR_eq (Data.core320.body.drop 3040), wsplit_320_3040]
    rfl
  exact wchkIdx_of_split (fn := Data.core320) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_321 : wchkIdx 321 = true := by
  have hb : blockB (wlookJ 321) (womLookJ 321) true [(.n 12, 1088), (.n 14, 272), (.n 16, 32), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 5), (.n 26, 197), (.n 28, 197), (.n 30, 128), (.n 160, 110), (.n 162, 20), (.n 342, 55), (.n 347, 0), (.n 348, 10), (.n 392, 64), (.n 396, 37), (.n 579, 55), (.n 584, 0), (.n 585, 5), (.n 622, 64), (.n 638, 38), (.n 821, 55), (.n 826, 0), (.n 827, 4), (.n 863, 64), (.n 879, 25), (.n 1062, 55), (.n 1067, 0), (.n 1068, 3), (.n 1104, 64), (.n 1120, 19), (.n 1201, 55), (.n 1206, 0), (.n 1207, 2), (.n 1243, 64), (.n 1259, 15), (.n 1273, 5), (.n 1506, 110), (.n 1508, 5), (.n 1960, 6), (.n 1964, 10), (.n 1970, 0), (.n 1971, 9), (.n 2353, 5), (.n 2359, 0), (.n 2360, 4), (.n 2973, 4), (.n 2979, 0), (.n 2980, 3), (.n 3064, 3), (.n 3070, 0), (.n 3071, 2), (.n 3237, 2), (.n 3243, 0), (.n 3244, 1)] Data.core321.params Data.core321.name ([], []) Data.core321.body = some (⟨122483, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core321.body)]
    rw [blockB_dropE _ _ _ 0 608 608 wsplit_321_0.1 rfl wsplit_321_0.2.2,
      ← blockR_eq ((Data.core321.body.drop 0).take 608), wsplit_321_0.2.1]
    rw [blockB_dropE _ _ _ 608 608 1216 wsplit_321_608.1 rfl wsplit_321_608.2.2,
      ← blockR_eq ((Data.core321.body.drop 608).take 608), wsplit_321_608.2.1]
    rw [blockB_dropE _ _ _ 1216 608 1824 wsplit_321_1216.1 rfl wsplit_321_1216.2.2,
      ← blockR_eq ((Data.core321.body.drop 1216).take 608), wsplit_321_1216.2.1]
    rw [blockB_dropE _ _ _ 1824 608 2432 wsplit_321_1824.1 rfl wsplit_321_1824.2.2,
      ← blockR_eq ((Data.core321.body.drop 1824).take 608), wsplit_321_1824.2.1]
    rw [blockB_dropE _ _ _ 2432 608 3040 wsplit_321_2432.1 rfl wsplit_321_2432.2.2,
      ← blockR_eq ((Data.core321.body.drop 2432).take 608), wsplit_321_2432.2.1]
    rw [blockB_dropE _ _ _ 3040 608 3648 wsplit_321_3040.1 rfl wsplit_321_3040.2.2,
      ← blockR_eq ((Data.core321.body.drop 3040).take 608), wsplit_321_3040.2.1]
    rw [← blockR_eq (Data.core321.body.drop 3648), wsplit_321_3648]
    rfl
  exact wchkIdx_of_split (fn := Data.core321) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_322 : wchkIdx 322 = true := by
  have hb : blockB (wlookJ 322) (womLookJ 322) true [(.n 12, 1152), (.n 14, 288), (.n 16, 4), (.n 18, 12), (.n 20, 26), (.n 22, 6), (.n 24, 6), (.n 26, 209), (.n 28, 209), (.n 30, 128), (.n 160, 132), (.n 162, 24), (.n 342, 60), (.n 347, 0), (.n 348, 11), (.n 392, 64), (.n 396, 37), (.n 579, 60), (.n 584, 0), (.n 585, 5), (.n 622, 64), (.n 638, 38), (.n 821, 60), (.n 826, 0), (.n 827, 4), (.n 863, 64), (.n 879, 25), (.n 1062, 60), (.n 1067, 0), (.n 1068, 3), (.n 1104, 64), (.n 1120, 19), (.n 1303, 60), (.n 1308, 0), (.n 1309, 2), (.n 1345, 64), (.n 1361, 15), (.n 1442, 60), (.n 1447, 0), (.n 1448, 2), (.n 1483, 64), (.n 1499, 13), (.n 1513, 5), (.n 1718, 132), (.n 1720, 6), (.n 2220, 7), (.n 2224, 10), (.n 2230, 0), (.n 2231, 9), (.n 2631, 5), (.n 2637, 0), (.n 2638, 4), (.n 3287, 4), (.n 3293, 0), (.n 3294, 3), (.n 3384, 3), (.n 3390, 0), (.n 3391, 2), (.n 3575, 2), (.n 3581, 0), (.n 3582, 1), (.n 3834, 2), (.n 3840, 0), (.n 3841, 1)] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨132027, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [blockB_dropE _ _ _ 0 534 534 wsplit_322_0.1 rfl wsplit_322_0.2.2,
      ← blockR_eq ((Data.core322.body.drop 0).take 534), wsplit_322_0.2.1]
    rw [blockB_dropE _ _ _ 534 534 1068 wsplit_322_534.1 rfl wsplit_322_534.2.2,
      ← blockR_eq ((Data.core322.body.drop 534).take 534), wsplit_322_534.2.1]
    rw [blockB_dropE _ _ _ 1068 534 1602 wsplit_322_1068.1 rfl wsplit_322_1068.2.2,
      ← blockR_eq ((Data.core322.body.drop 1068).take 534), wsplit_322_1068.2.1]
    rw [blockB_dropE _ _ _ 1602 534 2136 wsplit_322_1602.1 rfl wsplit_322_1602.2.2,
      ← blockR_eq ((Data.core322.body.drop 1602).take 534), wsplit_322_1602.2.1]
    rw [blockB_dropE _ _ _ 2136 534 2670 wsplit_322_2136.1 rfl wsplit_322_2136.2.2,
      ← blockR_eq ((Data.core322.body.drop 2136).take 534), wsplit_322_2136.2.1]
    rw [blockB_dropE _ _ _ 2670 534 3204 wsplit_322_2670.1 rfl wsplit_322_2670.2.2,
      ← blockR_eq ((Data.core322.body.drop 2670).take 534), wsplit_322_2670.2.1]
    rw [blockB_dropE _ _ _ 3204 534 3738 wsplit_322_3204.1 rfl wsplit_322_3204.2.2,
      ← blockR_eq ((Data.core322.body.drop 3204).take 534), wsplit_322_3204.2.1]
    rw [blockB_dropE _ _ _ 3738 534 4272 wsplit_322_3738.1 rfl wsplit_322_3738.2.2,
      ← blockR_eq ((Data.core322.body.drop 3738).take 534), wsplit_322_3738.2.1]
    rw [← blockR_eq (Data.core322.body.drop 4272), wsplit_322_4272]
    rfl
  exact wchkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_323 : wchkIdx 323 = true := by
  have hb : blockB (wlookJ 323) (womLookJ 323) true [(.n 12, 640), (.n 14, 160), (.n 16, 16), (.n 18, 8), (.n 20, 18), (.n 22, 4), (.n 24, 4), (.n 26, 155), (.n 28, 155), (.n 30, 128), (.n 160, 88), (.n 162, 16), (.n 342, 40), (.n 347, 0), (.n 348, 7), (.n 390, 64), (.n 394, 28), (.n 577, 40), (.n 582, 0), (.n 583, 4), (.n 618, 64), (.n 634, 32), (.n 817, 40), (.n 822, 0), (.n 823, 3), (.n 860, 64), (.n 876, 23), (.n 957, 40), (.n 962, 0), (.n 963, 2), (.n 998, 64), (.n 1014, 18), (.n 1028, 5), (.n 1241, 88), (.n 1243, 4), (.n 1521, 5), (.n 1525, 8), (.n 1531, 0), (.n 1532, 7), (.n 1539, 5), (.n 1545, 0), (.n 1546, 4), (.n 1553, 3), (.n 1559, 0), (.n 1560, 2), (.n 1896, 3), (.n 1902, 0), (.n 1903, 2)] Data.core323.params Data.core323.name ([], []) Data.core323.body = some (⟨88089, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core323.body)]
    rw [blockB_dropE _ _ _ 0 707 707 wsplit_323_0.1 rfl wsplit_323_0.2.2,
      ← blockR_eq ((Data.core323.body.drop 0).take 707), wsplit_323_0.2.1]
    rw [blockB_dropE _ _ _ 707 707 1414 wsplit_323_707.1 rfl wsplit_323_707.2.2,
      ← blockR_eq ((Data.core323.body.drop 707).take 707), wsplit_323_707.2.1]
    rw [blockB_dropE _ _ _ 1414 707 2121 wsplit_323_1414.1 rfl wsplit_323_1414.2.2,
      ← blockR_eq ((Data.core323.body.drop 1414).take 707), wsplit_323_1414.2.1]
    rw [← blockR_eq (Data.core323.body.drop 2121), wsplit_323_2121]
    rfl
  exact wchkIdx_of_split (fn := Data.core323) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_324 : wchkIdx 324 = true := by
  have hb : blockB (wlookJ 324) (womLookJ 324) true [(.n 12, 640), (.n 14, 160), (.n 16, 32), (.n 18, 8), (.n 20, 18), (.n 22, 4), (.n 24, 4), (.n 26, 149), (.n 28, 149), (.n 30, 128), (.n 160, 88), (.n 162, 16), (.n 342, 40), (.n 347, 0), (.n 348, 7), (.n 390, 64), (.n 394, 28), (.n 577, 40), (.n 582, 0), (.n 583, 4), (.n 618, 64), (.n 634, 32), (.n 817, 40), (.n 822, 0), (.n 823, 3), (.n 860, 64), (.n 876, 23), (.n 957, 40), (.n 962, 0), (.n 963, 2), (.n 998, 64), (.n 1014, 18), (.n 1028, 5), (.n 1253, 88), (.n 1255, 4), (.n 1561, 5), (.n 1565, 8), (.n 1571, 0), (.n 1572, 7), (.n 1579, 5), (.n 1585, 0), (.n 1586, 4), (.n 1593, 3), (.n 1599, 0), (.n 1600, 2), (.n 1978, 3), (.n 1984, 0), (.n 1985, 2)] Data.core324.params Data.core324.name ([], []) Data.core324.body = some (⟨89564, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core324.body)]
    rw [blockB_dropE _ _ _ 0 707 707 wsplit_324_0.1 rfl wsplit_324_0.2.2,
      ← blockR_eq ((Data.core324.body.drop 0).take 707), wsplit_324_0.2.1]
    rw [blockB_dropE _ _ _ 707 707 1414 wsplit_324_707.1 rfl wsplit_324_707.2.2,
      ← blockR_eq ((Data.core324.body.drop 707).take 707), wsplit_324_707.2.1]
    rw [blockB_dropE _ _ _ 1414 707 2121 wsplit_324_1414.1 rfl wsplit_324_1414.2.2,
      ← blockR_eq ((Data.core324.body.drop 1414).take 707), wsplit_324_1414.2.1]
    rw [← blockR_eq (Data.core324.body.drop 2121), wsplit_324_2121]
    rfl
  exact wchkIdx_of_split (fn := Data.core324) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_325 : wchkIdx 325 = true := by
  have hb : blockB (wlookJ 325) (womLookJ 325) true [(.n 12, 704), (.n 14, 176), (.n 16, 4), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 5), (.n 26, 159), (.n 28, 159), (.n 30, 128), (.n 160, 110), (.n 162, 20), (.n 342, 40), (.n 347, 0), (.n 348, 7), (.n 390, 64), (.n 394, 28), (.n 577, 40), (.n 582, 0), (.n 583, 4), (.n 618, 64), (.n 634, 32), (.n 817, 40), (.n 822, 0), (.n 823, 3), (.n 860, 64), (.n 876, 23), (.n 1059, 40), (.n 1064, 0), (.n 1065, 2), (.n 1100, 64), (.n 1116, 18), (.n 1197, 40), (.n 1202, 0), (.n 1203, 2), (.n 1238, 64), (.n 1254, 14), (.n 1268, 5), (.n 1465, 110), (.n 1467, 5), (.n 1814, 6), (.n 1818, 8), (.n 1824, 0), (.n 1825, 7), (.n 1832, 5), (.n 1838, 0), (.n 1839, 4), (.n 1846, 3), (.n 1852, 0), (.n 1853, 2), (.n 2273, 3), (.n 2279, 0), (.n 2280, 2), (.n 2357, 2), (.n 2363, 0), (.n 2364, 1)] Data.core325.params Data.core325.name ([], []) Data.core325.body = some (⟨98743, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core325.body)]
    rw [blockB_dropE _ _ _ 0 608 608 wsplit_325_0.1 rfl wsplit_325_0.2.2,
      ← blockR_eq ((Data.core325.body.drop 0).take 608), wsplit_325_0.2.1]
    rw [blockB_dropE _ _ _ 608 608 1216 wsplit_325_608.1 rfl wsplit_325_608.2.2,
      ← blockR_eq ((Data.core325.body.drop 608).take 608), wsplit_325_608.2.1]
    rw [blockB_dropE _ _ _ 1216 608 1824 wsplit_325_1216.1 rfl wsplit_325_1216.2.2,
      ← blockR_eq ((Data.core325.body.drop 1216).take 608), wsplit_325_1216.2.1]
    rw [blockB_dropE _ _ _ 1824 608 2432 wsplit_325_1824.1 rfl wsplit_325_1824.2.2,
      ← blockR_eq ((Data.core325.body.drop 1824).take 608), wsplit_325_1824.2.1]
    rw [← blockR_eq (Data.core325.body.drop 2432), wsplit_325_2432]
    rfl
  exact wchkIdx_of_split (fn := Data.core325) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_326 : wchkIdx 326 = true := by
  have hb : blockB (wlookJ 326) (womLookJ 326) true [(.n 12, 704), (.n 14, 176), (.n 16, 8), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 5), (.n 26, 153), (.n 28, 153), (.n 30, 128), (.n 160, 110), (.n 162, 20), (.n 342, 40), (.n 347, 0), (.n 348, 7), (.n 390, 64), (.n 394, 28), (.n 577, 40), (.n 582, 0), (.n 583, 4), (.n 618, 64), (.n 634, 32), (.n 817, 40), (.n 822, 0), (.n 823, 3), (.n 860, 64), (.n 876, 23), (.n 1059, 40), (.n 1064, 0), (.n 1065, 2), (.n 1100, 64), (.n 1116, 18), (.n 1197, 40), (.n 1202, 0), (.n 1203, 2), (.n 1238, 64), (.n 1254, 14), (.n 1268, 5), (.n 1477, 110), (.n 1479, 5), (.n 1861, 6), (.n 1865, 8), (.n 1871, 0), (.n 1872, 7), (.n 1879, 5), (.n 1885, 0), (.n 1886, 4), (.n 1893, 3), (.n 1899, 0), (.n 1900, 2), (.n 2362, 3), (.n 2368, 0), (.n 2369, 2), (.n 2458, 2), (.n 2464, 0), (.n 2465, 1)] Data.core326.params Data.core326.name ([], []) Data.core326.body = some (⟨99823, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core326.body)]
    rw [blockB_dropE _ _ _ 0 608 608 wsplit_326_0.1 rfl wsplit_326_0.2.2,
      ← blockR_eq ((Data.core326.body.drop 0).take 608), wsplit_326_0.2.1]
    rw [blockB_dropE _ _ _ 608 608 1216 wsplit_326_608.1 rfl wsplit_326_608.2.2,
      ← blockR_eq ((Data.core326.body.drop 608).take 608), wsplit_326_608.2.1]
    rw [blockB_dropE _ _ _ 1216 608 1824 wsplit_326_1216.1 rfl wsplit_326_1216.2.2,
      ← blockR_eq ((Data.core326.body.drop 1216).take 608), wsplit_326_1216.2.1]
    rw [blockB_dropE _ _ _ 1824 608 2432 wsplit_326_1824.1 rfl wsplit_326_1824.2.2,
      ← blockR_eq ((Data.core326.body.drop 1824).take 608), wsplit_326_1824.2.1]
    rw [← blockR_eq (Data.core326.body.drop 2432), wsplit_326_2432]
    rfl
  exact wchkIdx_of_split (fn := Data.core326) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_327 : wchkIdx 327 = true := by
  have hb : blockB (wlookJ 327) (womLookJ 327) true [(.n 12, 704), (.n 14, 176), (.n 16, 16), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 5), (.n 26, 148), (.n 28, 148), (.n 30, 128), (.n 160, 110), (.n 162, 20), (.n 342, 40), (.n 347, 0), (.n 348, 7), (.n 390, 64), (.n 394, 28), (.n 577, 40), (.n 582, 0), (.n 583, 4), (.n 618, 64), (.n 634, 32), (.n 817, 40), (.n 822, 0), (.n 823, 3), (.n 860, 64), (.n 876, 23), (.n 1059, 40), (.n 1064, 0), (.n 1065, 2), (.n 1100, 64), (.n 1116, 18), (.n 1197, 40), (.n 1202, 0), (.n 1203, 2), (.n 1238, 64), (.n 1254, 14), (.n 1268, 5), (.n 1489, 110), (.n 1491, 5), (.n 1908, 6), (.n 1912, 8), (.n 1918, 0), (.n 1919, 7), (.n 1926, 5), (.n 1932, 0), (.n 1933, 4), (.n 1940, 3), (.n 1946, 0), (.n 1947, 2), (.n 2451, 3), (.n 2457, 0), (.n 2458, 2), (.n 2559, 2), (.n 2565, 0), (.n 2566, 1)] Data.core327.params Data.core327.name ([], []) Data.core327.body = some (⟨101090, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core327.body)]
    rw [blockB_dropE _ _ _ 0 608 608 wsplit_327_0.1 rfl wsplit_327_0.2.2,
      ← blockR_eq ((Data.core327.body.drop 0).take 608), wsplit_327_0.2.1]
    rw [blockB_dropE _ _ _ 608 608 1216 wsplit_327_608.1 rfl wsplit_327_608.2.2,
      ← blockR_eq ((Data.core327.body.drop 608).take 608), wsplit_327_608.2.1]
    rw [blockB_dropE _ _ _ 1216 608 1824 wsplit_327_1216.1 rfl wsplit_327_1216.2.2,
      ← blockR_eq ((Data.core327.body.drop 1216).take 608), wsplit_327_1216.2.1]
    rw [blockB_dropE _ _ _ 1824 608 2432 wsplit_327_1824.1 rfl wsplit_327_1824.2.2,
      ← blockR_eq ((Data.core327.body.drop 1824).take 608), wsplit_327_1824.2.1]
    rw [blockB_dropE _ _ _ 2432 608 3040 wsplit_327_2432.1 rfl wsplit_327_2432.2.2,
      ← blockR_eq ((Data.core327.body.drop 2432).take 608), wsplit_327_2432.2.1]
    rw [← blockR_eq (Data.core327.body.drop 3040), wsplit_327_3040]
    rfl
  exact wchkIdx_of_split (fn := Data.core327) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_328 : wchkIdx 328 = true := by
  have hb : blockB (wlookJ 328) (womLookJ 328) true [(.n 12, 704), (.n 14, 176), (.n 16, 32), (.n 18, 10), (.n 20, 22), (.n 22, 5), (.n 24, 5), (.n 26, 154), (.n 28, 154), (.n 30, 128), (.n 160, 110), (.n 162, 20), (.n 342, 45), (.n 347, 0), (.n 348, 8), (.n 390, 64), (.n 394, 28), (.n 577, 45), (.n 582, 0), (.n 583, 4), (.n 618, 64), (.n 634, 32), (.n 817, 45), (.n 822, 0), (.n 823, 3), (.n 860, 64), (.n 876, 23), (.n 1059, 45), (.n 1064, 0), (.n 1065, 3), (.n 1100, 64), (.n 1116, 18), (.n 1197, 45), (.n 1202, 0), (.n 1203, 2), (.n 1239, 64), (.n 1255, 15), (.n 1269, 5), (.n 1502, 110), (.n 1504, 5), (.n 1956, 6), (.n 1960, 8), (.n 1966, 0), (.n 1967, 7), (.n 1974, 5), (.n 1980, 0), (.n 1981, 4), (.n 1988, 3), (.n 1994, 0), (.n 1995, 2), (.n 2541, 3), (.n 2547, 0), (.n 2548, 2), (.n 2661, 2), (.n 2667, 0), (.n 2668, 1)] Data.core328.params Data.core328.name ([], []) Data.core328.body = some (⟨105013, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core328.body)]
    rw [blockB_dropE _ _ _ 0 608 608 wsplit_328_0.1 rfl wsplit_328_0.2.2,
      ← blockR_eq ((Data.core328.body.drop 0).take 608), wsplit_328_0.2.1]
    rw [blockB_dropE _ _ _ 608 608 1216 wsplit_328_608.1 rfl wsplit_328_608.2.2,
      ← blockR_eq ((Data.core328.body.drop 608).take 608), wsplit_328_608.2.1]
    rw [blockB_dropE _ _ _ 1216 608 1824 wsplit_328_1216.1 rfl wsplit_328_1216.2.2,
      ← blockR_eq ((Data.core328.body.drop 1216).take 608), wsplit_328_1216.2.1]
    rw [blockB_dropE _ _ _ 1824 608 2432 wsplit_328_1824.1 rfl wsplit_328_1824.2.2,
      ← blockR_eq ((Data.core328.body.drop 1824).take 608), wsplit_328_1824.2.1]
    rw [blockB_dropE _ _ _ 2432 608 3040 wsplit_328_2432.1 rfl wsplit_328_2432.2.2,
      ← blockR_eq ((Data.core328.body.drop 2432).take 608), wsplit_328_2432.2.1]
    rw [← blockR_eq (Data.core328.body.drop 3040), wsplit_328_3040]
    rfl
  exact wchkIdx_of_split (fn := Data.core328) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_329 : wchkIdx 329 = true := by
  have hb : blockB (wlookJ 329) (womLookJ 329) true [(.n 12, 768), (.n 14, 192), (.n 16, 4), (.n 18, 12), (.n 20, 26), (.n 22, 6), (.n 24, 6), (.n 26, 173), (.n 28, 173), (.n 30, 128), (.n 160, 132), (.n 162, 24), (.n 342, 45), (.n 347, 0), (.n 348, 8), (.n 390, 64), (.n 394, 28), (.n 577, 45), (.n 582, 0), (.n 583, 5), (.n 618, 64), (.n 634, 32), (.n 817, 45), (.n 822, 0), (.n 823, 3), (.n 860, 64), (.n 876, 23), (.n 1059, 45), (.n 1064, 0), (.n 1065, 3), (.n 1100, 64), (.n 1116, 18), (.n 1299, 45), (.n 1304, 0), (.n 1305, 2), (.n 1341, 64), (.n 1357, 15), (.n 1438, 45), (.n 1443, 0), (.n 1444, 2), (.n 1478, 64), (.n 1494, 12), (.n 1508, 5), (.n 1713, 132), (.n 1715, 6), (.n 2215, 7), (.n 2219, 8), (.n 2225, 0), (.n 2226, 7), (.n 2233, 5), (.n 2239, 0), (.n 2240, 4), (.n 2247, 3), (.n 2253, 0), (.n 2254, 2), (.n 2842, 3), (.n 2848, 0), (.n 2849, 2), (.n 2974, 2), (.n 2980, 0), (.n 2981, 1), (.n 3233, 2), (.n 3239, 0), (.n 3240, 1)] Data.core329.params Data.core329.name ([], []) Data.core329.body = some (⟨114220, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core329.body)]
    rw [blockB_dropE _ _ _ 0 534 534 wsplit_329_0.1 rfl wsplit_329_0.2.2,
      ← blockR_eq ((Data.core329.body.drop 0).take 534), wsplit_329_0.2.1]
    rw [blockB_dropE _ _ _ 534 534 1068 wsplit_329_534.1 rfl wsplit_329_534.2.2,
      ← blockR_eq ((Data.core329.body.drop 534).take 534), wsplit_329_534.2.1]
    rw [blockB_dropE _ _ _ 1068 534 1602 wsplit_329_1068.1 rfl wsplit_329_1068.2.2,
      ← blockR_eq ((Data.core329.body.drop 1068).take 534), wsplit_329_1068.2.1]
    rw [blockB_dropE _ _ _ 1602 534 2136 wsplit_329_1602.1 rfl wsplit_329_1602.2.2,
      ← blockR_eq ((Data.core329.body.drop 1602).take 534), wsplit_329_1602.2.1]
    rw [blockB_dropE _ _ _ 2136 534 2670 wsplit_329_2136.1 rfl wsplit_329_2136.2.2,
      ← blockR_eq ((Data.core329.body.drop 2136).take 534), wsplit_329_2136.2.1]
    rw [blockB_dropE _ _ _ 2670 534 3204 wsplit_329_2670.1 rfl wsplit_329_2670.2.2,
      ← blockR_eq ((Data.core329.body.drop 2670).take 534), wsplit_329_2670.2.1]
    rw [← blockR_eq (Data.core329.body.drop 3204), wsplit_329_3204]
    rfl
  exact wchkIdx_of_split (fn := Data.core329) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem wchkIdx_all : ∀ j < 991, wchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact wchkIdx_19
  by_cases h1001 : j = 302
  · subst h1001; exact wchkIdx_302
  by_cases h1002 : j = 303
  · subst h1002; exact wchkIdx_303
  by_cases h1003 : j = 304
  · subst h1003; exact wchkIdx_304
  by_cases h1004 : j = 305
  · subst h1004; exact wchkIdx_305
  by_cases h1005 : j = 306
  · subst h1005; exact wchkIdx_306
  by_cases h1006 : j = 307
  · subst h1006; exact wchkIdx_307
  by_cases h1007 : j = 308
  · subst h1007; exact wchkIdx_308
  by_cases h1008 : j = 309
  · subst h1008; exact wchkIdx_309
  by_cases h1009 : j = 310
  · subst h1009; exact wchkIdx_310
  by_cases h1010 : j = 311
  · subst h1010; exact wchkIdx_311
  by_cases h1011 : j = 312
  · subst h1011; exact wchkIdx_312
  by_cases h1012 : j = 313
  · subst h1012; exact wchkIdx_313
  by_cases h1013 : j = 314
  · subst h1013; exact wchkIdx_314
  by_cases h1014 : j = 315
  · subst h1014; exact wchkIdx_315
  by_cases h1015 : j = 316
  · subst h1015; exact wchkIdx_316
  by_cases h1016 : j = 317
  · subst h1016; exact wchkIdx_317
  by_cases h1017 : j = 318
  · subst h1017; exact wchkIdx_318
  by_cases h1018 : j = 319
  · subst h1018; exact wchkIdx_319
  by_cases h1019 : j = 320
  · subst h1019; exact wchkIdx_320
  by_cases h1020 : j = 321
  · subst h1020; exact wchkIdx_321
  by_cases h1021 : j = 322
  · subst h1021; exact wchkIdx_322
  by_cases h1022 : j = 323
  · subst h1022; exact wchkIdx_323
  by_cases h1023 : j = 324
  · subst h1023; exact wchkIdx_324
  by_cases h1024 : j = 325
  · subst h1024; exact wchkIdx_325
  by_cases h1025 : j = 326
  · subst h1025; exact wchkIdx_326
  by_cases h1026 : j = 327
  · subst h1026; exact wchkIdx_327
  by_cases h1027 : j = 328
  · subst h1027; exact wchkIdx_328
  by_cases h1028 : j = 329
  · subst h1028; exact wchkIdx_329
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
  by_cases h10 : j < 186
  · exact wstaticRange_162.get (by omega) (by omega)
  by_cases h11 : j < 211
  · exact wstaticRange_186.get (by omega) (by omega)
  by_cases h12 : j < 237
  · exact wstaticRange_211.get (by omega) (by omega)
  by_cases h13 : j < 263
  · exact wstaticRange_237.get (by omega) (by omega)
  by_cases h14 : j < 283
  · exact wstaticRange_263.get (by omega) (by omega)
  by_cases h15 : j < 302
  · exact wstaticRange_283.get (by omega) (by omega)
  by_cases h16 : j < 351
  · exact wstaticRange_330.get (by omega) (by omega)
  by_cases h17 : j < 373
  · exact wstaticRange_351.get (by omega) (by omega)
  by_cases h18 : j < 396
  · exact wstaticRange_373.get (by omega) (by omega)
  by_cases h19 : j < 410
  · exact wstaticRange_396.get (by omega) (by omega)
  by_cases h20 : j < 430
  · exact wstaticRange_410.get (by omega) (by omega)
  by_cases h21 : j < 449
  · exact wstaticRange_430.get (by omega) (by omega)
  by_cases h22 : j < 469
  · exact wstaticRange_449.get (by omega) (by omega)
  by_cases h23 : j < 490
  · exact wstaticRange_469.get (by omega) (by omega)
  by_cases h24 : j < 511
  · exact wstaticRange_490.get (by omega) (by omega)
  by_cases h25 : j < 529
  · exact wstaticRange_511.get (by omega) (by omega)
  by_cases h26 : j < 547
  · exact wstaticRange_529.get (by omega) (by omega)
  by_cases h27 : j < 564
  · exact wstaticRange_547.get (by omega) (by omega)
  by_cases h28 : j < 582
  · exact wstaticRange_564.get (by omega) (by omega)
  by_cases h29 : j < 601
  · exact wstaticRange_582.get (by omega) (by omega)
  by_cases h30 : j < 616
  · exact wstaticRange_601.get (by omega) (by omega)
  by_cases h31 : j < 635
  · exact wstaticRange_616.get (by omega) (by omega)
  by_cases h32 : j < 652
  · exact wstaticRange_635.get (by omega) (by omega)
  by_cases h33 : j < 670
  · exact wstaticRange_652.get (by omega) (by omega)
  by_cases h34 : j < 687
  · exact wstaticRange_670.get (by omega) (by omega)
  by_cases h35 : j < 705
  · exact wstaticRange_687.get (by omega) (by omega)
  by_cases h36 : j < 722
  · exact wstaticRange_705.get (by omega) (by omega)
  by_cases h37 : j < 740
  · exact wstaticRange_722.get (by omega) (by omega)
  by_cases h38 : j < 758
  · exact wstaticRange_740.get (by omega) (by omega)
  by_cases h39 : j < 773
  · exact wstaticRange_758.get (by omega) (by omega)
  by_cases h40 : j < 792
  · exact wstaticRange_773.get (by omega) (by omega)
  by_cases h41 : j < 816
  · exact wstaticRange_792.get (by omega) (by omega)
  by_cases h42 : j < 840
  · exact wstaticRange_816.get (by omega) (by omega)
  by_cases h43 : j < 858
  · exact wstaticRange_840.get (by omega) (by omega)
  by_cases h44 : j < 874
  · exact wstaticRange_858.get (by omega) (by omega)
  by_cases h45 : j < 889
  · exact wstaticRange_874.get (by omega) (by omega)
  by_cases h46 : j < 905
  · exact wstaticRange_889.get (by omega) (by omega)
  by_cases h47 : j < 920
  · exact wstaticRange_905.get (by omega) (by omega)
  by_cases h48 : j < 930
  · exact wstaticRange_920.get (by omega) (by omega)
  by_cases h49 : j < 943
  · exact wstaticRange_930.get (by omega) (by omega)
  by_cases h50 : j < 958
  · exact wstaticRange_943.get (by omega) (by omega)
  by_cases h51 : j < 968
  · exact wstaticRange_958.get (by omega) (by omega)
  by_cases h52 : j < 977
  · exact wstaticRange_968.get (by omega) (by omega)
  by_cases h53 : j < 985
  · exact wstaticRange_977.get (by omega) (by omega)
  exact wstaticRange_985.get (by omega) (by omega)

end
end LeanVM.Guest
