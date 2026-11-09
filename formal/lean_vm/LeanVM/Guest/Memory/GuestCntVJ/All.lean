/-
  LeanVM.Guest.Memory.GuestCntVJ.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntVJ.Part00
public import LeanVM.Guest.Memory.GuestCntVJ.Part01
public import LeanVM.Guest.Memory.GuestCntVJ.Part02
public import LeanVM.Guest.Memory.GuestCntVJ.Part03
public import LeanVM.Guest.Memory.GuestCntVJ.Part04
public import LeanVM.Guest.Memory.GuestCntVJ.Part05
public import LeanVM.Guest.Memory.GuestCntVJ.Part06
public import LeanVM.Guest.Memory.GuestCntVJ.Part07
public import LeanVM.Guest.Memory.GuestCntVJ.Part08
public import LeanVM.Guest.Memory.GuestCntVJ.Part09
public import LeanVM.Guest.Memory.GuestCntVJ.Part10
public import LeanVM.Guest.Memory.GuestCntVJ.Part11
public import LeanVM.Guest.Memory.GuestCntVJ.Part12
public import LeanVM.Guest.Memory.GuestCntVJ.Part13
public import LeanVM.Guest.Memory.GuestCntVJ.Part14
public import LeanVM.Guest.Memory.GuestCntVJ.Part15
public import LeanVM.Guest.Memory.GuestCntVJ.Part16
public import LeanVM.Guest.Memory.GuestCntVJ.Part17
public import LeanVM.Guest.Memory.GuestCntVJ.Part18
public import LeanVM.Guest.Memory.GuestCntVJ.Part19
public import LeanVM.Guest.Memory.GuestCntVJ.Part20
public import LeanVM.Guest.Memory.GuestCntVJ.Part21
public import LeanVM.Guest.Memory.GuestCntVJ.Part22
public import LeanVM.Guest.Memory.GuestCntVJ.Part23
public import LeanVM.Guest.Memory.GuestCntVJ.Part24
public import LeanVM.Guest.Memory.GuestCntVJ.Part25
public import LeanVM.Guest.Memory.GuestCntVJ.Part26
public import LeanVM.Guest.Memory.GuestCntVJ.Part27
public import LeanVM.Guest.Memory.GuestCntVJ.Part28
public import LeanVM.Guest.Memory.GuestCntVJ.Part29
public import LeanVM.Guest.Memory.GuestCntVJ.Part30
public import LeanVM.Guest.Memory.GuestCntVJ.Part31

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjchkIdx_306 : kvjchkIdx 306 = true := by
  have hb : blockB (kvjlookJ 306) (kvjomLookJ 306) false [(.n 347, 0), (.n 348, 25), (.n 396, 112), (.n 584, 0), (.n 585, 7), (.n 638, 56), (.n 826, 0), (.n 827, 4), (.n 878, 32), (.n 1066, 0), (.n 1067, 3), (.n 1120, 23), (.n 1206, 0), (.n 1207, 2), (.n 1258, 18), (.n 1922, 0), (.n 1923, 28), (.n 1936, 0), (.n 1937, 7), (.n 1950, 0), (.n 1951, 4), (.n 1964, 0), (.n 1965, 2), (.n 2307, 0), (.n 2308, 2)] Data.core306.params Data.core306.name ([], []) Data.core306.body = some (⟨14864, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core306.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_306_0.1 rfl kvjsplit_306_0.2.2,
      ← blockR_eq ((Data.core306.body.drop 0).take 1320), kvjsplit_306_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_306_1320.1 rfl kvjsplit_306_1320.2.2,
      ← blockR_eq ((Data.core306.body.drop 1320).take 1320), kvjsplit_306_1320.2.1]
    rw [← blockR_eq (Data.core306.body.drop 2640), kvjsplit_306_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core306) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_307 : kvjchkIdx 307 = true := by
  have hb : blockB (kvjlookJ 307) (kvjomLookJ 307) false [(.n 347, 0), (.n 348, 29), (.n 397, 112), (.n 585, 0), (.n 586, 7), (.n 639, 56), (.n 827, 0), (.n 828, 4), (.n 879, 32), (.n 1067, 0), (.n 1068, 3), (.n 1121, 23), (.n 1207, 0), (.n 1208, 2), (.n 1259, 18), (.n 1970, 0), (.n 1971, 28), (.n 2109, 0), (.n 2110, 7), (.n 2123, 0), (.n 2124, 4), (.n 2137, 0), (.n 2138, 2), (.n 2522, 0), (.n 2523, 2)] Data.core307.params Data.core307.name ([], []) Data.core307.body = some (⟨14984, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core307.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_307_0.1 rfl kvjsplit_307_0.2.2,
      ← blockR_eq ((Data.core307.body.drop 0).take 1320), kvjsplit_307_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_307_1320.1 rfl kvjsplit_307_1320.2.2,
      ← blockR_eq ((Data.core307.body.drop 1320).take 1320), kvjsplit_307_1320.2.1]
    rw [← blockR_eq (Data.core307.body.drop 2640), kvjsplit_307_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core307) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_308 : kvjchkIdx 308 = true := by
  have hb : blockB (kvjlookJ 308) (kvjomLookJ 308) false [(.n 347, 0), (.n 348, 29), (.n 397, 112), (.n 585, 0), (.n 586, 7), (.n 639, 56), (.n 827, 0), (.n 828, 4), (.n 879, 32), (.n 1067, 0), (.n 1068, 3), (.n 1121, 23), (.n 1309, 0), (.n 1310, 2), (.n 1361, 18), (.n 1447, 0), (.n 1448, 2), (.n 1499, 14), (.n 2230, 0), (.n 2231, 28), (.n 2375, 0), (.n 2376, 7), (.n 2389, 0), (.n 2390, 4), (.n 2403, 0), (.n 2404, 2), (.n 2830, 0), (.n 2831, 2), (.n 2914, 0), (.n 2915, 1)] Data.core308.params Data.core308.name ([], []) Data.core308.body = some (⟨15497, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core308.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvjsplit_308_0.1 rfl kvjsplit_308_0.2.2,
      ← blockR_eq ((Data.core308.body.drop 0).take 1111), kvjsplit_308_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvjsplit_308_1111.1 rfl kvjsplit_308_1111.2.2,
      ← blockR_eq ((Data.core308.body.drop 1111).take 1111), kvjsplit_308_1111.2.1]
    rw [blockB_dropE _ _ _ 2222 1111 3333 kvjsplit_308_2222.1 rfl kvjsplit_308_2222.2.2,
      ← blockR_eq ((Data.core308.body.drop 2222).take 1111), kvjsplit_308_2222.2.1]
    rw [← blockR_eq (Data.core308.body.drop 3333), kvjsplit_308_3333]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core308) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_311 : kvjchkIdx 311 = true := by
  have hb : blockB (kvjlookJ 311) (kvjomLookJ 311) false [(.n 347, 0), (.n 348, 13), (.n 395, 56), (.n 583, 0), (.n 584, 5), (.n 638, 45), (.n 826, 0), (.n 827, 3), (.n 879, 28), (.n 1067, 0), (.n 1068, 2), (.n 1120, 21), (.n 1206, 0), (.n 1207, 2), (.n 1257, 16), (.n 1827, 0), (.n 1828, 14), (.n 1841, 0), (.n 1842, 5), (.n 2270, 0), (.n 2271, 3), (.n 2520, 0), (.n 2521, 2), (.n 2709, 0), (.n 2710, 2)] Data.core311.params Data.core311.name ([], []) Data.core311.body = some (⟨9158, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core311.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_311_0.1 rfl kvjsplit_311_0.2.2,
      ← blockR_eq ((Data.core311.body.drop 0).take 1320), kvjsplit_311_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_311_1320.1 rfl kvjsplit_311_1320.2.2,
      ← blockR_eq ((Data.core311.body.drop 1320).take 1320), kvjsplit_311_1320.2.1]
    rw [← blockR_eq (Data.core311.body.drop 2640), kvjsplit_311_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core311) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_312 : kvjchkIdx 312 = true := by
  have hb : blockB (kvjlookJ 312) (kvjomLookJ 312) false [(.n 347, 0), (.n 348, 13), (.n 395, 56), (.n 583, 0), (.n 584, 5), (.n 638, 45), (.n 826, 0), (.n 827, 3), (.n 879, 28), (.n 1067, 0), (.n 1068, 3), (.n 1120, 21), (.n 1206, 0), (.n 1207, 2), (.n 1257, 16), (.n 1874, 0), (.n 1875, 14), (.n 1888, 0), (.n 1889, 5), (.n 2347, 0), (.n 2348, 3), (.n 2621, 0), (.n 2622, 2), (.n 2840, 0), (.n 2841, 2)] Data.core312.params Data.core312.name ([], []) Data.core312.body = some (⟨9249, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core312.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_312_0.1 rfl kvjsplit_312_0.2.2,
      ← blockR_eq ((Data.core312.body.drop 0).take 1320), kvjsplit_312_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_312_1320.1 rfl kvjsplit_312_1320.2.2,
      ← blockR_eq ((Data.core312.body.drop 1320).take 1320), kvjsplit_312_1320.2.1]
    rw [← blockR_eq (Data.core312.body.drop 2640), kvjsplit_312_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core312) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_313 : kvjchkIdx 313 = true := by
  have hb : blockB (kvjlookJ 313) (kvjomLookJ 313) false [(.n 347, 0), (.n 348, 14), (.n 395, 56), (.n 583, 0), (.n 584, 5), (.n 638, 45), (.n 826, 0), (.n 827, 4), (.n 879, 28), (.n 1067, 0), (.n 1068, 3), (.n 1120, 21), (.n 1206, 0), (.n 1207, 2), (.n 1257, 16), (.n 1921, 0), (.n 1922, 14), (.n 1935, 0), (.n 1936, 5), (.n 2424, 0), (.n 2425, 3), (.n 2722, 0), (.n 2723, 2), (.n 2971, 0), (.n 2972, 2)] Data.core313.params Data.core313.name ([], []) Data.core313.body = some (⟨9275, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core313.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_313_0.1 rfl kvjsplit_313_0.2.2,
      ← blockR_eq ((Data.core313.body.drop 0).take 1320), kvjsplit_313_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_313_1320.1 rfl kvjsplit_313_1320.2.2,
      ← blockR_eq ((Data.core313.body.drop 1320).take 1320), kvjsplit_313_1320.2.1]
    rw [← blockR_eq (Data.core313.body.drop 2640), kvjsplit_313_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core313) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_314 : kvjchkIdx 314 = true := by
  have hb : blockB (kvjlookJ 314) (kvjomLookJ 314) false [(.n 347, 0), (.n 348, 14), (.n 395, 56), (.n 583, 0), (.n 584, 6), (.n 638, 45), (.n 826, 0), (.n 827, 4), (.n 879, 28), (.n 1067, 0), (.n 1068, 3), (.n 1120, 21), (.n 1206, 0), (.n 1207, 2), (.n 1257, 16), (.n 1968, 0), (.n 1969, 14), (.n 1982, 0), (.n 1983, 5), (.n 2501, 0), (.n 2502, 3), (.n 2823, 0), (.n 2824, 2), (.n 3102, 0), (.n 3103, 2)] Data.core314.params Data.core314.name ([], []) Data.core314.body = some (⟨9304, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core314.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_314_0.1 rfl kvjsplit_314_0.2.2,
      ← blockR_eq ((Data.core314.body.drop 0).take 1320), kvjsplit_314_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_314_1320.1 rfl kvjsplit_314_1320.2.2,
      ← blockR_eq ((Data.core314.body.drop 1320).take 1320), kvjsplit_314_1320.2.1]
    rw [← blockR_eq (Data.core314.body.drop 2640), kvjsplit_314_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core314) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_315 : kvjchkIdx 315 = true := by
  have hb : blockB (kvjlookJ 315) (kvjomLookJ 315) false [(.n 347, 0), (.n 348, 14), (.n 395, 56), (.n 583, 0), (.n 584, 6), (.n 638, 45), (.n 826, 0), (.n 827, 4), (.n 879, 28), (.n 1067, 0), (.n 1068, 3), (.n 1120, 21), (.n 1308, 0), (.n 1309, 2), (.n 1359, 16), (.n 1445, 0), (.n 1446, 2), (.n 1497, 13), (.n 2228, 0), (.n 2229, 14), (.n 2242, 0), (.n 2243, 5), (.n 2791, 0), (.n 2792, 3), (.n 3137, 0), (.n 3138, 2), (.n 3446, 0), (.n 3447, 2), (.n 3460, 0), (.n 3461, 1)] Data.core315.params Data.core315.name ([], []) Data.core315.body = some (⟨9783, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core315.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvjsplit_315_0.1 rfl kvjsplit_315_0.2.2,
      ← blockR_eq ((Data.core315.body.drop 0).take 1111), kvjsplit_315_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvjsplit_315_1111.1 rfl kvjsplit_315_1111.2.2,
      ← blockR_eq ((Data.core315.body.drop 1111).take 1111), kvjsplit_315_1111.2.1]
    rw [blockB_dropE _ _ _ 2222 1111 3333 kvjsplit_315_2222.1 rfl kvjsplit_315_2222.2.2,
      ← blockR_eq ((Data.core315.body.drop 2222).take 1111), kvjsplit_315_2222.2.1]
    rw [← blockR_eq (Data.core315.body.drop 3333), kvjsplit_315_3333]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core315) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_318 : kvjchkIdx 318 = true := by
  have hb : blockB (kvjlookJ 318) (kvjomLookJ 318) false [(.n 347, 0), (.n 348, 9), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 3), (.n 879, 25), (.n 1067, 0), (.n 1068, 2), (.n 1120, 19), (.n 1206, 0), (.n 1207, 2), (.n 1259, 15), (.n 1829, 0), (.n 1830, 9), (.n 2164, 0), (.n 2165, 4), (.n 2676, 0), (.n 2677, 3), (.n 2749, 0), (.n 2750, 2), (.n 2868, 0), (.n 2869, 1)] Data.core318.params Data.core318.name ([], []) Data.core318.body = some (⟨7238, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core318.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_318_0.1 rfl kvjsplit_318_0.2.2,
      ← blockR_eq ((Data.core318.body.drop 0).take 1320), kvjsplit_318_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_318_1320.1 rfl kvjsplit_318_1320.2.2,
      ← blockR_eq ((Data.core318.body.drop 1320).take 1320), kvjsplit_318_1320.2.1]
    rw [← blockR_eq (Data.core318.body.drop 2640), kvjsplit_318_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core318) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_319 : kvjchkIdx 319 = true := by
  have hb : blockB (kvjlookJ 319) (kvjomLookJ 319) false [(.n 347, 0), (.n 348, 10), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 3), (.n 879, 25), (.n 1067, 0), (.n 1068, 2), (.n 1120, 19), (.n 1206, 0), (.n 1207, 2), (.n 1259, 15), (.n 1876, 0), (.n 1877, 9), (.n 2229, 0), (.n 2230, 4), (.n 2777, 0), (.n 2778, 3), (.n 2856, 0), (.n 2857, 2), (.n 2993, 0), (.n 2994, 1)] Data.core319.params Data.core319.name ([], []) Data.core319.body = some (⟨7255, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core319.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_319_0.1 rfl kvjsplit_319_0.2.2,
      ← blockR_eq ((Data.core319.body.drop 0).take 1320), kvjsplit_319_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_319_1320.1 rfl kvjsplit_319_1320.2.2,
      ← blockR_eq ((Data.core319.body.drop 1320).take 1320), kvjsplit_319_1320.2.1]
    rw [← blockR_eq (Data.core319.body.drop 2640), kvjsplit_319_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core319) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_320 : kvjchkIdx 320 = true := by
  have hb : blockB (kvjlookJ 320) (kvjomLookJ 320) false [(.n 347, 0), (.n 348, 10), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 3), (.n 879, 25), (.n 1067, 0), (.n 1068, 3), (.n 1120, 19), (.n 1206, 0), (.n 1207, 2), (.n 1259, 15), (.n 1923, 0), (.n 1924, 9), (.n 2294, 0), (.n 2295, 4), (.n 2878, 0), (.n 2879, 3), (.n 2963, 0), (.n 2964, 2), (.n 3118, 0), (.n 3119, 1)] Data.core320.params Data.core320.name ([], []) Data.core320.body = some (⟨7276, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core320.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_320_0.1 rfl kvjsplit_320_0.2.2,
      ← blockR_eq ((Data.core320.body.drop 0).take 1320), kvjsplit_320_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_320_1320.1 rfl kvjsplit_320_1320.2.2,
      ← blockR_eq ((Data.core320.body.drop 1320).take 1320), kvjsplit_320_1320.2.1]
    rw [← blockR_eq (Data.core320.body.drop 2640), kvjsplit_320_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core320) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_321 : kvjchkIdx 321 = true := by
  have hb : blockB (kvjlookJ 321) (kvjomLookJ 321) false [(.n 347, 0), (.n 348, 10), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 4), (.n 879, 25), (.n 1067, 0), (.n 1068, 3), (.n 1120, 19), (.n 1206, 0), (.n 1207, 2), (.n 1259, 15), (.n 1970, 0), (.n 1971, 9), (.n 2359, 0), (.n 2360, 4), (.n 2979, 0), (.n 2980, 3), (.n 3070, 0), (.n 3071, 2), (.n 3243, 0), (.n 3244, 1)] Data.core321.params Data.core321.name ([], []) Data.core321.body = some (⟨7305, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core321.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_321_0.1 rfl kvjsplit_321_0.2.2,
      ← blockR_eq ((Data.core321.body.drop 0).take 1320), kvjsplit_321_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_321_1320.1 rfl kvjsplit_321_1320.2.2,
      ← blockR_eq ((Data.core321.body.drop 1320).take 1320), kvjsplit_321_1320.2.1]
    rw [← blockR_eq (Data.core321.body.drop 2640), kvjsplit_321_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core321) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_322 : kvjchkIdx 322 = true := by
  have hb : blockB (kvjlookJ 322) (kvjomLookJ 322) false [(.n 347, 0), (.n 348, 11), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 4), (.n 879, 25), (.n 1067, 0), (.n 1068, 3), (.n 1120, 19), (.n 1308, 0), (.n 1309, 2), (.n 1361, 15), (.n 1447, 0), (.n 1448, 2), (.n 1499, 13), (.n 2230, 0), (.n 2231, 9), (.n 2637, 0), (.n 2638, 4), (.n 3293, 0), (.n 3294, 3), (.n 3390, 0), (.n 3391, 2), (.n 3581, 0), (.n 3582, 1), (.n 3840, 0), (.n 3841, 1)] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨7789, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvjsplit_322_0.1 rfl kvjsplit_322_0.2.2,
      ← blockR_eq ((Data.core322.body.drop 0).take 1111), kvjsplit_322_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvjsplit_322_1111.1 rfl kvjsplit_322_1111.2.2,
      ← blockR_eq ((Data.core322.body.drop 1111).take 1111), kvjsplit_322_1111.2.1]
    rw [blockB_dropE _ _ _ 2222 1111 3333 kvjsplit_322_2222.1 rfl kvjsplit_322_2222.2.2,
      ← blockR_eq ((Data.core322.body.drop 2222).take 1111), kvjsplit_322_2222.2.1]
    rw [← blockR_eq (Data.core322.body.drop 3333), kvjsplit_322_3333]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_325 : kvjchkIdx 325 = true := by
  have hb : blockB (kvjlookJ 325) (kvjomLookJ 325) false [(.n 347, 0), (.n 348, 7), (.n 394, 28), (.n 582, 0), (.n 583, 4), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 2), (.n 1116, 18), (.n 1202, 0), (.n 1203, 2), (.n 1254, 14), (.n 1824, 0), (.n 1825, 7), (.n 1838, 0), (.n 1839, 4), (.n 1852, 0), (.n 1853, 2), (.n 2279, 0), (.n 2280, 2), (.n 2363, 0), (.n 2364, 1)] Data.core325.params Data.core325.name ([], []) Data.core325.body = some (⟨5907, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core325.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_325_0.1 rfl kvjsplit_325_0.2.2,
      ← blockR_eq ((Data.core325.body.drop 0).take 1320), kvjsplit_325_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_325_1320.1 rfl kvjsplit_325_1320.2.2,
      ← blockR_eq ((Data.core325.body.drop 1320).take 1320), kvjsplit_325_1320.2.1]
    rw [← blockR_eq (Data.core325.body.drop 2640), kvjsplit_325_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core325) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_326 : kvjchkIdx 326 = true := by
  have hb : blockB (kvjlookJ 326) (kvjomLookJ 326) false [(.n 347, 0), (.n 348, 7), (.n 394, 28), (.n 582, 0), (.n 583, 4), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 2), (.n 1116, 18), (.n 1202, 0), (.n 1203, 2), (.n 1254, 14), (.n 1871, 0), (.n 1872, 7), (.n 1885, 0), (.n 1886, 4), (.n 1899, 0), (.n 1900, 2), (.n 2368, 0), (.n 2369, 2), (.n 2464, 0), (.n 2465, 1)] Data.core326.params Data.core326.name ([], []) Data.core326.body = some (⟨5919, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core326.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_326_0.1 rfl kvjsplit_326_0.2.2,
      ← blockR_eq ((Data.core326.body.drop 0).take 1320), kvjsplit_326_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_326_1320.1 rfl kvjsplit_326_1320.2.2,
      ← blockR_eq ((Data.core326.body.drop 1320).take 1320), kvjsplit_326_1320.2.1]
    rw [← blockR_eq (Data.core326.body.drop 2640), kvjsplit_326_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core326) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_327 : kvjchkIdx 327 = true := by
  have hb : blockB (kvjlookJ 327) (kvjomLookJ 327) false [(.n 347, 0), (.n 348, 7), (.n 394, 28), (.n 582, 0), (.n 583, 4), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 2), (.n 1116, 18), (.n 1202, 0), (.n 1203, 2), (.n 1254, 14), (.n 1918, 0), (.n 1919, 7), (.n 1932, 0), (.n 1933, 4), (.n 1946, 0), (.n 1947, 2), (.n 2457, 0), (.n 2458, 2), (.n 2565, 0), (.n 2566, 1)] Data.core327.params Data.core327.name ([], []) Data.core327.body = some (⟨5935, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core327.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_327_0.1 rfl kvjsplit_327_0.2.2,
      ← blockR_eq ((Data.core327.body.drop 0).take 1320), kvjsplit_327_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_327_1320.1 rfl kvjsplit_327_1320.2.2,
      ← blockR_eq ((Data.core327.body.drop 1320).take 1320), kvjsplit_327_1320.2.1]
    rw [← blockR_eq (Data.core327.body.drop 2640), kvjsplit_327_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core327) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_328 : kvjchkIdx 328 = true := by
  have hb : blockB (kvjlookJ 328) (kvjomLookJ 328) false [(.n 347, 0), (.n 348, 8), (.n 394, 28), (.n 582, 0), (.n 583, 4), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 3), (.n 1116, 18), (.n 1202, 0), (.n 1203, 2), (.n 1255, 15), (.n 1966, 0), (.n 1967, 7), (.n 1980, 0), (.n 1981, 4), (.n 1994, 0), (.n 1995, 2), (.n 2547, 0), (.n 2548, 2), (.n 2667, 0), (.n 2668, 1)] Data.core328.params Data.core328.name ([], []) Data.core328.body = some (⟨6179, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core328.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvjsplit_328_0.1 rfl kvjsplit_328_0.2.2,
      ← blockR_eq ((Data.core328.body.drop 0).take 1320), kvjsplit_328_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvjsplit_328_1320.1 rfl kvjsplit_328_1320.2.2,
      ← blockR_eq ((Data.core328.body.drop 1320).take 1320), kvjsplit_328_1320.2.1]
    rw [← blockR_eq (Data.core328.body.drop 2640), kvjsplit_328_2640]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core328) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_329 : kvjchkIdx 329 = true := by
  have hb : blockB (kvjlookJ 329) (kvjomLookJ 329) false [(.n 347, 0), (.n 348, 8), (.n 394, 28), (.n 582, 0), (.n 583, 5), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 3), (.n 1116, 18), (.n 1304, 0), (.n 1305, 2), (.n 1357, 15), (.n 1443, 0), (.n 1444, 2), (.n 1494, 12), (.n 2225, 0), (.n 2226, 7), (.n 2239, 0), (.n 2240, 4), (.n 2253, 0), (.n 2254, 2), (.n 2848, 0), (.n 2849, 2), (.n 2980, 0), (.n 2981, 1), (.n 3239, 0), (.n 3240, 1)] Data.core329.params Data.core329.name ([], []) Data.core329.body = some (⟨6675, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core329.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvjsplit_329_0.1 rfl kvjsplit_329_0.2.2,
      ← blockR_eq ((Data.core329.body.drop 0).take 1111), kvjsplit_329_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvjsplit_329_1111.1 rfl kvjsplit_329_1111.2.2,
      ← blockR_eq ((Data.core329.body.drop 1111).take 1111), kvjsplit_329_1111.2.1]
    rw [blockB_dropE _ _ _ 2222 1111 3333 kvjsplit_329_2222.1 rfl kvjsplit_329_2222.2.2,
      ← blockR_eq ((Data.core329.body.drop 2222).take 1111), kvjsplit_329_2222.2.1]
    rw [← blockR_eq (Data.core329.body.drop 3333), kvjsplit_329_3333]
    rfl
  exact kvjchkIdx_of_split (fn := Data.core329) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvjchkIdx_all : ∀ j < 991, kvjchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 306
  · subst h1000; exact kvjchkIdx_306
  by_cases h1001 : j = 307
  · subst h1001; exact kvjchkIdx_307
  by_cases h1002 : j = 308
  · subst h1002; exact kvjchkIdx_308
  by_cases h1003 : j = 311
  · subst h1003; exact kvjchkIdx_311
  by_cases h1004 : j = 312
  · subst h1004; exact kvjchkIdx_312
  by_cases h1005 : j = 313
  · subst h1005; exact kvjchkIdx_313
  by_cases h1006 : j = 314
  · subst h1006; exact kvjchkIdx_314
  by_cases h1007 : j = 315
  · subst h1007; exact kvjchkIdx_315
  by_cases h1008 : j = 318
  · subst h1008; exact kvjchkIdx_318
  by_cases h1009 : j = 319
  · subst h1009; exact kvjchkIdx_319
  by_cases h1010 : j = 320
  · subst h1010; exact kvjchkIdx_320
  by_cases h1011 : j = 321
  · subst h1011; exact kvjchkIdx_321
  by_cases h1012 : j = 322
  · subst h1012; exact kvjchkIdx_322
  by_cases h1013 : j = 325
  · subst h1013; exact kvjchkIdx_325
  by_cases h1014 : j = 326
  · subst h1014; exact kvjchkIdx_326
  by_cases h1015 : j = 327
  · subst h1015; exact kvjchkIdx_327
  by_cases h1016 : j = 328
  · subst h1016; exact kvjchkIdx_328
  by_cases h1017 : j = 329
  · subst h1017; exact kvjchkIdx_329
  by_cases h0 : j < 11
  · exact kvjstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvjstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kvjstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 78
  · exact kvjstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 108
  · exact kvjstaticRange_78.get (by omega) (by omega)
  by_cases h5 : j < 138
  · exact kvjstaticRange_108.get (by omega) (by omega)
  by_cases h6 : j < 168
  · exact kvjstaticRange_138.get (by omega) (by omega)
  by_cases h7 : j < 198
  · exact kvjstaticRange_168.get (by omega) (by omega)
  by_cases h8 : j < 228
  · exact kvjstaticRange_198.get (by omega) (by omega)
  by_cases h9 : j < 258
  · exact kvjstaticRange_228.get (by omega) (by omega)
  by_cases h10 : j < 288
  · exact kvjstaticRange_258.get (by omega) (by omega)
  by_cases h11 : j < 303
  · exact kvjstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 304
  · exact kvjstaticRange_303.get (by omega) (by omega)
  by_cases h13 : j < 305
  · exact kvjstaticRange_304.get (by omega) (by omega)
  by_cases h14 : j < 306
  · exact kvjstaticRange_305.get (by omega) (by omega)
  by_cases h15 : j < 310
  · exact kvjstaticRange_309.get (by omega) (by omega)
  by_cases h16 : j < 311
  · exact kvjstaticRange_310.get (by omega) (by omega)
  by_cases h17 : j < 317
  · exact kvjstaticRange_316.get (by omega) (by omega)
  by_cases h18 : j < 318
  · exact kvjstaticRange_317.get (by omega) (by omega)
  by_cases h19 : j < 324
  · exact kvjstaticRange_323.get (by omega) (by omega)
  by_cases h20 : j < 325
  · exact kvjstaticRange_324.get (by omega) (by omega)
  by_cases h21 : j < 351
  · exact kvjstaticRange_330.get (by omega) (by omega)
  by_cases h22 : j < 373
  · exact kvjstaticRange_351.get (by omega) (by omega)
  by_cases h23 : j < 396
  · exact kvjstaticRange_373.get (by omega) (by omega)
  by_cases h24 : j < 410
  · exact kvjstaticRange_396.get (by omega) (by omega)
  by_cases h25 : j < 440
  · exact kvjstaticRange_410.get (by omega) (by omega)
  by_cases h26 : j < 461
  · exact kvjstaticRange_440.get (by omega) (by omega)
  by_cases h27 : j < 482
  · exact kvjstaticRange_461.get (by omega) (by omega)
  by_cases h28 : j < 502
  · exact kvjstaticRange_482.get (by omega) (by omega)
  by_cases h29 : j < 520
  · exact kvjstaticRange_502.get (by omega) (by omega)
  by_cases h30 : j < 538
  · exact kvjstaticRange_520.get (by omega) (by omega)
  by_cases h31 : j < 556
  · exact kvjstaticRange_538.get (by omega) (by omega)
  by_cases h32 : j < 574
  · exact kvjstaticRange_556.get (by omega) (by omega)
  by_cases h33 : j < 592
  · exact kvjstaticRange_574.get (by omega) (by omega)
  by_cases h34 : j < 610
  · exact kvjstaticRange_592.get (by omega) (by omega)
  by_cases h35 : j < 628
  · exact kvjstaticRange_610.get (by omega) (by omega)
  by_cases h36 : j < 644
  · exact kvjstaticRange_628.get (by omega) (by omega)
  by_cases h37 : j < 661
  · exact kvjstaticRange_644.get (by omega) (by omega)
  by_cases h38 : j < 679
  · exact kvjstaticRange_661.get (by omega) (by omega)
  by_cases h39 : j < 694
  · exact kvjstaticRange_679.get (by omega) (by omega)
  by_cases h40 : j < 712
  · exact kvjstaticRange_694.get (by omega) (by omega)
  by_cases h41 : j < 730
  · exact kvjstaticRange_712.get (by omega) (by omega)
  by_cases h42 : j < 748
  · exact kvjstaticRange_730.get (by omega) (by omega)
  by_cases h43 : j < 766
  · exact kvjstaticRange_748.get (by omega) (by omega)
  by_cases h44 : j < 784
  · exact kvjstaticRange_766.get (by omega) (by omega)
  by_cases h45 : j < 804
  · exact kvjstaticRange_784.get (by omega) (by omega)
  by_cases h46 : j < 828
  · exact kvjstaticRange_804.get (by omega) (by omega)
  by_cases h47 : j < 850
  · exact kvjstaticRange_828.get (by omega) (by omega)
  by_cases h48 : j < 867
  · exact kvjstaticRange_850.get (by omega) (by omega)
  by_cases h49 : j < 883
  · exact kvjstaticRange_867.get (by omega) (by omega)
  by_cases h50 : j < 898
  · exact kvjstaticRange_883.get (by omega) (by omega)
  by_cases h51 : j < 913
  · exact kvjstaticRange_898.get (by omega) (by omega)
  by_cases h52 : j < 925
  · exact kvjstaticRange_913.get (by omega) (by omega)
  by_cases h53 : j < 936
  · exact kvjstaticRange_925.get (by omega) (by omega)
  by_cases h54 : j < 950
  · exact kvjstaticRange_936.get (by omega) (by omega)
  by_cases h55 : j < 963
  · exact kvjstaticRange_950.get (by omega) (by omega)
  by_cases h56 : j < 972
  · exact kvjstaticRange_963.get (by omega) (by omega)
  by_cases h57 : j < 981
  · exact kvjstaticRange_972.get (by omega) (by omega)
  by_cases h58 : j < 988
  · exact kvjstaticRange_981.get (by omega) (by omega)
  exact kvjstaticRange_988.get (by omega) (by omega)

end
end LeanVM.Guest
