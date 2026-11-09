/-
  LeanVM.Guest.Memory.GuestCntVK.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntVK.Part00
public import LeanVM.Guest.Memory.GuestCntVK.Part01
public import LeanVM.Guest.Memory.GuestCntVK.Part02
public import LeanVM.Guest.Memory.GuestCntVK.Part03
public import LeanVM.Guest.Memory.GuestCntVK.Part04
public import LeanVM.Guest.Memory.GuestCntVK.Part05
public import LeanVM.Guest.Memory.GuestCntVK.Part06
public import LeanVM.Guest.Memory.GuestCntVK.Part07
public import LeanVM.Guest.Memory.GuestCntVK.Part08
public import LeanVM.Guest.Memory.GuestCntVK.Part09
public import LeanVM.Guest.Memory.GuestCntVK.Part10
public import LeanVM.Guest.Memory.GuestCntVK.Part11
public import LeanVM.Guest.Memory.GuestCntVK.Part12
public import LeanVM.Guest.Memory.GuestCntVK.Part13
public import LeanVM.Guest.Memory.GuestCntVK.Part14
public import LeanVM.Guest.Memory.GuestCntVK.Part15
public import LeanVM.Guest.Memory.GuestCntVK.Part16
public import LeanVM.Guest.Memory.GuestCntVK.Part17
public import LeanVM.Guest.Memory.GuestCntVK.Part18
public import LeanVM.Guest.Memory.GuestCntVK.Part19
public import LeanVM.Guest.Memory.GuestCntVK.Part20
public import LeanVM.Guest.Memory.GuestCntVK.Part21
public import LeanVM.Guest.Memory.GuestCntVK.Part22
public import LeanVM.Guest.Memory.GuestCntVK.Part23
public import LeanVM.Guest.Memory.GuestCntVK.Part24
public import LeanVM.Guest.Memory.GuestCntVK.Part25
public import LeanVM.Guest.Memory.GuestCntVK.Part26
public import LeanVM.Guest.Memory.GuestCntVK.Part27
public import LeanVM.Guest.Memory.GuestCntVK.Part28
public import LeanVM.Guest.Memory.GuestCntVK.Part29
public import LeanVM.Guest.Memory.GuestCntVK.Part30
public import LeanVM.Guest.Memory.GuestCntVK.Part31

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkchkIdx_306 : kvkchkIdx 306 = true := by
  have hb : blockB (kvklookJ 306) (kvkomLookJ 306) false [(.n 347, 0), (.n 348, 25), (.n 396, 112), (.n 584, 0), (.n 585, 7), (.n 638, 56), (.n 826, 0), (.n 827, 4), (.n 878, 32), (.n 1066, 0), (.n 1067, 3), (.n 1120, 23), (.n 1206, 0), (.n 1207, 2), (.n 1258, 18), (.n 1922, 0), (.n 1923, 28), (.n 1936, 0), (.n 1937, 7), (.n 1950, 0), (.n 1951, 4), (.n 1964, 0), (.n 1965, 2), (.n 2307, 0), (.n 2308, 2)] Data.core306.params Data.core306.name ([], []) Data.core306.body = some (⟨6480, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core306.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvksplit_306_0.1 rfl kvksplit_306_0.2.2,
      ← blockR_eq ((Data.core306.body.drop 0).take 1320), kvksplit_306_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvksplit_306_1320.1 rfl kvksplit_306_1320.2.2,
      ← blockR_eq ((Data.core306.body.drop 1320).take 1320), kvksplit_306_1320.2.1]
    rw [← blockR_eq (Data.core306.body.drop 2640), kvksplit_306_2640]
    rfl
  exact kvkchkIdx_of_split (fn := Data.core306) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_307 : kvkchkIdx 307 = true := by
  have hb : blockB (kvklookJ 307) (kvkomLookJ 307) false [(.n 347, 0), (.n 348, 29), (.n 397, 112), (.n 585, 0), (.n 586, 7), (.n 639, 56), (.n 827, 0), (.n 828, 4), (.n 879, 32), (.n 1067, 0), (.n 1068, 3), (.n 1121, 23), (.n 1207, 0), (.n 1208, 2), (.n 1259, 18), (.n 1970, 0), (.n 1971, 28), (.n 2109, 0), (.n 2110, 7), (.n 2123, 0), (.n 2124, 4), (.n 2137, 0), (.n 2138, 2), (.n 2522, 0), (.n 2523, 2)] Data.core307.params Data.core307.name ([], []) Data.core307.body = some (⟨6864, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core307.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvksplit_307_0.1 rfl kvksplit_307_0.2.2,
      ← blockR_eq ((Data.core307.body.drop 0).take 1320), kvksplit_307_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvksplit_307_1320.1 rfl kvksplit_307_1320.2.2,
      ← blockR_eq ((Data.core307.body.drop 1320).take 1320), kvksplit_307_1320.2.1]
    rw [← blockR_eq (Data.core307.body.drop 2640), kvksplit_307_2640]
    rfl
  exact kvkchkIdx_of_split (fn := Data.core307) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_308 : kvkchkIdx 308 = true := by
  have hb : blockB (kvklookJ 308) (kvkomLookJ 308) false [(.n 347, 0), (.n 348, 29), (.n 397, 112), (.n 585, 0), (.n 586, 7), (.n 639, 56), (.n 827, 0), (.n 828, 4), (.n 879, 32), (.n 1067, 0), (.n 1068, 3), (.n 1121, 23), (.n 1309, 0), (.n 1310, 2), (.n 1361, 18), (.n 1447, 0), (.n 1448, 2), (.n 1499, 14), (.n 2230, 0), (.n 2231, 28), (.n 2375, 0), (.n 2376, 7), (.n 2389, 0), (.n 2390, 4), (.n 2403, 0), (.n 2404, 2), (.n 2830, 0), (.n 2831, 2), (.n 2914, 0), (.n 2915, 1)] Data.core308.params Data.core308.name ([], []) Data.core308.body = some (⟨7477, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core308.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvksplit_308_0.1 rfl kvksplit_308_0.2.2,
      ← blockR_eq ((Data.core308.body.drop 0).take 1111), kvksplit_308_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvksplit_308_1111.1 rfl kvksplit_308_1111.2.2,
      ← blockR_eq ((Data.core308.body.drop 1111).take 1111), kvksplit_308_1111.2.1]
    rw [blockB_dropE _ _ _ 2222 1111 3333 kvksplit_308_2222.1 rfl kvksplit_308_2222.2.2,
      ← blockR_eq ((Data.core308.body.drop 2222).take 1111), kvksplit_308_2222.2.1]
    rw [← blockR_eq (Data.core308.body.drop 3333), kvksplit_308_3333]
    rfl
  exact kvkchkIdx_of_split (fn := Data.core308) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_311 : kvkchkIdx 311 = true := by
  have hb : blockB (kvklookJ 311) (kvkomLookJ 311) false [(.n 347, 0), (.n 348, 13), (.n 395, 56), (.n 583, 0), (.n 584, 5), (.n 638, 45), (.n 826, 0), (.n 827, 3), (.n 879, 28), (.n 1067, 0), (.n 1068, 2), (.n 1120, 21), (.n 1206, 0), (.n 1207, 2), (.n 1257, 16), (.n 1827, 0), (.n 1828, 14), (.n 1841, 0), (.n 1842, 5), (.n 2270, 0), (.n 2271, 3), (.n 2520, 0), (.n 2521, 2), (.n 2709, 0), (.n 2710, 2)] Data.core311.params Data.core311.name ([], []) Data.core311.body = some (⟨3992, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core311.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvksplit_311_0.1 rfl kvksplit_311_0.2.2,
      ← blockR_eq ((Data.core311.body.drop 0).take 1320), kvksplit_311_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvksplit_311_1320.1 rfl kvksplit_311_1320.2.2,
      ← blockR_eq ((Data.core311.body.drop 1320).take 1320), kvksplit_311_1320.2.1]
    rw [← blockR_eq (Data.core311.body.drop 2640), kvksplit_311_2640]
    rfl
  exact kvkchkIdx_of_split (fn := Data.core311) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_312 : kvkchkIdx 312 = true := by
  have hb : blockB (kvklookJ 312) (kvkomLookJ 312) false [(.n 347, 0), (.n 348, 13), (.n 395, 56), (.n 583, 0), (.n 584, 5), (.n 638, 45), (.n 826, 0), (.n 827, 3), (.n 879, 28), (.n 1067, 0), (.n 1068, 3), (.n 1120, 21), (.n 1206, 0), (.n 1207, 2), (.n 1257, 16), (.n 1874, 0), (.n 1875, 14), (.n 1888, 0), (.n 1889, 5), (.n 2347, 0), (.n 2348, 3), (.n 2621, 0), (.n 2622, 2), (.n 2840, 0), (.n 2841, 2)] Data.core312.params Data.core312.name ([], []) Data.core312.body = some (⟨4221, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core312.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvksplit_312_0.1 rfl kvksplit_312_0.2.2,
      ← blockR_eq ((Data.core312.body.drop 0).take 1320), kvksplit_312_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvksplit_312_1320.1 rfl kvksplit_312_1320.2.2,
      ← blockR_eq ((Data.core312.body.drop 1320).take 1320), kvksplit_312_1320.2.1]
    rw [← blockR_eq (Data.core312.body.drop 2640), kvksplit_312_2640]
    rfl
  exact kvkchkIdx_of_split (fn := Data.core312) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_313 : kvkchkIdx 313 = true := by
  have hb : blockB (kvklookJ 313) (kvkomLookJ 313) false [(.n 347, 0), (.n 348, 14), (.n 395, 56), (.n 583, 0), (.n 584, 5), (.n 638, 45), (.n 826, 0), (.n 827, 4), (.n 879, 28), (.n 1067, 0), (.n 1068, 3), (.n 1120, 21), (.n 1206, 0), (.n 1207, 2), (.n 1257, 16), (.n 1921, 0), (.n 1922, 14), (.n 1935, 0), (.n 1936, 5), (.n 2424, 0), (.n 2425, 3), (.n 2722, 0), (.n 2723, 2), (.n 2971, 0), (.n 2972, 2)] Data.core313.params Data.core313.name ([], []) Data.core313.body = some (⟨4452, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core313.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvksplit_313_0.1 rfl kvksplit_313_0.2.2,
      ← blockR_eq ((Data.core313.body.drop 0).take 1320), kvksplit_313_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvksplit_313_1320.1 rfl kvksplit_313_1320.2.2,
      ← blockR_eq ((Data.core313.body.drop 1320).take 1320), kvksplit_313_1320.2.1]
    rw [← blockR_eq (Data.core313.body.drop 2640), kvksplit_313_2640]
    rfl
  exact kvkchkIdx_of_split (fn := Data.core313) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_314 : kvkchkIdx 314 = true := by
  have hb : blockB (kvklookJ 314) (kvkomLookJ 314) false [(.n 347, 0), (.n 348, 14), (.n 395, 56), (.n 583, 0), (.n 584, 6), (.n 638, 45), (.n 826, 0), (.n 827, 4), (.n 879, 28), (.n 1067, 0), (.n 1068, 3), (.n 1120, 21), (.n 1206, 0), (.n 1207, 2), (.n 1257, 16), (.n 1968, 0), (.n 1969, 14), (.n 1982, 0), (.n 1983, 5), (.n 2501, 0), (.n 2502, 3), (.n 2823, 0), (.n 2824, 2), (.n 3102, 0), (.n 3103, 2)] Data.core314.params Data.core314.name ([], []) Data.core314.body = some (⟨4684, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core314.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvksplit_314_0.1 rfl kvksplit_314_0.2.2,
      ← blockR_eq ((Data.core314.body.drop 0).take 1320), kvksplit_314_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvksplit_314_1320.1 rfl kvksplit_314_1320.2.2,
      ← blockR_eq ((Data.core314.body.drop 1320).take 1320), kvksplit_314_1320.2.1]
    rw [← blockR_eq (Data.core314.body.drop 2640), kvksplit_314_2640]
    rfl
  exact kvkchkIdx_of_split (fn := Data.core314) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_315 : kvkchkIdx 315 = true := by
  have hb : blockB (kvklookJ 315) (kvkomLookJ 315) false [(.n 347, 0), (.n 348, 14), (.n 395, 56), (.n 583, 0), (.n 584, 6), (.n 638, 45), (.n 826, 0), (.n 827, 4), (.n 879, 28), (.n 1067, 0), (.n 1068, 3), (.n 1120, 21), (.n 1308, 0), (.n 1309, 2), (.n 1359, 16), (.n 1445, 0), (.n 1446, 2), (.n 1497, 13), (.n 2228, 0), (.n 2229, 14), (.n 2242, 0), (.n 2243, 5), (.n 2791, 0), (.n 2792, 3), (.n 3137, 0), (.n 3138, 2), (.n 3446, 0), (.n 3447, 2), (.n 3460, 0), (.n 3461, 1)] Data.core315.params Data.core315.name ([], []) Data.core315.body = some (⟨5161, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core315.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvksplit_315_0.1 rfl kvksplit_315_0.2.2,
      ← blockR_eq ((Data.core315.body.drop 0).take 1111), kvksplit_315_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvksplit_315_1111.1 rfl kvksplit_315_1111.2.2,
      ← blockR_eq ((Data.core315.body.drop 1111).take 1111), kvksplit_315_1111.2.1]
    rw [blockB_dropE _ _ _ 2222 1111 3333 kvksplit_315_2222.1 rfl kvksplit_315_2222.2.2,
      ← blockR_eq ((Data.core315.body.drop 2222).take 1111), kvksplit_315_2222.2.1]
    rw [← blockR_eq (Data.core315.body.drop 3333), kvksplit_315_3333]
    rfl
  exact kvkchkIdx_of_split (fn := Data.core315) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_318 : kvkchkIdx 318 = true := by
  have hb : blockB (kvklookJ 318) (kvkomLookJ 318) false [(.n 347, 0), (.n 348, 9), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 3), (.n 879, 25), (.n 1067, 0), (.n 1068, 2), (.n 1120, 19), (.n 1206, 0), (.n 1207, 2), (.n 1259, 15), (.n 1829, 0), (.n 1830, 9), (.n 2164, 0), (.n 2165, 4), (.n 2676, 0), (.n 2677, 3), (.n 2749, 0), (.n 2750, 2), (.n 2868, 0), (.n 2869, 1)] Data.core318.params Data.core318.name ([], []) Data.core318.body = some (⟨3326, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core318.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvksplit_318_0.1 rfl kvksplit_318_0.2.2,
      ← blockR_eq ((Data.core318.body.drop 0).take 1320), kvksplit_318_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvksplit_318_1320.1 rfl kvksplit_318_1320.2.2,
      ← blockR_eq ((Data.core318.body.drop 1320).take 1320), kvksplit_318_1320.2.1]
    rw [← blockR_eq (Data.core318.body.drop 2640), kvksplit_318_2640]
    rfl
  exact kvkchkIdx_of_split (fn := Data.core318) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_319 : kvkchkIdx 319 = true := by
  have hb : blockB (kvklookJ 319) (kvkomLookJ 319) false [(.n 347, 0), (.n 348, 10), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 3), (.n 879, 25), (.n 1067, 0), (.n 1068, 2), (.n 1120, 19), (.n 1206, 0), (.n 1207, 2), (.n 1259, 15), (.n 1876, 0), (.n 1877, 9), (.n 2229, 0), (.n 2230, 4), (.n 2777, 0), (.n 2778, 3), (.n 2856, 0), (.n 2857, 2), (.n 2993, 0), (.n 2994, 1)] Data.core319.params Data.core319.name ([], []) Data.core319.body = some (⟨3505, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core319.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvksplit_319_0.1 rfl kvksplit_319_0.2.2,
      ← blockR_eq ((Data.core319.body.drop 0).take 1320), kvksplit_319_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvksplit_319_1320.1 rfl kvksplit_319_1320.2.2,
      ← blockR_eq ((Data.core319.body.drop 1320).take 1320), kvksplit_319_1320.2.1]
    rw [← blockR_eq (Data.core319.body.drop 2640), kvksplit_319_2640]
    rfl
  exact kvkchkIdx_of_split (fn := Data.core319) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_320 : kvkchkIdx 320 = true := by
  have hb : blockB (kvklookJ 320) (kvkomLookJ 320) false [(.n 347, 0), (.n 348, 10), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 3), (.n 879, 25), (.n 1067, 0), (.n 1068, 3), (.n 1120, 19), (.n 1206, 0), (.n 1207, 2), (.n 1259, 15), (.n 1923, 0), (.n 1924, 9), (.n 2294, 0), (.n 2295, 4), (.n 2878, 0), (.n 2879, 3), (.n 2963, 0), (.n 2964, 2), (.n 3118, 0), (.n 3119, 1)] Data.core320.params Data.core320.name ([], []) Data.core320.body = some (⟨3685, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core320.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvksplit_320_0.1 rfl kvksplit_320_0.2.2,
      ← blockR_eq ((Data.core320.body.drop 0).take 1320), kvksplit_320_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvksplit_320_1320.1 rfl kvksplit_320_1320.2.2,
      ← blockR_eq ((Data.core320.body.drop 1320).take 1320), kvksplit_320_1320.2.1]
    rw [← blockR_eq (Data.core320.body.drop 2640), kvksplit_320_2640]
    rfl
  exact kvkchkIdx_of_split (fn := Data.core320) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_321 : kvkchkIdx 321 = true := by
  have hb : blockB (kvklookJ 321) (kvkomLookJ 321) false [(.n 347, 0), (.n 348, 10), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 4), (.n 879, 25), (.n 1067, 0), (.n 1068, 3), (.n 1120, 19), (.n 1206, 0), (.n 1207, 2), (.n 1259, 15), (.n 1970, 0), (.n 1971, 9), (.n 2359, 0), (.n 2360, 4), (.n 2979, 0), (.n 2980, 3), (.n 3070, 0), (.n 3071, 2), (.n 3243, 0), (.n 3244, 1)] Data.core321.params Data.core321.name ([], []) Data.core321.body = some (⟨3867, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core321.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvksplit_321_0.1 rfl kvksplit_321_0.2.2,
      ← blockR_eq ((Data.core321.body.drop 0).take 1320), kvksplit_321_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvksplit_321_1320.1 rfl kvksplit_321_1320.2.2,
      ← blockR_eq ((Data.core321.body.drop 1320).take 1320), kvksplit_321_1320.2.1]
    rw [← blockR_eq (Data.core321.body.drop 2640), kvksplit_321_2640]
    rfl
  exact kvkchkIdx_of_split (fn := Data.core321) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_322 : kvkchkIdx 322 = true := by
  have hb : blockB (kvklookJ 322) (kvkomLookJ 322) false [(.n 347, 0), (.n 348, 11), (.n 396, 37), (.n 584, 0), (.n 585, 5), (.n 638, 38), (.n 826, 0), (.n 827, 4), (.n 879, 25), (.n 1067, 0), (.n 1068, 3), (.n 1120, 19), (.n 1308, 0), (.n 1309, 2), (.n 1361, 15), (.n 1447, 0), (.n 1448, 2), (.n 1499, 13), (.n 2230, 0), (.n 2231, 9), (.n 2637, 0), (.n 2638, 4), (.n 3293, 0), (.n 3294, 3), (.n 3390, 0), (.n 3391, 2), (.n 3581, 0), (.n 3582, 1), (.n 3840, 0), (.n 3841, 1)] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨4308, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvksplit_322_0.1 rfl kvksplit_322_0.2.2,
      ← blockR_eq ((Data.core322.body.drop 0).take 1111), kvksplit_322_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvksplit_322_1111.1 rfl kvksplit_322_1111.2.2,
      ← blockR_eq ((Data.core322.body.drop 1111).take 1111), kvksplit_322_1111.2.1]
    rw [blockB_dropE _ _ _ 2222 1111 3333 kvksplit_322_2222.1 rfl kvksplit_322_2222.2.2,
      ← blockR_eq ((Data.core322.body.drop 2222).take 1111), kvksplit_322_2222.2.1]
    rw [← blockR_eq (Data.core322.body.drop 3333), kvksplit_322_3333]
    rfl
  exact kvkchkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_325 : kvkchkIdx 325 = true := by
  have hb : blockB (kvklookJ 325) (kvkomLookJ 325) false [(.n 347, 0), (.n 348, 7), (.n 394, 28), (.n 582, 0), (.n 583, 4), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 2), (.n 1116, 18), (.n 1202, 0), (.n 1203, 2), (.n 1254, 14), (.n 1824, 0), (.n 1825, 7), (.n 1838, 0), (.n 1839, 4), (.n 1852, 0), (.n 1853, 2), (.n 2279, 0), (.n 2280, 2), (.n 2363, 0), (.n 2364, 1)] Data.core325.params Data.core325.name ([], []) Data.core325.body = some (⟨2948, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core325.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvksplit_325_0.1 rfl kvksplit_325_0.2.2,
      ← blockR_eq ((Data.core325.body.drop 0).take 1320), kvksplit_325_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvksplit_325_1320.1 rfl kvksplit_325_1320.2.2,
      ← blockR_eq ((Data.core325.body.drop 1320).take 1320), kvksplit_325_1320.2.1]
    rw [← blockR_eq (Data.core325.body.drop 2640), kvksplit_325_2640]
    rfl
  exact kvkchkIdx_of_split (fn := Data.core325) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_326 : kvkchkIdx 326 = true := by
  have hb : blockB (kvklookJ 326) (kvkomLookJ 326) false [(.n 347, 0), (.n 348, 7), (.n 394, 28), (.n 582, 0), (.n 583, 4), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 2), (.n 1116, 18), (.n 1202, 0), (.n 1203, 2), (.n 1254, 14), (.n 1871, 0), (.n 1872, 7), (.n 1885, 0), (.n 1886, 4), (.n 1899, 0), (.n 1900, 2), (.n 2368, 0), (.n 2369, 2), (.n 2464, 0), (.n 2465, 1)] Data.core326.params Data.core326.name ([], []) Data.core326.body = some (⟨3097, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core326.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvksplit_326_0.1 rfl kvksplit_326_0.2.2,
      ← blockR_eq ((Data.core326.body.drop 0).take 1320), kvksplit_326_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvksplit_326_1320.1 rfl kvksplit_326_1320.2.2,
      ← blockR_eq ((Data.core326.body.drop 1320).take 1320), kvksplit_326_1320.2.1]
    rw [← blockR_eq (Data.core326.body.drop 2640), kvksplit_326_2640]
    rfl
  exact kvkchkIdx_of_split (fn := Data.core326) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_327 : kvkchkIdx 327 = true := by
  have hb : blockB (kvklookJ 327) (kvkomLookJ 327) false [(.n 347, 0), (.n 348, 7), (.n 394, 28), (.n 582, 0), (.n 583, 4), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 2), (.n 1116, 18), (.n 1202, 0), (.n 1203, 2), (.n 1254, 14), (.n 1918, 0), (.n 1919, 7), (.n 1932, 0), (.n 1933, 4), (.n 1946, 0), (.n 1947, 2), (.n 2457, 0), (.n 2458, 2), (.n 2565, 0), (.n 2566, 1)] Data.core327.params Data.core327.name ([], []) Data.core327.body = some (⟨3247, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core327.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvksplit_327_0.1 rfl kvksplit_327_0.2.2,
      ← blockR_eq ((Data.core327.body.drop 0).take 1320), kvksplit_327_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvksplit_327_1320.1 rfl kvksplit_327_1320.2.2,
      ← blockR_eq ((Data.core327.body.drop 1320).take 1320), kvksplit_327_1320.2.1]
    rw [← blockR_eq (Data.core327.body.drop 2640), kvksplit_327_2640]
    rfl
  exact kvkchkIdx_of_split (fn := Data.core327) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_328 : kvkchkIdx 328 = true := by
  have hb : blockB (kvklookJ 328) (kvkomLookJ 328) false [(.n 347, 0), (.n 348, 8), (.n 394, 28), (.n 582, 0), (.n 583, 4), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 3), (.n 1116, 18), (.n 1202, 0), (.n 1203, 2), (.n 1255, 15), (.n 1966, 0), (.n 1967, 7), (.n 1980, 0), (.n 1981, 4), (.n 1994, 0), (.n 1995, 2), (.n 2547, 0), (.n 2548, 2), (.n 2667, 0), (.n 2668, 1)] Data.core328.params Data.core328.name ([], []) Data.core328.body = some (⟨3421, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core328.body)]
    rw [blockB_dropE _ _ _ 0 1320 1320 kvksplit_328_0.1 rfl kvksplit_328_0.2.2,
      ← blockR_eq ((Data.core328.body.drop 0).take 1320), kvksplit_328_0.2.1]
    rw [blockB_dropE _ _ _ 1320 1320 2640 kvksplit_328_1320.1 rfl kvksplit_328_1320.2.2,
      ← blockR_eq ((Data.core328.body.drop 1320).take 1320), kvksplit_328_1320.2.1]
    rw [← blockR_eq (Data.core328.body.drop 2640), kvksplit_328_2640]
    rfl
  exact kvkchkIdx_of_split (fn := Data.core328) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_329 : kvkchkIdx 329 = true := by
  have hb : blockB (kvklookJ 329) (kvkomLookJ 329) false [(.n 347, 0), (.n 348, 8), (.n 394, 28), (.n 582, 0), (.n 583, 5), (.n 634, 32), (.n 822, 0), (.n 823, 3), (.n 876, 23), (.n 1064, 0), (.n 1065, 3), (.n 1116, 18), (.n 1304, 0), (.n 1305, 2), (.n 1357, 15), (.n 1443, 0), (.n 1444, 2), (.n 1494, 12), (.n 2225, 0), (.n 2226, 7), (.n 2239, 0), (.n 2240, 4), (.n 2253, 0), (.n 2254, 2), (.n 2848, 0), (.n 2849, 2), (.n 2980, 0), (.n 2981, 1), (.n 3239, 0), (.n 3240, 1)] Data.core329.params Data.core329.name ([], []) Data.core329.body = some (⟨3827, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core329.body)]
    rw [blockB_dropE _ _ _ 0 1111 1111 kvksplit_329_0.1 rfl kvksplit_329_0.2.2,
      ← blockR_eq ((Data.core329.body.drop 0).take 1111), kvksplit_329_0.2.1]
    rw [blockB_dropE _ _ _ 1111 1111 2222 kvksplit_329_1111.1 rfl kvksplit_329_1111.2.2,
      ← blockR_eq ((Data.core329.body.drop 1111).take 1111), kvksplit_329_1111.2.1]
    rw [blockB_dropE _ _ _ 2222 1111 3333 kvksplit_329_2222.1 rfl kvksplit_329_2222.2.2,
      ← blockR_eq ((Data.core329.body.drop 2222).take 1111), kvksplit_329_2222.2.1]
    rw [← blockR_eq (Data.core329.body.drop 3333), kvksplit_329_3333]
    rfl
  exact kvkchkIdx_of_split (fn := Data.core329) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvkchkIdx_all : ∀ j < 991, kvkchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 306
  · subst h1000; exact kvkchkIdx_306
  by_cases h1001 : j = 307
  · subst h1001; exact kvkchkIdx_307
  by_cases h1002 : j = 308
  · subst h1002; exact kvkchkIdx_308
  by_cases h1003 : j = 311
  · subst h1003; exact kvkchkIdx_311
  by_cases h1004 : j = 312
  · subst h1004; exact kvkchkIdx_312
  by_cases h1005 : j = 313
  · subst h1005; exact kvkchkIdx_313
  by_cases h1006 : j = 314
  · subst h1006; exact kvkchkIdx_314
  by_cases h1007 : j = 315
  · subst h1007; exact kvkchkIdx_315
  by_cases h1008 : j = 318
  · subst h1008; exact kvkchkIdx_318
  by_cases h1009 : j = 319
  · subst h1009; exact kvkchkIdx_319
  by_cases h1010 : j = 320
  · subst h1010; exact kvkchkIdx_320
  by_cases h1011 : j = 321
  · subst h1011; exact kvkchkIdx_321
  by_cases h1012 : j = 322
  · subst h1012; exact kvkchkIdx_322
  by_cases h1013 : j = 325
  · subst h1013; exact kvkchkIdx_325
  by_cases h1014 : j = 326
  · subst h1014; exact kvkchkIdx_326
  by_cases h1015 : j = 327
  · subst h1015; exact kvkchkIdx_327
  by_cases h1016 : j = 328
  · subst h1016; exact kvkchkIdx_328
  by_cases h1017 : j = 329
  · subst h1017; exact kvkchkIdx_329
  by_cases h0 : j < 11
  · exact kvkstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvkstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kvkstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 78
  · exact kvkstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 108
  · exact kvkstaticRange_78.get (by omega) (by omega)
  by_cases h5 : j < 138
  · exact kvkstaticRange_108.get (by omega) (by omega)
  by_cases h6 : j < 168
  · exact kvkstaticRange_138.get (by omega) (by omega)
  by_cases h7 : j < 198
  · exact kvkstaticRange_168.get (by omega) (by omega)
  by_cases h8 : j < 228
  · exact kvkstaticRange_198.get (by omega) (by omega)
  by_cases h9 : j < 258
  · exact kvkstaticRange_228.get (by omega) (by omega)
  by_cases h10 : j < 288
  · exact kvkstaticRange_258.get (by omega) (by omega)
  by_cases h11 : j < 303
  · exact kvkstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 304
  · exact kvkstaticRange_303.get (by omega) (by omega)
  by_cases h13 : j < 305
  · exact kvkstaticRange_304.get (by omega) (by omega)
  by_cases h14 : j < 306
  · exact kvkstaticRange_305.get (by omega) (by omega)
  by_cases h15 : j < 310
  · exact kvkstaticRange_309.get (by omega) (by omega)
  by_cases h16 : j < 311
  · exact kvkstaticRange_310.get (by omega) (by omega)
  by_cases h17 : j < 317
  · exact kvkstaticRange_316.get (by omega) (by omega)
  by_cases h18 : j < 318
  · exact kvkstaticRange_317.get (by omega) (by omega)
  by_cases h19 : j < 324
  · exact kvkstaticRange_323.get (by omega) (by omega)
  by_cases h20 : j < 325
  · exact kvkstaticRange_324.get (by omega) (by omega)
  by_cases h21 : j < 351
  · exact kvkstaticRange_330.get (by omega) (by omega)
  by_cases h22 : j < 373
  · exact kvkstaticRange_351.get (by omega) (by omega)
  by_cases h23 : j < 396
  · exact kvkstaticRange_373.get (by omega) (by omega)
  by_cases h24 : j < 410
  · exact kvkstaticRange_396.get (by omega) (by omega)
  by_cases h25 : j < 440
  · exact kvkstaticRange_410.get (by omega) (by omega)
  by_cases h26 : j < 461
  · exact kvkstaticRange_440.get (by omega) (by omega)
  by_cases h27 : j < 482
  · exact kvkstaticRange_461.get (by omega) (by omega)
  by_cases h28 : j < 502
  · exact kvkstaticRange_482.get (by omega) (by omega)
  by_cases h29 : j < 520
  · exact kvkstaticRange_502.get (by omega) (by omega)
  by_cases h30 : j < 538
  · exact kvkstaticRange_520.get (by omega) (by omega)
  by_cases h31 : j < 556
  · exact kvkstaticRange_538.get (by omega) (by omega)
  by_cases h32 : j < 574
  · exact kvkstaticRange_556.get (by omega) (by omega)
  by_cases h33 : j < 592
  · exact kvkstaticRange_574.get (by omega) (by omega)
  by_cases h34 : j < 610
  · exact kvkstaticRange_592.get (by omega) (by omega)
  by_cases h35 : j < 628
  · exact kvkstaticRange_610.get (by omega) (by omega)
  by_cases h36 : j < 644
  · exact kvkstaticRange_628.get (by omega) (by omega)
  by_cases h37 : j < 661
  · exact kvkstaticRange_644.get (by omega) (by omega)
  by_cases h38 : j < 679
  · exact kvkstaticRange_661.get (by omega) (by omega)
  by_cases h39 : j < 694
  · exact kvkstaticRange_679.get (by omega) (by omega)
  by_cases h40 : j < 712
  · exact kvkstaticRange_694.get (by omega) (by omega)
  by_cases h41 : j < 730
  · exact kvkstaticRange_712.get (by omega) (by omega)
  by_cases h42 : j < 748
  · exact kvkstaticRange_730.get (by omega) (by omega)
  by_cases h43 : j < 766
  · exact kvkstaticRange_748.get (by omega) (by omega)
  by_cases h44 : j < 784
  · exact kvkstaticRange_766.get (by omega) (by omega)
  by_cases h45 : j < 804
  · exact kvkstaticRange_784.get (by omega) (by omega)
  by_cases h46 : j < 828
  · exact kvkstaticRange_804.get (by omega) (by omega)
  by_cases h47 : j < 850
  · exact kvkstaticRange_828.get (by omega) (by omega)
  by_cases h48 : j < 867
  · exact kvkstaticRange_850.get (by omega) (by omega)
  by_cases h49 : j < 883
  · exact kvkstaticRange_867.get (by omega) (by omega)
  by_cases h50 : j < 898
  · exact kvkstaticRange_883.get (by omega) (by omega)
  by_cases h51 : j < 913
  · exact kvkstaticRange_898.get (by omega) (by omega)
  by_cases h52 : j < 925
  · exact kvkstaticRange_913.get (by omega) (by omega)
  by_cases h53 : j < 936
  · exact kvkstaticRange_925.get (by omega) (by omega)
  by_cases h54 : j < 950
  · exact kvkstaticRange_936.get (by omega) (by omega)
  by_cases h55 : j < 963
  · exact kvkstaticRange_950.get (by omega) (by omega)
  by_cases h56 : j < 972
  · exact kvkstaticRange_963.get (by omega) (by omega)
  by_cases h57 : j < 981
  · exact kvkstaticRange_972.get (by omega) (by omega)
  by_cases h58 : j < 988
  · exact kvkstaticRange_981.get (by omega) (by omega)
  exact kvkstaticRange_988.get (by omega) (by omega)

end
end LeanVM.Guest
