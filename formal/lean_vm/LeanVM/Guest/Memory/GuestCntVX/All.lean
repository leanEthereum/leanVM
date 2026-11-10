/-
  LeanVM.Guest.Memory.GuestCntVX.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntVX.Part00
public import LeanVM.Guest.Memory.GuestCntVX.Part01
public import LeanVM.Guest.Memory.GuestCntVX.Part02
public import LeanVM.Guest.Memory.GuestCntVX.Part03
public import LeanVM.Guest.Memory.GuestCntVX.Part04
public import LeanVM.Guest.Memory.GuestCntVX.Part05
public import LeanVM.Guest.Memory.GuestCntVX.Part06
public import LeanVM.Guest.Memory.GuestCntVX.Part07
public import LeanVM.Guest.Memory.GuestCntVX.Part08
public import LeanVM.Guest.Memory.GuestCntVX.Part09
public import LeanVM.Guest.Memory.GuestCntVX.Part10
public import LeanVM.Guest.Memory.GuestCntVX.Part11
public import LeanVM.Guest.Memory.GuestCntVX.Part12
public import LeanVM.Guest.Memory.GuestCntVX.Part13
public import LeanVM.Guest.Memory.GuestCntVX.Part14
public import LeanVM.Guest.Memory.GuestCntVX.Part15
public import LeanVM.Guest.Memory.GuestCntVX.Part16
public import LeanVM.Guest.Memory.GuestCntVX.Part17
public import LeanVM.Guest.Memory.GuestCntVX.Part18
public import LeanVM.Guest.Memory.GuestCntVX.Part19
public import LeanVM.Guest.Memory.GuestCntVX.Part20
public import LeanVM.Guest.Memory.GuestCntVX.Part21
public import LeanVM.Guest.Memory.GuestCntVX.Part22
public import LeanVM.Guest.Memory.GuestCntVX.Part23
public import LeanVM.Guest.Memory.GuestCntVX.Part24
public import LeanVM.Guest.Memory.GuestCntVX.Part25
public import LeanVM.Guest.Memory.GuestCntVX.Part26
public import LeanVM.Guest.Memory.GuestCntVX.Part27
public import LeanVM.Guest.Memory.GuestCntVX.Part28
public import LeanVM.Guest.Memory.GuestCntVX.Part29
public import LeanVM.Guest.Memory.GuestCntVX.Part30
public import LeanVM.Guest.Memory.GuestCntVX.Part31
public import LeanVM.Guest.Memory.GuestCntVX.Part32
public import LeanVM.Guest.Memory.GuestCntVX.Part33
public import LeanVM.Guest.Memory.GuestCntVX.Part34
public import LeanVM.Guest.Memory.GuestCntVX.Part35
public import LeanVM.Guest.Memory.GuestCntVX.Part36

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxchkIdx_333 : kvxchkIdx 333 = true := by
  have hb : blockB (kvxlookJ 333) (kvxomLookJ 333) false [(.n 160, 1), (.n 161, 37), (.n 213, 108), (.n 347, 1), (.n 348, 8), (.n 405, 55), (.n 537, 1), (.n 538, 5), (.n 595, 32), (.n 723, 1), (.n 724, 3), (.n 781, 23), (.n 862, 1), (.n 863, 3), (.n 910, 20), (.n 1457, 0), (.n 1458, 27), (.n 1610, 0), (.n 1611, 6), (.n 2332, 0), (.n 2333, 4), (.n 2354, 0), (.n 2355, 2)] Data.core333.params Data.core333.name ([], []) Data.core333.body = some (⟨48060, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core333.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvxsplit_333_0.1 rfl kvxsplit_333_0.2.2,
      ← blockR_eq ((Data.core333.body.drop 0).take 1428), kvxsplit_333_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvxsplit_333_1428.1 rfl kvxsplit_333_1428.2.2,
      ← blockR_eq ((Data.core333.body.drop 1428).take 1428), kvxsplit_333_1428.2.1]
    rw [← blockR_eq (Data.core333.body.drop 2856), kvxsplit_333_2856]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core333) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_334 : kvxchkIdx 334 = true := by
  have hb : blockB (kvxlookJ 334) (kvxomLookJ 334) false [(.n 160, 1), (.n 161, 37), (.n 213, 108), (.n 347, 1), (.n 348, 10), (.n 405, 55), (.n 537, 1), (.n 538, 5), (.n 595, 32), (.n 723, 1), (.n 724, 4), (.n 781, 23), (.n 862, 1), (.n 863, 3), (.n 922, 19), (.n 1510, 0), (.n 1511, 27), (.n 1669, 0), (.n 1670, 6), (.n 2433, 0), (.n 2434, 4), (.n 2455, 0), (.n 2456, 2)] Data.core334.params Data.core334.name ([], []) Data.core334.body = some (⟨48888, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core334.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvxsplit_334_0.1 rfl kvxsplit_334_0.2.2,
      ← blockR_eq ((Data.core334.body.drop 0).take 1428), kvxsplit_334_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvxsplit_334_1428.1 rfl kvxsplit_334_1428.2.2,
      ← blockR_eq ((Data.core334.body.drop 1428).take 1428), kvxsplit_334_1428.2.1]
    rw [← blockR_eq (Data.core334.body.drop 2856), kvxsplit_334_2856]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core334) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_335 : kvxchkIdx 335 = true := by
  have hb : blockB (kvxlookJ 335) (kvxomLookJ 335) false [(.n 160, 1), (.n 161, 37), (.n 213, 108), (.n 347, 1), (.n 348, 10), (.n 405, 55), (.n 537, 1), (.n 538, 6), (.n 595, 32), (.n 723, 1), (.n 724, 4), (.n 781, 22), (.n 861, 1), (.n 862, 3), (.n 945, 18), (.n 1574, 0), (.n 1575, 27), (.n 1739, 0), (.n 1740, 6), (.n 2545, 0), (.n 2546, 4), (.n 2567, 0), (.n 2568, 2)] Data.core335.params Data.core335.name ([], []) Data.core335.body = some (⟨49829, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core335.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvxsplit_335_0.1 rfl kvxsplit_335_0.2.2,
      ← blockR_eq ((Data.core335.body.drop 0).take 1428), kvxsplit_335_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvxsplit_335_1428.1 rfl kvxsplit_335_1428.2.2,
      ← blockR_eq ((Data.core335.body.drop 1428).take 1428), kvxsplit_335_1428.2.1]
    rw [← blockR_eq (Data.core335.body.drop 2856), kvxsplit_335_2856]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core335) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_336 : kvxchkIdx 336 = true := by
  have hb : blockB (kvxlookJ 336) (kvxomLookJ 336) false [(.n 160, 1), (.n 161, 44), (.n 213, 108), (.n 347, 1), (.n 348, 10), (.n 405, 55), (.n 537, 1), (.n 538, 6), (.n 595, 31), (.n 726, 1), (.n 727, 4), (.n 784, 22), (.n 864, 1), (.n 865, 3), (.n 996, 18), (.n 1666, 0), (.n 1667, 27), (.n 1837, 0), (.n 1838, 6), (.n 2685, 0), (.n 2686, 3), (.n 3365, 0), (.n 3366, 2)] Data.core336.params Data.core336.name ([], []) Data.core336.body = some (⟨50590, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core336.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvxsplit_336_0.1 rfl kvxsplit_336_0.2.2,
      ← blockR_eq ((Data.core336.body.drop 0).take 1428), kvxsplit_336_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvxsplit_336_1428.1 rfl kvxsplit_336_1428.2.2,
      ← blockR_eq ((Data.core336.body.drop 1428).take 1428), kvxsplit_336_1428.2.1]
    rw [blockB_dropE _ _ _ 2856 1428 4284 kvxsplit_336_2856.1 rfl kvxsplit_336_2856.2.2,
      ← blockR_eq ((Data.core336.body.drop 2856).take 1428), kvxsplit_336_2856.2.1]
    rw [← blockR_eq (Data.core336.body.drop 4284), kvxsplit_336_4284]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core336) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_337 : kvxchkIdx 337 = true := by
  have hb : blockB (kvxlookJ 337) (kvxomLookJ 337) false [(.n 160, 1), (.n 161, 44), (.n 213, 108), (.n 347, 1), (.n 348, 11), (.n 405, 55), (.n 537, 1), (.n 538, 6), (.n 595, 31), (.n 726, 1), (.n 727, 4), (.n 784, 22), (.n 913, 1), (.n 914, 3), (.n 971, 18), (.n 1050, 1), (.n 1051, 3), (.n 1098, 16), (.n 1827, 0), (.n 1828, 27), (.n 2004, 0), (.n 2005, 6), (.n 2894, 0), (.n 2895, 3), (.n 3616, 0), (.n 3617, 2), (.n 4094, 0), (.n 4095, 2)] Data.core337.params Data.core337.name ([], []) Data.core337.body = some (⟨51536, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core337.body)]
    rw [blockB_dropE _ _ _ 0 1186 1186 kvxsplit_337_0.1 rfl kvxsplit_337_0.2.2,
      ← blockR_eq ((Data.core337.body.drop 0).take 1186), kvxsplit_337_0.2.1]
    rw [blockB_dropE _ _ _ 1186 1186 2372 kvxsplit_337_1186.1 rfl kvxsplit_337_1186.2.2,
      ← blockR_eq ((Data.core337.body.drop 1186).take 1186), kvxsplit_337_1186.2.1]
    rw [blockB_dropE _ _ _ 2372 1186 3558 kvxsplit_337_2372.1 rfl kvxsplit_337_2372.2.2,
      ← blockR_eq ((Data.core337.body.drop 2372).take 1186), kvxsplit_337_2372.2.1]
    rw [blockB_dropE _ _ _ 3558 1186 4744 kvxsplit_337_3558.1 rfl kvxsplit_337_3558.2.2,
      ← blockR_eq ((Data.core337.body.drop 3558).take 1186), kvxsplit_337_3558.2.1]
    rw [← blockR_eq (Data.core337.body.drop 4744), kvxsplit_337_4744]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core337) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_340 : kvxchkIdx 340 = true := by
  have hb : blockB (kvxlookJ 340) (kvxomLookJ 340) false [(.n 160, 1), (.n 161, 19), (.n 213, 54), (.n 346, 1), (.n 347, 8), (.n 404, 44), (.n 534, 1), (.n 535, 4), (.n 592, 28), (.n 721, 1), (.n 722, 3), (.n 779, 21), (.n 859, 1), (.n 860, 3), (.n 907, 18), (.n 1454, 0), (.n 1455, 13), (.n 2131, 0), (.n 2132, 5), (.n 2553, 0), (.n 2554, 3), (.n 2879, 0), (.n 2880, 2)] Data.core340.params Data.core340.name ([], []) Data.core340.body = some (⟨27084, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core340.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvxsplit_340_0.1 rfl kvxsplit_340_0.2.2,
      ← blockR_eq ((Data.core340.body.drop 0).take 1428), kvxsplit_340_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvxsplit_340_1428.1 rfl kvxsplit_340_1428.2.2,
      ← blockR_eq ((Data.core340.body.drop 1428).take 1428), kvxsplit_340_1428.2.1]
    rw [← blockR_eq (Data.core340.body.drop 2856), kvxsplit_340_2856]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core340) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_341 : kvxchkIdx 341 = true := by
  have hb : blockB (kvxlookJ 341) (kvxomLookJ 341) false [(.n 160, 1), (.n 161, 19), (.n 213, 54), (.n 346, 1), (.n 347, 8), (.n 404, 44), (.n 534, 1), (.n 535, 5), (.n 592, 28), (.n 721, 1), (.n 722, 3), (.n 779, 21), (.n 859, 1), (.n 860, 3), (.n 919, 17), (.n 1507, 0), (.n 1508, 13), (.n 2214, 0), (.n 2215, 5), (.n 2660, 0), (.n 2661, 3), (.n 3010, 0), (.n 3011, 2)] Data.core341.params Data.core341.name ([], []) Data.core341.body = some (⟨27520, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core341.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvxsplit_341_0.1 rfl kvxsplit_341_0.2.2,
      ← blockR_eq ((Data.core341.body.drop 0).take 1428), kvxsplit_341_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvxsplit_341_1428.1 rfl kvxsplit_341_1428.2.2,
      ← blockR_eq ((Data.core341.body.drop 1428).take 1428), kvxsplit_341_1428.2.1]
    rw [← blockR_eq (Data.core341.body.drop 2856), kvxsplit_341_2856]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core341) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_342 : kvxchkIdx 342 = true := by
  have hb : blockB (kvxlookJ 342) (kvxomLookJ 342) false [(.n 160, 1), (.n 161, 22), (.n 213, 54), (.n 346, 1), (.n 347, 8), (.n 404, 44), (.n 534, 1), (.n 535, 5), (.n 592, 28), (.n 721, 1), (.n 722, 4), (.n 779, 20), (.n 858, 1), (.n 859, 3), (.n 942, 17), (.n 1571, 0), (.n 1572, 13), (.n 2308, 0), (.n 2309, 5), (.n 2778, 0), (.n 2779, 3), (.n 3152, 0), (.n 3153, 2)] Data.core342.params Data.core342.name ([], []) Data.core342.body = some (⟨28087, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core342.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvxsplit_342_0.1 rfl kvxsplit_342_0.2.2,
      ← blockR_eq ((Data.core342.body.drop 0).take 1428), kvxsplit_342_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvxsplit_342_1428.1 rfl kvxsplit_342_1428.2.2,
      ← blockR_eq ((Data.core342.body.drop 1428).take 1428), kvxsplit_342_1428.2.1]
    rw [← blockR_eq (Data.core342.body.drop 2856), kvxsplit_342_2856]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core342) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_343 : kvxchkIdx 343 = true := by
  have hb : blockB (kvxlookJ 343) (kvxomLookJ 343) false [(.n 160, 1), (.n 161, 22), (.n 213, 54), (.n 346, 1), (.n 347, 9), (.n 404, 44), (.n 534, 1), (.n 535, 5), (.n 592, 28), (.n 721, 1), (.n 722, 4), (.n 779, 20), (.n 858, 1), (.n 859, 3), (.n 990, 17), (.n 1660, 0), (.n 1661, 13), (.n 2427, 0), (.n 2428, 5), (.n 2921, 0), (.n 2922, 3), (.n 3319, 0), (.n 3320, 2)] Data.core343.params Data.core343.name ([], []) Data.core343.body = some (⟨28731, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core343.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvxsplit_343_0.1 rfl kvxsplit_343_0.2.2,
      ← blockR_eq ((Data.core343.body.drop 0).take 1428), kvxsplit_343_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvxsplit_343_1428.1 rfl kvxsplit_343_1428.2.2,
      ← blockR_eq ((Data.core343.body.drop 1428).take 1428), kvxsplit_343_1428.2.1]
    rw [blockB_dropE _ _ _ 2856 1428 4284 kvxsplit_343_2856.1 rfl kvxsplit_343_2856.2.2,
      ← blockR_eq ((Data.core343.body.drop 2856).take 1428), kvxsplit_343_2856.2.1]
    rw [← blockR_eq (Data.core343.body.drop 4284), kvxsplit_343_4284]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core343) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_344 : kvxchkIdx 344 = true := by
  have hb : blockB (kvxlookJ 344) (kvxomLookJ 344) false [(.n 160, 1), (.n 161, 22), (.n 213, 54), (.n 346, 1), (.n 347, 9), (.n 404, 44), (.n 534, 1), (.n 535, 6), (.n 592, 28), (.n 721, 1), (.n 722, 4), (.n 779, 20), (.n 907, 1), (.n 908, 3), (.n 965, 16), (.n 1043, 1), (.n 1044, 3), (.n 1091, 15), (.n 1820, 0), (.n 1821, 13), (.n 2617, 0), (.n 2618, 5), (.n 3135, 0), (.n 3136, 3), (.n 3557, 0), (.n 3558, 2), (.n 3883, 0), (.n 3884, 2)] Data.core344.params Data.core344.name ([], []) Data.core344.body = some (⟨29443, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core344.body)]
    rw [blockB_dropE _ _ _ 0 1186 1186 kvxsplit_344_0.1 rfl kvxsplit_344_0.2.2,
      ← blockR_eq ((Data.core344.body.drop 0).take 1186), kvxsplit_344_0.2.1]
    rw [blockB_dropE _ _ _ 1186 1186 2372 kvxsplit_344_1186.1 rfl kvxsplit_344_1186.2.2,
      ← blockR_eq ((Data.core344.body.drop 1186).take 1186), kvxsplit_344_1186.2.1]
    rw [blockB_dropE _ _ _ 2372 1186 3558 kvxsplit_344_2372.1 rfl kvxsplit_344_2372.2.2,
      ← blockR_eq ((Data.core344.body.drop 2372).take 1186), kvxsplit_344_2372.2.1]
    rw [← blockR_eq (Data.core344.body.drop 3558), kvxsplit_344_3558]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core344) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_347 : kvxchkIdx 347 = true := by
  have hb : blockB (kvxlookJ 347) (kvxomLookJ 347) false [(.n 160, 1), (.n 161, 13), (.n 213, 36), (.n 344, 1), (.n 345, 7), (.n 402, 37), (.n 532, 1), (.n 533, 5), (.n 590, 25), (.n 719, 1), (.n 720, 3), (.n 777, 19), (.n 857, 1), (.n 858, 3), (.n 905, 17), (.n 1452, 0), (.n 1453, 9), (.n 1605, 0), (.n 1606, 4), (.n 2127, 0), (.n 2128, 3), (.n 2225, 0), (.n 2226, 2)] Data.core347.params Data.core347.name ([], []) Data.core347.body = some (⟨19896, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core347.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvxsplit_347_0.1 rfl kvxsplit_347_0.2.2,
      ← blockR_eq ((Data.core347.body.drop 0).take 1428), kvxsplit_347_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvxsplit_347_1428.1 rfl kvxsplit_347_1428.2.2,
      ← blockR_eq ((Data.core347.body.drop 1428).take 1428), kvxsplit_347_1428.2.1]
    rw [← blockR_eq (Data.core347.body.drop 2856), kvxsplit_347_2856]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core347) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_348 : kvxchkIdx 348 = true := by
  have hb : blockB (kvxlookJ 348) (kvxomLookJ 348) false [(.n 160, 1), (.n 161, 15), (.n 213, 36), (.n 344, 1), (.n 345, 7), (.n 402, 37), (.n 532, 1), (.n 533, 5), (.n 590, 25), (.n 719, 1), (.n 720, 4), (.n 777, 19), (.n 857, 1), (.n 858, 3), (.n 917, 16), (.n 1505, 0), (.n 1506, 9), (.n 1664, 0), (.n 1665, 4), (.n 2216, 0), (.n 2217, 3), (.n 2320, 0), (.n 2321, 2)] Data.core348.params Data.core348.name ([], []) Data.core348.body = some (⟨20287, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core348.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvxsplit_348_0.1 rfl kvxsplit_348_0.2.2,
      ← blockR_eq ((Data.core348.body.drop 0).take 1428), kvxsplit_348_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvxsplit_348_1428.1 rfl kvxsplit_348_1428.2.2,
      ← blockR_eq ((Data.core348.body.drop 1428).take 1428), kvxsplit_348_1428.2.1]
    rw [← blockR_eq (Data.core348.body.drop 2856), kvxsplit_348_2856]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core348) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_349 : kvxchkIdx 349 = true := by
  have hb : blockB (kvxlookJ 349) (kvxomLookJ 349) false [(.n 160, 1), (.n 161, 15), (.n 213, 36), (.n 344, 1), (.n 345, 8), (.n 402, 37), (.n 532, 1), (.n 533, 5), (.n 590, 25), (.n 719, 1), (.n 720, 4), (.n 777, 19), (.n 857, 1), (.n 858, 3), (.n 941, 16), (.n 1570, 0), (.n 1571, 9), (.n 1735, 0), (.n 1736, 4), (.n 2317, 0), (.n 2318, 3), (.n 2427, 0), (.n 2428, 2)] Data.core349.params Data.core349.name ([], []) Data.core349.body = some (⟨20708, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core349.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvxsplit_349_0.1 rfl kvxsplit_349_0.2.2,
      ← blockR_eq ((Data.core349.body.drop 0).take 1428), kvxsplit_349_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvxsplit_349_1428.1 rfl kvxsplit_349_1428.2.2,
      ← blockR_eq ((Data.core349.body.drop 1428).take 1428), kvxsplit_349_1428.2.1]
    rw [← blockR_eq (Data.core349.body.drop 2856), kvxsplit_349_2856]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core349) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_350 : kvxchkIdx 350 = true := by
  have hb : blockB (kvxlookJ 350) (kvxomLookJ 350) false [(.n 160, 1), (.n 161, 15), (.n 213, 36), (.n 344, 1), (.n 345, 8), (.n 402, 37), (.n 532, 1), (.n 533, 5), (.n 590, 25), (.n 719, 1), (.n 720, 4), (.n 777, 19), (.n 857, 1), (.n 858, 3), (.n 989, 15), (.n 1659, 0), (.n 1660, 9), (.n 1830, 0), (.n 1831, 4), (.n 2442, 0), (.n 2443, 3), (.n 2558, 0), (.n 2559, 2)] Data.core350.params Data.core350.name ([], []) Data.core350.body = some (⟨21180, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core350.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvxsplit_350_0.1 rfl kvxsplit_350_0.2.2,
      ← blockR_eq ((Data.core350.body.drop 0).take 1428), kvxsplit_350_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvxsplit_350_1428.1 rfl kvxsplit_350_1428.2.2,
      ← blockR_eq ((Data.core350.body.drop 1428).take 1428), kvxsplit_350_1428.2.1]
    rw [← blockR_eq (Data.core350.body.drop 2856), kvxsplit_350_2856]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core350) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_351 : kvxchkIdx 351 = true := by
  have hb : blockB (kvxlookJ 351) (kvxomLookJ 351) false [(.n 160, 1), (.n 161, 15), (.n 213, 36), (.n 344, 1), (.n 345, 8), (.n 402, 37), (.n 532, 1), (.n 533, 5), (.n 590, 25), (.n 719, 1), (.n 720, 4), (.n 777, 19), (.n 906, 1), (.n 907, 3), (.n 964, 15), (.n 1044, 1), (.n 1045, 3), (.n 1092, 14), (.n 1821, 0), (.n 1822, 9), (.n 1998, 0), (.n 1999, 4), (.n 2640, 0), (.n 2641, 3), (.n 2762, 0), (.n 2763, 2), (.n 3012, 0), (.n 3013, 1)] Data.core351.params Data.core351.name ([], []) Data.core351.body = some (⟨21720, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core351.body)]
    rw [blockB_dropE _ _ _ 0 1186 1186 kvxsplit_351_0.1 rfl kvxsplit_351_0.2.2,
      ← blockR_eq ((Data.core351.body.drop 0).take 1186), kvxsplit_351_0.2.1]
    rw [blockB_dropE _ _ _ 1186 1186 2372 kvxsplit_351_1186.1 rfl kvxsplit_351_1186.2.2,
      ← blockR_eq ((Data.core351.body.drop 1186).take 1186), kvxsplit_351_1186.2.1]
    rw [blockB_dropE _ _ _ 2372 1186 3558 kvxsplit_351_2372.1 rfl kvxsplit_351_2372.2.2,
      ← blockR_eq ((Data.core351.body.drop 2372).take 1186), kvxsplit_351_2372.2.1]
    rw [← blockR_eq (Data.core351.body.drop 3558), kvxsplit_351_3558]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core351) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_353 : kvxchkIdx 353 = true := by
  have hb : blockB (kvxlookJ 353) (kvxomLookJ 353) false [(.n 160, 1), (.n 161, 10), (.n 213, 27), (.n 345, 1), (.n 346, 6), (.n 403, 31), (.n 534, 1), (.n 535, 4), (.n 592, 22), (.n 672, 1), (.n 673, 3), (.n 804, 18), (.n 1300, 0), (.n 1301, 6), (.n 2197, 0), (.n 2198, 3), (.n 2877, 0), (.n 2878, 2)] Data.core353.params Data.core353.name ([], []) Data.core353.body = some (⟨14852, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core353.body)]
    rw [blockB_dropE _ _ _ 0 1794 1794 kvxsplit_353_0.1 rfl kvxsplit_353_0.2.2,
      ← blockR_eq ((Data.core353.body.drop 0).take 1794), kvxsplit_353_0.2.1]
    rw [blockB_dropE _ _ _ 1794 1794 3588 kvxsplit_353_1794.1 rfl kvxsplit_353_1794.2.2,
      ← blockR_eq ((Data.core353.body.drop 1794).take 1794), kvxsplit_353_1794.2.1]
    rw [← blockR_eq (Data.core353.body.drop 3588), kvxsplit_353_3588]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core353) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_354 : kvxchkIdx 354 = true := by
  have hb : blockB (kvxlookJ 354) (kvxomLookJ 354) false [(.n 160, 1), (.n 161, 11), (.n 213, 27), (.n 345, 1), (.n 346, 6), (.n 403, 31), (.n 534, 1), (.n 535, 4), (.n 592, 22), (.n 721, 1), (.n 722, 3), (.n 779, 18), (.n 858, 1), (.n 859, 3), (.n 906, 16), (.n 1453, 0), (.n 1454, 6), (.n 2392, 0), (.n 2393, 3), (.n 3114, 0), (.n 3115, 2), (.n 3592, 0), (.n 3593, 2)] Data.core354.params Data.core354.name ([], []) Data.core354.body = some (⟨15410, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core354.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvxsplit_354_0.1 rfl kvxsplit_354_0.2.2,
      ← blockR_eq ((Data.core354.body.drop 0).take 1428), kvxsplit_354_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvxsplit_354_1428.1 rfl kvxsplit_354_1428.2.2,
      ← blockR_eq ((Data.core354.body.drop 1428).take 1428), kvxsplit_354_1428.2.1]
    rw [← blockR_eq (Data.core354.body.drop 2856), kvxsplit_354_2856]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core354) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_355 : kvxchkIdx 355 = true := by
  have hb : blockB (kvxlookJ 355) (kvxomLookJ 355) false [(.n 160, 1), (.n 161, 11), (.n 213, 27), (.n 345, 1), (.n 346, 7), (.n 403, 31), (.n 534, 1), (.n 535, 4), (.n 592, 22), (.n 721, 1), (.n 722, 3), (.n 779, 17), (.n 858, 1), (.n 859, 3), (.n 918, 15), (.n 1506, 0), (.n 1507, 6), (.n 2487, 0), (.n 2488, 3), (.n 3251, 0), (.n 3252, 2), (.n 3765, 0), (.n 3766, 2)] Data.core355.params Data.core355.name ([], []) Data.core355.body = some (⟨15599, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core355.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvxsplit_355_0.1 rfl kvxsplit_355_0.2.2,
      ← blockR_eq ((Data.core355.body.drop 0).take 1428), kvxsplit_355_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvxsplit_355_1428.1 rfl kvxsplit_355_1428.2.2,
      ← blockR_eq ((Data.core355.body.drop 1428).take 1428), kvxsplit_355_1428.2.1]
    rw [blockB_dropE _ _ _ 2856 1428 4284 kvxsplit_355_2856.1 rfl kvxsplit_355_2856.2.2,
      ← blockR_eq ((Data.core355.body.drop 2856).take 1428), kvxsplit_355_2856.2.1]
    rw [← blockR_eq (Data.core355.body.drop 4284), kvxsplit_355_4284]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core355) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_356 : kvxchkIdx 356 = true := by
  have hb : blockB (kvxlookJ 356) (kvxomLookJ 356) false [(.n 160, 1), (.n 161, 11), (.n 213, 27), (.n 345, 1), (.n 346, 7), (.n 403, 31), (.n 534, 1), (.n 535, 5), (.n 592, 22), (.n 721, 1), (.n 722, 3), (.n 779, 17), (.n 858, 1), (.n 859, 3), (.n 942, 15), (.n 1571, 0), (.n 1572, 6), (.n 2594, 0), (.n 2595, 3), (.n 3400, 0), (.n 3401, 2), (.n 3950, 0), (.n 3951, 2)] Data.core356.params Data.core356.name ([], []) Data.core356.body = some (⟨15966, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core356.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvxsplit_356_0.1 rfl kvxsplit_356_0.2.2,
      ← blockR_eq ((Data.core356.body.drop 0).take 1428), kvxsplit_356_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvxsplit_356_1428.1 rfl kvxsplit_356_1428.2.2,
      ← blockR_eq ((Data.core356.body.drop 1428).take 1428), kvxsplit_356_1428.2.1]
    rw [blockB_dropE _ _ _ 2856 1428 4284 kvxsplit_356_2856.1 rfl kvxsplit_356_2856.2.2,
      ← blockR_eq ((Data.core356.body.drop 2856).take 1428), kvxsplit_356_2856.2.1]
    rw [← blockR_eq (Data.core356.body.drop 4284), kvxsplit_356_4284]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core356) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_357 : kvxchkIdx 357 = true := by
  have hb : blockB (kvxlookJ 357) (kvxomLookJ 357) false [(.n 160, 1), (.n 161, 11), (.n 213, 27), (.n 345, 1), (.n 346, 7), (.n 403, 31), (.n 534, 1), (.n 535, 5), (.n 592, 22), (.n 721, 1), (.n 722, 4), (.n 779, 17), (.n 858, 1), (.n 859, 3), (.n 990, 14), (.n 1660, 0), (.n 1661, 6), (.n 2725, 0), (.n 2726, 3), (.n 3573, 0), (.n 3574, 2), (.n 4159, 0), (.n 4160, 2)] Data.core357.params Data.core357.name ([], []) Data.core357.body = some (⟨16470, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core357.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvxsplit_357_0.1 rfl kvxsplit_357_0.2.2,
      ← blockR_eq ((Data.core357.body.drop 0).take 1428), kvxsplit_357_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvxsplit_357_1428.1 rfl kvxsplit_357_1428.2.2,
      ← blockR_eq ((Data.core357.body.drop 1428).take 1428), kvxsplit_357_1428.2.1]
    rw [blockB_dropE _ _ _ 2856 1428 4284 kvxsplit_357_2856.1 rfl kvxsplit_357_2856.2.2,
      ← blockR_eq ((Data.core357.body.drop 2856).take 1428), kvxsplit_357_2856.2.1]
    rw [← blockR_eq (Data.core357.body.drop 4284), kvxsplit_357_4284]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core357) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_358 : kvxchkIdx 358 = true := by
  have hb : blockB (kvxlookJ 358) (kvxomLookJ 358) false [(.n 160, 1), (.n 161, 14), (.n 213, 27), (.n 345, 1), (.n 346, 7), (.n 403, 31), (.n 534, 1), (.n 535, 5), (.n 592, 22), (.n 721, 1), (.n 722, 4), (.n 779, 17), (.n 907, 1), (.n 908, 3), (.n 965, 14), (.n 1044, 1), (.n 1045, 3), (.n 1092, 13), (.n 1821, 0), (.n 1822, 6), (.n 2928, 0), (.n 2929, 3), (.n 3818, 0), (.n 3819, 2), (.n 4440, 0), (.n 4441, 2), (.n 4538, 0), (.n 4539, 1)] Data.core358.params Data.core358.name ([], []) Data.core358.body = some (⟨17005, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core358.body)]
    rw [blockB_dropE _ _ _ 0 1186 1186 kvxsplit_358_0.1 rfl kvxsplit_358_0.2.2,
      ← blockR_eq ((Data.core358.body.drop 0).take 1186), kvxsplit_358_0.2.1]
    rw [blockB_dropE _ _ _ 1186 1186 2372 kvxsplit_358_1186.1 rfl kvxsplit_358_1186.2.2,
      ← blockR_eq ((Data.core358.body.drop 1186).take 1186), kvxsplit_358_1186.2.1]
    rw [blockB_dropE _ _ _ 2372 1186 3558 kvxsplit_358_2372.1 rfl kvxsplit_358_2372.2.2,
      ← blockR_eq ((Data.core358.body.drop 2372).take 1186), kvxsplit_358_2372.2.1]
    rw [blockB_dropE _ _ _ 3558 1186 4744 kvxsplit_358_3558.1 rfl kvxsplit_358_3558.2.2,
      ← blockR_eq ((Data.core358.body.drop 3558).take 1186), kvxsplit_358_3558.2.1]
    rw [← blockR_eq (Data.core358.body.drop 4744), kvxsplit_358_4744]
    rfl
  exact kvxchkIdx_of_split (fn := Data.core358) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvxchkIdx_all : ∀ j < 1055, kvxchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 333
  · subst h1000; exact kvxchkIdx_333
  by_cases h1001 : j = 334
  · subst h1001; exact kvxchkIdx_334
  by_cases h1002 : j = 335
  · subst h1002; exact kvxchkIdx_335
  by_cases h1003 : j = 336
  · subst h1003; exact kvxchkIdx_336
  by_cases h1004 : j = 337
  · subst h1004; exact kvxchkIdx_337
  by_cases h1005 : j = 340
  · subst h1005; exact kvxchkIdx_340
  by_cases h1006 : j = 341
  · subst h1006; exact kvxchkIdx_341
  by_cases h1007 : j = 342
  · subst h1007; exact kvxchkIdx_342
  by_cases h1008 : j = 343
  · subst h1008; exact kvxchkIdx_343
  by_cases h1009 : j = 344
  · subst h1009; exact kvxchkIdx_344
  by_cases h1010 : j = 347
  · subst h1010; exact kvxchkIdx_347
  by_cases h1011 : j = 348
  · subst h1011; exact kvxchkIdx_348
  by_cases h1012 : j = 349
  · subst h1012; exact kvxchkIdx_349
  by_cases h1013 : j = 350
  · subst h1013; exact kvxchkIdx_350
  by_cases h1014 : j = 351
  · subst h1014; exact kvxchkIdx_351
  by_cases h1015 : j = 353
  · subst h1015; exact kvxchkIdx_353
  by_cases h1016 : j = 354
  · subst h1016; exact kvxchkIdx_354
  by_cases h1017 : j = 355
  · subst h1017; exact kvxchkIdx_355
  by_cases h1018 : j = 356
  · subst h1018; exact kvxchkIdx_356
  by_cases h1019 : j = 357
  · subst h1019; exact kvxchkIdx_357
  by_cases h1020 : j = 358
  · subst h1020; exact kvxchkIdx_358
  by_cases h0 : j < 11
  · exact kvxstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvxstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kvxstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 78
  · exact kvxstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 108
  · exact kvxstaticRange_78.get (by omega) (by omega)
  by_cases h5 : j < 138
  · exact kvxstaticRange_108.get (by omega) (by omega)
  by_cases h6 : j < 168
  · exact kvxstaticRange_138.get (by omega) (by omega)
  by_cases h7 : j < 198
  · exact kvxstaticRange_168.get (by omega) (by omega)
  by_cases h8 : j < 228
  · exact kvxstaticRange_198.get (by omega) (by omega)
  by_cases h9 : j < 258
  · exact kvxstaticRange_228.get (by omega) (by omega)
  by_cases h10 : j < 288
  · exact kvxstaticRange_258.get (by omega) (by omega)
  by_cases h11 : j < 318
  · exact kvxstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 331
  · exact kvxstaticRange_318.get (by omega) (by omega)
  by_cases h13 : j < 332
  · exact kvxstaticRange_331.get (by omega) (by omega)
  by_cases h14 : j < 333
  · exact kvxstaticRange_332.get (by omega) (by omega)
  by_cases h15 : j < 339
  · exact kvxstaticRange_338.get (by omega) (by omega)
  by_cases h16 : j < 340
  · exact kvxstaticRange_339.get (by omega) (by omega)
  by_cases h17 : j < 346
  · exact kvxstaticRange_345.get (by omega) (by omega)
  by_cases h18 : j < 347
  · exact kvxstaticRange_346.get (by omega) (by omega)
  by_cases h19 : j < 353
  · exact kvxstaticRange_352.get (by omega) (by omega)
  by_cases h20 : j < 380
  · exact kvxstaticRange_359.get (by omega) (by omega)
  by_cases h21 : j < 402
  · exact kvxstaticRange_380.get (by omega) (by omega)
  by_cases h22 : j < 425
  · exact kvxstaticRange_402.get (by omega) (by omega)
  by_cases h23 : j < 439
  · exact kvxstaticRange_425.get (by omega) (by omega)
  by_cases h24 : j < 469
  · exact kvxstaticRange_439.get (by omega) (by omega)
  by_cases h25 : j < 492
  · exact kvxstaticRange_469.get (by omega) (by omega)
  by_cases h26 : j < 513
  · exact kvxstaticRange_492.get (by omega) (by omega)
  by_cases h27 : j < 534
  · exact kvxstaticRange_513.get (by omega) (by omega)
  by_cases h28 : j < 555
  · exact kvxstaticRange_534.get (by omega) (by omega)
  by_cases h29 : j < 576
  · exact kvxstaticRange_555.get (by omega) (by omega)
  by_cases h30 : j < 595
  · exact kvxstaticRange_576.get (by omega) (by omega)
  by_cases h31 : j < 613
  · exact kvxstaticRange_595.get (by omega) (by omega)
  by_cases h32 : j < 632
  · exact kvxstaticRange_613.get (by omega) (by omega)
  by_cases h33 : j < 649
  · exact kvxstaticRange_632.get (by omega) (by omega)
  by_cases h34 : j < 666
  · exact kvxstaticRange_649.get (by omega) (by omega)
  by_cases h35 : j < 683
  · exact kvxstaticRange_666.get (by omega) (by omega)
  by_cases h36 : j < 700
  · exact kvxstaticRange_683.get (by omega) (by omega)
  by_cases h37 : j < 718
  · exact kvxstaticRange_700.get (by omega) (by omega)
  by_cases h38 : j < 731
  · exact kvxstaticRange_718.get (by omega) (by omega)
  by_cases h39 : j < 748
  · exact kvxstaticRange_731.get (by omega) (by omega)
  by_cases h40 : j < 765
  · exact kvxstaticRange_748.get (by omega) (by omega)
  by_cases h41 : j < 779
  · exact kvxstaticRange_765.get (by omega) (by omega)
  by_cases h42 : j < 798
  · exact kvxstaticRange_779.get (by omega) (by omega)
  by_cases h43 : j < 815
  · exact kvxstaticRange_798.get (by omega) (by omega)
  by_cases h44 : j < 831
  · exact kvxstaticRange_815.get (by omega) (by omega)
  by_cases h45 : j < 848
  · exact kvxstaticRange_831.get (by omega) (by omega)
  by_cases h46 : j < 863
  · exact kvxstaticRange_848.get (by omega) (by omega)
  by_cases h47 : j < 881
  · exact kvxstaticRange_863.get (by omega) (by omega)
  by_cases h48 : j < 903
  · exact kvxstaticRange_881.get (by omega) (by omega)
  by_cases h49 : j < 927
  · exact kvxstaticRange_903.get (by omega) (by omega)
  by_cases h50 : j < 947
  · exact kvxstaticRange_927.get (by omega) (by omega)
  by_cases h51 : j < 961
  · exact kvxstaticRange_947.get (by omega) (by omega)
  by_cases h52 : j < 975
  · exact kvxstaticRange_961.get (by omega) (by omega)
  by_cases h53 : j < 987
  · exact kvxstaticRange_975.get (by omega) (by omega)
  by_cases h54 : j < 1002
  · exact kvxstaticRange_987.get (by omega) (by omega)
  by_cases h55 : j < 1015
  · exact kvxstaticRange_1002.get (by omega) (by omega)
  by_cases h56 : j < 1025
  · exact kvxstaticRange_1015.get (by omega) (by omega)
  by_cases h57 : j < 1038
  · exact kvxstaticRange_1025.get (by omega) (by omega)
  by_cases h58 : j < 1047
  · exact kvxstaticRange_1038.get (by omega) (by omega)
  by_cases h59 : j < 1054
  · exact kvxstaticRange_1047.get (by omega) (by omega)
  exact kvxstaticRange_1054.get (by omega) (by omega)

end
end LeanVM.Guest
