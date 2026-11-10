/-
  LeanVM.Guest.Memory.GuestCntVM.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntVM.Part00
public import LeanVM.Guest.Memory.GuestCntVM.Part01
public import LeanVM.Guest.Memory.GuestCntVM.Part02
public import LeanVM.Guest.Memory.GuestCntVM.Part03
public import LeanVM.Guest.Memory.GuestCntVM.Part04
public import LeanVM.Guest.Memory.GuestCntVM.Part05
public import LeanVM.Guest.Memory.GuestCntVM.Part06
public import LeanVM.Guest.Memory.GuestCntVM.Part07
public import LeanVM.Guest.Memory.GuestCntVM.Part08
public import LeanVM.Guest.Memory.GuestCntVM.Part09
public import LeanVM.Guest.Memory.GuestCntVM.Part10
public import LeanVM.Guest.Memory.GuestCntVM.Part11
public import LeanVM.Guest.Memory.GuestCntVM.Part12
public import LeanVM.Guest.Memory.GuestCntVM.Part13
public import LeanVM.Guest.Memory.GuestCntVM.Part14
public import LeanVM.Guest.Memory.GuestCntVM.Part15
public import LeanVM.Guest.Memory.GuestCntVM.Part16
public import LeanVM.Guest.Memory.GuestCntVM.Part17
public import LeanVM.Guest.Memory.GuestCntVM.Part18
public import LeanVM.Guest.Memory.GuestCntVM.Part19
public import LeanVM.Guest.Memory.GuestCntVM.Part20
public import LeanVM.Guest.Memory.GuestCntVM.Part21
public import LeanVM.Guest.Memory.GuestCntVM.Part22
public import LeanVM.Guest.Memory.GuestCntVM.Part23
public import LeanVM.Guest.Memory.GuestCntVM.Part24
public import LeanVM.Guest.Memory.GuestCntVM.Part25
public import LeanVM.Guest.Memory.GuestCntVM.Part26
public import LeanVM.Guest.Memory.GuestCntVM.Part27
public import LeanVM.Guest.Memory.GuestCntVM.Part28
public import LeanVM.Guest.Memory.GuestCntVM.Part29
public import LeanVM.Guest.Memory.GuestCntVM.Part30
public import LeanVM.Guest.Memory.GuestCntVM.Part31
public import LeanVM.Guest.Memory.GuestCntVM.Part32
public import LeanVM.Guest.Memory.GuestCntVM.Part33
public import LeanVM.Guest.Memory.GuestCntVM.Part34
public import LeanVM.Guest.Memory.GuestCntVM.Part35
public import LeanVM.Guest.Memory.GuestCntVM.Part36

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmchkIdx_333 : kvmchkIdx 333 = true := by
  have hb : blockB (kvmlookJ 333) (kvmomLookJ 333) false [(.n 160, 1), (.n 161, 37), (.n 213, 108), (.n 347, 1), (.n 348, 8), (.n 405, 55), (.n 537, 1), (.n 538, 5), (.n 595, 32), (.n 723, 1), (.n 724, 3), (.n 781, 23), (.n 862, 1), (.n 863, 3), (.n 910, 20), (.n 1457, 0), (.n 1458, 27), (.n 1610, 0), (.n 1611, 6), (.n 2332, 0), (.n 2333, 4), (.n 2354, 0), (.n 2355, 2)] Data.core333.params Data.core333.name ([], []) Data.core333.body = some (⟨57953, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core333.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvmsplit_333_0.1 rfl kvmsplit_333_0.2.2,
      ← blockR_eq ((Data.core333.body.drop 0).take 1428), kvmsplit_333_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvmsplit_333_1428.1 rfl kvmsplit_333_1428.2.2,
      ← blockR_eq ((Data.core333.body.drop 1428).take 1428), kvmsplit_333_1428.2.1]
    rw [← blockR_eq (Data.core333.body.drop 2856), kvmsplit_333_2856]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core333) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_334 : kvmchkIdx 334 = true := by
  have hb : blockB (kvmlookJ 334) (kvmomLookJ 334) false [(.n 160, 1), (.n 161, 37), (.n 213, 108), (.n 347, 1), (.n 348, 10), (.n 405, 55), (.n 537, 1), (.n 538, 5), (.n 595, 32), (.n 723, 1), (.n 724, 4), (.n 781, 23), (.n 862, 1), (.n 863, 3), (.n 922, 19), (.n 1510, 0), (.n 1511, 27), (.n 1669, 0), (.n 1670, 6), (.n 2433, 0), (.n 2434, 4), (.n 2455, 0), (.n 2456, 2)] Data.core334.params Data.core334.name ([], []) Data.core334.body = some (⟨59434, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core334.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvmsplit_334_0.1 rfl kvmsplit_334_0.2.2,
      ← blockR_eq ((Data.core334.body.drop 0).take 1428), kvmsplit_334_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvmsplit_334_1428.1 rfl kvmsplit_334_1428.2.2,
      ← blockR_eq ((Data.core334.body.drop 1428).take 1428), kvmsplit_334_1428.2.1]
    rw [← blockR_eq (Data.core334.body.drop 2856), kvmsplit_334_2856]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core334) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_335 : kvmchkIdx 335 = true := by
  have hb : blockB (kvmlookJ 335) (kvmomLookJ 335) false [(.n 160, 1), (.n 161, 37), (.n 213, 108), (.n 347, 1), (.n 348, 10), (.n 405, 55), (.n 537, 1), (.n 538, 6), (.n 595, 32), (.n 723, 1), (.n 724, 4), (.n 781, 22), (.n 861, 1), (.n 862, 3), (.n 945, 18), (.n 1574, 0), (.n 1575, 27), (.n 1739, 0), (.n 1740, 6), (.n 2545, 0), (.n 2546, 4), (.n 2567, 0), (.n 2568, 2)] Data.core335.params Data.core335.name ([], []) Data.core335.body = some (⟨61249, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core335.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvmsplit_335_0.1 rfl kvmsplit_335_0.2.2,
      ← blockR_eq ((Data.core335.body.drop 0).take 1428), kvmsplit_335_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvmsplit_335_1428.1 rfl kvmsplit_335_1428.2.2,
      ← blockR_eq ((Data.core335.body.drop 1428).take 1428), kvmsplit_335_1428.2.1]
    rw [← blockR_eq (Data.core335.body.drop 2856), kvmsplit_335_2856]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core335) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_336 : kvmchkIdx 336 = true := by
  have hb : blockB (kvmlookJ 336) (kvmomLookJ 336) false [(.n 160, 1), (.n 161, 44), (.n 213, 108), (.n 347, 1), (.n 348, 10), (.n 405, 55), (.n 537, 1), (.n 538, 6), (.n 595, 31), (.n 726, 1), (.n 727, 4), (.n 784, 22), (.n 864, 1), (.n 865, 3), (.n 996, 18), (.n 1666, 0), (.n 1667, 27), (.n 1837, 0), (.n 1838, 6), (.n 2685, 0), (.n 2686, 3), (.n 3365, 0), (.n 3366, 2)] Data.core336.params Data.core336.name ([], []) Data.core336.body = some (⟨62468, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core336.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvmsplit_336_0.1 rfl kvmsplit_336_0.2.2,
      ← blockR_eq ((Data.core336.body.drop 0).take 1428), kvmsplit_336_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvmsplit_336_1428.1 rfl kvmsplit_336_1428.2.2,
      ← blockR_eq ((Data.core336.body.drop 1428).take 1428), kvmsplit_336_1428.2.1]
    rw [blockB_dropE _ _ _ 2856 1428 4284 kvmsplit_336_2856.1 rfl kvmsplit_336_2856.2.2,
      ← blockR_eq ((Data.core336.body.drop 2856).take 1428), kvmsplit_336_2856.2.1]
    rw [← blockR_eq (Data.core336.body.drop 4284), kvmsplit_336_4284]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core336) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_337 : kvmchkIdx 337 = true := by
  have hb : blockB (kvmlookJ 337) (kvmomLookJ 337) false [(.n 160, 1), (.n 161, 44), (.n 213, 108), (.n 347, 1), (.n 348, 11), (.n 405, 55), (.n 537, 1), (.n 538, 6), (.n 595, 31), (.n 726, 1), (.n 727, 4), (.n 784, 22), (.n 913, 1), (.n 914, 3), (.n 971, 18), (.n 1050, 1), (.n 1051, 3), (.n 1098, 16), (.n 1827, 0), (.n 1828, 27), (.n 2004, 0), (.n 2005, 6), (.n 2894, 0), (.n 2895, 3), (.n 3616, 0), (.n 3617, 2), (.n 4094, 0), (.n 4095, 2)] Data.core337.params Data.core337.name ([], []) Data.core337.body = some (⟨64011, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core337.body)]
    rw [blockB_dropE _ _ _ 0 1186 1186 kvmsplit_337_0.1 rfl kvmsplit_337_0.2.2,
      ← blockR_eq ((Data.core337.body.drop 0).take 1186), kvmsplit_337_0.2.1]
    rw [blockB_dropE _ _ _ 1186 1186 2372 kvmsplit_337_1186.1 rfl kvmsplit_337_1186.2.2,
      ← blockR_eq ((Data.core337.body.drop 1186).take 1186), kvmsplit_337_1186.2.1]
    rw [blockB_dropE _ _ _ 2372 1186 3558 kvmsplit_337_2372.1 rfl kvmsplit_337_2372.2.2,
      ← blockR_eq ((Data.core337.body.drop 2372).take 1186), kvmsplit_337_2372.2.1]
    rw [blockB_dropE _ _ _ 3558 1186 4744 kvmsplit_337_3558.1 rfl kvmsplit_337_3558.2.2,
      ← blockR_eq ((Data.core337.body.drop 3558).take 1186), kvmsplit_337_3558.2.1]
    rw [← blockR_eq (Data.core337.body.drop 4744), kvmsplit_337_4744]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core337) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_340 : kvmchkIdx 340 = true := by
  have hb : blockB (kvmlookJ 340) (kvmomLookJ 340) false [(.n 160, 1), (.n 161, 19), (.n 213, 54), (.n 346, 1), (.n 347, 8), (.n 404, 44), (.n 534, 1), (.n 535, 4), (.n 592, 28), (.n 721, 1), (.n 722, 3), (.n 779, 21), (.n 859, 1), (.n 860, 3), (.n 907, 18), (.n 1454, 0), (.n 1455, 13), (.n 2131, 0), (.n 2132, 5), (.n 2553, 0), (.n 2554, 3), (.n 2879, 0), (.n 2880, 2)] Data.core340.params Data.core340.name ([], []) Data.core340.body = some (⟨35327, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core340.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvmsplit_340_0.1 rfl kvmsplit_340_0.2.2,
      ← blockR_eq ((Data.core340.body.drop 0).take 1428), kvmsplit_340_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvmsplit_340_1428.1 rfl kvmsplit_340_1428.2.2,
      ← blockR_eq ((Data.core340.body.drop 1428).take 1428), kvmsplit_340_1428.2.1]
    rw [← blockR_eq (Data.core340.body.drop 2856), kvmsplit_340_2856]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core340) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_341 : kvmchkIdx 341 = true := by
  have hb : blockB (kvmlookJ 341) (kvmomLookJ 341) false [(.n 160, 1), (.n 161, 19), (.n 213, 54), (.n 346, 1), (.n 347, 8), (.n 404, 44), (.n 534, 1), (.n 535, 5), (.n 592, 28), (.n 721, 1), (.n 722, 3), (.n 779, 21), (.n 859, 1), (.n 860, 3), (.n 919, 17), (.n 1507, 0), (.n 1508, 13), (.n 2214, 0), (.n 2215, 5), (.n 2660, 0), (.n 2661, 3), (.n 3010, 0), (.n 3011, 2)] Data.core341.params Data.core341.name ([], []) Data.core341.body = some (⟨35849, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core341.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvmsplit_341_0.1 rfl kvmsplit_341_0.2.2,
      ← blockR_eq ((Data.core341.body.drop 0).take 1428), kvmsplit_341_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvmsplit_341_1428.1 rfl kvmsplit_341_1428.2.2,
      ← blockR_eq ((Data.core341.body.drop 1428).take 1428), kvmsplit_341_1428.2.1]
    rw [← blockR_eq (Data.core341.body.drop 2856), kvmsplit_341_2856]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core341) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_342 : kvmchkIdx 342 = true := by
  have hb : blockB (kvmlookJ 342) (kvmomLookJ 342) false [(.n 160, 1), (.n 161, 22), (.n 213, 54), (.n 346, 1), (.n 347, 8), (.n 404, 44), (.n 534, 1), (.n 535, 5), (.n 592, 28), (.n 721, 1), (.n 722, 4), (.n 779, 20), (.n 858, 1), (.n 859, 3), (.n 942, 17), (.n 1571, 0), (.n 1572, 13), (.n 2308, 0), (.n 2309, 5), (.n 2778, 0), (.n 2779, 3), (.n 3152, 0), (.n 3153, 2)] Data.core342.params Data.core342.name ([], []) Data.core342.body = some (⟨36717, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core342.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvmsplit_342_0.1 rfl kvmsplit_342_0.2.2,
      ← blockR_eq ((Data.core342.body.drop 0).take 1428), kvmsplit_342_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvmsplit_342_1428.1 rfl kvmsplit_342_1428.2.2,
      ← blockR_eq ((Data.core342.body.drop 1428).take 1428), kvmsplit_342_1428.2.1]
    rw [← blockR_eq (Data.core342.body.drop 2856), kvmsplit_342_2856]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core342) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_343 : kvmchkIdx 343 = true := by
  have hb : blockB (kvmlookJ 343) (kvmomLookJ 343) false [(.n 160, 1), (.n 161, 22), (.n 213, 54), (.n 346, 1), (.n 347, 9), (.n 404, 44), (.n 534, 1), (.n 535, 5), (.n 592, 28), (.n 721, 1), (.n 722, 4), (.n 779, 20), (.n 858, 1), (.n 859, 3), (.n 990, 17), (.n 1660, 0), (.n 1661, 13), (.n 2427, 0), (.n 2428, 5), (.n 2921, 0), (.n 2922, 3), (.n 3319, 0), (.n 3320, 2)] Data.core343.params Data.core343.name ([], []) Data.core343.body = some (⟨37304, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core343.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvmsplit_343_0.1 rfl kvmsplit_343_0.2.2,
      ← blockR_eq ((Data.core343.body.drop 0).take 1428), kvmsplit_343_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvmsplit_343_1428.1 rfl kvmsplit_343_1428.2.2,
      ← blockR_eq ((Data.core343.body.drop 1428).take 1428), kvmsplit_343_1428.2.1]
    rw [blockB_dropE _ _ _ 2856 1428 4284 kvmsplit_343_2856.1 rfl kvmsplit_343_2856.2.2,
      ← blockR_eq ((Data.core343.body.drop 2856).take 1428), kvmsplit_343_2856.2.1]
    rw [← blockR_eq (Data.core343.body.drop 4284), kvmsplit_343_4284]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core343) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_344 : kvmchkIdx 344 = true := by
  have hb : blockB (kvmlookJ 344) (kvmomLookJ 344) false [(.n 160, 1), (.n 161, 22), (.n 213, 54), (.n 346, 1), (.n 347, 9), (.n 404, 44), (.n 534, 1), (.n 535, 6), (.n 592, 28), (.n 721, 1), (.n 722, 4), (.n 779, 20), (.n 907, 1), (.n 908, 3), (.n 965, 16), (.n 1043, 1), (.n 1044, 3), (.n 1091, 15), (.n 1820, 0), (.n 1821, 13), (.n 2617, 0), (.n 2618, 5), (.n 3135, 0), (.n 3136, 3), (.n 3557, 0), (.n 3558, 2), (.n 3883, 0), (.n 3884, 2)] Data.core344.params Data.core344.name ([], []) Data.core344.body = some (⟨38818, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core344.body)]
    rw [blockB_dropE _ _ _ 0 1186 1186 kvmsplit_344_0.1 rfl kvmsplit_344_0.2.2,
      ← blockR_eq ((Data.core344.body.drop 0).take 1186), kvmsplit_344_0.2.1]
    rw [blockB_dropE _ _ _ 1186 1186 2372 kvmsplit_344_1186.1 rfl kvmsplit_344_1186.2.2,
      ← blockR_eq ((Data.core344.body.drop 1186).take 1186), kvmsplit_344_1186.2.1]
    rw [blockB_dropE _ _ _ 2372 1186 3558 kvmsplit_344_2372.1 rfl kvmsplit_344_2372.2.2,
      ← blockR_eq ((Data.core344.body.drop 2372).take 1186), kvmsplit_344_2372.2.1]
    rw [← blockR_eq (Data.core344.body.drop 3558), kvmsplit_344_3558]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core344) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_347 : kvmchkIdx 347 = true := by
  have hb : blockB (kvmlookJ 347) (kvmomLookJ 347) false [(.n 160, 1), (.n 161, 13), (.n 213, 36), (.n 344, 1), (.n 345, 7), (.n 402, 37), (.n 532, 1), (.n 533, 5), (.n 590, 25), (.n 719, 1), (.n 720, 3), (.n 777, 19), (.n 857, 1), (.n 858, 3), (.n 905, 17), (.n 1452, 0), (.n 1453, 9), (.n 1605, 0), (.n 1606, 4), (.n 2127, 0), (.n 2128, 3), (.n 2225, 0), (.n 2226, 2)] Data.core347.params Data.core347.name ([], []) Data.core347.body = some (⟨27063, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core347.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvmsplit_347_0.1 rfl kvmsplit_347_0.2.2,
      ← blockR_eq ((Data.core347.body.drop 0).take 1428), kvmsplit_347_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvmsplit_347_1428.1 rfl kvmsplit_347_1428.2.2,
      ← blockR_eq ((Data.core347.body.drop 1428).take 1428), kvmsplit_347_1428.2.1]
    rw [← blockR_eq (Data.core347.body.drop 2856), kvmsplit_347_2856]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core347) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_348 : kvmchkIdx 348 = true := by
  have hb : blockB (kvmlookJ 348) (kvmomLookJ 348) false [(.n 160, 1), (.n 161, 15), (.n 213, 36), (.n 344, 1), (.n 345, 7), (.n 402, 37), (.n 532, 1), (.n 533, 5), (.n 590, 25), (.n 719, 1), (.n 720, 4), (.n 777, 19), (.n 857, 1), (.n 858, 3), (.n 917, 16), (.n 1505, 0), (.n 1506, 9), (.n 1664, 0), (.n 1665, 4), (.n 2216, 0), (.n 2217, 3), (.n 2320, 0), (.n 2321, 2)] Data.core348.params Data.core348.name ([], []) Data.core348.body = some (⟨27700, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core348.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvmsplit_348_0.1 rfl kvmsplit_348_0.2.2,
      ← blockR_eq ((Data.core348.body.drop 0).take 1428), kvmsplit_348_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvmsplit_348_1428.1 rfl kvmsplit_348_1428.2.2,
      ← blockR_eq ((Data.core348.body.drop 1428).take 1428), kvmsplit_348_1428.2.1]
    rw [← blockR_eq (Data.core348.body.drop 2856), kvmsplit_348_2856]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core348) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_349 : kvmchkIdx 349 = true := by
  have hb : blockB (kvmlookJ 349) (kvmomLookJ 349) false [(.n 160, 1), (.n 161, 15), (.n 213, 36), (.n 344, 1), (.n 345, 8), (.n 402, 37), (.n 532, 1), (.n 533, 5), (.n 590, 25), (.n 719, 1), (.n 720, 4), (.n 777, 19), (.n 857, 1), (.n 858, 3), (.n 941, 16), (.n 1570, 0), (.n 1571, 9), (.n 1735, 0), (.n 1736, 4), (.n 2317, 0), (.n 2318, 3), (.n 2427, 0), (.n 2428, 2)] Data.core349.params Data.core349.name ([], []) Data.core349.body = some (⟨28089, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core349.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvmsplit_349_0.1 rfl kvmsplit_349_0.2.2,
      ← blockR_eq ((Data.core349.body.drop 0).take 1428), kvmsplit_349_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvmsplit_349_1428.1 rfl kvmsplit_349_1428.2.2,
      ← blockR_eq ((Data.core349.body.drop 1428).take 1428), kvmsplit_349_1428.2.1]
    rw [← blockR_eq (Data.core349.body.drop 2856), kvmsplit_349_2856]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core349) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_350 : kvmchkIdx 350 = true := by
  have hb : blockB (kvmlookJ 350) (kvmomLookJ 350) false [(.n 160, 1), (.n 161, 15), (.n 213, 36), (.n 344, 1), (.n 345, 8), (.n 402, 37), (.n 532, 1), (.n 533, 5), (.n 590, 25), (.n 719, 1), (.n 720, 4), (.n 777, 19), (.n 857, 1), (.n 858, 3), (.n 989, 15), (.n 1659, 0), (.n 1660, 9), (.n 1830, 0), (.n 1831, 4), (.n 2442, 0), (.n 2443, 3), (.n 2558, 0), (.n 2559, 2)] Data.core350.params Data.core350.name ([], []) Data.core350.body = some (⟨28535, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core350.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvmsplit_350_0.1 rfl kvmsplit_350_0.2.2,
      ← blockR_eq ((Data.core350.body.drop 0).take 1428), kvmsplit_350_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvmsplit_350_1428.1 rfl kvmsplit_350_1428.2.2,
      ← blockR_eq ((Data.core350.body.drop 1428).take 1428), kvmsplit_350_1428.2.1]
    rw [← blockR_eq (Data.core350.body.drop 2856), kvmsplit_350_2856]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core350) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_351 : kvmchkIdx 351 = true := by
  have hb : blockB (kvmlookJ 351) (kvmomLookJ 351) false [(.n 160, 1), (.n 161, 15), (.n 213, 36), (.n 344, 1), (.n 345, 8), (.n 402, 37), (.n 532, 1), (.n 533, 5), (.n 590, 25), (.n 719, 1), (.n 720, 4), (.n 777, 19), (.n 906, 1), (.n 907, 3), (.n 964, 15), (.n 1044, 1), (.n 1045, 3), (.n 1092, 14), (.n 1821, 0), (.n 1822, 9), (.n 1998, 0), (.n 1999, 4), (.n 2640, 0), (.n 2641, 3), (.n 2762, 0), (.n 2763, 2), (.n 3012, 0), (.n 3013, 1)] Data.core351.params Data.core351.name ([], []) Data.core351.body = some (⟨29752, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core351.body)]
    rw [blockB_dropE _ _ _ 0 1186 1186 kvmsplit_351_0.1 rfl kvmsplit_351_0.2.2,
      ← blockR_eq ((Data.core351.body.drop 0).take 1186), kvmsplit_351_0.2.1]
    rw [blockB_dropE _ _ _ 1186 1186 2372 kvmsplit_351_1186.1 rfl kvmsplit_351_1186.2.2,
      ← blockR_eq ((Data.core351.body.drop 1186).take 1186), kvmsplit_351_1186.2.1]
    rw [blockB_dropE _ _ _ 2372 1186 3558 kvmsplit_351_2372.1 rfl kvmsplit_351_2372.2.2,
      ← blockR_eq ((Data.core351.body.drop 2372).take 1186), kvmsplit_351_2372.2.1]
    rw [← blockR_eq (Data.core351.body.drop 3558), kvmsplit_351_3558]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core351) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_353 : kvmchkIdx 353 = true := by
  have hb : blockB (kvmlookJ 353) (kvmomLookJ 353) false [(.n 160, 1), (.n 161, 10), (.n 213, 27), (.n 345, 1), (.n 346, 6), (.n 403, 31), (.n 534, 1), (.n 535, 4), (.n 592, 22), (.n 672, 1), (.n 673, 3), (.n 804, 18), (.n 1300, 0), (.n 1301, 6), (.n 2197, 0), (.n 2198, 3), (.n 2877, 0), (.n 2878, 2)] Data.core353.params Data.core353.name ([], []) Data.core353.body = some (⟨20362, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core353.body)]
    rw [blockB_dropE _ _ _ 0 1794 1794 kvmsplit_353_0.1 rfl kvmsplit_353_0.2.2,
      ← blockR_eq ((Data.core353.body.drop 0).take 1794), kvmsplit_353_0.2.1]
    rw [blockB_dropE _ _ _ 1794 1794 3588 kvmsplit_353_1794.1 rfl kvmsplit_353_1794.2.2,
      ← blockR_eq ((Data.core353.body.drop 1794).take 1794), kvmsplit_353_1794.2.1]
    rw [← blockR_eq (Data.core353.body.drop 3588), kvmsplit_353_3588]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core353) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_354 : kvmchkIdx 354 = true := by
  have hb : blockB (kvmlookJ 354) (kvmomLookJ 354) false [(.n 160, 1), (.n 161, 11), (.n 213, 27), (.n 345, 1), (.n 346, 6), (.n 403, 31), (.n 534, 1), (.n 535, 4), (.n 592, 22), (.n 721, 1), (.n 722, 3), (.n 779, 18), (.n 858, 1), (.n 859, 3), (.n 906, 16), (.n 1453, 0), (.n 1454, 6), (.n 2392, 0), (.n 2393, 3), (.n 3114, 0), (.n 3115, 2), (.n 3592, 0), (.n 3593, 2)] Data.core354.params Data.core354.name ([], []) Data.core354.body = some (⟨21733, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core354.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvmsplit_354_0.1 rfl kvmsplit_354_0.2.2,
      ← blockR_eq ((Data.core354.body.drop 0).take 1428), kvmsplit_354_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvmsplit_354_1428.1 rfl kvmsplit_354_1428.2.2,
      ← blockR_eq ((Data.core354.body.drop 1428).take 1428), kvmsplit_354_1428.2.1]
    rw [← blockR_eq (Data.core354.body.drop 2856), kvmsplit_354_2856]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core354) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_355 : kvmchkIdx 355 = true := by
  have hb : blockB (kvmlookJ 355) (kvmomLookJ 355) false [(.n 160, 1), (.n 161, 11), (.n 213, 27), (.n 345, 1), (.n 346, 7), (.n 403, 31), (.n 534, 1), (.n 535, 4), (.n 592, 22), (.n 721, 1), (.n 722, 3), (.n 779, 17), (.n 858, 1), (.n 859, 3), (.n 918, 15), (.n 1506, 0), (.n 1507, 6), (.n 2487, 0), (.n 2488, 3), (.n 3251, 0), (.n 3252, 2), (.n 3765, 0), (.n 3766, 2)] Data.core355.params Data.core355.name ([], []) Data.core355.body = some (⟨21821, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core355.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvmsplit_355_0.1 rfl kvmsplit_355_0.2.2,
      ← blockR_eq ((Data.core355.body.drop 0).take 1428), kvmsplit_355_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvmsplit_355_1428.1 rfl kvmsplit_355_1428.2.2,
      ← blockR_eq ((Data.core355.body.drop 1428).take 1428), kvmsplit_355_1428.2.1]
    rw [blockB_dropE _ _ _ 2856 1428 4284 kvmsplit_355_2856.1 rfl kvmsplit_355_2856.2.2,
      ← blockR_eq ((Data.core355.body.drop 2856).take 1428), kvmsplit_355_2856.2.1]
    rw [← blockR_eq (Data.core355.body.drop 4284), kvmsplit_355_4284]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core355) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_356 : kvmchkIdx 356 = true := by
  have hb : blockB (kvmlookJ 356) (kvmomLookJ 356) false [(.n 160, 1), (.n 161, 11), (.n 213, 27), (.n 345, 1), (.n 346, 7), (.n 403, 31), (.n 534, 1), (.n 535, 5), (.n 592, 22), (.n 721, 1), (.n 722, 3), (.n 779, 17), (.n 858, 1), (.n 859, 3), (.n 942, 15), (.n 1571, 0), (.n 1572, 6), (.n 2594, 0), (.n 2595, 3), (.n 3400, 0), (.n 3401, 2), (.n 3950, 0), (.n 3951, 2)] Data.core356.params Data.core356.name ([], []) Data.core356.body = some (⟨22319, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core356.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvmsplit_356_0.1 rfl kvmsplit_356_0.2.2,
      ← blockR_eq ((Data.core356.body.drop 0).take 1428), kvmsplit_356_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvmsplit_356_1428.1 rfl kvmsplit_356_1428.2.2,
      ← blockR_eq ((Data.core356.body.drop 1428).take 1428), kvmsplit_356_1428.2.1]
    rw [blockB_dropE _ _ _ 2856 1428 4284 kvmsplit_356_2856.1 rfl kvmsplit_356_2856.2.2,
      ← blockR_eq ((Data.core356.body.drop 2856).take 1428), kvmsplit_356_2856.2.1]
    rw [← blockR_eq (Data.core356.body.drop 4284), kvmsplit_356_4284]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core356) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_357 : kvmchkIdx 357 = true := by
  have hb : blockB (kvmlookJ 357) (kvmomLookJ 357) false [(.n 160, 1), (.n 161, 11), (.n 213, 27), (.n 345, 1), (.n 346, 7), (.n 403, 31), (.n 534, 1), (.n 535, 5), (.n 592, 22), (.n 721, 1), (.n 722, 4), (.n 779, 17), (.n 858, 1), (.n 859, 3), (.n 990, 14), (.n 1660, 0), (.n 1661, 6), (.n 2725, 0), (.n 2726, 3), (.n 3573, 0), (.n 3574, 2), (.n 4159, 0), (.n 4160, 2)] Data.core357.params Data.core357.name ([], []) Data.core357.body = some (⟨23235, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core357.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvmsplit_357_0.1 rfl kvmsplit_357_0.2.2,
      ← blockR_eq ((Data.core357.body.drop 0).take 1428), kvmsplit_357_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvmsplit_357_1428.1 rfl kvmsplit_357_1428.2.2,
      ← blockR_eq ((Data.core357.body.drop 1428).take 1428), kvmsplit_357_1428.2.1]
    rw [blockB_dropE _ _ _ 2856 1428 4284 kvmsplit_357_2856.1 rfl kvmsplit_357_2856.2.2,
      ← blockR_eq ((Data.core357.body.drop 2856).take 1428), kvmsplit_357_2856.2.1]
    rw [← blockR_eq (Data.core357.body.drop 4284), kvmsplit_357_4284]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core357) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_358 : kvmchkIdx 358 = true := by
  have hb : blockB (kvmlookJ 358) (kvmomLookJ 358) false [(.n 160, 1), (.n 161, 14), (.n 213, 27), (.n 345, 1), (.n 346, 7), (.n 403, 31), (.n 534, 1), (.n 535, 5), (.n 592, 22), (.n 721, 1), (.n 722, 4), (.n 779, 17), (.n 907, 1), (.n 908, 3), (.n 965, 14), (.n 1044, 1), (.n 1045, 3), (.n 1092, 13), (.n 1821, 0), (.n 1822, 6), (.n 2928, 0), (.n 2929, 3), (.n 3818, 0), (.n 3819, 2), (.n 4440, 0), (.n 4441, 2), (.n 4538, 0), (.n 4539, 1)] Data.core358.params Data.core358.name ([], []) Data.core358.body = some (⟨24645, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core358.body)]
    rw [blockB_dropE _ _ _ 0 1186 1186 kvmsplit_358_0.1 rfl kvmsplit_358_0.2.2,
      ← blockR_eq ((Data.core358.body.drop 0).take 1186), kvmsplit_358_0.2.1]
    rw [blockB_dropE _ _ _ 1186 1186 2372 kvmsplit_358_1186.1 rfl kvmsplit_358_1186.2.2,
      ← blockR_eq ((Data.core358.body.drop 1186).take 1186), kvmsplit_358_1186.2.1]
    rw [blockB_dropE _ _ _ 2372 1186 3558 kvmsplit_358_2372.1 rfl kvmsplit_358_2372.2.2,
      ← blockR_eq ((Data.core358.body.drop 2372).take 1186), kvmsplit_358_2372.2.1]
    rw [blockB_dropE _ _ _ 3558 1186 4744 kvmsplit_358_3558.1 rfl kvmsplit_358_3558.2.2,
      ← blockR_eq ((Data.core358.body.drop 3558).take 1186), kvmsplit_358_3558.2.1]
    rw [← blockR_eq (Data.core358.body.drop 4744), kvmsplit_358_4744]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core358) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvmchkIdx_all : ∀ j < 1055, kvmchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 333
  · subst h1000; exact kvmchkIdx_333
  by_cases h1001 : j = 334
  · subst h1001; exact kvmchkIdx_334
  by_cases h1002 : j = 335
  · subst h1002; exact kvmchkIdx_335
  by_cases h1003 : j = 336
  · subst h1003; exact kvmchkIdx_336
  by_cases h1004 : j = 337
  · subst h1004; exact kvmchkIdx_337
  by_cases h1005 : j = 340
  · subst h1005; exact kvmchkIdx_340
  by_cases h1006 : j = 341
  · subst h1006; exact kvmchkIdx_341
  by_cases h1007 : j = 342
  · subst h1007; exact kvmchkIdx_342
  by_cases h1008 : j = 343
  · subst h1008; exact kvmchkIdx_343
  by_cases h1009 : j = 344
  · subst h1009; exact kvmchkIdx_344
  by_cases h1010 : j = 347
  · subst h1010; exact kvmchkIdx_347
  by_cases h1011 : j = 348
  · subst h1011; exact kvmchkIdx_348
  by_cases h1012 : j = 349
  · subst h1012; exact kvmchkIdx_349
  by_cases h1013 : j = 350
  · subst h1013; exact kvmchkIdx_350
  by_cases h1014 : j = 351
  · subst h1014; exact kvmchkIdx_351
  by_cases h1015 : j = 353
  · subst h1015; exact kvmchkIdx_353
  by_cases h1016 : j = 354
  · subst h1016; exact kvmchkIdx_354
  by_cases h1017 : j = 355
  · subst h1017; exact kvmchkIdx_355
  by_cases h1018 : j = 356
  · subst h1018; exact kvmchkIdx_356
  by_cases h1019 : j = 357
  · subst h1019; exact kvmchkIdx_357
  by_cases h1020 : j = 358
  · subst h1020; exact kvmchkIdx_358
  by_cases h0 : j < 11
  · exact kvmstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvmstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kvmstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 78
  · exact kvmstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 108
  · exact kvmstaticRange_78.get (by omega) (by omega)
  by_cases h5 : j < 138
  · exact kvmstaticRange_108.get (by omega) (by omega)
  by_cases h6 : j < 168
  · exact kvmstaticRange_138.get (by omega) (by omega)
  by_cases h7 : j < 198
  · exact kvmstaticRange_168.get (by omega) (by omega)
  by_cases h8 : j < 228
  · exact kvmstaticRange_198.get (by omega) (by omega)
  by_cases h9 : j < 258
  · exact kvmstaticRange_228.get (by omega) (by omega)
  by_cases h10 : j < 288
  · exact kvmstaticRange_258.get (by omega) (by omega)
  by_cases h11 : j < 318
  · exact kvmstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 332
  · exact kvmstaticRange_318.get (by omega) (by omega)
  by_cases h13 : j < 333
  · exact kvmstaticRange_332.get (by omega) (by omega)
  by_cases h14 : j < 339
  · exact kvmstaticRange_338.get (by omega) (by omega)
  by_cases h15 : j < 340
  · exact kvmstaticRange_339.get (by omega) (by omega)
  by_cases h16 : j < 346
  · exact kvmstaticRange_345.get (by omega) (by omega)
  by_cases h17 : j < 347
  · exact kvmstaticRange_346.get (by omega) (by omega)
  by_cases h18 : j < 353
  · exact kvmstaticRange_352.get (by omega) (by omega)
  by_cases h19 : j < 380
  · exact kvmstaticRange_359.get (by omega) (by omega)
  by_cases h20 : j < 402
  · exact kvmstaticRange_380.get (by omega) (by omega)
  by_cases h21 : j < 425
  · exact kvmstaticRange_402.get (by omega) (by omega)
  by_cases h22 : j < 439
  · exact kvmstaticRange_425.get (by omega) (by omega)
  by_cases h23 : j < 469
  · exact kvmstaticRange_439.get (by omega) (by omega)
  by_cases h24 : j < 497
  · exact kvmstaticRange_469.get (by omega) (by omega)
  by_cases h25 : j < 518
  · exact kvmstaticRange_497.get (by omega) (by omega)
  by_cases h26 : j < 539
  · exact kvmstaticRange_518.get (by omega) (by omega)
  by_cases h27 : j < 560
  · exact kvmstaticRange_539.get (by omega) (by omega)
  by_cases h28 : j < 581
  · exact kvmstaticRange_560.get (by omega) (by omega)
  by_cases h29 : j < 600
  · exact kvmstaticRange_581.get (by omega) (by omega)
  by_cases h30 : j < 618
  · exact kvmstaticRange_600.get (by omega) (by omega)
  by_cases h31 : j < 636
  · exact kvmstaticRange_618.get (by omega) (by omega)
  by_cases h32 : j < 653
  · exact kvmstaticRange_636.get (by omega) (by omega)
  by_cases h33 : j < 670
  · exact kvmstaticRange_653.get (by omega) (by omega)
  by_cases h34 : j < 688
  · exact kvmstaticRange_670.get (by omega) (by omega)
  by_cases h35 : j < 702
  · exact kvmstaticRange_688.get (by omega) (by omega)
  by_cases h36 : j < 721
  · exact kvmstaticRange_702.get (by omega) (by omega)
  by_cases h37 : j < 738
  · exact kvmstaticRange_721.get (by omega) (by omega)
  by_cases h38 : j < 755
  · exact kvmstaticRange_738.get (by omega) (by omega)
  by_cases h39 : j < 769
  · exact kvmstaticRange_755.get (by omega) (by omega)
  by_cases h40 : j < 786
  · exact kvmstaticRange_769.get (by omega) (by omega)
  by_cases h41 : j < 804
  · exact kvmstaticRange_786.get (by omega) (by omega)
  by_cases h42 : j < 821
  · exact kvmstaticRange_804.get (by omega) (by omega)
  by_cases h43 : j < 838
  · exact kvmstaticRange_821.get (by omega) (by omega)
  by_cases h44 : j < 854
  · exact kvmstaticRange_838.get (by omega) (by omega)
  by_cases h45 : j < 872
  · exact kvmstaticRange_854.get (by omega) (by omega)
  by_cases h46 : j < 891
  · exact kvmstaticRange_872.get (by omega) (by omega)
  by_cases h47 : j < 915
  · exact kvmstaticRange_891.get (by omega) (by omega)
  by_cases h48 : j < 939
  · exact kvmstaticRange_915.get (by omega) (by omega)
  by_cases h49 : j < 954
  · exact kvmstaticRange_939.get (by omega) (by omega)
  by_cases h50 : j < 968
  · exact kvmstaticRange_954.get (by omega) (by omega)
  by_cases h51 : j < 980
  · exact kvmstaticRange_968.get (by omega) (by omega)
  by_cases h52 : j < 991
  · exact kvmstaticRange_980.get (by omega) (by omega)
  by_cases h53 : j < 1005
  · exact kvmstaticRange_991.get (by omega) (by omega)
  by_cases h54 : j < 1018
  · exact kvmstaticRange_1005.get (by omega) (by omega)
  by_cases h55 : j < 1028
  · exact kvmstaticRange_1018.get (by omega) (by omega)
  by_cases h56 : j < 1040
  · exact kvmstaticRange_1028.get (by omega) (by omega)
  by_cases h57 : j < 1048
  · exact kvmstaticRange_1040.get (by omega) (by omega)
  exact kvmstaticRange_1048.get (by omega) (by omega)

end
end LeanVM.Guest
