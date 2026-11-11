/-
  LeanVM.Guest.Memory.GuestCntVS.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntVS.Part00
public import LeanVM.Guest.Memory.GuestCntVS.Part01
public import LeanVM.Guest.Memory.GuestCntVS.Part02
public import LeanVM.Guest.Memory.GuestCntVS.Part03
public import LeanVM.Guest.Memory.GuestCntVS.Part04
public import LeanVM.Guest.Memory.GuestCntVS.Part05
public import LeanVM.Guest.Memory.GuestCntVS.Part06
public import LeanVM.Guest.Memory.GuestCntVS.Part07
public import LeanVM.Guest.Memory.GuestCntVS.Part08
public import LeanVM.Guest.Memory.GuestCntVS.Part09
public import LeanVM.Guest.Memory.GuestCntVS.Part10
public import LeanVM.Guest.Memory.GuestCntVS.Part11
public import LeanVM.Guest.Memory.GuestCntVS.Part12
public import LeanVM.Guest.Memory.GuestCntVS.Part13
public import LeanVM.Guest.Memory.GuestCntVS.Part14
public import LeanVM.Guest.Memory.GuestCntVS.Part15
public import LeanVM.Guest.Memory.GuestCntVS.Part16
public import LeanVM.Guest.Memory.GuestCntVS.Part17
public import LeanVM.Guest.Memory.GuestCntVS.Part18
public import LeanVM.Guest.Memory.GuestCntVS.Part19
public import LeanVM.Guest.Memory.GuestCntVS.Part20
public import LeanVM.Guest.Memory.GuestCntVS.Part21
public import LeanVM.Guest.Memory.GuestCntVS.Part22
public import LeanVM.Guest.Memory.GuestCntVS.Part23
public import LeanVM.Guest.Memory.GuestCntVS.Part24
public import LeanVM.Guest.Memory.GuestCntVS.Part25
public import LeanVM.Guest.Memory.GuestCntVS.Part26
public import LeanVM.Guest.Memory.GuestCntVS.Part27
public import LeanVM.Guest.Memory.GuestCntVS.Part28
public import LeanVM.Guest.Memory.GuestCntVS.Part29
public import LeanVM.Guest.Memory.GuestCntVS.Part30
public import LeanVM.Guest.Memory.GuestCntVS.Part31
public import LeanVM.Guest.Memory.GuestCntVS.Part32

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvschkIdx_333 : kvschkIdx 333 = true := by
  have hb : blockB (kvslookJ 333) (kvsomLookJ 333) false [(.n 151, 1), (.n 152, 37), (.n 196, 109), (.n 313, 1), (.n 314, 8), (.n 368, 55), (.n 483, 1), (.n 484, 5), (.n 538, 32), (.n 649, 1), (.n 650, 3), (.n 704, 23), (.n 782, 1), (.n 783, 3), (.n 830, 20), (.n 1377, 0), (.n 1378, 27), (.n 1661, 0), (.n 1662, 6), (.n 2383, 0), (.n 2384, 4), (.n 2405, 0), (.n 2406, 2)] Data.core333.params Data.core333.name ([], []) Data.core333.body = some (⟨9434, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core333.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvssplit_333_0.1 rfl kvssplit_333_0.2.2,
      ← blockR_eq ((Data.core333.body.drop 0).take 1428), kvssplit_333_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvssplit_333_1428.1 rfl kvssplit_333_1428.2.2,
      ← blockR_eq ((Data.core333.body.drop 1428).take 1428), kvssplit_333_1428.2.1]
    rw [← blockR_eq (Data.core333.body.drop 2856), kvssplit_333_2856]
    rfl
  exact kvschkIdx_of_split (fn := Data.core333) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_334 : kvschkIdx 334 = true := by
  have hb : blockB (kvslookJ 334) (kvsomLookJ 334) false [(.n 151, 1), (.n 152, 37), (.n 196, 109), (.n 313, 1), (.n 314, 10), (.n 368, 55), (.n 483, 1), (.n 484, 5), (.n 538, 32), (.n 649, 1), (.n 650, 4), (.n 704, 23), (.n 782, 1), (.n 783, 3), (.n 842, 19), (.n 1430, 0), (.n 1431, 27), (.n 1726, 0), (.n 1727, 6), (.n 2490, 0), (.n 2491, 4), (.n 2512, 0), (.n 2513, 2)] Data.core334.params Data.core334.name ([], []) Data.core334.body = some (⟨9710, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core334.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvssplit_334_0.1 rfl kvssplit_334_0.2.2,
      ← blockR_eq ((Data.core334.body.drop 0).take 1428), kvssplit_334_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvssplit_334_1428.1 rfl kvssplit_334_1428.2.2,
      ← blockR_eq ((Data.core334.body.drop 1428).take 1428), kvssplit_334_1428.2.1]
    rw [← blockR_eq (Data.core334.body.drop 2856), kvssplit_334_2856]
    rfl
  exact kvschkIdx_of_split (fn := Data.core334) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_335 : kvschkIdx 335 = true := by
  have hb : blockB (kvslookJ 335) (kvsomLookJ 335) false [(.n 151, 1), (.n 152, 37), (.n 196, 109), (.n 313, 1), (.n 314, 10), (.n 368, 55), (.n 483, 1), (.n 484, 6), (.n 538, 32), (.n 649, 1), (.n 650, 4), (.n 704, 22), (.n 781, 1), (.n 782, 3), (.n 865, 18), (.n 1494, 0), (.n 1495, 27), (.n 1802, 0), (.n 1803, 6), (.n 2608, 0), (.n 2609, 4), (.n 2630, 0), (.n 2631, 2)] Data.core335.params Data.core335.name ([], []) Data.core335.body = some (⟨9922, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core335.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvssplit_335_0.1 rfl kvssplit_335_0.2.2,
      ← blockR_eq ((Data.core335.body.drop 0).take 1428), kvssplit_335_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvssplit_335_1428.1 rfl kvssplit_335_1428.2.2,
      ← blockR_eq ((Data.core335.body.drop 1428).take 1428), kvssplit_335_1428.2.1]
    rw [← blockR_eq (Data.core335.body.drop 2856), kvssplit_335_2856]
    rfl
  exact kvschkIdx_of_split (fn := Data.core335) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_336 : kvschkIdx 336 = true := by
  have hb : blockB (kvslookJ 336) (kvsomLookJ 336) false [(.n 151, 1), (.n 152, 44), (.n 196, 109), (.n 313, 1), (.n 314, 10), (.n 368, 55), (.n 483, 1), (.n 484, 6), (.n 538, 32), (.n 649, 1), (.n 650, 4), (.n 704, 22), (.n 781, 1), (.n 782, 3), (.n 913, 18), (.n 1583, 0), (.n 1584, 27), (.n 1903, 0), (.n 1904, 6), (.n 2751, 0), (.n 2752, 4), (.n 2773, 0), (.n 2774, 2)] Data.core336.params Data.core336.name ([], []) Data.core336.body = some (⟨10260, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core336.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvssplit_336_0.1 rfl kvssplit_336_0.2.2,
      ← blockR_eq ((Data.core336.body.drop 0).take 1428), kvssplit_336_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvssplit_336_1428.1 rfl kvssplit_336_1428.2.2,
      ← blockR_eq ((Data.core336.body.drop 1428).take 1428), kvssplit_336_1428.2.1]
    rw [← blockR_eq (Data.core336.body.drop 2856), kvssplit_336_2856]
    rfl
  exact kvschkIdx_of_split (fn := Data.core336) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_337 : kvschkIdx 337 = true := by
  have hb : blockB (kvslookJ 337) (kvsomLookJ 337) false [(.n 151, 1), (.n 152, 44), (.n 196, 109), (.n 313, 1), (.n 314, 11), (.n 368, 55), (.n 483, 1), (.n 484, 6), (.n 538, 32), (.n 649, 1), (.n 650, 4), (.n 704, 22), (.n 816, 1), (.n 817, 3), (.n 871, 18), (.n 947, 1), (.n 948, 3), (.n 995, 16), (.n 1724, 0), (.n 1725, 27), (.n 2056, 0), (.n 2057, 6), (.n 2946, 0), (.n 2947, 4), (.n 2968, 0), (.n 2969, 2), (.n 3446, 0), (.n 3447, 2)] Data.core337.params Data.core337.name ([], []) Data.core337.body = some (⟨10741, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core337.body)]
    rw [blockB_dropE _ _ _ 0 1186 1186 kvssplit_337_0.1 rfl kvssplit_337_0.2.2,
      ← blockR_eq ((Data.core337.body.drop 0).take 1186), kvssplit_337_0.2.1]
    rw [blockB_dropE _ _ _ 1186 1186 2372 kvssplit_337_1186.1 rfl kvssplit_337_1186.2.2,
      ← blockR_eq ((Data.core337.body.drop 1186).take 1186), kvssplit_337_1186.2.1]
    rw [blockB_dropE _ _ _ 2372 1186 3558 kvssplit_337_2372.1 rfl kvssplit_337_2372.2.2,
      ← blockR_eq ((Data.core337.body.drop 2372).take 1186), kvssplit_337_2372.2.1]
    rw [← blockR_eq (Data.core337.body.drop 3558), kvssplit_337_3558]
    rfl
  exact kvschkIdx_of_split (fn := Data.core337) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_340 : kvschkIdx 340 = true := by
  have hb : blockB (kvslookJ 340) (kvsomLookJ 340) false [(.n 151, 1), (.n 152, 19), (.n 196, 54), (.n 312, 1), (.n 313, 8), (.n 367, 44), (.n 480, 1), (.n 481, 4), (.n 535, 28), (.n 647, 1), (.n 648, 3), (.n 702, 21), (.n 779, 1), (.n 780, 3), (.n 827, 18), (.n 1374, 0), (.n 1375, 13), (.n 2051, 0), (.n 2052, 5), (.n 2473, 0), (.n 2474, 3), (.n 2799, 0), (.n 2800, 2)] Data.core340.params Data.core340.name ([], []) Data.core340.body = some (⟨6583, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core340.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvssplit_340_0.1 rfl kvssplit_340_0.2.2,
      ← blockR_eq ((Data.core340.body.drop 0).take 1428), kvssplit_340_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvssplit_340_1428.1 rfl kvssplit_340_1428.2.2,
      ← blockR_eq ((Data.core340.body.drop 1428).take 1428), kvssplit_340_1428.2.1]
    rw [← blockR_eq (Data.core340.body.drop 2856), kvssplit_340_2856]
    rfl
  exact kvschkIdx_of_split (fn := Data.core340) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_341 : kvschkIdx 341 = true := by
  have hb : blockB (kvslookJ 341) (kvsomLookJ 341) false [(.n 151, 1), (.n 152, 19), (.n 196, 54), (.n 312, 1), (.n 313, 8), (.n 367, 44), (.n 480, 1), (.n 481, 5), (.n 535, 28), (.n 647, 1), (.n 648, 3), (.n 702, 21), (.n 779, 1), (.n 780, 3), (.n 839, 17), (.n 1427, 0), (.n 1428, 13), (.n 2134, 0), (.n 2135, 5), (.n 2580, 0), (.n 2581, 3), (.n 2930, 0), (.n 2931, 2)] Data.core341.params Data.core341.name ([], []) Data.core341.body = some (⟨6599, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core341.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvssplit_341_0.1 rfl kvssplit_341_0.2.2,
      ← blockR_eq ((Data.core341.body.drop 0).take 1428), kvssplit_341_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvssplit_341_1428.1 rfl kvssplit_341_1428.2.2,
      ← blockR_eq ((Data.core341.body.drop 1428).take 1428), kvssplit_341_1428.2.1]
    rw [← blockR_eq (Data.core341.body.drop 2856), kvssplit_341_2856]
    rfl
  exact kvschkIdx_of_split (fn := Data.core341) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_342 : kvschkIdx 342 = true := by
  have hb : blockB (kvslookJ 342) (kvsomLookJ 342) false [(.n 151, 1), (.n 152, 22), (.n 196, 54), (.n 312, 1), (.n 313, 8), (.n 367, 44), (.n 480, 1), (.n 481, 5), (.n 535, 28), (.n 647, 1), (.n 648, 4), (.n 702, 20), (.n 778, 1), (.n 779, 3), (.n 862, 17), (.n 1491, 0), (.n 1492, 13), (.n 2228, 0), (.n 2229, 5), (.n 2698, 0), (.n 2699, 3), (.n 3072, 0), (.n 3073, 2)] Data.core342.params Data.core342.name ([], []) Data.core342.body = some (⟨6757, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core342.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvssplit_342_0.1 rfl kvssplit_342_0.2.2,
      ← blockR_eq ((Data.core342.body.drop 0).take 1428), kvssplit_342_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvssplit_342_1428.1 rfl kvssplit_342_1428.2.2,
      ← blockR_eq ((Data.core342.body.drop 1428).take 1428), kvssplit_342_1428.2.1]
    rw [← blockR_eq (Data.core342.body.drop 2856), kvssplit_342_2856]
    rfl
  exact kvschkIdx_of_split (fn := Data.core342) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_343 : kvschkIdx 343 = true := by
  have hb : blockB (kvslookJ 343) (kvsomLookJ 343) false [(.n 151, 1), (.n 152, 22), (.n 196, 54), (.n 312, 1), (.n 313, 9), (.n 367, 44), (.n 480, 1), (.n 481, 5), (.n 535, 28), (.n 647, 1), (.n 648, 4), (.n 702, 20), (.n 778, 1), (.n 779, 3), (.n 910, 17), (.n 1580, 0), (.n 1581, 13), (.n 2347, 0), (.n 2348, 5), (.n 2841, 0), (.n 2842, 3), (.n 3239, 0), (.n 3240, 2)] Data.core343.params Data.core343.name ([], []) Data.core343.body = some (⟨6835, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core343.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvssplit_343_0.1 rfl kvssplit_343_0.2.2,
      ← blockR_eq ((Data.core343.body.drop 0).take 1428), kvssplit_343_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvssplit_343_1428.1 rfl kvssplit_343_1428.2.2,
      ← blockR_eq ((Data.core343.body.drop 1428).take 1428), kvssplit_343_1428.2.1]
    rw [← blockR_eq (Data.core343.body.drop 2856), kvssplit_343_2856]
    rfl
  exact kvschkIdx_of_split (fn := Data.core343) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_344 : kvschkIdx 344 = true := by
  have hb : blockB (kvslookJ 344) (kvsomLookJ 344) false [(.n 151, 1), (.n 152, 22), (.n 196, 54), (.n 312, 1), (.n 313, 9), (.n 367, 44), (.n 480, 1), (.n 481, 6), (.n 535, 28), (.n 647, 1), (.n 648, 4), (.n 702, 20), (.n 813, 1), (.n 814, 3), (.n 868, 16), (.n 943, 1), (.n 944, 3), (.n 991, 15), (.n 1720, 0), (.n 1721, 13), (.n 2517, 0), (.n 2518, 5), (.n 3035, 0), (.n 3036, 3), (.n 3457, 0), (.n 3458, 2), (.n 3783, 0), (.n 3784, 2)] Data.core344.params Data.core344.name ([], []) Data.core344.body = some (⟨7280, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core344.body)]
    rw [blockB_dropE _ _ _ 0 1186 1186 kvssplit_344_0.1 rfl kvssplit_344_0.2.2,
      ← blockR_eq ((Data.core344.body.drop 0).take 1186), kvssplit_344_0.2.1]
    rw [blockB_dropE _ _ _ 1186 1186 2372 kvssplit_344_1186.1 rfl kvssplit_344_1186.2.2,
      ← blockR_eq ((Data.core344.body.drop 1186).take 1186), kvssplit_344_1186.2.1]
    rw [blockB_dropE _ _ _ 2372 1186 3558 kvssplit_344_2372.1 rfl kvssplit_344_2372.2.2,
      ← blockR_eq ((Data.core344.body.drop 2372).take 1186), kvssplit_344_2372.2.1]
    rw [← blockR_eq (Data.core344.body.drop 3558), kvssplit_344_3558]
    rfl
  exact kvschkIdx_of_split (fn := Data.core344) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_349 : kvschkIdx 349 = true := by
  have hb : blockB (kvslookJ 349) (kvsomLookJ 349) false [(.n 151, 1), (.n 152, 15), (.n 196, 36), (.n 310, 1), (.n 311, 8), (.n 365, 37), (.n 478, 1), (.n 479, 5), (.n 533, 25), (.n 645, 1), (.n 646, 4), (.n 700, 19), (.n 777, 1), (.n 778, 3), (.n 861, 16), (.n 1490, 0), (.n 1491, 9), (.n 1655, 0), (.n 1656, 4), (.n 2237, 0), (.n 2238, 3), (.n 2347, 0), (.n 2348, 2)] Data.core349.params Data.core349.name ([], []) Data.core349.body = some (⟨5605, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core349.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvssplit_349_0.1 rfl kvssplit_349_0.2.2,
      ← blockR_eq ((Data.core349.body.drop 0).take 1428), kvssplit_349_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvssplit_349_1428.1 rfl kvssplit_349_1428.2.2,
      ← blockR_eq ((Data.core349.body.drop 1428).take 1428), kvssplit_349_1428.2.1]
    rw [← blockR_eq (Data.core349.body.drop 2856), kvssplit_349_2856]
    rfl
  exact kvschkIdx_of_split (fn := Data.core349) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_350 : kvschkIdx 350 = true := by
  have hb : blockB (kvslookJ 350) (kvsomLookJ 350) false [(.n 151, 1), (.n 152, 15), (.n 196, 36), (.n 310, 1), (.n 311, 8), (.n 365, 37), (.n 478, 1), (.n 479, 5), (.n 533, 25), (.n 645, 1), (.n 646, 4), (.n 700, 19), (.n 777, 1), (.n 778, 3), (.n 909, 16), (.n 1579, 0), (.n 1580, 9), (.n 1750, 0), (.n 1751, 4), (.n 2362, 0), (.n 2363, 3), (.n 2478, 0), (.n 2479, 2)] Data.core350.params Data.core350.name ([], []) Data.core350.body = some (⟨5673, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core350.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvssplit_350_0.1 rfl kvssplit_350_0.2.2,
      ← blockR_eq ((Data.core350.body.drop 0).take 1428), kvssplit_350_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvssplit_350_1428.1 rfl kvssplit_350_1428.2.2,
      ← blockR_eq ((Data.core350.body.drop 1428).take 1428), kvssplit_350_1428.2.1]
    rw [← blockR_eq (Data.core350.body.drop 2856), kvssplit_350_2856]
    rfl
  exact kvschkIdx_of_split (fn := Data.core350) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_351 : kvschkIdx 351 = true := by
  have hb : blockB (kvslookJ 351) (kvsomLookJ 351) false [(.n 151, 1), (.n 152, 15), (.n 196, 36), (.n 310, 1), (.n 311, 8), (.n 365, 37), (.n 478, 1), (.n 479, 5), (.n 533, 25), (.n 645, 1), (.n 646, 4), (.n 700, 19), (.n 812, 1), (.n 813, 3), (.n 867, 16), (.n 942, 1), (.n 943, 3), (.n 990, 14), (.n 1719, 0), (.n 1720, 9), (.n 1896, 0), (.n 1897, 4), (.n 2538, 0), (.n 2539, 3), (.n 2660, 0), (.n 2661, 2), (.n 2910, 0), (.n 2911, 2)] Data.core351.params Data.core351.name ([], []) Data.core351.body = some (⟨6100, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core351.body)]
    rw [blockB_dropE _ _ _ 0 1186 1186 kvssplit_351_0.1 rfl kvssplit_351_0.2.2,
      ← blockR_eq ((Data.core351.body.drop 0).take 1186), kvssplit_351_0.2.1]
    rw [blockB_dropE _ _ _ 1186 1186 2372 kvssplit_351_1186.1 rfl kvssplit_351_1186.2.2,
      ← blockR_eq ((Data.core351.body.drop 1186).take 1186), kvssplit_351_1186.2.1]
    rw [← blockR_eq (Data.core351.body.drop 2372), kvssplit_351_2372]
    rfl
  exact kvschkIdx_of_split (fn := Data.core351) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_354 : kvschkIdx 354 = true := by
  have hb : blockB (kvslookJ 354) (kvsomLookJ 354) false [(.n 151, 1), (.n 152, 11), (.n 196, 27), (.n 311, 1), (.n 312, 6), (.n 366, 32), (.n 477, 1), (.n 478, 4), (.n 532, 22), (.n 644, 1), (.n 645, 3), (.n 699, 18), (.n 775, 1), (.n 776, 3), (.n 823, 16), (.n 1370, 0), (.n 1371, 6), (.n 2309, 0), (.n 2310, 4), (.n 2331, 0), (.n 2332, 2), (.n 2809, 0), (.n 2810, 2)] Data.core354.params Data.core354.name ([], []) Data.core354.body = some (⟨4583, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core354.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvssplit_354_0.1 rfl kvssplit_354_0.2.2,
      ← blockR_eq ((Data.core354.body.drop 0).take 1428), kvssplit_354_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvssplit_354_1428.1 rfl kvssplit_354_1428.2.2,
      ← blockR_eq ((Data.core354.body.drop 1428).take 1428), kvssplit_354_1428.2.1]
    rw [← blockR_eq (Data.core354.body.drop 2856), kvssplit_354_2856]
    rfl
  exact kvschkIdx_of_split (fn := Data.core354) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_355 : kvschkIdx 355 = true := by
  have hb : blockB (kvslookJ 355) (kvsomLookJ 355) false [(.n 151, 1), (.n 152, 11), (.n 196, 27), (.n 311, 1), (.n 312, 7), (.n 366, 32), (.n 477, 1), (.n 478, 4), (.n 532, 22), (.n 644, 1), (.n 645, 3), (.n 699, 18), (.n 775, 1), (.n 776, 3), (.n 835, 15), (.n 1423, 0), (.n 1424, 6), (.n 2404, 0), (.n 2405, 4), (.n 2426, 0), (.n 2427, 2), (.n 2940, 0), (.n 2941, 2)] Data.core355.params Data.core355.name ([], []) Data.core355.body = some (⟨4616, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core355.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvssplit_355_0.1 rfl kvssplit_355_0.2.2,
      ← blockR_eq ((Data.core355.body.drop 0).take 1428), kvssplit_355_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvssplit_355_1428.1 rfl kvssplit_355_1428.2.2,
      ← blockR_eq ((Data.core355.body.drop 1428).take 1428), kvssplit_355_1428.2.1]
    rw [← blockR_eq (Data.core355.body.drop 2856), kvssplit_355_2856]
    rfl
  exact kvschkIdx_of_split (fn := Data.core355) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_356 : kvschkIdx 356 = true := by
  have hb : blockB (kvslookJ 356) (kvsomLookJ 356) false [(.n 151, 1), (.n 152, 11), (.n 196, 27), (.n 311, 1), (.n 312, 7), (.n 366, 32), (.n 477, 1), (.n 478, 5), (.n 532, 22), (.n 644, 1), (.n 645, 3), (.n 699, 18), (.n 775, 1), (.n 776, 3), (.n 859, 15), (.n 1488, 0), (.n 1489, 6), (.n 2511, 0), (.n 2512, 4), (.n 2533, 0), (.n 2534, 2), (.n 3083, 0), (.n 3084, 2)] Data.core356.params Data.core356.name ([], []) Data.core356.body = some (⟨4687, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core356.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvssplit_356_0.1 rfl kvssplit_356_0.2.2,
      ← blockR_eq ((Data.core356.body.drop 0).take 1428), kvssplit_356_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvssplit_356_1428.1 rfl kvssplit_356_1428.2.2,
      ← blockR_eq ((Data.core356.body.drop 1428).take 1428), kvssplit_356_1428.2.1]
    rw [← blockR_eq (Data.core356.body.drop 2856), kvssplit_356_2856]
    rfl
  exact kvschkIdx_of_split (fn := Data.core356) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_357 : kvschkIdx 357 = true := by
  have hb : blockB (kvslookJ 357) (kvsomLookJ 357) false [(.n 151, 1), (.n 152, 11), (.n 196, 27), (.n 311, 1), (.n 312, 7), (.n 366, 32), (.n 477, 1), (.n 478, 5), (.n 532, 22), (.n 644, 1), (.n 645, 4), (.n 699, 18), (.n 775, 1), (.n 776, 3), (.n 907, 15), (.n 1577, 0), (.n 1578, 6), (.n 2642, 0), (.n 2643, 4), (.n 2664, 0), (.n 2665, 2), (.n 3250, 0), (.n 3251, 2)] Data.core357.params Data.core357.name ([], []) Data.core357.body = some (⟨4858, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core357.body)]
    rw [blockB_dropE _ _ _ 0 1428 1428 kvssplit_357_0.1 rfl kvssplit_357_0.2.2,
      ← blockR_eq ((Data.core357.body.drop 0).take 1428), kvssplit_357_0.2.1]
    rw [blockB_dropE _ _ _ 1428 1428 2856 kvssplit_357_1428.1 rfl kvssplit_357_1428.2.2,
      ← blockR_eq ((Data.core357.body.drop 1428).take 1428), kvssplit_357_1428.2.1]
    rw [← blockR_eq (Data.core357.body.drop 2856), kvssplit_357_2856]
    rfl
  exact kvschkIdx_of_split (fn := Data.core357) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_358 : kvschkIdx 358 = true := by
  have hb : blockB (kvslookJ 358) (kvsomLookJ 358) false [(.n 151, 1), (.n 152, 14), (.n 196, 27), (.n 311, 1), (.n 312, 7), (.n 366, 32), (.n 477, 1), (.n 478, 5), (.n 532, 22), (.n 644, 1), (.n 645, 4), (.n 699, 18), (.n 810, 1), (.n 811, 3), (.n 865, 15), (.n 942, 1), (.n 943, 3), (.n 990, 13), (.n 1719, 0), (.n 1720, 6), (.n 2826, 0), (.n 2827, 4), (.n 2848, 0), (.n 2849, 2), (.n 3470, 0), (.n 3471, 2), (.n 3644, 0), (.n 3645, 1)] Data.core358.params Data.core358.name ([], []) Data.core358.body = some (⟨5374, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core358.body)]
    rw [blockB_dropE _ _ _ 0 1186 1186 kvssplit_358_0.1 rfl kvssplit_358_0.2.2,
      ← blockR_eq ((Data.core358.body.drop 0).take 1186), kvssplit_358_0.2.1]
    rw [blockB_dropE _ _ _ 1186 1186 2372 kvssplit_358_1186.1 rfl kvssplit_358_1186.2.2,
      ← blockR_eq ((Data.core358.body.drop 1186).take 1186), kvssplit_358_1186.2.1]
    rw [blockB_dropE _ _ _ 2372 1186 3558 kvssplit_358_2372.1 rfl kvssplit_358_2372.2.2,
      ← blockR_eq ((Data.core358.body.drop 2372).take 1186), kvssplit_358_2372.2.1]
    rw [← blockR_eq (Data.core358.body.drop 3558), kvssplit_358_3558]
    rfl
  exact kvschkIdx_of_split (fn := Data.core358) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvschkIdx_all : ∀ j < 1037, kvschkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 333
  · subst h1000; exact kvschkIdx_333
  by_cases h1001 : j = 334
  · subst h1001; exact kvschkIdx_334
  by_cases h1002 : j = 335
  · subst h1002; exact kvschkIdx_335
  by_cases h1003 : j = 336
  · subst h1003; exact kvschkIdx_336
  by_cases h1004 : j = 337
  · subst h1004; exact kvschkIdx_337
  by_cases h1005 : j = 340
  · subst h1005; exact kvschkIdx_340
  by_cases h1006 : j = 341
  · subst h1006; exact kvschkIdx_341
  by_cases h1007 : j = 342
  · subst h1007; exact kvschkIdx_342
  by_cases h1008 : j = 343
  · subst h1008; exact kvschkIdx_343
  by_cases h1009 : j = 344
  · subst h1009; exact kvschkIdx_344
  by_cases h1010 : j = 349
  · subst h1010; exact kvschkIdx_349
  by_cases h1011 : j = 350
  · subst h1011; exact kvschkIdx_350
  by_cases h1012 : j = 351
  · subst h1012; exact kvschkIdx_351
  by_cases h1013 : j = 354
  · subst h1013; exact kvschkIdx_354
  by_cases h1014 : j = 355
  · subst h1014; exact kvschkIdx_355
  by_cases h1015 : j = 356
  · subst h1015; exact kvschkIdx_356
  by_cases h1016 : j = 357
  · subst h1016; exact kvschkIdx_357
  by_cases h1017 : j = 358
  · subst h1017; exact kvschkIdx_358
  by_cases h0 : j < 11
  · exact kvsstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvsstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kvsstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 78
  · exact kvsstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 108
  · exact kvsstaticRange_78.get (by omega) (by omega)
  by_cases h5 : j < 138
  · exact kvsstaticRange_108.get (by omega) (by omega)
  by_cases h6 : j < 168
  · exact kvsstaticRange_138.get (by omega) (by omega)
  by_cases h7 : j < 198
  · exact kvsstaticRange_168.get (by omega) (by omega)
  by_cases h8 : j < 228
  · exact kvsstaticRange_198.get (by omega) (by omega)
  by_cases h9 : j < 258
  · exact kvsstaticRange_228.get (by omega) (by omega)
  by_cases h10 : j < 288
  · exact kvsstaticRange_258.get (by omega) (by omega)
  by_cases h11 : j < 318
  · exact kvsstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 331
  · exact kvsstaticRange_318.get (by omega) (by omega)
  by_cases h13 : j < 332
  · exact kvsstaticRange_331.get (by omega) (by omega)
  by_cases h14 : j < 333
  · exact kvsstaticRange_332.get (by omega) (by omega)
  by_cases h15 : j < 339
  · exact kvsstaticRange_338.get (by omega) (by omega)
  by_cases h16 : j < 340
  · exact kvsstaticRange_339.get (by omega) (by omega)
  by_cases h17 : j < 347
  · exact kvsstaticRange_345.get (by omega) (by omega)
  by_cases h18 : j < 348
  · exact kvsstaticRange_347.get (by omega) (by omega)
  by_cases h19 : j < 349
  · exact kvsstaticRange_348.get (by omega) (by omega)
  by_cases h20 : j < 353
  · exact kvsstaticRange_352.get (by omega) (by omega)
  by_cases h21 : j < 354
  · exact kvsstaticRange_353.get (by omega) (by omega)
  by_cases h22 : j < 380
  · exact kvsstaticRange_359.get (by omega) (by omega)
  by_cases h23 : j < 402
  · exact kvsstaticRange_380.get (by omega) (by omega)
  by_cases h24 : j < 425
  · exact kvsstaticRange_402.get (by omega) (by omega)
  by_cases h25 : j < 439
  · exact kvsstaticRange_425.get (by omega) (by omega)
  by_cases h26 : j < 469
  · exact kvsstaticRange_439.get (by omega) (by omega)
  by_cases h27 : j < 491
  · exact kvsstaticRange_469.get (by omega) (by omega)
  by_cases h28 : j < 512
  · exact kvsstaticRange_491.get (by omega) (by omega)
  by_cases h29 : j < 533
  · exact kvsstaticRange_512.get (by omega) (by omega)
  by_cases h30 : j < 554
  · exact kvsstaticRange_533.get (by omega) (by omega)
  by_cases h31 : j < 574
  · exact kvsstaticRange_554.get (by omega) (by omega)
  by_cases h32 : j < 593
  · exact kvsstaticRange_574.get (by omega) (by omega)
  by_cases h33 : j < 612
  · exact kvsstaticRange_593.get (by omega) (by omega)
  by_cases h34 : j < 626
  · exact kvsstaticRange_612.get (by omega) (by omega)
  by_cases h35 : j < 644
  · exact kvsstaticRange_626.get (by omega) (by omega)
  by_cases h36 : j < 660
  · exact kvsstaticRange_644.get (by omega) (by omega)
  by_cases h37 : j < 677
  · exact kvsstaticRange_660.get (by omega) (by omega)
  by_cases h38 : j < 695
  · exact kvsstaticRange_677.get (by omega) (by omega)
  by_cases h39 : j < 712
  · exact kvsstaticRange_695.get (by omega) (by omega)
  by_cases h40 : j < 729
  · exact kvsstaticRange_712.get (by omega) (by omega)
  by_cases h41 : j < 742
  · exact kvsstaticRange_729.get (by omega) (by omega)
  by_cases h42 : j < 759
  · exact kvsstaticRange_742.get (by omega) (by omega)
  by_cases h43 : j < 778
  · exact kvsstaticRange_759.get (by omega) (by omega)
  by_cases h44 : j < 790
  · exact kvsstaticRange_778.get (by omega) (by omega)
  by_cases h45 : j < 808
  · exact kvsstaticRange_790.get (by omega) (by omega)
  by_cases h46 : j < 821
  · exact kvsstaticRange_808.get (by omega) (by omega)
  by_cases h47 : j < 838
  · exact kvsstaticRange_821.get (by omega) (by omega)
  by_cases h48 : j < 856
  · exact kvsstaticRange_838.get (by omega) (by omega)
  by_cases h49 : j < 875
  · exact kvsstaticRange_856.get (by omega) (by omega)
  by_cases h50 : j < 899
  · exact kvsstaticRange_875.get (by omega) (by omega)
  by_cases h51 : j < 922
  · exact kvsstaticRange_899.get (by omega) (by omega)
  by_cases h52 : j < 939
  · exact kvsstaticRange_922.get (by omega) (by omega)
  by_cases h53 : j < 954
  · exact kvsstaticRange_939.get (by omega) (by omega)
  by_cases h54 : j < 966
  · exact kvsstaticRange_954.get (by omega) (by omega)
  by_cases h55 : j < 980
  · exact kvsstaticRange_966.get (by omega) (by omega)
  by_cases h56 : j < 993
  · exact kvsstaticRange_980.get (by omega) (by omega)
  by_cases h57 : j < 1004
  · exact kvsstaticRange_993.get (by omega) (by omega)
  by_cases h58 : j < 1016
  · exact kvsstaticRange_1004.get (by omega) (by omega)
  by_cases h59 : j < 1025
  · exact kvsstaticRange_1016.get (by omega) (by omega)
  by_cases h60 : j < 1033
  · exact kvsstaticRange_1025.get (by omega) (by omega)
  exact kvsstaticRange_1033.get (by omega) (by omega)

end
end LeanVM.Guest
