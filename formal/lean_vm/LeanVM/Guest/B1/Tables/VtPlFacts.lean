/-
  LeanVM.Guest.B1.Tables.VtPlFacts

  `verify_tables`' placed form: its buffers' sizes and pointers by index, the loads' classes.
-/

module

public import LeanVM.Guest.B1.Tables.VtPlBase

/-!
# Sizes, pointers and the loads' classes

`vtSizes n` is a fixed prefix of 202 sizes and the three sum-check buffers (`vtSizes_split`);
the selectors' buffers are at `selBuf i` with values `selVal i + 12, 15, 16` (`vt_selBuf`). Every
load of the body is through an argument, a `HeapBuf`, a selector's or an index chain's product,
a sort rank's product, the table sum-check's slots, or a table's two product pointers
(`vt_loads`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Sig
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- The sizes before the sum-check's buffers. -/
def vtSzPre : List ℕ :=
  [102, 102, 102, 34, 102] ++ selSz ++ selSz ++ [42] ++ selSz ++ [42] ++
    (List.range 62).flatMap (fun _ => selSz)

theorem vtSizes_split (n : ℕ) : vtSizes n = vtSzPre ++ [4 * (n + 1), n + 1, n + 1] := rfl

theorem vtSzPre_length : vtSzPre.length = 202 := by simp [vtSzPre, selSz]

theorem vtSizes_lo (n : ℕ) {i : ℕ} (hi : i < 202) : (vtSizes n).getD i 0 = vtSzPre.getD i 0 := by
  rw [vtSizes_split, List.getD_append _ _ _ _ (by rw [vtSzPre_length]; exact hi)]

theorem vtSizes_202 (n : ℕ) : (vtSizes n).getD 202 0 = 4 * (n + 1) := by
  rw [vtSizes_split, List.getD_append_right _ _ _ _ (by simp [vtSzPre_length]), vtSzPre_length]; rfl

theorem vtSizes_203 (n : ℕ) : (vtSizes n).getD 203 0 = n + 1 := by
  rw [vtSizes_split, List.getD_append_right _ _ _ _ (by simp [vtSzPre_length]), vtSzPre_length]; rfl

theorem vtSizes_204 (n : ℕ) : (vtSizes n).getD 204 0 = n + 1 := by
  rw [vtSizes_split, List.getD_append_right _ _ _ _ (by simp [vtSzPre_length]), vtSzPre_length]; rfl

theorem vtSizes_mono (n : ℕ) {i : ℕ} (hi : i < 205) : (vtSizes 0).getD i 0 ≤ (vtSizes n).getD i 0 := by
  rcases Nat.lt_or_ge i 202 with h | h
  · rw [vtSizes_lo 0 h, vtSizes_lo n h]
  · interval_cases i
    · rw [vtSizes_202, vtSizes_202]; omega
    · rw [vtSizes_203, vtSizes_203]; omega
    · rw [vtSizes_204, vtSizes_204]; omega

set_option maxRecDepth 100000 in
/-- The selectors' buffers. -/
theorem vt_selBuf : ∀ i < 65, selBuf i + 2 < 202 ∧ vtSzPre.getD (selBuf i + 1) 0 = 42 ∧
    vtSzPre.getD (selBuf i + 2) 0 = 42 ∧ vtAllocVar.getD (selBuf i) 0 = selVal.getD i 0 + 12 ∧
    vtAllocVar.getD (selBuf i + 1) 0 = selVal.getD i 0 + 15 ∧
    vtAllocVar.getD (selBuf i + 2) 0 = selVal.getD i 0 + 16 ∧ selBlk.getD i 0 < 102 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem vt_allocVar_fixed : vtAllocVar.getD 0 0 = 24 ∧ vtAllocVar.getD 1 0 = 25 ∧
    vtAllocVar.getD 2 0 = 128 ∧ vtAllocVar.getD 11 0 = 1925 ∧ vtAllocVar.getD 15 0 = 2029 ∧
    vtAllocVar.getD 202 0 = 4636 ∧ vtAllocVar.getD 203 0 = 4639 ∧ vtAllocVar.getD 204 0 = 4655 ∧
    vtSzPre.getD 0 0 = 102 ∧ vtSzPre.getD 1 0 = 102 ∧ vtSzPre.getD 2 0 = 102 ∧
    vtSzPre.getD 11 0 = 42 ∧ vtSzPre.getD 15 0 = 42 := by
  decide +kernel

/-- `stackOrder`'s entries are below the length. -/
theorem stackOrder_getD_lt (l : List ℕ) {r : ℕ} (hr : r < l.length) : (stackOrder l).getD r 0 < l.length := by
  have hperm : (stackOrder l).Perm (List.range l.length) := List.mergeSort_perm _ _
  have hl : (stackOrder l).length = l.length := hperm.length_eq.trans (by simp)
  have := hperm.subset (List.getElem_mem (show r < (stackOrder l).length by omega))
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.mem_range.mp this

/-- `sort_order`'s entries: the push side's blocks, then the count side's. -/
theorem sortW_get (ks : ℕ → ℕ) {r : ℕ} (hr : r < 102) :
    (sortW ks).getD r 0 = if r < 37 then gen ^ (pushOrd ks).getD r 0
      else if 74 ≤ r then gen ^ (74 + (countOrd ks).getD (r - 74) 0) else 0 := by
  rw [sortW, getD_map_range _ _ hr]

theorem pushOrd_lt (ks : ℕ → ℕ) {r : ℕ} (hr : r < 37) : (pushOrd ks).getD r 0 < 37 := by
  have := stackOrder_getD_lt ((List.range 37).map ks) (r := r) (by simp; exact hr)
  simpa [pushOrd] using this

theorem countOrd_lt (ks : ℕ → ℕ) {r : ℕ} (hr : r < 28) : (countOrd ks).getD r 0 < 28 := by
  have := stackOrder_getD_lt ((List.range 28).map fun i => ks (74 + i)) (r := r) (by simp; exact hr)
  simpa [countOrd] using this

/-- The buffers' words before the sum-check's. -/
def vtOwnPre (ks : ℕ → ℕ) (point : List E) (logMem : ℕ) : List (List E) :=
  [sortW ks, sideW, offW ks, idxcW, bimW point logMem] ++ selW ks point 0 ++ selW ks point 1 ++
    [idxChainW point logMem] ++ selW ks point 2 ++ [idxChainW point 18] ++
    (List.range 62).flatMap (fun i => selW ks point (i + 3))

theorem vtOwnW_split (ks : ℕ → ℕ) (point : List E) (logMem n : ℕ) (cvr : ℕ → Digest) (cur : E)
    (cl ch : ℕ → E) (chis : List E) :
    vtOwnW ks point logMem n cvr cur cl ch chis =
      vtOwnPre ks point logMem ++ [zcRoundsW cvr cur cl n, zcCprodW ch n, zcPeqW point chis n] := rfl

theorem vtOwnPre_length (ks : ℕ → ℕ) (point : List E) (logMem : ℕ) :
    (vtOwnPre ks point logMem).length = 202 := by
  simp [vtOwnPre, selW]

theorem vtOwnW_202 (ks : ℕ → ℕ) (point : List E) (logMem n : ℕ) (cvr : ℕ → Digest) (cur : E)
    (cl ch : ℕ → E) (chis : List E) :
    (vtOwnW ks point logMem n cvr cur cl ch chis).getD 202 [] = zcRoundsW cvr cur cl n := by
  rw [vtOwnW_split, List.getD_append_right _ _ _ _ (by rw [vtOwnPre_length]), vtOwnPre_length]; rfl

theorem vtOwnW_0 (ks : ℕ → ℕ) (point : List E) (logMem n : ℕ) (cvr : ℕ → Digest) (cur : E)
    (cl ch : ℕ → E) (chis : List E) :
    (vtOwnW ks point logMem n cvr cur cl ch chis).getD 0 [] = sortW ks := rfl

/-! ## The loads' classes -/

/-- The `HeapBuf` hints' values and their least sizes. -/
def vtAllocPairs : List (ℕ × ℕ) :=
  [(24, 102), (25, 102), (128, 102), (1817, 34), (1852, 102), (1867, 34),
    (1870, 42), (1871, 42), (1905, 34), (1908, 42), (1909, 42), (1925, 42),
    (2009, 34), (2012, 42), (2013, 42), (2029, 42), (2089, 34), (2092, 42),
    (2093, 42), (2118, 34), (2121, 42), (2122, 42), (2147, 34), (2150, 42),
    (2151, 42), (2176, 34), (2179, 42), (2180, 42), (2205, 34), (2208, 42),
    (2209, 42), (2234, 34), (2237, 42), (2238, 42), (2263, 34), (2266, 42),
    (2267, 42), (2292, 34), (2295, 42), (2296, 42), (2321, 34), (2324, 42),
    (2325, 42), (2350, 34), (2353, 42), (2354, 42), (2379, 34), (2382, 42),
    (2383, 42), (2408, 34), (2411, 42), (2412, 42), (2437, 34), (2440, 42),
    (2441, 42), (2466, 34), (2469, 42), (2470, 42), (2495, 34), (2498, 42),
    (2499, 42), (2524, 34), (2527, 42), (2528, 42), (2553, 34), (2556, 42),
    (2557, 42), (2582, 34), (2585, 42), (2586, 42), (2611, 34), (2614, 42),
    (2615, 42), (2640, 34), (2643, 42), (2644, 42), (2669, 34), (2672, 42),
    (2673, 42), (2698, 34), (2701, 42), (2702, 42), (2727, 34), (2730, 42),
    (2731, 42), (2756, 34), (2759, 42), (2760, 42), (2785, 34), (2788, 42),
    (2789, 42), (2814, 34), (2817, 42), (2818, 42), (2843, 34), (2846, 42),
    (2847, 42), (2872, 34), (2875, 42), (2876, 42), (2901, 34), (2904, 42),
    (2905, 42), (2930, 34), (2933, 42), (2934, 42), (2959, 34), (2962, 42),
    (2963, 42), (2988, 34), (2991, 42), (2992, 42), (3017, 34), (3020, 42),
    (3021, 42), (3046, 34), (3049, 42), (3050, 42), (3718, 34), (3721, 42),
    (3722, 42), (3746, 34), (3749, 42), (3750, 42), (3775, 34), (3778, 42),
    (3779, 42), (3804, 34), (3807, 42), (3808, 42), (3833, 34), (3836, 42),
    (3837, 42), (3862, 34), (3865, 42), (3866, 42), (3891, 34), (3894, 42),
    (3895, 42), (3920, 34), (3923, 42), (3924, 42), (3949, 34), (3952, 42),
    (3953, 42), (3978, 34), (3981, 42), (3982, 42), (4007, 34), (4010, 42),
    (4011, 42), (4036, 34), (4039, 42), (4040, 42), (4065, 34), (4068, 42),
    (4069, 42), (4094, 34), (4097, 42), (4098, 42), (4123, 34), (4126, 42),
    (4127, 42), (4152, 34), (4155, 42), (4156, 42), (4181, 34), (4184, 42),
    (4185, 42), (4210, 34), (4213, 42), (4214, 42), (4239, 34), (4242, 42),
    (4243, 42), (4268, 34), (4271, 42), (4272, 42), (4297, 34), (4300, 42),
    (4301, 42), (4326, 34), (4329, 42), (4330, 42), (4355, 34), (4358, 42),
    (4359, 42), (4384, 34), (4387, 42), (4388, 42), (4413, 34), (4416, 42),
    (4417, 42), (4442, 34), (4445, 42), (4446, 42), (4471, 34), (4474, 42),
    (4475, 42), (4500, 34), (4503, 42), (4504, 42), (4636, 4), (4639, 1),
    (4655, 1)]

set_option maxRecDepth 100000 in
theorem vtAllocPairs_eq : vtAllocPairs = vtAllocVar.zip (vtSzPre ++ [4, 1, 1]) := by decide +kernel

/-- The selectors' two products. -/
def vtSelPtrs : List ℕ :=
  [1877, 1879, 1915, 1917, 2019, 2021, 2099, 2101, 2128, 2130, 2157, 2159,
    2186, 2188, 2215, 2217, 2244, 2246, 2273, 2275, 2302, 2304, 2331, 2333,
    2360, 2362, 2389, 2391, 2418, 2420, 2447, 2449, 2476, 2478, 2505, 2507,
    2534, 2536, 2563, 2565, 2592, 2594, 2621, 2623, 2650, 2652, 2679, 2681,
    2708, 2710, 2737, 2739, 2766, 2768, 2795, 2797, 2824, 2826, 2853, 2855,
    2882, 2884, 2911, 2913, 2940, 2942, 2969, 2971, 2998, 3000, 3027, 3029,
    3056, 3058, 3728, 3730, 3756, 3758, 3785, 3787, 3814, 3816, 3843, 3845,
    3872, 3874, 3901, 3903, 3930, 3932, 3959, 3961, 3988, 3990, 4017, 4019,
    4046, 4048, 4075, 4077, 4104, 4106, 4133, 4135, 4162, 4164, 4191, 4193,
    4220, 4222, 4249, 4251, 4278, 4280, 4307, 4309, 4336, 4338, 4365, 4367,
    4394, 4396, 4423, 4425, 4452, 4454, 4481, 4483, 4510, 4512]

set_option maxRecDepth 100000 in
theorem vtSelPtrs_eq : vtSelPtrs =
    (List.range 65).flatMap fun i => [selVal.getD i 0 + 22, selVal.getD i 0 + 24] := by decide +kernel

/-- The sort ranks' four product pointers (`side`, `bk`, `off`, the squares). -/
def vtRankPtrs : List ℕ :=
  [134, 137, 140, 141, 1048, 1051, 1054, 1055, 148, 151, 164, 165,
    173, 176, 189, 190, 198, 201, 214, 215, 223, 226, 239, 240,
    248, 251, 264, 265, 273, 276, 289, 290, 298, 301, 314, 315,
    323, 326, 339, 340, 348, 351, 364, 365, 373, 376, 389, 390,
    398, 401, 414, 415, 423, 426, 439, 440, 448, 451, 464, 465,
    473, 476, 489, 490, 498, 501, 514, 515, 523, 526, 539, 540,
    548, 551, 564, 565, 573, 576, 589, 590, 598, 601, 614, 615,
    623, 626, 639, 640, 648, 651, 664, 665, 673, 676, 689, 690,
    698, 701, 714, 715, 723, 726, 739, 740, 748, 751, 764, 765,
    773, 776, 789, 790, 798, 801, 814, 815, 823, 826, 839, 840,
    848, 851, 864, 865, 873, 876, 889, 890, 898, 901, 914, 915,
    923, 926, 939, 940, 948, 951, 964, 965, 973, 976, 989, 990,
    998, 1001, 1014, 1015, 1023, 1026, 1039, 1040, 1062, 1065, 1078, 1079,
    1087, 1090, 1103, 1104, 1112, 1115, 1128, 1129, 1137, 1140, 1153, 1154,
    1162, 1165, 1178, 1179, 1187, 1190, 1203, 1204, 1212, 1215, 1228, 1229,
    1237, 1240, 1253, 1254, 1262, 1265, 1278, 1279, 1287, 1290, 1303, 1304,
    1312, 1315, 1328, 1329, 1337, 1340, 1353, 1354, 1362, 1365, 1378, 1379,
    1387, 1390, 1403, 1404, 1412, 1415, 1428, 1429, 1437, 1440, 1453, 1454,
    1462, 1465, 1478, 1479, 1487, 1490, 1503, 1504, 1512, 1515, 1528, 1529,
    1537, 1540, 1553, 1554, 1562, 1565, 1578, 1579, 1587, 1590, 1603, 1604,
    1612, 1615, 1628, 1629, 1637, 1640, 1653, 1654, 1662, 1665, 1678, 1679,
    1687, 1690, 1703, 1704, 1712, 1715, 1728, 1729]

set_option maxRecDepth 100000 in
theorem vtRankPtrs_eq : vtRankPtrs = [134, 137, 140, 141, 1048, 1051, 1054, 1055] ++
    (List.range 36).flatMap (fun q => [rkV 129 q + 5, rkV 129 q + 8, rkV 129 q + 21, rkV 129 q + 22]) ++
    (List.range 27).flatMap (fun q => [rkV 1043 q + 5, rkV 1043 q + 8, rkV 1043 q + 21,
      rkV 1043 q + 22]) := by decide +kernel

/-- The tables' two product pointers. -/
def vtTabPtrs : List ℕ := [5142, 5144, 5670, 5672, 5947, 5949, 6470, 6472, 6972, 6974, 8133, 8135]

/-- The arguments' pointers and their words' counts. -/
def vtArgPairs : List (ℕ × ℕ) := [(2, 5), (7, 7), (8, 6), (9, 102), (11, 16), (13, 112), (14, 109)]

/-- **A load's class**, on its pointer's number and offset. -/
def vtLoadN (k off : ℕ) : Bool :=
  vtArgPairs.any (fun t => k == t.1 && decide (off < t.2)) ||
    (off == 0 && (vtTabPtrs.contains k || k == 1930 || k == 2034 || vtSelPtrs.contains k ||
      vtRankPtrs.contains k)) ||
    (k == 4648 && decide (off < 4)) || (k == 4651 && decide (off < 104)) ||
    vtAllocPairs.any (fun t => k == t.1 && decide (off < t.2))

def vtLoadB (q : V × ℕ) : Bool :=
  match q.1 with
  | .n k => vtLoadN k q.2
  | _ => false

set_option maxRecDepth 1000000 in
theorem vt_loads : (vtPre.filterMap Stmt.loadS).all vtLoadB = true := by decide +kernel

theorem vtLoadN_cases {k off : ℕ} (h : vtLoadN k off = true) :
    (∃ t ∈ vtArgPairs, k = t.1 ∧ off < t.2) ∨
      (off = 0 ∧ (k ∈ vtTabPtrs ∨ k = 1930 ∨ k = 2034 ∨ k ∈ vtSelPtrs ∨ k ∈ vtRankPtrs)) ∨
      (k = 4648 ∧ off < 4) ∨ (k = 4651 ∧ off < 104) ∨ (∃ t ∈ vtAllocPairs, k = t.1 ∧ off < t.2) := by
  unfold vtLoadN at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.any_eq_true,
    List.contains_iff_mem] at h
  rcases h with (((h | h) | h) | h) | h
  · exact Or.inl h
  · obtain ⟨h0, (((h1 | h1) | h1) | h1) | h1⟩ := h
    · exact Or.inr (Or.inl ⟨h0, Or.inl h1⟩)
    · exact Or.inr (Or.inl ⟨h0, Or.inr (Or.inl h1)⟩)
    · exact Or.inr (Or.inl ⟨h0, Or.inr (Or.inr (Or.inl h1))⟩)
    · exact Or.inr (Or.inl ⟨h0, Or.inr (Or.inr (Or.inr (Or.inl h1)))⟩)
    · exact Or.inr (Or.inl ⟨h0, Or.inr (Or.inr (Or.inr (Or.inr h1)))⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

end
end LeanVM.Guest.B1.VerifySub
