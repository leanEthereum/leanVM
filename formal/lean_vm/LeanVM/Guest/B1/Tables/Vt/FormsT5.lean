/-
  LeanVM.Guest.B1.Tables.Vt.FormsT5

  Table 5's forms on the three sides: the blocks' selectors times their values.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.FormsT5a
public import LeanVM.Guest.B1.Tables.Vt.FormsT5b

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
theorem vtSide05 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6675) =
      vtSideVal [σ (.n 1151), σ (.n 1160), σ (.n 1169), σ (.n 1178), σ (.n 1187), σ (.n 1196), σ (.n 1205),
        σ (.n 1214), σ (.n 1223), σ (.n 1232), σ (.n 1241), σ (.n 1250), σ (.n 1259),
        σ (.n 1268), σ (.n 1277), σ (.n 1286), σ (.n 1295), σ (.n 1304), σ (.n 1313),
        σ (.n 1322), σ (.n 1331), σ (.n 1340), σ (.n 1349), σ (.n 1358), σ (.n 1367),
        σ (.n 1376), σ (.n 1385), σ (.n 1394)]
        (σ (.n 14)) W ev vtBTerms05 := by
  rw [vtB05_27 h hw hev, vtB05_26 h hw hev, vtB05_25 h hw hev, vtB05_24 h hw hev, vtB05_23 h hw hev,
    vtB05_22 h hw hev, vtB05_21 h hw hev, vtB05_20 h hw hev, vtB05_19 h hw hev,
    vtB05_18 h hw hev, vtB05_17 h hw hev, vtB05_16 h hw hev, vtB05_15 h hw hev,
    vtB05_14 h hw hev, vtB05_13 h hw hev, vtB05_12 h hw hev, vtB05_11 h hw hev,
    vtB05_10 h hw hev, vtB05_9 h hw hev, vtB05_8 h hw hev, vtB05_7 h hw hev, vtB05_6 h hw hev,
    vtB05_5 h hw hev, vtB05_4 h hw hev, vtB05_3 h hw hev, vtB05_2 h hw hev, vtB05_1 h hw hev,
    vtB05_0 h hw hev]
  simp only [vtSideVal, vtBTerms05, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide15 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6856) =
      vtSideVal [σ (.n 2014), σ (.n 2016), σ (.n 2018), σ (.n 2020), σ (.n 2022), σ (.n 2024), σ (.n 2026),
        σ (.n 2028), σ (.n 2030), σ (.n 2032), σ (.n 2034), σ (.n 2036), σ (.n 2038),
        σ (.n 2040), σ (.n 2042), σ (.n 2044), σ (.n 2046), σ (.n 2048), σ (.n 2050),
        σ (.n 2052), σ (.n 2054), σ (.n 2056), σ (.n 2058), σ (.n 2060), σ (.n 2062),
        σ (.n 2064), σ (.n 2066), σ (.n 2068)]
        (σ (.n 14)) W ev vtBTerms15 := by
  have hF0 : σ (.n 6675) =
      vtSideVal [σ (.n 2014), σ (.n 2016), σ (.n 2018), σ (.n 2020), σ (.n 2022), σ (.n 2024), σ (.n 2026),
        σ (.n 2028), σ (.n 2030), σ (.n 2032), σ (.n 2034), σ (.n 2036), σ (.n 2038),
        σ (.n 2040), σ (.n 2042), σ (.n 2044), σ (.n 2046), σ (.n 2048), σ (.n 2050),
        σ (.n 2052), σ (.n 2054), σ (.n 2056), σ (.n 2058), σ (.n 2060), σ (.n 2062),
        σ (.n 2064), σ (.n 2066), σ (.n 2068)]
        (σ (.n 14)) W ev vtBTerms05 := by
    rw [vtPullSels5 h]; exact vtSide05 h hw hev
  have a6286 := h.atomAt 6286 (.add (.n 6856) (.n 6675) (.n 6855)) (by decide +kernel)
  simp only [Atom.Holds] at a6286
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull5, ← hF0, a6286, vtD5_27 h hw hev, vtD5_26 h hw hev, vtD5_25 h hw hev, vtD5_24 h hw hev, vtD5_23 h hw hev,
    vtD5_22 h hw hev, vtD5_21 h hw hev, vtD5_20 h hw hev, vtD5_19 h hw hev, vtD5_18 h hw hev,
    vtD5_17 h hw hev, vtD5_16 h hw hev, vtD5_15 h hw hev, vtD5_14 h hw hev, vtD5_13 h hw hev,
    vtD5_12 h hw hev, vtD5_11 h hw hev, vtD5_10 h hw hev, vtD5_9 h hw hev, vtD5_8 h hw hev,
    vtD5_7 h hw hev, vtD5_6 h hw hev, vtD5_5 h hw hev, vtD5_4 h hw hev, vtD5_3 h hw hev,
    vtD5_2 h hw hev, vtD5_1 h hw hev, vtD5_0 h hw hev]
  simp only [vtDiffSum, vtDTerms5, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide25 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6911) =
      vtSideVal [σ (.n 2227), σ (.n 2236), σ (.n 2245), σ (.n 2254), σ (.n 2263), σ (.n 2272), σ (.n 2281),
        σ (.n 2290), σ (.n 2299), σ (.n 2308), σ (.n 2317), σ (.n 2326), σ (.n 2335),
        σ (.n 2344), σ (.n 2353), σ (.n 2362), σ (.n 2371), σ (.n 2380), σ (.n 2389),
        σ (.n 2398), σ (.n 2407), σ (.n 2416), σ (.n 2425), σ (.n 2434), σ (.n 2443),
        σ (.n 2452), σ (.n 2461)]
        (0) (fun _ ↦ 1) ev vtBTerms25 := by
  obtain ⟨_, hs⟩ := h.sliceAt 6289 [
    .atom (.mul (.n 6859) (.n 2227) (.n 5373)),
    .atom (.mul (.n 6860) (.n 2236) (.n 5384)),
    .atom (.add (.n 6861) (.n 6859) (.n 6860)),
    .atom (.mul (.n 6862) (.n 2245) (.n 5395)),
    .atom (.add (.n 6863) (.n 6861) (.n 6862)),
    .atom (.mul (.n 6864) (.n 2254) (.n 5406)),
    .atom (.add (.n 6865) (.n 6863) (.n 6864)),
    .atom (.mul (.n 6866) (.n 2263) (.n 5430)),
    .atom (.add (.n 6867) (.n 6865) (.n 6866)),
    .atom (.mul (.n 6868) (.n 2272) (.n 5441)),
    .atom (.add (.n 6869) (.n 6867) (.n 6868)),
    .atom (.mul (.n 6870) (.n 2281) (.n 5452)),
    .atom (.add (.n 6871) (.n 6869) (.n 6870)),
    .atom (.mul (.n 6872) (.n 2290) (.n 5463)),
    .atom (.add (.n 6873) (.n 6871) (.n 6872)),
    .atom (.mul (.n 6874) (.n 2299) (.n 5487)),
    .atom (.add (.n 6875) (.n 6873) (.n 6874)),
    .atom (.mul (.n 6876) (.n 2308) (.n 5498)),
    .atom (.add (.n 6877) (.n 6875) (.n 6876)),
    .atom (.mul (.n 6878) (.n 2317) (.n 5509)),
    .atom (.add (.n 6879) (.n 6877) (.n 6878)),
    .atom (.mul (.n 6880) (.n 2326) (.n 5520)),
    .atom (.add (.n 6881) (.n 6879) (.n 6880)),
    .atom (.mul (.n 6882) (.n 2335) (.n 5544)),
    .atom (.add (.n 6883) (.n 6881) (.n 6882)),
    .atom (.mul (.n 6884) (.n 2344) (.n 5555)),
    .atom (.add (.n 6885) (.n 6883) (.n 6884)),
    .atom (.mul (.n 6886) (.n 2353) (.n 5566)),
    .atom (.add (.n 6887) (.n 6885) (.n 6886)),
    .atom (.mul (.n 6888) (.n 2362) (.n 5577)),
    .atom (.add (.n 6889) (.n 6887) (.n 6888)),
    .atom (.mul (.n 6890) (.n 2371) (.n 5601)),
    .atom (.add (.n 6891) (.n 6889) (.n 6890)),
    .atom (.mul (.n 6892) (.n 2380) (.n 5612)),
    .atom (.add (.n 6893) (.n 6891) (.n 6892)),
    .atom (.mul (.n 6894) (.n 2389) (.n 5623)),
    .atom (.add (.n 6895) (.n 6893) (.n 6894)),
    .atom (.mul (.n 6896) (.n 2398) (.n 5634)),
    .atom (.add (.n 6897) (.n 6895) (.n 6896)),
    .atom (.mul (.n 6898) (.n 2407) (.n 5658)),
    .atom (.add (.n 6899) (.n 6897) (.n 6898)),
    .atom (.mul (.n 6900) (.n 2416) (.n 5669)),
    .atom (.add (.n 6901) (.n 6899) (.n 6900)),
    .atom (.mul (.n 6902) (.n 2425) (.n 5680)),
    .atom (.add (.n 6903) (.n 6901) (.n 6902)),
    .atom (.mul (.n 6904) (.n 2434) (.n 5691)),
    .atom (.add (.n 6905) (.n 6903) (.n 6904)),
    .atom (.mul (.n 6906) (.n 2443) (.n 5715)),
    .atom (.add (.n 6907) (.n 6905) (.n 6906)),
    .atom (.mul (.n 6908) (.n 2452) (.n 5726)),
    .atom (.add (.n 6909) (.n 6907) (.n 6908)),
    .atom (.mul (.n 6910) (.n 2461) (.n 5737)),
    .atom (.add (.n 6911) (.n 6909) (.n 6910))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6289, a6290, a6291, a6292, a6293, a6294, a6295, a6296, a6297, a6298, a6299, a6300, a6301, a6302,
    a6303, a6304, a6305, a6306, a6307, a6308, a6309, a6310, a6311, a6312, a6313, a6314, a6315,
    a6316, a6317, a6318, a6319, a6320, a6321, a6322, a6323, a6324, a6325, a6326, a6327, a6328,
    a6329, a6330, a6331, a6332, a6333, a6334, a6335, a6336, a6337, a6338, a6339, a6340, a6341, -⟩ := hs
  have v5373 : σ (.n 5373) = ev 65 := by
    rw [← hev 65 (by norm_num)]; exact (vt_eval h (k := 132) (by norm_num)).2.2
  have v5384 : σ (.n 5384) = ev 66 := by
    rw [← hev 66 (by norm_num)]; exact (vt_eval h (k := 133) (by norm_num)).2.2
  have v5395 : σ (.n 5395) = ev 67 := by
    rw [← hev 67 (by norm_num)]; exact (vt_eval h (k := 134) (by norm_num)).2.2
  have v5406 : σ (.n 5406) = ev 68 := by
    rw [← hev 68 (by norm_num)]; exact (vt_eval h (k := 135) (by norm_num)).2.2
  have v5430 : σ (.n 5430) = ev 69 := by
    rw [← hev 69 (by norm_num)]; exact (vt_eval h (k := 136) (by norm_num)).2.2
  have v5441 : σ (.n 5441) = ev 70 := by
    rw [← hev 70 (by norm_num)]; exact (vt_eval h (k := 137) (by norm_num)).2.2
  have v5452 : σ (.n 5452) = ev 71 := by
    rw [← hev 71 (by norm_num)]; exact (vt_eval h (k := 138) (by norm_num)).2.2
  have v5463 : σ (.n 5463) = ev 72 := by
    rw [← hev 72 (by norm_num)]; exact (vt_eval h (k := 139) (by norm_num)).2.2
  have v5487 : σ (.n 5487) = ev 73 := by
    rw [← hev 73 (by norm_num)]; exact (vt_eval h (k := 140) (by norm_num)).2.2
  have v5498 : σ (.n 5498) = ev 74 := by
    rw [← hev 74 (by norm_num)]; exact (vt_eval h (k := 141) (by norm_num)).2.2
  have v5509 : σ (.n 5509) = ev 75 := by
    rw [← hev 75 (by norm_num)]; exact (vt_eval h (k := 142) (by norm_num)).2.2
  have v5520 : σ (.n 5520) = ev 76 := by
    rw [← hev 76 (by norm_num)]; exact (vt_eval h (k := 143) (by norm_num)).2.2
  have v5544 : σ (.n 5544) = ev 77 := by
    rw [← hev 77 (by norm_num)]; exact (vt_eval h (k := 144) (by norm_num)).2.2
  have v5555 : σ (.n 5555) = ev 78 := by
    rw [← hev 78 (by norm_num)]; exact (vt_eval h (k := 145) (by norm_num)).2.2
  have v5566 : σ (.n 5566) = ev 79 := by
    rw [← hev 79 (by norm_num)]; exact (vt_eval h (k := 146) (by norm_num)).2.2
  have v5577 : σ (.n 5577) = ev 80 := by
    rw [← hev 80 (by norm_num)]; exact (vt_eval h (k := 147) (by norm_num)).2.2
  have v5601 : σ (.n 5601) = ev 81 := by
    rw [← hev 81 (by norm_num)]; exact (vt_eval h (k := 148) (by norm_num)).2.2
  have v5612 : σ (.n 5612) = ev 82 := by
    rw [← hev 82 (by norm_num)]; exact (vt_eval h (k := 149) (by norm_num)).2.2
  have v5623 : σ (.n 5623) = ev 83 := by
    rw [← hev 83 (by norm_num)]; exact (vt_eval h (k := 150) (by norm_num)).2.2
  have v5634 : σ (.n 5634) = ev 84 := by
    rw [← hev 84 (by norm_num)]; exact (vt_eval h (k := 151) (by norm_num)).2.2
  have v5658 : σ (.n 5658) = ev 85 := by
    rw [← hev 85 (by norm_num)]; exact (vt_eval h (k := 152) (by norm_num)).2.2
  have v5669 : σ (.n 5669) = ev 86 := by
    rw [← hev 86 (by norm_num)]; exact (vt_eval h (k := 153) (by norm_num)).2.2
  have v5680 : σ (.n 5680) = ev 87 := by
    rw [← hev 87 (by norm_num)]; exact (vt_eval h (k := 154) (by norm_num)).2.2
  have v5691 : σ (.n 5691) = ev 88 := by
    rw [← hev 88 (by norm_num)]; exact (vt_eval h (k := 155) (by norm_num)).2.2
  have v5715 : σ (.n 5715) = ev 89 := by
    rw [← hev 89 (by norm_num)]; exact (vt_eval h (k := 156) (by norm_num)).2.2
  have v5726 : σ (.n 5726) = ev 90 := by
    rw [← hev 90 (by norm_num)]; exact (vt_eval h (k := 157) (by norm_num)).2.2
  have v5737 : σ (.n 5737) = ev 91 := by
    rw [← hev 91 (by norm_num)]; exact (vt_eval h (k := 158) (by norm_num)).2.2
  rw [a6341, a6339, a6337, a6335, a6333, a6331, a6329, a6327, a6325, a6323, a6321, a6319, a6317, a6315,
    a6313, a6311, a6309, a6307, a6305, a6303, a6301, a6299, a6297, a6295, a6293, a6291, a6289,
    a6290, a6292, a6294, a6296, a6298, a6300, a6302, a6304, a6306, a6308, a6310, a6312, a6314,
    a6316, a6318, a6320, a6322, a6324, a6326, a6328, a6330, a6332, a6334, a6336, a6338, a6340,
    v5373, v5384, v5395, v5406, v5430, v5441, v5452, v5463, v5487, v5498, v5509, v5520, v5544,
    v5555, v5566, v5577, v5601, v5612, v5623, v5634, v5658, v5669, v5680, v5691, v5715, v5726,
    v5737]
  simp only [vtSideVal, vtBTerms25, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one, zero_add,
    one_mul, mul_one, add_zero, add_assoc]

end
end LeanVM.Guest.B1.Tables
