/-
  LeanVM.Guest.B1.Tables.Vt.FormsT5

  Table 5's forms on the three sides: the blocks' selectors times their values.

  Do not edit: `scripts/b1c-vt/all.py` writes it (`regen-guest.sh`, step `vt`).
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
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5774) =
      vtSideVal [σ (.n 1049), σ (.n 1058), σ (.n 1067), σ (.n 1076), σ (.n 1085), σ (.n 1094), σ (.n 1103),
        σ (.n 1112), σ (.n 1121), σ (.n 1130), σ (.n 1139), σ (.n 1148), σ (.n 1157),
        σ (.n 1166), σ (.n 1175), σ (.n 1184), σ (.n 1193), σ (.n 1202), σ (.n 1211),
        σ (.n 1220), σ (.n 1229), σ (.n 1238), σ (.n 1247), σ (.n 1256), σ (.n 1265),
        σ (.n 1274), σ (.n 1283), σ (.n 1292)]
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
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5887) =
      vtSideVal [σ (.n 1381), σ (.n 1383), σ (.n 1385), σ (.n 1387), σ (.n 1389), σ (.n 1391), σ (.n 1393),
        σ (.n 1395), σ (.n 1397), σ (.n 1399), σ (.n 1401), σ (.n 1403), σ (.n 1405),
        σ (.n 1407), σ (.n 1409), σ (.n 1411), σ (.n 1413), σ (.n 1415), σ (.n 1417),
        σ (.n 1419), σ (.n 1421), σ (.n 1423), σ (.n 1425), σ (.n 1427), σ (.n 1429),
        σ (.n 1431), σ (.n 1433), σ (.n 1435)]
        (σ (.n 14)) W ev vtBTerms15 := by
  have hF0 : σ (.n 5774) =
      vtSideVal [σ (.n 1381), σ (.n 1383), σ (.n 1385), σ (.n 1387), σ (.n 1389), σ (.n 1391), σ (.n 1393),
        σ (.n 1395), σ (.n 1397), σ (.n 1399), σ (.n 1401), σ (.n 1403), σ (.n 1405),
        σ (.n 1407), σ (.n 1409), σ (.n 1411), σ (.n 1413), σ (.n 1415), σ (.n 1417),
        σ (.n 1419), σ (.n 1421), σ (.n 1423), σ (.n 1425), σ (.n 1427), σ (.n 1429),
        σ (.n 1431), σ (.n 1433), σ (.n 1435)]
        (σ (.n 14)) W ev vtBTerms05 := by
    rw [vtPullSels5 h]; exact vtSide05 h hw hev
  have a5463 := h.atomAt 5463 (.add (.n 5887) (.n 5774) (.n 5886)) (by decide +kernel)
  simp only [Atom.Holds] at a5463
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull5, ← hF0, a5463, vtD5_27 h hw hev, vtD5_26 h hw hev, vtD5_25 h hw hev, vtD5_24 h hw hev, vtD5_23 h hw hev,
    vtD5_22 h hw hev, vtD5_21 h hw hev, vtD5_20 h hw hev, vtD5_19 h hw hev, vtD5_18 h hw hev,
    vtD5_17 h hw hev, vtD5_16 h hw hev, vtD5_15 h hw hev, vtD5_14 h hw hev, vtD5_13 h hw hev,
    vtD5_12 h hw hev, vtD5_11 h hw hev, vtD5_10 h hw hev, vtD5_9 h hw hev, vtD5_8 h hw hev,
    vtD5_7 h hw hev, vtD5_6 h hw hev, vtD5_5 h hw hev, vtD5_4 h hw hev, vtD5_3 h hw hev,
    vtD5_2 h hw hev, vtD5_1 h hw hev, vtD5_0 h hw hev]
  simp only [vtDiffSum, vtDTerms5, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide25 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5942) =
      vtSideVal [σ (.n 1591), σ (.n 1600), σ (.n 1609), σ (.n 1618), σ (.n 1627), σ (.n 1636), σ (.n 1645),
        σ (.n 1654), σ (.n 1663), σ (.n 1672), σ (.n 1681), σ (.n 1690), σ (.n 1699),
        σ (.n 1708), σ (.n 1717), σ (.n 1726), σ (.n 1735), σ (.n 1744), σ (.n 1753),
        σ (.n 1762), σ (.n 1771), σ (.n 1780), σ (.n 1789), σ (.n 1798), σ (.n 1807),
        σ (.n 1816), σ (.n 1825)]
        (0) (fun _ ↦ 1) ev vtBTerms25 := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4822 [
    .atom (.copy (.n 5246) (.n 4500)),
    .atom (.copy (.n 5247) (.n 4504)),
    .atom (.copy (.n 5248) (.n 4521)),
    .atom (.copy (.n 5249) (.n 4525)),
    .atom (.copy (.n 5250) (.n 4529)),
    .atom (.copy (.n 5251) (.n 4533)),
    .atom (.copy (.n 5252) (.n 4550)),
    .atom (.copy (.n 5253) (.n 4554)),
    .atom (.copy (.n 5254) (.n 4558)),
    .atom (.copy (.n 5255) (.n 4562)),
    .atom (.copy (.n 5256) (.n 4579)),
    .atom (.copy (.n 5257) (.n 4583)),
    .atom (.copy (.n 5258) (.n 4587)),
    .atom (.copy (.n 5259) (.n 4591)),
    .atom (.copy (.n 5260) (.n 4608)),
    .atom (.copy (.n 5261) (.n 4612)),
    .atom (.copy (.n 5262) (.n 4616)),
    .atom (.copy (.n 5263) (.n 4620)),
    .atom (.copy (.n 5264) (.n 4637)),
    .atom (.copy (.n 5265) (.n 4641)),
    .atom (.copy (.n 5266) (.n 4645)),
    .atom (.copy (.n 5267) (.n 4649)),
    .atom (.copy (.n 5268) (.n 4666)),
    .atom (.copy (.n 5269) (.n 4670)),
    .atom (.copy (.n 5270) (.n 4674)),
    .atom (.copy (.n 5271) (.n 4678)),
    .atom (.copy (.n 5272) (.n 4695))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4822, a4823, a4824, a4825, a4826, a4827, a4828, a4829, a4830, a4831, a4832, a4833, a4834, a4835,
    a4836, a4837, a4838, a4839, a4840, a4841, a4842, a4843, a4844, a4845, a4846, a4847, a4848, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5466 [
    .atom (.mul (.n 5890) (.n 1591) (.n 5246)),
    .atom (.mul (.n 5891) (.n 1600) (.n 5247)),
    .atom (.add (.n 5892) (.n 5890) (.n 5891)),
    .atom (.mul (.n 5893) (.n 1609) (.n 5248)),
    .atom (.add (.n 5894) (.n 5892) (.n 5893)),
    .atom (.mul (.n 5895) (.n 1618) (.n 5249)),
    .atom (.add (.n 5896) (.n 5894) (.n 5895)),
    .atom (.mul (.n 5897) (.n 1627) (.n 5250)),
    .atom (.add (.n 5898) (.n 5896) (.n 5897)),
    .atom (.mul (.n 5899) (.n 1636) (.n 5251)),
    .atom (.add (.n 5900) (.n 5898) (.n 5899)),
    .atom (.mul (.n 5901) (.n 1645) (.n 5252)),
    .atom (.add (.n 5902) (.n 5900) (.n 5901)),
    .atom (.mul (.n 5903) (.n 1654) (.n 5253)),
    .atom (.add (.n 5904) (.n 5902) (.n 5903)),
    .atom (.mul (.n 5905) (.n 1663) (.n 5254)),
    .atom (.add (.n 5906) (.n 5904) (.n 5905)),
    .atom (.mul (.n 5907) (.n 1672) (.n 5255)),
    .atom (.add (.n 5908) (.n 5906) (.n 5907)),
    .atom (.mul (.n 5909) (.n 1681) (.n 5256)),
    .atom (.add (.n 5910) (.n 5908) (.n 5909)),
    .atom (.mul (.n 5911) (.n 1690) (.n 5257)),
    .atom (.add (.n 5912) (.n 5910) (.n 5911)),
    .atom (.mul (.n 5913) (.n 1699) (.n 5258)),
    .atom (.add (.n 5914) (.n 5912) (.n 5913)),
    .atom (.mul (.n 5915) (.n 1708) (.n 5259)),
    .atom (.add (.n 5916) (.n 5914) (.n 5915)),
    .atom (.mul (.n 5917) (.n 1717) (.n 5260)),
    .atom (.add (.n 5918) (.n 5916) (.n 5917)),
    .atom (.mul (.n 5919) (.n 1726) (.n 5261)),
    .atom (.add (.n 5920) (.n 5918) (.n 5919)),
    .atom (.mul (.n 5921) (.n 1735) (.n 5262)),
    .atom (.add (.n 5922) (.n 5920) (.n 5921)),
    .atom (.mul (.n 5923) (.n 1744) (.n 5263)),
    .atom (.add (.n 5924) (.n 5922) (.n 5923)),
    .atom (.mul (.n 5925) (.n 1753) (.n 5264)),
    .atom (.add (.n 5926) (.n 5924) (.n 5925)),
    .atom (.mul (.n 5927) (.n 1762) (.n 5265)),
    .atom (.add (.n 5928) (.n 5926) (.n 5927)),
    .atom (.mul (.n 5929) (.n 1771) (.n 5266)),
    .atom (.add (.n 5930) (.n 5928) (.n 5929)),
    .atom (.mul (.n 5931) (.n 1780) (.n 5267)),
    .atom (.add (.n 5932) (.n 5930) (.n 5931)),
    .atom (.mul (.n 5933) (.n 1789) (.n 5268)),
    .atom (.add (.n 5934) (.n 5932) (.n 5933)),
    .atom (.mul (.n 5935) (.n 1798) (.n 5269)),
    .atom (.add (.n 5936) (.n 5934) (.n 5935)),
    .atom (.mul (.n 5937) (.n 1807) (.n 5270)),
    .atom (.add (.n 5938) (.n 5936) (.n 5937)),
    .atom (.mul (.n 5939) (.n 1816) (.n 5271)),
    .atom (.add (.n 5940) (.n 5938) (.n 5939)),
    .atom (.mul (.n 5941) (.n 1825) (.n 5272)),
    .atom (.add (.n 5942) (.n 5940) (.n 5941))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5466, a5467, a5468, a5469, a5470, a5471, a5472, a5473, a5474, a5475, a5476, a5477, a5478, a5479,
    a5480, a5481, a5482, a5483, a5484, a5485, a5486, a5487, a5488, a5489, a5490, a5491, a5492,
    a5493, a5494, a5495, a5496, a5497, a5498, a5499, a5500, a5501, a5502, a5503, a5504, a5505,
    a5506, a5507, a5508, a5509, a5510, a5511, a5512, a5513, a5514, a5515, a5516, a5517, a5518, -⟩ := hs1
  have v4500 : σ (.n 4500) = ev 65 := by
    rw [← hev 65 (by norm_num)]; exact (vt_eval h (k := 126) (by norm_num)).2.2
  have v4504 : σ (.n 4504) = ev 66 := by
    rw [← hev 66 (by norm_num)]; exact (vt_eval h (k := 127) (by norm_num)).2.2
  have v4521 : σ (.n 4521) = ev 67 := by
    rw [← hev 67 (by norm_num)]; exact (vt_eval h (k := 128) (by norm_num)).2.2
  have v4525 : σ (.n 4525) = ev 68 := by
    rw [← hev 68 (by norm_num)]; exact (vt_eval h (k := 129) (by norm_num)).2.2
  have v4529 : σ (.n 4529) = ev 69 := by
    rw [← hev 69 (by norm_num)]; exact (vt_eval h (k := 130) (by norm_num)).2.2
  have v4533 : σ (.n 4533) = ev 70 := by
    rw [← hev 70 (by norm_num)]; exact (vt_eval h (k := 131) (by norm_num)).2.2
  have v4550 : σ (.n 4550) = ev 71 := by
    rw [← hev 71 (by norm_num)]; exact (vt_eval h (k := 132) (by norm_num)).2.2
  have v4554 : σ (.n 4554) = ev 72 := by
    rw [← hev 72 (by norm_num)]; exact (vt_eval h (k := 133) (by norm_num)).2.2
  have v4558 : σ (.n 4558) = ev 73 := by
    rw [← hev 73 (by norm_num)]; exact (vt_eval h (k := 134) (by norm_num)).2.2
  have v4562 : σ (.n 4562) = ev 74 := by
    rw [← hev 74 (by norm_num)]; exact (vt_eval h (k := 135) (by norm_num)).2.2
  have v4579 : σ (.n 4579) = ev 75 := by
    rw [← hev 75 (by norm_num)]; exact (vt_eval h (k := 136) (by norm_num)).2.2
  have v4583 : σ (.n 4583) = ev 76 := by
    rw [← hev 76 (by norm_num)]; exact (vt_eval h (k := 137) (by norm_num)).2.2
  have v4587 : σ (.n 4587) = ev 77 := by
    rw [← hev 77 (by norm_num)]; exact (vt_eval h (k := 138) (by norm_num)).2.2
  have v4591 : σ (.n 4591) = ev 78 := by
    rw [← hev 78 (by norm_num)]; exact (vt_eval h (k := 139) (by norm_num)).2.2
  have v4608 : σ (.n 4608) = ev 79 := by
    rw [← hev 79 (by norm_num)]; exact (vt_eval h (k := 140) (by norm_num)).2.2
  have v4612 : σ (.n 4612) = ev 80 := by
    rw [← hev 80 (by norm_num)]; exact (vt_eval h (k := 141) (by norm_num)).2.2
  have v4616 : σ (.n 4616) = ev 81 := by
    rw [← hev 81 (by norm_num)]; exact (vt_eval h (k := 142) (by norm_num)).2.2
  have v4620 : σ (.n 4620) = ev 82 := by
    rw [← hev 82 (by norm_num)]; exact (vt_eval h (k := 143) (by norm_num)).2.2
  have v4637 : σ (.n 4637) = ev 83 := by
    rw [← hev 83 (by norm_num)]; exact (vt_eval h (k := 144) (by norm_num)).2.2
  have v4641 : σ (.n 4641) = ev 84 := by
    rw [← hev 84 (by norm_num)]; exact (vt_eval h (k := 145) (by norm_num)).2.2
  have v4645 : σ (.n 4645) = ev 85 := by
    rw [← hev 85 (by norm_num)]; exact (vt_eval h (k := 146) (by norm_num)).2.2
  have v4649 : σ (.n 4649) = ev 86 := by
    rw [← hev 86 (by norm_num)]; exact (vt_eval h (k := 147) (by norm_num)).2.2
  have v4666 : σ (.n 4666) = ev 87 := by
    rw [← hev 87 (by norm_num)]; exact (vt_eval h (k := 148) (by norm_num)).2.2
  have v4670 : σ (.n 4670) = ev 88 := by
    rw [← hev 88 (by norm_num)]; exact (vt_eval h (k := 149) (by norm_num)).2.2
  have v4674 : σ (.n 4674) = ev 89 := by
    rw [← hev 89 (by norm_num)]; exact (vt_eval h (k := 150) (by norm_num)).2.2
  have v4678 : σ (.n 4678) = ev 90 := by
    rw [← hev 90 (by norm_num)]; exact (vt_eval h (k := 151) (by norm_num)).2.2
  have v4695 : σ (.n 4695) = ev 91 := by
    rw [← hev 91 (by norm_num)]; exact (vt_eval h (k := 152) (by norm_num)).2.2
  simp only [v4695, v4678, v4674, v4670, v4666, v4649, v4645, v4641, v4637, v4620, v4616, v4612, v4608, v4591,
    v4587, v4583, v4579, v4562, v4558, v4554, v4550, v4533, v4529, v4525, v4521, v4504, v4500,
    a5518, a5517, a5516, a5515, a5514, a5513, a5512, a5511, a5510, a5509, a5508, a5507, a5506,
    a5505, a5504, a5503, a5502, a5501, a5500, a5499, a5498, a5497, a5496, a5495, a5494, a5493,
    a5492, a5491, a5490, a5489, a5488, a5487, a5486, a5485, a5484, a5483, a5482, a5481, a5480,
    a5479, a5478, a5477, a5476, a5475, a5474, a5473, a5472, a5471, a5470, a5469, a5468, a5467,
    a5466, a4848, a4847, a4846, a4845, a4844, a4843, a4842, a4841, a4840, a4839, a4838, a4837,
    a4836, a4835, a4834, a4833, a4832, a4831, a4830, a4829, a4828, a4827, a4826, a4825, a4824,
    a4823, a4822]
  simp only [vtSideVal, vtBTerms25, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one]
  ring

end
end LeanVM.Guest.B1.Tables
