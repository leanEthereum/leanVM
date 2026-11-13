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
    σ (.n 5769) =
      vtSideVal [σ (.n 1048), σ (.n 1057), σ (.n 1066), σ (.n 1075), σ (.n 1084), σ (.n 1093), σ (.n 1102),
        σ (.n 1111), σ (.n 1120), σ (.n 1129), σ (.n 1138), σ (.n 1147), σ (.n 1156),
        σ (.n 1165), σ (.n 1174), σ (.n 1183), σ (.n 1192), σ (.n 1201), σ (.n 1210),
        σ (.n 1219), σ (.n 1228), σ (.n 1237), σ (.n 1246), σ (.n 1255), σ (.n 1264),
        σ (.n 1273), σ (.n 1282), σ (.n 1291)]
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
    σ (.n 5882) =
      vtSideVal [σ (.n 1380), σ (.n 1382), σ (.n 1384), σ (.n 1386), σ (.n 1388), σ (.n 1390), σ (.n 1392),
        σ (.n 1394), σ (.n 1396), σ (.n 1398), σ (.n 1400), σ (.n 1402), σ (.n 1404),
        σ (.n 1406), σ (.n 1408), σ (.n 1410), σ (.n 1412), σ (.n 1414), σ (.n 1416),
        σ (.n 1418), σ (.n 1420), σ (.n 1422), σ (.n 1424), σ (.n 1426), σ (.n 1428),
        σ (.n 1430), σ (.n 1432), σ (.n 1434)]
        (σ (.n 14)) W ev vtBTerms15 := by
  have hF0 : σ (.n 5769) =
      vtSideVal [σ (.n 1380), σ (.n 1382), σ (.n 1384), σ (.n 1386), σ (.n 1388), σ (.n 1390), σ (.n 1392),
        σ (.n 1394), σ (.n 1396), σ (.n 1398), σ (.n 1400), σ (.n 1402), σ (.n 1404),
        σ (.n 1406), σ (.n 1408), σ (.n 1410), σ (.n 1412), σ (.n 1414), σ (.n 1416),
        σ (.n 1418), σ (.n 1420), σ (.n 1422), σ (.n 1424), σ (.n 1426), σ (.n 1428),
        σ (.n 1430), σ (.n 1432), σ (.n 1434)]
        (σ (.n 14)) W ev vtBTerms05 := by
    rw [vtPullSels5 h]; exact vtSide05 h hw hev
  have a5458 := h.atomAt 5458 (.add (.n 5882) (.n 5769) (.n 5881)) (by decide +kernel)
  simp only [Atom.Holds] at a5458
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull5, ← hF0, a5458, vtD5_27 h hw hev, vtD5_26 h hw hev, vtD5_25 h hw hev, vtD5_24 h hw hev, vtD5_23 h hw hev,
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
    σ (.n 5937) =
      vtSideVal [σ (.n 1590), σ (.n 1599), σ (.n 1608), σ (.n 1617), σ (.n 1626), σ (.n 1635), σ (.n 1644),
        σ (.n 1653), σ (.n 1662), σ (.n 1671), σ (.n 1680), σ (.n 1689), σ (.n 1698),
        σ (.n 1707), σ (.n 1716), σ (.n 1725), σ (.n 1734), σ (.n 1743), σ (.n 1752),
        σ (.n 1761), σ (.n 1770), σ (.n 1779), σ (.n 1788), σ (.n 1797), σ (.n 1806),
        σ (.n 1815), σ (.n 1824)]
        (0) (fun _ ↦ 1) ev vtBTerms25 := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4817 [
    .atom (.copy (.n 5241) (.n 4495)),
    .atom (.copy (.n 5242) (.n 4499)),
    .atom (.copy (.n 5243) (.n 4516)),
    .atom (.copy (.n 5244) (.n 4520)),
    .atom (.copy (.n 5245) (.n 4524)),
    .atom (.copy (.n 5246) (.n 4528)),
    .atom (.copy (.n 5247) (.n 4545)),
    .atom (.copy (.n 5248) (.n 4549)),
    .atom (.copy (.n 5249) (.n 4553)),
    .atom (.copy (.n 5250) (.n 4557)),
    .atom (.copy (.n 5251) (.n 4574)),
    .atom (.copy (.n 5252) (.n 4578)),
    .atom (.copy (.n 5253) (.n 4582)),
    .atom (.copy (.n 5254) (.n 4586)),
    .atom (.copy (.n 5255) (.n 4603)),
    .atom (.copy (.n 5256) (.n 4607)),
    .atom (.copy (.n 5257) (.n 4611)),
    .atom (.copy (.n 5258) (.n 4615)),
    .atom (.copy (.n 5259) (.n 4632)),
    .atom (.copy (.n 5260) (.n 4636)),
    .atom (.copy (.n 5261) (.n 4640)),
    .atom (.copy (.n 5262) (.n 4644)),
    .atom (.copy (.n 5263) (.n 4661)),
    .atom (.copy (.n 5264) (.n 4665)),
    .atom (.copy (.n 5265) (.n 4669)),
    .atom (.copy (.n 5266) (.n 4673)),
    .atom (.copy (.n 5267) (.n 4690))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4817, a4818, a4819, a4820, a4821, a4822, a4823, a4824, a4825, a4826, a4827, a4828, a4829, a4830,
    a4831, a4832, a4833, a4834, a4835, a4836, a4837, a4838, a4839, a4840, a4841, a4842, a4843, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5461 [
    .atom (.mul (.n 5885) (.n 1590) (.n 5241)),
    .atom (.mul (.n 5886) (.n 1599) (.n 5242)),
    .atom (.add (.n 5887) (.n 5885) (.n 5886)),
    .atom (.mul (.n 5888) (.n 1608) (.n 5243)),
    .atom (.add (.n 5889) (.n 5887) (.n 5888)),
    .atom (.mul (.n 5890) (.n 1617) (.n 5244)),
    .atom (.add (.n 5891) (.n 5889) (.n 5890)),
    .atom (.mul (.n 5892) (.n 1626) (.n 5245)),
    .atom (.add (.n 5893) (.n 5891) (.n 5892)),
    .atom (.mul (.n 5894) (.n 1635) (.n 5246)),
    .atom (.add (.n 5895) (.n 5893) (.n 5894)),
    .atom (.mul (.n 5896) (.n 1644) (.n 5247)),
    .atom (.add (.n 5897) (.n 5895) (.n 5896)),
    .atom (.mul (.n 5898) (.n 1653) (.n 5248)),
    .atom (.add (.n 5899) (.n 5897) (.n 5898)),
    .atom (.mul (.n 5900) (.n 1662) (.n 5249)),
    .atom (.add (.n 5901) (.n 5899) (.n 5900)),
    .atom (.mul (.n 5902) (.n 1671) (.n 5250)),
    .atom (.add (.n 5903) (.n 5901) (.n 5902)),
    .atom (.mul (.n 5904) (.n 1680) (.n 5251)),
    .atom (.add (.n 5905) (.n 5903) (.n 5904)),
    .atom (.mul (.n 5906) (.n 1689) (.n 5252)),
    .atom (.add (.n 5907) (.n 5905) (.n 5906)),
    .atom (.mul (.n 5908) (.n 1698) (.n 5253)),
    .atom (.add (.n 5909) (.n 5907) (.n 5908)),
    .atom (.mul (.n 5910) (.n 1707) (.n 5254)),
    .atom (.add (.n 5911) (.n 5909) (.n 5910)),
    .atom (.mul (.n 5912) (.n 1716) (.n 5255)),
    .atom (.add (.n 5913) (.n 5911) (.n 5912)),
    .atom (.mul (.n 5914) (.n 1725) (.n 5256)),
    .atom (.add (.n 5915) (.n 5913) (.n 5914)),
    .atom (.mul (.n 5916) (.n 1734) (.n 5257)),
    .atom (.add (.n 5917) (.n 5915) (.n 5916)),
    .atom (.mul (.n 5918) (.n 1743) (.n 5258)),
    .atom (.add (.n 5919) (.n 5917) (.n 5918)),
    .atom (.mul (.n 5920) (.n 1752) (.n 5259)),
    .atom (.add (.n 5921) (.n 5919) (.n 5920)),
    .atom (.mul (.n 5922) (.n 1761) (.n 5260)),
    .atom (.add (.n 5923) (.n 5921) (.n 5922)),
    .atom (.mul (.n 5924) (.n 1770) (.n 5261)),
    .atom (.add (.n 5925) (.n 5923) (.n 5924)),
    .atom (.mul (.n 5926) (.n 1779) (.n 5262)),
    .atom (.add (.n 5927) (.n 5925) (.n 5926)),
    .atom (.mul (.n 5928) (.n 1788) (.n 5263)),
    .atom (.add (.n 5929) (.n 5927) (.n 5928)),
    .atom (.mul (.n 5930) (.n 1797) (.n 5264)),
    .atom (.add (.n 5931) (.n 5929) (.n 5930)),
    .atom (.mul (.n 5932) (.n 1806) (.n 5265)),
    .atom (.add (.n 5933) (.n 5931) (.n 5932)),
    .atom (.mul (.n 5934) (.n 1815) (.n 5266)),
    .atom (.add (.n 5935) (.n 5933) (.n 5934)),
    .atom (.mul (.n 5936) (.n 1824) (.n 5267)),
    .atom (.add (.n 5937) (.n 5935) (.n 5936))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5461, a5462, a5463, a5464, a5465, a5466, a5467, a5468, a5469, a5470, a5471, a5472, a5473, a5474,
    a5475, a5476, a5477, a5478, a5479, a5480, a5481, a5482, a5483, a5484, a5485, a5486, a5487,
    a5488, a5489, a5490, a5491, a5492, a5493, a5494, a5495, a5496, a5497, a5498, a5499, a5500,
    a5501, a5502, a5503, a5504, a5505, a5506, a5507, a5508, a5509, a5510, a5511, a5512, a5513, -⟩ := hs1
  have v4495 : σ (.n 4495) = ev 65 := by
    rw [← hev 65 (by norm_num)]; exact (vt_eval h (k := 126) (by norm_num)).2.2
  have v4499 : σ (.n 4499) = ev 66 := by
    rw [← hev 66 (by norm_num)]; exact (vt_eval h (k := 127) (by norm_num)).2.2
  have v4516 : σ (.n 4516) = ev 67 := by
    rw [← hev 67 (by norm_num)]; exact (vt_eval h (k := 128) (by norm_num)).2.2
  have v4520 : σ (.n 4520) = ev 68 := by
    rw [← hev 68 (by norm_num)]; exact (vt_eval h (k := 129) (by norm_num)).2.2
  have v4524 : σ (.n 4524) = ev 69 := by
    rw [← hev 69 (by norm_num)]; exact (vt_eval h (k := 130) (by norm_num)).2.2
  have v4528 : σ (.n 4528) = ev 70 := by
    rw [← hev 70 (by norm_num)]; exact (vt_eval h (k := 131) (by norm_num)).2.2
  have v4545 : σ (.n 4545) = ev 71 := by
    rw [← hev 71 (by norm_num)]; exact (vt_eval h (k := 132) (by norm_num)).2.2
  have v4549 : σ (.n 4549) = ev 72 := by
    rw [← hev 72 (by norm_num)]; exact (vt_eval h (k := 133) (by norm_num)).2.2
  have v4553 : σ (.n 4553) = ev 73 := by
    rw [← hev 73 (by norm_num)]; exact (vt_eval h (k := 134) (by norm_num)).2.2
  have v4557 : σ (.n 4557) = ev 74 := by
    rw [← hev 74 (by norm_num)]; exact (vt_eval h (k := 135) (by norm_num)).2.2
  have v4574 : σ (.n 4574) = ev 75 := by
    rw [← hev 75 (by norm_num)]; exact (vt_eval h (k := 136) (by norm_num)).2.2
  have v4578 : σ (.n 4578) = ev 76 := by
    rw [← hev 76 (by norm_num)]; exact (vt_eval h (k := 137) (by norm_num)).2.2
  have v4582 : σ (.n 4582) = ev 77 := by
    rw [← hev 77 (by norm_num)]; exact (vt_eval h (k := 138) (by norm_num)).2.2
  have v4586 : σ (.n 4586) = ev 78 := by
    rw [← hev 78 (by norm_num)]; exact (vt_eval h (k := 139) (by norm_num)).2.2
  have v4603 : σ (.n 4603) = ev 79 := by
    rw [← hev 79 (by norm_num)]; exact (vt_eval h (k := 140) (by norm_num)).2.2
  have v4607 : σ (.n 4607) = ev 80 := by
    rw [← hev 80 (by norm_num)]; exact (vt_eval h (k := 141) (by norm_num)).2.2
  have v4611 : σ (.n 4611) = ev 81 := by
    rw [← hev 81 (by norm_num)]; exact (vt_eval h (k := 142) (by norm_num)).2.2
  have v4615 : σ (.n 4615) = ev 82 := by
    rw [← hev 82 (by norm_num)]; exact (vt_eval h (k := 143) (by norm_num)).2.2
  have v4632 : σ (.n 4632) = ev 83 := by
    rw [← hev 83 (by norm_num)]; exact (vt_eval h (k := 144) (by norm_num)).2.2
  have v4636 : σ (.n 4636) = ev 84 := by
    rw [← hev 84 (by norm_num)]; exact (vt_eval h (k := 145) (by norm_num)).2.2
  have v4640 : σ (.n 4640) = ev 85 := by
    rw [← hev 85 (by norm_num)]; exact (vt_eval h (k := 146) (by norm_num)).2.2
  have v4644 : σ (.n 4644) = ev 86 := by
    rw [← hev 86 (by norm_num)]; exact (vt_eval h (k := 147) (by norm_num)).2.2
  have v4661 : σ (.n 4661) = ev 87 := by
    rw [← hev 87 (by norm_num)]; exact (vt_eval h (k := 148) (by norm_num)).2.2
  have v4665 : σ (.n 4665) = ev 88 := by
    rw [← hev 88 (by norm_num)]; exact (vt_eval h (k := 149) (by norm_num)).2.2
  have v4669 : σ (.n 4669) = ev 89 := by
    rw [← hev 89 (by norm_num)]; exact (vt_eval h (k := 150) (by norm_num)).2.2
  have v4673 : σ (.n 4673) = ev 90 := by
    rw [← hev 90 (by norm_num)]; exact (vt_eval h (k := 151) (by norm_num)).2.2
  have v4690 : σ (.n 4690) = ev 91 := by
    rw [← hev 91 (by norm_num)]; exact (vt_eval h (k := 152) (by norm_num)).2.2
  simp only [v4690, v4673, v4669, v4665, v4661, v4644, v4640, v4636, v4632, v4615, v4611, v4607, v4603, v4586,
    v4582, v4578, v4574, v4557, v4553, v4549, v4545, v4528, v4524, v4520, v4516, v4499, v4495,
    a5513, a5512, a5511, a5510, a5509, a5508, a5507, a5506, a5505, a5504, a5503, a5502, a5501,
    a5500, a5499, a5498, a5497, a5496, a5495, a5494, a5493, a5492, a5491, a5490, a5489, a5488,
    a5487, a5486, a5485, a5484, a5483, a5482, a5481, a5480, a5479, a5478, a5477, a5476, a5475,
    a5474, a5473, a5472, a5471, a5470, a5469, a5468, a5467, a5466, a5465, a5464, a5463, a5462,
    a5461, a4843, a4842, a4841, a4840, a4839, a4838, a4837, a4836, a4835, a4834, a4833, a4832,
    a4831, a4830, a4829, a4828, a4827, a4826, a4825, a4824, a4823, a4822, a4821, a4820, a4819,
    a4818, a4817]
  simp only [vtSideVal, vtBTerms25, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one]
  ring

end
end LeanVM.Guest.B1.Tables
