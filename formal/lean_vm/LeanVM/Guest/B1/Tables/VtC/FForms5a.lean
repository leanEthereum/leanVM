/-
  LeanVM.Guest.B1.Tables.VtC.FForms5a

  `Vt/FormsT5a.lean` on the window `VtF` (generated: scripts/b1c-vt/gentwins.py).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FEvals
public import LeanVM.Guest.B1.Tables.Vt.FormsT5a

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
theorem vtB05_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 5748) = σ (.n 1151) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5168 [
    .atom (.load (.n 5738) (.n 13) 0),
    .atom (.const (.n 5739) (word 2 0 0)),
    .atom (.mul (.n 5740) (.n 5739) (.n 4437)),
    .atom (.load (.n 5741) (.n 13) 1),
    .atom (.mul (.n 5742) (.n 5741) (.n 5740)),
    .atom (.add (.n 5743) (.n 5738) (.n 5742)),
    .atom (.load (.n 5744) (.n 13) 2),
    .atom (.mul (.n 5745) (.n 5744) (.n 4461)),
    .atom (.add (.n 5746) (.n 5743) (.n 5745)),
    .atom (.add (.n 5747) (.n 14) (.n 5746)),
    .atom (.mul (.n 5748) (.n 1151) (.n 5747))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5168, a5169, a5170, a5171, a5172, a5173, a5174, a5175, a5176, a5177, a5178, -⟩ := hs
  have e5168 := tb_loadHolds_unique a5168 (hw 0 (by norm_num))
  have e5171 := tb_loadHolds_unique a5171 (hw 1 (by norm_num))
  have e5174 := tb_loadHolds_unique a5174 (hw 2 (by norm_num))
  have v4437 : σ (.n 4437) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 67) (by norm_num)).2.2
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have hB : σ (.n 5747) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v4461, v4437, a5177, a5176, a5175, e5174, a5173, a5172, e5171, a5170, a5169, e5168]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5178, hB]

set_option maxRecDepth 10000 in
theorem vtB05_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 5802) = σ (.n 5748) + σ (.n 1160) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([91], 2)], [([], 32)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)], [([7], 1)], [([8], 1)], [([9], 1)], [([10], 1)], [([11], 1)], [([12], 1)], [([13], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5179 [
    .atom (.load (.n 5749) (.n 13) 0),
    .atom (.const (.n 5750) (word 4 0 0)),
    .atom (.mul (.n 5751) (.n 5749) (.n 5750)),
    .atom (.load (.n 5752) (.n 13) 1),
    .atom (.mul (.n 5753) (.n 5752) (.n 4437)),
    .atom (.add (.n 5754) (.n 5751) (.n 5753)),
    .atom (.const (.n 5755) (word 2 0 0)),
    .atom (.mul (.n 5756) (.n 5755) (.n 5737)),
    .atom (.load (.n 5757) (.n 13) 2),
    .atom (.mul (.n 5758) (.n 5757) (.n 5756)),
    .atom (.add (.n 5759) (.n 5754) (.n 5758)),
    .atom (.load (.n 5760) (.n 13) 3),
    .atom (.const (.n 5761) (word 32 0 0)),
    .atom (.mul (.n 5762) (.n 5760) (.n 5761)),
    .atom (.add (.n 5763) (.n 5759) (.n 5762)),
    .atom (.load (.n 5764) (.n 13) 4),
    .atom (.mul (.n 5765) (.n 5764) (.n 4472)),
    .atom (.add (.n 5766) (.n 5763) (.n 5765)),
    .atom (.load (.n 5767) (.n 13) 5),
    .atom (.mul (.n 5768) (.n 5767) (.n 4483)),
    .atom (.add (.n 5769) (.n 5766) (.n 5768)),
    .atom (.load (.n 5770) (.n 13) 6),
    .atom (.mul (.n 5771) (.n 5770) (.n 4494)),
    .atom (.add (.n 5772) (.n 5769) (.n 5771)),
    .atom (.load (.n 5773) (.n 13) 7),
    .atom (.mul (.n 5774) (.n 5773) (.n 4518)),
    .atom (.add (.n 5775) (.n 5772) (.n 5774)),
    .atom (.load (.n 5776) (.n 13) 8),
    .atom (.mul (.n 5777) (.n 5776) (.n 4529)),
    .atom (.add (.n 5778) (.n 5775) (.n 5777)),
    .atom (.load (.n 5779) (.n 13) 9),
    .atom (.mul (.n 5780) (.n 5779) (.n 4540)),
    .atom (.add (.n 5781) (.n 5778) (.n 5780)),
    .atom (.load (.n 5782) (.n 13) 10),
    .atom (.mul (.n 5783) (.n 5782) (.n 4551)),
    .atom (.add (.n 5784) (.n 5781) (.n 5783)),
    .atom (.load (.n 5785) (.n 13) 11),
    .atom (.mul (.n 5786) (.n 5785) (.n 4575)),
    .atom (.add (.n 5787) (.n 5784) (.n 5786)),
    .atom (.load (.n 5788) (.n 13) 12),
    .atom (.mul (.n 5789) (.n 5788) (.n 4586)),
    .atom (.add (.n 5790) (.n 5787) (.n 5789)),
    .atom (.load (.n 5791) (.n 13) 13),
    .atom (.mul (.n 5792) (.n 5791) (.n 4597)),
    .atom (.add (.n 5793) (.n 5790) (.n 5792)),
    .atom (.load (.n 5794) (.n 13) 14),
    .atom (.mul (.n 5795) (.n 5794) (.n 4608)),
    .atom (.add (.n 5796) (.n 5793) (.n 5795)),
    .atom (.load (.n 5797) (.n 13) 15),
    .atom (.mul (.n 5798) (.n 5797) (.n 4632)),
    .atom (.add (.n 5799) (.n 5796) (.n 5798)),
    .atom (.add (.n 5800) (.n 14) (.n 5799)),
    .atom (.mul (.n 5801) (.n 1160) (.n 5800)),
    .atom (.add (.n 5802) (.n 5748) (.n 5801))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5179, a5180, a5181, a5182, a5183, a5184, a5185, a5186, a5187, a5188, a5189, a5190, a5191, a5192,
    a5193, a5194, a5195, a5196, a5197, a5198, a5199, a5200, a5201, a5202, a5203, a5204, a5205,
    a5206, a5207, a5208, a5209, a5210, a5211, a5212, a5213, a5214, a5215, a5216, a5217, a5218,
    a5219, a5220, a5221, a5222, a5223, a5224, a5225, a5226, a5227, a5228, a5229, a5230, a5231,
    a5232, -⟩ := hs
  have e5179 := tb_loadHolds_unique a5179 (hw 0 (by norm_num))
  have e5182 := tb_loadHolds_unique a5182 (hw 1 (by norm_num))
  have e5187 := tb_loadHolds_unique a5187 (hw 2 (by norm_num))
  have e5190 := tb_loadHolds_unique a5190 (hw 3 (by norm_num))
  have e5194 := tb_loadHolds_unique a5194 (hw 4 (by norm_num))
  have e5197 := tb_loadHolds_unique a5197 (hw 5 (by norm_num))
  have e5200 := tb_loadHolds_unique a5200 (hw 6 (by norm_num))
  have e5203 := tb_loadHolds_unique a5203 (hw 7 (by norm_num))
  have e5206 := tb_loadHolds_unique a5206 (hw 8 (by norm_num))
  have e5209 := tb_loadHolds_unique a5209 (hw 9 (by norm_num))
  have e5212 := tb_loadHolds_unique a5212 (hw 10 (by norm_num))
  have e5215 := tb_loadHolds_unique a5215 (hw 11 (by norm_num))
  have e5218 := tb_loadHolds_unique a5218 (hw 12 (by norm_num))
  have e5221 := tb_loadHolds_unique a5221 (hw 13 (by norm_num))
  have e5224 := tb_loadHolds_unique a5224 (hw 14 (by norm_num))
  have e5227 := tb_loadHolds_unique a5227 (hw 15 (by norm_num))
  have v4437 : σ (.n 4437) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 67) (by norm_num)).2.2
  have v4472 : σ (.n 4472) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 69) (by norm_num)).2.2
  have v4483 : σ (.n 4483) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 70) (by norm_num)).2.2
  have v4494 : σ (.n 4494) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 71) (by norm_num)).2.2
  have v4518 : σ (.n 4518) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 72) (by norm_num)).2.2
  have v4529 : σ (.n 4529) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 73) (by norm_num)).2.2
  have v4540 : σ (.n 4540) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4551 : σ (.n 4551) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 75) (by norm_num)).2.2
  have v4575 : σ (.n 4575) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2
  have v4586 : σ (.n 4586) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 77) (by norm_num)).2.2
  have v4597 : σ (.n 4597) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 78) (by norm_num)).2.2
  have v4608 : σ (.n 4608) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_evalF h (k := 79) (by norm_num)).2.2
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 80) (by norm_num)).2.2
  have v5737 : σ (.n 5737) = ev 91 := by
    rw [← hev 91 (by norm_num)]; exact (vt_evalF h (k := 158) (by norm_num)).2.2
  have hB : σ (.n 5800) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([91], 2)], [([], 32)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)], [([7], 1)], [([8], 1)], [([9], 1)], [([10], 1)], [([11], 1)], [([12], 1)], [([13], 1)]] := by
    simp only [v5737, v4632, v4608, v4597, v4586, v4575, v4551, v4540, v4529, v4518, v4494, v4483, v4472,
      v4437, a5230, a5229, a5228, e5227, a5226, a5225, e5224, a5223, a5222, e5221, a5220,
      a5219, e5218, a5217, a5216, e5215, a5214, a5213, e5212, a5211, a5210, e5209, a5208,
      a5207, e5206, a5205, a5204, e5203, a5202, a5201, e5200, a5199, a5198, e5197, a5196,
      a5195, e5194, a5193, a5192, a5191, e5190, a5189, a5188, e5187, a5186, a5185, a5184,
      a5183, e5182, a5181, a5180, e5179]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5232, a5231, hB]

set_option maxRecDepth 10000 in
theorem vtB05_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 5835) = σ (.n 5802) + σ (.n 1169) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([65], 2)], [([15], 1), ([10, 15], 1), ([10, 14], 1)], [([16], 1), ([10, 16], 1), ([10, 15], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5233 [
    .atom (.load (.n 5803) (.n 13) 0),
    .atom (.const (.n 5804) (word 2 0 0)),
    .atom (.mul (.n 5805) (.n 5803) (.n 5804)),
    .atom (.mul (.n 5806) (.n 4461) (.n 4472)),
    .atom (.load (.n 5807) (.n 13) 1),
    .atom (.mul (.n 5808) (.n 5807) (.n 5806)),
    .atom (.add (.n 5809) (.n 5805) (.n 5808)),
    .atom (.const (.n 5810) (word 2 0 0)),
    .atom (.mul (.n 5811) (.n 5810) (.n 5373)),
    .atom (.load (.n 5812) (.n 13) 2),
    .atom (.mul (.n 5813) (.n 5812) (.n 5811)),
    .atom (.add (.n 5814) (.n 5809) (.n 5813)),
    .atom (.mul (.n 5815) (.n 4586) (.n 4654)),
    .atom (.add (.n 5816) (.n 4654) (.n 5815)),
    .atom (.mul (.n 5817) (.n 4586) (.n 4643)),
    .atom (.add (.n 5818) (.n 5816) (.n 5817)),
    .atom (.load (.n 5819) (.n 13) 3),
    .atom (.mul (.n 5820) (.n 5819) (.n 5818)),
    .atom (.add (.n 5821) (.n 5814) (.n 5820)),
    .atom (.mul (.n 5822) (.n 4586) (.n 4665)),
    .atom (.add (.n 5823) (.n 4665) (.n 5822)),
    .atom (.mul (.n 5824) (.n 4586) (.n 4654)),
    .atom (.add (.n 5825) (.n 5823) (.n 5824)),
    .atom (.load (.n 5826) (.n 13) 4),
    .atom (.mul (.n 5827) (.n 5826) (.n 5825)),
    .atom (.add (.n 5828) (.n 5821) (.n 5827)),
    .atom (.load (.n 5829) (.n 13) 5),
    .atom (.const (.n 5830) (word 0 0 0)),
    .atom (.mul (.n 5831) (.n 5829) (.n 5830)),
    .atom (.add (.n 5832) (.n 5828) (.n 5831)),
    .atom (.add (.n 5833) (.n 14) (.n 5832)),
    .atom (.mul (.n 5834) (.n 1169) (.n 5833)),
    .atom (.add (.n 5835) (.n 5802) (.n 5834))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5233, a5234, a5235, a5236, a5237, a5238, a5239, a5240, a5241, a5242, a5243, a5244, a5245, a5246,
    a5247, a5248, a5249, a5250, a5251, a5252, a5253, a5254, a5255, a5256, a5257, a5258, a5259,
    a5260, a5261, a5262, a5263, a5264, a5265, -⟩ := hs
  have e5233 := tb_loadHolds_unique a5233 (hw 0 (by norm_num))
  have e5237 := tb_loadHolds_unique a5237 (hw 1 (by norm_num))
  have e5242 := tb_loadHolds_unique a5242 (hw 2 (by norm_num))
  have e5249 := tb_loadHolds_unique a5249 (hw 3 (by norm_num))
  have e5256 := tb_loadHolds_unique a5256 (hw 4 (by norm_num))
  have e5259 := tb_loadHolds_unique a5259 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4472 : σ (.n 4472) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 69) (by norm_num)).2.2
  have v4586 : σ (.n 4586) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 77) (by norm_num)).2.2
  have v4643 : σ (.n 4643) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_evalF h (k := 81) (by norm_num)).2.2
  have v4654 : σ (.n 4654) = ev 15 := by
    rw [← hev 15 (by norm_num)]; exact (vt_evalF h (k := 82) (by norm_num)).2.2
  have v4665 : σ (.n 4665) = ev 16 := by
    rw [← hev 16 (by norm_num)]; exact (vt_evalF h (k := 83) (by norm_num)).2.2
  have v5373 : σ (.n 5373) = ev 65 := by
    rw [← hev 65 (by norm_num)]; exact (vt_evalF h (k := 132) (by norm_num)).2.2
  have hB : σ (.n 5833) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([65], 2)], [([15], 1), ([10, 15], 1), ([10, 14], 1)], [([16], 1), ([10, 16], 1), ([10, 15], 1)], [([], 0)]] := by
    simp only [v5373, v4665, v4654, v4643, v4586, v4472, v4461, a5263, a5262, a5261, a5260, e5259, a5258,
      a5257, e5256, a5255, a5254, a5253, a5252, a5251, a5250, e5249, a5248, a5247, a5246,
      a5245, a5244, a5243, e5242, a5241, a5240, a5239, a5238, e5237, a5236, a5235, a5234,
      e5233]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5265, a5264, hB]

set_option maxRecDepth 10000 in
theorem vtB05_3F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 5868) = σ (.n 5835) + σ (.n 1178) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 3], 1)], [([66], 2)], [([17], 1), ([10, 17], 1), ([10, 16], 1)], [([18], 1), ([10, 18], 1), ([10, 17], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5266 [
    .atom (.load (.n 5836) (.n 13) 0),
    .atom (.const (.n 5837) (word 2 0 0)),
    .atom (.mul (.n 5838) (.n 5836) (.n 5837)),
    .atom (.mul (.n 5839) (.n 4461) (.n 4483)),
    .atom (.load (.n 5840) (.n 13) 1),
    .atom (.mul (.n 5841) (.n 5840) (.n 5839)),
    .atom (.add (.n 5842) (.n 5838) (.n 5841)),
    .atom (.const (.n 5843) (word 2 0 0)),
    .atom (.mul (.n 5844) (.n 5843) (.n 5384)),
    .atom (.load (.n 5845) (.n 13) 2),
    .atom (.mul (.n 5846) (.n 5845) (.n 5844)),
    .atom (.add (.n 5847) (.n 5842) (.n 5846)),
    .atom (.mul (.n 5848) (.n 4586) (.n 4689)),
    .atom (.add (.n 5849) (.n 4689) (.n 5848)),
    .atom (.mul (.n 5850) (.n 4586) (.n 4665)),
    .atom (.add (.n 5851) (.n 5849) (.n 5850)),
    .atom (.load (.n 5852) (.n 13) 3),
    .atom (.mul (.n 5853) (.n 5852) (.n 5851)),
    .atom (.add (.n 5854) (.n 5847) (.n 5853)),
    .atom (.mul (.n 5855) (.n 4586) (.n 4700)),
    .atom (.add (.n 5856) (.n 4700) (.n 5855)),
    .atom (.mul (.n 5857) (.n 4586) (.n 4689)),
    .atom (.add (.n 5858) (.n 5856) (.n 5857)),
    .atom (.load (.n 5859) (.n 13) 4),
    .atom (.mul (.n 5860) (.n 5859) (.n 5858)),
    .atom (.add (.n 5861) (.n 5854) (.n 5860)),
    .atom (.load (.n 5862) (.n 13) 5),
    .atom (.const (.n 5863) (word 0 0 0)),
    .atom (.mul (.n 5864) (.n 5862) (.n 5863)),
    .atom (.add (.n 5865) (.n 5861) (.n 5864)),
    .atom (.add (.n 5866) (.n 14) (.n 5865)),
    .atom (.mul (.n 5867) (.n 1178) (.n 5866)),
    .atom (.add (.n 5868) (.n 5835) (.n 5867))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5266, a5267, a5268, a5269, a5270, a5271, a5272, a5273, a5274, a5275, a5276, a5277, a5278, a5279,
    a5280, a5281, a5282, a5283, a5284, a5285, a5286, a5287, a5288, a5289, a5290, a5291, a5292,
    a5293, a5294, a5295, a5296, a5297, a5298, -⟩ := hs
  have e5266 := tb_loadHolds_unique a5266 (hw 0 (by norm_num))
  have e5270 := tb_loadHolds_unique a5270 (hw 1 (by norm_num))
  have e5275 := tb_loadHolds_unique a5275 (hw 2 (by norm_num))
  have e5282 := tb_loadHolds_unique a5282 (hw 3 (by norm_num))
  have e5289 := tb_loadHolds_unique a5289 (hw 4 (by norm_num))
  have e5292 := tb_loadHolds_unique a5292 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4483 : σ (.n 4483) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 70) (by norm_num)).2.2
  have v4586 : σ (.n 4586) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 77) (by norm_num)).2.2
  have v4665 : σ (.n 4665) = ev 16 := by
    rw [← hev 16 (by norm_num)]; exact (vt_evalF h (k := 83) (by norm_num)).2.2
  have v4689 : σ (.n 4689) = ev 17 := by
    rw [← hev 17 (by norm_num)]; exact (vt_evalF h (k := 84) (by norm_num)).2.2
  have v4700 : σ (.n 4700) = ev 18 := by
    rw [← hev 18 (by norm_num)]; exact (vt_evalF h (k := 85) (by norm_num)).2.2
  have v5384 : σ (.n 5384) = ev 66 := by
    rw [← hev 66 (by norm_num)]; exact (vt_evalF h (k := 133) (by norm_num)).2.2
  have hB : σ (.n 5866) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 3], 1)], [([66], 2)], [([17], 1), ([10, 17], 1), ([10, 16], 1)], [([18], 1), ([10, 18], 1), ([10, 17], 1)], [([], 0)]] := by
    simp only [v5384, v4700, v4689, v4665, v4586, v4483, v4461, a5296, a5295, a5294, a5293, e5292, a5291,
      a5290, e5289, a5288, a5287, a5286, a5285, a5284, a5283, e5282, a5281, a5280, a5279,
      a5278, a5277, a5276, e5275, a5274, a5273, a5272, a5271, e5270, a5269, a5268, a5267,
      e5266]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5298, a5297, hB]

set_option maxRecDepth 10000 in
theorem vtB05_4F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 5901) = σ (.n 5868) + σ (.n 1187) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 4], 1)], [([67], 2)], [([19], 1), ([10, 19], 1), ([10, 18], 1)], [([20], 1), ([10, 20], 1), ([10, 19], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5299 [
    .atom (.load (.n 5869) (.n 13) 0),
    .atom (.const (.n 5870) (word 2 0 0)),
    .atom (.mul (.n 5871) (.n 5869) (.n 5870)),
    .atom (.mul (.n 5872) (.n 4461) (.n 4494)),
    .atom (.load (.n 5873) (.n 13) 1),
    .atom (.mul (.n 5874) (.n 5873) (.n 5872)),
    .atom (.add (.n 5875) (.n 5871) (.n 5874)),
    .atom (.const (.n 5876) (word 2 0 0)),
    .atom (.mul (.n 5877) (.n 5876) (.n 5395)),
    .atom (.load (.n 5878) (.n 13) 2),
    .atom (.mul (.n 5879) (.n 5878) (.n 5877)),
    .atom (.add (.n 5880) (.n 5875) (.n 5879)),
    .atom (.mul (.n 5881) (.n 4586) (.n 4711)),
    .atom (.add (.n 5882) (.n 4711) (.n 5881)),
    .atom (.mul (.n 5883) (.n 4586) (.n 4700)),
    .atom (.add (.n 5884) (.n 5882) (.n 5883)),
    .atom (.load (.n 5885) (.n 13) 3),
    .atom (.mul (.n 5886) (.n 5885) (.n 5884)),
    .atom (.add (.n 5887) (.n 5880) (.n 5886)),
    .atom (.mul (.n 5888) (.n 4586) (.n 4722)),
    .atom (.add (.n 5889) (.n 4722) (.n 5888)),
    .atom (.mul (.n 5890) (.n 4586) (.n 4711)),
    .atom (.add (.n 5891) (.n 5889) (.n 5890)),
    .atom (.load (.n 5892) (.n 13) 4),
    .atom (.mul (.n 5893) (.n 5892) (.n 5891)),
    .atom (.add (.n 5894) (.n 5887) (.n 5893)),
    .atom (.load (.n 5895) (.n 13) 5),
    .atom (.const (.n 5896) (word 0 0 0)),
    .atom (.mul (.n 5897) (.n 5895) (.n 5896)),
    .atom (.add (.n 5898) (.n 5894) (.n 5897)),
    .atom (.add (.n 5899) (.n 14) (.n 5898)),
    .atom (.mul (.n 5900) (.n 1187) (.n 5899)),
    .atom (.add (.n 5901) (.n 5868) (.n 5900))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5299, a5300, a5301, a5302, a5303, a5304, a5305, a5306, a5307, a5308, a5309, a5310, a5311, a5312,
    a5313, a5314, a5315, a5316, a5317, a5318, a5319, a5320, a5321, a5322, a5323, a5324, a5325,
    a5326, a5327, a5328, a5329, a5330, a5331, -⟩ := hs
  have e5299 := tb_loadHolds_unique a5299 (hw 0 (by norm_num))
  have e5303 := tb_loadHolds_unique a5303 (hw 1 (by norm_num))
  have e5308 := tb_loadHolds_unique a5308 (hw 2 (by norm_num))
  have e5315 := tb_loadHolds_unique a5315 (hw 3 (by norm_num))
  have e5322 := tb_loadHolds_unique a5322 (hw 4 (by norm_num))
  have e5325 := tb_loadHolds_unique a5325 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4494 : σ (.n 4494) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 71) (by norm_num)).2.2
  have v4586 : σ (.n 4586) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 77) (by norm_num)).2.2
  have v4700 : σ (.n 4700) = ev 18 := by
    rw [← hev 18 (by norm_num)]; exact (vt_evalF h (k := 85) (by norm_num)).2.2
  have v4711 : σ (.n 4711) = ev 19 := by
    rw [← hev 19 (by norm_num)]; exact (vt_evalF h (k := 86) (by norm_num)).2.2
  have v4722 : σ (.n 4722) = ev 20 := by
    rw [← hev 20 (by norm_num)]; exact (vt_evalF h (k := 87) (by norm_num)).2.2
  have v5395 : σ (.n 5395) = ev 67 := by
    rw [← hev 67 (by norm_num)]; exact (vt_evalF h (k := 134) (by norm_num)).2.2
  have hB : σ (.n 5899) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 4], 1)], [([67], 2)], [([19], 1), ([10, 19], 1), ([10, 18], 1)], [([20], 1), ([10, 20], 1), ([10, 19], 1)], [([], 0)]] := by
    simp only [v5395, v4722, v4711, v4700, v4586, v4494, v4461, a5329, a5328, a5327, a5326, e5325, a5324,
      a5323, e5322, a5321, a5320, a5319, a5318, a5317, a5316, e5315, a5314, a5313, a5312,
      a5311, a5310, a5309, e5308, a5307, a5306, a5305, a5304, e5303, a5302, a5301, a5300,
      e5299]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5331, a5330, hB]

set_option maxRecDepth 10000 in
theorem vtB05_5F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 5934) = σ (.n 5901) + σ (.n 1196) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 5], 1)], [([68], 2)], [([21], 1), ([10, 21], 1), ([10, 20], 1)], [([22], 1), ([10, 22], 1), ([10, 21], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5332 [
    .atom (.load (.n 5902) (.n 13) 0),
    .atom (.const (.n 5903) (word 2 0 0)),
    .atom (.mul (.n 5904) (.n 5902) (.n 5903)),
    .atom (.mul (.n 5905) (.n 4461) (.n 4518)),
    .atom (.load (.n 5906) (.n 13) 1),
    .atom (.mul (.n 5907) (.n 5906) (.n 5905)),
    .atom (.add (.n 5908) (.n 5904) (.n 5907)),
    .atom (.const (.n 5909) (word 2 0 0)),
    .atom (.mul (.n 5910) (.n 5909) (.n 5406)),
    .atom (.load (.n 5911) (.n 13) 2),
    .atom (.mul (.n 5912) (.n 5911) (.n 5910)),
    .atom (.add (.n 5913) (.n 5908) (.n 5912)),
    .atom (.mul (.n 5914) (.n 4586) (.n 4746)),
    .atom (.add (.n 5915) (.n 4746) (.n 5914)),
    .atom (.mul (.n 5916) (.n 4586) (.n 4722)),
    .atom (.add (.n 5917) (.n 5915) (.n 5916)),
    .atom (.load (.n 5918) (.n 13) 3),
    .atom (.mul (.n 5919) (.n 5918) (.n 5917)),
    .atom (.add (.n 5920) (.n 5913) (.n 5919)),
    .atom (.mul (.n 5921) (.n 4586) (.n 4757)),
    .atom (.add (.n 5922) (.n 4757) (.n 5921)),
    .atom (.mul (.n 5923) (.n 4586) (.n 4746)),
    .atom (.add (.n 5924) (.n 5922) (.n 5923)),
    .atom (.load (.n 5925) (.n 13) 4),
    .atom (.mul (.n 5926) (.n 5925) (.n 5924)),
    .atom (.add (.n 5927) (.n 5920) (.n 5926)),
    .atom (.load (.n 5928) (.n 13) 5),
    .atom (.const (.n 5929) (word 0 0 0)),
    .atom (.mul (.n 5930) (.n 5928) (.n 5929)),
    .atom (.add (.n 5931) (.n 5927) (.n 5930)),
    .atom (.add (.n 5932) (.n 14) (.n 5931)),
    .atom (.mul (.n 5933) (.n 1196) (.n 5932)),
    .atom (.add (.n 5934) (.n 5901) (.n 5933))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5332, a5333, a5334, a5335, a5336, a5337, a5338, a5339, a5340, a5341, a5342, a5343, a5344, a5345,
    a5346, a5347, a5348, a5349, a5350, a5351, a5352, a5353, a5354, a5355, a5356, a5357, a5358,
    a5359, a5360, a5361, a5362, a5363, a5364, -⟩ := hs
  have e5332 := tb_loadHolds_unique a5332 (hw 0 (by norm_num))
  have e5336 := tb_loadHolds_unique a5336 (hw 1 (by norm_num))
  have e5341 := tb_loadHolds_unique a5341 (hw 2 (by norm_num))
  have e5348 := tb_loadHolds_unique a5348 (hw 3 (by norm_num))
  have e5355 := tb_loadHolds_unique a5355 (hw 4 (by norm_num))
  have e5358 := tb_loadHolds_unique a5358 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4518 : σ (.n 4518) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 72) (by norm_num)).2.2
  have v4586 : σ (.n 4586) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 77) (by norm_num)).2.2
  have v4722 : σ (.n 4722) = ev 20 := by
    rw [← hev 20 (by norm_num)]; exact (vt_evalF h (k := 87) (by norm_num)).2.2
  have v4746 : σ (.n 4746) = ev 21 := by
    rw [← hev 21 (by norm_num)]; exact (vt_evalF h (k := 88) (by norm_num)).2.2
  have v4757 : σ (.n 4757) = ev 22 := by
    rw [← hev 22 (by norm_num)]; exact (vt_evalF h (k := 89) (by norm_num)).2.2
  have v5406 : σ (.n 5406) = ev 68 := by
    rw [← hev 68 (by norm_num)]; exact (vt_evalF h (k := 135) (by norm_num)).2.2
  have hB : σ (.n 5932) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 5], 1)], [([68], 2)], [([21], 1), ([10, 21], 1), ([10, 20], 1)], [([22], 1), ([10, 22], 1), ([10, 21], 1)], [([], 0)]] := by
    simp only [v5406, v4757, v4746, v4722, v4586, v4518, v4461, a5362, a5361, a5360, a5359, e5358, a5357,
      a5356, e5355, a5354, a5353, a5352, a5351, a5350, a5349, e5348, a5347, a5346, a5345,
      a5344, a5343, a5342, e5341, a5340, a5339, a5338, a5337, e5336, a5335, a5334, a5333,
      e5332]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5364, a5363, hB]

set_option maxRecDepth 10000 in
theorem vtB05_6F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 5967) = σ (.n 5934) + σ (.n 1205) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 6], 1)], [([69], 2)], [([23], 1), ([10, 23], 1), ([10, 22], 1)], [([24], 1), ([10, 24], 1), ([10, 23], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5365 [
    .atom (.load (.n 5935) (.n 13) 0),
    .atom (.const (.n 5936) (word 2 0 0)),
    .atom (.mul (.n 5937) (.n 5935) (.n 5936)),
    .atom (.mul (.n 5938) (.n 4461) (.n 4529)),
    .atom (.load (.n 5939) (.n 13) 1),
    .atom (.mul (.n 5940) (.n 5939) (.n 5938)),
    .atom (.add (.n 5941) (.n 5937) (.n 5940)),
    .atom (.const (.n 5942) (word 2 0 0)),
    .atom (.mul (.n 5943) (.n 5942) (.n 5430)),
    .atom (.load (.n 5944) (.n 13) 2),
    .atom (.mul (.n 5945) (.n 5944) (.n 5943)),
    .atom (.add (.n 5946) (.n 5941) (.n 5945)),
    .atom (.mul (.n 5947) (.n 4586) (.n 4768)),
    .atom (.add (.n 5948) (.n 4768) (.n 5947)),
    .atom (.mul (.n 5949) (.n 4586) (.n 4757)),
    .atom (.add (.n 5950) (.n 5948) (.n 5949)),
    .atom (.load (.n 5951) (.n 13) 3),
    .atom (.mul (.n 5952) (.n 5951) (.n 5950)),
    .atom (.add (.n 5953) (.n 5946) (.n 5952)),
    .atom (.mul (.n 5954) (.n 4586) (.n 4779)),
    .atom (.add (.n 5955) (.n 4779) (.n 5954)),
    .atom (.mul (.n 5956) (.n 4586) (.n 4768)),
    .atom (.add (.n 5957) (.n 5955) (.n 5956)),
    .atom (.load (.n 5958) (.n 13) 4),
    .atom (.mul (.n 5959) (.n 5958) (.n 5957)),
    .atom (.add (.n 5960) (.n 5953) (.n 5959)),
    .atom (.load (.n 5961) (.n 13) 5),
    .atom (.const (.n 5962) (word 0 0 0)),
    .atom (.mul (.n 5963) (.n 5961) (.n 5962)),
    .atom (.add (.n 5964) (.n 5960) (.n 5963)),
    .atom (.add (.n 5965) (.n 14) (.n 5964)),
    .atom (.mul (.n 5966) (.n 1205) (.n 5965)),
    .atom (.add (.n 5967) (.n 5934) (.n 5966))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5365, a5366, a5367, a5368, a5369, a5370, a5371, a5372, a5373, a5374, a5375, a5376, a5377, a5378,
    a5379, a5380, a5381, a5382, a5383, a5384, a5385, a5386, a5387, a5388, a5389, a5390, a5391,
    a5392, a5393, a5394, a5395, a5396, a5397, -⟩ := hs
  have e5365 := tb_loadHolds_unique a5365 (hw 0 (by norm_num))
  have e5369 := tb_loadHolds_unique a5369 (hw 1 (by norm_num))
  have e5374 := tb_loadHolds_unique a5374 (hw 2 (by norm_num))
  have e5381 := tb_loadHolds_unique a5381 (hw 3 (by norm_num))
  have e5388 := tb_loadHolds_unique a5388 (hw 4 (by norm_num))
  have e5391 := tb_loadHolds_unique a5391 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4529 : σ (.n 4529) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 73) (by norm_num)).2.2
  have v4586 : σ (.n 4586) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 77) (by norm_num)).2.2
  have v4757 : σ (.n 4757) = ev 22 := by
    rw [← hev 22 (by norm_num)]; exact (vt_evalF h (k := 89) (by norm_num)).2.2
  have v4768 : σ (.n 4768) = ev 23 := by
    rw [← hev 23 (by norm_num)]; exact (vt_evalF h (k := 90) (by norm_num)).2.2
  have v4779 : σ (.n 4779) = ev 24 := by
    rw [← hev 24 (by norm_num)]; exact (vt_evalF h (k := 91) (by norm_num)).2.2
  have v5430 : σ (.n 5430) = ev 69 := by
    rw [← hev 69 (by norm_num)]; exact (vt_evalF h (k := 136) (by norm_num)).2.2
  have hB : σ (.n 5965) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 6], 1)], [([69], 2)], [([23], 1), ([10, 23], 1), ([10, 22], 1)], [([24], 1), ([10, 24], 1), ([10, 23], 1)], [([], 0)]] := by
    simp only [v5430, v4779, v4768, v4757, v4586, v4529, v4461, a5395, a5394, a5393, a5392, e5391, a5390,
      a5389, e5388, a5387, a5386, a5385, a5384, a5383, a5382, e5381, a5380, a5379, a5378,
      a5377, a5376, a5375, e5374, a5373, a5372, a5371, a5370, e5369, a5368, a5367, a5366,
      e5365]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5397, a5396, hB]

set_option maxRecDepth 10000 in
theorem vtB05_7F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6002) = σ (.n 5967) + σ (.n 1214) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 6], 2)], [([70], 2)], [([25], 1), ([10, 25], 1), ([10, 24], 1)], [([26], 1), ([10, 26], 1), ([10, 25], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5398 [
    .atom (.load (.n 5968) (.n 13) 0),
    .atom (.const (.n 5969) (word 2 0 0)),
    .atom (.mul (.n 5970) (.n 5968) (.n 5969)),
    .atom (.const (.n 5971) (word 2 0 0)),
    .atom (.mul (.n 5972) (.n 4461) (.n 4529)),
    .atom (.mul (.n 5973) (.n 5971) (.n 5972)),
    .atom (.load (.n 5974) (.n 13) 1),
    .atom (.mul (.n 5975) (.n 5974) (.n 5973)),
    .atom (.add (.n 5976) (.n 5970) (.n 5975)),
    .atom (.const (.n 5977) (word 2 0 0)),
    .atom (.mul (.n 5978) (.n 5977) (.n 5441)),
    .atom (.load (.n 5979) (.n 13) 2),
    .atom (.mul (.n 5980) (.n 5979) (.n 5978)),
    .atom (.add (.n 5981) (.n 5976) (.n 5980)),
    .atom (.mul (.n 5982) (.n 4586) (.n 4803)),
    .atom (.add (.n 5983) (.n 4803) (.n 5982)),
    .atom (.mul (.n 5984) (.n 4586) (.n 4779)),
    .atom (.add (.n 5985) (.n 5983) (.n 5984)),
    .atom (.load (.n 5986) (.n 13) 3),
    .atom (.mul (.n 5987) (.n 5986) (.n 5985)),
    .atom (.add (.n 5988) (.n 5981) (.n 5987)),
    .atom (.mul (.n 5989) (.n 4586) (.n 4814)),
    .atom (.add (.n 5990) (.n 4814) (.n 5989)),
    .atom (.mul (.n 5991) (.n 4586) (.n 4803)),
    .atom (.add (.n 5992) (.n 5990) (.n 5991)),
    .atom (.load (.n 5993) (.n 13) 4),
    .atom (.mul (.n 5994) (.n 5993) (.n 5992)),
    .atom (.add (.n 5995) (.n 5988) (.n 5994)),
    .atom (.load (.n 5996) (.n 13) 5),
    .atom (.const (.n 5997) (word 0 0 0)),
    .atom (.mul (.n 5998) (.n 5996) (.n 5997)),
    .atom (.add (.n 5999) (.n 5995) (.n 5998)),
    .atom (.add (.n 6000) (.n 14) (.n 5999)),
    .atom (.mul (.n 6001) (.n 1214) (.n 6000)),
    .atom (.add (.n 6002) (.n 5967) (.n 6001))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5398, a5399, a5400, a5401, a5402, a5403, a5404, a5405, a5406, a5407, a5408, a5409, a5410, a5411,
    a5412, a5413, a5414, a5415, a5416, a5417, a5418, a5419, a5420, a5421, a5422, a5423, a5424,
    a5425, a5426, a5427, a5428, a5429, a5430, a5431, a5432, -⟩ := hs
  have e5398 := tb_loadHolds_unique a5398 (hw 0 (by norm_num))
  have e5404 := tb_loadHolds_unique a5404 (hw 1 (by norm_num))
  have e5409 := tb_loadHolds_unique a5409 (hw 2 (by norm_num))
  have e5416 := tb_loadHolds_unique a5416 (hw 3 (by norm_num))
  have e5423 := tb_loadHolds_unique a5423 (hw 4 (by norm_num))
  have e5426 := tb_loadHolds_unique a5426 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4529 : σ (.n 4529) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 73) (by norm_num)).2.2
  have v4586 : σ (.n 4586) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 77) (by norm_num)).2.2
  have v4779 : σ (.n 4779) = ev 24 := by
    rw [← hev 24 (by norm_num)]; exact (vt_evalF h (k := 91) (by norm_num)).2.2
  have v4803 : σ (.n 4803) = ev 25 := by
    rw [← hev 25 (by norm_num)]; exact (vt_evalF h (k := 92) (by norm_num)).2.2
  have v4814 : σ (.n 4814) = ev 26 := by
    rw [← hev 26 (by norm_num)]; exact (vt_evalF h (k := 93) (by norm_num)).2.2
  have v5441 : σ (.n 5441) = ev 70 := by
    rw [← hev 70 (by norm_num)]; exact (vt_evalF h (k := 137) (by norm_num)).2.2
  have hB : σ (.n 6000) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 6], 2)], [([70], 2)], [([25], 1), ([10, 25], 1), ([10, 24], 1)], [([26], 1), ([10, 26], 1), ([10, 25], 1)], [([], 0)]] := by
    simp only [v5441, v4814, v4803, v4779, v4586, v4529, v4461, a5430, a5429, a5428, a5427, e5426, a5425,
      a5424, e5423, a5422, a5421, a5420, a5419, a5418, a5417, e5416, a5415, a5414, a5413,
      a5412, a5411, a5410, e5409, a5408, a5407, a5406, a5405, e5404, a5403, a5402, a5401,
      a5400, a5399, e5398]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5432, a5431, hB]

set_option maxRecDepth 10000 in
theorem vtB05_8F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6037) = σ (.n 6002) + σ (.n 1223) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 6], 4)], [([71], 2)], [([27], 1), ([10, 27], 1), ([10, 26], 1)], [([28], 1), ([10, 28], 1), ([10, 27], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5433 [
    .atom (.load (.n 6003) (.n 13) 0),
    .atom (.const (.n 6004) (word 2 0 0)),
    .atom (.mul (.n 6005) (.n 6003) (.n 6004)),
    .atom (.const (.n 6006) (word 4 0 0)),
    .atom (.mul (.n 6007) (.n 4461) (.n 4529)),
    .atom (.mul (.n 6008) (.n 6006) (.n 6007)),
    .atom (.load (.n 6009) (.n 13) 1),
    .atom (.mul (.n 6010) (.n 6009) (.n 6008)),
    .atom (.add (.n 6011) (.n 6005) (.n 6010)),
    .atom (.const (.n 6012) (word 2 0 0)),
    .atom (.mul (.n 6013) (.n 6012) (.n 5452)),
    .atom (.load (.n 6014) (.n 13) 2),
    .atom (.mul (.n 6015) (.n 6014) (.n 6013)),
    .atom (.add (.n 6016) (.n 6011) (.n 6015)),
    .atom (.mul (.n 6017) (.n 4586) (.n 4825)),
    .atom (.add (.n 6018) (.n 4825) (.n 6017)),
    .atom (.mul (.n 6019) (.n 4586) (.n 4814)),
    .atom (.add (.n 6020) (.n 6018) (.n 6019)),
    .atom (.load (.n 6021) (.n 13) 3),
    .atom (.mul (.n 6022) (.n 6021) (.n 6020)),
    .atom (.add (.n 6023) (.n 6016) (.n 6022)),
    .atom (.mul (.n 6024) (.n 4586) (.n 4836)),
    .atom (.add (.n 6025) (.n 4836) (.n 6024)),
    .atom (.mul (.n 6026) (.n 4586) (.n 4825)),
    .atom (.add (.n 6027) (.n 6025) (.n 6026)),
    .atom (.load (.n 6028) (.n 13) 4),
    .atom (.mul (.n 6029) (.n 6028) (.n 6027)),
    .atom (.add (.n 6030) (.n 6023) (.n 6029)),
    .atom (.load (.n 6031) (.n 13) 5),
    .atom (.const (.n 6032) (word 0 0 0)),
    .atom (.mul (.n 6033) (.n 6031) (.n 6032)),
    .atom (.add (.n 6034) (.n 6030) (.n 6033)),
    .atom (.add (.n 6035) (.n 14) (.n 6034)),
    .atom (.mul (.n 6036) (.n 1223) (.n 6035)),
    .atom (.add (.n 6037) (.n 6002) (.n 6036))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5433, a5434, a5435, a5436, a5437, a5438, a5439, a5440, a5441, a5442, a5443, a5444, a5445, a5446,
    a5447, a5448, a5449, a5450, a5451, a5452, a5453, a5454, a5455, a5456, a5457, a5458, a5459,
    a5460, a5461, a5462, a5463, a5464, a5465, a5466, a5467, -⟩ := hs
  have e5433 := tb_loadHolds_unique a5433 (hw 0 (by norm_num))
  have e5439 := tb_loadHolds_unique a5439 (hw 1 (by norm_num))
  have e5444 := tb_loadHolds_unique a5444 (hw 2 (by norm_num))
  have e5451 := tb_loadHolds_unique a5451 (hw 3 (by norm_num))
  have e5458 := tb_loadHolds_unique a5458 (hw 4 (by norm_num))
  have e5461 := tb_loadHolds_unique a5461 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4529 : σ (.n 4529) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 73) (by norm_num)).2.2
  have v4586 : σ (.n 4586) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 77) (by norm_num)).2.2
  have v4814 : σ (.n 4814) = ev 26 := by
    rw [← hev 26 (by norm_num)]; exact (vt_evalF h (k := 93) (by norm_num)).2.2
  have v4825 : σ (.n 4825) = ev 27 := by
    rw [← hev 27 (by norm_num)]; exact (vt_evalF h (k := 94) (by norm_num)).2.2
  have v4836 : σ (.n 4836) = ev 28 := by
    rw [← hev 28 (by norm_num)]; exact (vt_evalF h (k := 95) (by norm_num)).2.2
  have v5452 : σ (.n 5452) = ev 71 := by
    rw [← hev 71 (by norm_num)]; exact (vt_evalF h (k := 138) (by norm_num)).2.2
  have hB : σ (.n 6035) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 6], 4)], [([71], 2)], [([27], 1), ([10, 27], 1), ([10, 26], 1)], [([28], 1), ([10, 28], 1), ([10, 27], 1)], [([], 0)]] := by
    simp only [v5452, v4836, v4825, v4814, v4586, v4529, v4461, a5465, a5464, a5463, a5462, e5461, a5460,
      a5459, e5458, a5457, a5456, a5455, a5454, a5453, a5452, e5451, a5450, a5449, a5448,
      a5447, a5446, a5445, e5444, a5443, a5442, a5441, a5440, e5439, a5438, a5437, a5436,
      a5435, a5434, e5433]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5467, a5466, hB]

set_option maxRecDepth 10000 in
theorem vtB05_9F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6072) = σ (.n 6037) + σ (.n 1232) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 6], 8)], [([72], 2)], [([29], 1), ([10, 29], 1), ([10, 28], 1)], [([30], 1), ([10, 30], 1), ([10, 29], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5468 [
    .atom (.load (.n 6038) (.n 13) 0),
    .atom (.const (.n 6039) (word 2 0 0)),
    .atom (.mul (.n 6040) (.n 6038) (.n 6039)),
    .atom (.const (.n 6041) (word 8 0 0)),
    .atom (.mul (.n 6042) (.n 4461) (.n 4529)),
    .atom (.mul (.n 6043) (.n 6041) (.n 6042)),
    .atom (.load (.n 6044) (.n 13) 1),
    .atom (.mul (.n 6045) (.n 6044) (.n 6043)),
    .atom (.add (.n 6046) (.n 6040) (.n 6045)),
    .atom (.const (.n 6047) (word 2 0 0)),
    .atom (.mul (.n 6048) (.n 6047) (.n 5463)),
    .atom (.load (.n 6049) (.n 13) 2),
    .atom (.mul (.n 6050) (.n 6049) (.n 6048)),
    .atom (.add (.n 6051) (.n 6046) (.n 6050)),
    .atom (.mul (.n 6052) (.n 4586) (.n 4860)),
    .atom (.add (.n 6053) (.n 4860) (.n 6052)),
    .atom (.mul (.n 6054) (.n 4586) (.n 4836)),
    .atom (.add (.n 6055) (.n 6053) (.n 6054)),
    .atom (.load (.n 6056) (.n 13) 3),
    .atom (.mul (.n 6057) (.n 6056) (.n 6055)),
    .atom (.add (.n 6058) (.n 6051) (.n 6057)),
    .atom (.mul (.n 6059) (.n 4586) (.n 4871)),
    .atom (.add (.n 6060) (.n 4871) (.n 6059)),
    .atom (.mul (.n 6061) (.n 4586) (.n 4860)),
    .atom (.add (.n 6062) (.n 6060) (.n 6061)),
    .atom (.load (.n 6063) (.n 13) 4),
    .atom (.mul (.n 6064) (.n 6063) (.n 6062)),
    .atom (.add (.n 6065) (.n 6058) (.n 6064)),
    .atom (.load (.n 6066) (.n 13) 5),
    .atom (.const (.n 6067) (word 0 0 0)),
    .atom (.mul (.n 6068) (.n 6066) (.n 6067)),
    .atom (.add (.n 6069) (.n 6065) (.n 6068)),
    .atom (.add (.n 6070) (.n 14) (.n 6069)),
    .atom (.mul (.n 6071) (.n 1232) (.n 6070)),
    .atom (.add (.n 6072) (.n 6037) (.n 6071))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5468, a5469, a5470, a5471, a5472, a5473, a5474, a5475, a5476, a5477, a5478, a5479, a5480, a5481,
    a5482, a5483, a5484, a5485, a5486, a5487, a5488, a5489, a5490, a5491, a5492, a5493, a5494,
    a5495, a5496, a5497, a5498, a5499, a5500, a5501, a5502, -⟩ := hs
  have e5468 := tb_loadHolds_unique a5468 (hw 0 (by norm_num))
  have e5474 := tb_loadHolds_unique a5474 (hw 1 (by norm_num))
  have e5479 := tb_loadHolds_unique a5479 (hw 2 (by norm_num))
  have e5486 := tb_loadHolds_unique a5486 (hw 3 (by norm_num))
  have e5493 := tb_loadHolds_unique a5493 (hw 4 (by norm_num))
  have e5496 := tb_loadHolds_unique a5496 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4529 : σ (.n 4529) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 73) (by norm_num)).2.2
  have v4586 : σ (.n 4586) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 77) (by norm_num)).2.2
  have v4836 : σ (.n 4836) = ev 28 := by
    rw [← hev 28 (by norm_num)]; exact (vt_evalF h (k := 95) (by norm_num)).2.2
  have v4860 : σ (.n 4860) = ev 29 := by
    rw [← hev 29 (by norm_num)]; exact (vt_evalF h (k := 96) (by norm_num)).2.2
  have v4871 : σ (.n 4871) = ev 30 := by
    rw [← hev 30 (by norm_num)]; exact (vt_evalF h (k := 97) (by norm_num)).2.2
  have v5463 : σ (.n 5463) = ev 72 := by
    rw [← hev 72 (by norm_num)]; exact (vt_evalF h (k := 139) (by norm_num)).2.2
  have hB : σ (.n 6070) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 6], 8)], [([72], 2)], [([29], 1), ([10, 29], 1), ([10, 28], 1)], [([30], 1), ([10, 30], 1), ([10, 29], 1)], [([], 0)]] := by
    simp only [v5463, v4871, v4860, v4836, v4586, v4529, v4461, a5500, a5499, a5498, a5497, e5496, a5495,
      a5494, e5493, a5492, a5491, a5490, a5489, a5488, a5487, e5486, a5485, a5484, a5483,
      a5482, a5481, a5480, e5479, a5478, a5477, a5476, a5475, e5474, a5473, a5472, a5471,
      a5470, a5469, e5468]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5502, a5501, hB]

set_option maxRecDepth 10000 in
theorem vtB05_10F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6105) = σ (.n 6072) + σ (.n 1241) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 7], 1)], [([73], 2)], [([31], 1), ([10, 31], 1), ([10, 30], 1)], [([14], 1), ([10, 14], 1), ([10, 31], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5503 [
    .atom (.load (.n 6073) (.n 13) 0),
    .atom (.const (.n 6074) (word 2 0 0)),
    .atom (.mul (.n 6075) (.n 6073) (.n 6074)),
    .atom (.mul (.n 6076) (.n 4461) (.n 4540)),
    .atom (.load (.n 6077) (.n 13) 1),
    .atom (.mul (.n 6078) (.n 6077) (.n 6076)),
    .atom (.add (.n 6079) (.n 6075) (.n 6078)),
    .atom (.const (.n 6080) (word 2 0 0)),
    .atom (.mul (.n 6081) (.n 6080) (.n 5487)),
    .atom (.load (.n 6082) (.n 13) 2),
    .atom (.mul (.n 6083) (.n 6082) (.n 6081)),
    .atom (.add (.n 6084) (.n 6079) (.n 6083)),
    .atom (.mul (.n 6085) (.n 4586) (.n 4882)),
    .atom (.add (.n 6086) (.n 4882) (.n 6085)),
    .atom (.mul (.n 6087) (.n 4586) (.n 4871)),
    .atom (.add (.n 6088) (.n 6086) (.n 6087)),
    .atom (.load (.n 6089) (.n 13) 3),
    .atom (.mul (.n 6090) (.n 6089) (.n 6088)),
    .atom (.add (.n 6091) (.n 6084) (.n 6090)),
    .atom (.mul (.n 6092) (.n 4586) (.n 4643)),
    .atom (.add (.n 6093) (.n 4643) (.n 6092)),
    .atom (.mul (.n 6094) (.n 4586) (.n 4882)),
    .atom (.add (.n 6095) (.n 6093) (.n 6094)),
    .atom (.load (.n 6096) (.n 13) 4),
    .atom (.mul (.n 6097) (.n 6096) (.n 6095)),
    .atom (.add (.n 6098) (.n 6091) (.n 6097)),
    .atom (.load (.n 6099) (.n 13) 5),
    .atom (.const (.n 6100) (word 0 0 0)),
    .atom (.mul (.n 6101) (.n 6099) (.n 6100)),
    .atom (.add (.n 6102) (.n 6098) (.n 6101)),
    .atom (.add (.n 6103) (.n 14) (.n 6102)),
    .atom (.mul (.n 6104) (.n 1241) (.n 6103)),
    .atom (.add (.n 6105) (.n 6072) (.n 6104))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5503, a5504, a5505, a5506, a5507, a5508, a5509, a5510, a5511, a5512, a5513, a5514, a5515, a5516,
    a5517, a5518, a5519, a5520, a5521, a5522, a5523, a5524, a5525, a5526, a5527, a5528, a5529,
    a5530, a5531, a5532, a5533, a5534, a5535, -⟩ := hs
  have e5503 := tb_loadHolds_unique a5503 (hw 0 (by norm_num))
  have e5507 := tb_loadHolds_unique a5507 (hw 1 (by norm_num))
  have e5512 := tb_loadHolds_unique a5512 (hw 2 (by norm_num))
  have e5519 := tb_loadHolds_unique a5519 (hw 3 (by norm_num))
  have e5526 := tb_loadHolds_unique a5526 (hw 4 (by norm_num))
  have e5529 := tb_loadHolds_unique a5529 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4540 : σ (.n 4540) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4586 : σ (.n 4586) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 77) (by norm_num)).2.2
  have v4643 : σ (.n 4643) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_evalF h (k := 81) (by norm_num)).2.2
  have v4871 : σ (.n 4871) = ev 30 := by
    rw [← hev 30 (by norm_num)]; exact (vt_evalF h (k := 97) (by norm_num)).2.2
  have v4882 : σ (.n 4882) = ev 31 := by
    rw [← hev 31 (by norm_num)]; exact (vt_evalF h (k := 98) (by norm_num)).2.2
  have v5487 : σ (.n 5487) = ev 73 := by
    rw [← hev 73 (by norm_num)]; exact (vt_evalF h (k := 140) (by norm_num)).2.2
  have hB : σ (.n 6103) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 7], 1)], [([73], 2)], [([31], 1), ([10, 31], 1), ([10, 30], 1)], [([14], 1), ([10, 14], 1), ([10, 31], 1)], [([], 0)]] := by
    simp only [v5487, v4882, v4871, v4643, v4586, v4540, v4461, a5533, a5532, a5531, a5530, e5529, a5528,
      a5527, e5526, a5525, a5524, a5523, a5522, a5521, a5520, e5519, a5518, a5517, a5516,
      a5515, a5514, a5513, e5512, a5511, a5510, a5509, a5508, e5507, a5506, a5505, a5504,
      e5503]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5535, a5534, hB]

set_option maxRecDepth 10000 in
theorem vtB05_11F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6130) = σ (.n 6105) + σ (.n 1250) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 8], 1)], [([74], 2)], [([32], 1)], [([33], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5536 [
    .atom (.load (.n 6106) (.n 13) 0),
    .atom (.const (.n 6107) (word 2 0 0)),
    .atom (.mul (.n 6108) (.n 6106) (.n 6107)),
    .atom (.mul (.n 6109) (.n 4461) (.n 4551)),
    .atom (.load (.n 6110) (.n 13) 1),
    .atom (.mul (.n 6111) (.n 6110) (.n 6109)),
    .atom (.add (.n 6112) (.n 6108) (.n 6111)),
    .atom (.const (.n 6113) (word 2 0 0)),
    .atom (.mul (.n 6114) (.n 6113) (.n 5498)),
    .atom (.load (.n 6115) (.n 13) 2),
    .atom (.mul (.n 6116) (.n 6115) (.n 6114)),
    .atom (.add (.n 6117) (.n 6112) (.n 6116)),
    .atom (.load (.n 6118) (.n 13) 3),
    .atom (.mul (.n 6119) (.n 6118) (.n 4893)),
    .atom (.add (.n 6120) (.n 6117) (.n 6119)),
    .atom (.load (.n 6121) (.n 13) 4),
    .atom (.mul (.n 6122) (.n 6121) (.n 4917)),
    .atom (.add (.n 6123) (.n 6120) (.n 6122)),
    .atom (.load (.n 6124) (.n 13) 5),
    .atom (.const (.n 6125) (word 0 0 0)),
    .atom (.mul (.n 6126) (.n 6124) (.n 6125)),
    .atom (.add (.n 6127) (.n 6123) (.n 6126)),
    .atom (.add (.n 6128) (.n 14) (.n 6127)),
    .atom (.mul (.n 6129) (.n 1250) (.n 6128)),
    .atom (.add (.n 6130) (.n 6105) (.n 6129))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5536, a5537, a5538, a5539, a5540, a5541, a5542, a5543, a5544, a5545, a5546, a5547, a5548, a5549,
    a5550, a5551, a5552, a5553, a5554, a5555, a5556, a5557, a5558, a5559, a5560, -⟩ := hs
  have e5536 := tb_loadHolds_unique a5536 (hw 0 (by norm_num))
  have e5540 := tb_loadHolds_unique a5540 (hw 1 (by norm_num))
  have e5545 := tb_loadHolds_unique a5545 (hw 2 (by norm_num))
  have e5548 := tb_loadHolds_unique a5548 (hw 3 (by norm_num))
  have e5551 := tb_loadHolds_unique a5551 (hw 4 (by norm_num))
  have e5554 := tb_loadHolds_unique a5554 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4551 : σ (.n 4551) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 75) (by norm_num)).2.2
  have v4893 : σ (.n 4893) = ev 32 := by
    rw [← hev 32 (by norm_num)]; exact (vt_evalF h (k := 99) (by norm_num)).2.2
  have v4917 : σ (.n 4917) = ev 33 := by
    rw [← hev 33 (by norm_num)]; exact (vt_evalF h (k := 100) (by norm_num)).2.2
  have v5498 : σ (.n 5498) = ev 74 := by
    rw [← hev 74 (by norm_num)]; exact (vt_evalF h (k := 141) (by norm_num)).2.2
  have hB : σ (.n 6128) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 8], 1)], [([74], 2)], [([32], 1)], [([33], 1)], [([], 0)]] := by
    simp only [v5498, v4917, v4893, v4551, v4461, a5558, a5557, a5556, a5555, e5554, a5553, a5552, e5551,
      a5550, a5549, e5548, a5547, a5546, e5545, a5544, a5543, a5542, a5541, e5540, a5539,
      a5538, a5537, e5536]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5560, a5559, hB]

set_option maxRecDepth 10000 in
theorem vtB05_12F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6157) = σ (.n 6130) + σ (.n 1259) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 8], 2)], [([75], 2)], [([34], 1)], [([35], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5561 [
    .atom (.load (.n 6131) (.n 13) 0),
    .atom (.const (.n 6132) (word 2 0 0)),
    .atom (.mul (.n 6133) (.n 6131) (.n 6132)),
    .atom (.const (.n 6134) (word 2 0 0)),
    .atom (.mul (.n 6135) (.n 4461) (.n 4551)),
    .atom (.mul (.n 6136) (.n 6134) (.n 6135)),
    .atom (.load (.n 6137) (.n 13) 1),
    .atom (.mul (.n 6138) (.n 6137) (.n 6136)),
    .atom (.add (.n 6139) (.n 6133) (.n 6138)),
    .atom (.const (.n 6140) (word 2 0 0)),
    .atom (.mul (.n 6141) (.n 6140) (.n 5509)),
    .atom (.load (.n 6142) (.n 13) 2),
    .atom (.mul (.n 6143) (.n 6142) (.n 6141)),
    .atom (.add (.n 6144) (.n 6139) (.n 6143)),
    .atom (.load (.n 6145) (.n 13) 3),
    .atom (.mul (.n 6146) (.n 6145) (.n 4928)),
    .atom (.add (.n 6147) (.n 6144) (.n 6146)),
    .atom (.load (.n 6148) (.n 13) 4),
    .atom (.mul (.n 6149) (.n 6148) (.n 4939)),
    .atom (.add (.n 6150) (.n 6147) (.n 6149)),
    .atom (.load (.n 6151) (.n 13) 5),
    .atom (.const (.n 6152) (word 0 0 0)),
    .atom (.mul (.n 6153) (.n 6151) (.n 6152)),
    .atom (.add (.n 6154) (.n 6150) (.n 6153)),
    .atom (.add (.n 6155) (.n 14) (.n 6154)),
    .atom (.mul (.n 6156) (.n 1259) (.n 6155)),
    .atom (.add (.n 6157) (.n 6130) (.n 6156))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5561, a5562, a5563, a5564, a5565, a5566, a5567, a5568, a5569, a5570, a5571, a5572, a5573, a5574,
    a5575, a5576, a5577, a5578, a5579, a5580, a5581, a5582, a5583, a5584, a5585, a5586, a5587, -⟩ := hs
  have e5561 := tb_loadHolds_unique a5561 (hw 0 (by norm_num))
  have e5567 := tb_loadHolds_unique a5567 (hw 1 (by norm_num))
  have e5572 := tb_loadHolds_unique a5572 (hw 2 (by norm_num))
  have e5575 := tb_loadHolds_unique a5575 (hw 3 (by norm_num))
  have e5578 := tb_loadHolds_unique a5578 (hw 4 (by norm_num))
  have e5581 := tb_loadHolds_unique a5581 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4551 : σ (.n 4551) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 75) (by norm_num)).2.2
  have v4928 : σ (.n 4928) = ev 34 := by
    rw [← hev 34 (by norm_num)]; exact (vt_evalF h (k := 101) (by norm_num)).2.2
  have v4939 : σ (.n 4939) = ev 35 := by
    rw [← hev 35 (by norm_num)]; exact (vt_evalF h (k := 102) (by norm_num)).2.2
  have v5509 : σ (.n 5509) = ev 75 := by
    rw [← hev 75 (by norm_num)]; exact (vt_evalF h (k := 142) (by norm_num)).2.2
  have hB : σ (.n 6155) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 8], 2)], [([75], 2)], [([34], 1)], [([35], 1)], [([], 0)]] := by
    simp only [v5509, v4939, v4928, v4551, v4461, a5585, a5584, a5583, a5582, e5581, a5580, a5579, e5578,
      a5577, a5576, e5575, a5574, a5573, e5572, a5571, a5570, a5569, a5568, e5567, a5566,
      a5565, a5564, a5563, a5562, e5561]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5587, a5586, hB]

set_option maxRecDepth 10000 in
theorem vtB05_13F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6184) = σ (.n 6157) + σ (.n 1268) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 8], 4)], [([76], 2)], [([36], 1)], [([37], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5588 [
    .atom (.load (.n 6158) (.n 13) 0),
    .atom (.const (.n 6159) (word 2 0 0)),
    .atom (.mul (.n 6160) (.n 6158) (.n 6159)),
    .atom (.const (.n 6161) (word 4 0 0)),
    .atom (.mul (.n 6162) (.n 4461) (.n 4551)),
    .atom (.mul (.n 6163) (.n 6161) (.n 6162)),
    .atom (.load (.n 6164) (.n 13) 1),
    .atom (.mul (.n 6165) (.n 6164) (.n 6163)),
    .atom (.add (.n 6166) (.n 6160) (.n 6165)),
    .atom (.const (.n 6167) (word 2 0 0)),
    .atom (.mul (.n 6168) (.n 6167) (.n 5520)),
    .atom (.load (.n 6169) (.n 13) 2),
    .atom (.mul (.n 6170) (.n 6169) (.n 6168)),
    .atom (.add (.n 6171) (.n 6166) (.n 6170)),
    .atom (.load (.n 6172) (.n 13) 3),
    .atom (.mul (.n 6173) (.n 6172) (.n 4950)),
    .atom (.add (.n 6174) (.n 6171) (.n 6173)),
    .atom (.load (.n 6175) (.n 13) 4),
    .atom (.mul (.n 6176) (.n 6175) (.n 4974)),
    .atom (.add (.n 6177) (.n 6174) (.n 6176)),
    .atom (.load (.n 6178) (.n 13) 5),
    .atom (.const (.n 6179) (word 0 0 0)),
    .atom (.mul (.n 6180) (.n 6178) (.n 6179)),
    .atom (.add (.n 6181) (.n 6177) (.n 6180)),
    .atom (.add (.n 6182) (.n 14) (.n 6181)),
    .atom (.mul (.n 6183) (.n 1268) (.n 6182)),
    .atom (.add (.n 6184) (.n 6157) (.n 6183))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5588, a5589, a5590, a5591, a5592, a5593, a5594, a5595, a5596, a5597, a5598, a5599, a5600, a5601,
    a5602, a5603, a5604, a5605, a5606, a5607, a5608, a5609, a5610, a5611, a5612, a5613, a5614, -⟩ := hs
  have e5588 := tb_loadHolds_unique a5588 (hw 0 (by norm_num))
  have e5594 := tb_loadHolds_unique a5594 (hw 1 (by norm_num))
  have e5599 := tb_loadHolds_unique a5599 (hw 2 (by norm_num))
  have e5602 := tb_loadHolds_unique a5602 (hw 3 (by norm_num))
  have e5605 := tb_loadHolds_unique a5605 (hw 4 (by norm_num))
  have e5608 := tb_loadHolds_unique a5608 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4551 : σ (.n 4551) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 75) (by norm_num)).2.2
  have v4950 : σ (.n 4950) = ev 36 := by
    rw [← hev 36 (by norm_num)]; exact (vt_evalF h (k := 103) (by norm_num)).2.2
  have v4974 : σ (.n 4974) = ev 37 := by
    rw [← hev 37 (by norm_num)]; exact (vt_evalF h (k := 104) (by norm_num)).2.2
  have v5520 : σ (.n 5520) = ev 76 := by
    rw [← hev 76 (by norm_num)]; exact (vt_evalF h (k := 143) (by norm_num)).2.2
  have hB : σ (.n 6182) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 8], 4)], [([76], 2)], [([36], 1)], [([37], 1)], [([], 0)]] := by
    simp only [v5520, v4974, v4950, v4551, v4461, a5612, a5611, a5610, a5609, e5608, a5607, a5606, e5605,
      a5604, a5603, e5602, a5601, a5600, e5599, a5598, a5597, a5596, a5595, e5594, a5593,
      a5592, a5591, a5590, a5589, e5588]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5614, a5613, hB]

set_option maxRecDepth 10000 in
theorem vtB05_14F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6211) = σ (.n 6184) + σ (.n 1277) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 8], 8)], [([77], 2)], [([38], 1)], [([39], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5615 [
    .atom (.load (.n 6185) (.n 13) 0),
    .atom (.const (.n 6186) (word 2 0 0)),
    .atom (.mul (.n 6187) (.n 6185) (.n 6186)),
    .atom (.const (.n 6188) (word 8 0 0)),
    .atom (.mul (.n 6189) (.n 4461) (.n 4551)),
    .atom (.mul (.n 6190) (.n 6188) (.n 6189)),
    .atom (.load (.n 6191) (.n 13) 1),
    .atom (.mul (.n 6192) (.n 6191) (.n 6190)),
    .atom (.add (.n 6193) (.n 6187) (.n 6192)),
    .atom (.const (.n 6194) (word 2 0 0)),
    .atom (.mul (.n 6195) (.n 6194) (.n 5544)),
    .atom (.load (.n 6196) (.n 13) 2),
    .atom (.mul (.n 6197) (.n 6196) (.n 6195)),
    .atom (.add (.n 6198) (.n 6193) (.n 6197)),
    .atom (.load (.n 6199) (.n 13) 3),
    .atom (.mul (.n 6200) (.n 6199) (.n 4985)),
    .atom (.add (.n 6201) (.n 6198) (.n 6200)),
    .atom (.load (.n 6202) (.n 13) 4),
    .atom (.mul (.n 6203) (.n 6202) (.n 4996)),
    .atom (.add (.n 6204) (.n 6201) (.n 6203)),
    .atom (.load (.n 6205) (.n 13) 5),
    .atom (.const (.n 6206) (word 0 0 0)),
    .atom (.mul (.n 6207) (.n 6205) (.n 6206)),
    .atom (.add (.n 6208) (.n 6204) (.n 6207)),
    .atom (.add (.n 6209) (.n 14) (.n 6208)),
    .atom (.mul (.n 6210) (.n 1277) (.n 6209)),
    .atom (.add (.n 6211) (.n 6184) (.n 6210))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5615, a5616, a5617, a5618, a5619, a5620, a5621, a5622, a5623, a5624, a5625, a5626, a5627, a5628,
    a5629, a5630, a5631, a5632, a5633, a5634, a5635, a5636, a5637, a5638, a5639, a5640, a5641, -⟩ := hs
  have e5615 := tb_loadHolds_unique a5615 (hw 0 (by norm_num))
  have e5621 := tb_loadHolds_unique a5621 (hw 1 (by norm_num))
  have e5626 := tb_loadHolds_unique a5626 (hw 2 (by norm_num))
  have e5629 := tb_loadHolds_unique a5629 (hw 3 (by norm_num))
  have e5632 := tb_loadHolds_unique a5632 (hw 4 (by norm_num))
  have e5635 := tb_loadHolds_unique a5635 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4551 : σ (.n 4551) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 75) (by norm_num)).2.2
  have v4985 : σ (.n 4985) = ev 38 := by
    rw [← hev 38 (by norm_num)]; exact (vt_evalF h (k := 105) (by norm_num)).2.2
  have v4996 : σ (.n 4996) = ev 39 := by
    rw [← hev 39 (by norm_num)]; exact (vt_evalF h (k := 106) (by norm_num)).2.2
  have v5544 : σ (.n 5544) = ev 77 := by
    rw [← hev 77 (by norm_num)]; exact (vt_evalF h (k := 144) (by norm_num)).2.2
  have hB : σ (.n 6209) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 8], 8)], [([77], 2)], [([38], 1)], [([39], 1)], [([], 0)]] := by
    simp only [v5544, v4996, v4985, v4551, v4461, a5639, a5638, a5637, a5636, e5635, a5634, a5633, e5632,
      a5631, a5630, e5629, a5628, a5627, e5626, a5625, a5624, a5623, a5622, e5621, a5620,
      a5619, a5618, a5617, a5616, e5615]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5641, a5640, hB]

set_option maxRecDepth 10000 in
theorem vtB05_15F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6242) = σ (.n 6211) + σ (.n 1286) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 1)], [([78], 2)], [([40], 1), ([11, 40], 1)], [([41], 1), ([11, 41], 1), ([11, 40], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5642 [
    .atom (.load (.n 6212) (.n 13) 0),
    .atom (.const (.n 6213) (word 2 0 0)),
    .atom (.mul (.n 6214) (.n 6212) (.n 6213)),
    .atom (.mul (.n 6215) (.n 4461) (.n 4575)),
    .atom (.load (.n 6216) (.n 13) 1),
    .atom (.mul (.n 6217) (.n 6216) (.n 6215)),
    .atom (.add (.n 6218) (.n 6214) (.n 6217)),
    .atom (.const (.n 6219) (word 2 0 0)),
    .atom (.mul (.n 6220) (.n 6219) (.n 5555)),
    .atom (.load (.n 6221) (.n 13) 2),
    .atom (.mul (.n 6222) (.n 6221) (.n 6220)),
    .atom (.add (.n 6223) (.n 6218) (.n 6222)),
    .atom (.mul (.n 6224) (.n 4597) (.n 5007)),
    .atom (.add (.n 6225) (.n 5007) (.n 6224)),
    .atom (.load (.n 6226) (.n 13) 3),
    .atom (.mul (.n 6227) (.n 6226) (.n 6225)),
    .atom (.add (.n 6228) (.n 6223) (.n 6227)),
    .atom (.mul (.n 6229) (.n 4597) (.n 5031)),
    .atom (.add (.n 6230) (.n 5031) (.n 6229)),
    .atom (.mul (.n 6231) (.n 4597) (.n 5007)),
    .atom (.add (.n 6232) (.n 6230) (.n 6231)),
    .atom (.load (.n 6233) (.n 13) 4),
    .atom (.mul (.n 6234) (.n 6233) (.n 6232)),
    .atom (.add (.n 6235) (.n 6228) (.n 6234)),
    .atom (.load (.n 6236) (.n 13) 5),
    .atom (.const (.n 6237) (word 0 0 0)),
    .atom (.mul (.n 6238) (.n 6236) (.n 6237)),
    .atom (.add (.n 6239) (.n 6235) (.n 6238)),
    .atom (.add (.n 6240) (.n 14) (.n 6239)),
    .atom (.mul (.n 6241) (.n 1286) (.n 6240)),
    .atom (.add (.n 6242) (.n 6211) (.n 6241))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5642, a5643, a5644, a5645, a5646, a5647, a5648, a5649, a5650, a5651, a5652, a5653, a5654, a5655,
    a5656, a5657, a5658, a5659, a5660, a5661, a5662, a5663, a5664, a5665, a5666, a5667, a5668,
    a5669, a5670, a5671, a5672, -⟩ := hs
  have e5642 := tb_loadHolds_unique a5642 (hw 0 (by norm_num))
  have e5646 := tb_loadHolds_unique a5646 (hw 1 (by norm_num))
  have e5651 := tb_loadHolds_unique a5651 (hw 2 (by norm_num))
  have e5656 := tb_loadHolds_unique a5656 (hw 3 (by norm_num))
  have e5663 := tb_loadHolds_unique a5663 (hw 4 (by norm_num))
  have e5666 := tb_loadHolds_unique a5666 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4575 : σ (.n 4575) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2
  have v4597 : σ (.n 4597) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 78) (by norm_num)).2.2
  have v5007 : σ (.n 5007) = ev 40 := by
    rw [← hev 40 (by norm_num)]; exact (vt_evalF h (k := 107) (by norm_num)).2.2
  have v5031 : σ (.n 5031) = ev 41 := by
    rw [← hev 41 (by norm_num)]; exact (vt_evalF h (k := 108) (by norm_num)).2.2
  have v5555 : σ (.n 5555) = ev 78 := by
    rw [← hev 78 (by norm_num)]; exact (vt_evalF h (k := 145) (by norm_num)).2.2
  have hB : σ (.n 6240) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 1)], [([78], 2)], [([40], 1), ([11, 40], 1)], [([41], 1), ([11, 41], 1), ([11, 40], 1)], [([], 0)]] := by
    simp only [v5555, v5031, v5007, v4597, v4575, v4461, a5670, a5669, a5668, a5667, e5666, a5665, a5664,
      e5663, a5662, a5661, a5660, a5659, a5658, a5657, e5656, a5655, a5654, a5653, a5652,
      e5651, a5650, a5649, a5648, a5647, e5646, a5645, a5644, a5643, e5642]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5672, a5671, hB]

set_option maxRecDepth 10000 in
theorem vtB05_16F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6281) = σ (.n 6242) + σ (.n 1295) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 2)], [([79], 1), ([12, 79], 2), ([12, 79], 1)], [([42], 1), ([11, 42], 1), ([11, 41], 1)], [([43], 1), ([11, 43], 1), ([11, 42], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5673 [
    .atom (.load (.n 6243) (.n 13) 0),
    .atom (.const (.n 6244) (word 2 0 0)),
    .atom (.mul (.n 6245) (.n 6243) (.n 6244)),
    .atom (.const (.n 6246) (word 2 0 0)),
    .atom (.mul (.n 6247) (.n 4461) (.n 4575)),
    .atom (.mul (.n 6248) (.n 6246) (.n 6247)),
    .atom (.load (.n 6249) (.n 13) 1),
    .atom (.mul (.n 6250) (.n 6249) (.n 6248)),
    .atom (.add (.n 6251) (.n 6245) (.n 6250)),
    .atom (.const (.n 6252) (word 2 0 0)),
    .atom (.mul (.n 6253) (.n 4608) (.n 5566)),
    .atom (.mul (.n 6254) (.n 6252) (.n 6253)),
    .atom (.add (.n 6255) (.n 5566) (.n 6254)),
    .atom (.mul (.n 6256) (.n 4608) (.n 5566)),
    .atom (.add (.n 6257) (.n 6255) (.n 6256)),
    .atom (.load (.n 6258) (.n 13) 2),
    .atom (.mul (.n 6259) (.n 6258) (.n 6257)),
    .atom (.add (.n 6260) (.n 6251) (.n 6259)),
    .atom (.mul (.n 6261) (.n 4597) (.n 5042)),
    .atom (.add (.n 6262) (.n 5042) (.n 6261)),
    .atom (.mul (.n 6263) (.n 4597) (.n 5031)),
    .atom (.add (.n 6264) (.n 6262) (.n 6263)),
    .atom (.load (.n 6265) (.n 13) 3),
    .atom (.mul (.n 6266) (.n 6265) (.n 6264)),
    .atom (.add (.n 6267) (.n 6260) (.n 6266)),
    .atom (.mul (.n 6268) (.n 4597) (.n 5053)),
    .atom (.add (.n 6269) (.n 5053) (.n 6268)),
    .atom (.mul (.n 6270) (.n 4597) (.n 5042)),
    .atom (.add (.n 6271) (.n 6269) (.n 6270)),
    .atom (.load (.n 6272) (.n 13) 4),
    .atom (.mul (.n 6273) (.n 6272) (.n 6271)),
    .atom (.add (.n 6274) (.n 6267) (.n 6273)),
    .atom (.load (.n 6275) (.n 13) 5),
    .atom (.const (.n 6276) (word 0 0 0)),
    .atom (.mul (.n 6277) (.n 6275) (.n 6276)),
    .atom (.add (.n 6278) (.n 6274) (.n 6277)),
    .atom (.add (.n 6279) (.n 14) (.n 6278)),
    .atom (.mul (.n 6280) (.n 1295) (.n 6279)),
    .atom (.add (.n 6281) (.n 6242) (.n 6280))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5673, a5674, a5675, a5676, a5677, a5678, a5679, a5680, a5681, a5682, a5683, a5684, a5685, a5686,
    a5687, a5688, a5689, a5690, a5691, a5692, a5693, a5694, a5695, a5696, a5697, a5698, a5699,
    a5700, a5701, a5702, a5703, a5704, a5705, a5706, a5707, a5708, a5709, a5710, a5711, -⟩ := hs
  have e5673 := tb_loadHolds_unique a5673 (hw 0 (by norm_num))
  have e5679 := tb_loadHolds_unique a5679 (hw 1 (by norm_num))
  have e5688 := tb_loadHolds_unique a5688 (hw 2 (by norm_num))
  have e5695 := tb_loadHolds_unique a5695 (hw 3 (by norm_num))
  have e5702 := tb_loadHolds_unique a5702 (hw 4 (by norm_num))
  have e5705 := tb_loadHolds_unique a5705 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4575 : σ (.n 4575) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2
  have v4597 : σ (.n 4597) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 78) (by norm_num)).2.2
  have v4608 : σ (.n 4608) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_evalF h (k := 79) (by norm_num)).2.2
  have v5031 : σ (.n 5031) = ev 41 := by
    rw [← hev 41 (by norm_num)]; exact (vt_evalF h (k := 108) (by norm_num)).2.2
  have v5042 : σ (.n 5042) = ev 42 := by
    rw [← hev 42 (by norm_num)]; exact (vt_evalF h (k := 109) (by norm_num)).2.2
  have v5053 : σ (.n 5053) = ev 43 := by
    rw [← hev 43 (by norm_num)]; exact (vt_evalF h (k := 110) (by norm_num)).2.2
  have v5566 : σ (.n 5566) = ev 79 := by
    rw [← hev 79 (by norm_num)]; exact (vt_evalF h (k := 146) (by norm_num)).2.2
  have hB : σ (.n 6279) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 2)], [([79], 1), ([12, 79], 2), ([12, 79], 1)], [([42], 1), ([11, 42], 1), ([11, 41], 1)], [([43], 1), ([11, 43], 1), ([11, 42], 1)], [([], 0)]] := by
    simp only [v5566, v5053, v5042, v5031, v4608, v4597, v4575, v4461, a5709, a5708, a5707, a5706, e5705,
      a5704, a5703, e5702, a5701, a5700, a5699, a5698, a5697, a5696, e5695, a5694, a5693,
      a5692, a5691, a5690, a5689, e5688, a5687, a5686, a5685, a5684, a5683, a5682, a5681,
      a5680, e5679, a5678, a5677, a5676, a5675, a5674, e5673]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5711, a5710, hB]

set_option maxRecDepth 10000 in
theorem vtB05_17F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6320) = σ (.n 6281) + σ (.n 1304) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 4)], [([80], 1), ([13, 80], 2), ([13, 80], 1)], [([44], 1), ([11, 44], 1), ([11, 43], 1)], [([45], 1), ([11, 45], 1), ([11, 44], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5712 [
    .atom (.load (.n 6282) (.n 13) 0),
    .atom (.const (.n 6283) (word 2 0 0)),
    .atom (.mul (.n 6284) (.n 6282) (.n 6283)),
    .atom (.const (.n 6285) (word 4 0 0)),
    .atom (.mul (.n 6286) (.n 4461) (.n 4575)),
    .atom (.mul (.n 6287) (.n 6285) (.n 6286)),
    .atom (.load (.n 6288) (.n 13) 1),
    .atom (.mul (.n 6289) (.n 6288) (.n 6287)),
    .atom (.add (.n 6290) (.n 6284) (.n 6289)),
    .atom (.const (.n 6291) (word 2 0 0)),
    .atom (.mul (.n 6292) (.n 4632) (.n 5577)),
    .atom (.mul (.n 6293) (.n 6291) (.n 6292)),
    .atom (.add (.n 6294) (.n 5577) (.n 6293)),
    .atom (.mul (.n 6295) (.n 4632) (.n 5577)),
    .atom (.add (.n 6296) (.n 6294) (.n 6295)),
    .atom (.load (.n 6297) (.n 13) 2),
    .atom (.mul (.n 6298) (.n 6297) (.n 6296)),
    .atom (.add (.n 6299) (.n 6290) (.n 6298)),
    .atom (.mul (.n 6300) (.n 4597) (.n 5064)),
    .atom (.add (.n 6301) (.n 5064) (.n 6300)),
    .atom (.mul (.n 6302) (.n 4597) (.n 5053)),
    .atom (.add (.n 6303) (.n 6301) (.n 6302)),
    .atom (.load (.n 6304) (.n 13) 3),
    .atom (.mul (.n 6305) (.n 6304) (.n 6303)),
    .atom (.add (.n 6306) (.n 6299) (.n 6305)),
    .atom (.mul (.n 6307) (.n 4597) (.n 5088)),
    .atom (.add (.n 6308) (.n 5088) (.n 6307)),
    .atom (.mul (.n 6309) (.n 4597) (.n 5064)),
    .atom (.add (.n 6310) (.n 6308) (.n 6309)),
    .atom (.load (.n 6311) (.n 13) 4),
    .atom (.mul (.n 6312) (.n 6311) (.n 6310)),
    .atom (.add (.n 6313) (.n 6306) (.n 6312)),
    .atom (.load (.n 6314) (.n 13) 5),
    .atom (.const (.n 6315) (word 0 0 0)),
    .atom (.mul (.n 6316) (.n 6314) (.n 6315)),
    .atom (.add (.n 6317) (.n 6313) (.n 6316)),
    .atom (.add (.n 6318) (.n 14) (.n 6317)),
    .atom (.mul (.n 6319) (.n 1304) (.n 6318)),
    .atom (.add (.n 6320) (.n 6281) (.n 6319))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5712, a5713, a5714, a5715, a5716, a5717, a5718, a5719, a5720, a5721, a5722, a5723, a5724, a5725,
    a5726, a5727, a5728, a5729, a5730, a5731, a5732, a5733, a5734, a5735, a5736, a5737, a5738,
    a5739, a5740, a5741, a5742, a5743, a5744, a5745, a5746, a5747, a5748, a5749, a5750, -⟩ := hs
  have e5712 := tb_loadHolds_unique a5712 (hw 0 (by norm_num))
  have e5718 := tb_loadHolds_unique a5718 (hw 1 (by norm_num))
  have e5727 := tb_loadHolds_unique a5727 (hw 2 (by norm_num))
  have e5734 := tb_loadHolds_unique a5734 (hw 3 (by norm_num))
  have e5741 := tb_loadHolds_unique a5741 (hw 4 (by norm_num))
  have e5744 := tb_loadHolds_unique a5744 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4575 : σ (.n 4575) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2
  have v4597 : σ (.n 4597) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 78) (by norm_num)).2.2
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 80) (by norm_num)).2.2
  have v5053 : σ (.n 5053) = ev 43 := by
    rw [← hev 43 (by norm_num)]; exact (vt_evalF h (k := 110) (by norm_num)).2.2
  have v5064 : σ (.n 5064) = ev 44 := by
    rw [← hev 44 (by norm_num)]; exact (vt_evalF h (k := 111) (by norm_num)).2.2
  have v5088 : σ (.n 5088) = ev 45 := by
    rw [← hev 45 (by norm_num)]; exact (vt_evalF h (k := 112) (by norm_num)).2.2
  have v5577 : σ (.n 5577) = ev 80 := by
    rw [← hev 80 (by norm_num)]; exact (vt_evalF h (k := 147) (by norm_num)).2.2
  have hB : σ (.n 6318) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 4)], [([80], 1), ([13, 80], 2), ([13, 80], 1)], [([44], 1), ([11, 44], 1), ([11, 43], 1)], [([45], 1), ([11, 45], 1), ([11, 44], 1)], [([], 0)]] := by
    simp only [v5577, v5088, v5064, v5053, v4632, v4597, v4575, v4461, a5748, a5747, a5746, a5745, e5744,
      a5743, a5742, e5741, a5740, a5739, a5738, a5737, a5736, a5735, e5734, a5733, a5732,
      a5731, a5730, a5729, a5728, e5727, a5726, a5725, a5724, a5723, a5722, a5721, a5720,
      a5719, e5718, a5717, a5716, a5715, a5714, a5713, e5712]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5750, a5749, hB]

set_option maxRecDepth 10000 in
theorem vtB05_18F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6359) = σ (.n 6320) + σ (.n 1313) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 8)], [([81], 1), ([13, 81], 2), ([13, 81], 1)], [([46], 1), ([11, 46], 1), ([11, 45], 1)], [([47], 1), ([11, 47], 1), ([11, 46], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5751 [
    .atom (.load (.n 6321) (.n 13) 0),
    .atom (.const (.n 6322) (word 2 0 0)),
    .atom (.mul (.n 6323) (.n 6321) (.n 6322)),
    .atom (.const (.n 6324) (word 8 0 0)),
    .atom (.mul (.n 6325) (.n 4461) (.n 4575)),
    .atom (.mul (.n 6326) (.n 6324) (.n 6325)),
    .atom (.load (.n 6327) (.n 13) 1),
    .atom (.mul (.n 6328) (.n 6327) (.n 6326)),
    .atom (.add (.n 6329) (.n 6323) (.n 6328)),
    .atom (.const (.n 6330) (word 2 0 0)),
    .atom (.mul (.n 6331) (.n 4632) (.n 5601)),
    .atom (.mul (.n 6332) (.n 6330) (.n 6331)),
    .atom (.add (.n 6333) (.n 5601) (.n 6332)),
    .atom (.mul (.n 6334) (.n 4632) (.n 5601)),
    .atom (.add (.n 6335) (.n 6333) (.n 6334)),
    .atom (.load (.n 6336) (.n 13) 2),
    .atom (.mul (.n 6337) (.n 6336) (.n 6335)),
    .atom (.add (.n 6338) (.n 6329) (.n 6337)),
    .atom (.mul (.n 6339) (.n 4597) (.n 5099)),
    .atom (.add (.n 6340) (.n 5099) (.n 6339)),
    .atom (.mul (.n 6341) (.n 4597) (.n 5088)),
    .atom (.add (.n 6342) (.n 6340) (.n 6341)),
    .atom (.load (.n 6343) (.n 13) 3),
    .atom (.mul (.n 6344) (.n 6343) (.n 6342)),
    .atom (.add (.n 6345) (.n 6338) (.n 6344)),
    .atom (.mul (.n 6346) (.n 4597) (.n 5110)),
    .atom (.add (.n 6347) (.n 5110) (.n 6346)),
    .atom (.mul (.n 6348) (.n 4597) (.n 5099)),
    .atom (.add (.n 6349) (.n 6347) (.n 6348)),
    .atom (.load (.n 6350) (.n 13) 4),
    .atom (.mul (.n 6351) (.n 6350) (.n 6349)),
    .atom (.add (.n 6352) (.n 6345) (.n 6351)),
    .atom (.load (.n 6353) (.n 13) 5),
    .atom (.const (.n 6354) (word 0 0 0)),
    .atom (.mul (.n 6355) (.n 6353) (.n 6354)),
    .atom (.add (.n 6356) (.n 6352) (.n 6355)),
    .atom (.add (.n 6357) (.n 14) (.n 6356)),
    .atom (.mul (.n 6358) (.n 1313) (.n 6357)),
    .atom (.add (.n 6359) (.n 6320) (.n 6358))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5751, a5752, a5753, a5754, a5755, a5756, a5757, a5758, a5759, a5760, a5761, a5762, a5763, a5764,
    a5765, a5766, a5767, a5768, a5769, a5770, a5771, a5772, a5773, a5774, a5775, a5776, a5777,
    a5778, a5779, a5780, a5781, a5782, a5783, a5784, a5785, a5786, a5787, a5788, a5789, -⟩ := hs
  have e5751 := tb_loadHolds_unique a5751 (hw 0 (by norm_num))
  have e5757 := tb_loadHolds_unique a5757 (hw 1 (by norm_num))
  have e5766 := tb_loadHolds_unique a5766 (hw 2 (by norm_num))
  have e5773 := tb_loadHolds_unique a5773 (hw 3 (by norm_num))
  have e5780 := tb_loadHolds_unique a5780 (hw 4 (by norm_num))
  have e5783 := tb_loadHolds_unique a5783 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4575 : σ (.n 4575) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2
  have v4597 : σ (.n 4597) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 78) (by norm_num)).2.2
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 80) (by norm_num)).2.2
  have v5088 : σ (.n 5088) = ev 45 := by
    rw [← hev 45 (by norm_num)]; exact (vt_evalF h (k := 112) (by norm_num)).2.2
  have v5099 : σ (.n 5099) = ev 46 := by
    rw [← hev 46 (by norm_num)]; exact (vt_evalF h (k := 113) (by norm_num)).2.2
  have v5110 : σ (.n 5110) = ev 47 := by
    rw [← hev 47 (by norm_num)]; exact (vt_evalF h (k := 114) (by norm_num)).2.2
  have v5601 : σ (.n 5601) = ev 81 := by
    rw [← hev 81 (by norm_num)]; exact (vt_evalF h (k := 148) (by norm_num)).2.2
  have hB : σ (.n 6357) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 8)], [([81], 1), ([13, 81], 2), ([13, 81], 1)], [([46], 1), ([11, 46], 1), ([11, 45], 1)], [([47], 1), ([11, 47], 1), ([11, 46], 1)], [([], 0)]] := by
    simp only [v5601, v5110, v5099, v5088, v4632, v4597, v4575, v4461, a5787, a5786, a5785, a5784, e5783,
      a5782, a5781, e5780, a5779, a5778, a5777, a5776, a5775, a5774, e5773, a5772, a5771,
      a5770, a5769, a5768, a5767, e5766, a5765, a5764, a5763, a5762, a5761, a5760, a5759,
      a5758, e5757, a5756, a5755, a5754, a5753, a5752, e5751]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5789, a5788, hB]

set_option maxRecDepth 10000 in
theorem vtB05_19F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6398) = σ (.n 6359) + σ (.n 1322) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 16)], [([82], 1), ([13, 82], 2), ([13, 82], 1)], [([48], 1), ([11, 48], 1), ([11, 47], 1)], [([49], 1), ([11, 49], 1), ([11, 48], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5790 [
    .atom (.load (.n 6360) (.n 13) 0),
    .atom (.const (.n 6361) (word 2 0 0)),
    .atom (.mul (.n 6362) (.n 6360) (.n 6361)),
    .atom (.const (.n 6363) (word 16 0 0)),
    .atom (.mul (.n 6364) (.n 4461) (.n 4575)),
    .atom (.mul (.n 6365) (.n 6363) (.n 6364)),
    .atom (.load (.n 6366) (.n 13) 1),
    .atom (.mul (.n 6367) (.n 6366) (.n 6365)),
    .atom (.add (.n 6368) (.n 6362) (.n 6367)),
    .atom (.const (.n 6369) (word 2 0 0)),
    .atom (.mul (.n 6370) (.n 4632) (.n 5612)),
    .atom (.mul (.n 6371) (.n 6369) (.n 6370)),
    .atom (.add (.n 6372) (.n 5612) (.n 6371)),
    .atom (.mul (.n 6373) (.n 4632) (.n 5612)),
    .atom (.add (.n 6374) (.n 6372) (.n 6373)),
    .atom (.load (.n 6375) (.n 13) 2),
    .atom (.mul (.n 6376) (.n 6375) (.n 6374)),
    .atom (.add (.n 6377) (.n 6368) (.n 6376)),
    .atom (.mul (.n 6378) (.n 4597) (.n 5121)),
    .atom (.add (.n 6379) (.n 5121) (.n 6378)),
    .atom (.mul (.n 6380) (.n 4597) (.n 5110)),
    .atom (.add (.n 6381) (.n 6379) (.n 6380)),
    .atom (.load (.n 6382) (.n 13) 3),
    .atom (.mul (.n 6383) (.n 6382) (.n 6381)),
    .atom (.add (.n 6384) (.n 6377) (.n 6383)),
    .atom (.mul (.n 6385) (.n 4597) (.n 5145)),
    .atom (.add (.n 6386) (.n 5145) (.n 6385)),
    .atom (.mul (.n 6387) (.n 4597) (.n 5121)),
    .atom (.add (.n 6388) (.n 6386) (.n 6387)),
    .atom (.load (.n 6389) (.n 13) 4),
    .atom (.mul (.n 6390) (.n 6389) (.n 6388)),
    .atom (.add (.n 6391) (.n 6384) (.n 6390)),
    .atom (.load (.n 6392) (.n 13) 5),
    .atom (.const (.n 6393) (word 0 0 0)),
    .atom (.mul (.n 6394) (.n 6392) (.n 6393)),
    .atom (.add (.n 6395) (.n 6391) (.n 6394)),
    .atom (.add (.n 6396) (.n 14) (.n 6395)),
    .atom (.mul (.n 6397) (.n 1322) (.n 6396)),
    .atom (.add (.n 6398) (.n 6359) (.n 6397))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5790, a5791, a5792, a5793, a5794, a5795, a5796, a5797, a5798, a5799, a5800, a5801, a5802, a5803,
    a5804, a5805, a5806, a5807, a5808, a5809, a5810, a5811, a5812, a5813, a5814, a5815, a5816,
    a5817, a5818, a5819, a5820, a5821, a5822, a5823, a5824, a5825, a5826, a5827, a5828, -⟩ := hs
  have e5790 := tb_loadHolds_unique a5790 (hw 0 (by norm_num))
  have e5796 := tb_loadHolds_unique a5796 (hw 1 (by norm_num))
  have e5805 := tb_loadHolds_unique a5805 (hw 2 (by norm_num))
  have e5812 := tb_loadHolds_unique a5812 (hw 3 (by norm_num))
  have e5819 := tb_loadHolds_unique a5819 (hw 4 (by norm_num))
  have e5822 := tb_loadHolds_unique a5822 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4575 : σ (.n 4575) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2
  have v4597 : σ (.n 4597) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 78) (by norm_num)).2.2
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 80) (by norm_num)).2.2
  have v5110 : σ (.n 5110) = ev 47 := by
    rw [← hev 47 (by norm_num)]; exact (vt_evalF h (k := 114) (by norm_num)).2.2
  have v5121 : σ (.n 5121) = ev 48 := by
    rw [← hev 48 (by norm_num)]; exact (vt_evalF h (k := 115) (by norm_num)).2.2
  have v5145 : σ (.n 5145) = ev 49 := by
    rw [← hev 49 (by norm_num)]; exact (vt_evalF h (k := 116) (by norm_num)).2.2
  have v5612 : σ (.n 5612) = ev 82 := by
    rw [← hev 82 (by norm_num)]; exact (vt_evalF h (k := 149) (by norm_num)).2.2
  have hB : σ (.n 6396) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 16)], [([82], 1), ([13, 82], 2), ([13, 82], 1)], [([48], 1), ([11, 48], 1), ([11, 47], 1)], [([49], 1), ([11, 49], 1), ([11, 48], 1)], [([], 0)]] := by
    simp only [v5612, v5145, v5121, v5110, v4632, v4597, v4575, v4461, a5826, a5825, a5824, a5823, e5822,
      a5821, a5820, e5819, a5818, a5817, a5816, a5815, a5814, a5813, e5812, a5811, a5810,
      a5809, a5808, a5807, a5806, e5805, a5804, a5803, a5802, a5801, a5800, a5799, a5798,
      a5797, e5796, a5795, a5794, a5793, a5792, a5791, e5790]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5828, a5827, hB]

set_option maxRecDepth 10000 in
theorem vtB05_20F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6437) = σ (.n 6398) + σ (.n 1331) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 32)], [([83], 1), ([13, 83], 2), ([13, 83], 1)], [([50], 1), ([11, 50], 1), ([11, 49], 1)], [([51], 1), ([11, 51], 1), ([11, 50], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5829 [
    .atom (.load (.n 6399) (.n 13) 0),
    .atom (.const (.n 6400) (word 2 0 0)),
    .atom (.mul (.n 6401) (.n 6399) (.n 6400)),
    .atom (.const (.n 6402) (word 32 0 0)),
    .atom (.mul (.n 6403) (.n 4461) (.n 4575)),
    .atom (.mul (.n 6404) (.n 6402) (.n 6403)),
    .atom (.load (.n 6405) (.n 13) 1),
    .atom (.mul (.n 6406) (.n 6405) (.n 6404)),
    .atom (.add (.n 6407) (.n 6401) (.n 6406)),
    .atom (.const (.n 6408) (word 2 0 0)),
    .atom (.mul (.n 6409) (.n 4632) (.n 5623)),
    .atom (.mul (.n 6410) (.n 6408) (.n 6409)),
    .atom (.add (.n 6411) (.n 5623) (.n 6410)),
    .atom (.mul (.n 6412) (.n 4632) (.n 5623)),
    .atom (.add (.n 6413) (.n 6411) (.n 6412)),
    .atom (.load (.n 6414) (.n 13) 2),
    .atom (.mul (.n 6415) (.n 6414) (.n 6413)),
    .atom (.add (.n 6416) (.n 6407) (.n 6415)),
    .atom (.mul (.n 6417) (.n 4597) (.n 5156)),
    .atom (.add (.n 6418) (.n 5156) (.n 6417)),
    .atom (.mul (.n 6419) (.n 4597) (.n 5145)),
    .atom (.add (.n 6420) (.n 6418) (.n 6419)),
    .atom (.load (.n 6421) (.n 13) 3),
    .atom (.mul (.n 6422) (.n 6421) (.n 6420)),
    .atom (.add (.n 6423) (.n 6416) (.n 6422)),
    .atom (.mul (.n 6424) (.n 4597) (.n 5167)),
    .atom (.add (.n 6425) (.n 5167) (.n 6424)),
    .atom (.mul (.n 6426) (.n 4597) (.n 5156)),
    .atom (.add (.n 6427) (.n 6425) (.n 6426)),
    .atom (.load (.n 6428) (.n 13) 4),
    .atom (.mul (.n 6429) (.n 6428) (.n 6427)),
    .atom (.add (.n 6430) (.n 6423) (.n 6429)),
    .atom (.load (.n 6431) (.n 13) 5),
    .atom (.const (.n 6432) (word 0 0 0)),
    .atom (.mul (.n 6433) (.n 6431) (.n 6432)),
    .atom (.add (.n 6434) (.n 6430) (.n 6433)),
    .atom (.add (.n 6435) (.n 14) (.n 6434)),
    .atom (.mul (.n 6436) (.n 1331) (.n 6435)),
    .atom (.add (.n 6437) (.n 6398) (.n 6436))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5829, a5830, a5831, a5832, a5833, a5834, a5835, a5836, a5837, a5838, a5839, a5840, a5841, a5842,
    a5843, a5844, a5845, a5846, a5847, a5848, a5849, a5850, a5851, a5852, a5853, a5854, a5855,
    a5856, a5857, a5858, a5859, a5860, a5861, a5862, a5863, a5864, a5865, a5866, a5867, -⟩ := hs
  have e5829 := tb_loadHolds_unique a5829 (hw 0 (by norm_num))
  have e5835 := tb_loadHolds_unique a5835 (hw 1 (by norm_num))
  have e5844 := tb_loadHolds_unique a5844 (hw 2 (by norm_num))
  have e5851 := tb_loadHolds_unique a5851 (hw 3 (by norm_num))
  have e5858 := tb_loadHolds_unique a5858 (hw 4 (by norm_num))
  have e5861 := tb_loadHolds_unique a5861 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4575 : σ (.n 4575) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2
  have v4597 : σ (.n 4597) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 78) (by norm_num)).2.2
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 80) (by norm_num)).2.2
  have v5145 : σ (.n 5145) = ev 49 := by
    rw [← hev 49 (by norm_num)]; exact (vt_evalF h (k := 116) (by norm_num)).2.2
  have v5156 : σ (.n 5156) = ev 50 := by
    rw [← hev 50 (by norm_num)]; exact (vt_evalF h (k := 117) (by norm_num)).2.2
  have v5167 : σ (.n 5167) = ev 51 := by
    rw [← hev 51 (by norm_num)]; exact (vt_evalF h (k := 118) (by norm_num)).2.2
  have v5623 : σ (.n 5623) = ev 83 := by
    rw [← hev 83 (by norm_num)]; exact (vt_evalF h (k := 150) (by norm_num)).2.2
  have hB : σ (.n 6435) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 32)], [([83], 1), ([13, 83], 2), ([13, 83], 1)], [([50], 1), ([11, 50], 1), ([11, 49], 1)], [([51], 1), ([11, 51], 1), ([11, 50], 1)], [([], 0)]] := by
    simp only [v5623, v5167, v5156, v5145, v4632, v4597, v4575, v4461, a5865, a5864, a5863, a5862, e5861,
      a5860, a5859, e5858, a5857, a5856, a5855, a5854, a5853, a5852, e5851, a5850, a5849,
      a5848, a5847, a5846, a5845, e5844, a5843, a5842, a5841, a5840, a5839, a5838, a5837,
      a5836, e5835, a5834, a5833, a5832, a5831, a5830, e5829]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5867, a5866, hB]

set_option maxRecDepth 10000 in
theorem vtB05_21F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6476) = σ (.n 6437) + σ (.n 1340) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 64)], [([84], 1), ([13, 84], 2), ([13, 84], 1)], [([52], 1), ([11, 52], 1), ([11, 51], 1)], [([53], 1), ([11, 53], 1), ([11, 52], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5868 [
    .atom (.load (.n 6438) (.n 13) 0),
    .atom (.const (.n 6439) (word 2 0 0)),
    .atom (.mul (.n 6440) (.n 6438) (.n 6439)),
    .atom (.const (.n 6441) (word 64 0 0)),
    .atom (.mul (.n 6442) (.n 4461) (.n 4575)),
    .atom (.mul (.n 6443) (.n 6441) (.n 6442)),
    .atom (.load (.n 6444) (.n 13) 1),
    .atom (.mul (.n 6445) (.n 6444) (.n 6443)),
    .atom (.add (.n 6446) (.n 6440) (.n 6445)),
    .atom (.const (.n 6447) (word 2 0 0)),
    .atom (.mul (.n 6448) (.n 4632) (.n 5634)),
    .atom (.mul (.n 6449) (.n 6447) (.n 6448)),
    .atom (.add (.n 6450) (.n 5634) (.n 6449)),
    .atom (.mul (.n 6451) (.n 4632) (.n 5634)),
    .atom (.add (.n 6452) (.n 6450) (.n 6451)),
    .atom (.load (.n 6453) (.n 13) 2),
    .atom (.mul (.n 6454) (.n 6453) (.n 6452)),
    .atom (.add (.n 6455) (.n 6446) (.n 6454)),
    .atom (.mul (.n 6456) (.n 4597) (.n 5178)),
    .atom (.add (.n 6457) (.n 5178) (.n 6456)),
    .atom (.mul (.n 6458) (.n 4597) (.n 5167)),
    .atom (.add (.n 6459) (.n 6457) (.n 6458)),
    .atom (.load (.n 6460) (.n 13) 3),
    .atom (.mul (.n 6461) (.n 6460) (.n 6459)),
    .atom (.add (.n 6462) (.n 6455) (.n 6461)),
    .atom (.mul (.n 6463) (.n 4597) (.n 5202)),
    .atom (.add (.n 6464) (.n 5202) (.n 6463)),
    .atom (.mul (.n 6465) (.n 4597) (.n 5178)),
    .atom (.add (.n 6466) (.n 6464) (.n 6465)),
    .atom (.load (.n 6467) (.n 13) 4),
    .atom (.mul (.n 6468) (.n 6467) (.n 6466)),
    .atom (.add (.n 6469) (.n 6462) (.n 6468)),
    .atom (.load (.n 6470) (.n 13) 5),
    .atom (.const (.n 6471) (word 0 0 0)),
    .atom (.mul (.n 6472) (.n 6470) (.n 6471)),
    .atom (.add (.n 6473) (.n 6469) (.n 6472)),
    .atom (.add (.n 6474) (.n 14) (.n 6473)),
    .atom (.mul (.n 6475) (.n 1340) (.n 6474)),
    .atom (.add (.n 6476) (.n 6437) (.n 6475))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5868, a5869, a5870, a5871, a5872, a5873, a5874, a5875, a5876, a5877, a5878, a5879, a5880, a5881,
    a5882, a5883, a5884, a5885, a5886, a5887, a5888, a5889, a5890, a5891, a5892, a5893, a5894,
    a5895, a5896, a5897, a5898, a5899, a5900, a5901, a5902, a5903, a5904, a5905, a5906, -⟩ := hs
  have e5868 := tb_loadHolds_unique a5868 (hw 0 (by norm_num))
  have e5874 := tb_loadHolds_unique a5874 (hw 1 (by norm_num))
  have e5883 := tb_loadHolds_unique a5883 (hw 2 (by norm_num))
  have e5890 := tb_loadHolds_unique a5890 (hw 3 (by norm_num))
  have e5897 := tb_loadHolds_unique a5897 (hw 4 (by norm_num))
  have e5900 := tb_loadHolds_unique a5900 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4575 : σ (.n 4575) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2
  have v4597 : σ (.n 4597) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 78) (by norm_num)).2.2
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 80) (by norm_num)).2.2
  have v5167 : σ (.n 5167) = ev 51 := by
    rw [← hev 51 (by norm_num)]; exact (vt_evalF h (k := 118) (by norm_num)).2.2
  have v5178 : σ (.n 5178) = ev 52 := by
    rw [← hev 52 (by norm_num)]; exact (vt_evalF h (k := 119) (by norm_num)).2.2
  have v5202 : σ (.n 5202) = ev 53 := by
    rw [← hev 53 (by norm_num)]; exact (vt_evalF h (k := 120) (by norm_num)).2.2
  have v5634 : σ (.n 5634) = ev 84 := by
    rw [← hev 84 (by norm_num)]; exact (vt_evalF h (k := 151) (by norm_num)).2.2
  have hB : σ (.n 6474) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 64)], [([84], 1), ([13, 84], 2), ([13, 84], 1)], [([52], 1), ([11, 52], 1), ([11, 51], 1)], [([53], 1), ([11, 53], 1), ([11, 52], 1)], [([], 0)]] := by
    simp only [v5634, v5202, v5178, v5167, v4632, v4597, v4575, v4461, a5904, a5903, a5902, a5901, e5900,
      a5899, a5898, e5897, a5896, a5895, a5894, a5893, a5892, a5891, e5890, a5889, a5888,
      a5887, a5886, a5885, a5884, e5883, a5882, a5881, a5880, a5879, a5878, a5877, a5876,
      a5875, e5874, a5873, a5872, a5871, a5870, a5869, e5868]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5906, a5905, hB]

set_option maxRecDepth 10000 in
theorem vtB05_22F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6515) = σ (.n 6476) + σ (.n 1349) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 128)], [([85], 1), ([13, 85], 2), ([13, 85], 1)], [([54], 1), ([11, 54], 1), ([11, 53], 1)], [([55], 1), ([11, 55], 1), ([11, 54], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5907 [
    .atom (.load (.n 6477) (.n 13) 0),
    .atom (.const (.n 6478) (word 2 0 0)),
    .atom (.mul (.n 6479) (.n 6477) (.n 6478)),
    .atom (.const (.n 6480) (word 128 0 0)),
    .atom (.mul (.n 6481) (.n 4461) (.n 4575)),
    .atom (.mul (.n 6482) (.n 6480) (.n 6481)),
    .atom (.load (.n 6483) (.n 13) 1),
    .atom (.mul (.n 6484) (.n 6483) (.n 6482)),
    .atom (.add (.n 6485) (.n 6479) (.n 6484)),
    .atom (.const (.n 6486) (word 2 0 0)),
    .atom (.mul (.n 6487) (.n 4632) (.n 5658)),
    .atom (.mul (.n 6488) (.n 6486) (.n 6487)),
    .atom (.add (.n 6489) (.n 5658) (.n 6488)),
    .atom (.mul (.n 6490) (.n 4632) (.n 5658)),
    .atom (.add (.n 6491) (.n 6489) (.n 6490)),
    .atom (.load (.n 6492) (.n 13) 2),
    .atom (.mul (.n 6493) (.n 6492) (.n 6491)),
    .atom (.add (.n 6494) (.n 6485) (.n 6493)),
    .atom (.mul (.n 6495) (.n 4597) (.n 5213)),
    .atom (.add (.n 6496) (.n 5213) (.n 6495)),
    .atom (.mul (.n 6497) (.n 4597) (.n 5202)),
    .atom (.add (.n 6498) (.n 6496) (.n 6497)),
    .atom (.load (.n 6499) (.n 13) 3),
    .atom (.mul (.n 6500) (.n 6499) (.n 6498)),
    .atom (.add (.n 6501) (.n 6494) (.n 6500)),
    .atom (.mul (.n 6502) (.n 4597) (.n 5224)),
    .atom (.add (.n 6503) (.n 5224) (.n 6502)),
    .atom (.mul (.n 6504) (.n 4597) (.n 5213)),
    .atom (.add (.n 6505) (.n 6503) (.n 6504)),
    .atom (.load (.n 6506) (.n 13) 4),
    .atom (.mul (.n 6507) (.n 6506) (.n 6505)),
    .atom (.add (.n 6508) (.n 6501) (.n 6507)),
    .atom (.load (.n 6509) (.n 13) 5),
    .atom (.const (.n 6510) (word 0 0 0)),
    .atom (.mul (.n 6511) (.n 6509) (.n 6510)),
    .atom (.add (.n 6512) (.n 6508) (.n 6511)),
    .atom (.add (.n 6513) (.n 14) (.n 6512)),
    .atom (.mul (.n 6514) (.n 1349) (.n 6513)),
    .atom (.add (.n 6515) (.n 6476) (.n 6514))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5907, a5908, a5909, a5910, a5911, a5912, a5913, a5914, a5915, a5916, a5917, a5918, a5919, a5920,
    a5921, a5922, a5923, a5924, a5925, a5926, a5927, a5928, a5929, a5930, a5931, a5932, a5933,
    a5934, a5935, a5936, a5937, a5938, a5939, a5940, a5941, a5942, a5943, a5944, a5945, -⟩ := hs
  have e5907 := tb_loadHolds_unique a5907 (hw 0 (by norm_num))
  have e5913 := tb_loadHolds_unique a5913 (hw 1 (by norm_num))
  have e5922 := tb_loadHolds_unique a5922 (hw 2 (by norm_num))
  have e5929 := tb_loadHolds_unique a5929 (hw 3 (by norm_num))
  have e5936 := tb_loadHolds_unique a5936 (hw 4 (by norm_num))
  have e5939 := tb_loadHolds_unique a5939 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4575 : σ (.n 4575) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2
  have v4597 : σ (.n 4597) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 78) (by norm_num)).2.2
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 80) (by norm_num)).2.2
  have v5202 : σ (.n 5202) = ev 53 := by
    rw [← hev 53 (by norm_num)]; exact (vt_evalF h (k := 120) (by norm_num)).2.2
  have v5213 : σ (.n 5213) = ev 54 := by
    rw [← hev 54 (by norm_num)]; exact (vt_evalF h (k := 121) (by norm_num)).2.2
  have v5224 : σ (.n 5224) = ev 55 := by
    rw [← hev 55 (by norm_num)]; exact (vt_evalF h (k := 122) (by norm_num)).2.2
  have v5658 : σ (.n 5658) = ev 85 := by
    rw [← hev 85 (by norm_num)]; exact (vt_evalF h (k := 152) (by norm_num)).2.2
  have hB : σ (.n 6513) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 128)], [([85], 1), ([13, 85], 2), ([13, 85], 1)], [([54], 1), ([11, 54], 1), ([11, 53], 1)], [([55], 1), ([11, 55], 1), ([11, 54], 1)], [([], 0)]] := by
    simp only [v5658, v5224, v5213, v5202, v4632, v4597, v4575, v4461, a5943, a5942, a5941, a5940, e5939,
      a5938, a5937, e5936, a5935, a5934, a5933, a5932, a5931, a5930, e5929, a5928, a5927,
      a5926, a5925, a5924, a5923, e5922, a5921, a5920, a5919, a5918, a5917, a5916, a5915,
      a5914, e5913, a5912, a5911, a5910, a5909, a5908, e5907]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5945, a5944, hB]

set_option maxRecDepth 10000 in
theorem vtB05_23F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6551) = σ (.n 6515) + σ (.n 1358) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 256)], [([86], 1), ([13, 86], 2), ([13, 86], 1)], [([56], 1), ([11, 56], 1), ([11, 55], 1)], [([11, 56], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5946 [
    .atom (.load (.n 6516) (.n 13) 0),
    .atom (.const (.n 6517) (word 2 0 0)),
    .atom (.mul (.n 6518) (.n 6516) (.n 6517)),
    .atom (.const (.n 6519) (word 256 0 0)),
    .atom (.mul (.n 6520) (.n 4461) (.n 4575)),
    .atom (.mul (.n 6521) (.n 6519) (.n 6520)),
    .atom (.load (.n 6522) (.n 13) 1),
    .atom (.mul (.n 6523) (.n 6522) (.n 6521)),
    .atom (.add (.n 6524) (.n 6518) (.n 6523)),
    .atom (.const (.n 6525) (word 2 0 0)),
    .atom (.mul (.n 6526) (.n 4632) (.n 5669)),
    .atom (.mul (.n 6527) (.n 6525) (.n 6526)),
    .atom (.add (.n 6528) (.n 5669) (.n 6527)),
    .atom (.mul (.n 6529) (.n 4632) (.n 5669)),
    .atom (.add (.n 6530) (.n 6528) (.n 6529)),
    .atom (.load (.n 6531) (.n 13) 2),
    .atom (.mul (.n 6532) (.n 6531) (.n 6530)),
    .atom (.add (.n 6533) (.n 6524) (.n 6532)),
    .atom (.mul (.n 6534) (.n 4597) (.n 5235)),
    .atom (.add (.n 6535) (.n 5235) (.n 6534)),
    .atom (.mul (.n 6536) (.n 4597) (.n 5224)),
    .atom (.add (.n 6537) (.n 6535) (.n 6536)),
    .atom (.load (.n 6538) (.n 13) 3),
    .atom (.mul (.n 6539) (.n 6538) (.n 6537)),
    .atom (.add (.n 6540) (.n 6533) (.n 6539)),
    .atom (.mul (.n 6541) (.n 4597) (.n 5235)),
    .atom (.load (.n 6542) (.n 13) 4),
    .atom (.mul (.n 6543) (.n 6542) (.n 6541)),
    .atom (.add (.n 6544) (.n 6540) (.n 6543)),
    .atom (.load (.n 6545) (.n 13) 5),
    .atom (.const (.n 6546) (word 0 0 0)),
    .atom (.mul (.n 6547) (.n 6545) (.n 6546)),
    .atom (.add (.n 6548) (.n 6544) (.n 6547)),
    .atom (.add (.n 6549) (.n 14) (.n 6548)),
    .atom (.mul (.n 6550) (.n 1358) (.n 6549)),
    .atom (.add (.n 6551) (.n 6515) (.n 6550))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5946, a5947, a5948, a5949, a5950, a5951, a5952, a5953, a5954, a5955, a5956, a5957, a5958, a5959,
    a5960, a5961, a5962, a5963, a5964, a5965, a5966, a5967, a5968, a5969, a5970, a5971, a5972,
    a5973, a5974, a5975, a5976, a5977, a5978, a5979, a5980, a5981, -⟩ := hs
  have e5946 := tb_loadHolds_unique a5946 (hw 0 (by norm_num))
  have e5952 := tb_loadHolds_unique a5952 (hw 1 (by norm_num))
  have e5961 := tb_loadHolds_unique a5961 (hw 2 (by norm_num))
  have e5968 := tb_loadHolds_unique a5968 (hw 3 (by norm_num))
  have e5972 := tb_loadHolds_unique a5972 (hw 4 (by norm_num))
  have e5975 := tb_loadHolds_unique a5975 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4575 : σ (.n 4575) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2
  have v4597 : σ (.n 4597) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 78) (by norm_num)).2.2
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 80) (by norm_num)).2.2
  have v5224 : σ (.n 5224) = ev 55 := by
    rw [← hev 55 (by norm_num)]; exact (vt_evalF h (k := 122) (by norm_num)).2.2
  have v5235 : σ (.n 5235) = ev 56 := by
    rw [← hev 56 (by norm_num)]; exact (vt_evalF h (k := 123) (by norm_num)).2.2
  have v5669 : σ (.n 5669) = ev 86 := by
    rw [← hev 86 (by norm_num)]; exact (vt_evalF h (k := 153) (by norm_num)).2.2
  have hB : σ (.n 6549) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 256)], [([86], 1), ([13, 86], 2), ([13, 86], 1)], [([56], 1), ([11, 56], 1), ([11, 55], 1)], [([11, 56], 1)], [([], 0)]] := by
    simp only [v5669, v5235, v5224, v4632, v4597, v4575, v4461, a5979, a5978, a5977, a5976, e5975, a5974,
      a5973, e5972, a5971, a5970, a5969, e5968, a5967, a5966, a5965, a5964, a5963, a5962,
      e5961, a5960, a5959, a5958, a5957, a5956, a5955, a5954, a5953, e5952, a5951, a5950,
      a5949, a5948, a5947, e5946]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a5981, a5980, hB]

set_option maxRecDepth 10000 in
theorem vtB05_24F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6582) = σ (.n 6551) + σ (.n 1367) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 512)], [([87], 1), ([13, 87], 2), ([13, 87], 1)], [([57], 1)], [([58], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 5982 [
    .atom (.load (.n 6552) (.n 13) 0),
    .atom (.const (.n 6553) (word 2 0 0)),
    .atom (.mul (.n 6554) (.n 6552) (.n 6553)),
    .atom (.const (.n 6555) (word 512 0 0)),
    .atom (.mul (.n 6556) (.n 4461) (.n 4575)),
    .atom (.mul (.n 6557) (.n 6555) (.n 6556)),
    .atom (.load (.n 6558) (.n 13) 1),
    .atom (.mul (.n 6559) (.n 6558) (.n 6557)),
    .atom (.add (.n 6560) (.n 6554) (.n 6559)),
    .atom (.const (.n 6561) (word 2 0 0)),
    .atom (.mul (.n 6562) (.n 4632) (.n 5680)),
    .atom (.mul (.n 6563) (.n 6561) (.n 6562)),
    .atom (.add (.n 6564) (.n 5680) (.n 6563)),
    .atom (.mul (.n 6565) (.n 4632) (.n 5680)),
    .atom (.add (.n 6566) (.n 6564) (.n 6565)),
    .atom (.load (.n 6567) (.n 13) 2),
    .atom (.mul (.n 6568) (.n 6567) (.n 6566)),
    .atom (.add (.n 6569) (.n 6560) (.n 6568)),
    .atom (.load (.n 6570) (.n 13) 3),
    .atom (.mul (.n 6571) (.n 6570) (.n 5259)),
    .atom (.add (.n 6572) (.n 6569) (.n 6571)),
    .atom (.load (.n 6573) (.n 13) 4),
    .atom (.mul (.n 6574) (.n 6573) (.n 5270)),
    .atom (.add (.n 6575) (.n 6572) (.n 6574)),
    .atom (.load (.n 6576) (.n 13) 5),
    .atom (.const (.n 6577) (word 0 0 0)),
    .atom (.mul (.n 6578) (.n 6576) (.n 6577)),
    .atom (.add (.n 6579) (.n 6575) (.n 6578)),
    .atom (.add (.n 6580) (.n 14) (.n 6579)),
    .atom (.mul (.n 6581) (.n 1367) (.n 6580)),
    .atom (.add (.n 6582) (.n 6551) (.n 6581))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a5982, a5983, a5984, a5985, a5986, a5987, a5988, a5989, a5990, a5991, a5992, a5993, a5994, a5995,
    a5996, a5997, a5998, a5999, a6000, a6001, a6002, a6003, a6004, a6005, a6006, a6007, a6008,
    a6009, a6010, a6011, a6012, -⟩ := hs
  have e5982 := tb_loadHolds_unique a5982 (hw 0 (by norm_num))
  have e5988 := tb_loadHolds_unique a5988 (hw 1 (by norm_num))
  have e5997 := tb_loadHolds_unique a5997 (hw 2 (by norm_num))
  have e6000 := tb_loadHolds_unique a6000 (hw 3 (by norm_num))
  have e6003 := tb_loadHolds_unique a6003 (hw 4 (by norm_num))
  have e6006 := tb_loadHolds_unique a6006 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4575 : σ (.n 4575) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 80) (by norm_num)).2.2
  have v5259 : σ (.n 5259) = ev 57 := by
    rw [← hev 57 (by norm_num)]; exact (vt_evalF h (k := 124) (by norm_num)).2.2
  have v5270 : σ (.n 5270) = ev 58 := by
    rw [← hev 58 (by norm_num)]; exact (vt_evalF h (k := 125) (by norm_num)).2.2
  have v5680 : σ (.n 5680) = ev 87 := by
    rw [← hev 87 (by norm_num)]; exact (vt_evalF h (k := 154) (by norm_num)).2.2
  have hB : σ (.n 6580) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 512)], [([87], 1), ([13, 87], 2), ([13, 87], 1)], [([57], 1)], [([58], 1)], [([], 0)]] := by
    simp only [v5680, v5270, v5259, v4632, v4575, v4461, a6010, a6009, a6008, a6007, e6006, a6005, a6004,
      e6003, a6002, a6001, e6000, a5999, a5998, e5997, a5996, a5995, a5994, a5993, a5992,
      a5991, a5990, a5989, e5988, a5987, a5986, a5985, a5984, a5983, e5982]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a6012, a6011, hB]

set_option maxRecDepth 10000 in
theorem vtB05_25F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6613) = σ (.n 6582) + σ (.n 1376) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 1024)], [([88], 1), ([13, 88], 2), ([13, 88], 1)], [([59], 1)], [([60], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6013 [
    .atom (.load (.n 6583) (.n 13) 0),
    .atom (.const (.n 6584) (word 2 0 0)),
    .atom (.mul (.n 6585) (.n 6583) (.n 6584)),
    .atom (.const (.n 6586) (word 1024 0 0)),
    .atom (.mul (.n 6587) (.n 4461) (.n 4575)),
    .atom (.mul (.n 6588) (.n 6586) (.n 6587)),
    .atom (.load (.n 6589) (.n 13) 1),
    .atom (.mul (.n 6590) (.n 6589) (.n 6588)),
    .atom (.add (.n 6591) (.n 6585) (.n 6590)),
    .atom (.const (.n 6592) (word 2 0 0)),
    .atom (.mul (.n 6593) (.n 4632) (.n 5691)),
    .atom (.mul (.n 6594) (.n 6592) (.n 6593)),
    .atom (.add (.n 6595) (.n 5691) (.n 6594)),
    .atom (.mul (.n 6596) (.n 4632) (.n 5691)),
    .atom (.add (.n 6597) (.n 6595) (.n 6596)),
    .atom (.load (.n 6598) (.n 13) 2),
    .atom (.mul (.n 6599) (.n 6598) (.n 6597)),
    .atom (.add (.n 6600) (.n 6591) (.n 6599)),
    .atom (.load (.n 6601) (.n 13) 3),
    .atom (.mul (.n 6602) (.n 6601) (.n 5281)),
    .atom (.add (.n 6603) (.n 6600) (.n 6602)),
    .atom (.load (.n 6604) (.n 13) 4),
    .atom (.mul (.n 6605) (.n 6604) (.n 5292)),
    .atom (.add (.n 6606) (.n 6603) (.n 6605)),
    .atom (.load (.n 6607) (.n 13) 5),
    .atom (.const (.n 6608) (word 0 0 0)),
    .atom (.mul (.n 6609) (.n 6607) (.n 6608)),
    .atom (.add (.n 6610) (.n 6606) (.n 6609)),
    .atom (.add (.n 6611) (.n 14) (.n 6610)),
    .atom (.mul (.n 6612) (.n 1376) (.n 6611)),
    .atom (.add (.n 6613) (.n 6582) (.n 6612))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6013, a6014, a6015, a6016, a6017, a6018, a6019, a6020, a6021, a6022, a6023, a6024, a6025, a6026,
    a6027, a6028, a6029, a6030, a6031, a6032, a6033, a6034, a6035, a6036, a6037, a6038, a6039,
    a6040, a6041, a6042, a6043, -⟩ := hs
  have e6013 := tb_loadHolds_unique a6013 (hw 0 (by norm_num))
  have e6019 := tb_loadHolds_unique a6019 (hw 1 (by norm_num))
  have e6028 := tb_loadHolds_unique a6028 (hw 2 (by norm_num))
  have e6031 := tb_loadHolds_unique a6031 (hw 3 (by norm_num))
  have e6034 := tb_loadHolds_unique a6034 (hw 4 (by norm_num))
  have e6037 := tb_loadHolds_unique a6037 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4575 : σ (.n 4575) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 80) (by norm_num)).2.2
  have v5281 : σ (.n 5281) = ev 59 := by
    rw [← hev 59 (by norm_num)]; exact (vt_evalF h (k := 126) (by norm_num)).2.2
  have v5292 : σ (.n 5292) = ev 60 := by
    rw [← hev 60 (by norm_num)]; exact (vt_evalF h (k := 127) (by norm_num)).2.2
  have v5691 : σ (.n 5691) = ev 88 := by
    rw [← hev 88 (by norm_num)]; exact (vt_evalF h (k := 155) (by norm_num)).2.2
  have hB : σ (.n 6611) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 1024)], [([88], 1), ([13, 88], 2), ([13, 88], 1)], [([59], 1)], [([60], 1)], [([], 0)]] := by
    simp only [v5691, v5292, v5281, v4632, v4575, v4461, a6041, a6040, a6039, a6038, e6037, a6036, a6035,
      e6034, a6033, a6032, e6031, a6030, a6029, e6028, a6027, a6026, a6025, a6024, a6023,
      a6022, a6021, a6020, e6019, a6018, a6017, a6016, a6015, a6014, e6013]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a6043, a6042, hB]

set_option maxRecDepth 10000 in
theorem vtB05_26F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6644) = σ (.n 6613) + σ (.n 1385) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 2048)], [([89], 1), ([13, 89], 2), ([13, 89], 1)], [([61], 1)], [([62], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6044 [
    .atom (.load (.n 6614) (.n 13) 0),
    .atom (.const (.n 6615) (word 2 0 0)),
    .atom (.mul (.n 6616) (.n 6614) (.n 6615)),
    .atom (.const (.n 6617) (word 2048 0 0)),
    .atom (.mul (.n 6618) (.n 4461) (.n 4575)),
    .atom (.mul (.n 6619) (.n 6617) (.n 6618)),
    .atom (.load (.n 6620) (.n 13) 1),
    .atom (.mul (.n 6621) (.n 6620) (.n 6619)),
    .atom (.add (.n 6622) (.n 6616) (.n 6621)),
    .atom (.const (.n 6623) (word 2 0 0)),
    .atom (.mul (.n 6624) (.n 4632) (.n 5715)),
    .atom (.mul (.n 6625) (.n 6623) (.n 6624)),
    .atom (.add (.n 6626) (.n 5715) (.n 6625)),
    .atom (.mul (.n 6627) (.n 4632) (.n 5715)),
    .atom (.add (.n 6628) (.n 6626) (.n 6627)),
    .atom (.load (.n 6629) (.n 13) 2),
    .atom (.mul (.n 6630) (.n 6629) (.n 6628)),
    .atom (.add (.n 6631) (.n 6622) (.n 6630)),
    .atom (.load (.n 6632) (.n 13) 3),
    .atom (.mul (.n 6633) (.n 6632) (.n 5316)),
    .atom (.add (.n 6634) (.n 6631) (.n 6633)),
    .atom (.load (.n 6635) (.n 13) 4),
    .atom (.mul (.n 6636) (.n 6635) (.n 5327)),
    .atom (.add (.n 6637) (.n 6634) (.n 6636)),
    .atom (.load (.n 6638) (.n 13) 5),
    .atom (.const (.n 6639) (word 0 0 0)),
    .atom (.mul (.n 6640) (.n 6638) (.n 6639)),
    .atom (.add (.n 6641) (.n 6637) (.n 6640)),
    .atom (.add (.n 6642) (.n 14) (.n 6641)),
    .atom (.mul (.n 6643) (.n 1385) (.n 6642)),
    .atom (.add (.n 6644) (.n 6613) (.n 6643))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6044, a6045, a6046, a6047, a6048, a6049, a6050, a6051, a6052, a6053, a6054, a6055, a6056, a6057,
    a6058, a6059, a6060, a6061, a6062, a6063, a6064, a6065, a6066, a6067, a6068, a6069, a6070,
    a6071, a6072, a6073, a6074, -⟩ := hs
  have e6044 := tb_loadHolds_unique a6044 (hw 0 (by norm_num))
  have e6050 := tb_loadHolds_unique a6050 (hw 1 (by norm_num))
  have e6059 := tb_loadHolds_unique a6059 (hw 2 (by norm_num))
  have e6062 := tb_loadHolds_unique a6062 (hw 3 (by norm_num))
  have e6065 := tb_loadHolds_unique a6065 (hw 4 (by norm_num))
  have e6068 := tb_loadHolds_unique a6068 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4575 : σ (.n 4575) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 80) (by norm_num)).2.2
  have v5316 : σ (.n 5316) = ev 61 := by
    rw [← hev 61 (by norm_num)]; exact (vt_evalF h (k := 128) (by norm_num)).2.2
  have v5327 : σ (.n 5327) = ev 62 := by
    rw [← hev 62 (by norm_num)]; exact (vt_evalF h (k := 129) (by norm_num)).2.2
  have v5715 : σ (.n 5715) = ev 89 := by
    rw [← hev 89 (by norm_num)]; exact (vt_evalF h (k := 156) (by norm_num)).2.2
  have hB : σ (.n 6642) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 2048)], [([89], 1), ([13, 89], 2), ([13, 89], 1)], [([61], 1)], [([62], 1)], [([], 0)]] := by
    simp only [v5715, v5327, v5316, v4632, v4575, v4461, a6072, a6071, a6070, a6069, e6068, a6067, a6066,
      e6065, a6064, a6063, e6062, a6061, a6060, e6059, a6058, a6057, a6056, a6055, a6054,
      a6053, a6052, a6051, e6050, a6049, a6048, a6047, a6046, a6045, e6044]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a6074, a6073, hB]

set_option maxRecDepth 10000 in
theorem vtB05_27F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6675) = σ (.n 6644) + σ (.n 1394) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 4096)], [([90], 1), ([13, 90], 2), ([13, 90], 1)], [([63], 1)], [([64], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6075 [
    .atom (.load (.n 6645) (.n 13) 0),
    .atom (.const (.n 6646) (word 2 0 0)),
    .atom (.mul (.n 6647) (.n 6645) (.n 6646)),
    .atom (.const (.n 6648) (word 4096 0 0)),
    .atom (.mul (.n 6649) (.n 4461) (.n 4575)),
    .atom (.mul (.n 6650) (.n 6648) (.n 6649)),
    .atom (.load (.n 6651) (.n 13) 1),
    .atom (.mul (.n 6652) (.n 6651) (.n 6650)),
    .atom (.add (.n 6653) (.n 6647) (.n 6652)),
    .atom (.const (.n 6654) (word 2 0 0)),
    .atom (.mul (.n 6655) (.n 4632) (.n 5726)),
    .atom (.mul (.n 6656) (.n 6654) (.n 6655)),
    .atom (.add (.n 6657) (.n 5726) (.n 6656)),
    .atom (.mul (.n 6658) (.n 4632) (.n 5726)),
    .atom (.add (.n 6659) (.n 6657) (.n 6658)),
    .atom (.load (.n 6660) (.n 13) 2),
    .atom (.mul (.n 6661) (.n 6660) (.n 6659)),
    .atom (.add (.n 6662) (.n 6653) (.n 6661)),
    .atom (.load (.n 6663) (.n 13) 3),
    .atom (.mul (.n 6664) (.n 6663) (.n 5338)),
    .atom (.add (.n 6665) (.n 6662) (.n 6664)),
    .atom (.load (.n 6666) (.n 13) 4),
    .atom (.mul (.n 6667) (.n 6666) (.n 5349)),
    .atom (.add (.n 6668) (.n 6665) (.n 6667)),
    .atom (.load (.n 6669) (.n 13) 5),
    .atom (.const (.n 6670) (word 0 0 0)),
    .atom (.mul (.n 6671) (.n 6669) (.n 6670)),
    .atom (.add (.n 6672) (.n 6668) (.n 6671)),
    .atom (.add (.n 6673) (.n 14) (.n 6672)),
    .atom (.mul (.n 6674) (.n 1394) (.n 6673)),
    .atom (.add (.n 6675) (.n 6644) (.n 6674))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6075, a6076, a6077, a6078, a6079, a6080, a6081, a6082, a6083, a6084, a6085, a6086, a6087, a6088,
    a6089, a6090, a6091, a6092, a6093, a6094, a6095, a6096, a6097, a6098, a6099, a6100, a6101,
    a6102, a6103, a6104, a6105, -⟩ := hs
  have e6075 := tb_loadHolds_unique a6075 (hw 0 (by norm_num))
  have e6081 := tb_loadHolds_unique a6081 (hw 1 (by norm_num))
  have e6090 := tb_loadHolds_unique a6090 (hw 2 (by norm_num))
  have e6093 := tb_loadHolds_unique a6093 (hw 3 (by norm_num))
  have e6096 := tb_loadHolds_unique a6096 (hw 4 (by norm_num))
  have e6099 := tb_loadHolds_unique a6099 (hw 5 (by norm_num))
  have v4461 : σ (.n 4461) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4575 : σ (.n 4575) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 80) (by norm_num)).2.2
  have v5338 : σ (.n 5338) = ev 63 := by
    rw [← hev 63 (by norm_num)]; exact (vt_evalF h (k := 130) (by norm_num)).2.2
  have v5349 : σ (.n 5349) = ev 64 := by
    rw [← hev 64 (by norm_num)]; exact (vt_evalF h (k := 131) (by norm_num)).2.2
  have v5726 : σ (.n 5726) = ev 90 := by
    rw [← hev 90 (by norm_num)]; exact (vt_evalF h (k := 157) (by norm_num)).2.2
  have hB : σ (.n 6673) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 4096)], [([90], 1), ([13, 90], 2), ([13, 90], 1)], [([63], 1)], [([64], 1)], [([], 0)]] := by
    simp only [v5726, v5349, v5338, v4632, v4575, v4461, a6103, a6102, a6101, a6100, e6099, a6098, a6097,
      e6096, a6095, a6094, e6093, a6092, a6091, e6090, a6089, a6088, a6087, a6086, a6085,
      a6084, a6083, a6082, e6081, a6080, a6079, a6078, a6077, a6076, e6075]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a6105, a6104, hB]

end
end LeanVM.Guest.B1.Tables
