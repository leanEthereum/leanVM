/-
  LeanVM.Guest.B1.Tables.VtC.FForms5b

  `Vt/FormsT5b.lean` on the window `VtF` (generated: scripts/b1c-vt/gentwins.py).

  Do not edit: `scripts/b1c-vt/all.py` writes it (`regen-guest.sh`, step `vt`).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FEvals
public import LeanVM.Guest.B1.Tables.Vt.FormsT5b

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
theorem vtD5_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5778) = σ (.n 1381) * vtSlots W ev 0
      [[], [([0], 3)], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4726 [
    .atom (.const (.n 5150) (word 3 0)),
    .atom (.mul (.n 5151) (.n 5150) (.n 4032)),
    .atom (.copy (.n 5152) (.n 5151))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4726, a4727, a4728, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5352 [
    .atom (.load (.n 5776) (.n 13) 1),
    .atom (.mul (.n 5777) (.n 5776) (.n 5152)),
    .atom (.mul (.n 5778) (.n 1381) (.n 5777))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5352, a5353, a5354, -⟩ := hs1
  have e5352 := tb_loadHolds_unique a5352 (hw 1 (by norm_num))
  have v4032 : σ (.n 4032) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 61) (by norm_num)).2.2
  have hB : σ (.n 5777) = vtSlots W ev 0 [[], [([0], 3)], []] := by
    simp only [v4032, a5353, e5352, a4728, a4727, a4726]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5354, hB]

set_option maxRecDepth 10000 in
theorem vtD5_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5782) = σ (.n 5778) + σ (.n 1383) * vtSlots W ev 0
      [[], [], [([91], 3)], [], [], [], [], [], [], [], [], [], [], [], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4729 [
    .atom (.const (.n 5153) (word 3 0)),
    .atom (.mul (.n 5154) (.n 5153) (.n 4695)),
    .atom (.copy (.n 5155) (.n 5154))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4729, a4730, a4731, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5355 [
    .atom (.load (.n 5779) (.n 13) 2),
    .atom (.mul (.n 5780) (.n 5779) (.n 5155)),
    .atom (.mul (.n 5781) (.n 1383) (.n 5780)),
    .atom (.add (.n 5782) (.n 5778) (.n 5781))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5355, a5356, a5357, a5358, -⟩ := hs1
  have e5355 := tb_loadHolds_unique a5355 (hw 2 (by norm_num))
  have v4695 : σ (.n 4695) = ev 91 := by
    rw [← hev 91 (by norm_num)]; exact (vt_evalF h (k := 152) (by norm_num)).2.2
  have hB : σ (.n 5780) = vtSlots W ev 0 [[], [], [([91], 3)], [], [], [], [], [], [], [], [], [], [], [], [], []] := by
    simp only [v4695, a5356, e5355, a4731, a4730, a4729]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5358, a5357, hB]

set_option maxRecDepth 10000 in
theorem vtD5_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5786) = σ (.n 5782) + σ (.n 1385) * vtSlots W ev 0
      [[], [], [([65], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4732 [
    .atom (.const (.n 5156) (word 3 0)),
    .atom (.mul (.n 5157) (.n 5156) (.n 4500)),
    .atom (.copy (.n 5158) (.n 5157))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4732, a4733, a4734, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5359 [
    .atom (.load (.n 5783) (.n 13) 2),
    .atom (.mul (.n 5784) (.n 5783) (.n 5158)),
    .atom (.mul (.n 5785) (.n 1385) (.n 5784)),
    .atom (.add (.n 5786) (.n 5782) (.n 5785))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5359, a5360, a5361, a5362, -⟩ := hs1
  have e5359 := tb_loadHolds_unique a5359 (hw 2 (by norm_num))
  have v4500 : σ (.n 4500) = ev 65 := by
    rw [← hev 65 (by norm_num)]; exact (vt_evalF h (k := 126) (by norm_num)).2.2
  have hB : σ (.n 5784) = vtSlots W ev 0 [[], [], [([65], 3)], [], []] := by
    simp only [v4500, a5360, e5359, a4734, a4733, a4732]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5362, a5361, hB]

set_option maxRecDepth 10000 in
theorem vtD5_3F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5790) = σ (.n 5786) + σ (.n 1387) * vtSlots W ev 0
      [[], [], [([66], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4735 [
    .atom (.const (.n 5159) (word 3 0)),
    .atom (.mul (.n 5160) (.n 5159) (.n 4504)),
    .atom (.copy (.n 5161) (.n 5160))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4735, a4736, a4737, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5363 [
    .atom (.load (.n 5787) (.n 13) 2),
    .atom (.mul (.n 5788) (.n 5787) (.n 5161)),
    .atom (.mul (.n 5789) (.n 1387) (.n 5788)),
    .atom (.add (.n 5790) (.n 5786) (.n 5789))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5363, a5364, a5365, a5366, -⟩ := hs1
  have e5363 := tb_loadHolds_unique a5363 (hw 2 (by norm_num))
  have v4504 : σ (.n 4504) = ev 66 := by
    rw [← hev 66 (by norm_num)]; exact (vt_evalF h (k := 127) (by norm_num)).2.2
  have hB : σ (.n 5788) = vtSlots W ev 0 [[], [], [([66], 3)], [], []] := by
    simp only [v4504, a5364, e5363, a4737, a4736, a4735]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5366, a5365, hB]

set_option maxRecDepth 10000 in
theorem vtD5_4F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5794) = σ (.n 5790) + σ (.n 1389) * vtSlots W ev 0
      [[], [], [([67], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4738 [
    .atom (.const (.n 5162) (word 3 0)),
    .atom (.mul (.n 5163) (.n 5162) (.n 4521)),
    .atom (.copy (.n 5164) (.n 5163))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4738, a4739, a4740, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5367 [
    .atom (.load (.n 5791) (.n 13) 2),
    .atom (.mul (.n 5792) (.n 5791) (.n 5164)),
    .atom (.mul (.n 5793) (.n 1389) (.n 5792)),
    .atom (.add (.n 5794) (.n 5790) (.n 5793))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5367, a5368, a5369, a5370, -⟩ := hs1
  have e5367 := tb_loadHolds_unique a5367 (hw 2 (by norm_num))
  have v4521 : σ (.n 4521) = ev 67 := by
    rw [← hev 67 (by norm_num)]; exact (vt_evalF h (k := 128) (by norm_num)).2.2
  have hB : σ (.n 5792) = vtSlots W ev 0 [[], [], [([67], 3)], [], []] := by
    simp only [v4521, a5368, e5367, a4740, a4739, a4738]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5370, a5369, hB]

set_option maxRecDepth 10000 in
theorem vtD5_5F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5798) = σ (.n 5794) + σ (.n 1391) * vtSlots W ev 0
      [[], [], [([68], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4741 [
    .atom (.const (.n 5165) (word 3 0)),
    .atom (.mul (.n 5166) (.n 5165) (.n 4525)),
    .atom (.copy (.n 5167) (.n 5166))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4741, a4742, a4743, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5371 [
    .atom (.load (.n 5795) (.n 13) 2),
    .atom (.mul (.n 5796) (.n 5795) (.n 5167)),
    .atom (.mul (.n 5797) (.n 1391) (.n 5796)),
    .atom (.add (.n 5798) (.n 5794) (.n 5797))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5371, a5372, a5373, a5374, -⟩ := hs1
  have e5371 := tb_loadHolds_unique a5371 (hw 2 (by norm_num))
  have v4525 : σ (.n 4525) = ev 68 := by
    rw [← hev 68 (by norm_num)]; exact (vt_evalF h (k := 129) (by norm_num)).2.2
  have hB : σ (.n 5796) = vtSlots W ev 0 [[], [], [([68], 3)], [], []] := by
    simp only [v4525, a5372, e5371, a4743, a4742, a4741]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5374, a5373, hB]

set_option maxRecDepth 10000 in
theorem vtD5_6F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5802) = σ (.n 5798) + σ (.n 1393) * vtSlots W ev 0
      [[], [], [([69], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4744 [
    .atom (.const (.n 5168) (word 3 0)),
    .atom (.mul (.n 5169) (.n 5168) (.n 4529)),
    .atom (.copy (.n 5170) (.n 5169))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4744, a4745, a4746, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5375 [
    .atom (.load (.n 5799) (.n 13) 2),
    .atom (.mul (.n 5800) (.n 5799) (.n 5170)),
    .atom (.mul (.n 5801) (.n 1393) (.n 5800)),
    .atom (.add (.n 5802) (.n 5798) (.n 5801))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5375, a5376, a5377, a5378, -⟩ := hs1
  have e5375 := tb_loadHolds_unique a5375 (hw 2 (by norm_num))
  have v4529 : σ (.n 4529) = ev 69 := by
    rw [← hev 69 (by norm_num)]; exact (vt_evalF h (k := 130) (by norm_num)).2.2
  have hB : σ (.n 5800) = vtSlots W ev 0 [[], [], [([69], 3)], [], []] := by
    simp only [v4529, a5376, e5375, a4746, a4745, a4744]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5378, a5377, hB]

set_option maxRecDepth 10000 in
theorem vtD5_7F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5806) = σ (.n 5802) + σ (.n 1395) * vtSlots W ev 0
      [[], [], [([70], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4747 [
    .atom (.const (.n 5171) (word 3 0)),
    .atom (.mul (.n 5172) (.n 5171) (.n 4533)),
    .atom (.copy (.n 5173) (.n 5172))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4747, a4748, a4749, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5379 [
    .atom (.load (.n 5803) (.n 13) 2),
    .atom (.mul (.n 5804) (.n 5803) (.n 5173)),
    .atom (.mul (.n 5805) (.n 1395) (.n 5804)),
    .atom (.add (.n 5806) (.n 5802) (.n 5805))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5379, a5380, a5381, a5382, -⟩ := hs1
  have e5379 := tb_loadHolds_unique a5379 (hw 2 (by norm_num))
  have v4533 : σ (.n 4533) = ev 70 := by
    rw [← hev 70 (by norm_num)]; exact (vt_evalF h (k := 131) (by norm_num)).2.2
  have hB : σ (.n 5804) = vtSlots W ev 0 [[], [], [([70], 3)], [], []] := by
    simp only [v4533, a5380, e5379, a4749, a4748, a4747]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5382, a5381, hB]

set_option maxRecDepth 10000 in
theorem vtD5_8F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5810) = σ (.n 5806) + σ (.n 1397) * vtSlots W ev 0
      [[], [], [([71], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4750 [
    .atom (.const (.n 5174) (word 3 0)),
    .atom (.mul (.n 5175) (.n 5174) (.n 4550)),
    .atom (.copy (.n 5176) (.n 5175))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4750, a4751, a4752, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5383 [
    .atom (.load (.n 5807) (.n 13) 2),
    .atom (.mul (.n 5808) (.n 5807) (.n 5176)),
    .atom (.mul (.n 5809) (.n 1397) (.n 5808)),
    .atom (.add (.n 5810) (.n 5806) (.n 5809))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5383, a5384, a5385, a5386, -⟩ := hs1
  have e5383 := tb_loadHolds_unique a5383 (hw 2 (by norm_num))
  have v4550 : σ (.n 4550) = ev 71 := by
    rw [← hev 71 (by norm_num)]; exact (vt_evalF h (k := 132) (by norm_num)).2.2
  have hB : σ (.n 5808) = vtSlots W ev 0 [[], [], [([71], 3)], [], []] := by
    simp only [v4550, a5384, e5383, a4752, a4751, a4750]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5386, a5385, hB]

set_option maxRecDepth 10000 in
theorem vtD5_9F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5814) = σ (.n 5810) + σ (.n 1399) * vtSlots W ev 0
      [[], [], [([72], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4753 [
    .atom (.const (.n 5177) (word 3 0)),
    .atom (.mul (.n 5178) (.n 5177) (.n 4554)),
    .atom (.copy (.n 5179) (.n 5178))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4753, a4754, a4755, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5387 [
    .atom (.load (.n 5811) (.n 13) 2),
    .atom (.mul (.n 5812) (.n 5811) (.n 5179)),
    .atom (.mul (.n 5813) (.n 1399) (.n 5812)),
    .atom (.add (.n 5814) (.n 5810) (.n 5813))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5387, a5388, a5389, a5390, -⟩ := hs1
  have e5387 := tb_loadHolds_unique a5387 (hw 2 (by norm_num))
  have v4554 : σ (.n 4554) = ev 72 := by
    rw [← hev 72 (by norm_num)]; exact (vt_evalF h (k := 133) (by norm_num)).2.2
  have hB : σ (.n 5812) = vtSlots W ev 0 [[], [], [([72], 3)], [], []] := by
    simp only [v4554, a5388, e5387, a4755, a4754, a4753]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5390, a5389, hB]

set_option maxRecDepth 10000 in
theorem vtD5_10F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5818) = σ (.n 5814) + σ (.n 1401) * vtSlots W ev 0
      [[], [], [([73], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4756 [
    .atom (.const (.n 5180) (word 3 0)),
    .atom (.mul (.n 5181) (.n 5180) (.n 4558)),
    .atom (.copy (.n 5182) (.n 5181))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4756, a4757, a4758, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5391 [
    .atom (.load (.n 5815) (.n 13) 2),
    .atom (.mul (.n 5816) (.n 5815) (.n 5182)),
    .atom (.mul (.n 5817) (.n 1401) (.n 5816)),
    .atom (.add (.n 5818) (.n 5814) (.n 5817))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5391, a5392, a5393, a5394, -⟩ := hs1
  have e5391 := tb_loadHolds_unique a5391 (hw 2 (by norm_num))
  have v4558 : σ (.n 4558) = ev 73 := by
    rw [← hev 73 (by norm_num)]; exact (vt_evalF h (k := 134) (by norm_num)).2.2
  have hB : σ (.n 5816) = vtSlots W ev 0 [[], [], [([73], 3)], [], []] := by
    simp only [v4558, a5392, e5391, a4758, a4757, a4756]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5394, a5393, hB]

set_option maxRecDepth 10000 in
theorem vtD5_11F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5822) = σ (.n 5818) + σ (.n 1403) * vtSlots W ev 0
      [[], [], [([74], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4759 [
    .atom (.const (.n 5183) (word 3 0)),
    .atom (.mul (.n 5184) (.n 5183) (.n 4562)),
    .atom (.copy (.n 5185) (.n 5184))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4759, a4760, a4761, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5395 [
    .atom (.load (.n 5819) (.n 13) 2),
    .atom (.mul (.n 5820) (.n 5819) (.n 5185)),
    .atom (.mul (.n 5821) (.n 1403) (.n 5820)),
    .atom (.add (.n 5822) (.n 5818) (.n 5821))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5395, a5396, a5397, a5398, -⟩ := hs1
  have e5395 := tb_loadHolds_unique a5395 (hw 2 (by norm_num))
  have v4562 : σ (.n 4562) = ev 74 := by
    rw [← hev 74 (by norm_num)]; exact (vt_evalF h (k := 135) (by norm_num)).2.2
  have hB : σ (.n 5820) = vtSlots W ev 0 [[], [], [([74], 3)], [], []] := by
    simp only [v4562, a5396, e5395, a4761, a4760, a4759]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5398, a5397, hB]

set_option maxRecDepth 10000 in
theorem vtD5_12F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5826) = σ (.n 5822) + σ (.n 1405) * vtSlots W ev 0
      [[], [], [([75], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4762 [
    .atom (.const (.n 5186) (word 3 0)),
    .atom (.mul (.n 5187) (.n 5186) (.n 4579)),
    .atom (.copy (.n 5188) (.n 5187))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4762, a4763, a4764, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5399 [
    .atom (.load (.n 5823) (.n 13) 2),
    .atom (.mul (.n 5824) (.n 5823) (.n 5188)),
    .atom (.mul (.n 5825) (.n 1405) (.n 5824)),
    .atom (.add (.n 5826) (.n 5822) (.n 5825))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5399, a5400, a5401, a5402, -⟩ := hs1
  have e5399 := tb_loadHolds_unique a5399 (hw 2 (by norm_num))
  have v4579 : σ (.n 4579) = ev 75 := by
    rw [← hev 75 (by norm_num)]; exact (vt_evalF h (k := 136) (by norm_num)).2.2
  have hB : σ (.n 5824) = vtSlots W ev 0 [[], [], [([75], 3)], [], []] := by
    simp only [v4579, a5400, e5399, a4764, a4763, a4762]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5402, a5401, hB]

set_option maxRecDepth 10000 in
theorem vtD5_13F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5830) = σ (.n 5826) + σ (.n 1407) * vtSlots W ev 0
      [[], [], [([76], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4765 [
    .atom (.const (.n 5189) (word 3 0)),
    .atom (.mul (.n 5190) (.n 5189) (.n 4583)),
    .atom (.copy (.n 5191) (.n 5190))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4765, a4766, a4767, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5403 [
    .atom (.load (.n 5827) (.n 13) 2),
    .atom (.mul (.n 5828) (.n 5827) (.n 5191)),
    .atom (.mul (.n 5829) (.n 1407) (.n 5828)),
    .atom (.add (.n 5830) (.n 5826) (.n 5829))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5403, a5404, a5405, a5406, -⟩ := hs1
  have e5403 := tb_loadHolds_unique a5403 (hw 2 (by norm_num))
  have v4583 : σ (.n 4583) = ev 76 := by
    rw [← hev 76 (by norm_num)]; exact (vt_evalF h (k := 137) (by norm_num)).2.2
  have hB : σ (.n 5828) = vtSlots W ev 0 [[], [], [([76], 3)], [], []] := by
    simp only [v4583, a5404, e5403, a4767, a4766, a4765]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5406, a5405, hB]

set_option maxRecDepth 10000 in
theorem vtD5_14F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5834) = σ (.n 5830) + σ (.n 1409) * vtSlots W ev 0
      [[], [], [([77], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4768 [
    .atom (.const (.n 5192) (word 3 0)),
    .atom (.mul (.n 5193) (.n 5192) (.n 4587)),
    .atom (.copy (.n 5194) (.n 5193))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4768, a4769, a4770, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5407 [
    .atom (.load (.n 5831) (.n 13) 2),
    .atom (.mul (.n 5832) (.n 5831) (.n 5194)),
    .atom (.mul (.n 5833) (.n 1409) (.n 5832)),
    .atom (.add (.n 5834) (.n 5830) (.n 5833))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5407, a5408, a5409, a5410, -⟩ := hs1
  have e5407 := tb_loadHolds_unique a5407 (hw 2 (by norm_num))
  have v4587 : σ (.n 4587) = ev 77 := by
    rw [← hev 77 (by norm_num)]; exact (vt_evalF h (k := 138) (by norm_num)).2.2
  have hB : σ (.n 5832) = vtSlots W ev 0 [[], [], [([77], 3)], [], []] := by
    simp only [v4587, a5408, e5407, a4770, a4769, a4768]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5410, a5409, hB]

set_option maxRecDepth 10000 in
theorem vtD5_15F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5838) = σ (.n 5834) + σ (.n 1411) * vtSlots W ev 0
      [[], [], [([78], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4771 [
    .atom (.const (.n 5195) (word 3 0)),
    .atom (.mul (.n 5196) (.n 5195) (.n 4591)),
    .atom (.copy (.n 5197) (.n 5196))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4771, a4772, a4773, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5411 [
    .atom (.load (.n 5835) (.n 13) 2),
    .atom (.mul (.n 5836) (.n 5835) (.n 5197)),
    .atom (.mul (.n 5837) (.n 1411) (.n 5836)),
    .atom (.add (.n 5838) (.n 5834) (.n 5837))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5411, a5412, a5413, a5414, -⟩ := hs1
  have e5411 := tb_loadHolds_unique a5411 (hw 2 (by norm_num))
  have v4591 : σ (.n 4591) = ev 78 := by
    rw [← hev 78 (by norm_num)]; exact (vt_evalF h (k := 139) (by norm_num)).2.2
  have hB : σ (.n 5836) = vtSlots W ev 0 [[], [], [([78], 3)], [], []] := by
    simp only [v4591, a5412, e5411, a4773, a4772, a4771]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5414, a5413, hB]

set_option maxRecDepth 10000 in
theorem vtD5_16F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5842) = σ (.n 5838) + σ (.n 1413) * vtSlots W ev 0
      [[], [], [([12, 79], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4774 [
    .atom (.const (.n 5198) (word 3 0)),
    .atom (.mul (.n 5199) (.n 4119) (.n 4608)),
    .atom (.mul (.n 5200) (.n 5198) (.n 5199)),
    .atom (.copy (.n 5201) (.n 5200))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4774, a4775, a4776, a4777, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5415 [
    .atom (.load (.n 5839) (.n 13) 2),
    .atom (.mul (.n 5840) (.n 5839) (.n 5201)),
    .atom (.mul (.n 5841) (.n 1413) (.n 5840)),
    .atom (.add (.n 5842) (.n 5838) (.n 5841))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5415, a5416, a5417, a5418, -⟩ := hs1
  have e5415 := tb_loadHolds_unique a5415 (hw 2 (by norm_num))
  have v4119 : σ (.n 4119) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_evalF h (k := 73) (by norm_num)).2.2
  have v4608 : σ (.n 4608) = ev 79 := by
    rw [← hev 79 (by norm_num)]; exact (vt_evalF h (k := 140) (by norm_num)).2.2
  have hB : σ (.n 5840) = vtSlots W ev 0 [[], [], [([12, 79], 3)], [], []] := by
    simp only [v4608, v4119, a5416, e5415, a4777, a4776, a4775, a4774]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5418, a5417, hB]

set_option maxRecDepth 10000 in
theorem vtD5_17F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5846) = σ (.n 5842) + σ (.n 1415) * vtSlots W ev 0
      [[], [], [([13, 80], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4778 [
    .atom (.const (.n 5202) (word 3 0)),
    .atom (.mul (.n 5203) (.n 4123) (.n 4612)),
    .atom (.mul (.n 5204) (.n 5202) (.n 5203)),
    .atom (.copy (.n 5205) (.n 5204))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4778, a4779, a4780, a4781, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5419 [
    .atom (.load (.n 5843) (.n 13) 2),
    .atom (.mul (.n 5844) (.n 5843) (.n 5205)),
    .atom (.mul (.n 5845) (.n 1415) (.n 5844)),
    .atom (.add (.n 5846) (.n 5842) (.n 5845))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5419, a5420, a5421, a5422, -⟩ := hs1
  have e5419 := tb_loadHolds_unique a5419 (hw 2 (by norm_num))
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4612 : σ (.n 4612) = ev 80 := by
    rw [← hev 80 (by norm_num)]; exact (vt_evalF h (k := 141) (by norm_num)).2.2
  have hB : σ (.n 5844) = vtSlots W ev 0 [[], [], [([13, 80], 3)], [], []] := by
    simp only [v4612, v4123, a5420, e5419, a4781, a4780, a4779, a4778]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5422, a5421, hB]

set_option maxRecDepth 10000 in
theorem vtD5_18F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5850) = σ (.n 5846) + σ (.n 1417) * vtSlots W ev 0
      [[], [], [([13, 81], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4782 [
    .atom (.const (.n 5206) (word 3 0)),
    .atom (.mul (.n 5207) (.n 4123) (.n 4616)),
    .atom (.mul (.n 5208) (.n 5206) (.n 5207)),
    .atom (.copy (.n 5209) (.n 5208))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4782, a4783, a4784, a4785, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5423 [
    .atom (.load (.n 5847) (.n 13) 2),
    .atom (.mul (.n 5848) (.n 5847) (.n 5209)),
    .atom (.mul (.n 5849) (.n 1417) (.n 5848)),
    .atom (.add (.n 5850) (.n 5846) (.n 5849))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5423, a5424, a5425, a5426, -⟩ := hs1
  have e5423 := tb_loadHolds_unique a5423 (hw 2 (by norm_num))
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4616 : σ (.n 4616) = ev 81 := by
    rw [← hev 81 (by norm_num)]; exact (vt_evalF h (k := 142) (by norm_num)).2.2
  have hB : σ (.n 5848) = vtSlots W ev 0 [[], [], [([13, 81], 3)], [], []] := by
    simp only [v4616, v4123, a5424, e5423, a4785, a4784, a4783, a4782]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5426, a5425, hB]

set_option maxRecDepth 10000 in
theorem vtD5_19F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5854) = σ (.n 5850) + σ (.n 1419) * vtSlots W ev 0
      [[], [], [([13, 82], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4786 [
    .atom (.const (.n 5210) (word 3 0)),
    .atom (.mul (.n 5211) (.n 4123) (.n 4620)),
    .atom (.mul (.n 5212) (.n 5210) (.n 5211)),
    .atom (.copy (.n 5213) (.n 5212))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4786, a4787, a4788, a4789, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5427 [
    .atom (.load (.n 5851) (.n 13) 2),
    .atom (.mul (.n 5852) (.n 5851) (.n 5213)),
    .atom (.mul (.n 5853) (.n 1419) (.n 5852)),
    .atom (.add (.n 5854) (.n 5850) (.n 5853))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5427, a5428, a5429, a5430, -⟩ := hs1
  have e5427 := tb_loadHolds_unique a5427 (hw 2 (by norm_num))
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4620 : σ (.n 4620) = ev 82 := by
    rw [← hev 82 (by norm_num)]; exact (vt_evalF h (k := 143) (by norm_num)).2.2
  have hB : σ (.n 5852) = vtSlots W ev 0 [[], [], [([13, 82], 3)], [], []] := by
    simp only [v4620, v4123, a5428, e5427, a4789, a4788, a4787, a4786]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5430, a5429, hB]

set_option maxRecDepth 10000 in
theorem vtD5_20F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5858) = σ (.n 5854) + σ (.n 1421) * vtSlots W ev 0
      [[], [], [([13, 83], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4790 [
    .atom (.const (.n 5214) (word 3 0)),
    .atom (.mul (.n 5215) (.n 4123) (.n 4637)),
    .atom (.mul (.n 5216) (.n 5214) (.n 5215)),
    .atom (.copy (.n 5217) (.n 5216))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4790, a4791, a4792, a4793, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5431 [
    .atom (.load (.n 5855) (.n 13) 2),
    .atom (.mul (.n 5856) (.n 5855) (.n 5217)),
    .atom (.mul (.n 5857) (.n 1421) (.n 5856)),
    .atom (.add (.n 5858) (.n 5854) (.n 5857))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5431, a5432, a5433, a5434, -⟩ := hs1
  have e5431 := tb_loadHolds_unique a5431 (hw 2 (by norm_num))
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4637 : σ (.n 4637) = ev 83 := by
    rw [← hev 83 (by norm_num)]; exact (vt_evalF h (k := 144) (by norm_num)).2.2
  have hB : σ (.n 5856) = vtSlots W ev 0 [[], [], [([13, 83], 3)], [], []] := by
    simp only [v4637, v4123, a5432, e5431, a4793, a4792, a4791, a4790]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5434, a5433, hB]

set_option maxRecDepth 10000 in
theorem vtD5_21F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5862) = σ (.n 5858) + σ (.n 1423) * vtSlots W ev 0
      [[], [], [([13, 84], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4794 [
    .atom (.const (.n 5218) (word 3 0)),
    .atom (.mul (.n 5219) (.n 4123) (.n 4641)),
    .atom (.mul (.n 5220) (.n 5218) (.n 5219)),
    .atom (.copy (.n 5221) (.n 5220))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4794, a4795, a4796, a4797, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5435 [
    .atom (.load (.n 5859) (.n 13) 2),
    .atom (.mul (.n 5860) (.n 5859) (.n 5221)),
    .atom (.mul (.n 5861) (.n 1423) (.n 5860)),
    .atom (.add (.n 5862) (.n 5858) (.n 5861))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5435, a5436, a5437, a5438, -⟩ := hs1
  have e5435 := tb_loadHolds_unique a5435 (hw 2 (by norm_num))
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4641 : σ (.n 4641) = ev 84 := by
    rw [← hev 84 (by norm_num)]; exact (vt_evalF h (k := 145) (by norm_num)).2.2
  have hB : σ (.n 5860) = vtSlots W ev 0 [[], [], [([13, 84], 3)], [], []] := by
    simp only [v4641, v4123, a5436, e5435, a4797, a4796, a4795, a4794]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5438, a5437, hB]

set_option maxRecDepth 10000 in
theorem vtD5_22F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5866) = σ (.n 5862) + σ (.n 1425) * vtSlots W ev 0
      [[], [], [([13, 85], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4798 [
    .atom (.const (.n 5222) (word 3 0)),
    .atom (.mul (.n 5223) (.n 4123) (.n 4645)),
    .atom (.mul (.n 5224) (.n 5222) (.n 5223)),
    .atom (.copy (.n 5225) (.n 5224))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4798, a4799, a4800, a4801, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5439 [
    .atom (.load (.n 5863) (.n 13) 2),
    .atom (.mul (.n 5864) (.n 5863) (.n 5225)),
    .atom (.mul (.n 5865) (.n 1425) (.n 5864)),
    .atom (.add (.n 5866) (.n 5862) (.n 5865))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5439, a5440, a5441, a5442, -⟩ := hs1
  have e5439 := tb_loadHolds_unique a5439 (hw 2 (by norm_num))
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4645 : σ (.n 4645) = ev 85 := by
    rw [← hev 85 (by norm_num)]; exact (vt_evalF h (k := 146) (by norm_num)).2.2
  have hB : σ (.n 5864) = vtSlots W ev 0 [[], [], [([13, 85], 3)], [], []] := by
    simp only [v4645, v4123, a5440, e5439, a4801, a4800, a4799, a4798]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5442, a5441, hB]

set_option maxRecDepth 10000 in
theorem vtD5_23F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5870) = σ (.n 5866) + σ (.n 1427) * vtSlots W ev 0
      [[], [], [([13, 86], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4802 [
    .atom (.const (.n 5226) (word 3 0)),
    .atom (.mul (.n 5227) (.n 4123) (.n 4649)),
    .atom (.mul (.n 5228) (.n 5226) (.n 5227)),
    .atom (.copy (.n 5229) (.n 5228))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4802, a4803, a4804, a4805, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5443 [
    .atom (.load (.n 5867) (.n 13) 2),
    .atom (.mul (.n 5868) (.n 5867) (.n 5229)),
    .atom (.mul (.n 5869) (.n 1427) (.n 5868)),
    .atom (.add (.n 5870) (.n 5866) (.n 5869))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5443, a5444, a5445, a5446, -⟩ := hs1
  have e5443 := tb_loadHolds_unique a5443 (hw 2 (by norm_num))
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4649 : σ (.n 4649) = ev 86 := by
    rw [← hev 86 (by norm_num)]; exact (vt_evalF h (k := 147) (by norm_num)).2.2
  have hB : σ (.n 5868) = vtSlots W ev 0 [[], [], [([13, 86], 3)], [], []] := by
    simp only [v4649, v4123, a5444, e5443, a4805, a4804, a4803, a4802]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5446, a5445, hB]

set_option maxRecDepth 10000 in
theorem vtD5_24F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5874) = σ (.n 5870) + σ (.n 1429) * vtSlots W ev 0
      [[], [], [([13, 87], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4806 [
    .atom (.const (.n 5230) (word 3 0)),
    .atom (.mul (.n 5231) (.n 4123) (.n 4666)),
    .atom (.mul (.n 5232) (.n 5230) (.n 5231)),
    .atom (.copy (.n 5233) (.n 5232))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4806, a4807, a4808, a4809, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5447 [
    .atom (.load (.n 5871) (.n 13) 2),
    .atom (.mul (.n 5872) (.n 5871) (.n 5233)),
    .atom (.mul (.n 5873) (.n 1429) (.n 5872)),
    .atom (.add (.n 5874) (.n 5870) (.n 5873))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5447, a5448, a5449, a5450, -⟩ := hs1
  have e5447 := tb_loadHolds_unique a5447 (hw 2 (by norm_num))
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4666 : σ (.n 4666) = ev 87 := by
    rw [← hev 87 (by norm_num)]; exact (vt_evalF h (k := 148) (by norm_num)).2.2
  have hB : σ (.n 5872) = vtSlots W ev 0 [[], [], [([13, 87], 3)], [], []] := by
    simp only [v4666, v4123, a5448, e5447, a4809, a4808, a4807, a4806]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5450, a5449, hB]

set_option maxRecDepth 10000 in
theorem vtD5_25F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5878) = σ (.n 5874) + σ (.n 1431) * vtSlots W ev 0
      [[], [], [([13, 88], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4810 [
    .atom (.const (.n 5234) (word 3 0)),
    .atom (.mul (.n 5235) (.n 4123) (.n 4670)),
    .atom (.mul (.n 5236) (.n 5234) (.n 5235)),
    .atom (.copy (.n 5237) (.n 5236))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4810, a4811, a4812, a4813, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5451 [
    .atom (.load (.n 5875) (.n 13) 2),
    .atom (.mul (.n 5876) (.n 5875) (.n 5237)),
    .atom (.mul (.n 5877) (.n 1431) (.n 5876)),
    .atom (.add (.n 5878) (.n 5874) (.n 5877))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5451, a5452, a5453, a5454, -⟩ := hs1
  have e5451 := tb_loadHolds_unique a5451 (hw 2 (by norm_num))
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4670 : σ (.n 4670) = ev 88 := by
    rw [← hev 88 (by norm_num)]; exact (vt_evalF h (k := 149) (by norm_num)).2.2
  have hB : σ (.n 5876) = vtSlots W ev 0 [[], [], [([13, 88], 3)], [], []] := by
    simp only [v4670, v4123, a5452, e5451, a4813, a4812, a4811, a4810]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5454, a5453, hB]

set_option maxRecDepth 10000 in
theorem vtD5_26F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5882) = σ (.n 5878) + σ (.n 1433) * vtSlots W ev 0
      [[], [], [([13, 89], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4814 [
    .atom (.const (.n 5238) (word 3 0)),
    .atom (.mul (.n 5239) (.n 4123) (.n 4674)),
    .atom (.mul (.n 5240) (.n 5238) (.n 5239)),
    .atom (.copy (.n 5241) (.n 5240))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4814, a4815, a4816, a4817, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5455 [
    .atom (.load (.n 5879) (.n 13) 2),
    .atom (.mul (.n 5880) (.n 5879) (.n 5241)),
    .atom (.mul (.n 5881) (.n 1433) (.n 5880)),
    .atom (.add (.n 5882) (.n 5878) (.n 5881))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5455, a5456, a5457, a5458, -⟩ := hs1
  have e5455 := tb_loadHolds_unique a5455 (hw 2 (by norm_num))
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4674 : σ (.n 4674) = ev 89 := by
    rw [← hev 89 (by norm_num)]; exact (vt_evalF h (k := 150) (by norm_num)).2.2
  have hB : σ (.n 5880) = vtSlots W ev 0 [[], [], [([13, 89], 3)], [], []] := by
    simp only [v4674, v4123, a5456, e5455, a4817, a4816, a4815, a4814]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5458, a5457, hB]

set_option maxRecDepth 10000 in
theorem vtD5_27F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5886) = σ (.n 5882) + σ (.n 1435) * vtSlots W ev 0
      [[], [], [([13, 90], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4818 [
    .atom (.const (.n 5242) (word 3 0)),
    .atom (.mul (.n 5243) (.n 4123) (.n 4678)),
    .atom (.mul (.n 5244) (.n 5242) (.n 5243)),
    .atom (.copy (.n 5245) (.n 5244))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4818, a4819, a4820, a4821, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5459 [
    .atom (.load (.n 5883) (.n 13) 2),
    .atom (.mul (.n 5884) (.n 5883) (.n 5245)),
    .atom (.mul (.n 5885) (.n 1435) (.n 5884)),
    .atom (.add (.n 5886) (.n 5882) (.n 5885))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5459, a5460, a5461, a5462, -⟩ := hs1
  have e5459 := tb_loadHolds_unique a5459 (hw 2 (by norm_num))
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4678 : σ (.n 4678) = ev 90 := by
    rw [← hev 90 (by norm_num)]; exact (vt_evalF h (k := 151) (by norm_num)).2.2
  have hB : σ (.n 5884) = vtSlots W ev 0 [[], [], [([13, 90], 3)], [], []] := by
    simp only [v4678, v4123, a5460, e5459, a4821, a4820, a4819, a4818]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5462, a5461, hB]

end
end LeanVM.Guest.B1.Tables
