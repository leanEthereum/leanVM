/-
  LeanVM.Guest.B1.Tables.Vt.FormsT5b

  Table 5's blocks' values on the pull side, from the guest's statements.

  Do not edit: `scripts/b1c-vt/all.py` writes it (`regen-guest.sh`, step `vt`).
-/

module

public import LeanVM.Guest.B1.Tables.Vt.FormsDiff
public import LeanVM.Guest.B1.Tables.Vt.PullSels
public import LeanVM.Guest.B1.Tables.Vt.Pi

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
theorem vtD5_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5773) = σ (.n 1380) * vtSlots W ev 0
      [[], [([0], 3)], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4721 [
    .atom (.const (.n 5145) (word 3 0)),
    .atom (.mul (.n 5146) (.n 5145) (.n 4027)),
    .atom (.copy (.n 5147) (.n 5146))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4721, a4722, a4723, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5347 [
    .atom (.load (.n 5771) (.n 13) 1),
    .atom (.mul (.n 5772) (.n 5771) (.n 5147)),
    .atom (.mul (.n 5773) (.n 1380) (.n 5772))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5347, a5348, a5349, -⟩ := hs1
  have e5347 := tb_loadHolds_unique a5347 (hw 1 (by norm_num))
  have v4027 : σ (.n 4027) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 61) (by norm_num)).2.2
  have hB : σ (.n 5772) = vtSlots W ev 0 [[], [([0], 3)], []] := by
    simp only [v4027, a5348, e5347, a4723, a4722, a4721]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5349, hB]

set_option maxRecDepth 10000 in
theorem vtD5_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5777) = σ (.n 5773) + σ (.n 1382) * vtSlots W ev 0
      [[], [], [([91], 3)], [], [], [], [], [], [], [], [], [], [], [], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4724 [
    .atom (.const (.n 5148) (word 3 0)),
    .atom (.mul (.n 5149) (.n 5148) (.n 4690)),
    .atom (.copy (.n 5150) (.n 5149))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4724, a4725, a4726, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5350 [
    .atom (.load (.n 5774) (.n 13) 2),
    .atom (.mul (.n 5775) (.n 5774) (.n 5150)),
    .atom (.mul (.n 5776) (.n 1382) (.n 5775)),
    .atom (.add (.n 5777) (.n 5773) (.n 5776))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5350, a5351, a5352, a5353, -⟩ := hs1
  have e5350 := tb_loadHolds_unique a5350 (hw 2 (by norm_num))
  have v4690 : σ (.n 4690) = ev 91 := by
    rw [← hev 91 (by norm_num)]; exact (vt_eval h (k := 152) (by norm_num)).2.2
  have hB : σ (.n 5775) = vtSlots W ev 0 [[], [], [([91], 3)], [], [], [], [], [], [], [], [], [], [], [], [], []] := by
    simp only [v4690, a5351, e5350, a4726, a4725, a4724]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5353, a5352, hB]

set_option maxRecDepth 10000 in
theorem vtD5_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5781) = σ (.n 5777) + σ (.n 1384) * vtSlots W ev 0
      [[], [], [([65], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4727 [
    .atom (.const (.n 5151) (word 3 0)),
    .atom (.mul (.n 5152) (.n 5151) (.n 4495)),
    .atom (.copy (.n 5153) (.n 5152))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4727, a4728, a4729, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5354 [
    .atom (.load (.n 5778) (.n 13) 2),
    .atom (.mul (.n 5779) (.n 5778) (.n 5153)),
    .atom (.mul (.n 5780) (.n 1384) (.n 5779)),
    .atom (.add (.n 5781) (.n 5777) (.n 5780))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5354, a5355, a5356, a5357, -⟩ := hs1
  have e5354 := tb_loadHolds_unique a5354 (hw 2 (by norm_num))
  have v4495 : σ (.n 4495) = ev 65 := by
    rw [← hev 65 (by norm_num)]; exact (vt_eval h (k := 126) (by norm_num)).2.2
  have hB : σ (.n 5779) = vtSlots W ev 0 [[], [], [([65], 3)], [], []] := by
    simp only [v4495, a5355, e5354, a4729, a4728, a4727]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5357, a5356, hB]

set_option maxRecDepth 10000 in
theorem vtD5_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5785) = σ (.n 5781) + σ (.n 1386) * vtSlots W ev 0
      [[], [], [([66], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4730 [
    .atom (.const (.n 5154) (word 3 0)),
    .atom (.mul (.n 5155) (.n 5154) (.n 4499)),
    .atom (.copy (.n 5156) (.n 5155))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4730, a4731, a4732, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5358 [
    .atom (.load (.n 5782) (.n 13) 2),
    .atom (.mul (.n 5783) (.n 5782) (.n 5156)),
    .atom (.mul (.n 5784) (.n 1386) (.n 5783)),
    .atom (.add (.n 5785) (.n 5781) (.n 5784))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5358, a5359, a5360, a5361, -⟩ := hs1
  have e5358 := tb_loadHolds_unique a5358 (hw 2 (by norm_num))
  have v4499 : σ (.n 4499) = ev 66 := by
    rw [← hev 66 (by norm_num)]; exact (vt_eval h (k := 127) (by norm_num)).2.2
  have hB : σ (.n 5783) = vtSlots W ev 0 [[], [], [([66], 3)], [], []] := by
    simp only [v4499, a5359, e5358, a4732, a4731, a4730]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5361, a5360, hB]

set_option maxRecDepth 10000 in
theorem vtD5_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5789) = σ (.n 5785) + σ (.n 1388) * vtSlots W ev 0
      [[], [], [([67], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4733 [
    .atom (.const (.n 5157) (word 3 0)),
    .atom (.mul (.n 5158) (.n 5157) (.n 4516)),
    .atom (.copy (.n 5159) (.n 5158))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4733, a4734, a4735, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5362 [
    .atom (.load (.n 5786) (.n 13) 2),
    .atom (.mul (.n 5787) (.n 5786) (.n 5159)),
    .atom (.mul (.n 5788) (.n 1388) (.n 5787)),
    .atom (.add (.n 5789) (.n 5785) (.n 5788))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5362, a5363, a5364, a5365, -⟩ := hs1
  have e5362 := tb_loadHolds_unique a5362 (hw 2 (by norm_num))
  have v4516 : σ (.n 4516) = ev 67 := by
    rw [← hev 67 (by norm_num)]; exact (vt_eval h (k := 128) (by norm_num)).2.2
  have hB : σ (.n 5787) = vtSlots W ev 0 [[], [], [([67], 3)], [], []] := by
    simp only [v4516, a5363, e5362, a4735, a4734, a4733]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5365, a5364, hB]

set_option maxRecDepth 10000 in
theorem vtD5_5 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5793) = σ (.n 5789) + σ (.n 1390) * vtSlots W ev 0
      [[], [], [([68], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4736 [
    .atom (.const (.n 5160) (word 3 0)),
    .atom (.mul (.n 5161) (.n 5160) (.n 4520)),
    .atom (.copy (.n 5162) (.n 5161))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4736, a4737, a4738, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5366 [
    .atom (.load (.n 5790) (.n 13) 2),
    .atom (.mul (.n 5791) (.n 5790) (.n 5162)),
    .atom (.mul (.n 5792) (.n 1390) (.n 5791)),
    .atom (.add (.n 5793) (.n 5789) (.n 5792))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5366, a5367, a5368, a5369, -⟩ := hs1
  have e5366 := tb_loadHolds_unique a5366 (hw 2 (by norm_num))
  have v4520 : σ (.n 4520) = ev 68 := by
    rw [← hev 68 (by norm_num)]; exact (vt_eval h (k := 129) (by norm_num)).2.2
  have hB : σ (.n 5791) = vtSlots W ev 0 [[], [], [([68], 3)], [], []] := by
    simp only [v4520, a5367, e5366, a4738, a4737, a4736]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5369, a5368, hB]

set_option maxRecDepth 10000 in
theorem vtD5_6 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5797) = σ (.n 5793) + σ (.n 1392) * vtSlots W ev 0
      [[], [], [([69], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4739 [
    .atom (.const (.n 5163) (word 3 0)),
    .atom (.mul (.n 5164) (.n 5163) (.n 4524)),
    .atom (.copy (.n 5165) (.n 5164))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4739, a4740, a4741, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5370 [
    .atom (.load (.n 5794) (.n 13) 2),
    .atom (.mul (.n 5795) (.n 5794) (.n 5165)),
    .atom (.mul (.n 5796) (.n 1392) (.n 5795)),
    .atom (.add (.n 5797) (.n 5793) (.n 5796))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5370, a5371, a5372, a5373, -⟩ := hs1
  have e5370 := tb_loadHolds_unique a5370 (hw 2 (by norm_num))
  have v4524 : σ (.n 4524) = ev 69 := by
    rw [← hev 69 (by norm_num)]; exact (vt_eval h (k := 130) (by norm_num)).2.2
  have hB : σ (.n 5795) = vtSlots W ev 0 [[], [], [([69], 3)], [], []] := by
    simp only [v4524, a5371, e5370, a4741, a4740, a4739]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5373, a5372, hB]

set_option maxRecDepth 10000 in
theorem vtD5_7 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5801) = σ (.n 5797) + σ (.n 1394) * vtSlots W ev 0
      [[], [], [([70], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4742 [
    .atom (.const (.n 5166) (word 3 0)),
    .atom (.mul (.n 5167) (.n 5166) (.n 4528)),
    .atom (.copy (.n 5168) (.n 5167))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4742, a4743, a4744, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5374 [
    .atom (.load (.n 5798) (.n 13) 2),
    .atom (.mul (.n 5799) (.n 5798) (.n 5168)),
    .atom (.mul (.n 5800) (.n 1394) (.n 5799)),
    .atom (.add (.n 5801) (.n 5797) (.n 5800))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5374, a5375, a5376, a5377, -⟩ := hs1
  have e5374 := tb_loadHolds_unique a5374 (hw 2 (by norm_num))
  have v4528 : σ (.n 4528) = ev 70 := by
    rw [← hev 70 (by norm_num)]; exact (vt_eval h (k := 131) (by norm_num)).2.2
  have hB : σ (.n 5799) = vtSlots W ev 0 [[], [], [([70], 3)], [], []] := by
    simp only [v4528, a5375, e5374, a4744, a4743, a4742]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5377, a5376, hB]

set_option maxRecDepth 10000 in
theorem vtD5_8 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5805) = σ (.n 5801) + σ (.n 1396) * vtSlots W ev 0
      [[], [], [([71], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4745 [
    .atom (.const (.n 5169) (word 3 0)),
    .atom (.mul (.n 5170) (.n 5169) (.n 4545)),
    .atom (.copy (.n 5171) (.n 5170))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4745, a4746, a4747, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5378 [
    .atom (.load (.n 5802) (.n 13) 2),
    .atom (.mul (.n 5803) (.n 5802) (.n 5171)),
    .atom (.mul (.n 5804) (.n 1396) (.n 5803)),
    .atom (.add (.n 5805) (.n 5801) (.n 5804))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5378, a5379, a5380, a5381, -⟩ := hs1
  have e5378 := tb_loadHolds_unique a5378 (hw 2 (by norm_num))
  have v4545 : σ (.n 4545) = ev 71 := by
    rw [← hev 71 (by norm_num)]; exact (vt_eval h (k := 132) (by norm_num)).2.2
  have hB : σ (.n 5803) = vtSlots W ev 0 [[], [], [([71], 3)], [], []] := by
    simp only [v4545, a5379, e5378, a4747, a4746, a4745]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5381, a5380, hB]

set_option maxRecDepth 10000 in
theorem vtD5_9 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5809) = σ (.n 5805) + σ (.n 1398) * vtSlots W ev 0
      [[], [], [([72], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4748 [
    .atom (.const (.n 5172) (word 3 0)),
    .atom (.mul (.n 5173) (.n 5172) (.n 4549)),
    .atom (.copy (.n 5174) (.n 5173))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4748, a4749, a4750, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5382 [
    .atom (.load (.n 5806) (.n 13) 2),
    .atom (.mul (.n 5807) (.n 5806) (.n 5174)),
    .atom (.mul (.n 5808) (.n 1398) (.n 5807)),
    .atom (.add (.n 5809) (.n 5805) (.n 5808))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5382, a5383, a5384, a5385, -⟩ := hs1
  have e5382 := tb_loadHolds_unique a5382 (hw 2 (by norm_num))
  have v4549 : σ (.n 4549) = ev 72 := by
    rw [← hev 72 (by norm_num)]; exact (vt_eval h (k := 133) (by norm_num)).2.2
  have hB : σ (.n 5807) = vtSlots W ev 0 [[], [], [([72], 3)], [], []] := by
    simp only [v4549, a5383, e5382, a4750, a4749, a4748]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5385, a5384, hB]

set_option maxRecDepth 10000 in
theorem vtD5_10 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5813) = σ (.n 5809) + σ (.n 1400) * vtSlots W ev 0
      [[], [], [([73], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4751 [
    .atom (.const (.n 5175) (word 3 0)),
    .atom (.mul (.n 5176) (.n 5175) (.n 4553)),
    .atom (.copy (.n 5177) (.n 5176))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4751, a4752, a4753, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5386 [
    .atom (.load (.n 5810) (.n 13) 2),
    .atom (.mul (.n 5811) (.n 5810) (.n 5177)),
    .atom (.mul (.n 5812) (.n 1400) (.n 5811)),
    .atom (.add (.n 5813) (.n 5809) (.n 5812))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5386, a5387, a5388, a5389, -⟩ := hs1
  have e5386 := tb_loadHolds_unique a5386 (hw 2 (by norm_num))
  have v4553 : σ (.n 4553) = ev 73 := by
    rw [← hev 73 (by norm_num)]; exact (vt_eval h (k := 134) (by norm_num)).2.2
  have hB : σ (.n 5811) = vtSlots W ev 0 [[], [], [([73], 3)], [], []] := by
    simp only [v4553, a5387, e5386, a4753, a4752, a4751]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5389, a5388, hB]

set_option maxRecDepth 10000 in
theorem vtD5_11 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5817) = σ (.n 5813) + σ (.n 1402) * vtSlots W ev 0
      [[], [], [([74], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4754 [
    .atom (.const (.n 5178) (word 3 0)),
    .atom (.mul (.n 5179) (.n 5178) (.n 4557)),
    .atom (.copy (.n 5180) (.n 5179))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4754, a4755, a4756, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5390 [
    .atom (.load (.n 5814) (.n 13) 2),
    .atom (.mul (.n 5815) (.n 5814) (.n 5180)),
    .atom (.mul (.n 5816) (.n 1402) (.n 5815)),
    .atom (.add (.n 5817) (.n 5813) (.n 5816))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5390, a5391, a5392, a5393, -⟩ := hs1
  have e5390 := tb_loadHolds_unique a5390 (hw 2 (by norm_num))
  have v4557 : σ (.n 4557) = ev 74 := by
    rw [← hev 74 (by norm_num)]; exact (vt_eval h (k := 135) (by norm_num)).2.2
  have hB : σ (.n 5815) = vtSlots W ev 0 [[], [], [([74], 3)], [], []] := by
    simp only [v4557, a5391, e5390, a4756, a4755, a4754]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5393, a5392, hB]

set_option maxRecDepth 10000 in
theorem vtD5_12 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5821) = σ (.n 5817) + σ (.n 1404) * vtSlots W ev 0
      [[], [], [([75], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4757 [
    .atom (.const (.n 5181) (word 3 0)),
    .atom (.mul (.n 5182) (.n 5181) (.n 4574)),
    .atom (.copy (.n 5183) (.n 5182))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4757, a4758, a4759, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5394 [
    .atom (.load (.n 5818) (.n 13) 2),
    .atom (.mul (.n 5819) (.n 5818) (.n 5183)),
    .atom (.mul (.n 5820) (.n 1404) (.n 5819)),
    .atom (.add (.n 5821) (.n 5817) (.n 5820))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5394, a5395, a5396, a5397, -⟩ := hs1
  have e5394 := tb_loadHolds_unique a5394 (hw 2 (by norm_num))
  have v4574 : σ (.n 4574) = ev 75 := by
    rw [← hev 75 (by norm_num)]; exact (vt_eval h (k := 136) (by norm_num)).2.2
  have hB : σ (.n 5819) = vtSlots W ev 0 [[], [], [([75], 3)], [], []] := by
    simp only [v4574, a5395, e5394, a4759, a4758, a4757]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5397, a5396, hB]

set_option maxRecDepth 10000 in
theorem vtD5_13 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5825) = σ (.n 5821) + σ (.n 1406) * vtSlots W ev 0
      [[], [], [([76], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4760 [
    .atom (.const (.n 5184) (word 3 0)),
    .atom (.mul (.n 5185) (.n 5184) (.n 4578)),
    .atom (.copy (.n 5186) (.n 5185))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4760, a4761, a4762, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5398 [
    .atom (.load (.n 5822) (.n 13) 2),
    .atom (.mul (.n 5823) (.n 5822) (.n 5186)),
    .atom (.mul (.n 5824) (.n 1406) (.n 5823)),
    .atom (.add (.n 5825) (.n 5821) (.n 5824))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5398, a5399, a5400, a5401, -⟩ := hs1
  have e5398 := tb_loadHolds_unique a5398 (hw 2 (by norm_num))
  have v4578 : σ (.n 4578) = ev 76 := by
    rw [← hev 76 (by norm_num)]; exact (vt_eval h (k := 137) (by norm_num)).2.2
  have hB : σ (.n 5823) = vtSlots W ev 0 [[], [], [([76], 3)], [], []] := by
    simp only [v4578, a5399, e5398, a4762, a4761, a4760]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5401, a5400, hB]

set_option maxRecDepth 10000 in
theorem vtD5_14 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5829) = σ (.n 5825) + σ (.n 1408) * vtSlots W ev 0
      [[], [], [([77], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4763 [
    .atom (.const (.n 5187) (word 3 0)),
    .atom (.mul (.n 5188) (.n 5187) (.n 4582)),
    .atom (.copy (.n 5189) (.n 5188))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4763, a4764, a4765, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5402 [
    .atom (.load (.n 5826) (.n 13) 2),
    .atom (.mul (.n 5827) (.n 5826) (.n 5189)),
    .atom (.mul (.n 5828) (.n 1408) (.n 5827)),
    .atom (.add (.n 5829) (.n 5825) (.n 5828))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5402, a5403, a5404, a5405, -⟩ := hs1
  have e5402 := tb_loadHolds_unique a5402 (hw 2 (by norm_num))
  have v4582 : σ (.n 4582) = ev 77 := by
    rw [← hev 77 (by norm_num)]; exact (vt_eval h (k := 138) (by norm_num)).2.2
  have hB : σ (.n 5827) = vtSlots W ev 0 [[], [], [([77], 3)], [], []] := by
    simp only [v4582, a5403, e5402, a4765, a4764, a4763]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5405, a5404, hB]

set_option maxRecDepth 10000 in
theorem vtD5_15 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5833) = σ (.n 5829) + σ (.n 1410) * vtSlots W ev 0
      [[], [], [([78], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4766 [
    .atom (.const (.n 5190) (word 3 0)),
    .atom (.mul (.n 5191) (.n 5190) (.n 4586)),
    .atom (.copy (.n 5192) (.n 5191))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4766, a4767, a4768, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5406 [
    .atom (.load (.n 5830) (.n 13) 2),
    .atom (.mul (.n 5831) (.n 5830) (.n 5192)),
    .atom (.mul (.n 5832) (.n 1410) (.n 5831)),
    .atom (.add (.n 5833) (.n 5829) (.n 5832))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5406, a5407, a5408, a5409, -⟩ := hs1
  have e5406 := tb_loadHolds_unique a5406 (hw 2 (by norm_num))
  have v4586 : σ (.n 4586) = ev 78 := by
    rw [← hev 78 (by norm_num)]; exact (vt_eval h (k := 139) (by norm_num)).2.2
  have hB : σ (.n 5831) = vtSlots W ev 0 [[], [], [([78], 3)], [], []] := by
    simp only [v4586, a5407, e5406, a4768, a4767, a4766]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5409, a5408, hB]

set_option maxRecDepth 10000 in
theorem vtD5_16 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5837) = σ (.n 5833) + σ (.n 1412) * vtSlots W ev 0
      [[], [], [([12, 79], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4769 [
    .atom (.const (.n 5193) (word 3 0)),
    .atom (.mul (.n 5194) (.n 4114) (.n 4603)),
    .atom (.mul (.n 5195) (.n 5193) (.n 5194)),
    .atom (.copy (.n 5196) (.n 5195))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4769, a4770, a4771, a4772, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5410 [
    .atom (.load (.n 5834) (.n 13) 2),
    .atom (.mul (.n 5835) (.n 5834) (.n 5196)),
    .atom (.mul (.n 5836) (.n 1412) (.n 5835)),
    .atom (.add (.n 5837) (.n 5833) (.n 5836))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5410, a5411, a5412, a5413, -⟩ := hs1
  have e5410 := tb_loadHolds_unique a5410 (hw 2 (by norm_num))
  have v4114 : σ (.n 4114) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 73) (by norm_num)).2.2
  have v4603 : σ (.n 4603) = ev 79 := by
    rw [← hev 79 (by norm_num)]; exact (vt_eval h (k := 140) (by norm_num)).2.2
  have hB : σ (.n 5835) = vtSlots W ev 0 [[], [], [([12, 79], 3)], [], []] := by
    simp only [v4603, v4114, a5411, e5410, a4772, a4771, a4770, a4769]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5413, a5412, hB]

set_option maxRecDepth 10000 in
theorem vtD5_17 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5841) = σ (.n 5837) + σ (.n 1414) * vtSlots W ev 0
      [[], [], [([13, 80], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4773 [
    .atom (.const (.n 5197) (word 3 0)),
    .atom (.mul (.n 5198) (.n 4118) (.n 4607)),
    .atom (.mul (.n 5199) (.n 5197) (.n 5198)),
    .atom (.copy (.n 5200) (.n 5199))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4773, a4774, a4775, a4776, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5414 [
    .atom (.load (.n 5838) (.n 13) 2),
    .atom (.mul (.n 5839) (.n 5838) (.n 5200)),
    .atom (.mul (.n 5840) (.n 1414) (.n 5839)),
    .atom (.add (.n 5841) (.n 5837) (.n 5840))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5414, a5415, a5416, a5417, -⟩ := hs1
  have e5414 := tb_loadHolds_unique a5414 (hw 2 (by norm_num))
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4607 : σ (.n 4607) = ev 80 := by
    rw [← hev 80 (by norm_num)]; exact (vt_eval h (k := 141) (by norm_num)).2.2
  have hB : σ (.n 5839) = vtSlots W ev 0 [[], [], [([13, 80], 3)], [], []] := by
    simp only [v4607, v4118, a5415, e5414, a4776, a4775, a4774, a4773]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5417, a5416, hB]

set_option maxRecDepth 10000 in
theorem vtD5_18 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5845) = σ (.n 5841) + σ (.n 1416) * vtSlots W ev 0
      [[], [], [([13, 81], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4777 [
    .atom (.const (.n 5201) (word 3 0)),
    .atom (.mul (.n 5202) (.n 4118) (.n 4611)),
    .atom (.mul (.n 5203) (.n 5201) (.n 5202)),
    .atom (.copy (.n 5204) (.n 5203))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4777, a4778, a4779, a4780, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5418 [
    .atom (.load (.n 5842) (.n 13) 2),
    .atom (.mul (.n 5843) (.n 5842) (.n 5204)),
    .atom (.mul (.n 5844) (.n 1416) (.n 5843)),
    .atom (.add (.n 5845) (.n 5841) (.n 5844))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5418, a5419, a5420, a5421, -⟩ := hs1
  have e5418 := tb_loadHolds_unique a5418 (hw 2 (by norm_num))
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4611 : σ (.n 4611) = ev 81 := by
    rw [← hev 81 (by norm_num)]; exact (vt_eval h (k := 142) (by norm_num)).2.2
  have hB : σ (.n 5843) = vtSlots W ev 0 [[], [], [([13, 81], 3)], [], []] := by
    simp only [v4611, v4118, a5419, e5418, a4780, a4779, a4778, a4777]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5421, a5420, hB]

set_option maxRecDepth 10000 in
theorem vtD5_19 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5849) = σ (.n 5845) + σ (.n 1418) * vtSlots W ev 0
      [[], [], [([13, 82], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4781 [
    .atom (.const (.n 5205) (word 3 0)),
    .atom (.mul (.n 5206) (.n 4118) (.n 4615)),
    .atom (.mul (.n 5207) (.n 5205) (.n 5206)),
    .atom (.copy (.n 5208) (.n 5207))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4781, a4782, a4783, a4784, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5422 [
    .atom (.load (.n 5846) (.n 13) 2),
    .atom (.mul (.n 5847) (.n 5846) (.n 5208)),
    .atom (.mul (.n 5848) (.n 1418) (.n 5847)),
    .atom (.add (.n 5849) (.n 5845) (.n 5848))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5422, a5423, a5424, a5425, -⟩ := hs1
  have e5422 := tb_loadHolds_unique a5422 (hw 2 (by norm_num))
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4615 : σ (.n 4615) = ev 82 := by
    rw [← hev 82 (by norm_num)]; exact (vt_eval h (k := 143) (by norm_num)).2.2
  have hB : σ (.n 5847) = vtSlots W ev 0 [[], [], [([13, 82], 3)], [], []] := by
    simp only [v4615, v4118, a5423, e5422, a4784, a4783, a4782, a4781]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5425, a5424, hB]

set_option maxRecDepth 10000 in
theorem vtD5_20 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5853) = σ (.n 5849) + σ (.n 1420) * vtSlots W ev 0
      [[], [], [([13, 83], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4785 [
    .atom (.const (.n 5209) (word 3 0)),
    .atom (.mul (.n 5210) (.n 4118) (.n 4632)),
    .atom (.mul (.n 5211) (.n 5209) (.n 5210)),
    .atom (.copy (.n 5212) (.n 5211))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4785, a4786, a4787, a4788, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5426 [
    .atom (.load (.n 5850) (.n 13) 2),
    .atom (.mul (.n 5851) (.n 5850) (.n 5212)),
    .atom (.mul (.n 5852) (.n 1420) (.n 5851)),
    .atom (.add (.n 5853) (.n 5849) (.n 5852))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5426, a5427, a5428, a5429, -⟩ := hs1
  have e5426 := tb_loadHolds_unique a5426 (hw 2 (by norm_num))
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4632 : σ (.n 4632) = ev 83 := by
    rw [← hev 83 (by norm_num)]; exact (vt_eval h (k := 144) (by norm_num)).2.2
  have hB : σ (.n 5851) = vtSlots W ev 0 [[], [], [([13, 83], 3)], [], []] := by
    simp only [v4632, v4118, a5427, e5426, a4788, a4787, a4786, a4785]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5429, a5428, hB]

set_option maxRecDepth 10000 in
theorem vtD5_21 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5857) = σ (.n 5853) + σ (.n 1422) * vtSlots W ev 0
      [[], [], [([13, 84], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4789 [
    .atom (.const (.n 5213) (word 3 0)),
    .atom (.mul (.n 5214) (.n 4118) (.n 4636)),
    .atom (.mul (.n 5215) (.n 5213) (.n 5214)),
    .atom (.copy (.n 5216) (.n 5215))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4789, a4790, a4791, a4792, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5430 [
    .atom (.load (.n 5854) (.n 13) 2),
    .atom (.mul (.n 5855) (.n 5854) (.n 5216)),
    .atom (.mul (.n 5856) (.n 1422) (.n 5855)),
    .atom (.add (.n 5857) (.n 5853) (.n 5856))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5430, a5431, a5432, a5433, -⟩ := hs1
  have e5430 := tb_loadHolds_unique a5430 (hw 2 (by norm_num))
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4636 : σ (.n 4636) = ev 84 := by
    rw [← hev 84 (by norm_num)]; exact (vt_eval h (k := 145) (by norm_num)).2.2
  have hB : σ (.n 5855) = vtSlots W ev 0 [[], [], [([13, 84], 3)], [], []] := by
    simp only [v4636, v4118, a5431, e5430, a4792, a4791, a4790, a4789]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5433, a5432, hB]

set_option maxRecDepth 10000 in
theorem vtD5_22 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5861) = σ (.n 5857) + σ (.n 1424) * vtSlots W ev 0
      [[], [], [([13, 85], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4793 [
    .atom (.const (.n 5217) (word 3 0)),
    .atom (.mul (.n 5218) (.n 4118) (.n 4640)),
    .atom (.mul (.n 5219) (.n 5217) (.n 5218)),
    .atom (.copy (.n 5220) (.n 5219))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4793, a4794, a4795, a4796, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5434 [
    .atom (.load (.n 5858) (.n 13) 2),
    .atom (.mul (.n 5859) (.n 5858) (.n 5220)),
    .atom (.mul (.n 5860) (.n 1424) (.n 5859)),
    .atom (.add (.n 5861) (.n 5857) (.n 5860))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5434, a5435, a5436, a5437, -⟩ := hs1
  have e5434 := tb_loadHolds_unique a5434 (hw 2 (by norm_num))
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4640 : σ (.n 4640) = ev 85 := by
    rw [← hev 85 (by norm_num)]; exact (vt_eval h (k := 146) (by norm_num)).2.2
  have hB : σ (.n 5859) = vtSlots W ev 0 [[], [], [([13, 85], 3)], [], []] := by
    simp only [v4640, v4118, a5435, e5434, a4796, a4795, a4794, a4793]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5437, a5436, hB]

set_option maxRecDepth 10000 in
theorem vtD5_23 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5865) = σ (.n 5861) + σ (.n 1426) * vtSlots W ev 0
      [[], [], [([13, 86], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4797 [
    .atom (.const (.n 5221) (word 3 0)),
    .atom (.mul (.n 5222) (.n 4118) (.n 4644)),
    .atom (.mul (.n 5223) (.n 5221) (.n 5222)),
    .atom (.copy (.n 5224) (.n 5223))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4797, a4798, a4799, a4800, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5438 [
    .atom (.load (.n 5862) (.n 13) 2),
    .atom (.mul (.n 5863) (.n 5862) (.n 5224)),
    .atom (.mul (.n 5864) (.n 1426) (.n 5863)),
    .atom (.add (.n 5865) (.n 5861) (.n 5864))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5438, a5439, a5440, a5441, -⟩ := hs1
  have e5438 := tb_loadHolds_unique a5438 (hw 2 (by norm_num))
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4644 : σ (.n 4644) = ev 86 := by
    rw [← hev 86 (by norm_num)]; exact (vt_eval h (k := 147) (by norm_num)).2.2
  have hB : σ (.n 5863) = vtSlots W ev 0 [[], [], [([13, 86], 3)], [], []] := by
    simp only [v4644, v4118, a5439, e5438, a4800, a4799, a4798, a4797]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5441, a5440, hB]

set_option maxRecDepth 10000 in
theorem vtD5_24 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5869) = σ (.n 5865) + σ (.n 1428) * vtSlots W ev 0
      [[], [], [([13, 87], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4801 [
    .atom (.const (.n 5225) (word 3 0)),
    .atom (.mul (.n 5226) (.n 4118) (.n 4661)),
    .atom (.mul (.n 5227) (.n 5225) (.n 5226)),
    .atom (.copy (.n 5228) (.n 5227))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4801, a4802, a4803, a4804, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5442 [
    .atom (.load (.n 5866) (.n 13) 2),
    .atom (.mul (.n 5867) (.n 5866) (.n 5228)),
    .atom (.mul (.n 5868) (.n 1428) (.n 5867)),
    .atom (.add (.n 5869) (.n 5865) (.n 5868))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5442, a5443, a5444, a5445, -⟩ := hs1
  have e5442 := tb_loadHolds_unique a5442 (hw 2 (by norm_num))
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4661 : σ (.n 4661) = ev 87 := by
    rw [← hev 87 (by norm_num)]; exact (vt_eval h (k := 148) (by norm_num)).2.2
  have hB : σ (.n 5867) = vtSlots W ev 0 [[], [], [([13, 87], 3)], [], []] := by
    simp only [v4661, v4118, a5443, e5442, a4804, a4803, a4802, a4801]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5445, a5444, hB]

set_option maxRecDepth 10000 in
theorem vtD5_25 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5873) = σ (.n 5869) + σ (.n 1430) * vtSlots W ev 0
      [[], [], [([13, 88], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4805 [
    .atom (.const (.n 5229) (word 3 0)),
    .atom (.mul (.n 5230) (.n 4118) (.n 4665)),
    .atom (.mul (.n 5231) (.n 5229) (.n 5230)),
    .atom (.copy (.n 5232) (.n 5231))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4805, a4806, a4807, a4808, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5446 [
    .atom (.load (.n 5870) (.n 13) 2),
    .atom (.mul (.n 5871) (.n 5870) (.n 5232)),
    .atom (.mul (.n 5872) (.n 1430) (.n 5871)),
    .atom (.add (.n 5873) (.n 5869) (.n 5872))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5446, a5447, a5448, a5449, -⟩ := hs1
  have e5446 := tb_loadHolds_unique a5446 (hw 2 (by norm_num))
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4665 : σ (.n 4665) = ev 88 := by
    rw [← hev 88 (by norm_num)]; exact (vt_eval h (k := 149) (by norm_num)).2.2
  have hB : σ (.n 5871) = vtSlots W ev 0 [[], [], [([13, 88], 3)], [], []] := by
    simp only [v4665, v4118, a5447, e5446, a4808, a4807, a4806, a4805]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5449, a5448, hB]

set_option maxRecDepth 10000 in
theorem vtD5_26 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5877) = σ (.n 5873) + σ (.n 1432) * vtSlots W ev 0
      [[], [], [([13, 89], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4809 [
    .atom (.const (.n 5233) (word 3 0)),
    .atom (.mul (.n 5234) (.n 4118) (.n 4669)),
    .atom (.mul (.n 5235) (.n 5233) (.n 5234)),
    .atom (.copy (.n 5236) (.n 5235))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4809, a4810, a4811, a4812, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5450 [
    .atom (.load (.n 5874) (.n 13) 2),
    .atom (.mul (.n 5875) (.n 5874) (.n 5236)),
    .atom (.mul (.n 5876) (.n 1432) (.n 5875)),
    .atom (.add (.n 5877) (.n 5873) (.n 5876))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5450, a5451, a5452, a5453, -⟩ := hs1
  have e5450 := tb_loadHolds_unique a5450 (hw 2 (by norm_num))
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4669 : σ (.n 4669) = ev 89 := by
    rw [← hev 89 (by norm_num)]; exact (vt_eval h (k := 150) (by norm_num)).2.2
  have hB : σ (.n 5875) = vtSlots W ev 0 [[], [], [([13, 89], 3)], [], []] := by
    simp only [v4669, v4118, a5451, e5450, a4812, a4811, a4810, a4809]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5453, a5452, hB]

set_option maxRecDepth 10000 in
theorem vtD5_27 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5881) = σ (.n 5877) + σ (.n 1434) * vtSlots W ev 0
      [[], [], [([13, 90], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4813 [
    .atom (.const (.n 5237) (word 3 0)),
    .atom (.mul (.n 5238) (.n 4118) (.n 4673)),
    .atom (.mul (.n 5239) (.n 5237) (.n 5238)),
    .atom (.copy (.n 5240) (.n 5239))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4813, a4814, a4815, a4816, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5454 [
    .atom (.load (.n 5878) (.n 13) 2),
    .atom (.mul (.n 5879) (.n 5878) (.n 5240)),
    .atom (.mul (.n 5880) (.n 1434) (.n 5879)),
    .atom (.add (.n 5881) (.n 5877) (.n 5880))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5454, a5455, a5456, a5457, -⟩ := hs1
  have e5454 := tb_loadHolds_unique a5454 (hw 2 (by norm_num))
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4673 : σ (.n 4673) = ev 90 := by
    rw [← hev 90 (by norm_num)]; exact (vt_eval h (k := 151) (by norm_num)).2.2
  have hB : σ (.n 5879) = vtSlots W ev 0 [[], [], [([13, 90], 3)], [], []] := by
    simp only [v4673, v4118, a5455, e5454, a4816, a4815, a4814, a4813]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a5457, a5456, hB]

end
end LeanVM.Guest.B1.Tables
