/-
  LeanVM.Guest.B1.Tables.Vt.FormsT5b

  Table 5's blocks' values on the pull side, from the guest's statements.
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
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6681) = σ (.n 2014) * vtSlots W ev 0
      [[], [([0], 3)], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6107 [
    .atom (.const (.n 6677) (word 3 0 0)),
    .atom (.mul (.n 6678) (.n 6677) (.n 4437)),
    .atom (.load (.n 6679) (.n 13) 1),
    .atom (.mul (.n 6680) (.n 6679) (.n 6678)),
    .atom (.mul (.n 6681) (.n 2014) (.n 6680))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6107, a6108, a6109, a6110, a6111, -⟩ := hs
  have e6109 := tb_loadHolds_unique a6109 (hw 1 (by norm_num))
  have v4437 : σ (.n 4437) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 67) (by norm_num)).2.2
  have hB : σ (.n 6680) = vtSlots W ev 0 [[], [([0], 3)], []] := by
    simp only [v4437, a6110, e6109, a6108, a6107]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6111, hB]

set_option maxRecDepth 10000 in
theorem vtD5_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6687) = σ (.n 6681) + σ (.n 2016) * vtSlots W ev 0
      [[], [], [([91], 3)], [], [], [], [], [], [], [], [], [], [], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6112 [
    .atom (.const (.n 6682) (word 3 0 0)),
    .atom (.mul (.n 6683) (.n 6682) (.n 5737)),
    .atom (.load (.n 6684) (.n 13) 2),
    .atom (.mul (.n 6685) (.n 6684) (.n 6683)),
    .atom (.mul (.n 6686) (.n 2016) (.n 6685)),
    .atom (.add (.n 6687) (.n 6681) (.n 6686))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6112, a6113, a6114, a6115, a6116, a6117, -⟩ := hs
  have e6114 := tb_loadHolds_unique a6114 (hw 2 (by norm_num))
  have v5737 : σ (.n 5737) = ev 91 := by
    rw [← hev 91 (by norm_num)]; exact (vt_eval h (k := 158) (by norm_num)).2.2
  have hB : σ (.n 6685) = vtSlots W ev 0 [[], [], [([91], 3)], [], [], [], [], [], [], [], [], [], [], [], [], []] := by
    simp only [v5737, a6115, e6114, a6113, a6112]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6117, a6116, hB]

set_option maxRecDepth 10000 in
theorem vtD5_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6693) = σ (.n 6687) + σ (.n 2018) * vtSlots W ev 0
      [[], [], [([65], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6118 [
    .atom (.const (.n 6688) (word 3 0 0)),
    .atom (.mul (.n 6689) (.n 6688) (.n 5373)),
    .atom (.load (.n 6690) (.n 13) 2),
    .atom (.mul (.n 6691) (.n 6690) (.n 6689)),
    .atom (.mul (.n 6692) (.n 2018) (.n 6691)),
    .atom (.add (.n 6693) (.n 6687) (.n 6692))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6118, a6119, a6120, a6121, a6122, a6123, -⟩ := hs
  have e6120 := tb_loadHolds_unique a6120 (hw 2 (by norm_num))
  have v5373 : σ (.n 5373) = ev 65 := by
    rw [← hev 65 (by norm_num)]; exact (vt_eval h (k := 132) (by norm_num)).2.2
  have hB : σ (.n 6691) = vtSlots W ev 0 [[], [], [([65], 3)], [], [], []] := by
    simp only [v5373, a6121, e6120, a6119, a6118]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6123, a6122, hB]

set_option maxRecDepth 10000 in
theorem vtD5_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6699) = σ (.n 6693) + σ (.n 2020) * vtSlots W ev 0
      [[], [], [([66], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6124 [
    .atom (.const (.n 6694) (word 3 0 0)),
    .atom (.mul (.n 6695) (.n 6694) (.n 5384)),
    .atom (.load (.n 6696) (.n 13) 2),
    .atom (.mul (.n 6697) (.n 6696) (.n 6695)),
    .atom (.mul (.n 6698) (.n 2020) (.n 6697)),
    .atom (.add (.n 6699) (.n 6693) (.n 6698))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6124, a6125, a6126, a6127, a6128, a6129, -⟩ := hs
  have e6126 := tb_loadHolds_unique a6126 (hw 2 (by norm_num))
  have v5384 : σ (.n 5384) = ev 66 := by
    rw [← hev 66 (by norm_num)]; exact (vt_eval h (k := 133) (by norm_num)).2.2
  have hB : σ (.n 6697) = vtSlots W ev 0 [[], [], [([66], 3)], [], [], []] := by
    simp only [v5384, a6127, e6126, a6125, a6124]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6129, a6128, hB]

set_option maxRecDepth 10000 in
theorem vtD5_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6705) = σ (.n 6699) + σ (.n 2022) * vtSlots W ev 0
      [[], [], [([67], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6130 [
    .atom (.const (.n 6700) (word 3 0 0)),
    .atom (.mul (.n 6701) (.n 6700) (.n 5395)),
    .atom (.load (.n 6702) (.n 13) 2),
    .atom (.mul (.n 6703) (.n 6702) (.n 6701)),
    .atom (.mul (.n 6704) (.n 2022) (.n 6703)),
    .atom (.add (.n 6705) (.n 6699) (.n 6704))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6130, a6131, a6132, a6133, a6134, a6135, -⟩ := hs
  have e6132 := tb_loadHolds_unique a6132 (hw 2 (by norm_num))
  have v5395 : σ (.n 5395) = ev 67 := by
    rw [← hev 67 (by norm_num)]; exact (vt_eval h (k := 134) (by norm_num)).2.2
  have hB : σ (.n 6703) = vtSlots W ev 0 [[], [], [([67], 3)], [], [], []] := by
    simp only [v5395, a6133, e6132, a6131, a6130]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6135, a6134, hB]

set_option maxRecDepth 10000 in
theorem vtD5_5 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6711) = σ (.n 6705) + σ (.n 2024) * vtSlots W ev 0
      [[], [], [([68], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6136 [
    .atom (.const (.n 6706) (word 3 0 0)),
    .atom (.mul (.n 6707) (.n 6706) (.n 5406)),
    .atom (.load (.n 6708) (.n 13) 2),
    .atom (.mul (.n 6709) (.n 6708) (.n 6707)),
    .atom (.mul (.n 6710) (.n 2024) (.n 6709)),
    .atom (.add (.n 6711) (.n 6705) (.n 6710))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6136, a6137, a6138, a6139, a6140, a6141, -⟩ := hs
  have e6138 := tb_loadHolds_unique a6138 (hw 2 (by norm_num))
  have v5406 : σ (.n 5406) = ev 68 := by
    rw [← hev 68 (by norm_num)]; exact (vt_eval h (k := 135) (by norm_num)).2.2
  have hB : σ (.n 6709) = vtSlots W ev 0 [[], [], [([68], 3)], [], [], []] := by
    simp only [v5406, a6139, e6138, a6137, a6136]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6141, a6140, hB]

set_option maxRecDepth 10000 in
theorem vtD5_6 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6717) = σ (.n 6711) + σ (.n 2026) * vtSlots W ev 0
      [[], [], [([69], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6142 [
    .atom (.const (.n 6712) (word 3 0 0)),
    .atom (.mul (.n 6713) (.n 6712) (.n 5430)),
    .atom (.load (.n 6714) (.n 13) 2),
    .atom (.mul (.n 6715) (.n 6714) (.n 6713)),
    .atom (.mul (.n 6716) (.n 2026) (.n 6715)),
    .atom (.add (.n 6717) (.n 6711) (.n 6716))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6142, a6143, a6144, a6145, a6146, a6147, -⟩ := hs
  have e6144 := tb_loadHolds_unique a6144 (hw 2 (by norm_num))
  have v5430 : σ (.n 5430) = ev 69 := by
    rw [← hev 69 (by norm_num)]; exact (vt_eval h (k := 136) (by norm_num)).2.2
  have hB : σ (.n 6715) = vtSlots W ev 0 [[], [], [([69], 3)], [], [], []] := by
    simp only [v5430, a6145, e6144, a6143, a6142]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6147, a6146, hB]

set_option maxRecDepth 10000 in
theorem vtD5_7 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6723) = σ (.n 6717) + σ (.n 2028) * vtSlots W ev 0
      [[], [], [([70], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6148 [
    .atom (.const (.n 6718) (word 3 0 0)),
    .atom (.mul (.n 6719) (.n 6718) (.n 5441)),
    .atom (.load (.n 6720) (.n 13) 2),
    .atom (.mul (.n 6721) (.n 6720) (.n 6719)),
    .atom (.mul (.n 6722) (.n 2028) (.n 6721)),
    .atom (.add (.n 6723) (.n 6717) (.n 6722))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6148, a6149, a6150, a6151, a6152, a6153, -⟩ := hs
  have e6150 := tb_loadHolds_unique a6150 (hw 2 (by norm_num))
  have v5441 : σ (.n 5441) = ev 70 := by
    rw [← hev 70 (by norm_num)]; exact (vt_eval h (k := 137) (by norm_num)).2.2
  have hB : σ (.n 6721) = vtSlots W ev 0 [[], [], [([70], 3)], [], [], []] := by
    simp only [v5441, a6151, e6150, a6149, a6148]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6153, a6152, hB]

set_option maxRecDepth 10000 in
theorem vtD5_8 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6729) = σ (.n 6723) + σ (.n 2030) * vtSlots W ev 0
      [[], [], [([71], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6154 [
    .atom (.const (.n 6724) (word 3 0 0)),
    .atom (.mul (.n 6725) (.n 6724) (.n 5452)),
    .atom (.load (.n 6726) (.n 13) 2),
    .atom (.mul (.n 6727) (.n 6726) (.n 6725)),
    .atom (.mul (.n 6728) (.n 2030) (.n 6727)),
    .atom (.add (.n 6729) (.n 6723) (.n 6728))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6154, a6155, a6156, a6157, a6158, a6159, -⟩ := hs
  have e6156 := tb_loadHolds_unique a6156 (hw 2 (by norm_num))
  have v5452 : σ (.n 5452) = ev 71 := by
    rw [← hev 71 (by norm_num)]; exact (vt_eval h (k := 138) (by norm_num)).2.2
  have hB : σ (.n 6727) = vtSlots W ev 0 [[], [], [([71], 3)], [], [], []] := by
    simp only [v5452, a6157, e6156, a6155, a6154]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6159, a6158, hB]

set_option maxRecDepth 10000 in
theorem vtD5_9 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6735) = σ (.n 6729) + σ (.n 2032) * vtSlots W ev 0
      [[], [], [([72], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6160 [
    .atom (.const (.n 6730) (word 3 0 0)),
    .atom (.mul (.n 6731) (.n 6730) (.n 5463)),
    .atom (.load (.n 6732) (.n 13) 2),
    .atom (.mul (.n 6733) (.n 6732) (.n 6731)),
    .atom (.mul (.n 6734) (.n 2032) (.n 6733)),
    .atom (.add (.n 6735) (.n 6729) (.n 6734))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6160, a6161, a6162, a6163, a6164, a6165, -⟩ := hs
  have e6162 := tb_loadHolds_unique a6162 (hw 2 (by norm_num))
  have v5463 : σ (.n 5463) = ev 72 := by
    rw [← hev 72 (by norm_num)]; exact (vt_eval h (k := 139) (by norm_num)).2.2
  have hB : σ (.n 6733) = vtSlots W ev 0 [[], [], [([72], 3)], [], [], []] := by
    simp only [v5463, a6163, e6162, a6161, a6160]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6165, a6164, hB]

set_option maxRecDepth 10000 in
theorem vtD5_10 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6741) = σ (.n 6735) + σ (.n 2034) * vtSlots W ev 0
      [[], [], [([73], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6166 [
    .atom (.const (.n 6736) (word 3 0 0)),
    .atom (.mul (.n 6737) (.n 6736) (.n 5487)),
    .atom (.load (.n 6738) (.n 13) 2),
    .atom (.mul (.n 6739) (.n 6738) (.n 6737)),
    .atom (.mul (.n 6740) (.n 2034) (.n 6739)),
    .atom (.add (.n 6741) (.n 6735) (.n 6740))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6166, a6167, a6168, a6169, a6170, a6171, -⟩ := hs
  have e6168 := tb_loadHolds_unique a6168 (hw 2 (by norm_num))
  have v5487 : σ (.n 5487) = ev 73 := by
    rw [← hev 73 (by norm_num)]; exact (vt_eval h (k := 140) (by norm_num)).2.2
  have hB : σ (.n 6739) = vtSlots W ev 0 [[], [], [([73], 3)], [], [], []] := by
    simp only [v5487, a6169, e6168, a6167, a6166]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6171, a6170, hB]

set_option maxRecDepth 10000 in
theorem vtD5_11 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6747) = σ (.n 6741) + σ (.n 2036) * vtSlots W ev 0
      [[], [], [([74], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6172 [
    .atom (.const (.n 6742) (word 3 0 0)),
    .atom (.mul (.n 6743) (.n 6742) (.n 5498)),
    .atom (.load (.n 6744) (.n 13) 2),
    .atom (.mul (.n 6745) (.n 6744) (.n 6743)),
    .atom (.mul (.n 6746) (.n 2036) (.n 6745)),
    .atom (.add (.n 6747) (.n 6741) (.n 6746))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6172, a6173, a6174, a6175, a6176, a6177, -⟩ := hs
  have e6174 := tb_loadHolds_unique a6174 (hw 2 (by norm_num))
  have v5498 : σ (.n 5498) = ev 74 := by
    rw [← hev 74 (by norm_num)]; exact (vt_eval h (k := 141) (by norm_num)).2.2
  have hB : σ (.n 6745) = vtSlots W ev 0 [[], [], [([74], 3)], [], [], []] := by
    simp only [v5498, a6175, e6174, a6173, a6172]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6177, a6176, hB]

set_option maxRecDepth 10000 in
theorem vtD5_12 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6753) = σ (.n 6747) + σ (.n 2038) * vtSlots W ev 0
      [[], [], [([75], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6178 [
    .atom (.const (.n 6748) (word 3 0 0)),
    .atom (.mul (.n 6749) (.n 6748) (.n 5509)),
    .atom (.load (.n 6750) (.n 13) 2),
    .atom (.mul (.n 6751) (.n 6750) (.n 6749)),
    .atom (.mul (.n 6752) (.n 2038) (.n 6751)),
    .atom (.add (.n 6753) (.n 6747) (.n 6752))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6178, a6179, a6180, a6181, a6182, a6183, -⟩ := hs
  have e6180 := tb_loadHolds_unique a6180 (hw 2 (by norm_num))
  have v5509 : σ (.n 5509) = ev 75 := by
    rw [← hev 75 (by norm_num)]; exact (vt_eval h (k := 142) (by norm_num)).2.2
  have hB : σ (.n 6751) = vtSlots W ev 0 [[], [], [([75], 3)], [], [], []] := by
    simp only [v5509, a6181, e6180, a6179, a6178]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6183, a6182, hB]

set_option maxRecDepth 10000 in
theorem vtD5_13 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6759) = σ (.n 6753) + σ (.n 2040) * vtSlots W ev 0
      [[], [], [([76], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6184 [
    .atom (.const (.n 6754) (word 3 0 0)),
    .atom (.mul (.n 6755) (.n 6754) (.n 5520)),
    .atom (.load (.n 6756) (.n 13) 2),
    .atom (.mul (.n 6757) (.n 6756) (.n 6755)),
    .atom (.mul (.n 6758) (.n 2040) (.n 6757)),
    .atom (.add (.n 6759) (.n 6753) (.n 6758))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6184, a6185, a6186, a6187, a6188, a6189, -⟩ := hs
  have e6186 := tb_loadHolds_unique a6186 (hw 2 (by norm_num))
  have v5520 : σ (.n 5520) = ev 76 := by
    rw [← hev 76 (by norm_num)]; exact (vt_eval h (k := 143) (by norm_num)).2.2
  have hB : σ (.n 6757) = vtSlots W ev 0 [[], [], [([76], 3)], [], [], []] := by
    simp only [v5520, a6187, e6186, a6185, a6184]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6189, a6188, hB]

set_option maxRecDepth 10000 in
theorem vtD5_14 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6765) = σ (.n 6759) + σ (.n 2042) * vtSlots W ev 0
      [[], [], [([77], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6190 [
    .atom (.const (.n 6760) (word 3 0 0)),
    .atom (.mul (.n 6761) (.n 6760) (.n 5544)),
    .atom (.load (.n 6762) (.n 13) 2),
    .atom (.mul (.n 6763) (.n 6762) (.n 6761)),
    .atom (.mul (.n 6764) (.n 2042) (.n 6763)),
    .atom (.add (.n 6765) (.n 6759) (.n 6764))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6190, a6191, a6192, a6193, a6194, a6195, -⟩ := hs
  have e6192 := tb_loadHolds_unique a6192 (hw 2 (by norm_num))
  have v5544 : σ (.n 5544) = ev 77 := by
    rw [← hev 77 (by norm_num)]; exact (vt_eval h (k := 144) (by norm_num)).2.2
  have hB : σ (.n 6763) = vtSlots W ev 0 [[], [], [([77], 3)], [], [], []] := by
    simp only [v5544, a6193, e6192, a6191, a6190]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6195, a6194, hB]

set_option maxRecDepth 10000 in
theorem vtD5_15 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6771) = σ (.n 6765) + σ (.n 2044) * vtSlots W ev 0
      [[], [], [([78], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6196 [
    .atom (.const (.n 6766) (word 3 0 0)),
    .atom (.mul (.n 6767) (.n 6766) (.n 5555)),
    .atom (.load (.n 6768) (.n 13) 2),
    .atom (.mul (.n 6769) (.n 6768) (.n 6767)),
    .atom (.mul (.n 6770) (.n 2044) (.n 6769)),
    .atom (.add (.n 6771) (.n 6765) (.n 6770))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6196, a6197, a6198, a6199, a6200, a6201, -⟩ := hs
  have e6198 := tb_loadHolds_unique a6198 (hw 2 (by norm_num))
  have v5555 : σ (.n 5555) = ev 78 := by
    rw [← hev 78 (by norm_num)]; exact (vt_eval h (k := 145) (by norm_num)).2.2
  have hB : σ (.n 6769) = vtSlots W ev 0 [[], [], [([78], 3)], [], [], []] := by
    simp only [v5555, a6199, e6198, a6197, a6196]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6201, a6200, hB]

set_option maxRecDepth 10000 in
theorem vtD5_16 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6778) = σ (.n 6771) + σ (.n 2046) * vtSlots W ev 0
      [[], [], [([12, 79], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6202 [
    .atom (.const (.n 6772) (word 3 0 0)),
    .atom (.mul (.n 6773) (.n 4608) (.n 5566)),
    .atom (.mul (.n 6774) (.n 6772) (.n 6773)),
    .atom (.load (.n 6775) (.n 13) 2),
    .atom (.mul (.n 6776) (.n 6775) (.n 6774)),
    .atom (.mul (.n 6777) (.n 2046) (.n 6776)),
    .atom (.add (.n 6778) (.n 6771) (.n 6777))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6202, a6203, a6204, a6205, a6206, a6207, a6208, -⟩ := hs
  have e6205 := tb_loadHolds_unique a6205 (hw 2 (by norm_num))
  have v4608 : σ (.n 4608) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 79) (by norm_num)).2.2
  have v5566 : σ (.n 5566) = ev 79 := by
    rw [← hev 79 (by norm_num)]; exact (vt_eval h (k := 146) (by norm_num)).2.2
  have hB : σ (.n 6776) = vtSlots W ev 0 [[], [], [([12, 79], 3)], [], [], []] := by
    simp only [v5566, v4608, a6206, e6205, a6204, a6203, a6202]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6208, a6207, hB]

set_option maxRecDepth 10000 in
theorem vtD5_17 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6785) = σ (.n 6778) + σ (.n 2048) * vtSlots W ev 0
      [[], [], [([13, 80], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6209 [
    .atom (.const (.n 6779) (word 3 0 0)),
    .atom (.mul (.n 6780) (.n 4632) (.n 5577)),
    .atom (.mul (.n 6781) (.n 6779) (.n 6780)),
    .atom (.load (.n 6782) (.n 13) 2),
    .atom (.mul (.n 6783) (.n 6782) (.n 6781)),
    .atom (.mul (.n 6784) (.n 2048) (.n 6783)),
    .atom (.add (.n 6785) (.n 6778) (.n 6784))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6209, a6210, a6211, a6212, a6213, a6214, a6215, -⟩ := hs
  have e6212 := tb_loadHolds_unique a6212 (hw 2 (by norm_num))
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 80) (by norm_num)).2.2
  have v5577 : σ (.n 5577) = ev 80 := by
    rw [← hev 80 (by norm_num)]; exact (vt_eval h (k := 147) (by norm_num)).2.2
  have hB : σ (.n 6783) = vtSlots W ev 0 [[], [], [([13, 80], 3)], [], [], []] := by
    simp only [v5577, v4632, a6213, e6212, a6211, a6210, a6209]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6215, a6214, hB]

set_option maxRecDepth 10000 in
theorem vtD5_18 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6792) = σ (.n 6785) + σ (.n 2050) * vtSlots W ev 0
      [[], [], [([13, 81], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6216 [
    .atom (.const (.n 6786) (word 3 0 0)),
    .atom (.mul (.n 6787) (.n 4632) (.n 5601)),
    .atom (.mul (.n 6788) (.n 6786) (.n 6787)),
    .atom (.load (.n 6789) (.n 13) 2),
    .atom (.mul (.n 6790) (.n 6789) (.n 6788)),
    .atom (.mul (.n 6791) (.n 2050) (.n 6790)),
    .atom (.add (.n 6792) (.n 6785) (.n 6791))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6216, a6217, a6218, a6219, a6220, a6221, a6222, -⟩ := hs
  have e6219 := tb_loadHolds_unique a6219 (hw 2 (by norm_num))
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 80) (by norm_num)).2.2
  have v5601 : σ (.n 5601) = ev 81 := by
    rw [← hev 81 (by norm_num)]; exact (vt_eval h (k := 148) (by norm_num)).2.2
  have hB : σ (.n 6790) = vtSlots W ev 0 [[], [], [([13, 81], 3)], [], [], []] := by
    simp only [v5601, v4632, a6220, e6219, a6218, a6217, a6216]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6222, a6221, hB]

set_option maxRecDepth 10000 in
theorem vtD5_19 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6799) = σ (.n 6792) + σ (.n 2052) * vtSlots W ev 0
      [[], [], [([13, 82], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6223 [
    .atom (.const (.n 6793) (word 3 0 0)),
    .atom (.mul (.n 6794) (.n 4632) (.n 5612)),
    .atom (.mul (.n 6795) (.n 6793) (.n 6794)),
    .atom (.load (.n 6796) (.n 13) 2),
    .atom (.mul (.n 6797) (.n 6796) (.n 6795)),
    .atom (.mul (.n 6798) (.n 2052) (.n 6797)),
    .atom (.add (.n 6799) (.n 6792) (.n 6798))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6223, a6224, a6225, a6226, a6227, a6228, a6229, -⟩ := hs
  have e6226 := tb_loadHolds_unique a6226 (hw 2 (by norm_num))
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 80) (by norm_num)).2.2
  have v5612 : σ (.n 5612) = ev 82 := by
    rw [← hev 82 (by norm_num)]; exact (vt_eval h (k := 149) (by norm_num)).2.2
  have hB : σ (.n 6797) = vtSlots W ev 0 [[], [], [([13, 82], 3)], [], [], []] := by
    simp only [v5612, v4632, a6227, e6226, a6225, a6224, a6223]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6229, a6228, hB]

set_option maxRecDepth 10000 in
theorem vtD5_20 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6806) = σ (.n 6799) + σ (.n 2054) * vtSlots W ev 0
      [[], [], [([13, 83], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6230 [
    .atom (.const (.n 6800) (word 3 0 0)),
    .atom (.mul (.n 6801) (.n 4632) (.n 5623)),
    .atom (.mul (.n 6802) (.n 6800) (.n 6801)),
    .atom (.load (.n 6803) (.n 13) 2),
    .atom (.mul (.n 6804) (.n 6803) (.n 6802)),
    .atom (.mul (.n 6805) (.n 2054) (.n 6804)),
    .atom (.add (.n 6806) (.n 6799) (.n 6805))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6230, a6231, a6232, a6233, a6234, a6235, a6236, -⟩ := hs
  have e6233 := tb_loadHolds_unique a6233 (hw 2 (by norm_num))
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 80) (by norm_num)).2.2
  have v5623 : σ (.n 5623) = ev 83 := by
    rw [← hev 83 (by norm_num)]; exact (vt_eval h (k := 150) (by norm_num)).2.2
  have hB : σ (.n 6804) = vtSlots W ev 0 [[], [], [([13, 83], 3)], [], [], []] := by
    simp only [v5623, v4632, a6234, e6233, a6232, a6231, a6230]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6236, a6235, hB]

set_option maxRecDepth 10000 in
theorem vtD5_21 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6813) = σ (.n 6806) + σ (.n 2056) * vtSlots W ev 0
      [[], [], [([13, 84], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6237 [
    .atom (.const (.n 6807) (word 3 0 0)),
    .atom (.mul (.n 6808) (.n 4632) (.n 5634)),
    .atom (.mul (.n 6809) (.n 6807) (.n 6808)),
    .atom (.load (.n 6810) (.n 13) 2),
    .atom (.mul (.n 6811) (.n 6810) (.n 6809)),
    .atom (.mul (.n 6812) (.n 2056) (.n 6811)),
    .atom (.add (.n 6813) (.n 6806) (.n 6812))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6237, a6238, a6239, a6240, a6241, a6242, a6243, -⟩ := hs
  have e6240 := tb_loadHolds_unique a6240 (hw 2 (by norm_num))
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 80) (by norm_num)).2.2
  have v5634 : σ (.n 5634) = ev 84 := by
    rw [← hev 84 (by norm_num)]; exact (vt_eval h (k := 151) (by norm_num)).2.2
  have hB : σ (.n 6811) = vtSlots W ev 0 [[], [], [([13, 84], 3)], [], [], []] := by
    simp only [v5634, v4632, a6241, e6240, a6239, a6238, a6237]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6243, a6242, hB]

set_option maxRecDepth 10000 in
theorem vtD5_22 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6820) = σ (.n 6813) + σ (.n 2058) * vtSlots W ev 0
      [[], [], [([13, 85], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6244 [
    .atom (.const (.n 6814) (word 3 0 0)),
    .atom (.mul (.n 6815) (.n 4632) (.n 5658)),
    .atom (.mul (.n 6816) (.n 6814) (.n 6815)),
    .atom (.load (.n 6817) (.n 13) 2),
    .atom (.mul (.n 6818) (.n 6817) (.n 6816)),
    .atom (.mul (.n 6819) (.n 2058) (.n 6818)),
    .atom (.add (.n 6820) (.n 6813) (.n 6819))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6244, a6245, a6246, a6247, a6248, a6249, a6250, -⟩ := hs
  have e6247 := tb_loadHolds_unique a6247 (hw 2 (by norm_num))
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 80) (by norm_num)).2.2
  have v5658 : σ (.n 5658) = ev 85 := by
    rw [← hev 85 (by norm_num)]; exact (vt_eval h (k := 152) (by norm_num)).2.2
  have hB : σ (.n 6818) = vtSlots W ev 0 [[], [], [([13, 85], 3)], [], [], []] := by
    simp only [v5658, v4632, a6248, e6247, a6246, a6245, a6244]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6250, a6249, hB]

set_option maxRecDepth 10000 in
theorem vtD5_23 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6827) = σ (.n 6820) + σ (.n 2060) * vtSlots W ev 0
      [[], [], [([13, 86], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6251 [
    .atom (.const (.n 6821) (word 3 0 0)),
    .atom (.mul (.n 6822) (.n 4632) (.n 5669)),
    .atom (.mul (.n 6823) (.n 6821) (.n 6822)),
    .atom (.load (.n 6824) (.n 13) 2),
    .atom (.mul (.n 6825) (.n 6824) (.n 6823)),
    .atom (.mul (.n 6826) (.n 2060) (.n 6825)),
    .atom (.add (.n 6827) (.n 6820) (.n 6826))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6251, a6252, a6253, a6254, a6255, a6256, a6257, -⟩ := hs
  have e6254 := tb_loadHolds_unique a6254 (hw 2 (by norm_num))
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 80) (by norm_num)).2.2
  have v5669 : σ (.n 5669) = ev 86 := by
    rw [← hev 86 (by norm_num)]; exact (vt_eval h (k := 153) (by norm_num)).2.2
  have hB : σ (.n 6825) = vtSlots W ev 0 [[], [], [([13, 86], 3)], [], [], []] := by
    simp only [v5669, v4632, a6255, e6254, a6253, a6252, a6251]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6257, a6256, hB]

set_option maxRecDepth 10000 in
theorem vtD5_24 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6834) = σ (.n 6827) + σ (.n 2062) * vtSlots W ev 0
      [[], [], [([13, 87], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6258 [
    .atom (.const (.n 6828) (word 3 0 0)),
    .atom (.mul (.n 6829) (.n 4632) (.n 5680)),
    .atom (.mul (.n 6830) (.n 6828) (.n 6829)),
    .atom (.load (.n 6831) (.n 13) 2),
    .atom (.mul (.n 6832) (.n 6831) (.n 6830)),
    .atom (.mul (.n 6833) (.n 2062) (.n 6832)),
    .atom (.add (.n 6834) (.n 6827) (.n 6833))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6258, a6259, a6260, a6261, a6262, a6263, a6264, -⟩ := hs
  have e6261 := tb_loadHolds_unique a6261 (hw 2 (by norm_num))
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 80) (by norm_num)).2.2
  have v5680 : σ (.n 5680) = ev 87 := by
    rw [← hev 87 (by norm_num)]; exact (vt_eval h (k := 154) (by norm_num)).2.2
  have hB : σ (.n 6832) = vtSlots W ev 0 [[], [], [([13, 87], 3)], [], [], []] := by
    simp only [v5680, v4632, a6262, e6261, a6260, a6259, a6258]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6264, a6263, hB]

set_option maxRecDepth 10000 in
theorem vtD5_25 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6841) = σ (.n 6834) + σ (.n 2064) * vtSlots W ev 0
      [[], [], [([13, 88], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6265 [
    .atom (.const (.n 6835) (word 3 0 0)),
    .atom (.mul (.n 6836) (.n 4632) (.n 5691)),
    .atom (.mul (.n 6837) (.n 6835) (.n 6836)),
    .atom (.load (.n 6838) (.n 13) 2),
    .atom (.mul (.n 6839) (.n 6838) (.n 6837)),
    .atom (.mul (.n 6840) (.n 2064) (.n 6839)),
    .atom (.add (.n 6841) (.n 6834) (.n 6840))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6265, a6266, a6267, a6268, a6269, a6270, a6271, -⟩ := hs
  have e6268 := tb_loadHolds_unique a6268 (hw 2 (by norm_num))
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 80) (by norm_num)).2.2
  have v5691 : σ (.n 5691) = ev 88 := by
    rw [← hev 88 (by norm_num)]; exact (vt_eval h (k := 155) (by norm_num)).2.2
  have hB : σ (.n 6839) = vtSlots W ev 0 [[], [], [([13, 88], 3)], [], [], []] := by
    simp only [v5691, v4632, a6269, e6268, a6267, a6266, a6265]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6271, a6270, hB]

set_option maxRecDepth 10000 in
theorem vtD5_26 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6848) = σ (.n 6841) + σ (.n 2066) * vtSlots W ev 0
      [[], [], [([13, 89], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6272 [
    .atom (.const (.n 6842) (word 3 0 0)),
    .atom (.mul (.n 6843) (.n 4632) (.n 5715)),
    .atom (.mul (.n 6844) (.n 6842) (.n 6843)),
    .atom (.load (.n 6845) (.n 13) 2),
    .atom (.mul (.n 6846) (.n 6845) (.n 6844)),
    .atom (.mul (.n 6847) (.n 2066) (.n 6846)),
    .atom (.add (.n 6848) (.n 6841) (.n 6847))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6272, a6273, a6274, a6275, a6276, a6277, a6278, -⟩ := hs
  have e6275 := tb_loadHolds_unique a6275 (hw 2 (by norm_num))
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 80) (by norm_num)).2.2
  have v5715 : σ (.n 5715) = ev 89 := by
    rw [← hev 89 (by norm_num)]; exact (vt_eval h (k := 156) (by norm_num)).2.2
  have hB : σ (.n 6846) = vtSlots W ev 0 [[], [], [([13, 89], 3)], [], [], []] := by
    simp only [v5715, v4632, a6276, e6275, a6274, a6273, a6272]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6278, a6277, hB]

set_option maxRecDepth 10000 in
theorem vtD5_27 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (67 + c))) = ev c) :
    σ (.n 6855) = σ (.n 6848) + σ (.n 2068) * vtSlots W ev 0
      [[], [], [([13, 90], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 6279 [
    .atom (.const (.n 6849) (word 3 0 0)),
    .atom (.mul (.n 6850) (.n 4632) (.n 5726)),
    .atom (.mul (.n 6851) (.n 6849) (.n 6850)),
    .atom (.load (.n 6852) (.n 13) 2),
    .atom (.mul (.n 6853) (.n 6852) (.n 6851)),
    .atom (.mul (.n 6854) (.n 2068) (.n 6853)),
    .atom (.add (.n 6855) (.n 6848) (.n 6854))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a6279, a6280, a6281, a6282, a6283, a6284, a6285, -⟩ := hs
  have e6282 := tb_loadHolds_unique a6282 (hw 2 (by norm_num))
  have v4632 : σ (.n 4632) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 80) (by norm_num)).2.2
  have v5726 : σ (.n 5726) = ev 90 := by
    rw [← hev 90 (by norm_num)]; exact (vt_eval h (k := 157) (by norm_num)).2.2
  have hB : σ (.n 6853) = vtSlots W ev 0 [[], [], [([13, 90], 3)], [], [], []] := by
    simp only [v5726, v4632, a6283, e6282, a6281, a6280, a6279]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a6285, a6284, hB]

end
end LeanVM.Guest.B1.Tables
