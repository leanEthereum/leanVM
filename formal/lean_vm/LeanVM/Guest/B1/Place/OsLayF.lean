/-
  LeanVM.Guest.B1.Place.OsLayF

  open_stacked's own buffers on f128, at `osSizesF`'s layout: their pointers from a base, the
  window pointers' buffer from the levels' decoder groups, and the callees' words.
-/

module

public import LeanVM.Guest.B1.Place.OsSqGroup
public import LeanVM.Guest.B1.Place.OsBos
public import LeanVM.Guest.B1.Place.OsPlace
public import LeanVM.Guest.B1.Place.OsCallV

/-!
# The buffers, laid out

The buffers in allocation order (`osSizesF c`, S6's `OsBos`) from the base `b`: buffer `j` at
`g^(osBaseF c b j)` (`bases`), its pointer `osPtrF c b j`. `query_win_ptrs` (index `osIxQbp`)
holds the window pointers into the decoders' frames, so its words depend on where the levels'
decoder groups are placed: `osQbpC c ws`, level `l`'s slice `ws l` from its `posOff`; the other
buffers' words `own` do not.

* `memL_bufL_get`: a memory holding the buffers reads buffer `j`'s words at its pointer.
* `osLkF c b own Lin`: the words the callees read before the groups are placed: every buffer but
  `query_win_ptrs`, and the caller's words; `memL_osLkF` from the buffers with any window pointers.
* `osQbpC_get`, `memL_osW`: level `l`'s slice of `query_win_ptrs` (`sqW`), held where the buffers
  are; `regionL_osW`, `regionL_osLkF`: their addresses among the buffers' and the caller's.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir

@[expose] public section

/-- `query_win_ptrs`' index among the buffers. -/
abbrev osIxQbp : ℕ := 12

/-- Buffer `j`'s exponent from `b`. -/
def osBaseF (c : OsCfg) (b j : ℕ) : ℕ := (bases b (osSizesF c)).getD j 0

/-- Buffer `j`'s pointer from `b`. -/
def osPtrF (c : OsCfg) (b j : ℕ) : E := ofK (addressOfIndex (osBaseF c b j))

/-- `query_win_ptrs`' words: level `l`'s slice `ws l` from its offset, `0` elsewhere. -/
def osQbpC (c : OsCfg) (ws : ℕ → List E) : List E :=
  (List.range c.posLen).map fun k ↦
    match (List.range c.levels.length).find?
        (fun l ↦ decide ((osLvAt c l).posOff ≤ k ∧ k < (osLvAt c l).posOff + (ws l).length)) with
    | some l => (ws l).getD (k - (osLvAt c l).posOff) 0
    | none => 0

/-- The callees' words before the groups are placed: the buffers but `query_win_ptrs`, and the
caller's. -/
def osLkF (c : OsCfg) (b : ℕ) (own : List (List E)) (Lin : Layout) : Layout :=
  (bufL b (osSizesF c) own).eraseIdx osIxQbp ++ Lin

theorem length_bases : ∀ (b : ℕ) (sizes : List ℕ), (bases b sizes).length = sizes.length :=
  os_length_bases

/-- **A memory holding the buffers reads buffer `j`.** -/
theorem memL_bufL_get {rd : Reader} {b : ℕ} {sizes : List ℕ} {own : List (List E)}
    (hf : List.Forall₂ (fun c s ↦ c.length ≤ s) own sizes) (hm : MemL rd (bufL b sizes own))
    {j : ℕ} (hj : j < sizes.length) :
    ReadsAt rd (ofK (addressOfIndex ((bases b sizes).getD j 0))) (own.getD j []) := by
  have e := os_bufL_getD (b := b) hf hj
  have hlen : j < (bufL b sizes own).length := by
    simp only [bufL, List.length_zip, os_length_bases, hf.length_eq, Nat.min_self]; exact hj
  have hmem : (bufL b sizes own).getD j default ∈ bufL b sizes own := by
    rw [List.getD_eq_getElem _ _ hlen]; exact List.getElem_mem hlen
  rw [e] at hmem
  exact hm _ hmem

theorem forall₂_set {own : List (List E)} {sizes : List ℕ}
    (hf : List.Forall₂ (fun c s ↦ c.length ≤ s) own sizes) {j : ℕ} {q : List E}
    (hq : q.length ≤ sizes.getD j 0) :
    List.Forall₂ (fun c s ↦ c.length ≤ s) (own.set j q) sizes := by
  rw [List.forall₂_iff_get] at hf ⊢
  obtain ⟨hl, hg⟩ := hf
  refine ⟨by rw [List.length_set, hl], fun i h1 h2 ↦ ?_⟩
  simp only [List.get_eq_getElem, List.getElem_set]
  split
  · next he =>
    subst he
    rwa [List.getD_eq_getElem _ _ h2] at hq
  · exact hg i (by rw [List.length_set] at h1; exact h1) h2

/-- **The callees' words**, held where the buffers are, whatever `query_win_ptrs` holds. -/
theorem memL_osLkF {rd : Reader} {c : OsCfg} {b : ℕ} {own : List (List E)} {q : List E}
    {Lin : Layout} (hm : MemL rd (bufL b (osSizesF c) (own.set osIxQbp q))) (hLin : MemL rd Lin) :
    MemL rd (osLkF c b own Lin) := by
  refine Main.memL_append.mpr ⟨fun x hx ↦ ?_, hLin⟩
  obtain ⟨i, hi, hne, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hx
  have hl : (bufL b (osSizesF c) (own.set osIxQbp q)).length =
      (bufL b (osSizesF c) own).length := by simp [bufL]
  have hi1 : i < (bufL b (osSizesF c) (own.set osIxQbp q)).length := by omega
  have e : (bufL b (osSizesF c) own)[i]'hi = (bufL b (osSizesF c) (own.set osIxQbp q))[i]'hi1 := by
    simp only [bufL, List.getElem_zip, List.getElem_set, Ne.symm hne, ↓reduceIte]
  rw [e]
  exact hm _ (List.getElem_mem hi1)

theorem regionL_osLkF {c : OsCfg} {b : ℕ} {own : List (List E)} {q : List E} {Lin : Layout}
    {i : ℕ} (h : RegionL (osLkF c b own Lin) i) :
    RegionL Lin i ∨ RegionL (bufL b (osSizesF c) (own.set osIxQbp q)) i := by
  obtain ⟨x, hx, h1, h2⟩ := h
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨j, hj, hne, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hx
    refine Or.inr ⟨(bufL b (osSizesF c) (own.set osIxQbp q))[j]'(by simpa [bufL] using hj),
      List.getElem_mem _, ?_, ?_⟩
    · simpa [bufL, List.getElem_zip] using h1
    · simpa [bufL, List.getElem_zip, List.getElem_set, Ne.symm hne] using h2
  · exact Or.inl ⟨x, hx, h1, h2⟩

/-! ## The window pointers -/

theorem osIxQbp_lt (c : OsCfg) : osIxQbp < (osSizesF c).length := by
  show 12 < _
  unfold osSizesF
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

theorem osSizesF_qbp (c : OsCfg) : (osSizesF c).getD osIxQbp 0 = c.posLen := by
  simp [osSizesF]

theorem osQbpC_length (c : OsCfg) (ws : ℕ → List E) : (osQbpC c ws).length = c.posLen := by
  simp [osQbpC]

/-- The levels' slices are in order, within the buffer. -/
def OsQbpFit (c : OsCfg) (ws : ℕ → List E) : Prop :=
  (∀ l l', l < l' → l' < c.levels.length →
      (osLvAt c l).posOff + (ws l).length ≤ (osLvAt c l').posOff) ∧
    ∀ l < c.levels.length, (osLvAt c l).posOff + (ws l).length ≤ c.posLen

theorem osQbpC_get {c : OsCfg} {ws : ℕ → List E} (hfit : OsQbpFit c ws)
    {l : ℕ} (hl : l < c.levels.length) {k : ℕ} (hk : k < (ws l).length) :
    (osQbpC c ws).getD ((osLvAt c l).posOff + k) 0 = (ws l)[k] := by
  have h2 := hfit.2 l hl
  have hlt : (osLvAt c l).posOff + k < (osQbpC c ws).length := by
    rw [osQbpC_length]; omega
  rw [List.getD_eq_getElem _ _ hlt]
  simp only [osQbpC, List.getElem_map, List.getElem_range]
  have hfind : (List.range c.levels.length).find?
      (fun l' ↦ decide ((osLvAt c l').posOff ≤ (osLvAt c l).posOff + k ∧
        (osLvAt c l).posOff + k < (osLvAt c l').posOff + (ws l').length)) = some l := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by rw [decide_eq_true_eq]; omega, l, by rw [List.length_range]; exact hl,
      List.getElem_range _, fun j hj ↦ ?_⟩
    have hj' : j < l := hj
    have := hfit.1 j l hj' hl
    rw [List.getElem_range, Bool.not_eq_true', decide_eq_false_iff_not]
    rintro ⟨-, h⟩
    omega
  rw [hfind]
  simp only [Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ hk]

/-- **Level `l`'s window pointers**, held where the buffers are. -/
theorem memL_osW {rd : Reader} {c : OsCfg} {b : ℕ} {own : List (List E)} {ws : ℕ → List E}
    (hf : List.Forall₂ (fun c s ↦ c.length ≤ s) own (osSizesF c)) (hfit : OsQbpFit c ws)
    (hm : MemL rd (bufL b (osSizesF c) (own.set osIxQbp (osQbpC c ws)))) {l : ℕ}
    (hl : l < c.levels.length) :
    MemL rd [(osBaseF c b osIxQbp + (osLvAt c l).posOff, ws l)] := by
  intro x hx k hk
  simp only [List.mem_singleton] at hx
  subst hx
  have hk' : k < (ws l).length := hk
  have hf' := forall₂_set hf (j := osIxQbp) (q := osQbpC c ws)
    (by rw [osSizesF_qbp, osQbpC_length])
  have hj := osIxQbp_lt c
  have R := memL_bufL_get hf' hm hj
  have e : (own.set osIxQbp (osQbpC c ws)).getD osIxQbp [] = osQbpC c ws := by
    rw [List.getD_eq_getElem _ _ (by simp [hf.length_eq, hj]), List.getElem_set_self]
  rw [e] at R
  have h2 := hfit.2 l hl
  have hlt : (osLvAt c l).posOff + k < (osQbpC c ws).length := by rw [osQbpC_length]; omega
  have := R _ hlt
  rw [← List.getD_eq_getElem _ 0 hlt, osQbpC_get hfit hl hk'] at this
  exact (loadHolds_ofK_iff (by simp only [osBaseF]; ring)).mp this

theorem regionL_osW {c : OsCfg} {b : ℕ} {own : List (List E)} {ws : ℕ → List E}
    (hf : List.Forall₂ (fun c s ↦ c.length ≤ s) own (osSizesF c)) (hfit : OsQbpFit c ws) {l : ℕ}
    (hl : l < c.levels.length) {i : ℕ}
    (h : RegionL [(osBaseF c b osIxQbp + (osLvAt c l).posOff, ws l)] i) :
    RegionL (bufL b (osSizesF c) (own.set osIxQbp (osQbpC c ws))) i := by
  obtain ⟨x, hx, h1, h2⟩ := h
  simp only [List.mem_singleton] at hx
  subst hx
  have hj := osIxQbp_lt c
  have hjb : osIxQbp < (bases b (osSizesF c)).length := by rw [length_bases]; exact hj
  have hjo : osIxQbp < (own.set osIxQbp (osQbpC c ws)).length := by
    simp [hf.length_eq, hj]
  have hl1 : osIxQbp < (bufL b (osSizesF c) (own.set osIxQbp (osQbpC c ws))).length := by
    simp only [bufL, List.length_zip]; omega
  have h3 := hfit.2 l hl
  have h1' : osBaseF c b osIxQbp + (osLvAt c l).posOff ≤ i := h1
  have h2' : i < osBaseF c b osIxQbp + (osLvAt c l).posOff + (ws l).length := h2
  refine ⟨_, List.getElem_mem hl1, ?_, ?_⟩
  · simp only [bufL, List.getElem_zip]
    rw [osBaseF, List.getD_eq_getElem _ _ hjb] at h1'
    omega
  · simp only [bufL, List.getElem_zip, List.getElem_set_self, osQbpC_length]
    rw [osBaseF, List.getD_eq_getElem _ _ hjb] at h2'
    omega

end
end LeanVM.Guest.B1
