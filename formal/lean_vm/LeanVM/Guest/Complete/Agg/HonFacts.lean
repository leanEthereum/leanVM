module

public import LeanVM.Guest.Complete.Agg.Hon
public import LeanVM.Guest.Complete.MainRunFacts

/-!
# `aggregate_claims`' honest valuation

`aV al s w cover c`: the forward valuation at the honest data (`aRd0`, `aOrc`, `main`'s arguments).

* `aV_good`: each atom of the body satisfies its equations on it; `aV_param`: the arguments.
* `aV_ptrs`: the eleven `HeapBuf` pointers are `ptrAt` of their bases `aB c m j`.
* `aLoad_fresh`: a load into a new value reads the evaluation memory's word, and every memory holding
  its runs holds it there.
* The own words: `aWo_get` (buffer `j` from its base), `valAt_own` (the evaluation memory's word in a
  buffer is the honest content), `aB_lt` (the buffers lie in `[c, c + Σ aBufs m)`), `own_aB` (they
  are the node's own data).
* `main`'s words: `holds_run` (a memory holding runs holds each run's words).
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VsC LeanVM.Guest.Complete
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

attribute [local instance high] LeanVM.Guest.Core.instDecidableEqAtom

/-- **`aggregate_claims`' forward valuation at the honest data.** -/
noncomputable def aV (al : String → Bool) (s : NodeStatement) (w : NodeWitness) (cover : List E) (c : ℕ) : Val :=
  aVal (aRd0 al s w cover c) (aOrc w c) (aggArgs al (mainCounts s w))

theorem addr_ptr (b o : ℕ) : (ptrAt b).limb 0 * addressOfIndex o = addressOfIndex (b + o) := Main.addr_ofK b o

theorem loadHolds_of_rd {rd : Reader} {b off : ℕ} {v : E} (h : rd (addressOfIndex (b + off)) = some v) :
    LoadHolds rd (ptrAt b) off v := ⟨ofK_isInK _, by rw [addr_ptr]; exact h⟩

/-- **A memory holding runs holds each run's words.** -/
theorem holds_run {rd : Reader} {W : Words} (h : HoldsWords rd W) {q : ℕ × List E} (hq : q ∈ W) {k : ℕ}
    (hk : k < q.2.length) : rd (addressOfIndex (q.1 + k)) = some (q.2.getD k 0) := by
  have := (h q hq k hk).2
  rwa [Main.addr_ofK, ← List.getD_eq_getElem _ 0 hk] at this

theorem valAt_append_left : ∀ {W W' : Words} {i : ℕ}, InW W i → valAt (W ++ W') i = valAt W i
  | [], _, _, h => by obtain ⟨q, hq, -⟩ := h; simp at hq
  | q :: W, W', i, h => by
    by_cases hi : q.1 ≤ i ∧ i < q.1 + q.2.length
    · simp [valAt, hi]
    · obtain ⟨q', hq', h'⟩ := h
      rcases List.mem_cons.mp hq' with rfl | hq'
      · exact (hi h').elim
      · simp only [List.cons_append, valAt, hi, ↓reduceIte]
        exact valAt_append_left ⟨q', hq', h'⟩

section
variable {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {cover : List E} {c : ℕ}

theorem aggArgs_length (al : String → Bool) (m : MainCounts) : (aggArgs al m).length = 6 := rfl

/-- **An atom of the body satisfies its equations** on the honest valuation. -/
theorem aV_good {x : Atom} (hx : x ∈ atomsOf aggP) :
    Good (aRd0 al s w cover c) (storesOf 6 aggP) (aOrc w c) (aV al s w cover c) x :=
  aVal_good (aggArgs_length _ _) _ (atom_mem_of_atomsOf hx)

theorem aV_param {i : ℕ} (hi : i < 6) : aV al s w cover c (.n i) = (aggArgs al (mainCounts s w)).getD i 0 :=
  aVal_param (aggArgs_length _ _) hi

set_option maxRecDepth 200000 in
theorem aAlloc_mems :
    Atom.hint (.alloc (.n 6) 51) ∈ atomsOf aggP ∧ Atom.hint (.allocDyn (.n 8) (.n 0)) ∈ atomsOf aggP ∧
    Atom.hint (.allocDyn (.n 9) (.n 0)) ∈ atomsOf aggP ∧ Atom.hint (.allocDyn (.n 30) (.n 29)) ∈ atomsOf aggP ∧
    Atom.hint (.alloc (.n 156) 6) ∈ atomsOf aggP ∧ Atom.hint (.alloc (.n 235) 126) ∈ atomsOf aggP ∧
    Atom.hint (.allocDyn (.n 440) (.n 0)) ∈ atomsOf aggP ∧ Atom.hint (.allocDyn (.n 449) (.n 448)) ∈ atomsOf aggP ∧
    Atom.hint (.alloc (.n 458) 25) ∈ atomsOf aggP ∧ Atom.hint (.alloc (.n 467) 25) ∈ atomsOf aggP ∧
    Atom.hint (.allocDyn (.n 568) (.n 567)) ∈ atomsOf aggP := by
  decide +kernel

/-- **The `HeapBuf` pointers** at the honest oracle: their bases from `c`. -/
theorem aV_ptrs : aV al s w cover c (.n 6) = ptrAt (aB c w.children.length 0) ∧
    aV al s w cover c (.n 8) = ptrAt (aB c w.children.length 1) ∧
    aV al s w cover c (.n 9) = ptrAt (aB c w.children.length 2) ∧
    aV al s w cover c (.n 30) = ptrAt (aB c w.children.length 3) ∧
    aV al s w cover c (.n 156) = ptrAt (aB c w.children.length 4) ∧
    aV al s w cover c (.n 235) = ptrAt (aB c w.children.length 5) ∧
    aV al s w cover c (.n 440) = ptrAt (aB c w.children.length 6) ∧
    aV al s w cover c (.n 449) = ptrAt (aB c w.children.length 7) ∧
    aV al s w cover c (.n 458) = ptrAt (aB c w.children.length 8) ∧
    aV al s w cover c (.n 467) = ptrAt (aB c w.children.length 9) ∧
    aV al s w cover c (.n 568) = ptrAt (aB c w.children.length 10) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := aAlloc_mems
  exact ⟨(aV_good h0).trans rfl, (aV_good h1).trans rfl, (aV_good h2).trans rfl, (aV_good h3).trans rfl,
    (aV_good h4).trans rfl, (aV_good h5).trans rfl, (aV_good h6).trans rfl, (aV_good h7).trans rfl,
    (aV_good h8).trans rfl, (aV_good h9).trans rfl, (aV_good h10).trans rfl⟩

/-- **A load into a new value** reads the evaluation memory's word, and every memory holding the
runs holds it. -/
theorem aLoad_fresh {d p : V} {off b : ℕ} (hx : Atom.load d p off ∈ atomsOf aggP)
    (hS : Atom.load d p off ∉ storesOf 6 aggP) (hp : aV al s w cover c p = ptrAt b)
    (hi : InW (aAll al s w cover c) (b + off)) (hb : b + off < 2 ^ 64 - 1) :
    aV al s w cover c d = valAt (aAll al s w cover c) (b + off) ∧
      ∀ rd, HoldsWords rd (aAll al s w cover c) →
        LoadHolds rd (aV al s w cover c p) off (aV al s w cover c d) := by
  have hg := aV_good (al := al) (s := s) (w := w) (cover := cover) (c := c) hx
  have e : aV al s w cover c d = valAt (aAll al s w cover c) (b + off) := by
    rcases hg with h | h
    · exact absurd h hS
    · rw [h, rdAt, hp, addr_ptr, aRd0, rdW_inW hi hb]; rfl
  refine ⟨e, fun rd hW => ?_⟩
  rw [hp]
  exact loadHolds_of_rd (by rw [rd_eq_rdW hW hi hb, rdW_inW hi hb, e])

/-! ## The own words -/

theorem aLists_len (s : NodeStatement) (w : NodeWitness) : (aLists s w).length = 11 := rfl

theorem aBufs_len (m : ℕ) : (aBufs m).length = 11 := rfl

/-- **Buffer `j`'s run** of the own words, its length the buffer's. -/
theorem aWo_get (hl : (aLists s w).map List.length = aBufs w.children.length) {j : ℕ} (hj : j < 11) :
    (aB c w.children.length j, (aLists s w).getD j []) ∈ aWo s w c ∧
      ((aLists s w).getD j []).length = (aBufs w.children.length).getD j 0 := by
  have hb : (bases c (aBufs w.children.length)).length = 11 := by rw [length_bases, aBufs_len]
  refine ⟨List.mem_iff_getElem.mpr ⟨j, by simp [aWo, hb, aLists_len, hj], ?_⟩, ?_⟩
  · simp only [aWo, List.getElem_zip, aB]
    rw [List.getD_eq_getElem _ _ (by rw [hb]; exact hj), List.getD_eq_getElem _ _ (by rw [aLists_len]; exact hj)]
  · rw [← hl, List.getD_eq_getElem _ _ (by rw [aLists_len]; exact hj),
      List.getD_eq_getElem _ _ (by rw [List.length_map, aLists_len]; exact hj), List.getElem_map]

/-- **The buffers lie from `c`.** -/
theorem aB_lt {m j o : ℕ} (hj : j < 11) (ho : o < (aBufs m).getD j 0) :
    c ≤ aB c m j ∧ aB c m j + o < c + (aBufs m).sum := by
  have hb : (bases c (aBufs m)).length = 11 := by rw [length_bases, aBufs_len]
  have hm : ((aBufs m).getD j 0, aB c m j) ∈ (aBufs m).zip (bases c (aBufs m)) := by
    refine List.mem_iff_getElem.mpr ⟨j, by simp [hb, aBufs_len, hj], ?_⟩
    simp only [List.getElem_zip, aB]
    rw [List.getD_eq_getElem _ _ (by rw [aBufs_len]; exact hj), List.getD_eq_getElem _ _ (by rw [hb]; exact hj)]
  have := bases_zip hm
  exact ⟨this.1, by omega⟩

/-- **The buffers are the node's own data.** -/
theorem own_aB {cert : String → V → ℕ} {fp m j o : ℕ} {f : String} {es : List Ev} (hj : j < 11)
    (ho : o < (aBufs m).getD j 0) : ownData cert fp c f (aBufs m) es (aB c m j + o) := by
  have hb : (bases c (aBufs m)).length = 11 := by rw [length_bases, aBufs_len]
  refine Or.inl ⟨((aBufs m).getD j 0, aB c m j), ?_, by omega, by omega⟩
  refine List.mem_iff_getElem.mpr ⟨j, by simp [hb, aBufs_len, hj], ?_⟩
  simp only [List.getElem_zip, aB]
  rw [List.getD_eq_getElem _ _ (by rw [aBufs_len]; exact hj), List.getD_eq_getElem _ _ (by rw [hb]; exact hj)]

/-- **The evaluation memory's word in a buffer** is its honest content. -/
theorem valAt_own (hl : (aLists s w).map List.length = aBufs w.children.length) {j o : ℕ} (hj : j < 11)
    (ho : o < (aBufs w.children.length).getD j 0) :
    InW (aAll al s w cover c) (aB c w.children.length j + o) ∧
      valAt (aAll al s w cover c) (aB c w.children.length j + o) = ((aLists s w).getD j []).getD o 0 := by
  obtain ⟨hq, hlen⟩ := aWo_get (c := c) hl hj
  have hin : InW (aWo s w c) (aB c w.children.length j + o) :=
    ⟨_, hq, by dsimp only; omega, by dsimp only; rw [hlen]; omega⟩
  refine ⟨inW_append_left (inW_append_left hin), ?_⟩
  rw [aAll, valAt_append_left (inW_append_left hin), valAt_append_left hin]
  have hd : Disj (aWo s w c) := by
    have := bases_zip_pairwise c (aLists s w)
    rwa [hl] at this
  rw [valAt_of_mem hd hq (by dsimp only; omega) (by dsimp only; rw [hlen]; omega), Nat.add_sub_cancel_left]

end

end
end LeanVM.Guest.Complete.Agg
