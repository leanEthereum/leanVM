/-
  LeanVM.Guest.B1.Digest.Basic

  Shared lemmas of the digest family: straight-line bodies, `pack_pair`'s three cells, the
  padding cells of a whole-cell message, digests as cells.
-/

module

public import LeanVM.Guest.B1.Digest.Interface

/-!
# Digests: shared lemmas

* `holdsList_atoms_ret`: a body of atoms then a `ret` holds exactly when every atom does and the
  returned words are the continuation's.
* `pair_fwd`: `pack_pair(cells, off, s, t)` (G:574-584) as the guest lowers it, 27 atoms: the
  hinted limbs pinned by the three `pack64x2` checks make the three packed cells the six limbs of
  `s` and `t` (`pair_cells`), whose sixteen-byte cells are `eBytes s ++ eBytes t`
  (`pair_bytes`).
* `padCells_getD_lt`, `padCells_getD_last`: the cells a whole-cell message of `16 m` bytes is
  absorbed from are its cells, then the padding cell `0x01 … 0x80` (`padCellWord`).
* `digestOfCells`: canonical cells hold a digest (`digestScalars_ofCells`, `digestBytes_ofCells`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Straight-line bodies -/

theorem holdsList_atoms_ret {C : CallRel} {rd : Reader} {σ : Val} (as : List Atom) (vs : List V)
    (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (as.map Stmt.atom ++ [Stmt.ret vs]) next kret ↔
      (∀ a ∈ as, a.Holds rd σ) ∧ kret (vs.map σ) := by
  induction as with
  | nil => simp [Stmt.HoldsList, Stmt.Holds]
  | cons a as ih =>
    simp only [List.map_cons, List.cons_append, Stmt.HoldsList, Stmt.Holds, List.forall_mem_cons,
      ih, and_assoc]

theorem forall_mem_flatMap_range {α : Type} {n : ℕ} {f : ℕ → List α} {P : α → Prop} :
    (∀ a ∈ (List.range n).flatMap f, P a) ↔ ∀ i < n, ∀ a ∈ f i, P a := by
  simp only [List.mem_flatMap, List.mem_range, forall_exists_index, and_imp]
  exact ⟨fun h i hi a ha => h a i hi ha, fun h a i hi ha => h i hi a ha⟩

/-! ## `pack_pair` -/

/-- `y` and `y⁻¹` as the guest's words. -/
abbrev wY : E := word 0 1
abbrev wYi : E := word 1 0 1

theorem wY_eq : wY = y := by rw [y_eq]; rfl

theorem wYi_eq : wYi = y⁻¹ := by rw [y_inv]; rfl

/-- `pack_pair` of the words `.n b`, `.n (b + 1)`, read through the pointer `ptr` at offsets
`o`, `o + 1`: 27 atoms, its three cells `.n (b + 8)`, `.n (b + 17)`, `.n (b + 26)`. -/
def pairAtoms (ptr : V) (o b : ℕ) : List Atom :=
  let v := fun r => V.n (b + r)
  [.load (v 0) ptr o, .load (v 1) ptr (o + 1),
   .hint (.limbs (v 0) [v 2, v 3]), .hint (.limbs (v 1) [v 4, v 5]),
   .assertInK (v 2) (v 3), .const (v 6) wY, .mul (v 7) (v 6) (v 3),
   .add (v 8) (v 2) (v 7), .add (v 9) (v 0) (v 2), .const (v 10) wYi,
   .mul (v 11) (v 9) (v 10), .add (v 12) (v 11) (v 3), .const (v 13) wYi,
   .mul (v 14) (v 12) (v 13), .assertInK (v 14) (v 4), .const (v 15) wY,
   .mul (v 16) (v 15) (v 4), .add (v 17) (v 14) (v 16),
   .add (v 18) (v 1) (v 4), .const (v 19) wYi, .mul (v 20) (v 18) (v 19),
   .add (v 21) (v 20) (v 5), .const (v 22) wYi, .mul (v 23) (v 21) (v 22),
   .assertInK (v 5) (v 23), .const (v 24) wY, .mul (v 25) (v 24) (v 23),
   .add (v 26) (v 5) (v 25)]

/-- **A deferred pair**: the hinted limbs pinned by the three `pack64x2` checks make the three
packed cells the pair's six limbs. -/
theorem pair_spec {s t s0 s1 t0 t1 : E} (h1 : IsInK s0 ∧ IsInK s1)
    (h2 : IsInK (((s + s0) * wYi + s1) * wYi) ∧ IsInK t0)
    (h3 : IsInK t1 ∧ IsInK (((t + t0) * wYi + t1) * wYi)) :
    s0 = ofK (s.limb 0) ∧ s1 = ofK (s.limb 1) ∧ t0 = ofK (t.limb 0) ∧ t1 = ofK (t.limb 1) := by
  rw [wYi_eq] at h2 h3
  obtain ⟨hs0, hs1⟩ := (split3_iff s s0 s1).mp ⟨h1.1, h1.2, h2.1⟩
  obtain ⟨ht0, ht1⟩ := (split3_iff t t0 t1).mp ⟨h2.2, h3.1, h3.2⟩
  exact ⟨hs0, hs1, ht0, ht1⟩

/-- The three cells of a pair, from its limbs. -/
theorem pair_cells (s t : E) :
    ofK (s.limb 0) + wY * ofK (s.limb 1) = E.ofLimbs (s.limb 0) (s.limb 1) 0 ∧
    ((s + ofK (s.limb 0)) * wYi + ofK (s.limb 1)) * wYi + wY * ofK (t.limb 0) =
      E.ofLimbs (s.limb 2) (t.limb 0) 0 ∧
    ofK (t.limb 1) + wY * (((t + ofK (t.limb 0)) * wYi + ofK (t.limb 1)) * wYi) =
      E.ofLimbs (t.limb 1) (t.limb 2) 0 := by
  rw [wY_eq, wYi_eq, split3_top, split3_top]
  refine ⟨?_, ?_, ?_⟩ <;> rw [pack64x2_eq (ofK_isInK _) (ofK_isInK _)] <;> simp

/-- The three cells of a pair `s, t`. -/
def pairCells (s t : E) : List E :=
  [E.ofLimbs (s.limb 0) (s.limb 1) 0, E.ofLimbs (s.limb 2) (t.limb 0) 0,
    E.ofLimbs (t.limb 1) (t.limb 2) 0]

theorem pair_bytes (s t : E) : cellsBytes (pairCells s t) = E.toBytes s ++ E.toBytes t := by
  simp only [pairCells, cellsBytes, List.flatMap_cons, List.flatMap_nil, cellBytes,
    ofLimbs_limb0, ofLimbs_limb1, E.toBytes, List.append_assoc, List.append_nil]

theorem pairCells_canonical (s t : E) : AllCanonical (pairCells s t) := by
  intro c hc
  simp only [pairCells, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl

/-- **`pack_pair`, forward**: the loads, and the three cells. -/
theorem pair_fwd {rd : Reader} {σ : Val} {ptr : V} {o b : ℕ}
    (h : ∀ a ∈ pairAtoms ptr o b, a.Holds rd σ) :
    LoadHolds rd (σ ptr) o (σ (.n b)) ∧ LoadHolds rd (σ ptr) (o + 1) (σ (.n (b + 1))) ∧
      [σ (.n (b + 8)), σ (.n (b + 17)), σ (.n (b + 26))] =
        pairCells (σ (.n b)) (σ (.n (b + 1))) := by
  simp only [pairAtoms, List.forall_mem_cons, Atom.Holds, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, Nat.add_zero] at h
  obtain ⟨l0, l1, -, -, k1, c6, m7, a8, a9, c10, m11, a12, c13, m14, k2, c15, m16, a17, a18, c19,
    m20, a21, c22, m23, k3, c24, m25, a26⟩ := h
  have e14 : σ (.n (b + 14)) = ((σ (.n b) + σ (.n (b + 2))) * wYi + σ (.n (b + 3))) * wYi := by
    rw [m14, a12, m11, a9, c10, c13]
  have e23 : σ (.n (b + 23)) = ((σ (.n (b + 1)) + σ (.n (b + 4))) * wYi + σ (.n (b + 5))) * wYi := by
    rw [m23, a21, m20, a18, c19, c22]
  rw [e14] at k2
  rw [e23] at k3
  obtain ⟨hs0, hs1, ht0, ht1⟩ := pair_spec k1 k2 k3
  obtain ⟨p1, p2, p3⟩ := pair_cells (σ (.n b)) (σ (.n (b + 1)))
  refine ⟨l0, l1, ?_⟩
  simp only [pairCells, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩
  · rw [a8, m7, c6, hs0, hs1, p1]
  · rw [a17, m16, c15, e14, hs0, hs1, ht0, p2]
  · rw [a26, m25, c24, e23, ht0, ht1, p3]

/-! ## The padding of a whole-cell message -/

/-- The padding cell of a message of whole cells, `len = 16 m` with `16 m ≡ 8 (mod 136)`, … in
general `byteCell len 1 + byteCell (136 B - 1) 0x80` when both bytes fall in cell `m`. -/
theorem padCells_getD_lt (cells : List E) (len : ℕ) {i : ℕ} (hi : i < cells.length)
    (h1 : i ≠ len / 16) (h2 : i ≠ (rate * (len / rate + 1) - 1) / 16) :
    (padCells cells len).getD i 0 = cells.getD i 0 := by
  unfold padCells xorByte
  rw [List.getD_eq_getElem?_getD, List.getElem?_modify, List.getElem?_modify,
    List.getElem?_append_left hi]
  simp [Ne.symm h1, Ne.symm h2, List.getD_eq_getElem?_getD]

/-! ## Digests as cells -/

theorem digestScalars_ofCells {a b : E} (ha : IsCanonical128 a) (hb : IsCanonical128 b) :
    digestHalves #v[(a.limb 0).lane, (a.limb 1).lane, (b.limb 0).lane, (b.limb 1).lane] =
      (a, b) := by
  simp only [digestHalves, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, K.ofLane_lane]
  rw [eq_ofLimbs_of_canonical ha, eq_ofLimbs_of_canonical hb]
  simp

end
end LeanVM.Guest.B1.Digest
