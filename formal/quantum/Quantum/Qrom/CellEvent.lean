module

public import Quantum.Qrom.Embed
public import Quantum.Xmss.FlipCost

@[expose] public section

/-!
# Cell targets of the random oracle

In the QROM a database is a partial function `D → Option Y`, and the hash of `x` in a state of
the hardwired register is the union view `unionH s x` (the hardwired value, else the database
content). `CellTargetBad tgt` holds when some recorded or hardwired cell `x` has its value in
`tgt W m x`, for the hardwired cells `W` and the memory `m`. It is the event of the graded event
bound (`eventWeight_spongeHardwiredRuntime_le`) at `(X, Z) := (Y, D)`:

* every slice is upward closed (`upClosed_slice_cellTargetBad`);
* the start is outside when no hardwired cell has its value in its target
  (`not_mem_cellTargetBad_start`);
* a fresh `h` cell enters with probability at most the largest target fraction of the
  non-hardwired cells, a fresh `k`, `k'` cell never (`freshBound_slice_cellTargetBad`).

Classical ports, per cell:

* **program**: hardwiring `z` to `v` flips nothing if `v` is outside the new target of `z` and the
  other targets do not grow (`not_mem_cellTargetBad_programH`, so
  `flipCost_programH_cellTargetBad_eq_zero`); in general at most the number of values in their
  own target flip (`card_flip_programH_cellTargetBad_le`);
* **read**: reading a cell without a target, with memory updates that add targets only of the form
  `out y = out v` on cells satisfying `P`, flips at most `cellCount P * F` values `v`, `F` a bound
  on the fibers of `out` (`card_flip_readH_cellTargetBad_le`); filling a cell keeps the event when
  the targets only grow (`mem_cellTargetBad_fill`).
-/

open Matrix
open scoped ENNReal ComplexOrder

namespace Quantum.Qrom

open Quantum Quantum.Sponge

variable {D Y M : Type} [Fintype D] [DecidableEq D] [Fintype Y] [DecidableEq Y]

/-- **Cell targets**: some recorded or hardwired cell `x` has its value in `tgt W m x`, for the
hardwired cells `W` and the memory `m` of the state. -/
def CellTargetBad (tgt : Hw Y D → M → D → Set Y) : Set (RomReg D Y M) :=
  {s | ∃ x y, unionH s x = some y ∧ y ∈ tgt s.2.1 s.2.2 x}

/-- Membership in the cell-target event, decided classically. -/
noncomputable instance instDecidablePredCellTargetBad (tgt : Hw Y D → M → D → Set Y) :
    DecidablePred (· ∈ CellTargetBad tgt) :=
  fun _ ↦ Classical.propDecidable _

variable {tgt : Hw Y D → M → D → Set Y}

omit [Fintype D] [DecidableEq D] [Fintype Y] [DecidableEq Y] in
theorem mem_cellTargetBad_iff {s : RomReg D Y M} :
    s ∈ CellTargetBad tgt ↔ ∃ x y, unionH s x = some y ∧ y ∈ tgt s.2.1 s.2.2 x :=
  Iff.rfl

omit [Fintype D] [Fintype Y] [DecidableEq Y] in
/-- A state outside the event whose `h` database changes at `z` only enters the event at `z`. -/
theorem exists_of_mem_cellTargetBad_updateH {s : RomReg D Y M} (hs : s ∉ CellTargetBad tgt)
    {z : D} {o : Option Y} {m' : M}
    (hm : ∀ x, x ≠ z → ∀ y ∈ tgt s.2.1 m' x, y ∈ tgt s.2.1 s.2.2 x)
    (h : ((Function.update s.1.1 z o, s.1.2), s.2.1, m') ∈ CellTargetBad tgt) :
    ∃ y, (s.2.1.1 z).or o = some y ∧ y ∈ tgt s.2.1 m' z := by
  obtain ⟨x, y, hxy, hy⟩ := h
  by_cases hx : x = z
  · subst hx
    simp only [unionH, Function.update_self] at hxy
    exact ⟨y, hxy, hy⟩
  · simp only [unionH, Function.update_of_ne hx] at hxy
    exact absurd ⟨x, y, hxy, hm x hx y hy⟩ hs

/-! ## The graded-bound hypotheses -/

omit [Fintype D] [Fintype Y] in
/-- **Every slice of the event is upward closed.** -/
theorem upClosed_slice_cellTargetBad (W : Hw Y D) (m : M) :
    UpClosed (slice (CellTargetBad tgt) W m) where
  h Db hDb z u hz := by
    obtain ⟨x, y, hxy, hy⟩ := hDb
    refine ⟨x, y, ?_, hy⟩
    by_cases hx : x = z
    · subst hx
      change (W.1 x).or (Function.update Db.h x (some u) x) = some y
      change (W.1 x).or (Db.h x) = some y at hxy
      rw [hz] at hxy
      rw [Function.update_self]
      cases hw : W.1 x with
      | none => simp [hw] at hxy
      | some w => simpa [hw] using hxy
    · change (W.1 x).or (Function.update Db.h z (some u) x) = some y
      rw [Function.update_of_ne hx]
      exact hxy
  k Db hDb _ _ _ := hDb
  k' Db hDb _ _ _ := hDb

omit [Fintype D] [DecidableEq D] [Fintype Y] [DecidableEq Y] in
/-- **The start is outside the event** when no hardwired cell has its value in its target. -/
theorem not_mem_cellTargetBad_start (W₀ : Hw Y D) (m₀ : M)
    (h : ∀ x y, W₀.1 x = some y → y ∉ tgt W₀ m₀ x) :
    (((Database.empty, Database.empty, Database.empty), W₀, m₀) : RomReg D Y M) ∉
      CellTargetBad tgt := by
  rintro ⟨x, y, hxy, hy⟩
  refine h x y ?_ hy
  change (W₀.1 x).or none = some y at hxy
  simpa using hxy

open scoped Classical in
/-- **The fresh bound of every slice**: filling a fresh `h` cell `z` enters the event for the
values in the target of `z` only, and only if `z` is not hardwired; `k`, `k'` cells never. -/
theorem freshBound_slice_cellTargetBad [DecidablePred (· ∈ CellTargetBad tgt)] (W : Hw Y D)
    (m : M) {ε : ℝ≥0∞}
    (hε : ∀ x, W.1 x = none →
      ((Finset.univ.filter fun y ↦ y ∈ tgt W m x).card : ℝ≥0∞) / Fintype.card Y ≤ ε)
    (t : ℕ) : FreshBound (slice (CellTargetBad tgt) W m) t ε where
  h Db hDb _ _ _ z hz := by
    have hs : (((Db.h, Db.k, Db.k'), W, m) : RomReg D Y M) ∉ CellTargetBad tgt := hDb
    cases hw : W.1 z with
    | some w =>
      rw [Finset.filter_false_of_mem fun u _ hu ↦ ?_]
      · simp
      obtain ⟨y, hy, hyt⟩ := exists_of_mem_cellTargetBad_updateH (o := some u) hs
        (fun _ _ _ h ↦ h) hu
      change (W.1 z).or (some u) = some y at hy
      rw [hw] at hy
      refine hs ⟨z, y, ?_, hyt⟩
      change (W.1 z).or (Db.h z) = some y
      rw [hw]
      exact hy
    | none =>
      refine le_trans (ENNReal.div_le_div_right (Nat.cast_le.2
        (Finset.card_le_card fun u hu ↦ ?_)) _) (hε z hw)
      obtain ⟨y, hy, hyt⟩ := exists_of_mem_cellTargetBad_updateH (o := some u) hs
        (fun _ _ _ h ↦ h) (Finset.mem_filter.1 hu).2
      change (W.1 z).or (some u) = some y at hy
      rw [hw] at hy
      cases hy
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hyt⟩
  k Db hDb _ _ _ x _ := by
    have h0 : (Finset.univ.filter fun u : D ↦
        ({ Db with k := Function.update Db.k x (some u) } : Dbs Y D) ∈
          slice (CellTargetBad tgt) W m) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun _ _ hu ↦ hDb hu
    rw [h0]
    simp
  k' Db hDb _ _ _ x _ := by
    have h0 : (Finset.univ.filter fun u : D ↦
        ({ Db with k' := Function.update Db.k' x (some u) } : Dbs Y D) ∈
          slice (CellTargetBad tgt) W m) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun _ _ hu ↦ hDb hu
    rw [h0]
    simp

/-! ## Program ports -/

omit [Fintype D] [Fintype Y] in
/-- **Programming a cell flips nothing** if the programmed value is outside the new target of the
cell and the targets of the other cells do not grow. -/
theorem not_mem_cellTargetBad_programH {s : RomReg D Y M} (hs : s ∉ CellTargetBad tgt) (z : D)
    (v : Y)
    (htgt : ∀ x, x ≠ z → ∀ y ∈ tgt (Function.update s.2.1.1 z (some v), s.2.1.2) s.2.2 x,
      y ∈ tgt s.2.1 s.2.2 x)
    (hv : v ∉ tgt (Function.update s.2.1.1 z (some v), s.2.1.2) s.2.2 z) :
    progMap (.programH z v) s ∉ CellTargetBad tgt := by
  rintro ⟨x, y, hxy, hy⟩
  by_cases hx : x = z
  · subst hx
    change (Function.update s.2.1.1 x (some v) x).or (Function.update s.1.1 x none x) = some y
      at hxy
    rw [Function.update_self] at hxy
    cases hxy
    exact hv hy
  · change (Function.update s.2.1.1 z (some v) x).or (Function.update s.1.1 z none x) = some y
      at hxy
    rw [Function.update_of_ne hx, Function.update_of_ne hx] at hxy
    exact hs ⟨x, y, hxy, htgt x hx y hy⟩

omit [Fintype D] in
open scoped Classical in
/-- **The flip count of programming a cell**: if the targets of the other cells do not grow, at
most the values in their own target of the programmed cell flip a state outside the event. -/
theorem card_flip_programH_cellTargetBad_le {s : RomReg D Y M} (hs : s ∉ CellTargetBad tgt)
    (z : D)
    (htgt : ∀ v x, x ≠ z → ∀ y ∈ tgt (Function.update s.2.1.1 z (some v), s.2.1.2) s.2.2 x,
      y ∈ tgt s.2.1 s.2.2 x) :
    (Finset.univ.filter fun v : Y ↦ progMap (.programH z v) s ∈ CellTargetBad tgt).card ≤
      (Finset.univ.filter fun v : Y ↦
        v ∈ tgt (Function.update s.2.1.1 z (some v), s.2.1.2) s.2.2 z).card := by
  refine Finset.card_le_card fun v hv ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
  by_contra hn
  exact not_mem_cellTargetBad_programH hs z v (htgt v) hn (Finset.mem_filter.1 hv).2

variable [Fintype M] [DecidableEq M]

/-- **Programming cost zero**: a program of cell `z` with `v` costs nothing on states whose
support, outside the event, has `v` outside the new target of `z` and no growing targets
elsewhere. -/
theorem flipCost_programH_cellTargetBad_eq_zero [DecidablePred (· ∈ CellTargetBad tgt)] (z : D)
    (v : Y) {σ : Matrix (Unit × RomReg D Y M) (Unit × RomReg D Y M) ℂ} (hσ : σ.PosSemidef)
    (h : ∀ q : Unit × RomReg D Y M, σ q q ≠ 0 → q.2 ∉ CellTargetBad tgt →
      (∀ x, x ≠ z → ∀ y ∈ tgt (Function.update q.2.2.1.1 z (some v), q.2.2.1.2) q.2.2.2 x,
        y ∈ tgt q.2.2.1 q.2.2.2 x) ∧
      v ∉ tgt (Function.update q.2.2.1.1 z (some v), q.2.2.1.2) q.2.2.2 z) :
    flipCost (CellTargetBad tgt) (hwProgKraus (.programH z v)) 0 σ = 0 := by
  refine le_antisymm ((flipCost_prog_le (CellTargetBad tgt) (.programH z v) hσ).trans ?_)
    (by simp)
  rw [Finset.sum_eq_zero fun q _ ↦ ?_, ENNReal.ofReal_zero]
  by_cases hq : σ q q = 0
  · simp [hq]
  · refine ite_eq_right fun hf ↦ absurd hf.2 ?_
    obtain ⟨h₁, h₂⟩ := h q hq hf.1
    exact not_mem_cellTargetBad_programH hf.1 z v h₁ h₂

/-! ## Read ports -/

omit [Fintype D] [Fintype Y] [DecidableEq Y] [Fintype M] [DecidableEq M] in
/-- **Filling a cell keeps the event** when the targets only grow (for the memory after the
read). -/
theorem mem_cellTargetBad_fill {s : RomReg D Y M} (hs : s ∈ CellTargetBad tgt) {z : D}
    (hz : s.1.1 z = none) (u : Option Y) (m' : M)
    (hmono : ∀ x, ∀ y ∈ tgt s.2.1 s.2.2 x, y ∈ tgt s.2.1 m' x) :
    ((Function.update s.1.1 z u, s.1.2), s.2.1, m') ∈ CellTargetBad tgt := by
  obtain ⟨x, y, hxy, hy⟩ := hs
  refine ⟨x, y, ?_, hmono x y hy⟩
  change (s.2.1.1 x).or (Function.update s.1.1 z u x) = some y
  change (s.2.1.1 x).or (s.1.1 x) = some y at hxy
  by_cases hx : x = z
  · subst hx
    rw [hz] at hxy
    cases hw : s.2.1.1 x with
    | none => simp [hw] at hxy
    | some w => simpa [hw] using hxy
  · rw [Function.update_of_ne hx]
    exact hxy

omit [Fintype D] [Fintype Y] [DecidableEq Y] [Fintype M] [DecidableEq M] in
/-- **A read of a cell without a target flips nothing** when the memory after the read adds no
targets: whatever the read leaves in the cell, the state stays outside the event. -/
theorem not_mem_cellTargetBad_readH {s : RomReg D Y M} (hs : s ∉ CellTargetBad tgt) {z : D}
    (m' : M) (hz : tgt s.2.1 m' z = ∅)
    (hext : ∀ x, x ≠ z → ∀ y ∈ tgt s.2.1 m' x, y ∈ tgt s.2.1 s.2.2 x) (u : Option Y) :
    ((Function.update s.1.1 z u, s.1.2), s.2.1, m') ∉ CellTargetBad tgt := by
  intro h
  obtain ⟨y, -, hy⟩ := exists_of_mem_cellTargetBad_updateH hs hext h
  rw [hz] at hy
  exact hy

open scoped Classical in
/-- The recorded or hardwired cells of a union view satisfying `P`. -/
noncomputable def cellCount (U : D → Option Y) (P : D → Prop) : ℕ :=
  (Finset.univ.filter fun x ↦ P x ∧ (U x).isSome).card

omit [DecidableEq D] [Fintype Y] [DecidableEq Y] [Fintype M] [DecidableEq M] in
theorem cellCount_le_card (U : D → Option Y) (P : D → Prop) : cellCount U P ≤ Fintype.card D := by
  classical
  exact Finset.card_le_univ _

omit [Fintype M] [DecidableEq M] in
open scoped Classical in
/-- **The flip count of a read**: reading a cell `z` that has no target after the read, with
memory `m' v` after reading the value `v`, whose new targets on other cells
are the values `y` with `out y = out v` on cells satisfying `P`. Then at most `cellCount P * F`
values `v` flip a state outside the event, whatever the read leaves in the cell; `F` bounds the
fibers of `out`. -/
theorem card_flip_readH_cellTargetBad_le {O : Type} [DecidableEq O] (out : Y → O) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ out y = o).card ≤ F) {s : RomReg D Y M}
    (hs : s ∉ CellTargetBad tgt) {z : D} (P : D → Prop) (m' : Y → M)
    (hz : ∀ v, tgt s.2.1 (m' v) z = ∅)
    (hext : ∀ v x, x ≠ z → ∀ y ∈ tgt s.2.1 (m' v) x,
      y ∈ tgt s.2.1 s.2.2 x ∨ (P x ∧ out y = out v)) :
    (Finset.univ.filter fun v : Y ↦ ∃ u : Option Y,
      ((Function.update s.1.1 z u, s.1.2), s.2.1, m' v) ∈ CellTargetBad tgt).card ≤
        cellCount (unionH s) P * F := by
  let C := Finset.univ.filter fun x ↦ P x ∧ (unionH s x).isSome
  let S : D → Finset Y := fun x ↦ Finset.univ.filter fun v ↦
    ∃ y, unionH s x = some y ∧ out v = out y
  have hsub : (Finset.univ.filter fun v : Y ↦ ∃ u : Option Y,
      ((Function.update s.1.1 z u, s.1.2), s.2.1, m' v) ∈ CellTargetBad tgt) ⊆ C.biUnion S := by
    intro v hv
    obtain ⟨u, x, y, hxy, hy⟩ := (Finset.mem_filter.1 hv).2
    by_cases hx : x = z
    · subst hx
      rw [hz v] at hy
      exact absurd hy (Set.notMem_empty y)
    · change (s.2.1.1 x).or (Function.update s.1.1 z u x) = some y at hxy
      rw [Function.update_of_ne hx] at hxy
      rcases hext v x hx y hy with hy' | ⟨hP, ho⟩
      · exact absurd ⟨x, y, hxy, hy'⟩ hs
      · exact Finset.mem_biUnion.2 ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, hP,
          by rw [unionH, hxy]; rfl⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, y, hxy, ho.symm⟩⟩
  have hS : ∀ x ∈ C, (S x).card ≤ F := by
    intro x _
    rcases hx : unionH s x with _ | y₀
    · have h0 : S x = ∅ := Finset.filter_eq_empty_iff.mpr fun v _ ⟨y, hy, _⟩ ↦ by
        rw [hx] at hy
        cases hy
      rw [h0, Finset.card_empty]
      exact Nat.zero_le F
    · refine le_trans (Finset.card_le_card fun v hv ↦ ?_) (hF (out y₀))
      obtain ⟨y, hy, hv'⟩ := (Finset.mem_filter.1 hv).2
      rw [hx] at hy
      cases hy
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hv'⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le_card_mul C S _ hS)

end Quantum.Qrom

end
