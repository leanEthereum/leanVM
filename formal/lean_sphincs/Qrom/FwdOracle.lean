module

public import Qrom.FwdCell
public import Qrom.Search

@[expose] public section

/-!
# The forward block of the compressed oracle, on reachable databases

For the search event (`Qrom.searchEvent`: some cell holds a good value), with at most `s` good
values per input and `λ = s / N`, the part of the phase oracle that moves a database from outside
the event into it, restricted to databases whose queried cell is reachable (`Qrom.reachQ`, the
projector `cellReach` on the queried cell), has squared norm at most `λ (2 + 4 λ)`
(`Qrom.norm_phFwd_sq_le`). The operator keeps the blocks of the query register and of the other
cells, and its block at `((x, χ), r)` is the one-cell forward block `Qrom.cellFwd χ (good x)`, or
zero when `r` already holds a good value.
-/

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Qrom

open Quantum

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The projector onto the databases whose queried cell is reachable. -/
noncomputable def reachQ (Q : Type) [DecidableEq Q] :
    Matrix ((X × Q) × Database X Y) ((X × Q) × Database X Y) ℂ :=
  of fun m' m ↦ if m'.1 = m.1 ∧ ∀ j ≠ m.1.1, m'.2 j = m.2 j then
    cellReach Y (m'.2 m.1.1) (m.2 m.1.1) else 0

omit [Fintype X] [Fintype Y] [DecidableEq Y] in
theorem update_none_eq_of_agree {D D' : Database X Y} {x : X} (h : ∀ j ≠ x, D' j = D j) :
    Function.update D' x none = Function.update D x none := by
  funext j
  by_cases hj : j = x
  · subst hj
    simp
  · rw [Function.update_of_ne hj, Function.update_of_ne hj, h j hj]

omit [DecidableEq X] [Fintype Y] [DecidableEq Y] in
theorem size_le_card (D : Database X Y) : D.size ≤ Fintype.card X :=
  (Finset.card_filter_le _ _).trans (by simp)

/-- The entries of a product `diag d · A · diag e · B`. -/
theorem diag_mul_mul_diag_mul_apply {n : Type*} [Fintype n] [DecidableEq n] (d e : n → ℂ)
    (A B : Matrix n n ℂ) (i j : n) :
    (diagonal d * A * diagonal e * B) i j = ∑ k, d i * A i k * e k * B k j := by
  rw [mul_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [mul_diagonal, diagonal_mul]

variable [AddCommGroup Y] [Nonempty Y]
variable (good : X → Y → Prop) [∀ z, DecidablePred (good z)]

/-- The forward block of the phase oracle for the search event, on reachable databases. -/
noncomputable def phFwd :
    Matrix ((X × AddChar Y ℂ) × Database X Y) ((X × AddChar Y ℂ) × Database X Y) ℂ :=
  labelProjector (fun m : (X × AddChar Y ℂ) × Database X Y ↦ searchEvent good m.2) true *
    truncatedPhaseOracle X Y (Fintype.card X) *
    labelProjector (fun m : (X × AddChar Y ℂ) × Database X Y ↦ searchEvent good m.2) false *
    reachQ (AddChar Y ℂ)

omit [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Nonempty Y] in
/-- The search event after filling the empty cell `x` of a database outside the event. -/
theorem searchEvent_update {r : Database X Y} {x : X} (hr : r x = none)
    (hno : searchEvent good r = false) (a : Option Y) :
    searchEvent good (Function.update r x a) = decide (∃ y, a = some y ∧ good x y) := by
  simp only [searchEvent, decide_eq_false_iff_not, not_exists, not_and] at hno ⊢
  refine decide_eq_decide.mpr ⟨fun ⟨z, y, hz, hg⟩ ↦ ?_, fun ⟨y, ha, hg⟩ ↦ ⟨x, y, by simp [ha], hg⟩⟩
  by_cases hzx : z = x
  · subst hzx
    rw [Function.update_self] at hz
    exact ⟨y, hz, hg⟩
  · rw [Function.update_of_ne hzx] at hz
    exact absurd hg (hno z y hz)

omit [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Nonempty Y] in
theorem searchEvent_update_true {r : Database X Y} {x : X} (hr : r x = none)
    (hyes : searchEvent good r = true) (a : Option Y) :
    searchEvent good (Function.update r x a) = true := by
  simp only [searchEvent, decide_eq_true_eq] at hyes ⊢
  obtain ⟨z, y, hz, hg⟩ := hyes
  have hzx : z ≠ x := by
    rintro rfl
    rw [hr] at hz
    cases hz
  exact ⟨z, y, by rw [Function.update_of_ne hzx, hz], hg⟩

omit [Nonempty Y] in
/-- The entries of the forward block, as a sum over the queried cell. -/
theorem phFwd_apply (m' m : (X × AddChar Y ℂ) × Database X Y) :
    phFwd good m' m = ∑ k, (if searchEvent good m'.2 = true then 1 else 0) *
      truncatedPhaseOracle X Y (Fintype.card X) m' k *
      (if searchEvent good k.2 = false then 1 else 0) * reachQ (AddChar Y ℂ) k m := by
  rw [phFwd, labelProjector, labelProjector, diag_mul_mul_diag_mul_apply]

omit [Nonempty Y] in
/-- The forward block keeps the blocks of the query register and the other cells. -/
theorem queryBlock_eq_of_phFwd_ne_zero {m' m : (X × AddChar Y ℂ) × Database X Y}
    (h : phFwd good m' m ≠ 0) : queryBlock m' = queryBlock m := by
  rw [phFwd_apply] at h
  obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hT : truncatedPhaseOracle X Y (Fintype.card X) m' k ≠ 0 := fun h0 ↦ hk (by simp [h0])
  have hP : reachQ (AddChar Y ℂ) k m ≠ 0 := fun h0 ↦ hk (by simp [h0])
  have h1 := phaseBlock_eq_of_truncatedPhaseOracle_ne_zero hT
  have h2 : k.1 = m.1 ∧ ∀ j ≠ m.1.1, k.2 j = m.2 j := by
    by_contra hc
    exact hP (by simp [reachQ, hc])
  change (m'.1, Function.update m'.2 m'.1.1 none) = (m.1, Function.update m.2 m.1.1 none)
  rw [h1, h2.1]
  exact congrArg _ (update_none_eq_of_agree h2.2)

/-- **The blocks of the forward block**: the one-cell forward block, or zero when the rest of the
database already holds a good value. -/
theorem phFwd_apply_update (x : X) (χ : AddChar Y ℂ) {r : Database X Y} (hr : r x = none)
    (a' a : Option Y) :
    phFwd good ((x, χ), Function.update r x a') ((x, χ), Function.update r x a) =
      if searchEvent good r = true then 0 else cellFwd χ (good x) a' a := by
  rw [phFwd_apply]
  -- the sum runs over the block
  have hblk : ∀ k : (X × AddChar Y ℂ) × Database X Y,
      (if searchEvent good (Function.update r x a') = true then (1 : ℂ) else 0) *
        truncatedPhaseOracle X Y (Fintype.card X) ((x, χ), Function.update r x a') k *
        (if searchEvent good k.2 = false then 1 else 0) *
          reachQ (AddChar Y ℂ) k ((x, χ), Function.update r x a) =
      if (k.1, Function.update k.2 k.1.1 none) = ((x, χ), r) then
        (if searchEvent good (Function.update r x a') = true then (1 : ℂ) else 0) *
          truncatedPhaseOracle X Y (Fintype.card X) ((x, χ), Function.update r x a') k *
          (if searchEvent good k.2 = false then 1 else 0) *
            reachQ (AddChar Y ℂ) k ((x, χ), Function.update r x a) else 0 := by
    intro k
    by_cases hk : (k.1, Function.update k.2 k.1.1 none) = ((x, χ), r)
    · rw [ite_eq_left hk]
    · rw [ite_eq_right hk]
      by_cases hT : truncatedPhaseOracle X Y (Fintype.card X) ((x, χ), Function.update r x a') k = 0
      · simp [hT]
      · exfalso
        have h1 := phaseBlock_eq_of_truncatedPhaseOracle_ne_zero hT
        simp only [Function.update_idem, Database.update_none_of_eq_none hr] at h1
        exact hk h1.symm
  rw [Finset.sum_congr rfl fun k _ ↦ hblk k, sum_ite_phaseBlock x χ hr]
  have hsz : ∀ b : Option Y, Database.size (Function.update r x b) ≤ Fintype.card X :=
    fun b ↦ size_le_card _
  have hreach : ∀ b, reachQ (AddChar Y ℂ) ((x, χ), Function.update r x b)
      ((x, χ), Function.update r x a) = cellReach Y b a := by
    intro b
    have hc : ((x, χ) : X × AddChar Y ℂ) = (x, χ) ∧
        ∀ j ≠ x, Function.update r x b j = Function.update r x a j :=
      ⟨rfl, fun j hj ↦ by rw [Function.update_of_ne hj, Function.update_of_ne hj]⟩
    simp only [reachQ, of_apply, true_and]
    rw [ite_eq_left hc.2, Function.update_self, Function.update_self]
  simp only [truncatedPhaseOracle_apply_update, hsz, ↓reduceIte, one_mul, mul_one, hreach]
  by_cases hyes : searchEvent good r = true
  · rw [ite_eq_left hyes]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    rw [searchEvent_update_true good hr hyes b]
    simp
  · rw [ite_eq_right hyes]
    have hno : searchEvent good r = false := by simpa using hyes
    rw [cellFwd, diag_mul_mul_diag_mul_apply]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    have hgi : ∀ c : Option Y, (if searchEvent good (Function.update r x c) = true then (1 : ℂ)
        else 0) = goodInd (good x) c := by
      intro c
      rw [searchEvent_update good hr hno]
      rcases c with _ | c
      · simp [goodInd]
      · by_cases h : good x c <;> simp [goodInd, h]
    have hgi' : ∀ c : Option Y, (if searchEvent good (Function.update r x c) = false then (1 : ℂ)
        else 0) = (1 - goodInd (good x)) c := by
      intro c
      rw [Pi.sub_apply, Pi.one_apply, ← hgi]
      cases searchEvent good (Function.update r x c) <;> simp
    rw [hgi a', hgi' b]

/-- **The forward block of the phase oracle, on reachable databases.** -/
theorem norm_phFwd_sq_le (s : ℕ) (hs : ∀ z, (Finset.univ.filter (good z)).card ≤ s) :
    ‖phFwd good‖ ^ 2 ≤ (s / Fintype.card Y : ℝ) * (2 + 4 * (s / Fintype.card Y)) := by
  have hc : 0 ≤ (s / Fintype.card Y : ℝ) * (2 + 4 * (s / Fintype.card Y)) := by positivity
  have h : ‖phFwd good‖ ≤ √((s / Fintype.card Y : ℝ) * (2 + 4 * (s / Fintype.card Y))) := by
    refine l2_opNorm_le_of_queryBlock (fun m' m h ↦ queryBlock_eq_of_phFwd_ne_zero good h)
      (Real.sqrt_nonneg _) ?_
    rintro ⟨x, χ⟩ r hr
    have he : (of fun a' a : Option Y ↦ phFwd good ((x, χ), Function.update r x a')
        ((x, χ), Function.update r x a)) =
        if searchEvent good r = true then 0 else cellFwd χ (good x) := by
      ext a' a
      rw [of_apply, phFwd_apply_update good x χ hr]
      split_ifs <;> rfl
    rw [he]
    split_ifs
    · rw [norm_zero]
      exact Real.sqrt_nonneg _
    · exact Real.le_sqrt_of_sq_le (norm_cellFwd_sq_le χ (good x) s (hs x))
  calc ‖phFwd good‖ ^ 2 ≤ √((s / Fintype.card Y : ℝ) * (2 + 4 * (s / Fintype.card Y))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt hc

end Qrom
