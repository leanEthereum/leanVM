import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Base.UniformTableCompletion
namespace SphincsSecurity.Concrete.UniformPublicCoordinates

open _root_.OracleComp ENNReal UniformTableCompletion
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {Coordinate Value : Type} [Fintype Coordinate] [DecidableEq Coordinate]
  [Fintype Value] [DecidableEq Value] [Nonempty Value]

abbrev Public (exposed : Coordinate → Prop) := {coordinate // exposed coordinate}

def restrict (exposed : Coordinate → Prop) (labels : Coordinate → Value) : Public exposed → Value :=
  fun coordinate => labels coordinate.val

noncomputable def allowed (exposed : Coordinate → Prop) (known : Public exposed → Value) : Coordinate → Finset Value :=
  fun coordinate => if h : exposed coordinate then {known ⟨coordinate, h⟩} else Finset.univ

omit [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value] in
theorem allowed_nonempty (exposed : Coordinate → Prop) (known : Public exposed → Value) :
    ∀ coordinate, (allowed exposed known coordinate).Nonempty := by
  intro coordinate
  unfold allowed
  split
  · exact Finset.singleton_nonempty _
  · exact Finset.univ_nonempty

omit [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value] [Nonempty Value] in
theorem mem_allowed_iff (exposed : Coordinate → Prop) (known : Public exposed → Value)
    (labels : Coordinate → Value) :
    (∀ coordinate, labels coordinate ∈ allowed exposed known coordinate) ↔ restrict exposed labels = known := by
  constructor
  · intro h
    funext coordinate
    change labels coordinate.val = known coordinate
    have hc := h coordinate.val
    simpa only [allowed, dif_pos coordinate.property, Finset.mem_singleton] using hc
  · intro h coordinate
    by_cases hc : exposed coordinate
    · simp only [allowed, dif_pos hc, Finset.mem_singleton]
      exact congrFun h ⟨coordinate, hc⟩
    · simp only [allowed, dif_neg hc, Finset.mem_univ]

omit [DecidableEq Value] [Nonempty Value] in
theorem allowed_card_product (exposed : Coordinate → Prop) (known : Public exposed → Value) :
    Fintype.card (Public exposed → Value) * (∏ coordinate, (allowed exposed known coordinate).card) =
      Fintype.card (Coordinate → Value) := by
  have hcard : ∀ coordinate, (allowed exposed known coordinate).card =
      if exposed coordinate then 1 else Fintype.card Value := by
    intro coordinate
    by_cases hc : exposed coordinate <;> simp [allowed, hc]
  simp only [hcard, Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const,
    Fintype.card_fun, ← pow_add]
  congr 1
  simp only [Public, Fintype.card_subtype]
  exact Finset.card_filter_add_card_filter_not _

theorem completion_mass (exposed : Coordinate → Prop) (known : Public exposed → Value)
    (labels : Coordinate → Value) :
    PMF.uniformOfFintype (Public exposed → Value) known * complete (allowed exposed known) labels =
      if restrict exposed labels = known then PMF.uniformOfFintype (Coordinate → Value) labels else 0 := by
  simp only [complete_apply, mem_allowed_iff]
  by_cases h : restrict exposed labels = known
  · simp only [h, if_true, PMF.uniformOfFintype_apply]
    rw [← ENNReal.mul_inv (by simp) (by simp), ← Nat.cast_mul, allowed_card_product]
  · simp only [h, if_false, mul_zero]

omit [Fintype Value] [Nonempty Value] in
theorem completion_member (candidates : Coordinate → Finset Value) (labels : Coordinate → Value)
    (hlabels : complete candidates labels ≠ 0) : ∀ coordinate, labels coordinate ∈ candidates coordinate := by
  by_contra h
  rw [complete_apply, if_neg h] at hlabels
  exact hlabels rfl

theorem uniform_bind_complete {Result : Type} (exposed : Coordinate → Prop)
    (next : (Public exposed → Value) → (Coordinate → Value) → SPMF Result) :
    ((liftM (PMF.uniformOfFintype (Coordinate → Value)) : SPMF _) >>= fun labels => next (restrict exposed labels) labels) =
      ((liftM (PMF.uniformOfFintype (Public exposed → Value)) : SPMF _) >>= fun known =>
        complete (allowed exposed known) >>= next known) := by
  classical
  apply SPMF.ext
  intro result
  simp only [SPMF.bind_apply_eq_tsum, SPMF.liftM_apply, ← ENNReal.tsum_mul_left,
    ← mul_assoc, completion_mass, ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  simp

end SphincsSecurity.Concrete.UniformPublicCoordinates
