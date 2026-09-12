import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Base.UniformTableCompletion
import SphincsSecurity.Statement

namespace SphincsSecurity.Concrete.HiddenLabelObservation

open _root_.OracleComp ENNReal UniformTableCompletion
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

inductive Probe (Coordinate : Type) where
  | pair (child parent : Coordinate) (distinct : child ≠ parent) (candidate : Digest)
  | output (parent : Coordinate)

variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]

def Probe.keep (probe : Probe Coordinate) (labels : Coordinate → Digest) (answer : HashOutput) : Prop :=
  match probe with
  | .pair child parent _ candidate => labels child ≠ candidate ∧ labels parent ≠ truncateHash answer
  | .output parent => labels parent ≠ truncateHash answer

def Probe.restrict (probe : Probe Coordinate) (allowed : Coordinate → Finset Digest)
    (answer : HashOutput) : Coordinate → Finset Digest :=
  match probe with
  | .pair child parent _ candidate => pairedMissAllowed allowed child candidate parent (truncateHash answer)
  | .output parent => eraseTableValue allowed parent (truncateHash answer)

omit [Fintype Coordinate] in
theorem Probe.card_lower (probe : Probe Coordinate) (allowed : Coordinate → Finset Digest)
    (answer : HashOutput) (coordinate : Coordinate) :
    (allowed coordinate).card - 1 ≤ (probe.restrict allowed answer coordinate).card := by
  cases probe with
  | pair child parent distinct candidate =>
      exact pairedMissAllowed_card_lower allowed child parent distinct candidate (truncateHash answer) coordinate
  | output parent =>
      by_cases heq : coordinate = parent
      · subst coordinate
        simpa only [Probe.restrict, eraseTableValue, Function.update_self] using
          (Finset.pred_card_le_card_erase (s := allowed parent) (a := truncateHash answer))
      · simpa only [Probe.restrict, eraseTableValue, Function.update_of_ne heq] using Nat.sub_le (allowed coordinate).card 1

theorem Probe.mass (probe : Probe Coordinate) (allowed : Coordinate → Finset Digest)
    (answer : HashOutput) (labels : Coordinate → Digest) :
    (if probe.keep labels answer then complete allowed labels else 0) =
      restrictionWeight allowed (probe.restrict allowed answer) * complete (probe.restrict allowed answer) labels := by
  cases probe with
  | pair child parent distinct candidate =>
      have h := paired_mass allowed child parent distinct candidate (truncateHash answer) labels
      by_cases hk : labels child ≠ candidate ∧ labels parent ≠ truncateHash answer
      · simpa only [Probe.keep, Probe.restrict, if_pos hk] using h
      · simpa only [Probe.keep, Probe.restrict, if_neg hk] using h
  | output parent =>
      have h := single_mass allowed parent (truncateHash answer) labels
      by_cases hk : labels parent ≠ truncateHash answer
      · simpa only [Probe.keep, Probe.restrict, if_pos hk] using h
      · simpa only [Probe.keep, Probe.restrict, if_neg hk] using h

noncomputable def response (labels : Coordinate → Digest) (probe : Probe Coordinate) : SPMF HashOutput := do
  let answer ← (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)
  if probe.keep labels answer then pure answer else failure

omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem response_apply (labels : Coordinate → Digest) (probe : Probe Coordinate) (answer : HashOutput) :
    response labels probe answer = if probe.keep labels answer then PMF.uniformOfFintype HashOutput answer else 0 := by
  rw [response, SPMF.bind_apply_eq_tsum]
  rw [tsum_eq_single answer]
  · by_cases h : probe.keep labels answer <;> simp only [h, if_true, if_false, SPMF.liftM_apply,
      SPMF.pure_apply_self, SPMF.failure_apply, mul_one, mul_zero]
  · intro other hother
    by_cases h : probe.keep labels other <;> simp only [h, if_true, if_false, SPMF.pure_apply,
      if_neg (Ne.symm hother), SPMF.failure_apply, mul_zero]

noncomputable def lazyResponse (allowed : Coordinate → Finset Digest) (probe : Probe Coordinate) : SPMF HashOutput :=
  complete allowed >>= fun labels => response labels probe

theorem lazyResponse_apply (allowed : Coordinate → Finset Digest) (probe : Probe Coordinate) (answer : HashOutput) :
    lazyResponse allowed probe answer = PMF.uniformOfFintype HashOutput answer *
      restrictionWeight allowed (probe.restrict allowed answer) := by
  rw [lazyResponse, SPMF.bind_apply_eq_tsum]
  simp only [response_apply, mul_ite, mul_zero]
  calc
    _ = PMF.uniformOfFintype HashOutput answer *
        ∑' labels, restrictionWeight allowed (probe.restrict allowed answer) *
          complete (probe.restrict allowed answer) labels := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro labels
      rw [← Probe.mass]
      split <;> simp only [mul_comm, zero_mul]
    _ = _ := by rw [ENNReal.tsum_mul_left, weight_tsum_complete]

theorem posterior_mass (allowed : Coordinate → Finset Digest) (probe : Probe Coordinate)
    (answer : HashOutput) (labels : Coordinate → Digest) :
    lazyResponse allowed probe answer * complete (probe.restrict allowed answer) labels =
      complete allowed labels * response labels probe answer := by
  rw [lazyResponse_apply, mul_assoc, ← Probe.mass, response_apply]
  split <;> simp only [mul_comm, zero_mul]

theorem lazyResponse_nonempty (allowed : Coordinate → Finset Digest) (probe : Probe Coordinate)
    (answer : HashOutput) (h : lazyResponse allowed probe answer ≠ 0) :
    ∀ coordinate, (probe.restrict allowed answer coordinate).Nonempty := by
  by_contra hnonempty
  rw [lazyResponse_apply, weight_of_empty _ _ hnonempty, mul_zero] at h
  exact h rfl

end SphincsSecurity.Concrete.HiddenLabelObservation
