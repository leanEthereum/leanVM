import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.HiddenLabelProbe
import SphincsSecurity.Proof.Residual.RetainedObservation
namespace SphincsSecurity.Concrete.HiddenLabelObservation

open _root_.OracleComp OracleSpec ENNReal UniformTableCompletion RetainedObservation
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]

omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem response_failure (labels : Coordinate → Digest) (probe : Probe Coordinate) :
    (response labels probe).toPMF none =
      Pr[fun answer => ¬probe.keep labels answer | PMF.uniformOfFintype HashOutput] := by
  rw [response, toPMF_bind_lift, PMF.bind_apply, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro answer
  by_cases h : probe.keep labels answer
  · simp only [h, if_true, not_true_eq_false, if_false, SPMF.toPMF_pure, PMF.pure_apply,
      reduceCtorEq, mul_zero]
  · simp only [h, if_false, not_false_eq_true, if_true, SPMF.toPMF_failure, PMF.pure_apply,
      mul_one, PMF.probOutput_eq_apply]

theorem lazyResponse_pair_failure (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child parent : Coordinate) (hne : child ≠ parent)
    (candidate : Digest) :
    (lazyResponse allowed (.pair child parent hne candidate)).toPMF none =
      Pr[HiddenLabelProbe.Match child parent candidate | HiddenLabelProbe.law allowed ha] := by
  rw [lazyResponse, complete_of_nonempty allowed ha, toPMF_bind_lift, PMF.bind_apply]
  change _ = Pr[HiddenLabelProbe.Match child parent candidate |
    (uniformTable allowed ha) >>= fun labels => (fun answer => (labels, answer)) <$> PMF.uniformOfFintype HashOutput]
  rw [probEvent_bind_eq_tsum]
  simp only [PMF.probOutput_eq_apply, probEvent_map]
  apply tsum_congr
  intro labels
  apply congrArg (uniformTable allowed ha labels * ·)
  rw [response_failure]
  apply congrArg (fun event => Pr[event | PMF.uniformOfFintype HashOutput])
  funext answer
  apply propext
  simp only [Probe.keep, HiddenLabelProbe.Match, Function.comp_def, not_and_or, not_not, eq_comm]

theorem lazyResponse_pair_failure_le_rounds (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child parent : Coordinate) (hne : child ≠ parent)
    (candidate : Digest) (rounds : Nat) (hmin : 2 ^ digestBits - rounds ≤ (allowed child).card) :
    (lazyResponse allowed (.pair child parent hne candidate)).toPMF none ≤
      1 - (1 - ((2 ^ digestBits - rounds : Nat) : ENNReal)⁻¹) ^ 2 := by
  rw [lazyResponse_pair_failure allowed ha child parent hne candidate]
  exact HiddenLabelProbe.prob_match_le_rounds allowed ha child parent candidate rounds hmin

omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem response_output_failure (labels : Coordinate → Digest) (parent : Coordinate) :
    (response labels (.output parent)).toPMF none = (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [response_failure]
  simpa only [Probe.keep, not_not, eq_comm] using HiddenLabelProbe.prob_truncate_eq (labels parent)

theorem lazyResponse_output_failure (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (parent : Coordinate) :
    (lazyResponse allowed (.output parent)).toPMF none = (Fintype.card Digest : ENNReal)⁻¹ := by
  simp only [lazyResponse, complete_of_nonempty allowed ha, toPMF_bind_lift, PMF.bind_apply,
    response_output_failure, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end SphincsSecurity.Concrete.HiddenLabelObservation

namespace SphincsSecurity.Concrete.AdaptiveHiddenLabels

open _root_.OracleComp OracleSpec ENNReal HiddenLabelObservation

end SphincsSecurity.Concrete.AdaptiveHiddenLabels
