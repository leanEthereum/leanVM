import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.HiddenLabelObservation
namespace SphincsSecurity.Concrete.RetainedObservation

open _root_.OracleComp ENNReal
set_option backward.isDefEq.respectTransparency false

variable {Label Answer Result : Type}

theorem bind_comm (p : SPMF Label) (q : SPMF Answer) (next : Label → Answer → SPMF Result) :
    (p >>= fun label => q >>= next label) = (q >>= fun answer => p >>= fun label => next label answer) := by
  apply SPMF.ext
  intro result
  simp only [SPMF.bind_apply_eq_tsum, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro answer
  apply tsum_congr
  intro label
  exact mul_left_comm _ _ _

theorem bind_congr (p : SPMF Label) (f g : Label → SPMF Result)
    (h : ∀ label, p label ≠ 0 → f label = g label) : (p >>= f) = (p >>= g) := by
  apply SPMF.ext
  intro result
  simp only [SPMF.bind_apply_eq_tsum]
  apply tsum_congr
  intro label
  by_cases hp : p label = 0
  · simp only [hp, zero_mul]
  · rw [h label hp]

theorem bind_nonzero (p : SPMF Label) (next : Label → SPMF Result) (result : Result) :
    (p >>= next) result ≠ 0 ↔ ∃ label, p label ≠ 0 ∧ next label result ≠ 0 := by
  rw [← SPMF.mem_support_iff, SPMF.support_bind]
  simp only [Set.mem_iUnion, SPMF.mem_support_iff, exists_prop]

theorem lift_bind_const (p : PMF Label) (next : SPMF Result) :
    ((liftM p : SPMF Label) >>= fun _ => next) = next := by
  apply SPMF.ext
  intro result
  simp only [SPMF.bind_apply_eq_tsum, SPMF.liftM_apply, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem toPMF_bind_lift (p : PMF Label) (next : Label → SPMF Answer) :
    ((liftM p : SPMF Label) >>= next).toPMF = p.bind (fun label => (next label).toPMF) := by
  rw [SPMF.toPMF_bind, SPMF.liftM_eq_map, SPMF.toPMF_mk]
  simp only [Option.elimM, PMF.monad_bind_eq_bind, PMF.bind_map]
  rfl

noncomputable def observe (response : SPMF Answer) (stopped : SPMF Result)
    (next : Answer → SPMF Result) : SPMF Result :=
  (liftM response.toPMF : SPMF (Option Answer)) >>= fun
    | none => stopped
    | some answer => next answer

theorem observe_apply (response : SPMF Answer) (stopped : SPMF Result)
    (next : Answer → SPMF Result) (result : Result) :
    observe response stopped next result = response.toPMF none * stopped result +
      ∑' answer, response answer * next answer result := by
  rw [observe, SPMF.bind_apply_eq_tsum]
  simp only [SPMF.liftM_apply]
  rw [tsum_option _ ENNReal.summable]
  rfl

theorem observe_nonzero (response : SPMF Answer) (stopped : SPMF Result)
    (next : Answer → SPMF Result) (result : Result) :
    observe response stopped next result ≠ 0 ↔
      (response.toPMF none ≠ 0 ∧ stopped result ≠ 0) ∨
        ∃ answer, response answer ≠ 0 ∧ next answer result ≠ 0 := by
  rw [observe, bind_nonzero]
  constructor
  · rintro ⟨answer, hanswer, hresult⟩
    cases answer with
    | none => exact Or.inl ⟨by simpa only [SPMF.liftM_apply] using hanswer, hresult⟩
    | some answer =>
        refine Or.inr ⟨answer, ?_, hresult⟩
        rw [SPMF.apply_eq_toPMF_some response answer]
        simpa only [SPMF.liftM_apply] using hanswer
  · rintro (⟨hanswer, hresult⟩ | ⟨answer, hanswer, hresult⟩)
    · exact ⟨none, by simpa only [SPMF.liftM_apply] using hanswer, hresult⟩
    · refine ⟨some answer, ?_, hresult⟩
      rw [SPMF.liftM_apply, ← SPMF.apply_eq_toPMF_some response answer]
      exact hanswer

theorem observe_bind {Other : Type} (response : SPMF Answer) (stopped : SPMF Result)
    (next : Answer → SPMF Result) (after : Result → SPMF Other) :
    (observe response stopped next >>= after) =
      observe response (stopped >>= after) (fun answer => next answer >>= after) := by
  simp only [observe, bind_assoc]
  congr 1
  funext answer
  cases answer <;> rfl

theorem observe_congr (response : SPMF Answer) (stopped : SPMF Result)
    (f g : Answer → SPMF Result) (h : ∀ answer, response answer ≠ 0 → f answer = g answer) :
    observe response stopped f = observe response stopped g := by
  apply SPMF.ext
  intro result
  simp only [observe_apply]
  apply congrArg (response.toPMF none * stopped result + ·)
  apply tsum_congr
  intro answer
  by_cases hp : response answer = 0
  · simp only [hp, zero_mul]
  · rw [h answer hp]

theorem posterior_observe (prior : PMF Label) (response : Label → SPMF Answer)
    (predictive : SPMF Answer) (posterior : Answer → SPMF Label)
    (hpredictive : predictive = ((liftM prior : SPMF Label) >>= response))
    (hmass : ∀ answer label, predictive answer * posterior answer label = prior label * response label answer)
    (stopped : SPMF Result) (next : Answer → Label → SPMF Result) :
    ((liftM prior : SPMF Label) >>= fun label => observe (response label) stopped (fun answer => next answer label)) =
      observe predictive stopped (fun answer => posterior answer >>= next answer) := by
  have hnone : (∑' label, prior label * (response label).toPMF none) = predictive.toPMF none := by
    rw [hpredictive, toPMF_bind_lift, PMF.bind_apply]
  apply SPMF.ext
  intro result
  simp only [SPMF.bind_apply_eq_tsum, SPMF.liftM_apply, observe_apply, mul_add, ENNReal.tsum_add]
  apply congrArg₂ (· + ·)
  · simpa only [← mul_assoc, ENNReal.tsum_mul_right] using congrArg (· * stopped result) hnone
  · simp only [← ENNReal.tsum_mul_left, ← mul_assoc, hmass]
    rw [ENNReal.tsum_comm]

end SphincsSecurity.Concrete.RetainedObservation

namespace SphincsSecurity.Concrete.HiddenLabelObservation

open _root_.OracleComp UniformTableCompletion RetainedObservation

theorem bind_response_stopped {Coordinate Result : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (allowed : Coordinate → Finset Digest) (ha : ∀ coordinate, (allowed coordinate).Nonempty)
    (probe : Probe Coordinate) (stopped : SPMF Result) (next : HashOutput → (Coordinate → Digest) → SPMF Result) :
    (complete allowed >>= fun labels => observe (response labels probe) stopped (fun answer => next answer labels)) =
      observe (lazyResponse allowed probe) stopped (fun answer => complete (probe.restrict allowed answer) >>= next answer) := by
  have h := posterior_observe (uniformTable allowed ha) (fun labels => response labels probe)
    (lazyResponse allowed probe) (fun answer => complete (probe.restrict allowed answer))
    (by rw [lazyResponse, complete_of_nonempty allowed ha])
    (fun answer labels => by
      simpa only [complete_of_nonempty allowed ha, SPMF.liftM_apply] using posterior_mass allowed probe answer labels)
    stopped next
  simpa only [complete_of_nonempty allowed ha] using h

end SphincsSecurity.Concrete.HiddenLabelObservation
