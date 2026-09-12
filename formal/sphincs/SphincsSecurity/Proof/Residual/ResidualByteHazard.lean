import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.AdaptiveHiddenHazard
import SphincsSecurity.Proof.Ots.PrefixEncodingRisk
import SphincsSecurity.Proof.Residual.ResidualByteCandidates
namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting HiddenLabelObservation ResidualByteAction
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def probeHazard (probes : Nat) : ENNReal :=
  1 - (1 - ((2 ^ digestBits - probes : Nat) : ENNReal)⁻¹) ^ 2

theorem digest_inverse_le_probeHazard (probes : Nat) :
    (Fintype.card Digest : ENNReal)⁻¹ ≤ probeHazard probes := by
  have hcard : Fintype.card Digest = 2 ^ digestBits := card_bitVec digestBits
  have hone : (Fintype.card Digest : ENNReal)⁻¹ ≤ 1 := by
    rw [hcard]
    norm_num [digestBits]
  have hinv : (Fintype.card Digest : ENNReal)⁻¹ ≤ ((2 ^ digestBits - probes : Nat) : ENNReal)⁻¹ := by
    apply ENNReal.inv_le_inv.mpr
    exact_mod_cast (show 2 ^ digestBits - probes ≤ Fintype.card Digest by rw [hcard]; exact Nat.sub_le _ _)
  have hsquare : (1 - ((2 ^ digestBits - probes : Nat) : ENNReal)⁻¹) ^ 2 ≤
      1 - (Fintype.card Digest : ENNReal)⁻¹ := by
    rw [pow_two]
    calc
      _ ≤ 1 * (1 - ((2 ^ digestBits - probes : Nat) : ENNReal)⁻¹) :=
        mul_le_mul' tsub_le_self le_rfl
      _ ≤ _ := by rw [one_mul]; exact tsub_le_tsub_left hinv _
  apply ENNReal.le_sub_of_add_le_right (ne_top_of_le_ne_top (by simp) (hsquare.trans tsub_le_self))
  calc
    _ ≤ (Fintype.card Digest : ENNReal)⁻¹ + (1 - (Fintype.card Digest : ENNReal)⁻¹) := add_le_add le_rfl hsquare
    _ = 1 := add_tsub_cancel_of_le hone

theorem prob_stopped_observe {Answer Memory : Type} (response : SPMF Answer)
    (stopped : Memory) (next : Answer → Memory) :
    Pr[fun result => result.1 = none |
      RetainedObservation.observe response (pure (none, stopped)) (fun answer => pure (some answer, next answer))] =
      response.toPMF none := by
  rw [RetainedObservation.observe, probEvent_bind_eq_tsum]
  rw [tsum_option _ ENNReal.summable]
  simp only [probEvent_pure, if_true, reduceCtorEq, if_false,
    mul_one, mul_zero, tsum_zero, add_zero, SPMF.probOutput_liftM, PMF.probOutput_eq_apply]

variable (parameter : PublicParameter) (inputs : Finset HashInput) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (actions : inputs → Action inputs)

theorem prob_lazyRun_execute_probe_stop (input : inputs) (test : Probe CanonicalCoordinate) (state : State inputs)
    (hrow : state.rows input = none) :
    Pr[fun result => result.1 = none |
      lazyRun (environment parameter inputs words disclosed known actions) (execute (.probe input test)) state] =
      (lazyResponse state.candidates test).toPMF none := by
  simp only [lazyRun, execute, runWith, simulateQ_spec_query, lazyImpl, OptionT.run_mk, StateT.run_mk, hrow]
  exact prob_stopped_observe _ _ _

attribute [local irreducible] lazyResponse probeHazard

theorem prob_hashQuery_stop_le (input : inputs) (state : State inputs) (bound : ENNReal)
    (hcovered : RowsCovered inputs state) (hlocal : Local input (actions input))
    (hprobe : ∀ row test, actions input = .probe row test → (lazyResponse state.candidates test).toPMF none ≤ bound) :
    Pr[fun result => result.1 = none |
      lazyRun (environment parameter inputs words disclosed known actions) (hashQuery input) state] ≤ bound := by
  rw [hashQuery, lazyRun_prepare_bind]
  cases hcache : state.memory.cache input.val with
  | some answer =>
      rw [prepare_cached parameter inputs words disclosed known actions input state.memory answer hcache, lazyRun_execute_known]
      simp only [probEvent_pure, reduceCtorEq, if_false, zero_le]
  | none =>
      have hrow := rowsCovered_fresh inputs state hcovered input hcache
      cases haction : actions input with
      | known answer =>
          simp only [prepare, hcache, haction]
          rw [lazyRun_execute_known]
          simp only [probEvent_pure, reduceCtorEq, if_false, zero_le]
      | read row =>
          simp only [prepare, hcache, haction]
          rw [lazyRun_execute_read]
          simp only [probEvent_map, Function.comp_def, reduceCtorEq, probEvent_False, zero_le]
      | probe row test =>
          have heq : row = input := by simpa only [haction, Local] using hlocal
          subst row
          simp only [prepare, hcache, haction]
          let paid : State inputs := { state with memory := charge parameter words disclosed known input.val state.memory }
          have hpaid : paid.candidates = state.candidates := rfl
          have hstop := prob_lazyRun_execute_probe_stop parameter inputs words disclosed known actions input test paid hrow
          rw [hpaid] at hstop
          exact hstop.le.trans (hprobe input test haction)

omit actions in
theorem prob_prefixHashQuery_stop_le (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (input : inputs) (state : State inputs) (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : RowsCovered inputs state) (hbound : HiddenCandidateBound words disclosed state) :
    Pr[fun result => result.1 = none |
      lazyRun (prefixEnvironment parameter inputs hencoding words disclosed known publicReplies selections rows)
        (hashQuery input) state] ≤ probeHazard state.memory.probes := by
  refine prob_hashQuery_stop_le parameter inputs words disclosed known
    (freshPrefix parameter inputs hencoding words disclosed known publicReplies selections rows) input state
    (probeHazard state.memory.probes) hcovered
    (freshPrefix_local parameter inputs hencoding words disclosed known publicReplies selections rows input) ?_
  intro row test haction
  have hroute := freshPrefix_probe_route parameter inputs hencoding words disclosed known publicReplies selections rows
    input row test haction
  cases test with
  | output parent =>
      rw [lazyResponse_output_failure _ ha parent]
      exact digest_inverse_le_probeHazard _
  | pair child parent hne candidate =>
      have hspec := route_spec parameter words disclosed known known (fun _ _ => rfl) input.val
      rw [hroute] at hspec
      obtain ⟨_, _, _, _, hhidden, _⟩ := hspec
      have hmin : 2 ^ digestBits - state.memory.probes ≤ (state.candidates child).card := by
        have h := hbound child hhidden
        omega
      unfold probeHazard
      exact lazyResponse_pair_failure_le_rounds state.candidates ha child parent hne candidate state.memory.probes hmin

end SphincsSecurity.Concrete.ResidualByteFrontend
