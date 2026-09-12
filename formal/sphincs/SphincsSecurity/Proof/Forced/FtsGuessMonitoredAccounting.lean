import SphincsSecurity.Proof.Forced.FtsGuessProposalCompleted
import SphincsSecurity.Proof.Residual.RetainedResidualMessagePayment
import SphincsSecurity.Proof.Residual.RetainedResidualWorkCost
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec UniformTableCompletion OtsContactTrace ENNReal
open FtsGuessSigning (Coordinate)
open FtsProbeSimulation (MessageHashInput messageAnswers)
open SecretGuessObservation (State)
open RetainedResidual (proposalOfSigningRecord proposalOfWorldResult digestWork digestWork_messageCalls)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  publicDigestLoop canonicalGraphRoot canonicalGraphInput hashInputs UniformTableCompletion.complete signDigestLoop

variable (parameter : PublicParameter) (root : Digest)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
  (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
  (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords) (slot : Nat)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

/-! ### Trace bookkeeping -/

theorem SigningBoundaryTrace.hashCalls_one : SigningBoundaryTrace.hashCalls (1 : SigningBoundaryTrace) = 0 := rfl

theorem SigningBoundaryTrace.hashCalls_of (entry : Option (HashInput × HashOutput)) :
    SigningBoundaryTrace.hashCalls (FreeMonoid.of entry : SigningBoundaryTrace) = 1 := rfl

theorem digestWork_hashCalls_ge (known : CanonicalProbeRouting.Labels) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (selected : Option (Randomness × Index × (IndexGroup → FtsLeaf)) × SigningBoundaryTrace) :
    selected.2.hashCalls ≤ (digestWork known words selections selected).1.2.hashCalls := by
  rcases selected with ⟨selected, trace⟩
  cases selected with
  | none => exact le_rfl
  | some selected =>
      simp only [digestWork, SigningBoundaryTrace.hashCalls_mul]
      exact Nat.le_add_right _ _

theorem romImpl_hash_cached (input : HashInput) (cache : QueryCache HashSpec) (result : HashOutput × QueryCache HashSpec)
    (hr : 𝒟[(romImpl (.inr input)).run cache] result ≠ 0) : result.2 input = some result.1 := by
  have hmem : result ∈ support ((romImpl (.inr input)).run cache) := (mem_support_iff_evalDist_apply_ne_zero _ _).mpr hr
  change result ∈ support ((randomOracle input).run cache) at hmem
  cases hc : cache input with
  | some output =>
      rw [randomOracle, QueryImpl.withCaching_run_some _ hc, mem_support_pure_iff] at hmem
      subst result
      exact hc
  | none =>
      rw [randomOracle, QueryImpl.withCaching_run_none _ hc, support_map] at hmem
      obtain ⟨output, _, rfl⟩ := hmem
      exact QueryCache.cacheQuery_self cache input output

/-! ### The signing law through the boundary run -/

theorem publicSigningWork_boundary_support (known : CanonicalProbeRouting.Labels) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (message : Message) (cache : QueryCache HashSpec) (result : PublicSigningRecord × QueryCache HashSpec)
    (hr : 𝒟[(simulateQ romImpl (Prod.fst <$> ResidualByteFrontend.publicSigningWork parameter root known words selections message)).run cache]
      result ≠ 0) :
    ∃ boundary ∈ support (boundaryRun parameter (publicDigestLoop parameter root message digestAttemptLimit) cache),
      result = ((digestWork known words selections boundary.1).1, boundary.2) := by
  have hmem := (mem_support_iff_evalDist_apply_ne_zero _ _).mpr hr
  rw [RetainedResidual.publicSigningWork_eq_digestWork, Functor.map_map, simulateQ_map, StateT.run_map, support_map] at hmem
  obtain ⟨boundary, hboundary, rfl⟩ := hmem
  refine ⟨boundary, ?_, rfl⟩
  rw [simulateQ_boundaryComputation] at hboundary
  exact hboundary

theorem publicSigningWork_hashCalls_min' (key : SecretKey) (hparameter : key.parameter = parameter) (hroot : key.root = root)
    (known : CanonicalProbeRouting.Labels) (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message)
    (cache : QueryCache HashSpec) (result : PublicSigningRecord × QueryCache HashSpec)
    (hr : 𝒟[(simulateQ romImpl (Prod.fst <$> ResidualByteFrontend.publicSigningWork parameter root known words selections message)).run cache]
      result ≠ 0) : 28504 ≤ result.1.2.hashCalls := by
  subst hparameter hroot
  have hmem := (mem_support_iff_evalDist_apply_ne_zero _ _).mpr hr
  rw [simulateQ_map, StateT.run_map, support_map] at hmem
  obtain ⟨full, hfull, rfl⟩ := hmem
  exact RetainedResidual.publicSigningWork_hashCalls_min key known words selections message cache full hfull

theorem forcedSigning_source (message : Message) (state : MonitoredState) (hvalid : Valid state)
    (hinputs : hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs)
    (result : ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × CachedState)
    (hresult : forcedSigning parameter root otsSecret labels inputs hencoding selections rows dummy slot message state result ≠ 0) :
    ∃ raw : PublicSigningRecord × QueryCache HashSpec,
      𝒟[(simulateQ romImpl (Prod.fst <$> ResidualByteFrontend.publicSigningWork parameter root (known otsSecret labels)
        (referenceFamilyWords selections dummy) selections message)).run state.1.1] raw ≠ 0 ∧
      result.1.2 = raw.1.2 ∧ result.2.1 = raw.2 := by
  rw [forcedSigning, cachedForcedRun_signingProgram' parameter root otsSecret labels inputs hencoding selections rows dummy slot message state.1
    hvalid hinputs (referenceAnswers parameter root otsSecret labels inputs hencoding ⟨selections, rows, fun _ => 0⟩ dummy),
    RetainedObservation.bind_nonzero] at hresult
  obtain ⟨secrets, _, hresult⟩ := hresult
  obtain ⟨raw, hraw, rfl⟩ := map_nonzero_source' _ _ _ hresult
  exact ⟨raw, hraw, completePublicSigningRecord_trace _ raw.1, rfl⟩

/-! ### Accounting along a run -/

structure RunAccount (state : MonitoredState) (trace : SigningBoundaryTrace) (entries : QueryLog SigningSpec) (result : MonitoredState) :
    Prop where
  cache_le : state.1.1 ≤ result.1.1
  rows : ∀ row ∈ trace.messageCalls, result.1.1 row.1 = some row.2
  enncard : QueryCache.enncard result.1.1 ≤ QueryCache.enncard state.1.1 + trace.hashCalls
  mass : result.2.creationMass ≤ state.2.creationMass + trace.hashCalls
  alive : result.2.stopped = false → state.2.stopped = false
  spent : result.2.stopped = false → result.2.spent = state.2.spent + trace.hashCalls
  log : result.2.stopped = false → result.2.log = state.2.log ++ entries
  digests : ∀ reference, SigningDigestsCached parameter state.1.1 root reference →
    SigningDigestsCached parameter result.1.1 root (reference ++ entries)
  bank : (state.2.stopped = false → CertificateBankComplete (monitorKey parameter root) required (monitorView state)) →
    result.2.stopped = false → CertificateBankComplete (monitorKey parameter root) required (monitorView result)

theorem RunAccount.refl (state : MonitoredState) : RunAccount parameter root required state 1 [] state where
  cache_le := le_rfl
  rows := fun _ hrow => by cases hrow
  enncard := by rw [SigningBoundaryTrace.hashCalls_one, Nat.cast_zero, add_zero]
  mass := by rw [SigningBoundaryTrace.hashCalls_one, Nat.cast_zero, add_zero]
  alive := id
  spent := fun _ => by rw [SigningBoundaryTrace.hashCalls_one, Nat.add_zero]
  log := fun _ => by rw [List.append_nil]
  digests := fun reference h => by rw [List.append_nil]; exact h
  bank := fun h halive => h halive

theorem RunAccount.trans {first middle last : MonitoredState} {trace tail : SigningBoundaryTrace} {log more : QueryLog SigningSpec}
    (hfirst : RunAccount parameter root required first trace log middle) (hlast : RunAccount parameter root required middle tail more last) :
    RunAccount parameter root required first (trace * tail) (log ++ more) last where
  cache_le := hfirst.cache_le.trans hlast.cache_le
  rows := by
    intro row hrow
    rw [SigningBoundaryTrace.messageCalls_mul, List.mem_append] at hrow
    rcases hrow with hrow | hrow
    · exact hlast.cache_le (hfirst.rows row hrow)
    · exact hlast.rows row hrow
  enncard := by
    rw [SigningBoundaryTrace.hashCalls_mul, Nat.cast_add, ← add_assoc]
    exact hlast.enncard.trans (add_le_add hfirst.enncard le_rfl)
  mass := by
    rw [SigningBoundaryTrace.hashCalls_mul, Nat.cast_add, ← add_assoc]
    exact hlast.mass.trans (add_le_add hfirst.mass le_rfl)
  alive := fun halive => hfirst.alive (hlast.alive halive)
  spent := fun halive => by
    rw [hlast.spent halive, hfirst.spent (hlast.alive halive), SigningBoundaryTrace.hashCalls_mul, Nat.add_assoc]
  log := fun halive => by
    rw [hlast.log halive, hfirst.log (hlast.alive halive), List.append_assoc]
  digests := fun reference h => by
    rw [← List.append_assoc]
    exact hlast.digests _ (hfirst.digests reference h)
  bank := fun h halive => hlast.bank (hfirst.bank h) halive

private theorem update_active_of_alive (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) (length : Nat)
    (record : ProposalExecutionRecord input)
    (halive : (certificateMonitorUpdate (monitorKey parameter root) budget required stopAfter input state length record).stopped = false) :
    CertificateMonitorActive (monitorKey parameter root) budget input state := by
  by_contra h
  rw [certificateMonitorUpdate_inactive (monitorKey parameter root) budget required stopAfter input state length record h] at halive
  contradiction

private theorem update_alive (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) (length : Nat)
    (record : ProposalExecutionRecord input)
    (halive : (certificateMonitorUpdate (monitorKey parameter root) budget required stopAfter input state length record).stopped = false) :
    state.2.stopped = false :=
  (update_active_of_alive parameter root budget required stopAfter input state length record halive).1

private theorem update_mass_le (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) (length : Nat)
    (record : ProposalExecutionRecord input) (bound : ENNReal)
    (hbound : targetCreationMultiplier (monitorKey parameter root) state.1 input ≤ bound) :
    (certificateMonitorUpdate (monitorKey parameter root) budget required stopAfter input state length record).creationMass ≤
      state.2.creationMass + bound := by
  rw [certificateMonitorUpdate_creationMass]
  apply add_le_add le_rfl
  by_cases hactive : CertificateMonitorActive (monitorKey parameter root) budget input state
  · rw [certificateMonitorMass, if_pos hactive]
    exact hbound
  · rw [certificateMonitorMass, if_neg hactive]
    exact zero_le

theorem worldStep_account (input : OracleWorld.Domain) (state : MonitoredState) (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs)
    (raw : OracleWorld.Range input × CachedState)
    (hraw : cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (worldProgram parameter labels input)
      state.1 raw ≠ 0) :
    RunAccount parameter root required state (signingBoundaryTrace parameter input raw.1) []
      (raw.2, certificateMonitorUpdate (monitorKey parameter root) budget required stopAfter (.inl input) (monitorView state) 0
        (proposalOfWorldResult parameter input (raw.1, raw.2.1))) := by
  have hcache := worldStep_cache_le parameter root otsSecret labels inputs hencoding selections rows dummy slot input state hinputs raw hraw
  have hmass : targetCreationMultiplier (monitorKey parameter root) state.1.1 (.inl input) ≤
      ((signingBoundaryTrace parameter input raw.1).hashCalls : ENNReal) := by
    rw [signingBoundaryTrace_hashCalls_eq, targetCreationMultiplier]
    cases input with
    | inl sample => exact le_rfl
    | inr hash =>
        simp only [freshWorldTargetHashCost]
        split_ifs <;> norm_num
  refine ⟨hcache.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro row hrow
    cases input with
    | inl sample => cases hrow
    | inr hash =>
        by_cases hmessage : MessageHashInput parameter hash
        · have hlaw := hraw
          rw [cachedForcedRun_world_message' parameter root otsSecret labels inputs hencoding selections rows dummy slot hash
            (hinputs (by simpa only [bind_pure] using mem_hashInputs_hash_bind hash pure)) hmessage state.1] at hlaw
          obtain ⟨source, hsource, heq⟩ := map_nonzero_source' _ _ _ hlaw
          have hcached := romImpl_hash_cached hash state.1.1 source hsource
          simp only [signingBoundaryTrace, if_pos hmessage] at hrow
          change row ∈ [(hash, raw.1)] at hrow
          obtain rfl := List.mem_singleton.mp hrow
          rw [heq]
          exact hcached
        · simp [signingBoundaryTrace, SigningBoundaryTrace.messageCalls, hmessage] at hrow
  · cases input with
    | inl sample =>
        rw [cachedForcedRun_world_unif'] at hraw
        obtain ⟨answer, _, rfl⟩ := map_nonzero_source' _ _ _ hraw
        simp only [signingBoundaryTrace, SigningBoundaryTrace.hashCalls_one, Nat.cast_zero, add_zero]
        exact le_rfl
    | inr hash =>
        simp only [signingBoundaryTrace, SigningBoundaryTrace.hashCalls_of, Nat.cast_one]
        exact (cachedForcedRun_world_hash_support' parameter root otsSecret labels inputs hencoding selections rows dummy slot hash state.1 raw
          hraw).2.2
  · exact update_mass_le parameter root budget required stopAfter (.inl input) (monitorView state) 0 _ _ hmass
  · exact update_alive parameter root budget required stopAfter (.inl input) (monitorView state) 0 _
  · intro halive
    rw [certificateMonitorUpdate_spent (monitorKey parameter root) budget required stopAfter (.inl input) (monitorView state) 0 _
      (update_active_of_alive parameter root budget required stopAfter (.inl input) (monitorView state) 0 _ halive)]
    rfl
  · intro halive
    rw [certificateMonitorUpdate, if_pos (update_active_of_alive parameter root budget required stopAfter (.inl input) (monitorView state) 0 _
      halive)]
    rfl
  · intro reference hreference
    rw [List.append_nil]
    exact worldStep_digestsCached parameter root otsSecret labels inputs hencoding selections rows dummy slot input state hinputs reference
      hreference raw hraw
  · intro _ halive
    exact certificateMonitorUpdate_bank_complete (monitorKey parameter root) budget required stopAfter (.inl input) (monitorView state) 0 _ halive

theorem signStep_account (message : Message) (state : MonitoredState) (hvalid : Valid state)
    (hinputs : hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs) (annotation : Nat × Index)
    (raw : ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × CachedState)
    (hraw : forcedSigning parameter root otsSecret labels inputs hencoding selections rows dummy slot message state raw ≠ 0) :
    RunAccount parameter root required state raw.1.2 [⟨message, raw.1.1.1⟩]
      (raw.2, certificateMonitorUpdate (monitorKey parameter root) budget required stopAfter (.inr message) (monitorView state) annotation.1
        (proposalOfSigningRecord message raw.1 raw.2.1 (raw.1.1.2.elim annotation.2 Prod.fst))) := by
  obtain ⟨source, hsource, htrace, hcache⟩ := forcedSigning_source parameter root otsSecret labels inputs hencoding selections rows dummy slot
    message state hvalid hinputs raw hraw
  obtain ⟨boundary, hboundary, hsplit⟩ := publicSigningWork_boundary_support parameter root (known otsSecret labels)
    (referenceFamilyWords selections dummy) selections message state.1.1 source hsource
  have hmin := publicSigningWork_hashCalls_min' parameter root (monitorKey parameter root) rfl rfl (known otsSecret labels)
    (referenceFamilyWords selections dummy) selections message state.1.1 source hsource
  have hcalls : boundary.1.2.hashCalls ≤ raw.1.2.hashCalls := by
    rw [htrace, hsplit]
    exact digestWork_hashCalls_ge _ _ _ boundary.1
  have hrows : raw.1.2.messageCalls = boundary.1.2.messageCalls := by
    rw [htrace, hsplit]
    exact digestWork_messageCalls _ _ _ boundary.1
  have hcachesplit : raw.2.1 = boundary.2 := by rw [hcache, hsplit]
  have hmass : targetCreationMultiplier (monitorKey parameter root) state.1.1 (.inr message) ≤ (raw.1.2.hashCalls : ENNReal) := by
    have hp := mul_le_mul' (le_refl (((2 ^ ftsTreeHeight : Nat) : ENNReal)))
      (freshDigestSelectionProbability_le_one (monitorKey parameter root) message state.1.1)
    calc
      _ ≤ ((2 ^ ftsTreeHeight : Nat) : ENNReal) := by simpa only [targetCreationMultiplier, mul_one] using hp
      _ ≤ (28504 : Nat) := by norm_num [ftsTreeHeight]
      _ ≤ _ := by
        rw [htrace]
        exact Nat.cast_le.mpr hmin
  refine ⟨forcedSigning_cache_le parameter root otsSecret labels inputs hencoding selections rows dummy slot message state hvalid hinputs raw hraw,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro row hrow
    rw [hrows] at hrow
    change raw.2.1 row.1 = some row.2
    rw [hcachesplit]
    exact boundaryRun_message_cached parameter _ state.1.1 boundary hboundary row hrow
  · change QueryCache.enncard raw.2.1 ≤ _
    rw [hcachesplit]
    exact (boundaryRun_enncard_le parameter _ state.1.1 boundary hboundary).trans (add_le_add le_rfl (Nat.cast_le.mpr hcalls))
  · exact update_mass_le parameter root budget required stopAfter (.inr message) (monitorView state) annotation.1 _ _ hmass
  · exact update_alive parameter root budget required stopAfter (.inr message) (monitorView state) annotation.1 _
  · intro halive
    rw [certificateMonitorUpdate_spent (monitorKey parameter root) budget required stopAfter (.inr message) (monitorView state) annotation.1 _
      (update_active_of_alive parameter root budget required stopAfter (.inr message) (monitorView state) annotation.1 _ halive)]
    rfl
  · intro halive
    rw [certificateMonitorUpdate, if_pos (update_active_of_alive parameter root budget required stopAfter (.inr message) (monitorView state)
      annotation.1 _ halive)]
    rfl
  · intro reference hreference
    exact forcedSigning_digestsCached parameter root otsSecret labels inputs hencoding selections rows dummy slot message state hvalid hinputs
      reference hreference raw hraw
  · intro _ halive
    exact certificateMonitorUpdate_bank_complete (monitorKey parameter root) budget required stopAfter (.inr message) (monitorView state)
      annotation.1 _ halive

theorem monitoredStep_account (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState) (hvalid : Valid state)
    (hworld : ∀ world, input = .inl world → hashInputs (liftM (OracleWorld.query world)) ⊆ inputs)
    (hsign : ∀ message, input = .inr message → hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs)
    (result : AdversaryStep input × MonitoredState)
    (hresult : monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      input state result ≠ 0) :
    RunAccount parameter root required state result.1.1.2 (signingLogFragment input result.1.1.1) result.2 := by
  cases input with
  | inl input =>
      rw [monitoredStep, monitoredWorldStep] at hresult
      obtain ⟨raw, hraw, rfl⟩ := map_nonzero_source' _ _ _ hresult
      exact worldStep_account parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state
        (hworld input rfl) raw hraw
  | inr message =>
      rw [monitoredStep, monitoredSignStep_eq, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨annotation, _, hresult⟩ := hresult
      obtain ⟨raw, hraw, rfl⟩ := map_nonzero_source' _ _ _ hresult
      exact signStep_account parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter message state
        hvalid (hsign message rfl) annotation raw hraw

variable (hauxiliary : ∀ seed : inputs → HashOutput,
  (⟨selections, rows, seed⟩ : ReferenceAuxiliary inputs) ∈ (referenceAuxiliarySample inputs).support)

include hauxiliary in
theorem monitoredRun_account (computation : OracleComp (OracleWorld + SigningSpec) Forgery) (state : MonitoredState) (hvalid : Valid state)
    (hcovered : CoveredRun parameter root otsSecret inputs computation state) (result : AdversaryTrace × MonitoredState)
    (hresult : monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      computation state result ≠ 0) :
    RunAccount parameter root required state result.1.1.2 result.1.1.1.2 result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [monitoredRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact RunAccount.refl parameter root required state
  | query_bind input next ih =>
      rw [monitoredRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨step, hstep, hresult⟩ := hresult
      obtain ⟨tail, htail, rfl⟩ := map_nonzero_source' _ _ _ hresult
      have hfirst := monitoredStep_account parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        input state hvalid
        (fun world heq => by subst heq; exact covered_world_inputs parameter root otsSecret inputs world next state hvalid hcovered)
        (covered_step_digest parameter root otsSecret inputs input next state hvalid hcovered) step hstep
      have hlast := ih step.1.1.1 step.2
        (monitoredStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state
          hvalid step hstep)
        (covered_step_next parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter hauxiliary input
          next state hvalid hcovered step hstep) tail htail
      exact RunAccount.trans parameter root required hfirst hlast

theorem monitoredWorldRun_account {Result : Type} (computation : OracleComp OracleWorld Result) (state : MonitoredState) (hvalid : Valid state)
    (hinputs : hashInputs computation ⊆ inputs) (result : ((Result × SigningBoundaryTrace) × Trace) × MonitoredState)
    (hresult : monitoredWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      computation state result ≠ 0) :
    RunAccount parameter root required state result.1.1.2 [] result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [monitoredWorldRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact RunAccount.refl parameter root required state
  | query_bind input next ih =>
      rw [monitoredWorldRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨step, hstep, hresult⟩ := hresult
      obtain ⟨tail, htail, rfl⟩ := map_nonzero_source' _ _ _ hresult
      have hfirst := monitoredStep_account parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        (.inl input) state hvalid (fun world heq => by cases heq; exact (hashInputs_world_query input next).trans hinputs)
        (fun message heq => by cases heq) step hstep
      have hlast := ih step.1.1.1 step.2
        (monitoredStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter (.inl input)
          state hvalid step hstep) ((hashInputs_world_next input next step.1.1.1).trans hinputs) tail htail
      simpa only [signingLogFragment, List.nil_append] using RunAccount.trans parameter root required hfirst hlast

include hauxiliary in
theorem monitoredCompletedRun_account (adversary : Adversary) (state : MonitoredState) (hvalid : Valid state)
    (hcovered : CoveredRun parameter root otsSecret inputs (adversary.main ⟨root, parameter⟩) state) (result : Completed × MonitoredState)
    (hresult : monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      adversary state result ≠ 0) :
    RunAccount parameter root required state (result.1.1.1.2 * result.1.2.1.2) result.1.1.1.1.2 result.2 := by
  rw [monitoredCompletedRun_eq, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨before, hbefore, hresult⟩ := hresult
  obtain ⟨checked, hchecked, rfl⟩ := map_nonzero_source' _ _ _ hresult
  have hfirst := monitoredRun_account parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
    hauxiliary (adversary.main ⟨root, parameter⟩) state hvalid hcovered before hbefore
  have hvalid' := monitoredRun_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
    (adversary.main ⟨root, parameter⟩) state hvalid before hbefore
  have hfinal := monitoredRun_covered parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
    hauxiliary (adversary.main ⟨root, parameter⟩) state hvalid hcovered before hbefore
  have hlast := monitoredWorldRun_account parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
    (verifyComputation parameter root before.1.1.1.1) before.2 hvalid'
    (covered_pure parameter root otsSecret inputs before.1.1.1.1 before.2 hvalid' hfinal) checked hchecked
  simpa only [List.append_nil] using RunAccount.trans parameter root required hfirst hlast

/-! ### Consequences for the completed run -/

include hauxiliary in
theorem monitoredCompletedRun_creationMass_le (adversary : Adversary) (spent : Nat) (stopped : Bool)
    (hcovered : CoveredRun parameter root otsSecret inputs (adversary.main ⟨root, parameter⟩)
      ((∅, SecretGuessObservation.initialState PUnit.unit), initialCertificateMonitor spent stopped))
    (result : Completed × MonitoredState)
    (hresult : monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      adversary ((∅, SecretGuessObservation.initialState PUnit.unit), initialCertificateMonitor spent stopped) result ≠ 0) :
    result.2.2.creationMass ≤ (completedWork result.1 : ENNReal) := by
  have h := (monitoredCompletedRun_account parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
    hauxiliary adversary _ (fun _ => Finset.univ_nonempty) hcovered result hresult).mass
  simpa only [initialCertificateMonitor, zero_add, SigningBoundaryTrace.hashCalls_mul, completedWork, Nat.cast_add] using h

include hauxiliary in
theorem monitoredCompletedRun_certificate_count (adversary : Adversary) (spent : Nat) (stopped : Bool)
    (hcovered : CoveredRun parameter root otsSecret inputs (adversary.main ⟨root, parameter⟩)
      ((∅, SecretGuessObservation.initialState PUnit.unit), initialCertificateMonitor spent stopped))
    (result : Completed × MonitoredState)
    (hresult : monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      adversary ((∅, SecretGuessObservation.initialState PUnit.unit), initialCertificateMonitor spent stopped) result ≠ 0)
    (halive : result.2.2.stopped = false) (input : HashInput)
    (hcertificate : TargetCertificateAt (monitorKey parameter root) required
      (hashRowsCache (result.1.1.1.2 * result.1.2.1.2).messageCalls, result.1.1.1.1.2) input) :
    1 ≤ certificateBankCount result.2.2.bank := by
  have haccount := monitoredCompletedRun_account parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
    stopAfter hauxiliary adversary _ (fun _ => Finset.univ_nonempty) hcovered result hresult
  have hbank := haccount.bank (fun _ => initialCertificateMonitor_bank_complete (monitorKey parameter root) spent required ∅ stopped
    (fun _ _ => rfl)) halive
  have hlog := haccount.log halive
  simp only [initialCertificateMonitor, List.nil_append] at hlog
  apply one_le_certificateBankCount _ input
  apply hbank input
  change TargetCertificateAt (monitorKey parameter root) required (result.2.1.1, result.2.2.log) input
  rw [hlog]
  exact hcertificate.mono (hashRowsCache_le _ _ haccount.rows)

end SphincsSecurity.Concrete.FtsGuessHash
