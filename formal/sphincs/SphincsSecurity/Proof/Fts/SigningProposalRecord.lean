import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.AdaptiveProposalWords
import SphincsSecurity.Proof.Fts.DigestSelectionIndex
import SphincsSecurity.Proof.Fts.ProposalBridgeKernel
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop signAfterDigest

private theorem probCompLift_apply {α : Type} (comp : ProbComp α) (value : α) :
    (liftM comp : PMF α) value = Pr[= value | comp] := by
  rw [← PMF.probOutput_eq_apply]
  rfl

theorem probOutput_completeSigningIndex_eq_loop (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (index : Index) :
    Pr[= index | (simulateQ romImpl (signWithView key message)).run cache >>=
      fun result => completeSelectedIndex result.1.2] =
    Pr[= index | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache >>=
      fun result => completeSelectedIndex (selectedLoopView? result)] := by
  rw [signWithView, simulateQ_bind, StateT.run_bind, bind_assoc]
  apply probOutput_bind_congr
  rintro ⟨selected, loopCache⟩ _
  cases selected with
  | none => simp only [simulateQ_pure, StateT.run_pure, pure_bind, selectedLoopView?, Option.map_none]
  | some selected =>
      obtain ⟨randomness, selectedIndex, leaves⟩ := selected
      simp only [simulateQ_bind, StateT.run_bind, bind_assoc, simulateQ_pure, StateT.run_pure,
        pure_bind, selectedLoopView?, Option.map_some]
      simp

abbrev TracedSigningRecord (ω : Type) :=
  ((Option Signature × Option FewTimeView) × ω) × QueryCache HashSpec

noncomputable def tracedSigningRun {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ProbComp (TracedSigningRecord ω) :=
  ((simulateQ (romImpl.withTrace trace) (signWithView key message)).run).run cache

theorem tracedSigningRun_forget {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    (fun result : TracedSigningRecord ω => (result.1.1, result.2)) <$>
      tracedSigningRun trace key message cache = (simulateQ romImpl (signWithView key message)).run cache := by
  have h := congrArg (fun comp : StateT (QueryCache HashSpec) ProbComp (Option Signature × Option FewTimeView) => comp.run cache)
    (QueryImpl.fst_map_run_withTrace romImpl trace (signWithView key message))
  simpa only [StateT.run_map, tracedSigningRun] using h

def signingRecordResponse {ω : Type} (result : TracedSigningRecord ω) :
    (Option Signature × ω) × QueryCache HashSpec :=
  ((result.1.1.1, result.1.2), result.2)

theorem tracedSigningRun_signature {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    signingRecordResponse <$> tracedSigningRun trace key message cache =
      ((simulateQ (romImpl.withTrace trace) (sign key message)).run).run cache := by
  change (fun result : TracedSigningRecord ω => ((result.1.1.1, result.1.2), result.2)) <$>
    tracedSigningRun trace key message cache = _
  have h := congrArg (fun comp : OracleComp OracleWorld (Option Signature) =>
    ((simulateQ (romImpl.withTrace trace) comp).run).run cache) (signWithView_fst key message)
  simpa only [simulateQ_map, WriterT.run_map, StateT.run_map, tracedSigningRun] using h

theorem probOutput_tracedSigningIndex_eq_loop {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (index : Index) :
    Pr[= index | tracedSigningRun trace key message cache >>= fun result => completeSelectedIndex result.1.1.2] =
    Pr[= index | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache >>=
      fun result => completeSelectedIndex (selectedLoopView? result)] := by
  rw [← probOutput_completeSigningIndex_eq_loop, ← tracedSigningRun_forget trace key message cache]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]

noncomputable def completedSigningRecord {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : PMF (TracedSigningRecord ω × Index) :=
  (liftM (tracedSigningRun trace key message cache) : PMF (TracedSigningRecord ω)).bind fun result =>
    (liftM (completeSelectedIndex result.1.1.2) : PMF Index).map (fun index => (result, index))

theorem completedSigningRecord_forget {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    (completedSigningRecord trace key message cache).map Prod.fst =
      (liftM (tracedSigningRun trace key message cache) : PMF (TracedSigningRecord ω)) := by
  rw [completedSigningRecord, PMF.map_bind]
  have hbranch (result : TracedSigningRecord ω) :
      ((liftM (completeSelectedIndex result.1.1.2) : PMF Index).map
        (fun index => (result, index))).map Prod.fst = PMF.pure result := by
    rw [PMF.map_comp]
    exact PMF.map_const _ result
  simp_rw [hbranch]
  exact PMF.bind_pure _

theorem completedSigningRecord_index {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    (completedSigningRecord trace key message cache).map Prod.snd =
      (liftM (tracedSigningRun trace key message cache >>= fun result => completeSelectedIndex result.1.1.2) : PMF Index) := by
  rw [completedSigningRecord, PMF.map_bind]
  have hbranch (result : TracedSigningRecord ω) :
      ((liftM (completeSelectedIndex result.1.1.2) : PMF Index).map
        (fun index => (result, index))).map Prod.snd = liftM (completeSelectedIndex result.1.1.2) := by
    rw [PMF.map_comp]
    exact PMF.map_id _
  simp_rw [hbranch]
  exact (liftM_bind (m := ProbComp) (n := PMF) _ _).symm

theorem completedSigningRecord_index_le {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (spent : Nat) (hspent : spent ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ spent)
    (hclean : ¬ MessageDeficitExceptional key cache)
    (hindex : ∀ index, cachedIndexMultiplicity key.parameter cache index ≤
      (spent : ENNReal) * ((2 ^ 36 : Nat) : ENNReal)⁻¹ + ((2 ^ 80 : Nat) : ENNReal)) (index : Index) :
    ((completedSigningRecord trace key message cache).map Prod.snd) index ≤ targetProposalIndexRate := by
  rw [completedSigningRecord_index, probCompLift_apply, probOutput_tracedSigningIndex_eq_loop]
  exact probOutput_completeSelectedLoopIndex_le_proposalRate key message cache spent hspent hcache hclean hindex index

theorem completedSigningRecord_selected_index {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (record : TracedSigningRecord ω) (index : Index) (view : FewTimeView)
    (hr : (record, index) ∈ (completedSigningRecord trace key message cache).support)
    (hview : record.1.1.2 = some view) : index = view.1 := by
  rw [completedSigningRecord, PMF.mem_support_bind_iff] at hr
  obtain ⟨source, _, hr⟩ := hr
  rw [PMF.mem_support_map_iff] at hr
  obtain ⟨selected, hselected, heq⟩ := hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  simpa only [hview, completeSelectedIndex, Option.elim_some, liftM_pure,
    PMF.monad_pure_eq_pure, PMF.support_pure, Set.mem_singleton_iff] using hselected

abbrev SigningBoundaryTrace := FreeMonoid (Option (HashInput × HashOutput))

noncomputable def signingBoundaryTrace (parameter : PublicParameter) :
    (input : OracleWorld.Domain) → OracleWorld.Range input → SigningBoundaryTrace
  | .inl _, _ => 1
  | .inr input, output => FreeMonoid.of
      (if FtsProbeSimulation.MessageHashInput parameter input then some (input, output) else none)

def SigningBoundaryTrace.hashCalls (trace : SigningBoundaryTrace) : Nat := trace.toList.length

def SigningBoundaryTrace.messageCalls (trace : SigningBoundaryTrace) : List (HashInput × HashOutput) :=
  trace.toList.filterMap id

theorem signingBoundaryTrace_nonmessage (parameter : PublicParameter) (input : HashInput) (output : HashOutput)
    (hinput : ¬ FtsProbeSimulation.MessageHashInput parameter input) :
    signingBoundaryTrace parameter (.inr input) output = FreeMonoid.of none := by
  simp only [signingBoundaryTrace, if_neg hinput]

structure ProposalCacheBound (key : SecretKey) (cache : QueryCache HashSpec) (spent : Nat) : Prop where
  spent_le : spent ≤ 2 ^ 127
  cache_le : QueryCache.enncard cache ≤ spent
  no_deficit : ¬ MessageDeficitExceptional key cache
  index_le : ∀ index, cachedIndexMultiplicity key.parameter cache index ≤
    (spent : ENNReal) * ((2 ^ 36 : Nat) : ENNReal)⁻¹ + ((2 ^ 80 : Nat) : ENNReal)

theorem completedSigningRecord_acceptance_cap {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (spent : Nat)
    (hbound : ProposalCacheBound key cache spent) (index : Index) :
    targetProposalAcceptance * ((completedSigningRecord trace key message cache).map Prod.snd) index ≤
      PMF.uniformOfFintype Index index :=
  targetProposalAcceptance_cap (completedSigningRecord trace key message cache) Prod.snd
    (completedSigningRecord_index_le trace key message cache spent hbound.spent_le hbound.cache_le
      hbound.no_deficit hbound.index_le) index

end SphincsSecurity.Concrete
