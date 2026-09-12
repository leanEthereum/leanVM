import SphincsSecurity.Proof.Forced.FtsGuessWork
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec OtsContactTrace
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (State Environment fixedRun fixedImpl runWith afterTrial)
set_option backward.isDefEq.respectTransparency false

variable {Memory : Type}

def Covered (key : SecretKey) (f : QueryImpl HashSpec Id) (log : QueryLog SigningSpec) (coordinate : Coordinate) : Prop :=
  ∃ message signature, (⟨message, some signature⟩ : SigningEntry) ∈ log ∧
    (RetainedResidual.signingView key f message signature).1 = coordinate.1 ∧
    (RetainedResidual.signingView key f message signature).2 coordinate.2.1 = coordinate.2.2

structure Tracking (key : SecretKey) (f : QueryImpl HashSpec Id) (before after : State Coordinate Digest Memory)
    (log : QueryLog SigningSpec) (trace : Trace) : Prop where
  guesses : before.guesses ⊆ after.guesses
  retired : before.retired ⊆ after.retired
  origin : ∀ coordinate ∈ after.retired, coordinate ∈ before.retired ∨ coordinate ∈ after.guesses ∨ Covered key f log coordinate
  queried : ∀ coordinate, FtsVerifierWitness.TrueSecretQuery f key coordinate.1 coordinate.2.1 coordinate.2.2 trace →
    coordinate ∈ after.retired

theorem Tracking.refl (key : SecretKey) (f : QueryImpl HashSpec Id) (state : State Coordinate Digest Memory) :
    Tracking key f state state [] 1 := by
  refine ⟨Finset.Subset.refl _, Finset.Subset.refl _, fun _ h => Or.inl h, ?_⟩
  intro coordinate h
  cases h

theorem Tracking.trans {key : SecretKey} {f : QueryImpl HashSpec Id} {before middle after : State Coordinate Digest Memory}
    {firstLog secondLog : QueryLog SigningSpec} {firstTrace secondTrace : Trace}
    (first : Tracking key f before middle firstLog firstTrace) (second : Tracking key f middle after secondLog secondTrace) :
    Tracking key f before after (firstLog ++ secondLog) (firstTrace * secondTrace) := by
  refine ⟨first.guesses.trans second.guesses, first.retired.trans second.retired, ?_, ?_⟩
  · intro coordinate h
    rcases second.origin coordinate h with h | h | h
    · rcases first.origin coordinate h with h | h | ⟨message, signature, hm, hi, hl⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl (second.guesses h))
      · exact Or.inr (Or.inr ⟨message, signature, List.mem_append_left _ hm, hi, hl⟩)
    · exact Or.inr (Or.inl h)
    · obtain ⟨message, signature, hm, hi, hl⟩ := h
      exact Or.inr (Or.inr ⟨message, signature, List.mem_append_right _ hm, hi, hl⟩)
  · intro coordinate h
    rw [FtsVerifierWitness.TrueSecretQuery, FreeMonoid.toList_mul, List.mem_append] at h
    exact h.elim (fun h => second.retired (first.queried coordinate h)) (second.queried coordinate)

private theorem map_nonzero {First Result : Type} (function : First → Result) (law : SPMF First) (result : Result) :
    (function <$> law) result ≠ 0 ↔ ∃ first, law first ≠ 0 ∧ result = function first := by
  simp only [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def,
    ne_eq, SPMF.pure_apply_eq_zero_iff, not_not]

theorem fixed_auxiliary_tracking (environment : Environment Auxiliary Coordinate Digest Memory) (secrets : Coordinate → Digest)
    (key : SecretKey) (f : QueryImpl HashSpec Id) (input : Auxiliary.Domain)
    (state : State Coordinate Digest Memory) (result : Auxiliary.Range input × State Coordinate Digest Memory)
    (hr : fixedRun environment secrets (liftM (World.query (.inl input))) state result ≠ 0) :
    Tracking key f state result.2 [] 1 := by
  simp only [fixedRun, runWith, simulateQ_spec_query, fixedImpl, StateT.run_mk, map_nonzero] at hr
  obtain ⟨answer, _, rfl⟩ := hr
  have h := Tracking.refl key f state
  exact ⟨h.guesses, h.retired, h.origin, h.queried⟩

theorem afterTrial_tracking (environment : Environment Auxiliary Coordinate Digest Memory) (key : SecretKey)
    (f : QueryImpl HashSpec Id) (state : State Coordinate Digest Memory) (coordinate : Coordinate) (candidate : Digest) (hit : Bool) :
    Tracking key f state (afterTrial environment state coordinate candidate hit) [] 1 := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [afterTrial]
    split <;> simp only [Finset.subset_insert, Finset.Subset.refl]
  · cases hit <;> simp only [afterTrial, Bool.false_eq_true, if_false, if_true, Finset.Subset.refl, Finset.subset_insert]
  · intro other h
    cases hit with
    | false => exact Or.inl h
    | true =>
        change other ∈ insert coordinate state.retired at h
        rcases Finset.mem_insert.mp h with rfl | h
        · by_cases hc : other ∈ state.retired
          · exact Or.inl hc
          · right; left; simp only [afterTrial, hc, not_false_eq_true, and_self, if_true, Finset.mem_insert_self]
        · exact Or.inl h
  · intro other h
    cases h

theorem fixed_hashProgram_tracking (environment : Environment Auxiliary Coordinate Digest Memory) (key : SecretKey)
    (f : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels) (input : HashInput)
    (state : State Coordinate Digest Memory) (result : HashOutput × State Coordinate Digest Memory)
    (hr : fixedRun environment (FtsGuessSigning.secretTable key.ftsSecret) (hashProgram key.parameter labels input) state result ≠ 0) :
    Tracking key f state result.2 [] (FreeMonoid.of (input, result.1)) := by
  have hbase : Tracking key f state result.2 [] 1 := by
    cases hd : FtsProbeSimulation.decodeProbe? key.parameter input with
    | none =>
        rw [hashProgram, hd] at hr
        exact fixed_auxiliary_tracking environment _ key f (.inl (.inr input)) state result hr
    | some probe =>
        rw [hashProgram, hd, fixedRun, SecretGuessObservation.runWith_query_bind] at hr
        simp only [fixedImpl, StateT.run_mk, pure_bind] at hr
        split at hr
        · simp only [SecretGuessObservation.runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
          subst result
          exact afterTrial_tracking environment key f state _ _ _
        · have h := (afterTrial_tracking environment key f state _ _ _).trans
            (fixed_auxiliary_tracking environment _ key f (.inl (.inr input)) _ result hr)
          simpa only [List.nil_append, one_mul] using h
  refine { hbase with queried := ?_ }
  intro target h
  have hi := congrArg Prod.fst (List.mem_singleton.mp h)
  let probe : FtsSecretProbe := ⟨target.1, target.2.1, target.2.2, key.ftsSecret target.1 target.2.1 target.2.2⟩
  have hp : probe.input key.parameter = input := hi
  rw [hashProgram, (FtsProbeSimulation.decodeProbe?_eq_some_iff key.parameter input probe).mpr hp,
    fixedRun, SecretGuessObservation.runWith_query_bind] at hr
  simp only [fixedImpl, StateT.run_mk, FtsGuessSigning.secretTable, Equiv.coe_fn_mk, coordinate, probe,
    decide_true, if_true, pure_bind, SecretGuessObservation.runWith_pure,
    ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  subst result
  exact Finset.mem_insert_self _ _

theorem fixed_worldProgram_tracking (environment : Environment Auxiliary Coordinate Digest Memory) (key : SecretKey)
    (f : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels) (input : OracleWorld.Domain)
    (state : State Coordinate Digest Memory) (result : OracleWorld.Range input × State Coordinate Digest Memory)
    (hr : fixedRun environment (FtsGuessSigning.secretTable key.ftsSecret) (worldProgram key.parameter labels input) state result ≠ 0) :
    Tracking key f state result.2 [] (hashObservationTrace input result.1) := by
  cases input with
  | inl input => exact fixed_auxiliary_tracking environment _ key f (.inl (.inl input)) state result hr
  | inr input => exact fixed_hashProgram_tracking environment key f labels input state result hr

private theorem disclosureList_retired (environment : Environment Auxiliary Coordinate Digest Memory) (secrets : Coordinate → Digest)
    (entries : List Coordinate) (state : State Coordinate Digest Memory) (target : Coordinate) :
    target ∈ (entries.foldl (fun state coordinate =>
      SecretGuessObservation.afterDisclosure environment state coordinate (secrets coordinate)) state).retired ↔
        target ∈ state.retired ∨ target ∈ entries := by
  induction entries generalizing state with
  | nil => simp only [List.foldl_nil, List.not_mem_nil, or_false]
  | cons coordinate entries ih =>
      rw [List.foldl_cons, ih]
      simp only [SecretGuessObservation.afterDisclosure, Finset.mem_insert, List.mem_cons]
      tauto

theorem completedState_retired (environment : Environment Auxiliary Coordinate Digest Memory) (secrets : Coordinate → Digest)
    (record : PublicSigningRecord) (state : State Coordinate Digest Memory) (target : Coordinate) :
    target ∈ (FtsGuessSigning.completedState environment secrets record state).retired ↔
      target ∈ state.retired ∨ ∃ signature view,
        (completePublicSigningRecord (FtsGuessSigning.secretTable.symm secrets) record).1.1 = some signature ∧
        record.1.2 = some view ∧ view.1 = target.1 ∧ view.2 target.2.1 = target.2.2 := by
  rcases record with ⟨⟨plan, view⟩, trace⟩
  cases plan with
  | none =>
      cases view <;> simp only [FtsGuessSigning.completedState, completePublicSigningRecord, Option.map_none,
        reduceCtorEq, false_and, exists_false, or_false]
  | some plan =>
      cases view with
      | none => simp only [FtsGuessSigning.completedState, completePublicSigningRecord, reduceCtorEq, false_and, exists_false, or_false]
      | some view =>
          simp only [FtsGuessSigning.completedState, SecretGuessObservation.disclosureSequenceState, disclosureList_retired]
          simp only [completePublicSigningRecord, Option.map_some, Option.some.injEq]
          apply or_congr_right
          constructor
          · intro h
            obtain ⟨tree, ht⟩ := List.mem_ofFn.mp h
            refine ⟨_, view, rfl, rfl, congrArg Prod.fst ht, ?_⟩
            have htree := congrArg (fun coordinate : Coordinate => coordinate.2.1) ht
            simpa only [← htree] using congrArg (fun coordinate : Coordinate => coordinate.2.2) ht
          · rintro ⟨signature, selected, _, rfl, hi, hl⟩
            apply List.mem_ofFn.mpr
            exact ⟨target.2.1, Prod.ext hi (Prod.ext rfl hl)⟩

theorem fixed_signingProgram_tracking (environment : Environment Auxiliary Coordinate Digest Memory) (key : SecretKey)
    (f : QueryImpl HashSpec Id) (message : Message) (state : State Coordinate Digest Memory)
    (result : ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × State Coordinate Digest Memory)
    (hr : fixedRun environment (FtsGuessSigning.secretTable key.ftsSecret) (signingProgram message) state result ≠ 0)
    (hview : ∀ signature, result.1.1.1 = some signature →
      result.1.1.2 = some (RetainedResidual.signingView key f message signature)) :
    Tracking key f state result.2 [⟨message, result.1.1.1⟩] 1 := by
  rw [signingProgram, fixedRun, runWith_bind, RetainedObservation.bind_nonzero] at hr
  obtain ⟨middle, hm, hr⟩ := hr
  change PublicSigningRecord × State Coordinate Digest Memory at middle
  have hbase := fixed_auxiliary_tracking environment _ key f (.inr message) state middle hm
  change fixedRun environment _ (FtsGuessSigning.completeRecord middle.1) middle.2 result ≠ 0 at hr
  rw [FtsGuessSigning.fixedRun_completeRecord] at hr
  simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  subst result
  change Tracking key f state
    (FtsGuessSigning.completedState environment (FtsGuessSigning.secretTable key.ftsSecret) middle.1 middle.2)
    [⟨message, (completePublicSigningRecord key.ftsSecret middle.1).1.1⟩] 1
  change ∀ signature, (completePublicSigningRecord key.ftsSecret middle.1).1.1 = some signature →
    (completePublicSigningRecord key.ftsSecret middle.1).1.2 = some (RetainedResidual.signingView key f message signature) at hview
  have hcounts := congrArg Prod.fst (FtsGuessSigning.completedState_counts environment (FtsGuessSigning.secretTable key.ftsSecret) middle.1 middle.2)
  dsimp only at hcounts
  have hview_eq : (completePublicSigningRecord key.ftsSecret middle.1).1.2 = middle.1.1.2 := by
    rcases middle.1 with ⟨⟨plan, view⟩, trace⟩
    cases view <;> rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcounts]; exact hbase.guesses
  · intro target h
    exact (completedState_retired environment _ middle.1 middle.2 target).mpr (Or.inl (hbase.retired h))
  · intro target h
    rcases (completedState_retired environment _ middle.1 middle.2 target).mp h with h | ⟨signature, view, hs, hv, hi, hl⟩
    · rcases hbase.origin target h with h | h | h
      · exact Or.inl h
      · right; left; rwa [hcounts]
      · obtain ⟨_, _, h, _⟩ := h; cases h
    · right; right
      change (completePublicSigningRecord key.ftsSecret middle.1).1.1 = some signature at hs
      have hselected := hview signature hs
      rw [hview_eq, hv] at hselected
      have heq := Option.some.inj hselected
      refine ⟨message, signature, ?_, ?_, ?_⟩
      · rw [hs]; exact List.mem_singleton_self _
      · simpa only [← heq] using hi
      · simpa only [← heq] using hl
  · intro target h
    cases h

end SphincsSecurity.Concrete.FtsGuessHash
