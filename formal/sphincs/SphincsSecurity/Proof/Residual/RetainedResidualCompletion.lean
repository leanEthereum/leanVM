import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.ResidualSigningDisclosure
import SphincsSecurity.Proof.Residual.RetainedResidualMessageTrace
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
set_option backward.isDefEq.respectTransparency false

def Memory.accountWork (memory : Memory) (cost : Nat) : Memory :=
  { memory with external := ResidualByteFrontend.accountWork memory.external cost }

theorem applyBoundary_pow_none (memory : Memory) (cost : Nat) :
    memory.applyBoundary ((FreeMonoid.of none : SigningBoundaryTrace) ^ cost) = memory.accountWork cost := by
  simp only [Memory.applyBoundary, ResidualByteFrontend.applyBoundary_pow_none, SigningBoundaryTrace.messageCalls_pow_none,
    List.append_nil, Memory.accountWork]

theorem publicSigningWork_fixed_memory (parameter : PublicParameter) (root : Digest) (oracle : QueryImpl HashSpec Id)
    (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) (memory : Memory) :
    (fun result => (result.1.1, (memory.applyBoundary result.2).accountWork result.1.2)) <$>
        fixedBoundaryRun parameter oracle (ResidualByteFrontend.publicSigningWork parameter root known words selections message) =
      (fun record => (record, memory.applyBoundary record.2)) <$>
        publicSigningRecord parameter root oracle known words selections message := by
  rw [ResidualByteFrontend.publicSigningWork, fixedBoundaryRun_bind, ResidualByteFrontend.fixedBoundaryRun_boundaryComputation,
    publicSigningRecord, map_bind, bind_map_left, map_bind]
  apply bind_congr
  rintro ⟨selected, trace⟩
  cases selected with
  | none => simp only [fixedBoundaryRun_pure, map_pure, mul_one]; rfl
  | some selected =>
      simp only [fixedBoundaryRun_pure, map_pure, mul_one]
      rw [applyBoundary_mul, applyBoundary_pow_none]

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

noncomputable def disclosureSequenceState (actual : Labels) {n : Nat} (coordinates : Fin n → CanonicalCoordinate) (state : State inputs) : State inputs :=
  (List.ofFn coordinates).foldl (fun state coordinate =>
    disclosedState (environment parameter inputs hencoding words publicReplies selections rows) state coordinate (actual coordinate)) state

theorem observedRun_disclosureSequence_bind {Result : Type} (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    {n : Nat} (coordinates : Fin n → CanonicalCoordinate) (next : (Fin n → Digest) → OracleComp (World inputs) Result) (state : State inputs) :
    observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (simulateQ (embed inputs routing) (sequenceFin fun index => ResidualByteFrontend.jointDisclosure (coordinates index)) >>= next) state =
      observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
        (next (fun index => actual (coordinates index)))
        (disclosureSequenceState parameter inputs hencoding words publicReplies selections rows actual coordinates state) := by
  induction n generalizing state with
  | zero =>
      have hvalues : (Fin.elim0 : Fin 0 → Digest) = (fun index => actual (coordinates index)) := by
        funext index
        exact Fin.elim0 index
      simp only [sequenceFin, simulateQ_pure, pure_bind, hvalues, disclosureSequenceState, List.ofFn_zero, List.foldl_nil]
  | succ n ih =>
      rw [sequenceFin, simulateQ_bind, bind_assoc]
      simp only [ResidualByteFrontend.jointDisclosure, simulateQ_spec_query, embed]
      rw [observedRun, runWith_query_bind]
      simp only [observedImpl, OptionT.run_mk, StateT.run_mk, pure_bind, simulateQ_bind, simulateQ_pure, bind_assoc]
      change observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
        (simulateQ (embed inputs routing) (sequenceFin fun index => ResidualByteFrontend.jointDisclosure (coordinates index.succ)) >>=
          fun tail => next (Fin.cons (actual (coordinates 0)) tail))
        (disclosedState (environment parameter inputs hencoding words publicReplies selections rows) state (coordinates 0) (actual (coordinates 0))) = _
      rw [ih]
      have hvalues : Fin.cons (actual (coordinates 0)) (fun index => actual (coordinates index.succ)) =
          (fun index => actual (coordinates index)) := by
        funext index
        cases index using Fin.cases <;> rfl
      rw [hvalues]
      simp only [disclosureSequenceState, List.ofFn_succ, List.foldl_cons]

theorem disclosureSequenceState_memory (actual : Labels) {n : Nat} (coordinates : Fin n → CanonicalCoordinate) (state : State inputs) :
    (disclosureSequenceState parameter inputs hencoding words publicReplies selections rows actual coordinates state).memory = state.memory := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      rw [disclosureSequenceState, List.ofFn_succ, List.foldl_cons]
      change (disclosureSequenceState parameter inputs hencoding words publicReplies selections rows actual
        (fun index => coordinates index.succ)
        (disclosedState (environment parameter inputs hencoding words publicReplies selections rows) state (coordinates 0) (actual (coordinates 0)))).memory = _
      rw [ih]
      rfl

theorem observedRun_completeRecord_memory (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (record : PublicSigningRecord) (state : State inputs) :
    forgetState <$> observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (simulateQ (embed inputs routing) (ResidualByteFrontend.jointCompleteSigningRecord record)) state =
      pure (some (completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) record), state.memory) := by
  rcases record with ⟨⟨plan, view⟩, trace⟩
  cases plan <;> cases view <;> simp only [ResidualByteFrontend.jointCompleteSigningRecord, completePublicSigningRecord,
    Option.map_none, Option.map_some, simulateQ_pure]
  all_goals try (solve | simp only [observedRun, runWith_pure, map_pure, forgetState])
  rw [simulateQ_bind]
  simp only [simulateQ_pure]
  rw [observedRun_disclosureSequence_bind]
  simp only [observedRun, runWith_pure, map_pure, forgetState, disclosureSequenceState_memory]

theorem observedRun_account_bind {Result : Type} (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (cost : Nat) (next : Unit → OracleComp (World inputs) Result) (state : State inputs) :
    observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (embed inputs routing (.inl (.account cost)) >>= next) state =
      observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
        (next ()) { state with memory := state.memory.accountWork cost } := by
  rw [embed, observedRun, runWith_query_bind]
  simp only [observedImpl, environment, ResidualByteFrontend.environment, OptionT.run_mk, StateT.run_mk,
    PMF.pure_map, SPMF.lift_pure, pure_bind, Option.elim_some, observedRun, afterControl, project,
    Memory.accountWork, ResidualByteFrontend.accountWork]

theorem observedRun_completeWork_memory (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (work : PublicSigningRecord × Nat) (state : State inputs) :
    forgetState <$> observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (simulateQ (embed inputs routing) (ResidualByteFrontend.jointCompleteSigningWork work)) state =
      pure (some (completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) work.1), state.memory.accountWork work.2) := by
  rw [ResidualByteFrontend.jointCompleteSigningWork, simulateQ_bind, simulateQ_spec_query, observedRun_account_bind, observedRun_completeRecord_memory]

end SphincsSecurity.Concrete.RetainedResidual
