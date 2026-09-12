import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Reference.CausalPublicSigning
namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec CanonicalProbeRouting
set_option backward.isDefEq.respectTransparency false

variable {inputs : Finset HashInput}

open AdaptiveResidualLabels hiding World State Environment

def jointDisclosure (coordinate : CanonicalCoordinate) : OracleComp (World inputs) Digest :=
  liftM ((World inputs).query (.inr (.disclose coordinate)))

def jointDisclosureSequenceState (environment : AdaptiveResidualLabels.Environment (ControlSpec inputs) CanonicalCoordinate inputs ExternalMemory)
    (labels : CanonicalCoordinate → Digest) {n : Nat} (coordinates : Fin n → CanonicalCoordinate)
    (state : State inputs) : State inputs :=
  (List.ofFn coordinates).foldl (fun state coordinate => disclosedState environment state coordinate (labels coordinate)) state

theorem observedRun_jointDisclosureSequence_bind {Result : Type}
    (environment : AdaptiveResidualLabels.Environment (ControlSpec inputs) CanonicalCoordinate inputs ExternalMemory) (labels : CanonicalCoordinate → Digest) (seed : inputs → HashOutput)
    {n : Nat} (coordinates : Fin n → CanonicalCoordinate)
    (next : (Fin n → Digest) → OracleComp (World inputs) Result)
    (state : State inputs) :
    observedRun environment labels seed ((sequenceFin fun index => jointDisclosure (coordinates index)) >>= next) state =
      observedRun environment labels seed (next (fun index => labels (coordinates index)))
        (jointDisclosureSequenceState environment labels coordinates state) := by
  induction n generalizing state with
  | zero =>
      have hvalues : (Fin.elim0 : Fin 0 → Digest) = (fun index => labels (coordinates index)) := by
        funext index
        exact Fin.elim0 index
      simp only [sequenceFin, pure_bind, hvalues, jointDisclosureSequenceState, List.ofFn_zero, List.foldl_nil]
  | succ n ih =>
      rw [sequenceFin, bind_assoc]
      change runWith (observedImpl environment labels seed)
        (liftM ((World inputs).query (.inr (.disclose (coordinates 0)))) >>= _) state = _
      rw [runWith_query_bind]
      simp only [observedImpl, OptionT.run_mk, StateT.run_mk, pure_bind, bind_assoc]
      change observedRun environment labels seed
        ((sequenceFin fun index => jointDisclosure (coordinates index.succ)) >>=
          fun tail => next (Fin.cons (labels (coordinates 0)) tail))
        (disclosedState environment state (coordinates 0) (labels (coordinates 0))) = _
      rw [ih]
      have hvalues : Fin.cons (labels (coordinates 0)) (fun index => labels (coordinates index.succ)) =
          (fun index => labels (coordinates index)) := by
        funext index
        cases index using Fin.cases <;> rfl
      rw [hvalues]
      simp only [jointDisclosureSequenceState, List.ofFn_succ, List.foldl_cons]

def jointCompleteSigningRecord (record : PublicSigningRecord) :
    OracleComp (World inputs) ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) :=
  match record.1.1, record.1.2 with
  | some plan, some view => do
      let secrets ← sequenceFin fun tree => jointDisclosure (.ftsStart view.1 tree (view.2 tree))
      pure ((some (plan.finish secrets), some view), record.2)
  | _, _ => pure ((none, record.1.2), record.2)

def jointCompletedSigningState (environment : AdaptiveResidualLabels.Environment (ControlSpec inputs) CanonicalCoordinate inputs ExternalMemory)
    (labels : CanonicalCoordinate → Digest) (record : PublicSigningRecord)
    (state : State inputs) : State inputs :=
  match record.1.1, record.1.2 with
  | some _, some view => jointDisclosureSequenceState environment labels (fun tree => .ftsStart view.1 tree (view.2 tree)) state
  | _, _ => state

theorem observedRun_jointCompleteSigningRecord
    (environment : AdaptiveResidualLabels.Environment (ControlSpec inputs) CanonicalCoordinate inputs ExternalMemory) (labels : CanonicalCoordinate → Digest) (seed : inputs → HashOutput)
    (record : PublicSigningRecord) (state : State inputs) :
    observedRun environment labels seed (jointCompleteSigningRecord record) state =
      pure (some (completePublicSigningRecord (fun index tree leaf => labels (.ftsStart index tree leaf)) record),
        jointCompletedSigningState environment labels record state) := by
  obtain ⟨⟨plan, view⟩, trace⟩ := record
  cases plan <;> cases view <;> simp only [jointCompleteSigningRecord, completePublicSigningRecord, jointCompletedSigningState,
    Option.map_none, Option.map_some]
  all_goals first
    | exact runWith_pure (observedImpl environment labels seed) _ _
    | rw [observedRun_jointDisclosureSequence_bind]; exact runWith_pure (observedImpl environment labels seed) _ _

variable (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (actions : inputs → ResidualByteAction.Action inputs)

theorem jointDisclosureSequenceState_memory (actual : Labels) {n : Nat} (coordinates : Fin n → CanonicalCoordinate)
    (state : State inputs) :
    (jointDisclosureSequenceState (environment parameter inputs words disclosed known actions) actual coordinates state).memory = state.memory := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      rw [jointDisclosureSequenceState, List.ofFn_succ, List.foldl_cons]
      change (jointDisclosureSequenceState (environment parameter inputs words disclosed known actions) actual
        (fun index => coordinates index.succ)
        (disclosedState (environment parameter inputs words disclosed known actions) state (coordinates 0) (actual (coordinates 0)))).memory = _
      rw [ih]
      rfl

theorem observedRun_account_bind {Result : Type} (actual : Labels) (seed : inputs → HashOutput) (cost : Nat)
    (next : Unit → OracleComp (World inputs) Result) (state : State inputs) :
    observedRun (environment parameter inputs words disclosed known actions) actual seed
      (liftM ((World inputs).query (.inl (.account cost))) >>= next) state =
    observedRun (environment parameter inputs words disclosed known actions) actual seed
      (next ()) { state with memory := accountWork state.memory cost } := by
  rw [observedRun, runWith_query_bind]
  simp only [observedImpl, environment, OptionT.run_mk, StateT.run_mk,
    SPMF.lift_pure, pure_bind, Option.elim_some, observedRun, accountWork]

omit parameter words disclosed known actions in
def jointCompleteSigningWork (work : PublicSigningRecord × Nat) :
    OracleComp (World inputs) ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) := do
  let _ ← liftM ((World inputs).query (.inl (.account work.2)))
  jointCompleteSigningRecord work.1

theorem observedRun_jointCompleteSigningWork (actual : Labels) (seed : inputs → HashOutput)
    (work : PublicSigningRecord × Nat) (state : State inputs) :
    observedRun (environment parameter inputs words disclosed known actions) actual seed (jointCompleteSigningWork work) state =
      pure (some (completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) work.1),
        jointCompletedSigningState (environment parameter inputs words disclosed known actions) actual work.1
          { state with memory := accountWork state.memory work.2 }) := by
  rw [jointCompleteSigningWork, observedRun_account_bind, observedRun_jointCompleteSigningRecord]

end SphincsSecurity.Concrete.ResidualByteFrontend
