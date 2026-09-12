import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.ResidualSigningProgram
import SphincsSecurity.Proof.Residual.RetainedResidualExecution
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

def currentRouting (inputs : Finset HashInput) : OracleComp (World inputs) Routing :=
  liftM ((World inputs).query (.inl .routing))

def recordSigning (inputs : Finset HashInput) (message : Message) (result : SigningRecord) : OracleComp (World inputs) Unit :=
  liftM ((World inputs).query (.inl (.record message result)))

noncomputable def externalProgram {Result : Type} (inputs : Finset HashInput) (parameter : PublicParameter)
    (words : OtsReferenceWords) (selections : ReferenceFamily) (computation : OracleComp OracleWorld Result) :
    OracleComp (World inputs) Result := do
  let routing ← currentRouting inputs
  simulateQ (embed inputs routing) (simulateQ (ResidualByteFrontend.checkedTranslate inputs
    (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections)) computation)

noncomputable def signingProgram (inputs : Finset HashInput) (parameter : PublicParameter) (root : Digest)
    (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) : OracleComp (World inputs) (Option Signature) := do
  let routing ← currentRouting inputs
  let result ← simulateQ (embed inputs routing)
    (ResidualByteFrontend.jointSigningProgram inputs parameter root routing.known words selections message)
  let _ ← recordSigning inputs message result
  pure result.1.1

noncomputable def adversaryImpl (inputs : Finset HashInput) (parameter : PublicParameter) (root : Digest)
    (words : OtsReferenceWords) (selections : ReferenceFamily) :
    QueryImpl (OracleWorld + SigningSpec) (OracleComp (World inputs))
  | .inl input => externalProgram inputs parameter words selections (liftM (OracleWorld.query input))
  | .inr message => signingProgram inputs parameter root words selections message

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem observedRun_routing_bind {Result : Type} (actual : Labels) (seed : inputs → HashOutput)
    (next : Routing → OracleComp (World inputs) Result) (state : State inputs) :
    observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (currentRouting inputs >>= next) state =
      observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
        (next state.memory.routing) state := by
  rw [currentRouting, observedRun, runWith_query_bind]
  simp only [observedImpl, environment, OptionT.run_mk, StateT.run_mk, SPMF.lift_pure, pure_bind, Option.elim_some, observedRun]

theorem observedRun_record_bind {Result : Type} (actual : Labels) (seed : inputs → HashOutput)
    (message : Message) (result : SigningRecord) (next : Unit → OracleComp (World inputs) Result) (state : State inputs) :
    observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (recordSigning inputs message result >>= next) state =
      observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
        (next ()) { state with memory := state.memory.recordSigning message result } := by
  rw [recordSigning, observedRun, runWith_query_bind]
  simp only [observedImpl, environment, OptionT.run_mk, StateT.run_mk, SPMF.lift_pure, pure_bind, Option.elim_some, observedRun]

theorem observedRun_signingProgram (actual : Labels) (seed : inputs → HashOutput)
    (root : Digest) (message : Message) (state : State inputs) :
    observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (signingProgram inputs parameter root words selections message) state =
      (observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
        (simulateQ (embed inputs state.memory.routing)
          (ResidualByteFrontend.jointSigningProgram inputs parameter root state.memory.routing.known words selections message)) state >>= fun result =>
        result.1.elim (pure (none, result.2)) (fun record =>
          pure (some record.1.1, { result.2 with memory := result.2.memory.recordSigning message record }))) := by
  rw [signingProgram, observedRun_routing_bind, observedRun_bind]
  apply congrArg (_ >>= ·)
  funext result
  rcases result with ⟨record, after⟩
  cases record with
  | none => rfl
  | some record =>
      rw [Option.elim_some, observedRun_record_bind]
      exact runWith_pure _ _ _

end SphincsSecurity.Concrete.RetainedResidual
