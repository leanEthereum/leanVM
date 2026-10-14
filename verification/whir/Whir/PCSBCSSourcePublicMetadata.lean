import Whir.PCSBCSSourceCoordinateDecoderSource
import Whir.PCSBCSSourceSavedRecordProvenance
import Whir.PCSBCSPublicCallerCompletion

/-! Source metadata is recovered from the actual primitive input and its public
prefix. Original caller reconstruction completes missing earlier outputs with
real compression draws before using a public-only finite getter. Invalid or
incomplete public metadata returns `none`, never a manufactured record. -/
set_option autoImplicit false
namespace Whir.PCSBCSSourcePublicMetadata
open Concrete FiatShamirGame DuplexFraming DuplexPublicSimulator
open PublicCompressionProgram PCSBCSPublicCallerCompletion
open DuplexRefinement DuplexModeGame TypedOracleCompiler RawOracleCoupling

structure Metadata where
  coordinate : Coordinate
  saved : AnchoredHeaderCodec.Record

/-- The boundary is public source geometry, not supplied saved-header data. -/
def entry (boundary : Nat) (coordinate : Coordinate) : FramedHistory :=
  { coordinate.history with frames := coordinate.history.frames.take boundary }

def recover (p : ParameterBounds.Profile) (Q boundary : Nat)
    (queryPrefix : PublicLog) (input : Node) : Option Metadata := do
  let coordinate ← PCSBCSSourceCoordinateDecoder.recover Q
    PCSBCSSourceCoordinateDecoder.seedIV queryPrefix input
  let saved ← PCSBCSSourceSavedRecordDecoder.decode p (entry boundary coordinate)
  return ⟨coordinate,saved⟩

theorem recover_sound (p : ParameterBounds.Profile) (Q boundary : Nat)
    (queryPrefix : PublicLog) (input : Node) (metadata : Metadata)
    (accepted : recover p Q boundary queryPrefix input = some metadata) :
    PCSBCSSourceCoordinateDecoder.recover Q
      PCSBCSSourceCoordinateDecoder.seedIV queryPrefix input = some metadata.coordinate ∧
    PCSBCSSourceSavedRecordDecoder.decode p (entry boundary metadata.coordinate) =
      some metadata.saved ∧ metadata.saved.Valid ∧
      PCSBCSSourceSavedRecordDecoder.Compatible p metadata.saved := by
  unfold recover at accepted
  cases decoded : PCSBCSSourceCoordinateDecoder.recover Q
      PCSBCSSourceCoordinateDecoder.seedIV queryPrefix input with
  | none => simp [decoded] at accepted
  | some coordinate =>
    simp only [decoded,Option.bind_eq_bind,Option.bind_some] at accepted
    cases saved : PCSBCSSourceSavedRecordDecoder.decode p (entry boundary coordinate) with
    | none => simp [saved] at accepted
    | some record =>
      simp only [saved,Option.bind_some] at accepted
      change some (⟨coordinate,record⟩ : Metadata) = some metadata at accepted
      have equal := Option.some.inj accepted
      cases equal
      have sound := PCSBCSSourceSavedRecordDecoder.decode_sound p
        (entry boundary coordinate) record saved
      exact ⟨rfl,saved,sound.1,sound.2.1⟩

/-- A recovered coordinate and successful actual native caller parse determine
all saved fields. Saved metadata is not fixed before random-table sampling. -/
theorem recover_native (p : ParameterBounds.Profile) (Q boundary : Nat)
    (queryPrefix : PublicLog) (input : Node) (coordinate : Coordinate)
    (layout : WHIRCallerClaims.CallerLayout) (saved : AnchoredHeaderCodec.Record)
    (answers : Coordinate → Digest32) (claims : AnchoredSourceCaller.Claims)
    (decoded : PCSBCSSourceCoordinateDecoder.recover Q
      PCSBCSSourceCoordinateDecoder.seedIV queryPrefix input = some coordinate)
    (accepted : AnchoredSourceFreshCaller.decode layout saved
      (entry boundary coordinate) answers = some claims)
    (valid : saved.Valid) (profile : PCSBCSSourceSavedRecordDecoder.Compatible p saved) :
    recover p Q boundary queryPrefix input = some ⟨coordinate,saved⟩ := by
  have found := PCSBCSSourceSavedRecordProvenance.decode_saved p layout saved
    (entry boundary coordinate) answers claims accepted valid profile
  simp only [recover,decoded,Option.bind_eq_bind,Option.bind_some,found]
  rfl

/-- A finite executable availability check justifies the public-only getter.
The outside callback is never used for a caller-observed coordinate. -/
def resolveOriginal (p : ParameterBounds.Profile) (layout : WHIRCallerClaims.CallerLayout)
    (iv : Digest32) (boundary : Nat) (metadata : Metadata) (log : PublicLog)
    (outside : Coordinate → Digest32) : Option (PCSBCSCallerBinding.CallerInput p) :=
  let originalEntry := entry boundary metadata.coordinate
  if ready : (WHIRCallerOutputs.callerOutputs originalEntry).all
      (fun q => (PCSBCSPublicCallerAnswers.answer? log iv q).isSome) = true then
    PCSBCSSourceCallerOriginal.original p layout metadata.saved originalEntry
      (callerAnswers iv log originalEntry (List.all_eq_true.mp ready) outside)
  else none

def originalCompletion (p : ParameterBounds.Profile) (layout : WHIRCallerClaims.CallerLayout)
    (iv : Digest32) (boundary : Nat) (metadata : Metadata) (log : PublicLog)
    (outside : Coordinate → Digest32) :
    Computation (Option (PCSBCSCallerBinding.CallerInput p))
      (budget (WHIRCallerOutputs.callerOutputs (entry boundary metadata.coordinate))) :=
  mapResult (fun completed => resolveOriginal p layout iv boundary metadata completed outside)
    (callerCompletion iv log (entry boundary metadata.coordinate))

theorem originalCompletion_exact (C : PrimitiveOracle) (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (iv : Digest32) (boundary : Nat)
    (metadata : Metadata) (log : PublicLog) (auth : PublicMerkleLog.AuthenticLog C log)
    (outside : Coordinate → Digest32) :
    Sampling.eval C (originalCompletion p layout iv boundary metadata log outside) =
      PCSBCSSourceCallerOriginal.original p layout metadata.saved
        (entry boundary metadata.coordinate) (evalCoordinate (compressionOf C) iv) := by
  let originalEntry := entry boundary metadata.coordinate
  have available := callerCompletion_total C iv log auth originalEntry
  have ready : (WHIRCallerOutputs.callerOutputs originalEntry).all
      (fun q => (PCSBCSPublicCallerAnswers.answer?
        (Sampling.execute C (callerCompletion iv log originalEntry)).1 iv q).isSome) = true :=
    List.all_eq_true.mpr available
  simp only [originalCompletion,eval_mapResult]
  rw [← Sampling.execute_value]
  change resolveOriginal p layout iv boundary metadata
    (Sampling.execute C (callerCompletion iv log originalEntry)).1 outside = _
  simp only [resolveOriginal,show entry boundary metadata.coordinate = originalEntry from rfl,
    ready,↓reduceDIte]
  exact original_resolved C iv log auth originalEntry p layout metadata.saved outside

theorem originalCompletion_draws_le (C : PrimitiveOracle) (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (iv : Digest32) (boundary : Nat)
    (metadata : Metadata) (log : PublicLog) (outside : Coordinate → Digest32) :
    (Sampling.execute C (originalCompletion p layout iv boundary metadata log outside)).2.length ≤
      ((WHIRCallerOutputs.callerOutputs (entry boundary metadata.coordinate)).map pathCost).sum := by
  simp only [originalCompletion,execute_mapResult]
  exact complete_draws_le C iv log _

#print axioms recover_sound
#print axioms recover_native
#print axioms originalCompletion_exact
#print axioms originalCompletion_draws_le
end Whir.PCSBCSSourcePublicMetadata
