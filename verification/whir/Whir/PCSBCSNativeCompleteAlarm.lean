import Whir.PCSBCSSourceRootAdmission
import Whir.PCSBCSNativePhysicalMerkleBad

/-! Exact whole-trace primitive-event join. A real first mention supplies its
physical freeze and scanner admission; actual accepted native execution supplies
all opening plans. The shared alarm, not an extracted-row-mismatch converse,
therefore excludes the retained primitive opening event. Actual first-mention
coverage of every native reference remains an explicit source-chronology join. -/
namespace Whir.PCSBCSNativeCompleteAlarm
open Concrete Protocol FiatShamirGame DuplexModeGame TypedOracleCompiler
open PublicCompressionProgram PublicMerkleLog PCSBCSSourceRootReferences

set_option autoImplicit false

theorem firstMention_opening_quiet {R : Type} (p : ParameterBounds.Profile)
    (B boundary : Nat) (registry : AnchoredHeaderRoots.Public) (C : PrimitiveOracle)
    (program : Program R) (A : Nat) (limit : A ≤ B) (counted : Counts A program)
    (ref : Reference)
    (events : List (Sigma (PCSBCSSourceRootCapture.Answer
      (p := p) (Q := B) (iv := PCSBCSSourceCoordinateDecoder.seedIV) (boundary := boundary))))
    (mentioned : PCSBCSFirstRootDisclosure.firstMention
      (PCSBCSCapturedSourceTransport.address (p := p) (Q := B)
        (iv := PCSBCSSourceCoordinateDecoder.seedIV) (boundary := boundary)) ref
      (PCSBCSNativePhysicalFreeze.allocationProgram (p := p) (boundary := boundary) program A limit counted)
      (PCSBCSNativePhysicalFreeze.actualTable (p := p) (B := B)
        (iv := PCSBCSSourceCoordinateDecoder.seedIV) (boundary := boundary) C) = some events)
    (quiet : PublicMerkleProbability.traceAlarm
      (PCSBCSSourcePrimitiveRootBudget.targets p B boundary registry) []
      (primitiveLog C PCSBCSSourceCoordinateDecoder.seedIV program A counted) = false)
    (output : List MerkleTransport.RawPath)
    (bounds : ∀ path ∈ output, ∀ bytes ∈ path.opening.inputs (MerkleTransport.hashing (hash C)), bytes.length < 2^56)
    (plans : ∀ path ∈ output, ∀ bytes ∈ path.opening.inputs (MerkleTransport.hashing (hash C)),
      ∀ e ∈ plan C bytes, e ∈ primitiveLog C PCSBCSSourceCoordinateDecoder.seedIV program A counted) :
    ¬ PublicMerkleBinding.OpenPrimitiveBad C
      (PCSBCSNativePhysicalFreeze.actualSourceLog (p := p)
        (iv := PCSBCSSourceCoordinateDecoder.seedIV) (boundary := boundary)
        C program A limit counted ref) ref.root output := by
  intro bad
  obtain ⟨frozen,registered,_⟩ := PCSBCSSourceRootAdmission.actual_firstMention_admitted
    p B boundary registry C program A limit counted ref events mentioned quiet
  have alarm := PublicMerkleProbability.opening_alarm C
    (PCSBCSSourcePrimitiveRootBudget.targets p B boundary registry)
    (PCSBCSSourcePrimitiveRootBudget.targets_grow p B boundary registry)
    (primitiveLog C PCSBCSSourceCoordinateDecoder.seedIV program A counted)
    (primitiveLog_authentic C PCSBCSSourceCoordinateDecoder.seedIV program A counted)
    ⟨frozen.before,frozen.after,_,ref.root,output,frozen.split,frozen.captured,
      frozen.saturated,registered,bounds,plans,bad⟩
  rw [quiet] at alarm
  cases alarm


section WholeNative
variable (cap : Nat)
    (nativeRegistry : {r : WHIRPhysicalDriver.ProductionRegistry //
      r.context.iv = PCSBCSSourceCoordinateDecoder.seedIV}) (Q : Nat)
    (attacker : WHIRSourceChronology.Source cap (AnchoredPhysicalAfter.Input nativeRegistry.val.context Q))
    (a b : Nat) (attackerCounted : WHIRSourceChronology.Counts a attacker)
    (nativeBudget : WHIRSourceBackfill.AllResults
      (fun input => WHIRPhysicalVerifier.sourceBudget nativeRegistry.val.context Q input.packet ≤ b)
      (WHIRSourceChronology.erase attacker))
local notation "whole" => PCSBCSNativePhysicalFreeze.wholeProgram cap nativeRegistry.val Q attacker
local notation "counted" => PCSBCSNativePhysicalFreeze.whole_counted
  cap nativeRegistry.val Q attacker a b attackerCounted nativeBudget

/-- The actual accepted native wire supplies all full opening plans. The only
remaining coverage input is the genuine first mention in the whole allocation,
not assumed saturation, raw equality, root admission or a primitive probability. -/
theorem whole_native_opening_quiet (B boundary : Nat) (limit : a+b ≤ B)
    (registry : AnchoredHeaderRoots.Public) (C : PrimitiveOracle)
    (accepted : AnchoredPhysicalAfter.Accepted nativeRegistry.val.context Q cap)
    (success : (runReal C nativeRegistry.val.context.iv whole).view.result.value = some accepted)
    (opening : WHIRPhysicalVerifier.QueryOpening accepted.input.packet.val.profile)
    (opened : opening ∈ accepted.native.wire.openings)
    (ref : Reference) (root : ref.root = opening.root)
    (events : List (Sigma (PCSBCSSourceRootCapture.Answer
      (p := accepted.input.packet.val.profile) (Q := B)
      (iv := PCSBCSSourceCoordinateDecoder.seedIV) (boundary := boundary))))
    (mentioned : PCSBCSFirstRootDisclosure.firstMention
      (PCSBCSCapturedSourceTransport.address (p := accepted.input.packet.val.profile) (Q := B)
        (iv := PCSBCSSourceCoordinateDecoder.seedIV) (boundary := boundary)) ref
      (PCSBCSNativePhysicalFreeze.allocationProgram (p := accepted.input.packet.val.profile)
        (boundary := boundary) whole (a+b) limit counted)
      (PCSBCSNativePhysicalFreeze.actualTable (p := accepted.input.packet.val.profile) (B := B)
        (iv := PCSBCSSourceCoordinateDecoder.seedIV) (boundary := boundary) C) = some events)
    (quiet : PublicMerkleProbability.traceAlarm
      (PCSBCSSourcePrimitiveRootBudget.targets accepted.input.packet.val.profile B boundary registry) []
      (primitiveLog C PCSBCSSourceCoordinateDecoder.seedIV whole (a+b) counted) = false) :
    ¬ PublicMerkleBinding.OpenPrimitiveBad C
      (PCSBCSNativePhysicalFreeze.actualSourceLog (p := accepted.input.packet.val.profile)
        (iv := PCSBCSSourceCoordinateDecoder.seedIV) (boundary := boundary)
        C whole (a+b) limit counted ref) opening.root opening.result.paths := by
  have evaluated := PCSBCSNativePhysicalFreeze.counted_whole_success_evaluated
    cap nativeRegistry.val Q attacker a b attackerCounted nativeBudget C accepted success opening opened
  rw [← root]
  apply firstMention_opening_quiet accepted.input.packet.val.profile B boundary registry C
    whole (a+b) limit counted ref events mentioned quiet opening.result.paths
  · intro path member bytes input
    exact (evaluated path member bytes input).1
  · intro path member bytes input event present
    simpa only [nativeRegistry.property] using (evaluated path member bytes input).2 event present
end WholeNative

#print axioms firstMention_opening_quiet
#print axioms whole_native_opening_quiet
end Whir.PCSBCSNativeCompleteAlarm
