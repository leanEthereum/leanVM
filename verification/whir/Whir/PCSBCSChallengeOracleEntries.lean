import Whir.PCSBCSChallengeOracleErasure

/-! All admitted caller prefixes at one public boundary count, rather than one
fixed data-valued entry. Source-key injectivity supplies finiteness. The actual
caller must derive its boundary count from its bound control shape; this module
does not assert a universal Rust parser or sum silently over other profiles. -/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Whir.PCSBCSChallengeOracle
open Concrete Protocol CausalGame CausalProbability WHIRHistory PCSBCSRounds
open FiatShamirGame DuplexModeGame DuplexFraming RawOracleCoupling

abbrev EnteredPacket (p : ParameterBounds.Profile) (Q : Nat) (iv : Digest32)
    (boundary : Nat) :=
  Sigma (fun entry : {entry : FramedHistory // entry.frames.length = boundary} =>
    CanonicalPacket p Q iv entry.val)

namespace EnteredPacket
variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {boundary : Nat}

def firstKey (packet : EnteredPacket p Q iv boundary) : RawKey Q := packet.2.firstKey

/-- The literal raw key determines the live data-valued caller prefix when the
caller boundary count is fixed by the public control shape. -/
theorem entry_eq_of_firstKey_eq (a b : EnteredPacket p Q iv boundary)
    (same : a.firstKey = b.firstKey) : a.1.val = b.1.val := by
  have coordinates := constructionKey_injective Q iv (a.2.2.valid a.2.firstBlock)
    (b.2.2.valid b.2.firstBlock) (a.2.2.pathBound a.2.firstBlock)
    (b.2.2.pathBound b.2.firstBlock) same
  have history := congrArg FiatShamirGame.Coordinate.history coordinates
  unfold SourcePacket.coordinate at history
  rw [WHIRCallerPrefix.outputKeyFrom_history _ (WHIRHistoryKey.stackWidth_positive p) a.1.val
      (WHIRHistoryKey.scheduled_normal _ _ a.2.2.nonempty a.2.2.admitted),
    WHIRCallerPrefix.outputKeyFrom_history _ (WHIRHistoryKey.stackWidth_positive p) b.1.val
      (WHIRHistoryKey.scheduled_normal _ _ b.2.2.nonempty b.2.2.admitted)] at history
  have domains := congrArg FramedHistory.domain history
  have statements := congrArg FramedHistory.statement history
  have frames := congrArg FramedHistory.frames history
  have prefixes := congrArg (List.take boundary) frames
  have takePrefix (xs ys : List Frame) (length : xs.length = boundary) :
      (xs ++ ys).take boundary = xs := by
    have count := congrArg (fun n => (xs ++ ys).take n) length
    exact count.symm.trans List.take_left
  change List.take boundary (a.1.val.frames ++ WHIRHistoryKey.canonicalFrames
      (WHIRHistoryKey.stackWidth (ParameterBounds.config p)) a.2.messages) =
    List.take boundary (b.1.val.frames ++ WHIRHistoryKey.canonicalFrames
      (WHIRHistoryKey.stackWidth (ParameterBounds.config p)) b.2.messages) at prefixes
  rw [takePrefix _ _ a.1.property,takePrefix _ _ b.1.property] at prefixes
  have records : FramedHistory.mk a.1.val.domain a.1.val.statement a.1.val.frames =
      FramedHistory.mk b.1.val.domain b.1.val.statement b.1.val.frames := by
    rw [domains,statements,prefixes]
  exact records

/-- Caller prefix data may be chosen adaptively; it is not a single reserved
prefix. Different admitted entries cannot share the same first raw source key. -/
theorem firstKey_injective :
    Function.Injective (firstKey (p := p) (Q := Q) (iv := iv) (boundary := boundary)) := by
  intro a b same
  have entrySame : a.1 = b.1 := Subtype.ext (entry_eq_of_firstKey_eq a b same)
  cases a with
  | mk ae ap =>
    cases b with
    | mk be bp =>
      cases entrySame
      have packetSame : ap = bp := CanonicalPacket.firstKey_injective same
      cases packetSame
      rfl

noncomputable instance : Fintype (EnteredPacket p Q iv boundary) := by
  classical
  letI := rawKeyFintype Q
  exact Fintype.ofInjective firstKey firstKey_injective

end EnteredPacket
#print axioms EnteredPacket.entry_eq_of_firstKey_eq
#print axioms EnteredPacket.firstKey_injective
end Whir.PCSBCSChallengeOracle
