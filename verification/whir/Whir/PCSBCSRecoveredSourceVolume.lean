import Whir.PCSBCSCoordinateCodecCost
import Whir.PCSBCSPublicLogParserCost

/-! A successful actual public-log coordinate recovery derives its wire-volume
cap from the same physical compression budget. Numeric cursor values contribute
by value and their admitted 49-bit range is kept explicit. No source-work
certificate or bound on an arbitrary metadata callback is used. -/
set_option autoImplicit false
namespace Whir.PCSBCSRecoveredSourceVolume
open FiatShamirGame DuplexFraming DuplexEncoding DuplexPublicSimulator
open PCSBCSCoordinateCodecCost PCSBCSPublicLogParserCost

def recoveredFramePolynomial (Q : Nat) : Nat := (2^49+1)*(65*Q)

theorem frameSize_valid (frame : Frame) (valid : FrameValid frame) :
    frameSize frame ≤ (2^49+1)*frameUnits frame := by
  cases frame <;> simp only [FrameValid] at valid <;>
    simp only [frameSize,frameUnits] <;> nlinarith

theorem framesSize_valid (frames : List Frame)
    (valid : ∀ frame ∈ frames, FrameValid frame) :
    framesSize frames ≤ (2^49+1)*bodyUnits frames := by
  induction frames with
  | nil => simp [framesSize,bodyUnits]
  | cons frame rest ih =>
    have first := frameSize_valid frame (valid frame (by simp))
    have later := ih (fun f member => valid f (by simp [member]))
    simp only [framesSize,bodyUnits,List.map_cons,List.sum_cons] at *
    nlinarith

theorem coordinate_wire (q : Coordinate) (valid : Admissible q) (Q : Nat)
    (physical : pathCost q ≤ Q) :
    framesSize q.history.frames ≤ recoveredFramePolynomial Q := by
  have decoded : decode (plan q) = some q := decode_plan q valid
  have parsed : parse (plan q) = some q := by
    unfold decode at decoded
    cases found : parse (plan q) with
    | none => simp [found] at decoded
    | some candidate =>
      simp only [found] at decoded
      split at decoded
      · cases decoded; rfl
      · contradiction
  have units := parse_units (plan q) q parsed
  have volume := framesSize_valid q.history.frames valid.1
  change (plan q).length ≤ Q at physical
  unfold recoveredFramePolynomial
  nlinarith

theorem recover_wire {Q : Nat} {iv : Digest32} {log : PublicLog} {input : Node}
    {q : Coordinate} (recovered : PCSBCSSourceCoordinateDecoder.recover Q iv log input = some q) :
    framesSize q.history.frames ≤ recoveredFramePolynomial Q := by
  obtain ⟨_,_,_,_,_,_,valid,physical⟩ := PCSBCSSourceCoordinateDecoder.recover_sound recovered
  exact coordinate_wire q valid Q physical

#print axioms frameSize_valid
#print axioms framesSize_valid
#print axioms coordinate_wire
#print axioms recover_wire
end Whir.PCSBCSRecoveredSourceVolume
