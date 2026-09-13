import SphincsSecurity.Proof.Reference.CausalFrontierAllocation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

def SigningBoundaryTrace.nonmessageCalls (trace : SigningBoundaryTrace) : Nat :=
  trace.toList.countP Option.isNone

theorem SigningBoundaryTrace.nonmessageCalls_mul (first second : SigningBoundaryTrace) :
    (first * second).nonmessageCalls = first.nonmessageCalls + second.nonmessageCalls := by
  simp only [SigningBoundaryTrace.nonmessageCalls, FreeMonoid.toList_mul, List.countP_append]

theorem SigningBoundaryTrace.partition (trace : SigningBoundaryTrace) :
    trace.nonmessageCalls + trace.messageCalls.length = trace.hashCalls := by
  unfold SigningBoundaryTrace.nonmessageCalls SigningBoundaryTrace.messageCalls SigningBoundaryTrace.hashCalls
  generalize trace.toList = records
  induction records with
  | nil => rfl
  | cons entry records ih =>
      cases entry <;> simp_all <;> omega

namespace CausalFrontierProgram

def NonmessageHash (parameter : PublicParameter) : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr input => ¬FtsProbeSimulation.MessageHashInput parameter input

noncomputable instance (parameter : PublicParameter) : DecidablePred (NonmessageHash parameter) := Classical.decPred _

noncomputable def nonmessageTraceCharge (parameter : PublicParameter) : TraceCharge parameter where
  selected := NonmessageHash parameter
  decidable := inferInstance
  cost := SigningBoundaryTrace.nonmessageCalls
  cost_mul := SigningBoundaryTrace.nonmessageCalls_mul
  uniform := by intro input; exact not_false
  step := by
    intro input answer
    cases input with
    | inl input => simp [NonmessageHash, signingBoundaryTrace, SigningBoundaryTrace.nonmessageCalls]
    | inr input =>
        by_cases hmessage : FtsProbeSimulation.MessageHashInput parameter input <;>
          simp [NonmessageHash, signingBoundaryTrace, SigningBoundaryTrace.nonmessageCalls, hmessage]

theorem game_nonmessage_recorded_le (parameter : PublicParameter) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (adversary : Adversary) (result : (Bool × SigningBoundaryTrace) × List OracleWorld.Domain)
    (hresult : result ∈ support (QueryCap.recorded (game parameter external ftsSecret words frontier adversary))) :
    QueryCap.calls (NonmessageHash parameter) result.2 + result.1.2.messageCalls.length ≤ result.1.2.hashCalls := by
  have h := QueryCap.recorded_calls_le (NonmessageHash parameter) _ (fun result => result.2.nonmessageCalls)
    (TraceCharge.game_counted_le (nonmessageTraceCharge parameter) external ftsSecret words frontier adversary) result hresult
  exact (Nat.add_le_add_right h _).trans_eq (SigningBoundaryTrace.partition result.1.2)

end CausalFrontierProgram

end SphincsSecurity.Concrete
