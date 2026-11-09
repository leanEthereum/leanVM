module

public import XmssSecurity.Proof.CappedChain.EncodingQueryBound
public import XmssSecurity.Proof.ChainInputTrace
public import VCVio.OracleComp.QueryTracking.QueryBound

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

abbrev AttackerAction := XmssSecurity.AttackerAction

abbrev AttackerActionTrace := XmssSecurity.AttackerActionTrace

def AttackerAction.hashInput? : AttackerAction → Option HashInput
  | .hash input => some input
  | .sign _request _signature => none

def AttackerAction.signingEntry? :
    AttackerAction → Option ((_request : SignRequest) × Option Signature)
  | .hash _ => none
  | .sign request signature => some ⟨request, signature⟩

def AttackerActionTrace.hashInputs (trace : AttackerActionTrace) : List HashInput :=
  trace.filterMap AttackerAction.hashInput?

@[simp]
theorem AttackerActionTrace.hashInputs_append
    (left right : AttackerActionTrace) :
    (left ++ right).hashInputs = left.hashInputs ++ right.hashInputs := by
  simp [AttackerActionTrace.hashInputs]

def AttackerActionTrace.toSigningLog
    (trace : AttackerActionTrace) : QueryLog SigningSpec :=
  trace.filterMap AttackerAction.signingEntry?

@[simp]
theorem AttackerActionTrace.toSigningLog_append
    (left right : AttackerActionTrace) :
    (left ++ right).toSigningLog = left.toSigningLog ++ right.toSigningLog := by
  simp [AttackerActionTrace.toSigningLog]

def attackerActionFragment
    (input : (OracleWorld + SigningSpec).Domain)
    (output : (OracleWorld + SigningSpec).Range input) : AttackerActionTrace :=
  match input with
  | .inl (.inl _) => []
  | .inl (.inr hashInput) => [.hash hashInput]
  | .inr request => [.sign request output]

@[simp]
theorem attackerActionFragment_toSigningLog
    (input : (OracleWorld + SigningSpec).Domain)
    (output : (OracleWorld + SigningSpec).Range input) :
    (attackerActionFragment input output).toSigningLog = signingLogFragment input output := by
  cases input with
  | inl worldInput => cases worldInput <;> rfl
  | inr request => rfl

end XmssSecurity.CappedChain
