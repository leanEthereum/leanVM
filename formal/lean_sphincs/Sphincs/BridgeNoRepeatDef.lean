import Sphincs.Statement

/-! Programs and adversaries that never request a signature on the same message twice (the
definitions only, so that their users do not depend on the potential modules). -/

open OracleComp OracleSpec

namespace Sphincs.Security.ForsPotential

variable [Params]

/-- The program never requests a signature on a message of `S`, nor twice on the same message. -/
def NoRepeat {α : Type} (M : OracleComp (OracleWorld + SigningSpec) α) : List Message → Prop :=
  OracleComp.construct (C := fun _ => List Message → Prop) (fun _ _ => True)
    (fun input _ rec S => match input with
      | .inl _ => ∀ v, rec v S
      | .inr m => m ∉ S ∧ ∀ r, rec r (S ++ [m])) M

omit [Params] in
theorem noRepeat_sign {α : Type} (m : Message)
    (next : Option Signature → OracleComp (OracleWorld + SigningSpec) α) (S : List Message) :
    NoRepeat (liftM ((OracleWorld + SigningSpec).query (.inr m)) >>= next) S ↔
      m ∉ S ∧ ∀ r, NoRepeat (next r) (S ++ [m]) :=
  Iff.rfl

/-- An adversary that never requests a signature on the same message twice. -/
def _root_.Sphincs.Security.Adversary.NoRepeat (adversary : Adversary) : Prop :=
  ∀ pk, ForsPotential.NoRepeat (adversary.main pk) []

end Sphincs.Security.ForsPotential
