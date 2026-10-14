import Whir.PCSBCSMerkleSeedProjection

/-! Every atomic source table has its literal primitive/raw-oracle decomposition.
Captured ordinary prefix authenticity is derived, not an assumed whole-game
certificate. This does not authenticate missing leaves or exclude collisions. -/
set_option autoImplicit false
namespace Whir.PCSBCSMerkleTableAuthenticity
open Concrete FiatShamirGame DuplexModeGame TypedOracleCompiler TypedFiatShamirGame
open PCSStateRestoration.Latent
open PCSBCSChallengeOracle PCSBCSSourceRootReferences PCSBCSCapturedNativeReplyBridge

variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {boundary : Nat}
local notation "part" => EnteredPacket.partition (p := p) (Q := Q) (iv := iv) (boundary := boundary)
local notation "Keys" => PCSBCSSourceRootCapture.Key (p := p) (Q := Q) (iv := iv) (boundary := boundary)
local notation "Answers" => PCSBCSSourceRootCapture.Answer (p := p) (Q := Q) (iv := iv) (boundary := boundary)

noncomputable def seed (table : Table Keys Answers) : PrimitiveOracle :=
  fun input => (part).join table (.inl input)

noncomputable def raw (table : Table Keys Answers) : DuplexModeGame.RawKey Q → Digest32 :=
  fun key => (part).join table (.inr key)

theorem oracle_eq (table : Table Keys Answers) :
    PublicCompressionCouplingMixed.oracle (seed table) (raw table) = (part).join table := by
  funext key
  cases key <;> rfl

theorem split_eq (table : Table Keys Answers) :
    (part).split (PublicCompressionCouplingMixed.oracle (seed table) (raw table)) = table := by
  rw [oracle_eq]
  exact (part).split_join table

/-- Even adaptively selected addresses use the same literal table's seed. -/
theorem sourceLog_authentic {R : Type} {n : Nat}
    (addresses : Keys → List Reference) (ref : Reference)
    (program : Sampling Keys Answers R n) (table : Table Keys Answers) :
    PublicMerkleLog.AuthenticLog (seed table) (sourceLog addresses ref program table) := by
  have derived := PCSBCSMerkleSeedProjection.sourceLog_authentic
    (seed table) (raw table) addresses ref program
  rw [split_eq] at derived
  exact derived

#print axioms oracle_eq
#print axioms split_eq
#print axioms sourceLog_authentic
end Whir.PCSBCSMerkleTableAuthenticity
