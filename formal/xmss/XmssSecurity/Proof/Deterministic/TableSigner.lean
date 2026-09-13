import XmssSecurity.Proof.Deterministic.DerivationTable
import XmssSecurity.Proof.Seeded.Erasure
import XmssSecurity.Proof.Seeded.GameExpansion

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

def tableSignFrom (randomizers : RandomizerOutputs) (secretKey : XmssSecurity.SecretKey)
    (epoch : Epoch) (message : Message) : Nat → Nat → m (Option Signature)
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness := (randomizers (⟨epoch, message⟩, BitVec.ofNat 32 trial)).extractLsb' 0 randomnessBits
      match ← Concrete.precomputedSignAttempt secretKey epoch message randomness with
      | some signature => return some signature
      | none => tableSignFrom randomizers secretKey epoch message attempts (trial + 1)

def tableSign (randomizers : RandomizerOutputs) (secretKey : XmssSecurity.SecretKey)
    (epoch : Epoch) (message : Message) : m (Option Signature) :=
  tableSignFrom randomizers secretKey epoch message signingAttemptLimit 0

noncomputable def tableScheme (randomizers : RandomizerOutputs) : Scheme XmssSecurity.SecretKey where
  keygen := Concrete.scheme.keygen
  sign := fun sk epoch message => liftM (tableSign randomizers sk epoch message : OracleComp HashSpec _)
  verify := Concrete.scheme.verify

theorem erases_signFrom (known : QueryCache HashSpec)
    (seed : MasterSeed) (sk : XmssSecurity.SecretKey) (randomizers : RandomizerOutputs)
    (hknown : ∀ position, known (randomizerInputs sk.parameter seed position) = some (randomizers position))
    (epoch : Epoch) (message : Message) (attempts trial : Nat) :
    Erases known (signFrom ⟨seed, sk⟩ epoch message attempts trial : OracleComp HashSpec _)
      (tableSignFrom randomizers sk epoch message attempts trial) := by
  induction attempts generalizing trial with
  | zero => exact .pure _
  | succ attempts ih =>
      unfold signFrom tableSignFrom deriveRandomizer Concrete.oracleHash
      simp only [bind_assoc, pure_bind]
      apply Erases.skip _ _ (hknown (⟨epoch, message⟩, BitVec.ofNat 32 trial))
      change Erases known (Concrete.precomputedSignAttempt sk epoch message
        ((randomizers (⟨epoch, message⟩, BitVec.ofNat 32 trial)).extractLsb' 0 randomnessBits) >>= _)
          (Concrete.precomputedSignAttempt sk epoch message
            ((randomizers (⟨epoch, message⟩, BitVec.ofNat 32 trial)).extractLsb' 0 randomnessBits) >>= _)
      apply (Erases.refl known _).bind
      intro attempt
      cases attempt with
      | none => exact ih _
      | some result => exact .pure _

theorem erases_sign (known : QueryCache HashSpec)
    (seed : MasterSeed) (sk : XmssSecurity.SecretKey) (randomizers : RandomizerOutputs)
    (hknown : ∀ position, known (randomizerInputs sk.parameter seed position) = some (randomizers position))
    (epoch : Epoch) (message : Message) :
    Erases known (sign ⟨seed, sk⟩ epoch message : OracleComp HashSpec _)
      (tableSign randomizers sk epoch message) :=
  erases_signFrom known seed sk randomizers hknown epoch message _ _

end XmssSecurity.Seeded
