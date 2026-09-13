import SphincsSecurity.Proof.Deterministic.TableSigner
import SphincsSecurity.Proof.Deterministic.FreshRequests
import SphincsSecurity.Proof.Ots.EncodingProbability

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev Trial := BitVec 32
abbrev TrialSpec := Trial →ₒ HashOutput
abbrev TrialWorld := OracleWorld + TrialSpec
abbrev TrialResult := Option (Randomness × Index × (IndexGroup → FtsLeaf))
abbrev TrialTape := Trial → HashOutput

noncomputable opaque trialTapeSampleableType : SampleableType TrialTape := SampleableType.ofFintype TrialTape
noncomputable local instance : SampleableType TrialTape := trialTapeSampleableType

noncomputable def sampleTrialTape : ProbComp TrialTape := $ᵗ TrialTape

def trialLoop (secretKey : SphincsSecurity.SecretKey) (message : Message) : Nat → Nat → OracleComp TrialWorld TrialResult
  | 0, _ => pure none
  | attempts + 1, trial => do
      let output ← liftM (TrialWorld.query (.inr (BitVec.ofNat 32 trial)))
      let randomness := truncateHash output
      let attempt ← baseLift (liftM
        (Concrete.signAttempt secretKey message randomness : OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf)))) :
          OracleComp OracleWorld (Option (Index × (IndexGroup → FtsLeaf))))
      match attempt with
      | some (index, leaves) => return some (randomness, index, leaves)
      | none => trialLoop secretKey message attempts (trial + 1)

def earlierTrials (trial : Nat) : Set Trial := {value | value.toNat < trial}

theorem earlierTrials_succ (trial : Nat) (htrial : trial < 2 ^ 32) :
    earlierTrials (trial + 1) = insert (BitVec.ofNat 32 trial) (earlierTrials trial) := by
  ext value
  simp only [earlierTrials, Set.mem_setOf_eq, Set.mem_insert_iff]
  have heq : value = BitVec.ofNat 32 trial ↔ value.toNat = trial := by
    rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htrial]
  rw [heq]
  omega

theorem freshRequests_trialLoop (secretKey : SphincsSecurity.SecretKey) (message : Message)
    (attempts trial : Nat) (hbound : trial + attempts ≤ 2 ^ 32) :
    FreshRequests (earlierTrials trial) (trialLoop secretKey message attempts trial) := by
  induction attempts generalizing trial with
  | zero => exact .pure _
  | succ attempts ih =>
      rw [trialLoop]
      have htrial : trial < 2 ^ 32 := by omega
      apply FreshRequests.request (used := earlierTrials trial) (BitVec.ofNat 32 trial)
        (by
          change ¬ (BitVec.ofNat 32 trial).toNat < trial
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htrial]
          exact Nat.lt_irrefl _)
      intro output
      dsimp only
      apply freshRequests_base_bind (base := OracleWorld) (Request := Trial) (Answer := HashOutput) _
        (liftM (Concrete.signAttempt secretKey message (truncateHash output) : OracleComp HashSpec _) :
          OracleComp OracleWorld _)
      intro attempt
      cases attempt with
      | none =>
          rw [← earlierTrials_succ trial htrial]
          exact ih (trial + 1) (by omega)
      | some result => exact .pure _

end SphincsSecurity.Seeded
