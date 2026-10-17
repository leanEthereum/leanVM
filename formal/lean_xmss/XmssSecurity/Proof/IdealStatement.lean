import XmssSecurity.Proof.RandomizedStatement

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

namespace Concrete

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

/-- `rho`, fresh per attempt. -/
noncomputable def signingRandomness : ProbComp Randomness :=
  $ᵗ Randomness

/-- At most `attempts` attempts with the randomizers `base + trial, base + trial + 1, ...`, stopping
at the first that encodes. -/
def precomputedSignBoundedAttempts (secretKey : SecretKey) (leafIndex : LeafIndex)
    (message : Message) (base : Randomness) :
    Nat → Nat → OracleComp OracleWorld (Option Signature)
  | 0, _ => pure none
  | attempts + 1, trial => do
      let result ← liftM
        (precomputedSignAttempt secretKey leafIndex message (base + BitVec.ofNat randomnessBits trial) :
          OracleComp HashSpec (Option Signature))
      match result with
      | some signature => pure (some signature)
      | none => precomputedSignBoundedAttempts secretKey leafIndex message base attempts (trial + 1)

/-- `Sig(sk, idx, m)`: a uniform randomizer base `R0`, then at most `A_max` trials `R0 + c`. The
once-per-leaf-index discipline is the game's, in `SigningTranscript.Valid`. -/
noncomputable def precomputedCappedSign (secretKey : SecretKey)
    (leafIndex : LeafIndex) (message : Message) :
    OracleComp OracleWorld (Option Signature) := do
  let base ← liftM signingRandomness
  let result ← precomputedSignBoundedAttempts secretKey leafIndex message base signingAttemptLimit 0
  return if topSignedAt secretKey leafIndex then result else none

attribute [irreducible] signingRandomness precomputedCappedSign


variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

noncomputable local instance : SampleableType PublicParameter :=
  SampleableType.ofFintype PublicParameter

noncomputable local instance : SampleableType (LeafIndex → ChainIndex → Digest) :=
  SampleableType.ofFintype (LeafIndex → ChainIndex → Digest)

noncomputable def samplePublicParameter : ProbComp PublicParameter :=
  $ᵗ PublicParameter

noncomputable def sampleSecret : ProbComp (LeafIndex → ChainIndex → Digest) :=
  $ᵗ (LeafIndex → ChainIndex → Digest)

noncomputable local instance : SampleableType (TopIndex → ChainIndex → Digest) :=
  SampleableType.ofFintype (TopIndex → ChainIndex → Digest)

noncomputable local instance : SampleableType (TopIndex → Randomness) :=
  SampleableType.ofFintype (TopIndex → Randomness)

noncomputable def sampleTopSecret : ProbComp (TopIndex → ChainIndex → Digest) :=
  $ᵗ (TopIndex → ChainIndex → Digest)

/-- The top randomizer bases `R0_top(b)`, uniform once the seed is eliminated. -/
noncomputable def sampleTopBase : ProbComp (TopIndex → Randomness) :=
  $ᵗ (TopIndex → Randomness)

/-- `Gen`: sample the parameter and the secrets, compute the root through the oracle, and store every chain value and node as the replay of that computation. -/
noncomputable def precomputedKeygen :
    OracleComp OracleWorld (PublicKey × SecretKey) := do
  let parameter ← liftM samplePublicParameter
  let secret ← liftM sampleSecret
  let topSecret ← liftM sampleTopSecret
  let topBase ← liftM sampleTopBase
  let result ← liftM
    (honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _).withQueryLog
  let cache := hashCacheOfLog result.2
  return (⟨result.1.1, parameter⟩, precomputedSecretKey parameter secret topSecret result.1.2 cache)

attribute [irreducible] samplePublicParameter sampleSecret sampleTopSecret sampleTopBase
  precomputedKeygen

end Concrete

/-- The concrete XMSS scheme: the precomputed key generation, the capped retry signer, and the ordinary verifier defined above. -/
noncomputable def Concrete.scheme : Scheme SecretKey where
  keygen := Concrete.precomputedKeygen
  sign := Concrete.precomputedCappedSign
  verify := fun publicKey leafIndex message signature =>
    liftM (Concrete.verify publicKey leafIndex message signature : OracleComp HashSpec Bool)

/-- The security claim: `127` bits of classical strong unforgeability in the random-oracle model. -/
abbrev IndependentSecurityStatement : Prop :=
  HasClassicalSecurityBits Concrete.scheme 127

noncomputable def Seeded.randomizedScheme : Scheme Seeded.SecretKey where
  keygen := Seeded.keygen
  sign := fun sk => Concrete.precomputedCappedSign sk.precomputed
  verify := fun publicKey leafIndex message signature =>
    liftM (Concrete.verify publicKey leafIndex message signature : OracleComp HashSpec Bool)

end XmssSecurity
