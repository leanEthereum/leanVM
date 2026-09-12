import XmssSecurity.Statement

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

namespace Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

noncomputable local instance : SampleableType PublicParameter :=
  SampleableType.ofFintype PublicParameter

noncomputable local instance : SampleableType (Epoch → ChainIndex → Digest) :=
  SampleableType.ofFintype (Epoch → ChainIndex → Digest)

noncomputable def samplePublicParameter : ProbComp PublicParameter :=
  $ᵗ PublicParameter

noncomputable def sampleSecret : ProbComp (Epoch → ChainIndex → Digest) :=
  $ᵗ (Epoch → ChainIndex → Digest)

/-- `Gen`: sample the parameter and the secrets, compute the root through the oracle, and store every chain value and node as the replay of that computation. -/
noncomputable def precomputedKeygen :
    OracleComp OracleWorld (PublicKey × SecretKey) := do
  let parameter ← liftM samplePublicParameter
  let secret ← liftM sampleSecret
  let result ← liftM
    (treeNode parameter secret treeHeight rootNode :
      OracleComp HashSpec Digest).withQueryLog
  let cache := hashCacheOfLog result.2
  return (⟨result.1, parameter⟩, precomputedSecretKey parameter secret cache)

attribute [irreducible] samplePublicParameter sampleSecret precomputedKeygen

end Concrete

/-- The concrete XMSS scheme: the precomputed key generation, the capped retry signer, and the ordinary verifier defined above. -/
noncomputable def Concrete.scheme : Scheme SecretKey where
  keygen := Concrete.precomputedKeygen
  sign := Concrete.precomputedCappedSign
  verify := fun publicKey epoch message signature =>
    liftM (Concrete.verify publicKey epoch message signature : OracleComp HashSpec Bool)

/-- The security claim: `127` bits of classical strong unforgeability in the random-oracle model. -/
abbrev IndependentSecurityStatement : Prop :=
  HasClassicalSecurityBits Concrete.scheme 127

end XmssSecurity
