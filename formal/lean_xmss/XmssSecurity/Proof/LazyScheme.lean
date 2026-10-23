import XmssSecurity.Proof.EvalDistEq
import XmssSecurity.Proof.IdealStatement
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec

namespace XmssSecurity

/-- A key with its secrets and top signatures but no stored chain values or nodes. -/
def SecretKey.withoutPrecomputation
    (parameter : PublicParameter) (chainStart : LeafIndex → ChainIndex → Digest)
    (topChainStart : TopIndex → ChainIndex → Digest)
    (topSigned : TopIndex → Option (Randomness × Encoding)) : SecretKey :=
  ⟨parameter, chainStart, fun _ _ _ => 0, fun _ _ => 0, topChainStart, fun _ _ _ => 0, fun _ _ => 0,
    topSigned⟩

namespace Concrete

noncomputable local instance : SampleableType (LeafIndex → ChainIndex → Digest) :=
  SampleableType.ofFintype (LeafIndex → ChainIndex → Digest)

@[simp]
theorem probOutput_sampleSecret
    (secret : LeafIndex → ChainIndex → Digest) :
    Pr{let x ← sampleSecret}[x = secret] =
      (Fintype.card (LeafIndex → ChainIndex → Digest) : ENNReal)⁻¹ := by
  rw [sampleSecret_eq]
  exact SampleableType.prEvent_uniformSample_eq_singleton secret

noncomputable def keygen : OracleComp OracleWorld (PublicKey × SecretKey) := do
  let parameter ← liftM samplePublicParameter
  let secret ← liftM sampleSecret
  let topSecret ← liftM sampleTopSecret
  let topBase ← liftM sampleTopBase
  let result ← liftM
    (honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _)
  return (⟨result.1, parameter⟩,
    SecretKey.withoutPrecomputation parameter secret topSecret result.2)

attribute [irreducible] keygen

def signedChainValues {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretKey : SecretKey) (leafIndex : LeafIndex) (encoding : Encoding) :
    m (ChainIndex → Digest) :=
  sequenceFin fun chain =>
    chainWalk secretKey.parameter leafIndex chain 0 (encoding chain).val
      (secretKey.chainStart leafIndex chain)

def authenticationPath {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretKey : SecretKey) (leafIndex : LeafIndex) : m (Fin treeHeight → Digest) :=
  sequenceFin fun level =>
    treeNode secretKey.parameter secretKey.chainStart level.val
      (authenticationPathNode leafIndex level)

/-- The top layer's signature of bottom tree `b`, its values and path through the oracle. -/
def topSignature {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretKey : SecretKey) (key : TopIndex) : m LayerSignature :=
  match secretKey.topSigned key with
  | some (randomness, encoding) => do
      let chainValue ← sequenceFin fun chain =>
        topChainWalk secretKey.parameter key chain 0 (encoding chain).val
          (secretKey.topChainStart key chain)
      let authPath ← sequenceFin fun level : Fin treeHeight =>
        topTreeNode secretKey.parameter secretKey.topChainStart level.val (topPathNode key level)
      return ⟨randomness, chainValue, authPath⟩
  | none => pure ⟨0, fun _ => 0, fun _ => 0⟩

def signWithEncoding {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretKey : SecretKey) (leafIndex : LeafIndex) (randomness : Randomness)
    (encoding : Encoding) : m Signature := do
  let chainValue ← signedChainValues secretKey leafIndex encoding
  let authPath ← authenticationPath secretKey leafIndex
  let top ← topSignature secretKey (topKeyOf leafIndex)
  return ⟨randomness, chainValue, authPath, top⟩

noncomputable def signAttempt {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) : m (Option Signature) := do
  let digest ← encodingHash secretKey.parameter leafIndex message randomness
  match TargetSum.decodeDigest digest with
  | none => pure none
  | some encoding => some <$> signWithEncoding secretKey leafIndex randomness encoding

noncomputable def sign (secretKey : SecretKey)
    (leafIndex : LeafIndex) (message : Message) : OracleComp OracleWorld (Option Signature) := do
  let randomness ← liftM signingRandomness
  liftM (signAttempt secretKey leafIndex message randomness :
    OracleComp HashSpec (Option Signature))

theorem sign_eq (secretKey : SecretKey)
    (leafIndex : LeafIndex) (message : Message) :
    sign secretKey leafIndex message = (do
      let randomness ← liftM signingRandomness
      liftM (signAttempt secretKey leafIndex message randomness :
        OracleComp HashSpec (Option Signature))) := rfl

attribute [irreducible] sign

noncomputable def signBoundedAttempts (secretKey : SecretKey) (leafIndex : LeafIndex)
    (message : Message) (base : Randomness) : Nat → Nat → OracleComp OracleWorld (Option Signature)
  | 0, _ => pure none
  | attempts + 1, trial => do
      let result ← liftM (signAttempt secretKey leafIndex message
        (base + BitVec.ofNat randomnessBits trial) : OracleComp HashSpec (Option Signature))
      match result with
      | some signature => pure (some signature)
      | none => signBoundedAttempts secretKey leafIndex message base attempts (trial + 1)

noncomputable def cappedSign (secretKey : SecretKey)
    (leafIndex : LeafIndex) (message : Message) : OracleComp OracleWorld (Option Signature) := do
  let base ← liftM signingRandomness
  let result ← signBoundedAttempts secretKey leafIndex message base signingAttemptLimit 0
  return if topSignedAt secretKey leafIndex then result else none

theorem cappedSign_eq (secretKey : SecretKey)
    (leafIndex : LeafIndex) (message : Message) :
    cappedSign secretKey leafIndex message = (do
      let base ← liftM signingRandomness
      let result ← signBoundedAttempts secretKey leafIndex message base signingAttemptLimit 0
      return if topSignedAt secretKey leafIndex then result else none) := rfl

attribute [irreducible] cappedSign

def erasePrecomputation (secretKey : SecretKey) : SecretKey :=
  SecretKey.withoutPrecomputation secretKey.parameter secretKey.chainStart secretKey.topChainStart
    secretKey.topSigned

def erasePrecomputedKeyResult (result : PublicKey × SecretKey) :
    PublicKey × SecretKey :=
  (result.1, erasePrecomputation result.2)

theorem erasePrecomputedKeygen_eq_keygen :
    erasePrecomputedKeyResult <$> precomputedKeygen = keygen := by
  unfold precomputedKeygen keygen
  simp only [erasePrecomputedKeyResult, erasePrecomputation,
    precomputedSecretKey, map_bind, map_pure]
  refine bind_congr fun parameter => bind_congr fun secret => bind_congr fun topSecret =>
    bind_congr fun topBase => ?_
  rw [bind_pure_comp, bind_pure_comp, ← liftM_map, ← liftM_map]
  apply congrArg (fun computation : OracleComp HashSpec (PublicKey × SecretKey) =>
    (liftM computation : OracleComp OracleWorld (PublicKey × SecretKey)))
  have hlog := loggingOracle.fst_map_run_simulateQ
    (honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec (Digest × (TopIndex → Option (Randomness × Encoding))))
  conv_rhs => rw [← hlog, Functor.map_map]
  rfl

end Concrete

end XmssSecurity
