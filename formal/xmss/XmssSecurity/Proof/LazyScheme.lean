import XmssSecurity.Proof.IdealStatement
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec

namespace XmssSecurity

def SecretKey.withoutPrecomputation
    (parameter : PublicParameter) (chainStart : Epoch → ChainIndex → Digest) :
    SecretKey :=
  ⟨parameter, chainStart, fun _ _ _ => 0, fun _ _ => 0⟩

namespace Concrete

noncomputable local instance : SampleableType (Epoch → ChainIndex → Digest) :=
  SampleableType.ofFintype (Epoch → ChainIndex → Digest)

@[simp]
theorem probOutput_sampleSecret
    (secret : Epoch → ChainIndex → Digest) :
    Pr[= secret | sampleSecret] =
      (Fintype.card (Epoch → ChainIndex → Digest) : ENNReal)⁻¹ := by
  rw [sampleSecret_eq]
  exact probOutput_uniformSample (Epoch → ChainIndex → Digest) secret

noncomputable def keygen : OracleComp OracleWorld (PublicKey × SecretKey) := do
  let parameter ← liftM samplePublicParameter
  let secret ← liftM sampleSecret
  let root ← liftM
    (treeNode parameter secret treeHeight rootNode : OracleComp HashSpec Digest)
  return (⟨root, parameter⟩, SecretKey.withoutPrecomputation parameter secret)

attribute [irreducible] keygen

def signedChainValues {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretKey : SecretKey) (epoch : Epoch) (encoding : Encoding) :
    m (ChainIndex → Digest) :=
  sequenceFin fun chain =>
    chainWalk secretKey.parameter epoch chain 0 (encoding chain).val
      (secretKey.chainStart epoch chain)

def authenticationPath {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretKey : SecretKey) (epoch : Epoch) : m (Fin treeHeight → Digest) :=
  sequenceFin fun level =>
    treeNode secretKey.parameter secretKey.chainStart level.val
      (authenticationPathNode epoch level)

def signWithEncoding {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretKey : SecretKey) (epoch : Epoch) (randomness : Randomness)
    (encoding : Encoding) : m Signature := do
  let chainValue ← signedChainValues secretKey epoch encoding
  let authPath ← authenticationPath secretKey epoch
  return ⟨randomness, chainValue, authPath⟩

noncomputable def signAttempt {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) : m (Option Signature) := do
  let digest ← encodingHash secretKey.parameter epoch message randomness
  match TargetSum.decodeDigest digest with
  | none => pure none
  | some encoding => some <$> signWithEncoding secretKey epoch randomness encoding

noncomputable def sign (secretKey : SecretKey)
    (epoch : Epoch) (message : Message) : OracleComp OracleWorld (Option Signature) := do
  let randomness ← liftM signingRandomness
  liftM (signAttempt secretKey epoch message randomness :
    OracleComp HashSpec (Option Signature))

theorem sign_eq (secretKey : SecretKey)
    (epoch : Epoch) (message : Message) :
    sign secretKey epoch message = (do
      let randomness ← liftM signingRandomness
      liftM (signAttempt secretKey epoch message randomness :
        OracleComp HashSpec (Option Signature))) := rfl

attribute [irreducible] sign

noncomputable def signBoundedAttempts : Nat → SecretKey → Epoch → Message →
    OracleComp OracleWorld (Option Signature)
  | 0, _secretKey, _epoch, _message => pure none
  | attempts + 1, secretKey, epoch, message => do
      let randomness ← liftM signingRandomness
      let result ← liftM (signAttempt secretKey epoch message randomness :
        OracleComp HashSpec (Option Signature))
      match result with
      | some signature => pure (some signature)
      | none => signBoundedAttempts attempts secretKey epoch message

noncomputable def cappedSign (secretKey : SecretKey)
    (epoch : Epoch) (message : Message) : OracleComp OracleWorld (Option Signature) :=
  signBoundedAttempts signingAttemptLimit secretKey epoch message

theorem cappedSign_eq (secretKey : SecretKey)
    (epoch : Epoch) (message : Message) :
    cappedSign secretKey epoch message =
      signBoundedAttempts signingAttemptLimit secretKey epoch message := rfl

attribute [irreducible] cappedSign

def erasePrecomputation (secretKey : SecretKey) : SecretKey :=
  SecretKey.withoutPrecomputation secretKey.parameter secretKey.chainStart

def erasePrecomputedKeyResult (result : PublicKey × SecretKey) :
    PublicKey × SecretKey :=
  (result.1, erasePrecomputation result.2)

theorem erasePrecomputedKeygen_eq_keygen :
    erasePrecomputedKeyResult <$> precomputedKeygen = keygen := by
  unfold precomputedKeygen keygen
  simp only [erasePrecomputedKeyResult, erasePrecomputation,
    precomputedSecretKey, map_bind, map_pure]
  apply bind_congr
  intro parameter
  apply bind_congr
  intro secret
  rw [bind_pure_comp, bind_pure_comp]
  rw [← liftM_map, ← liftM_map]
  apply congrArg (fun computation : OracleComp HashSpec (PublicKey × SecretKey) =>
    (liftM computation : OracleComp OracleWorld (PublicKey × SecretKey)))
  calc
    (fun result : Digest × QueryLog HashSpec =>
        (PublicKey.mk result.1 parameter,
          SecretKey.withoutPrecomputation parameter secret)) <$>
        (treeNode parameter secret treeHeight rootNode :
          OracleComp HashSpec Digest).withQueryLog =
      (fun root : Digest =>
        (PublicKey.mk root parameter,
          SecretKey.withoutPrecomputation parameter secret)) <$>
        (Prod.fst <$> (treeNode parameter secret treeHeight rootNode :
          OracleComp HashSpec Digest).withQueryLog) := by
            rw [Functor.map_map]
    _ = _ := congrArg
      (fun computation : OracleComp HashSpec Digest =>
        (fun root : Digest =>
          (PublicKey.mk root parameter,
            SecretKey.withoutPrecomputation parameter secret)) <$> computation)
      (loggingOracle.fst_map_run_simulateQ
        (treeNode parameter secret treeHeight rootNode :
          OracleComp HashSpec Digest))

end Concrete

end XmssSecurity
