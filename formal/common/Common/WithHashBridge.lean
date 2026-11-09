module

public import Common.WithHash

@[expose] public section

/-!
# The statement's SUF-CMA game and leanXMSS are the hash-query forms, the hash over `π`

The statement's signature schemes hash with Keccak-256 over the permutation they are given
(`HashSig.OverPermutation.keccakHash`); the proofs' forms query a hash (`Common.WithHash`). With the
model's permutation `π`, the statement's algorithms are the hash-query ones with each query
answered by Keccak-256 over `π` (`SufCma.schemeHashOverPermutation`):

* `SufCma.SchemeWithHash.overPermutation`: a hash-query scheme with its queries so answered, a
  scheme of the statement's game, whose game is the hash-query one
  (`SufCma.forgeryGame_overPermutation`);
* `LeanXmss.RandomPermutationModel.scheme_eq`: the statement's leanXMSS is `schemeWithHashFromSeed`
  (`schemeWithHash` with the seed as the key) so answered, each
  algorithm by its simulation lemma (`simulateQ_verifyWithHash`, …).
-/

open OracleComp OracleSpec

namespace Common.SufCma

variable {Seed PK SK Req Resp F : Type}

/-- **A hash-query scheme over `π`**: its algorithms with each hash query answered by Keccak-256
over `π` (`schemeHashOverPermutation`). -/
def SchemeWithHash.overPermutation (S : SchemeWithHash Seed PK SK Req Resp F) :
    Scheme Seed PK SK Req Resp F where
  sampleSeed := S.sample
  generateKeys seed := simulateQ schemeHashOverPermutation (S.keygen seed)
  sign sk r := simulateQ schemeHashOverPermutation (S.sign sk r)
  verify pk f := simulateQ schemeHashOverPermutation (S.verify pk f)
  winningCondition := S.win

/-- The statement's game of a hash-query scheme over `π` is its hash-query game. -/
theorem forgeryGame_overPermutation (S : SchemeWithHash Seed PK SK Req Resp F)
    (main : PK → OracleComp (RandomPermutationOracles + (Req →ₒ Resp)) F) :
    forgeryGame S.overPermutation main = forgeryGameWithHash S main := rfl

end Common.SufCma

namespace LeanXmss

open HashSig

open Common Common.SufCma

/-! ## The combinators commute with a simulation -/

section Combinators

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
  (impl : QueryImpl spec (OracleComp spec'))

open Verification HashSig.OverPermutation

theorem simulateQ_sequenceFin {α : Type} :
    ∀ {n : ℕ} (c : Fin n → OracleComp spec α),
      simulateQ impl (sequenceFin c) = sequenceFin fun i ↦ simulateQ impl (c i)
  | 0, c => by simp [sequenceFin]
  | n + 1, c => by
    simp only [sequenceFin, simulateQ_bind, simulateQ_pure]
    congr 1; funext head; rw [simulateQ_sequenceFin]

theorem simulateQ_walkChain {top : ℕ} (step : Fin top → Digest → OracleComp spec Digest) :
    ∀ (start steps : ℕ) (value : Digest),
      simulateQ impl (walkChain step start steps value) =
        walkChain (fun t v ↦ simulateQ impl (step t v)) start steps value
  | _, 0, _ => by simp [walkChain]
  | start, steps + 1, value => by
    simp only [walkChain, simulateQ_bind, simulateQ_walkChain]
    congr 1; funext previous; split <;> simp

theorem simulateQ_foldPath (node : ℕ → ℕ → HashInput → OracleComp spec Digest) (idx : ℕ)
    (path : ℕ → Digest) :
    ∀ (levels : ℕ) (value : Digest),
      simulateQ impl (foldPath node idx path levels value) =
        foldPath (fun l i x ↦ simulateQ impl (node l i x)) idx path levels value
  | 0, _ => by simp [foldPath]
  | l + 1, value => by
    simp only [foldPath, simulateQ_bind, simulateQ_foldPath]

theorem simulateQ_buildTree (leaf : ℕ → OracleComp spec Digest)
    (node : ℕ → ℕ → HashInput → OracleComp spec Digest) :
    ∀ (level index : ℕ),
      simulateQ impl (buildTree leaf node level index) =
        buildTree (fun i ↦ simulateQ impl (leaf i)) (fun l i x ↦ simulateQ impl (node l i x))
          level index
  | 0, _ => by simp [buildTree]
  | l + 1, index => by
    simp only [buildTree, simulateQ_bind, simulateQ_buildTree]

end Combinators

/-! ## leanXMSS's algorithms -/

local notation "σ" => schemeHashOverPermutation

namespace Verification

open HashSig.OverPermutation

theorem simulateQ_oracleHashWithHash (input : HashInput) :
    simulateQ σ (oracleHashWithHash (m := OracleComp HashSpec) input) =
      keccakHash queryPermutation input := by
  simp only [oracleHashWithHash, simulateQ_HasQuery_query, schemeHashOverPermutation,
    keccak256OverPermutation, keccakHash, Functor.map_map]
  refine congrArg (· <$> _) (funext fun digest ↦ ?_)
  simp only [digestBytesEquivBitVec_apply, LeanVM.Protocol.Digest.toBytes,
    Vector.toList]

theorem simulateQ_thWithHash (parameter : PublicParameter) (fields : TweakFields)
    (payload : HashInput) :
    simulateQ σ (thWithHash (m := OracleComp HashSpec) parameter fields payload) =
      th queryPermutation parameter fields payload := by
  simp only [thWithHash, th, simulateQ_bind, simulateQ_pure, simulateQ_oracleHashWithHash]

theorem simulateQ_thPairWithHash (parameter : PublicParameter) (fields : TweakFields)
    (payload : HashInput) :
    simulateQ σ (thPairWithHash (m := OracleComp HashSpec) parameter fields payload) =
      thPair queryPermutation parameter fields payload := by
  simp only [thPairWithHash, thPair, simulateQ_oracleHashWithHash]

theorem simulateQ_taggedSeedWithHash (seed : MasterSeed) :
    simulateQ σ (taggedSeedWithHash (m := OracleComp HashSpec) seedTag seed) =
      schemeSeedOf queryPermutation seed := by
  simp only [taggedSeedWithHash, schemeSeedOf, simulateQ_oracleHashWithHash]

theorem simulateQ_tweakableHashWithHash (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    simulateQ σ (tweakableHashWithHash (m := OracleComp HashSpec) parameter domain payload) =
      tweakableHash queryPermutation parameter domain payload :=
  simulateQ_thWithHash _ _ _

theorem simulateQ_chainWalkWithHash (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (chainIdx : ChainIndex) (start steps : ℕ) (value : Digest) :
    simulateQ σ (chainWalkWithHash (m := OracleComp HashSpec) parameter lay key chainIdx start steps
      value) = chainWalk queryPermutation parameter lay key chainIdx start steps value := by
  simp only [chainWalkWithHash, chainWalk, simulateQ_walkChain, simulateQ_tweakableHashWithHash]

theorem simulateQ_recoverChainWithHash (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (chainIdx : ChainIndex) (digit : WinternitzDigit) (value : Digest) :
    simulateQ σ (recoverChainWithHash (m := OracleComp HashSpec) parameter lay key chainIdx digit
      value) = recoverChain queryPermutation parameter lay key chainIdx digit value :=
  simulateQ_chainWalkWithHash _ _ _ _ _ _ _

theorem simulateQ_leafHashWithHash (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (endpoints : ChainIndex → Digest) :
    simulateQ σ (leafHashWithHash (m := OracleComp HashSpec) parameter lay key endpoints) =
      leafHash queryPermutation parameter lay key endpoints :=
  simulateQ_tweakableHashWithHash _ _ _

theorem simulateQ_messageDigestWithHash (parameter : PublicParameter) (lay : Layer)
    (key : KeyIndex) (message : HashInput) (randomness : Randomizer) :
    simulateQ σ (messageDigestWithHash (m := OracleComp HashSpec) parameter lay key message
      randomness) = messageDigest queryPermutation parameter lay key message randomness :=
  simulateQ_tweakableHashWithHash _ _ _

theorem simulateQ_otsLeafWithHash (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (message : HashInput) (randomness : Randomizer) (values : ChainIndex → Digest) :
    simulateQ σ (otsLeafWithHash (m := OracleComp HashSpec) parameter lay key message randomness
      values) = otsLeaf queryPermutation parameter lay key message randomness values := by
  simp only [otsLeafWithHash, otsLeaf, simulateQ_bind, simulateQ_messageDigestWithHash]
  congr 1; funext digest
  rcases Codeword.decode digest with _ | encoding
  · simp
  · simp only [simulateQ_bind, simulateQ_sequenceFin, simulateQ_recoverChainWithHash,
      simulateQ_leafHashWithHash, simulateQ_pure]

theorem simulateQ_treeFoldWithHash (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (path : Fin layerHeight → Digest) (levels : ℕ) (value : Digest) :
    simulateQ σ (treeFoldWithHash (m := OracleComp HashSpec) parameter lay key path levels value) =
      treeFold queryPermutation parameter lay key path levels value := by
  simp only [treeFoldWithHash, treeFold, simulateQ_foldPath, simulateQ_tweakableHashWithHash]

theorem simulateQ_layerRootWithHash (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (message : HashInput) (part : LayerSignature) :
    simulateQ σ (layerRootWithHash (m := OracleComp HashSpec) parameter lay key message part) =
      layerRoot queryPermutation parameter lay key message part := by
  simp only [layerRootWithHash, layerRoot, simulateQ_bind, simulateQ_otsLeafWithHash]
  congr 1; funext leaf
  rcases leaf with _ | leaf
  · simp
  · simp only [simulateQ_bind, simulateQ_treeFoldWithHash, simulateQ_pure]

theorem simulateQ_verifyWithHash (publicKey : PublicKey) (message : Message)
    (signature : Signature) :
    simulateQ σ (verifyWithHash (m := OracleComp HashSpec) publicKey message signature) =
      verify queryPermutation publicKey message signature := by
  simp only [verifyWithHash, verify, simulateQ_bind, simulateQ_layerRootWithHash]
  congr 1; funext bottomRoot
  rcases bottomRoot with _ | bottomRoot
  · simp
  · simp only [simulateQ_bind, simulateQ_layerRootWithHash]
    congr 1; funext root
    rcases root with _ | root <;> simp

end Verification

namespace KeyGenerationAndSigning

open Verification HashSig.OverPermutation

theorem simulateQ_otsSecretsWithHash (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (seed : MasterSeed) :
    simulateQ σ (otsSecretsWithHash (m := OracleComp HashSpec) parameter lay key seed) =
      otsSecrets queryPermutation parameter lay key seed := by
  simp only [otsSecretsWithHash, otsSecrets, simulateQ_bind, simulateQ_pure, simulateQ_sequenceFin,
    simulateQ_thPairWithHash]

theorem simulateQ_oneTimePublicKeyWithHash (parameter : PublicParameter) (lay : Layer)
    (key : KeyIndex) (seed : MasterSeed) :
    simulateQ σ (oneTimePublicKeyWithHash (m := OracleComp HashSpec) parameter lay key seed) =
      oneTimePublicKey queryPermutation parameter lay key seed := by
  simp only [oneTimePublicKeyWithHash, oneTimePublicKey, simulateQ_bind, simulateQ_sequenceFin,
    simulateQ_otsSecretsWithHash, simulateQ_chainWalkWithHash]

theorem simulateQ_otsSignFromWithHash (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (seed : MasterSeed) (message : HashInput) (base : Randomizer) :
    ∀ attempts trial : ℕ,
      simulateQ σ (otsSignFromWithHash (m := OracleComp HashSpec) parameter lay key seed message
        base attempts trial) =
        otsSignFrom queryPermutation parameter lay key seed message base attempts trial
  | 0, _ => by simp [otsSignFromWithHash, otsSignFrom]
  | attempts + 1, trial => by
    simp only [otsSignFromWithHash, otsSignFrom, simulateQ_bind, simulateQ_messageDigestWithHash]
    congr 1; funext digest
    rcases Codeword.decode digest with _ | encoding
    · exact simulateQ_otsSignFromWithHash parameter lay key seed message base attempts _
    · simp only [simulateQ_bind, simulateQ_pure, simulateQ_otsSecretsWithHash,
        simulateQ_sequenceFin, simulateQ_chainWalkWithHash]

theorem simulateQ_otsSignWithHash (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (seed : MasterSeed) (message : HashInput) :
    simulateQ σ (otsSignWithHash (m := OracleComp HashSpec) parameter lay key seed message) =
      otsSign queryPermutation parameter lay key seed message := by
  simp only [otsSignWithHash, otsSign, simulateQ_bind, simulateQ_thWithHash,
    simulateQ_otsSignFromWithHash]

theorem simulateQ_treeNodeWithHash (parameter : PublicParameter) (lay : Layer) (seed : MasterSeed)
    (level index : ℕ) :
    simulateQ σ (treeNodeWithHash (m := OracleComp HashSpec) parameter lay seed level index) =
      treeNode queryPermutation parameter lay seed level index := by
  simp only [treeNodeWithHash, treeNode, simulateQ_buildTree, simulateQ_bind,
    simulateQ_oneTimePublicKeyWithHash, simulateQ_leafHashWithHash,
    simulateQ_tweakableHashWithHash]

theorem simulateQ_treePathWithHash (parameter : PublicParameter) (lay : Layer) (seed : MasterSeed)
    (key : KeyIndex) :
    simulateQ σ (treePathWithHash (m := OracleComp HashSpec) parameter lay seed key) =
      treePath queryPermutation parameter lay seed key := by
  simp only [treePathWithHash, treePath, simulateQ_sequenceFin, simulateQ_treeNodeWithHash]

theorem simulateQ_deriveSchemeSeedKey (keySeed : MasterSeed) :
    simulateQ σ (deriveSchemeSeedKey keySeed) = (do
      let seed ← schemeSeedOf queryPermutation keySeed
      let parameter ← publicParameterOf queryPermutation seed
      return (⟨seed, parameter⟩ : SchemeSeedKey)) := by
  simp only [deriveSchemeSeedKey, publicParameterOf, simulateQ_bind, simulateQ_pure,
    simulateQ_taggedSeedWithHash, simulateQ_thWithHash]
  rfl

theorem simulateQ_signLayerWithHash (secretKey : SchemeSeedKey) (lay : Layer) (key : KeyIndex)
    (message : HashInput) :
    simulateQ σ (signLayerWithHash (m := OracleComp HashSpec) secretKey lay key message) =
      signLayer queryPermutation secretKey.schemeSeed secretKey.parameter lay key message := by
  simp only [signLayerWithHash, signLayer, simulateQ_bind, simulateQ_otsSignWithHash]
  congr 1; funext signed
  rcases signed with _ | ⟨randomness, values⟩
  · simp
  · simp only [simulateQ_bind, simulateQ_pure, simulateQ_treePathWithHash]

theorem simulateQ_signWithHash (secretKey : SchemeSeedKey) (index : LeafIndex)
    (message : Message) :
    simulateQ σ (signWithHash (m := OracleComp HashSpec) secretKey index message) =
      signWithSchemeSeed queryPermutation secretKey.schemeSeed secretKey.parameter index message := by
  simp only [signWithHash, signWithSchemeSeed, simulateQ_bind, simulateQ_signLayerWithHash]
  congr 1; funext bottom
  rcases bottom with _ | bottom
  · simp
  · simp only [simulateQ_bind, simulateQ_treeNodeWithHash, simulateQ_signLayerWithHash]
    congr 1; funext bottomRoot; congr 1; funext top
    rcases top with _ | top <;> simp

end KeyGenerationAndSigning

namespace RandomPermutationModel

/-- **The statement's leanXMSS is the hash-query scheme with the crate's key, over `π`.** -/
theorem scheme_eq : sufCmaScheme = schemeWithHashFromSeed.overPermutation := by
  simp only [sufCmaScheme, schemeWithHashFromSeed, KeptKey.scheme, keptKey,
    SchemeWithHash.overPermutation]
  congr 1
  · funext keySeed
    rw [simulateQ_bind, KeyGenerationAndSigning.simulateQ_deriveSchemeSeedKey]
    simp only [KeyGenerationAndSigning.keygenFromSeed, keygenRest, bind_assoc, pure_bind,
      map_bind, simulateQ_bind, simulateQ_pure, KeyGenerationAndSigning.simulateQ_treeNodeWithHash,
      map_pure]
  · funext secretKey request
    simp only [simulateQ_bind, KeyGenerationAndSigning.rederiveSchemeSeedKey,
      KeyGenerationAndSigning.sign, bind_assoc, pure_bind, schemeWithHash,
      Verification.simulateQ_taggedSeedWithHash, KeyGenerationAndSigning.simulateQ_signWithHash]
  · funext publicKey forgery
    simp only [schemeWithHash, Verification.simulateQ_verifyWithHash]

/-- **leanXMSS in the random-permutation model, from the hash-query scheme over `π`.** -/
theorem leanXmssStronglyUnforgeable_of_overPermutation
    (h : StronglyUnforgeable schemeWithHashFromSeed.overPermutation lifetime securitySlack 127) :
    LeanXmssStronglyUnforgeable := by
  rw [LeanXmssStronglyUnforgeable, scheme_eq]
  exact h

end RandomPermutationModel

end LeanXmss
