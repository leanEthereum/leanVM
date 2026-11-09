module

public import XmssSecurity.Proof.Bridge.Real
public import XmssSecurity.Proof.OwnTotal

@[expose] public section

/-!
# The real game's hash calls

Static bounds on the real scheme's hash calls: key generation makes `K`, a signature at most
`realSignCalls` (its `2^32` randomizer trials and the trees it rebuilds), and verification
`realVerifyCalls`. With the adversary's own calls and requests bounded, so is the whole game.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Bridge

set_option backward.isDefEq.respectTransparency false

local notation "RH" => OracleComp LeanXmss.HashSpec

/- A tree node at the literal height `16` unfolds to `2^16` leaves under `whnf`. -/
attribute [local irreducible] LeanXmss.layerHeight

theorem QueryCount.total {ι : Type} {spec : OracleSpec ι} {α : Type} {c : OracleComp spec α} {n : Nat}
    (h : QueryCount c n) : IsTotalQueryBound c n := by
  induction h with
  | pure a => exact isQueryBound_pure _ _ _ _
  | query x next n _ ih =>
      rw [isTotalQueryBound_query_bind_iff]
      exact ⟨Nat.succ_pos _, fun a => by simpa using ih a⟩

theorem tbind {ι : Type} {spec : OracleSpec ι} {α β : Type} {first : OracleComp spec α}
    {next : α → OracleComp spec β} {a b n : Nat}
    (h1 : IsTotalQueryBound first a) (h2 : ∀ value, IsTotalQueryBound (next value) b) (h : a + b ≤ n) :
    IsTotalQueryBound (first >>= next) n :=
  (isTotalQueryBound_bind h1 h2).mono h

theorem tpure {ι : Type} {spec : OracleSpec ι} {α : Type} (a : α) (n : Nat) :
    IsTotalQueryBound (pure a : OracleComp spec α) n :=
  isQueryBound_pure _ _ _ _

theorem total_thWithHash (parameter : PublicParameter) (fields : LeanXmss.TweakFields) (payload : HashInput) :
    IsTotalQueryBound (LeanXmss.Verification.thWithHash parameter fields payload : RH HashSig.Digest) 1 := by
  unfold LeanXmss.Verification.thWithHash
  have h := (queryCount_oracleHash (LeanXmss.thInput parameter fields payload)).bind
    (f := fun output => (pure (HashSig.truncateHash output) : OracleComp HashSpec HashSig.Digest))
    fun _ => QueryCount.pure _
  exact h.total

theorem total_realChainWalk (parameter : PublicParameter) (lay : LeanXmss.Layer)
    (key : LeanXmss.KeyIndex) (chain : ChainIndex) (start steps : Nat)
    (hsteps : start + steps ≤ chainLength - 1) (value : Digest) :
    IsTotalQueryBound (LeanXmss.Verification.chainWalkWithHash parameter lay key chain start steps value :
      RH HashSig.Digest) 3 :=
  (queryCount_realChainWalk parameter lay key chain start steps hsteps value).total.mono (by
    simp only [chainLength, winternitzBits] at hsteps; omega)

theorem total_chains {f : LeanXmss.ChainIndex → RH HashSig.Digest} (h : ∀ chain, IsTotalQueryBound (f chain) 3) :
    IsTotalQueryBound (HashSig.OverPermutation.sequenceFin f) 174 := by
  rw [sequenceFin_eq]
  exact total_sequenceFin 3 f h

/-- The hash calls of a real one-time signature: the trials, then the secrets and chains. -/
theorem total_otsSignFrom (parameter : PublicParameter) (lay : LeanXmss.Layer) (key : LeanXmss.KeyIndex)
    (seed : MasterSeed) (message : HashInput) (base : HashSig.Randomizer) :
    ∀ attempts trial, IsTotalQueryBound (LeanXmss.KeyGenerationAndSigning.otsSignFromWithHash parameter lay
      key seed message base attempts trial : RH _) (attempts + 203)
  | 0, _ => tpure _ _
  | attempts + 1, trial => by
      rw [LeanXmss.KeyGenerationAndSigning.otsSignFromWithHash]
      refine tbind (total_thWithHash _ _ _) (b := attempts + 203) (fun digest => ?_) (by omega)
      split
      · refine tbind (queryCount_otsSecrets parameter lay key seed).total (b := 174) (fun secrets => ?_)
          (by omega)
        refine tbind (total_chains fun chain => total_realChainWalk _ _ _ _ 0 _ ?_ _) (b := 0)
          (fun _ => tpure _ _) le_rfl
        have := (‹LeanXmss.Encoding› chain).isLt
        simp only [HashSig.chainLength, HashSig.winternitzBits, chainLength, winternitzBits] at this ⊢
        omega
      · exact total_otsSignFrom parameter lay key seed message base attempts (trial + 1)

theorem nodeQueries_le {level : Nat} (h : level ≤ 16) : nodeQueries level ≤ nodeQueries 16 := by
  have hp : 2 ^ level ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) h
  have h1 : 1 ≤ 2 ^ level := Nat.one_le_two_pow
  simp only [nodeQueries]
  have := Nat.mul_le_mul_right (29 + 174 + 1) hp
  omega

theorem total_treeNode (parameter : PublicParameter) (lay : LeanXmss.Layer) (seed : MasterSeed) :
    ∀ (level node : Nat), level ≤ 16 →
    IsTotalQueryBound (LeanXmss.KeyGenerationAndSigning.treeNodeWithHash parameter lay seed level node :
      RH HashSig.Digest) (nodeQueries 16) := fun level node h =>
  (queryCount_realTreeNode parameter lay seed level node).total.mono (nodeQueries_le h)

theorem total_treePath (parameter : PublicParameter) (lay : LeanXmss.Layer) (seed : MasterSeed)
    (key : LeanXmss.KeyIndex) :
    IsTotalQueryBound (LeanXmss.KeyGenerationAndSigning.treePathWithHash parameter lay seed key :
      RH (Fin LeanXmss.layerHeight → HashSig.Digest)) (16 * nodeQueries 16) := by
  unfold LeanXmss.KeyGenerationAndSigning.treePathWithHash
  rw [sequenceFin_eq]
  refine (total_sequenceFin (nodeQueries 16) _ fun level =>
    total_treeNode _ _ _ _ _ (by have := level.isLt; simp only [LeanXmss.layerHeight] at this; omega)).mono ?_
  simp only [LeanXmss.layerHeight, le_refl]

/-- One layer's signature: the randomizer, the trials, the chains and the path. -/
def realLayerCalls : Nat := 1 + (2 ^ 32 + 203) + 16 * nodeQueries 16

theorem total_signLayer (secretKey : LeanXmss.SchemeSeedKey) (lay : LeanXmss.Layer) (key : LeanXmss.KeyIndex)
    (message : HashInput) :
    IsTotalQueryBound (LeanXmss.KeyGenerationAndSigning.signLayerWithHash secretKey lay key message :
      RH (Option LeanXmss.LayerSignature)) realLayerCalls := by
  unfold LeanXmss.KeyGenerationAndSigning.signLayerWithHash LeanXmss.KeyGenerationAndSigning.otsSignWithHash
  rw [bind_assoc]
  refine tbind (total_thWithHash _ _ _) (b := (2 ^ 32 + 203) + 16 * nodeQueries 16) (fun base => ?_)
    (by simp only [realLayerCalls]; omega)
  refine tbind (total_otsSignFrom _ _ _ _ _ _ _ _) (b := 16 * nodeQueries 16) (fun result => ?_) le_rfl
  split
  · exact tbind (total_treePath _ _ _ _) (b := 0) (fun _ => tpure _ _) le_rfl
  · exact tpure _ _

theorem total_treeNode_root (parameter : PublicParameter) (lay : LeanXmss.Layer) (seed : MasterSeed)
    (node : Nat) :
    IsTotalQueryBound (LeanXmss.KeyGenerationAndSigning.treeNodeWithHash parameter lay seed LeanXmss.layerHeight
      node : RH HashSig.Digest) (nodeQueries 16) := by
  have h := total_treeNode parameter lay seed
  exact h _ _ (by simp [LeanXmss.layerHeight])

/-- A real signature: two layers and the bottom tree's root. -/
def realSignCalls : Nat := realLayerCalls + (nodeQueries 16 + realLayerCalls)

theorem total_signWithHash (secretKey : LeanXmss.SchemeSeedKey) (index : LeanXmss.LeafIndex)
    (message : HashSig.Message) :
    IsTotalQueryBound (LeanXmss.KeyGenerationAndSigning.signWithHash secretKey index message :
      RH (Option LeanXmss.Signature)) realSignCalls := by
  unfold LeanXmss.KeyGenerationAndSigning.signWithHash
  refine tbind (total_signLayer _ _ _ _) (b := nodeQueries 16 + realLayerCalls) (fun bottom => ?_) le_rfl
  split
  · refine tbind (total_treeNode_root secretKey.parameter LeanXmss.bottomLayer secretKey.schemeSeed _)
      (b := realLayerCalls) (fun root => ?_) le_rfl
    refine tbind (total_signLayer _ _ _ _) (b := 0) (fun top => ?_) (by omega)
    split <;> exact tpure _ _
  · exact tpure _ _

theorem queryCount_keygen (keySeed : MasterSeed) :
    QueryCount (LeanXmss.KeyGenerationAndSigning.keygenFromSeedWithHash keySeed : RH _) keygenQueries := by
  rw [keygenFromSeed_eq, show keygenQueries = 1 + (keygenQueries - 1) by decide]
  have h := (queryCount_oracleHash (LeanXmss.seedTag ++ HashSig.littleEndianBytes 32 keySeed)).bind
    (f := realKeygen) fun seed => queryCount_realKeygen seed
  exact h

/-! ## Verification -/

theorem total_treeFold (parameter : PublicParameter) (lay : LeanXmss.Layer) (key : LeanXmss.KeyIndex)
    (path : Fin LeanXmss.layerHeight → HashSig.Digest) :
    ∀ (levels : Nat) (value : HashSig.Digest),
      IsTotalQueryBound (LeanXmss.Verification.treeFoldWithHash parameter lay key path levels value :
        RH HashSig.Digest) levels
  | 0, _ => tpure _ _
  | levels + 1, value => by
      rw [LeanXmss.Verification.treeFold_eq_succ]
      refine tbind (total_treeFold parameter lay key path levels value) (b := 1) (fun current => ?_) le_rfl
      split <;> · dsimp only; split <;> exact (queryCount_realHash _ _ _).total

theorem total_otsLeaf (parameter : PublicParameter) (lay : LeanXmss.Layer) (key : LeanXmss.KeyIndex)
    (message : HashInput) (randomness : HashSig.Randomizer) (values : LeanXmss.ChainIndex → HashSig.Digest) :
    IsTotalQueryBound (LeanXmss.Verification.otsLeafWithHash parameter lay key message randomness values :
      RH (Option HashSig.Digest)) (1 + (174 + 1)) := by
  unfold LeanXmss.Verification.otsLeafWithHash
  refine tbind (queryCount_realHash _ _ _).total (b := 174 + 1) (fun digest => ?_) le_rfl
  split
  · refine tbind (total_chains fun chain => total_realChainWalk _ _ _ _ _ _ ?_ _) (b := 1)
      (fun endpoints => ?_) le_rfl
    · have := (‹LeanXmss.Encoding› chain).isLt
      simp only [HashSig.chainLength, HashSig.winternitzBits, chainLength, winternitzBits] at this ⊢
      omega
    · exact tbind (queryCount_realHash _ _ _).total (b := 0) (fun _ => tpure _ _) le_rfl
  · exact tpure _ _

/-- One layer of verification: the digest, the chains, the leaf and the path. -/
def realLayerVerifyCalls : Nat := 1 + (174 + 1) + 16

theorem total_layerRoot (parameter : PublicParameter) (lay : LeanXmss.Layer) (key : LeanXmss.KeyIndex)
    (message : HashInput) (part : LeanXmss.LayerSignature) :
    IsTotalQueryBound (LeanXmss.Verification.layerRootWithHash parameter lay key message part :
      RH (Option HashSig.Digest)) realLayerVerifyCalls := by
  unfold LeanXmss.Verification.layerRootWithHash
  refine tbind (total_otsLeaf _ _ _ _ _ _) (b := 16) (fun leaf => ?_) le_rfl
  split
  · refine tbind ((total_treeFold _ _ _ _ _ _).mono (show LeanXmss.layerHeight ≤ 16 by
      simp only [LeanXmss.layerHeight, le_refl])) (b := 0) (fun _ => tpure _ _) le_rfl
  · exact tpure _ _

/-- Verification: two layers. -/
def realVerifyCalls : Nat := realLayerVerifyCalls + realLayerVerifyCalls

theorem total_verifyWithHash (publicKey : HashSig.PublicKey) (message : HashSig.Message)
    (signature : LeanXmss.Signature) :
    IsTotalQueryBound (LeanXmss.Verification.verifyWithHash publicKey message signature : RH Bool)
      realVerifyCalls := by
  unfold LeanXmss.Verification.verifyWithHash
  refine tbind (total_layerRoot _ _ _ _ _) (b := realLayerVerifyCalls) (fun bottom => ?_) le_rfl
  split
  · exact tbind (total_layerRoot _ _ _ _ _) (b := 0) (fun top => by split <;> exact tpure _ _) le_rfl
  · exact tpure _ _

/-! ## The real game -/

theorem realOwn_iff (t : (LeanXmss.OracleWorld + LeanXmss.SigningOracleSpec).Domain) :
    (t matches .inl (.inr _)) = true ↔ OnWorld IsWorldHashQuery t := by
  rcases t with (_ | _) | _ <;> simp [OnWorld, IsWorldHashQuery]

theorem real_forward_bound (t : LeanXmss.OracleWorld.Domain) :
    IsQueryBoundP ((QueryImpl.ofLift LeanXmss.OracleWorld (WriterT (QueryLog LeanXmss.SigningOracleSpec)
      (OracleComp LeanXmss.OracleWorld))) t).run IsWorldHashQuery (if IsWorldHashQuery t then 1 else 0) := by
  change IsQueryBoundP ((fun a => (a, (∅ : QueryLog LeanXmss.SigningOracleSpec))) <$>
    (liftM (LeanXmss.OracleWorld.query t) : OracleComp LeanXmss.OracleWorld _)) IsWorldHashQuery _
  rw [isQueryBoundP_map_iff, ← bind_pure (liftM _), isQueryBoundP_query_bind_iff]
  refine ⟨?_, fun _ => isQueryBoundP_pure _ _ _⟩
  by_cases h : IsWorldHashQuery t <;> simp [h]

theorem real_signing_bound (secretKey : LeanXmss.SchemeSeedKey) (request : LeanXmss.SigningRequest) :
    IsQueryBoundP (LeanXmss.Security.signingOracle secretKey request).run IsWorldHashQuery realSignCalls := by
  simp only [LeanXmss.Security.signingOracle, QueryImpl.withLogging_apply]
  simp [WriterT.run_bind, WriterT.run_liftM, WriterT.run_tell]
  exact isQueryBoundP_liftM_of_total _ _ (total_signWithHash _ _ _)

/-- The real game's hash calls: key generation, the adversary's own, its requests' and verification. -/
theorem realGame_bound (adversary : LeanXmss.Security.Adversary) (q s : Nat)
    (hadv : LeanXmss.Security.AdversaryHashQueryBound adversary q)
    (hsign : LeanXmss.Security.SigningRequestBound adversary s) :
    IsQueryBoundP (LeanXmss.Security.gameCore adversary : OracleComp OracleWorld Bool) IsWorldHashQuery
      (keygenQueries + (q + s * realSignCalls) + realVerifyCalls) := by
  unfold LeanXmss.Security.gameCore
  rw [show keygenQueries + (q + s * realSignCalls) + realVerifyCalls =
    0 + (keygenQueries + ((q + s * realSignCalls) + (realVerifyCalls + 0))) by omega]
  refine isQueryBoundP_bind (isQueryBoundP_liftM_probComp _ _) fun seed _ => ?_
  refine isQueryBoundP_bind (isQueryBoundP_liftM_of_total _ _ (queryCount_keygen seed).total) fun keys _ => ?_
  obtain ⟨publicKey, secretKey⟩ := keys
  refine isQueryBoundP_bind (isQueryBoundP_simulateQ_writer_run IsWorldHashQuery _ realSignCalls
    real_forward_bound (real_signing_bound secretKey) _ q s
    ((isQueryBoundP_congr_pred realOwn_iff).mp (hadv _))
    ((isQueryBoundP_congr_pred fun t => by rcases t with _ | _ <;> simp [OnSecond]).mp (hsign _)))
    fun result _ => ?_
  obtain ⟨forgery, log⟩ := result
  exact isQueryBoundP_bind (isQueryBoundP_liftM_of_total _ _ (total_verifyWithHash _ _ _)) fun _ _ =>
    isQueryBoundP_pure _ _ _

theorem realGame_hasHashQueryBound (adversary : LeanXmss.Security.Adversary) (q s : Nat)
    (hadv : LeanXmss.Security.AdversaryHashQueryBound adversary q)
    (hsign : LeanXmss.Security.SigningRequestBound adversary s) :
    LeanXmss.Security.HasHashQueryBound adversary (keygenQueries + (q + s * realSignCalls) + realVerifyCalls) := by
  intro result hresult
  have h := hashQueryBound_of_isQueryBoundP _ _ (realGame_bound adversary q s hadv hsign) ∅
  simp only [HashQueryBound, simulateQ_countHashQueries] at h
  exact h result hresult

end XmssSecurity.Bridge
