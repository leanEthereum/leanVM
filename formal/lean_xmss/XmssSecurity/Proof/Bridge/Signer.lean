import XmssSecurity.Proof.Bridge.Real

/-!
# The real signer

Under the prepared cache the real signer is the model's table signer: it derives the same randomizer
base, makes the same trials, and everything it recomputes after a codeword (the chains, the paths,
the bottom root and the whole top signature) is cached, so it erases to the stored values.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Bridge

open Seeded DeterministicSigning

set_option backward.isDefEq.respectTransparency false

theorem xor_one_lt {n k : Nat} (hn : n < 2 ^ k) (hk : 1 ≤ k) : Nat.xor n 1 < 2 ^ k :=
  Nat.xor_lt_two_pow hn (Nat.one_lt_two_pow (by omega))

namespace Prepared

variable {seed : MasterSeed} {d : Derivations}
  {result : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec}
  {cache : QueryCache HashSpec}

theorem realTopSignFrom (h : Prepared seed d result cache) (key : TopIndex) (base : Randomness)
    (attempts trial : Nat) (res : Option (Randomness × Encoding))
    (hmodel : Resolves cache (Concrete.topSignFrom d.parameter key (h.root key) base attempts trial) res) :
    Resolves cache (LeanXmss.Seeded.otsSignFrom d.parameter LeanXmss.topLayer (topKey key) seed
        (LeanXmss.bytesLE 16 (h.root key)) base attempts trial :
          OracleComp LeanXmss.HashSpec (Option (LeanXmss.Randomness × (LeanXmss.ChainIndex → LeanXmss.Digest))))
      (res.map fun p => (p.1, fun chain => (modelSecretKey d result).topChainValue key chain (p.2 chain))) := by
  induction attempts generalizing trial res with
  | zero =>
      rw [← hmodel.pure_inv]
      exact .pure _
  | succ attempts ih =>
      rw [Concrete.topSignFrom] at hmodel
      rw [LeanXmss.Seeded.otsSignFrom]
      rw [messageDigest_top]
      obtain ⟨digest, hdigest, hrest⟩ := hmodel.of_bind
      refine hdigest.bind ?_
      rw [decode_eq]
      cases hdec : TargetSum.decodeDigest digest with
      | none =>
          rw [hdec] at hrest
          exact ih _ _ hrest
      | some encoding =>
          rw [hdec] at hrest
          rw [← hrest.pure_inv]
          refine ((otsSecrets_top seed d key).mono h.prog_le).bind ?_
          rw [sequenceFin_eq]
          refine (Resolves.sequenceFin fun chain => ?_).bind (.pure _)
          rw [chainWalk_top]
          exact h.topChain key chain (encoding chain)

theorem realTopPath (h : Prepared seed d result cache) (key : TopIndex) :
    Resolves cache (LeanXmss.Seeded.treePath d.parameter LeanXmss.topLayer seed (topKey key) :
        OracleComp LeanXmss.HashSpec (Fin LeanXmss.layerHeight → LeanXmss.Digest))
      (fun level => (modelSecretKey d result).topTreeValue level.castSucc (Concrete.topPathNode key level)) := by
  unfold LeanXmss.Seeded.treePath
  rw [sequenceFin_eq]
  refine Resolves.sequenceFin fun level => ?_
  have hlevel : level.val < 16 := level.isLt
  have hb : key.val / 2 ^ level.val < 2 ^ (16 - level.val) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, show 16 - level.val + level.val = 16 by omega]
    exact lt_of_lt_of_eq key.isLt (by norm_num [topLifetime, treeHeight])
  exact h.realTopNode level.val (by omega) _ (xor_one_lt hb (by omega))

theorem realBottomPath (h : Prepared seed d result cache) (index : LeafIndex) :
    Resolves cache (LeanXmss.Seeded.treePath d.parameter LeanXmss.bottomLayer seed index :
        OracleComp LeanXmss.HashSpec (Fin LeanXmss.layerHeight → LeanXmss.Digest))
      (fun level => (modelSecretKey d result).treeValue level.castSucc (Concrete.authenticationPathNode index level)) := by
  unfold LeanXmss.Seeded.treePath
  rw [sequenceFin_eq]
  refine Resolves.sequenceFin fun level => ?_
  have hlevel : level.val < 16 := level.isLt
  have hb : index.val / 2 ^ level.val < 2 ^ (32 - level.val) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, show 32 - level.val + level.val = 32 by omega]
    exact lt_of_lt_of_eq index.isLt (by norm_num [lifetime, treeHeight])
  exact h.realBottomNode level.val (by omega) _ (xor_one_lt hb (by omega))

/-- The real top signature of bottom tree `b`, as the key stores it. -/
theorem realTopLayer (h : Prepared seed d result cache) (key : TopIndex) :
    Resolves cache (LeanXmss.Seeded.signLayer ⟨seed, d.parameter, result.1.1⟩ LeanXmss.topLayer (topKey key)
        (LeanXmss.bytesLE 16 (h.root key)) :
          OracleComp LeanXmss.HashSpec (Option LeanXmss.LayerSignature))
      (((modelSecretKey d result).topSigned key).map fun _ => layerToReal (Concrete.topPart (modelSecretKey d result) key)) := by
  unfold LeanXmss.Seeded.signLayer LeanXmss.Seeded.otsSign LeanXmss.deriveRandomizer
  simp only [bind_assoc, pure_bind]
  have hbase : cache (topRndInput d.parameter seed (key, h.root key)) = some (d.topRnd (key, h.root key)) :=
    h.prog_le (progCache_topRnd seed d (key, h.root key))
  change Resolves cache (liftM (HashSpec.query (topRndInput d.parameter seed (key, h.root key))) >>= _) _
  refine .query _ _ hbase _ _ ?_
  have hgrind := h.realTopSignFrom key _ signingAttemptLimit 0 _ (h.topSign key)
  refine hgrind.bind ?_
  cases hsigned : result.1.2 key with
  | none =>
      have : (modelSecretKey d result).topSigned key = none := hsigned
      rw [this]
      exact .pure _
  | some signed =>
      obtain ⟨randomness, encoding⟩ := signed
      have hsk : (modelSecretKey d result).topSigned key = some (randomness, encoding) := hsigned
      refine (h.realTopPath key).bind ?_
      rw [hsk]
      simp only [Option.map_some, Concrete.topPart, hsk, layerToReal]
      exact .pure _


theorem erases_otsSignFrom_bottom (h : Prepared seed d result cache) (index : LeafIndex) (message : Message)
    (base : Randomness)
    (K : Option (LeanXmss.Randomness × (LeanXmss.ChainIndex → LeanXmss.Digest)) →
      OracleComp LeanXmss.HashSpec (Option LeanXmss.Signature))
    (hnone : K none = pure none)
    (hsome : ∀ (randomness : Randomness) (encoding : Encoding),
      Resolves cache (K (some (randomness, fun chain =>
          (modelSecretKey d result).chainValue index chain (encoding chain))))
        (Option.map (toRealSig index) (if Concrete.topSignedAt (modelSecretKey d result) index then
          some (Concrete.precomputedSignWithEncoding (modelSecretKey d result) index randomness encoding)
          else none)))
    (attempts trial : Nat) :
    Erases cache ((LeanXmss.Seeded.otsSignFrom d.parameter LeanXmss.bottomLayer index seed
        (LeanXmss.bytesLE 32 message) base attempts trial : OracleComp LeanXmss.HashSpec _) >>= K)
      (Option.map (toRealSig index) <$> ((tableSignFrom base (modelSecretKey d result) index message
        attempts trial : OracleComp HashSpec (Option Signature)) >>= fun r =>
          pure (if Concrete.topSignedAt (modelSecretKey d result) index then r else none))) := by
  induction attempts generalizing trial with
  | zero =>
      simp only [LeanXmss.Seeded.otsSignFrom, tableSignFrom, pure_bind, hnone, ite_self, map_pure,
        Option.map_none]
      exact .pure _
  | succ attempts ih =>
      rw [LeanXmss.Seeded.otsSignFrom, tableSignFrom]
      simp only [Concrete.precomputedSignAttempt, bind_assoc, map_bind]
      rw [messageDigest_bottom]
      refine (Erases.refl cache _).bind _ _ fun digest => ?_
      rw [decode_eq]
      cases hdec : TargetSum.decodeDigest digest with
      | none =>
          simp only [pure_bind]
          simpa only [map_bind] using ih (trial + 1)
      | some encoding =>
          simp only [pure_bind, map_pure, bind_assoc]
          apply erases_pure_of_resolves
          refine ((otsSecrets_bottom seed d index).mono h.prog_le).bind ?_
          rw [sequenceFin_eq]
          refine (Resolves.sequenceFin (v := fun chain =>
            (modelSecretKey d result).chainValue index chain (encoding chain)) fun chain => ?_).bind ?_
          · rw [chainWalk_bottom]
            exact h.chain index chain (encoding chain)
          · exact hsome _ encoding

theorem bottomKey_lt (index : LeafIndex) : (topKeyOf index).val < 2 ^ (32 - 16) := by
  exact lt_of_lt_of_eq (topKeyOf index).isLt (by norm_num [topLifetime, treeHeight])

theorem signLayer_bottom (secretKey : LeanXmss.Seeded.SecretKey) (key : LeanXmss.KeyIndex)
    (message : HashInput) :
    (LeanXmss.Seeded.signLayer secretKey LeanXmss.bottomLayer key message :
        OracleComp LeanXmss.HashSpec (Option LeanXmss.LayerSignature)) = (do
      let base ← LeanXmss.deriveRandomizer secretKey.parameter LeanXmss.bottomLayer key secretKey.seed message
      let result ← LeanXmss.Seeded.otsSignFrom secretKey.parameter LeanXmss.bottomLayer key secretKey.seed
        message base LeanXmss.randomizerAttemptLimit 0
      match result with
      | some (randomness, values) => do
          let path ← LeanXmss.Seeded.treePath secretKey.parameter LeanXmss.bottomLayer secretKey.seed key
          return some ⟨randomness, values, path⟩
      | none => return none) := by
  rw [LeanXmss.Seeded.signLayer, LeanXmss.Seeded.otsSign, bind_assoc]
  apply bind_congr
  intro base
  apply bind_congr
  intro result
  rcases result with _ | ⟨randomness, values⟩ <;> rfl

theorem root_resolves (h : Prepared seed d result cache) (index : LeafIndex) :
    Resolves cache (LeanXmss.Seeded.treeNode d.parameter LeanXmss.bottomLayer seed LeanXmss.layerHeight
        (topKey (topKeyOf index)).val : OracleComp LeanXmss.HashSpec LeanXmss.Digest)
      (h.root (topKeyOf index)) := by
  have hroot := h.realBottomNode 16 le_rfl (topKeyOf index).val (bottomKey_lt index)
  unfold Prepared.root
  rw [Prepared.bottomRootNode_eq]
  exact hroot

/-- The real signer erases to the table signer, its signatures translated. -/
theorem erases_sign (h : Prepared seed d result cache) (index : LeafIndex) (message : Message) :
    Erases cache (LeanXmss.Seeded.sign ⟨seed, d.parameter, result.1.1⟩ index message :
        OracleComp LeanXmss.HashSpec (Option LeanXmss.Signature))
      (Option.map (toRealSig index) <$> (tableSign d.rnd (modelSecretKey d result) index message :
        OracleComp HashSpec (Option Signature))) := by
  rw [LeanXmss.Seeded.sign]
  simp only [keyAt_bottom, keyAt_top, signLayer_bottom, LeanXmss.deriveRandomizer, bind_assoc, pure_bind]
  unfold tableSign
  have hR0 : cache (rndInput d.parameter seed ⟨index, message⟩) = some (d.rnd ⟨index, message⟩) :=
    h.prog_le (progCache_rnd seed d ⟨index, message⟩)
  change Erases cache (liftM (HashSpec.query (rndInput d.parameter seed ⟨index, message⟩)) >>= _) _
  refine .skip _ _ hR0 _ _ ?_
  refine erases_otsSignFrom_bottom h index message _ _ ?_ ?_ signingAttemptLimit 0
  · rfl
  · intro randomness encoding
    simp only [bind_assoc]
    refine (h.realBottomPath index).bind ?_
    simp only [pure_bind]
    refine (h.root_resolves index).bind ?_
    refine (h.realTopLayer (topKeyOf index)).bind ?_
    cases hsigned : (modelSecretKey d result).topSigned (topKeyOf index) with
    | none =>
        have hat : Concrete.topSignedAt (modelSecretKey d result) index = false := by
          simp [Concrete.topSignedAt, hsigned]
        simp only [Option.map_none, hat]
        exact .pure _
    | some signed =>
        have hat : Concrete.topSignedAt (modelSecretKey d result) index = true := by
          simp [Concrete.topSignedAt, hsigned]
        simp only [Option.map_some, hat, ite_true]
        apply Resolves.pure

end Prepared

end XmssSecurity.Bridge
