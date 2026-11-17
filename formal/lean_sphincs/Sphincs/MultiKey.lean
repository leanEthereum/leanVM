module

public import FORS.Main
public import Sphincs.AdvRpm
public import Common.MultiKey.Main

@[expose] public section

/-!
# leanSPHINCS against many keys

`Sphincs.leanSphincs_multiKey`: against `k ≤ 2^32` keys of the statement's leanSPHINCS
(`Common.SufCma.MultiKeyStronglyUnforgeable`), an adversary that itself makes at most `q` calls of
`π` and `π⁻¹` and at most `1,182,000,000` signing requests to each key forges under one of them with
probability at most `k · (q + 2^19 + k) · 2^-127`.

The generic theorem (`Common.SufCma.MultiKey.romBoundMulti_of_romBoundAdv`) is applied to
upstream's model (`Sphincs.Model.modelScheme`), whose secret key carries the public parameter. The
crate's copy (`Sphincs.Model.crateScheme`) does not satisfy its separation facts: its secret key is
the seed alone, and its signer derives the parameter again from the seed (`FORS.Crate.expandKey`,
the key seed input `leanSPHINCS ‖ SK.seed ‖ 0`), so on a path where that query is answered unlike
at key generation it asks inputs carrying another parameter, which its key neither owns nor queried
at key generation (`QueriesIn` quantifies over every answer).

* **Ownership** (`FORS.Owned.Owns`): the inputs are told apart by their length, a message digest
  call (84 bytes) carrying the parameter at bytes 16 to 32, a randomizer (93 bytes) at bytes 32 to
  48, a key seed derivation (44 bytes) none, every other input (a tweakable hash, `48 + 16`, `+ 20`,
  `+ 32`, `+ 16 k` or `+ 1024` bytes, or a seed derivation, 80 bytes) at bytes 0 to 16. The model's
  signer and the verifier ask only inputs their key owns (`FORS.Owned.Seeded.only_sign`,
  `FORS.Owned.only_verify`), key generation the two key seed derivations of its seed and inputs its
  key owns (`keyFacts_keygenFromSeed`): `separation`.
* **The clash** (`prob_clash_le`): two keys clash only with equal seeds or equal public parameters
  (`clash_imp`); a fresh key's seed is uniform and its parameter the truncation of a fresh uniform
  answer, `2^-256 + 2^-128 ≤ 2^-127`.
* **The crate's copy**: the model's `k` keys and the crate's win as often in the random-oracle
  model (`staticSwapMulti`, `Common.SufCma.StaticSwap` for the `k` keys); then
  `Common.SufCma.multiKey_of_romBoundMulti` moves the bound to `π` (`crate_multiKey`), and the
  statement's game is the crate's copy's against the adversary read through the maps
  (`multiKey_forgeryGame_eq`), key by key.
-/

open OracleComp OracleSpec ENNReal Common Common.SufCma

namespace FORS.Owned

variable [Params]

open Concrete

attribute [local irreducible] digestAttemptLimit encodingAttemptLimit

/-- **The inputs a public parameter owns**, told apart by their length: a message digest call
(84 bytes) carries it at bytes 16 to 32, a randomizer (93 bytes) at bytes 32 to 48, a key seed
derivation (44 bytes) none, every other input (a tweakable hash, a seed derivation) at bytes 0 to
16. -/
def Owns (parameter : PublicParameter) (input : HashInput) : Prop :=
  if input.length = 44 then False
  else if input.length = 84 then (input.drop 16).take 16 = bytesLE 16 parameter
  else if input.length = 93 then (input.drop 32).take 16 = bytesLE 16 parameter
  else input.take 16 = bytesLE 16 parameter

instance (parameter : PublicParameter) : DecidablePred (Owns parameter) := fun input => by
  unfold Owns
  infer_instance

/-- An input has at most one owner. -/
theorem owns_unique {parameter parameter' : PublicParameter} {input : HashInput}
    (h : Owns parameter input) (h' : Owns parameter' input) : parameter = parameter' := by
  unfold Owns at h h'
  split_ifs at h h' <;> exact bytesLE_injective (h.symm.trans h')

theorem owns_iff_take {parameter : PublicParameter} {input : HashInput} (h44 : input.length ≠ 44)
    (h84 : input.length ≠ 84) (h93 : input.length ≠ 93) :
    Owns parameter input ↔ input.take 16 = bytesLE 16 parameter := by
  unfold Owns
  split_ifs <;> first | exact Iff.rfl | (exfalso; omega)

theorem owns_iff_84 {parameter : PublicParameter} {input : HashInput} (h : input.length = 84) :
    Owns parameter input ↔ (input.drop 16).take 16 = bytesLE 16 parameter := by
  unfold Owns
  split_ifs <;> first | exact Iff.rfl | (exfalso; omega)

theorem owns_iff_93 {parameter : PublicParameter} {input : HashInput} (h : input.length = 93) :
    Owns parameter input ↔ (input.drop 32).take 16 = bytesLE 16 parameter := by
  unfold Owns
  split_ifs <;> first | exact Iff.rfl | (exfalso; omega)

theorem not_owns_of_length {parameter : PublicParameter} {input : HashInput}
    (h : input.length = 44) : ¬Owns parameter input := by
  unfold Owns
  split_ifs
  exact id

theorem not_owns_keySeedInput (parameter : PublicParameter) (seed : MasterSeed) (domain : Nat) :
    ¬Owns parameter (keySeedInput seed domain) :=
  not_owns_of_length (Security.keySeedInput_length seed domain)

theorem owns_tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) (h : payload.length ≠ 36 ∧ payload.length ≠ 45) :
    Owns parameter (tweakableHashInput parameter domain payload) := by
  have hl := tweakableHashInput_length parameter domain payload
  rw [owns_iff_take (by omega) (by omega) (by omega)]
  simp only [tweakableHashInput, List.append_assoc]
  exact List.take_left' (bytesLE_parameter_length parameter)

theorem owns_keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : Owns parameter (keygenHashInput parameter domain seed) := by
  have hl := keygenHashInput_length parameter domain seed
  rw [owns_iff_take (by omega) (by omega) (by omega)]
  simp only [keygenHashInput, List.append_assoc]
  exact List.take_left' (bytesLE_parameter_length parameter)

theorem owns_randomizerHashInput (prf : HashOutput) (parameter : PublicParameter)
    (message : Message) : Owns parameter (randomizerHashInput prf parameter message) := by
  rw [owns_iff_93 (Security.randomizerHashInput_length prf parameter message)]
  simp only [randomizerHashInput, List.append_assoc]
  rw [List.drop_left' (bytesLE_length 32 prf)]
  exact List.take_left' (bytesLE_parameter_length parameter)

theorem owns_messageDigestInput (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) (call : DigestCall) :
    Owns parameter (messageDigestInput parameter root message randomness call) := by
  rw [owns_iff_84 (Security.messageDigestInput_length parameter root message randomness call)]
  simp only [messageDigestInput, List.append_assoc]
  rw [List.drop_left' (bytesLE_digest_length randomness)]
  exact List.take_left' (bytesLE_parameter_length parameter)

/-- Every query of the computation is owned by `parameter`. -/
abbrev Only (parameter : PublicParameter) {α : Type} (oa : OracleComp HashSpec α) : Prop :=
  QueriesIn (Owns parameter) (oa : OracleComp SchemeHashSpec α)

variable {parameter : PublicParameter}

theorem Only.pure' {α : Type} (value : α) : Only parameter (pure value : OracleComp HashSpec α) :=
  trivial

theorem Only.bind {α β : Type} {oa : OracleComp HashSpec α} {next : α → OracleComp HashSpec β}
    (h : Only parameter oa) (hnext : ∀ value, Only parameter (next value)) :
    Only parameter (oa >>= next) :=
  queriesIn_bind h hnext

theorem Only.ite {α : Type} (condition : Prop) [Decidable condition]
    {left right : OracleComp HashSpec α} (hleft : Only parameter left)
    (hright : Only parameter right) : Only parameter (if condition then left else right) := by
  split
  · exact hleft
  · exact hright

theorem Only.query {input : HashInput} (h : Owns parameter input) :
    Only parameter (oracleHash input : OracleComp HashSpec HashOutput) :=
  queriesIn_query h

theorem Only.tweakableHash (domain : HashDomain) (payload : HashInput)
    (h : payload.length ≠ 36 ∧ payload.length ≠ 45) :
    Only parameter (Concrete.tweakableHash parameter domain payload :
      OracleComp HashSpec Digest) := by
  unfold Concrete.tweakableHash
  exact Only.bind (Only.query (owns_tweakableHashInput _ _ _ h)) fun _ ↦ Only.pure' _

theorem Only.deriveKey (domain : KeygenDomain) (seed : MasterSeed) :
    Only parameter (FORS.deriveKey parameter domain seed : OracleComp HashSpec Digest) := by
  unfold FORS.deriveKey
  exact Only.bind (Only.query (owns_keygenHashInput _ _ _)) fun _ ↦ Only.pure' _

theorem Only.deriveRandomizer (prf : HashOutput) (message : Message) :
    Only parameter (FORS.deriveRandomizer prf parameter message :
      OracleComp HashSpec (Randomness × Randomness)) := by
  unfold FORS.deriveRandomizer
  exact Only.bind (Only.query (owns_randomizerHashInput _ _ _)) fun _ ↦ Only.pure' _

theorem Only.sequenceFin {α : Type} {n : Nat} (computation : Fin n → OracleComp HashSpec α)
    (h : ∀ i, Only parameter (computation i)) :
    Only parameter (Concrete.sequenceFin computation) := by
  induction n with
  | zero => exact Only.pure' _
  | succ n ih =>
      rw [Concrete.sequenceFin]
      exact Only.bind (h 0) fun _ ↦ Only.bind (ih _ fun i ↦ h i.succ) fun _ ↦ Only.pure' _

theorem Only.chainWalk (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (start : Nat) : ∀ steps value, Only parameter
      (Concrete.chainWalk parameter lay tree leaf chainIdx start steps value :
        OracleComp HashSpec Digest)
  | 0, _ => Only.pure' _
  | steps + 1, value => by
      rw [Concrete.chainWalk]
      refine Only.bind (Only.chainWalk lay tree leaf chainIdx start steps value) fun _ ↦ ?_
      split
      · exact Only.tweakableHash _ _ (by rw [bytesLE_digest_length]; omega)
      · exact Only.pure' _

theorem Only.leafHash (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest) :
    Only parameter (Concrete.leafHash parameter lay tree leaf endpoints :
      OracleComp HashSpec Digest) :=
  Only.tweakableHash _ _ (by rw [leafPayload_length]; omega)

theorem Only.encode (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : HashInput)
    (hmsg : message.length = 16) (counter : Counter) :
    Only parameter (Concrete.encode parameter lay tree leaf message counter :
      OracleComp HashSpec (Option Encoding)) := by
  unfold Concrete.encode
  exact Only.bind (Only.tweakableHash _ _ (by
    have := bytesBE_length 4 counter
    rw [List.length_append]
    omega)) fun _ ↦ Only.pure' _

theorem Only.otsLeaf (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : HashInput)
    (hmsg : message.length = 16) (counter : Counter) (values : ChainIndex → Digest) :
    Only parameter (Concrete.otsLeaf parameter lay tree leaf message counter values :
      OracleComp HashSpec (Option Digest)) := by
  unfold Concrete.otsLeaf
  refine Only.bind (Only.encode _ _ _ _ hmsg _) fun encoding ↦ ?_
  rcases encoding with _ | encoding
  · exact Only.pure' _
  · exact Only.bind (Only.sequenceFin _ fun _ ↦ Only.chainWalk _ _ _ _ _ _ _) fun _ ↦
      Only.bind (Only.leafHash _ _ _ _) fun _ ↦ Only.pure' _

theorem Only.treeFold (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (path : Nat → Digest) :
    ∀ levels value, Only parameter (Concrete.treeFold parameter lay tree leaf path levels value :
      OracleComp HashSpec Digest)
  | 0, _ => Only.pure' _
  | levels + 1, value => by
      rw [Concrete.treeFold]
      refine Only.bind (Only.treeFold lay tree leaf path levels value) fun _ ↦ ?_
      split <;> exact Only.tweakableHash _ _ (by rw [nodePayload_length]; omega)

theorem Only.forsLeafHash (index : Index) (κ : FTree) (leaf : FLeaf) (secret : Digest) :
    Only parameter (Concrete.forsLeafHash parameter index κ leaf secret :
      OracleComp HashSpec Digest) :=
  Only.tweakableHash _ _ (by rw [bytesLE_digest_length]; omega)

theorem Only.forsFold (index : Index) (κ : FTree) (leaf : FLeaf) (path : Fin forsHeight → Digest) :
    ∀ levels value, Only parameter (Concrete.forsFold parameter index κ leaf path levels value :
      OracleComp HashSpec Digest)
  | 0, _ => Only.pure' _
  | levels + 1, value => by
      rw [Concrete.forsFold]
      refine Only.bind (Only.forsFold index κ leaf path levels value) fun _ ↦ ?_
      dsimp only
      split_ifs
      · exact Only.tweakableHash _ _ (by rw [nodePayload_length]; omega)
      · exact Only.tweakableHash _ _ (by rw [nodePayload_length]; omega)
      · exact Only.pure' _

theorem Only.forsRecover (index : Index) (leaves : FTree → FLeaf) (opening : FTree → TreeOpening) :
    Only parameter (Concrete.forsRecover parameter index leaves opening :
      OracleComp HashSpec ForsKey) := by
  unfold Concrete.forsRecover Concrete.treeRecover
  exact Only.sequenceFin _ fun _ ↦ Only.bind (Only.forsLeafHash _ _ _ _) fun _ ↦
    Only.forsFold _ _ _ _ _ _

theorem Only.forsPublicKey (index : Index) (roots : ForsKey) :
    Only parameter (Concrete.forsPublicKey parameter index roots : OracleComp HashSpec Digest) :=
  Only.tweakableHash _ _ (by rw [rootsPayload_length]; omega)

theorem Only.messageDigestCall (root : Digest) (message : Message) (randomness : Randomness)
    (call : DigestCall) :
    Only parameter (Concrete.messageDigestCall parameter root message randomness call :
      OracleComp HashSpec HashOutput) :=
  Only.query (owns_messageDigestInput _ _ _ _ _)

theorem Only.messageDigest (root : Digest) (message : Message) (randomness : Randomness) :
    Only parameter (Concrete.messageDigest parameter root message randomness :
      OracleComp HashSpec MessageDigest) := by
  unfold Concrete.messageDigest
  exact Only.bind (Only.sequenceFin _ fun _ ↦ Only.messageDigestCall _ _ _ _) fun _ ↦
    Only.pure' _

attribute [local irreducible] Concrete.treeFold Concrete.chainWalk Concrete.otsLeaf
  Concrete.forsRecover Concrete.messageDigest

theorem Only.verifyLayers (index : Index) (signature : Signature) :
    ∀ (n : Nat) (message : HashInput), message.length = 16 →
      Only parameter (Concrete.verifyLayers parameter index signature n message :
        OracleComp HashSpec (Option Digest))
  | 0, _, _ => Only.pure' _
  | n + 1, message, hmsg => by
      rw [Concrete.verifyLayers]
      split
      · refine Only.bind (Only.otsLeaf _ _ _ _ hmsg _ _) fun value ↦ ?_
        rcases value with _ | value
        · exact Only.pure' _
        · refine Only.bind (Only.treeFold _ _ _ _ _ value) fun root ↦ ?_
          split
          · exact Only.pure' _
          · exact Only.verifyLayers index signature n _ (rootPayload_length root)
      · exact Only.pure' _

/-- **The verifier asks only inputs its public key's parameter owns.** -/
theorem only_verify (publicKey : PublicKey) (message : Message) (signature : Signature) :
    Only publicKey.parameter (Concrete.verify publicKey message signature :
      OracleComp HashSpec Bool) := by
  rw [Security.verify_eq_layers]
  refine Only.bind (Only.messageDigest _ _ _) fun digest ↦ ?_
  refine Only.bind (Only.forsRecover _ _ _) fun roots ↦ ?_
  refine Only.bind (Only.forsPublicKey _ _) fun key ↦ ?_
  refine Only.bind (Only.verifyLayers _ _ _ _ (rootPayload_length key)) fun value ↦ ?_
  rcases value with _ | value <;> exact Only.pure' _

namespace Seeded

open FORS.Seeded

theorem Only.otsSecrets (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) :
    Only parameter (otsSecrets parameter lay tree leaf seed :
      OracleComp HashSpec (ChainIndex → Digest)) :=
  Owned.Only.sequenceFin _ fun _ ↦ Owned.Only.deriveKey _ _

theorem Only.oneTimePublicKey (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (seed : MasterSeed) :
    Only parameter (oneTimePublicKey parameter lay tree leaf seed :
      OracleComp HashSpec (ChainIndex → Digest)) :=
  Owned.Only.bind (Only.otsSecrets _ _ _ _) fun _ ↦
    Owned.Only.sequenceFin _ fun _ ↦ Owned.Only.chainWalk _ _ _ _ _ _ _

theorem Only.otsSignFrom (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed)
    (message : HashInput) (hmsg : message.length = 16) :
    ∀ attempts counter, Only parameter (otsSignFrom parameter lay tree leaf seed message attempts
      counter : OracleComp HashSpec (Option (Counter × (ChainIndex → Digest))))
  | 0, _ => Owned.Only.pure' _
  | attempts + 1, counter => by
      rw [FORS.Seeded.otsSignFrom]
      refine Owned.Only.bind (Owned.Only.encode _ _ _ _ hmsg _) fun encoding ↦ ?_
      rcases encoding with _ | encoding
      · exact Only.otsSignFrom lay tree leaf seed message hmsg attempts (counter + 1)
      · exact Owned.Only.bind (Only.otsSecrets _ _ _ _) fun _ ↦
          Owned.Only.bind (Owned.Only.sequenceFin _ fun _ ↦ Owned.Only.chainWalk _ _ _ _ _ _ _)
            fun _ ↦ Owned.Only.pure' _

theorem Only.treeNode (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) :
    ∀ level nodeIdx, Only parameter (treeNode parameter lay tree seed level nodeIdx :
      OracleComp HashSpec Digest)
  | 0, nodeIdx => by
      rw [FORS.Seeded.treeNode]
      exact Owned.Only.bind (Only.oneTimePublicKey _ _ _ _) fun _ ↦ Owned.Only.leafHash _ _ _ _
  | level + 1, nodeIdx => by
      rw [FORS.Seeded.treeNode]
      exact Owned.Only.bind (Only.treeNode lay tree seed level _) fun _ ↦
        Owned.Only.bind (Only.treeNode lay tree seed level _) fun _ ↦
          Owned.Only.tweakableHash _ _ (by rw [nodePayload_length]; omega)

theorem Only.forsNode (index : Index) (κ : FTree) (seed : MasterSeed) :
    ∀ level node, Only parameter (forsNode parameter index κ seed level node :
      OracleComp HashSpec Digest)
  | 0, node => by
      rw [FORS.Seeded.forsNode]
      exact Owned.Only.bind (Owned.Only.deriveKey _ _) fun _ ↦ Owned.Only.forsLeafHash _ _ _ _
  | level + 1, node => by
      rw [FORS.Seeded.forsNode]
      refine Owned.Only.bind (Only.forsNode index κ seed level _) fun _ ↦
        Owned.Only.bind (Only.forsNode index κ seed level _) fun _ ↦ ?_
      split
      · exact Owned.Only.tweakableHash _ _ (by rw [nodePayload_length]; omega)
      · exact Owned.Only.pure' _

theorem Only.forsOpen (index : Index) (leaves : FTree → FLeaf) (seed : MasterSeed) :
    Only parameter (forsOpen parameter index leaves seed :
      OracleComp HashSpec (FTree → TreeOpening)) := by
  unfold FORS.Seeded.forsOpen FORS.Seeded.treeOpen
  exact Owned.Only.sequenceFin _ fun _ ↦
    Owned.Only.bind (Owned.Only.deriveKey _ _) fun _ ↦
      Owned.Only.bind (Owned.Only.sequenceFin _ fun _ ↦ Only.forsNode _ _ _ _ _) fun _ ↦
        Owned.Only.pure' _

theorem Only.surrogate (seed : MasterSeed) (level : Nat) :
    Only parameter (surrogate parameter seed level : OracleComp HashSpec Digest) := by
  unfold FORS.Seeded.surrogate
  split
  · exact Owned.Only.deriveKey _ _
  · exact Owned.Only.pure' _

theorem Only.spineNode (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) :
    ∀ steps, Only parameter (spineNode parameter lay tree seed steps : OracleComp HashSpec Digest)
  | 0 => by
      rw [FORS.Seeded.spineNode]
      exact Only.treeNode _ _ _ _ _
  | steps + 1 => by
      rw [FORS.Seeded.spineNode]
      refine Owned.Only.bind (Only.spineNode lay tree seed steps) fun _ ↦
        Owned.Only.bind (Only.surrogate _ _) fun _ ↦ ?_
      dsimp only
      exact Owned.Only.ite _
        (Owned.Only.tweakableHash _ _ (by rw [nodePayload_length]; omega))
        (Owned.Only.tweakableHash _ _ (by rw [nodePayload_length]; omega))

theorem Only.treeRoot (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) :
    Only parameter (treeRoot parameter lay tree seed : OracleComp HashSpec Digest) :=
  Only.spineNode _ _ _ _

theorem Only.treePath (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) (leaf : LeafIndex) :
    Only parameter (treePath parameter lay tree seed leaf :
      OracleComp HashSpec (Fin (layerHeight lay) → Digest)) :=
  Owned.Only.sequenceFin _ fun _ ↦ by
    split
    · exact Only.treeNode _ _ _ _ _
    · exact Only.surrogate _ _

end Seeded

end FORS.Owned

namespace FORS.Owned.Seeded

variable [Params]

open Concrete FORS.Seeded

attribute [local irreducible] digestAttemptLimit encodingAttemptLimit

theorem Only.signAttempt (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    Only secretKey.parameter (signAttempt secretKey message randomness :
      OracleComp HashSpec (Option Index)) := by
  unfold FORS.Seeded.signAttempt
  exact Owned.Only.bind (Owned.Only.messageDigestCall _ _ _ _) fun _ ↦
    Owned.Only.ite _ (Owned.Only.pure' _) (Owned.Only.pure' _)

attribute [local irreducible] FORS.Seeded.treeNode FORS.Seeded.forsNode FORS.Seeded.otsSignFrom
  FORS.Seeded.forsKey FORS.Seeded.treePath

theorem Only.signLayerWith (secretKey : SecretKey) (index : Index) (lay : Layer)
    (message : HashInput) (hmsg : message.length = 16) :
    Only secretKey.parameter (signLayerWith secretKey index lay message :
      OracleComp HashSpec (Option (LayerSignature lay))) := by
  unfold FORS.Seeded.signLayerWith FORS.Seeded.otsSign
  refine Owned.Only.bind (Only.otsSignFrom _ _ _ _ _ hmsg _ _) fun result ↦ ?_
  rcases result with _ | ⟨counter, values⟩
  · exact Owned.Only.pure' _
  · exact Owned.Only.bind (Only.treePath _ _ _ _) fun _ ↦ Owned.Only.pure' _

theorem Only.layerRecover (parameter : PublicParameter) (index : Index) (lay : Layer)
    (message : HashInput) (hmsg : message.length = 16) (part : LayerSignature lay) :
    Only parameter (layerRecover parameter index lay message part :
      OracleComp HashSpec (Option Digest)) := by
  unfold Concrete.layerRecover
  refine Owned.Only.bind (Owned.Only.otsLeaf _ _ _ _ hmsg _ _) fun value ↦ ?_
  rcases value with _ | value
  · exact Owned.Only.pure' _
  · exact Owned.Only.bind (Owned.Only.treeFold _ _ _ _ _ _) fun _ ↦ Owned.Only.pure' _

theorem Only.layerStep (secretKey : SecretKey) (index : Index) (lay : Layer) (below : Digest) :
    Only secretKey.parameter (layerStep secretKey index lay below :
      OracleComp HashSpec (Option (LayerSignature lay × Digest))) := by
  unfold FORS.Seeded.layerStep
  refine Owned.Only.bind (Only.signLayerWith _ _ _ _ (rootPayload_length below)) fun part ↦ ?_
  rcases part with _ | part
  · exact Owned.Only.pure' _
  · refine Owned.Only.ite _ (Owned.Only.pure' _) ?_
    refine Owned.Only.bind (Only.layerRecover _ _ _ _ (rootPayload_length below) _) fun root ↦ ?_
    rcases root with _ | root <;> exact Owned.Only.pure' _

attribute [local irreducible] FORS.Seeded.signLayer FORS.Seeded.layerStep FORS.Seeded.forsOpen

theorem Only.sequenceThread {parameter : PublicParameter} {σ : Type} :
    ∀ {n : Nat} {α : Fin n → Type}
      {computation : (i : Fin n) → σ → OracleComp HashSpec (Option (α i × σ))},
      (∀ i state, Only parameter (computation i state)) → ∀ state,
        Only parameter (sequenceThread computation state)
  | 0, _, _, _, _ => Owned.Only.pure' _
  | _ + 1, α, computation, h, state => by
      unfold FORS.Concrete.sequenceThread
      refine Owned.Only.bind (h (Fin.last _) state) fun last ↦ ?_
      rcases last with _ | ⟨last, next⟩
      · exact Owned.Only.pure' _
      · refine Owned.Only.bind (Only.sequenceThread (α := fun i ↦ α i.castSucc)
          (fun i ↦ h i.castSucc) next) fun init ↦ ?_
        rcases init with _ | init <;> exact Owned.Only.pure' _

theorem Only.finishSign (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    Only secretKey.parameter (finishSign secretKey message randomness :
      OracleComp HashSpec (Option Signature)) := by
  unfold FORS.Seeded.finishSign
  refine Owned.Only.bind (Owned.Only.messageDigest _ _ _) fun digest ↦ ?_
  dsimp only
  generalize digestIndex digest = index
  generalize digestLeaves digest = leaves
  refine Owned.Only.bind (Only.forsOpen _ _ _) fun opening ↦ ?_
  refine Owned.Only.bind (Owned.Only.forsRecover _ _ _) fun roots ↦ ?_
  refine Owned.Only.bind (Owned.Only.forsPublicKey _ _) fun forsKey ↦ ?_
  refine Owned.Only.bind (Only.sequenceThread (fun lay below ↦ Only.layerStep secretKey index lay
    below) forsKey) fun layers ↦ ?_
  rcases layers with _ | layers <;> exact Owned.Only.pure' _

attribute [local irreducible] FORS.Seeded.finishSign FORS.Seeded.signAttempt

theorem Only.signDigestLoop (secretKey : SecretKey) (message : Message) (step : Randomness) :
    ∀ attempts randomness, Only secretKey.parameter
      (signDigestLoop secretKey message step attempts randomness :
        OracleComp HashSpec (Option (Randomness × Index)))
  | 0, _ => Owned.Only.pure' _
  | attempts + 1, randomness => by
      rw [FORS.Seeded.signDigestLoop]
      refine Owned.Only.bind (Only.signAttempt _ _ _) fun result ↦ ?_
      rcases result with _ | _
      · exact Only.signDigestLoop secretKey message step attempts (randomness + step)
      · exact Owned.Only.pure' _

/-- **The model's signer asks only inputs its key's parameter owns.** -/
theorem only_sign (secretKey : SecretKey) (message : Message) :
    Only secretKey.parameter (FORS.Seeded.sign secretKey message :
      OracleComp HashSpec (Option Signature)) := by
  rw [Security.Det.seededSign_eq]
  refine Owned.Only.bind (Owned.Only.deriveRandomizer _ _) fun walk ↦ ?_
  refine Owned.Only.bind (Only.signDigestLoop _ _ _ _ _) fun result ↦ ?_
  rcases result with _ | ⟨randomness, _⟩
  · exact Owned.Only.pure' _
  · exact Only.finishSign _ _ _

end FORS.Owned.Seeded

namespace Sphincs.MultiKey

open Common.SufCma.MultiKey FORS.Owned Model

/-! ## The logged key generation -/

theorem queriesIn_mono {Q Q' : List UInt8 → Prop} (hQ : ∀ x, Q x → Q' x) {α : Type}
    {X : OracleComp SchemeHashSpec α} (hX : QueriesIn Q X) : QueriesIn Q' X := by
  induction X using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [queriesIn_query_bind] at hX ⊢
    exact ⟨hQ t hX.1, fun u ↦ ih u (hX.2 u)⟩

theorem mem_support_log_bind {α β : Type} (X : OracleComp SchemeHashSpec α)
    (f : α → OracleComp SchemeHashSpec β) {z : β × List (List UInt8)}
    (hz : z ∈ support (simulateQ logImpl (X >>= f)).run) :
    ∃ z₁ ∈ support (simulateQ logImpl X).run, ∃ z₂ ∈ support (simulateQ logImpl (f z₁.1)).run,
      z = (z₂.1, z₁.2 ++ z₂.2) := by
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hz
  obtain ⟨⟨a, w⟩, hz₁, hz⟩ := hz
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨⟨b, w'⟩, hz₂, rfl⟩ := hz
  exact ⟨(a, w), hz₁, (b, w'), hz₂, rfl⟩

theorem log_pure {α : Type} {a : α} {z : α × List (List UInt8)}
    (hz : z ∈ support (simulateQ logImpl (pure a : OracleComp SchemeHashSpec α)).run) :
    z = (a, []) := by
  simp only [simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  exact hz

theorem log_query {t : List UInt8} {z : BitVec 256 × List (List UInt8)}
    (hz : z ∈ support (simulateQ logImpl
      (liftM (SchemeHashSpec.query t) : OracleComp SchemeHashSpec (BitVec 256))).run) :
    z.2 = [t] := by
  have h0 : (logImpl t).run = (fun u ↦ (u, [t])) <$>
      (liftM (SchemeHashSpec.query t) : OracleComp SchemeHashSpec _) := by
    simp [logImpl, run_liftM_query_writer]
  rw [simulateQ_spec_query, h0, support_map] at hz
  obtain ⟨u, -, rfl⟩ := hz
  rfl

/-- **A logged computation logs only inputs it may query.** -/
theorem mem_log_of_queriesIn {Q : List UInt8 → Prop} {α : Type} (X : OracleComp SchemeHashSpec α)
    (hX : QueriesIn Q X) {z : α × List (List UInt8)}
    (hz : z ∈ support (simulateQ logImpl X).run) : ∀ x ∈ z.2, Q x := by
  induction X using OracleComp.inductionOn generalizing z with
  | pure a =>
    rw [log_pure hz]
    intro x hx
    simp at hx
  | query_bind t k ih =>
    rw [queriesIn_query_bind] at hX
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := mem_support_log_bind _ _ hz
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rw [log_query hz₁, List.mem_singleton] at hx
      rw [hx]
      exact hX.1
    · exact ih z₁.1 (hX.2 z₁.1) hz₂ x hx

section Generic

variable [FORS.Params]

/-- **What a key record of the model's key generation says**: the secret key's parameter is the
public key's, and every input key generation queried is one of the two key seed derivations of
its seed or owned by its parameter. -/
def KeyFacts (z : KeyRec FORS.PublicKey FORS.Seeded.SecretKey) : Prop :=
  z.1.2.parameter = z.1.1.parameter ∧ ∀ x ∈ z.2,
    x = FORS.keySeedInput z.1.2.seed 0 ∨ x = FORS.keySeedInput z.1.2.seed 1 ∨
      Owns z.1.1.parameter x

/-- `mem_support_log_bind` for computations of FORS's hash monad. -/
theorem mem_support_log_bindH {α β : Type} (X : OracleComp FORS.HashSpec α)
    (f : α → OracleComp FORS.HashSpec β) {z : β × List (List UInt8)}
    (hz : z ∈ support (simulateQ logImpl (X >>= f : OracleComp FORS.HashSpec β)).run) :
    ∃ z₁ ∈ support (simulateQ logImpl X).run, ∃ z₂ ∈ support (simulateQ logImpl (f z₁.1)).run,
      z = (z₂.1, z₁.2 ++ z₂.2) :=
  mem_support_log_bind X f hz

theorem log_treeRoot (parameter : FORS.PublicParameter) (lay : FORS.Layer) (tree : FORS.TreeIndex)
    (seed : FORS.MasterSeed) {z : FORS.Digest × List (List UInt8)}
    (hz : z ∈ support (simulateQ logImpl
      (FORS.Seeded.treeRoot parameter lay tree seed : OracleComp FORS.HashSpec FORS.Digest)).run) :
    ∀ x ∈ z.2, Owns parameter x :=
  mem_log_of_queriesIn _ (FORS.Owned.Seeded.Only.treeRoot lay tree seed) hz

/-- **The model's key generation, logged**: a record of `KeyFacts`, of its seed. -/
theorem keyFacts_keygenFromSeed (seed : FORS.MasterSeed)
    {z : KeyRec FORS.PublicKey FORS.Seeded.SecretKey}
    (hz : z ∈ support (simulateQ logImpl (FORS.Seeded.keygenFromSeed seed :
      OracleComp FORS.HashSpec (FORS.PublicKey × FORS.Seeded.SecretKey))).run) :
    KeyFacts z ∧ z.1.2.seed = seed := by
  unfold FORS.Seeded.keygenFromSeed at hz
  obtain ⟨z₁, hz₁, z', hz', rfl⟩ := mem_support_log_bindH _ _ hz
  obtain ⟨z₂, hz₂, z'', hz'', rfl⟩ := mem_support_log_bindH _ _ hz'
  obtain ⟨z₃, hz₃, z₄, hz₄, rfl⟩ := mem_support_log_bindH _ _ hz''
  rw [log_pure hz₄]
  have h1 : ∀ x ∈ z₁.2, x = FORS.keySeedInput seed 0 :=
    mem_log_of_queriesIn (Q := fun x ↦ x = FORS.keySeedInput seed 0) _ (by
      unfold FORS.derivePublicSeed
      exact queriesIn_bind (queriesIn_query rfl) fun _ ↦ trivial) hz₁
  have h2 : ∀ x ∈ z₂.2, x = FORS.keySeedInput seed 1 :=
    mem_log_of_queriesIn (Q := fun x ↦ x = FORS.keySeedInput seed 1) _ (by
      unfold FORS.derivePrf
      exact queriesIn_query rfl) hz₂
  have h3 : ∀ x ∈ z₃.2, Owns z₁.1 x := log_treeRoot _ _ _ _ hz₃
  refine ⟨⟨rfl, fun x hx ↦ ?_⟩, rfl⟩
  simp only [List.mem_append, List.not_mem_nil, or_false] at hx
  rcases hx with hx | hx | hx
  · exact .inl (h1 x hx)
  · exact .inr (.inl (h2 x hx))
  · exact .inr (.inr (h3 x hx))

theorem run_log_bind {α β : Type} (X : OracleComp SchemeHashSpec α)
    (f : α → OracleComp SchemeHashSpec β) :
    (simulateQ logImpl (X >>= f)).run = (simulateQ logImpl X).run >>= fun p ↦
      Prod.map id (p.2 ++ ·) <$> (simulateQ logImpl (f p.1)).run := by
  rw [simulateQ_bind, WriterT.run_bind']

/-- `run_log_bind` for computations of FORS's hash monad. -/
theorem run_log_bindH {α β : Type} (X : OracleComp FORS.HashSpec α)
    (f : α → OracleComp FORS.HashSpec β) :
    (simulateQ logImpl (X >>= f : OracleComp FORS.HashSpec β)).run =
      (simulateQ logImpl X).run >>= fun p ↦
        Prod.map id (p.2 ++ ·) <$> (simulateQ logImpl (f p.1)).run :=
  run_log_bind X f

theorem run_log_oracleHash (x : List UInt8) :
    (simulateQ logImpl
      (FORS.Concrete.oracleHash x : OracleComp FORS.HashSpec FORS.HashOutput)).run =
      (fun u ↦ (u, [x])) <$> (liftM (SchemeHashSpec.query x) : OracleComp SchemeHashSpec _) := by
  show (simulateQ logImpl
    (liftM (SchemeHashSpec.query x) : OracleComp SchemeHashSpec (BitVec 256))).run = _
  rw [simulateQ_spec_query]
  simp [logImpl, run_liftM_query_writer]

/-- **The model's key generation, logged, after its first query** (the parameter's derivation)
answered `u`: the parameter is `truncateHash u`. -/
noncomputable def keygenRest (seed : FORS.MasterSeed) (u : BitVec 256) :
    OracleComp SchemeHashSpec (KeyRec FORS.PublicKey FORS.Seeded.SecretKey) :=
  Prod.map id ([FORS.keySeedInput seed 0] ++ ·) <$> (simulateQ logImpl
    ((FORS.derivePrf seed : OracleComp FORS.HashSpec FORS.HashOutput) >>= fun prf ↦
      (FORS.Seeded.treeRoot (FORS.truncateHash u) FORS.topLayer FORS.Concrete.rootTree seed :
        OracleComp FORS.HashSpec FORS.Digest) >>= fun root ↦
        pure ((⟨root, FORS.truncateHash u⟩ : FORS.PublicKey),
          (⟨seed, prf, FORS.truncateHash u, root⟩ : FORS.Seeded.SecretKey)))).run

theorem logged_keygenFromSeed_eq (seed : FORS.MasterSeed) :
    (simulateQ logImpl (FORS.Seeded.keygenFromSeed seed :
      OracleComp FORS.HashSpec (FORS.PublicKey × FORS.Seeded.SecretKey))).run =
      (liftM (SchemeHashSpec.query (FORS.keySeedInput seed 0)) : OracleComp SchemeHashSpec _) >>=
        keygenRest seed := by
  unfold FORS.Seeded.keygenFromSeed FORS.derivePublicSeed
  erw [bind_assoc]
  rw [run_log_bindH, run_log_oracleHash]
  erw [bind_map_left]

theorem keygenRest_parameter (seed : FORS.MasterSeed) (u : BitVec 256)
    {z : KeyRec FORS.PublicKey FORS.Seeded.SecretKey} (hz : z ∈ support (keygenRest seed u)) :
    z.1.1.parameter = FORS.truncateHash u := by
  unfold keygenRest at hz
  rw [support_map] at hz
  obtain ⟨z', hz', rfl⟩ := hz
  obtain ⟨z₂, -, z'', hz'', rfl⟩ := mem_support_log_bindH _ _ hz'
  obtain ⟨z₃, -, z₄, hz₄, rfl⟩ := mem_support_log_bindH _ _ hz''
  rw [log_pure hz₄]
  rfl

end Generic

attribute [local instance] params

/-- **A public key's inputs**: those its public parameter owns (`FORS.Owned.Owns`). -/
def ownedPub (publicKey : FORS.PublicKey) (input : List UInt8) : Prop :=
  Owns publicKey.parameter input

instance (publicKey : FORS.PublicKey) : DecidablePred (ownedPub publicKey) := fun input ↦
  inferInstanceAs (Decidable (Owns publicKey.parameter input))

theorem keyFacts_of_mem {seed : FORS.MasterSeed} {z : KeyRec FORS.PublicKey FORS.Seeded.SecretKey}
    (hz : z ∈ support (loggedKeygen modelScheme seed)) : KeyFacts z ∧ z.1.2.seed = seed :=
  keyFacts_keygenFromSeed seed hz

theorem keyFacts_of_isKey {z : KeyRec FORS.PublicKey FORS.Seeded.SecretKey}
    (hz : IsKey modelScheme z) : KeyFacts z := by
  obtain ⟨seed, h⟩ := hz
  exact (keyFacts_of_mem h).1

/-! ## The separation and the clash -/

/-- **The model's separation facts**: its signer asks only inputs its key owns, its verifier
only inputs the public key owns, and a key-generation input another key owns is owned by its own
key (the key seed derivations have no owner). -/
theorem separation : Separation modelScheme ownedPub where
  sign_queries z hz r := by
    have hpar := (keyFacts_of_isKey hz).1
    refine queriesIn_mono (fun x hx ↦ Or.inl ?_) (FORS.Owned.Seeded.only_sign z.1.2 r)
    show Owns z.1.1.parameter x
    rw [← hpar]
    exact hx
  verify_queries pk f := FORS.Owned.only_verify pk f.message f.signature
  keygen_owned z hz x hx pk' hown := by
    rcases (keyFacts_of_isKey hz).2 x hx with rfl | rfl | h
    · exact (not_owns_keySeedInput _ _ _ hown).elim
    · exact (not_owns_keySeedInput _ _ _ hown).elim
    · exact h

theorem keyInput_or_owns {z : KeyRec FORS.PublicKey FORS.Seeded.SecretKey} (hz : KeyFacts z)
    {x : List UInt8} (hx : x ∈ z.2) :
    (∃ d < 256, x = FORS.keySeedInput z.1.2.seed d) ∨ Owns z.1.1.parameter x := by
  rcases hz.2 x hx with h | h | h
  · exact .inl ⟨0, by norm_num, h⟩
  · exact .inl ⟨1, by norm_num, h⟩
  · exact .inr h

/-- **A clash of two keys** needs equal seeds or equal public parameters. -/
theorem clash_imp {za zb : KeyRec FORS.PublicKey FORS.Seeded.SecretKey} (ha : KeyFacts za)
    (hb : KeyFacts zb) (h : Clash ownedPub za zb) :
    za.1.2.seed = zb.1.2.seed ∨ za.1.1.parameter = zb.1.1.parameter := by
  obtain ⟨x, ⟨hxb, hxa | hxa⟩ | ⟨hxa, hxb⟩⟩ := h
  · rcases keyInput_or_owns hb hxb with ⟨d, hd, rfl⟩ | hob
    · rcases keyInput_or_owns ha hxa with ⟨d', hd', hx⟩ | hoa
      · exact .inl (FORS.Security.keySeedInput_injective hd' hd hx.symm).1
      · exact (not_owns_keySeedInput _ _ _ hoa).elim
    · rcases keyInput_or_owns ha hxa with ⟨d', hd', rfl⟩ | hoa
      · exact (not_owns_keySeedInput _ _ _ hob).elim
      · exact .inr (owns_unique hoa hob)
  · rcases keyInput_or_owns hb hxb with ⟨d, hd, rfl⟩ | hob
    · exact (not_owns_keySeedInput _ _ _ hxa).elim
    · exact .inr (owns_unique hxa hob)
  · exact .inr (owns_unique hxa hxb)

/-! ## The probability of a clash -/

theorem fresh_isKey {z : KeyRec FORS.PublicKey FORS.Seeded.SecretKey × SchemeHashSpec.QueryCache}
    (hz : z ∈ support (SufCma.romRun (freshRec modelScheme) ∅)) :
    ∃ seed, z.1 ∈ support (loggedKeygen modelScheme seed) := by
  have h := KeptKey.fst_mem_support_romRun' hz
  rw [freshRec, mem_support_bind_iff] at h
  obtain ⟨s, -, hs⟩ := h
  exact ⟨s, (mem_support_liftM_world _ _).mp hs⟩

theorem romRun_sample (c : SchemeHashSpec.QueryCache) :
    SufCma.romRun (liftM modelScheme.sample : OracleComp World FORS.MasterSeed) c =
      (·, c) <$> modelScheme.sample :=
  OracleSpec.simulateQ_romImpl_liftM_run _ _

theorem romRun_query_empty (x : List UInt8) :
    SufCma.romRun (liftM (World.query (.inr x)) : OracleComp World (BitVec 256)) ∅ =
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u ↦
        pure (u, (∅ : SchemeHashSpec.QueryCache).cacheQuery x u) := by
  change (SchemeHashSpec.randomOracle x).run ∅ = _
  rw [randomOracle.run_eq]
  rfl

/-- A fresh key's seed is a given one with probability `2^-256`. -/
theorem prob_seed_le (sb : FORS.MasterSeed) :
    Pr{let z ← SufCma.romRun (freshRec modelScheme) ∅}[z.1.1.2.seed = sb] ≤
      ((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [freshRec, romRun_bind]
  refine (prEvent_bind_le_of_imp _ _ (fun a ↦ a.1 = sb) _ fun a _ b hb hq ↦ ?_).trans ?_
  · exact ((keyFacts_of_mem ((mem_support_liftM_world _ _).mp
      (KeptKey.fst_mem_support_romRun' hb))).2).symm.trans hq
  · simp only [romRun_sample, prEvent_map]
    simp only [modelScheme, FORS.sampleMasterSeed]
    rw [@SampleableType.prEvent_uniformSample_eq_singleton FORS.MasterSeed
      (SampleableType.ofFintype FORS.MasterSeed) _ sb, Fintype.card_bitVec]

/-- A fresh key's public parameter is a given one with probability `2^-128`: it is the
truncation of a fresh uniform answer. -/
theorem prob_parameter_le (pb : FORS.PublicParameter) :
    Pr{let z ← SufCma.romRun (freshRec modelScheme) ∅}[z.1.1.1.parameter = pb] ≤
      ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [freshRec, romRun_bind]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun a ha ↦ ?_
  rw [romRun_sample, support_map] at ha
  obtain ⟨s, -, rfl⟩ := ha
  have hk : (liftM (loggedKeygen modelScheme s) : OracleComp World _) =
      liftM (World.query (.inr (FORS.keySeedInput s 0))) >>= fun u ↦ liftM (keygenRest s u) := by
    rw [← liftM_query_bind]
    exact congrArg _ (logged_keygenFromSeed_eq s)
  dsimp only
  rw [hk, romRun_bind]
  refine (prEvent_bind_le_of_imp _ _ (fun p ↦ FORS.truncateHash p.1 = pb) _
    fun p _ b hb hq ↦ ?_).trans ?_
  · exact (keygenRest_parameter s p.1 ((mem_support_liftM_world _ _).mp
      (KeptKey.fst_mem_support_romRun' hb))).symm.trans hq
  · rw [romRun_query_empty, bind_pure_comp]
    simp only [prEvent_map]
    calc Pr{let x ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))}[FORS.truncateHash x = pb]
        = Pr{let x ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))}[
            FORS.truncateHash x ∈ ({pb} : Finset FORS.Digest)] :=
          prEvent_congr _ _ _ fun _ ↦ Finset.mem_singleton.symm
      _ = _ := FORS.probEvent_uniform_truncateHash_mem {pb}
      _ ≤ _ := by
          erw [Finset.card_singleton]
          rw [Fintype.card_bitVec, Nat.cast_one, one_div]
          exact le_rfl

/-- **The clash bound**: a fresh key clashes with a fixed key with probability at most
`2^-256 + 2^-128`. -/
theorem prob_clash_le (zb : KeyRec FORS.PublicKey FORS.Seeded.SecretKey)
    (hzb : IsKey modelScheme zb) :
    Pr{let z ← SufCma.romRun (freshRec modelScheme) ∅}[Clash ownedPub z.1 zb] ≤
      ((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ + ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
  have hb := keyFacts_of_isKey hzb
  calc _ ≤ Pr{let z ← SufCma.romRun (freshRec modelScheme) ∅}[
        z.1.1.2.seed = zb.1.2.seed ∨ z.1.1.1.parameter = zb.1.1.parameter] :=
        prEvent_mono_of_support _ _ _ fun z hz hc ↦ by
          obtain ⟨s, hs⟩ := fresh_isKey hz
          exact clash_imp (keyFacts_of_mem hs).1 hb hc
    _ ≤ _ := prEvent_or_le _ _ _
    _ ≤ _ := add_le_add (prob_seed_le _) (prob_parameter_le _)

theorem clash_eps_le :
    ((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ + ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ ≤ ((2 ^ 127 : ℕ) : ℝ≥0∞)⁻¹ := by
  have e : ∀ n : ℕ, ((2 ^ n : ℕ) : ℝ≥0∞)⁻¹ = (2⁻¹ : ℝ≥0∞) ^ n := fun n ↦ by
    rw [Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]
  rw [e, e, e]
  calc (2⁻¹ : ℝ≥0∞) ^ 256 + 2⁻¹ ^ 128 ≤ 2⁻¹ ^ 128 + 2⁻¹ ^ 128 :=
        add_le_add (pow_le_pow_of_le_one zero_le (by norm_num) (by norm_num)) le_rfl
    _ = 2 * 2⁻¹ ^ 128 := (two_mul _).symm
    _ = 2⁻¹ ^ 127 := by
        rw [pow_succ', ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top,
          one_mul]

/-! ## The crate's keys in the random-oracle model -/

open HashSig.OverPermutation (sequenceFin)

theorem evalWithAnswerFn_sequenceFin {ι : Type} {spec : OracleSpec.{0, 0} ι}
    (f : QueryImpl spec Id) {α : Type} :
    ∀ {n : ℕ} (c : Fin n → OracleComp spec α),
      evalWithAnswerFn f (sequenceFin c) = fun j ↦ evalWithAnswerFn f (c j)
  | 0, _ => funext fun j ↦ j.elim0
  | n + 1, c => by
    simp only [sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
      evalWithAnswerFn_sequenceFin]
    funext j
    refine Fin.cases ?_ (fun i ↦ ?_) j <;> rfl

theorem queriesIn_sequenceFin {Q : List UInt8 → Prop} {γ : Type} :
    ∀ {n : ℕ} (cs : Fin n → OracleComp SchemeHashSpec γ), (∀ j, QueriesIn Q (cs j)) →
      QueriesIn Q (sequenceFin cs)
  | 0, _, _ => trivial
  | n + 1, cs, h => by
    simp only [sequenceFin]
    exact queriesIn_bind (h 0) fun _ ↦
      queriesIn_bind (queriesIn_sequenceFin _ fun j ↦ h j.succ) fun _ ↦ trivial

section Swap

variable {Seed PK SK₁ SK₂ Req Resp F : Type} {S₁ : SchemeWithHash Seed PK SK₁ Req Resp F}
  {S₂ : SchemeWithHash Seed PK SK₂ Req Resp F}

/-- **A swap of the signer, key by key**: a `StaticSwap` for `k` keys. -/
def staticSwapMulti (K : StaticSwap S₁ S₂) (k : ℕ) :
    StaticSwap (S₁.multiKey k) (S₂.multiKey k) where
  keep seeds j := K.keep (seeds j)
  sample_eq := by simp only [SchemeWithHash.multiKey, K.sample_eq]
  verify_eq := by simp only [SchemeWithHash.multiKey, K.verify_eq]
  win_eq := by simp only [SchemeWithHash.multiKey, K.win_eq]
  keygen_eval f seeds := by
    simp only [SchemeWithHash.multiKey, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
      evalWithAnswerFn_sequenceFin, K.keygen_eval]
  sign_eval f seeds r := by
    simp only [SchemeWithHash.multiKey, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
      evalWithAnswerFn_sequenceFin]
    exact K.sign_eval f (seeds r.1) r.2

/-- **The multi-key random-oracle bound passes through a swap** whose algorithms query a finite
part `P` of the hash's domain. -/
theorem romBoundMulti_swap (K : StaticSwap S₁ S₂) (P : List UInt8 → Prop) [DecidablePred P]
    [Fintype {d // P d}] (hk₁ : ∀ seed, QueriesIn P (S₁.keygen seed))
    (hk₂ : ∀ seed, QueriesIn P (S₂.keygen seed)) (hs₁ : ∀ sk r, QueriesIn P (S₁.sign sk r))
    (hs₂ : ∀ seed r, QueriesIn P (S₂.sign (K.keep seed) r)) (k : ℕ) {bits slack maxRequests : ℕ}
    (h : RomBoundMulti S₁ k bits slack maxRequests) :
    RomBoundMulti S₂ k bits slack maxRequests := by
  intro q main hq hn
  rw [(staticSwapMulti K k).success_eq P
    (fun seeds ↦ queriesIn_bind (queriesIn_sequenceFin _ fun j ↦ hk₁ (seeds j)) fun _ ↦ trivial)
    (fun seeds ↦ queriesIn_bind (queriesIn_sequenceFin _ fun j ↦ hk₂ (seeds j)) fun _ ↦ trivial)
    (fun sks r ↦ hs₁ (sks r.1) r.2) (fun seeds r ↦ hs₂ (seeds r.1) r.2) main]
  exact h q main hq hn

end Swap

/-- **The crate's `k` keys win as often as the model's** in the random-oracle model. -/
theorem crate_romBoundMulti (k : ℕ) {bits slack maxRequests : ℕ}
    (h : RomBoundMulti modelScheme k bits slack maxRequests) :
    RomBoundMulti crateScheme k bits slack maxRequests :=
  romBoundMulti_swap staticSwap Queries.Honest Queries.queriesIn_seededKeygen
    Queries.queriesIn_crateKeygen Queries.queriesIn_seededSign Queries.queriesIn_crateSign k h

/-- **The crate's copy over `π` against many keys**, from upstream's model at the adversary's
own count: the generic theorem on the model's scheme, whose separation and clash bound hold,
moved to the crate's copy key by key. -/
theorem crate_multiKey {c : ℕ} (h : AdvBound c) :
    MultiKeyStronglyUnforgeable crateScheme.overPermutation (2 ^ 32) signatureLimit (c + 1) 127 :=
  fun k hk1 hk q main hq hn ↦ multiKey_of_romBoundMulti crateScheme (by norm_num) hk1 hk
    (crate_romBoundMulti k (romBoundMulti_of_romBoundAdv modelScheme ownedPub k
      (modelScheme_romBoundAdv h signatureLimit) separation prob_clash_le clash_eps_le))
    crate_keygen_cost (fun seed message ↦ crate_sign_cost seed message) crate_verify_cost
    SphincsCost.total_le q main hq hn

/-! ## The statement's scheme, through the maps -/

local notation "σ" => schemeHashOverPermutation

theorem keyLog_mapLog {k : ℕ} {Req Resp₁ Resp₂ : Type} (j : Fin k) (φ : Resp₁ → Resp₂)
    (log : QueryLog (Fin k × Req →ₒ Resp₁)) :
    keyLog j (Transport.mapLog φ log) = Transport.mapLog φ (keyLog j log) := by
  induction log with
  | nil => rfl
  | cons e log ih =>
    by_cases hj : e.1.1 = j
    · simp only [keyLog, Transport.mapLog, List.map_cons, List.filterMap_cons, hj,
        ↓reduceIte] at ih ⊢
      rw [ih]
    · simp only [keyLog, Transport.mapLog, List.map_cons, List.filterMap_cons, hj,
        ↓reduceIte] at ih ⊢
      exact ih

/-- **The statement's game against `k` keys is the crate's copy's** against the adversary read
through the maps, key by key. -/
theorem multiKey_forgeryGame_eq (k : ℕ)
    (main : (Fin k → PublicKey) → OracleComp
      (RandomPermutationOracles + (Fin k × FORS.Message →ₒ Option Signature)) (Fin k × Forgery)) :
    forgeryGame (RandomPermutationModel.sufCmaScheme.multiKey k) main =
      forgeryGame (crateScheme.overPermutation.multiKey k)
        (Transport.mapAdversary (fun pks j ↦ ofModelPublicKey (pks j))
          (Option.map ofModelSignature) (fun f ↦ (f.1, toModelForgery f.2)) main) := by
  rw [← multiKey_overPermutation, forgeryGame_overPermutation]
  refine Transport.forgeryGame_eq (crateScheme.multiKey k)
    (RandomPermutationModel.sufCmaScheme.multiKey k) (fun pks j ↦ ofModelPublicKey (pks j)) id
    (Option.map ofModelSignature) (fun f ↦ (f.1, toModelForgery f.2)) rfl (fun seeds ↦ ?_)
    (fun sks r ↦ (simulateQ_crateSign (sks r.1) r.2).symm)
    (fun pks f ↦ (simulateQ_verify (ofModelPublicKey (pks f.1)) f.2.message
      f.2.signature).symm)
    (fun log f ↦ ?_) main
  · simp only [Scheme.multiKey, SchemeWithHash.multiKey, simulateQ_bind, simulateQ_pure,
      LeanXmss.simulateQ_sequenceFin, map_bind, map_pure]
    have hj : ∀ j, RandomPermutationModel.sufCmaScheme.generateKeys (seeds j) =
        (fun keys ↦ (ofModelPublicKey keys.1, keys.2)) <$>
          simulateQ σ (crateScheme.keygen (seeds j)) :=
      fun j ↦ (simulateQ_crateKeygen (seeds j)).symm
    simp only [hj]
    rw [sequenceFin_map (fun (_ : Fin k) (keys : FORS.PublicKey × FORS.MasterSeed) ↦
      (ofModelPublicKey keys.1, keys.2)), bind_map_left]
    rfl
  · show RandomPermutationModel.sufCmaScheme.winningCondition
        (keyLog f.1 (Transport.mapLog (Option.map ofModelSignature) log)) f.2 =
      crateScheme.win (keyLog f.1 log) (toModelForgery f.2)
    exact (congrArg (fun l ↦ RandomPermutationModel.sufCmaScheme.winningCondition l f.2)
      (keyLog_mapLog f.1 (Option.map ofModelSignature) log)).trans (win_eq (keyLog f.1 log) f.2)

/-- A larger constant is a weaker multi-key bound. -/
theorem multiKey_mono_slack {Seed PK SK Req Resp F : Type} {scheme : Scheme Seed PK SK Req Resp F}
    {maxKeys maxSignings slack slack' bits : ℕ}
    (h : MultiKeyStronglyUnforgeable scheme maxKeys maxSignings slack bits) (hle : slack ≤ slack') :
    MultiKeyStronglyUnforgeable scheme maxKeys maxSignings slack' bits := by
  intro k hk1 hk q main hq hn
  refine (h k hk1 hk q main hq hn).trans ?_
  gcongr

/-- **The statement's leanSPHINCS against many keys**, from upstream's model at the adversary's
own count. -/
theorem multiKey_of_model {c : ℕ} (h : AdvBound c) :
    MultiKeyStronglyUnforgeable RandomPermutationModel.sufCmaScheme (2 ^ 32) signatureLimit
      (c + 1) 127 := by
  intro k hk1 hk q main hq hn
  rw [multiKey_forgeryGame_eq k main]
  exact crate_multiKey h k hk1 hk q _
    (fun pks ↦ mapAdversary_cost _ _ _ main _ pks (hq _))
    (fun pks j ↦ mapAdversary_cost _ _ _ main _ pks (hn _ j))

end Sphincs.MultiKey

namespace Sphincs

/-- **leanSPHINCS is multi-key strongly unforgeable in the random-permutation model**: against
`k ≤ 2^32` keys, an adversary that itself makes at most `q` calls of `π` and `π⁻¹` and at most
`1,182,000,000` signing requests to each key forges under one of them with probability at most
`k · (q + 2^19 + k) · 2^-127`. -/
theorem leanSphincs_multiKey :
    Common.SufCma.MultiKeyStronglyUnforgeable RandomPermutationModel.sufCmaScheme (2 ^ 32)
      signatureLimit securitySlack 127 :=
  MultiKey.multiKey_mono_slack
    (MultiKey.multiKey_of_model
      (fun adversary q hq ↦ FORS.Lifetimes.h26_layered_adversary adversary q hq))
    (by decide)

end Sphincs
