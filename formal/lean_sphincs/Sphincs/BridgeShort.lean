import Sphincs.SecurityVerifier
import Sphincs.Randomized
import VCVio.OracleComp.QueryTracking.QueryBound

set_option backward.isDefEq.respectTransparency false

/-! Every hash input of the honest algorithms and of the verifier has at most 1056 bytes.
Longer adversarial inputs never meet honest work, which lets them be simulated privately. -/

open OracleComp OracleSpec

namespace Sphincs.Security.Short

open Concrete

attribute [local irreducible] digestAttemptLimit encodingAttemptLimit

/-- The longest honest input: 16 parameter bytes, 16 address bytes and 64 chain ends. -/
def bound : Nat := 1056

def IsShort (input : HashInput) : Prop := input.length ≤ bound

instance : DecidablePred IsShort := fun input => inferInstanceAs (Decidable (input.length ≤ bound))

/-- Every hash query of the computation is short. -/
def Only {α : Type} (oa : OracleComp HashSpec α) : Prop :=
  oa.IsQueryBoundP (fun input => ¬IsShort input) 0

theorem Only.pure' {α : Type} (value : α) : Only (pure value : OracleComp HashSpec α) := trivial

theorem Only.bind {α β : Type} {oa : OracleComp HashSpec α} {next : α → OracleComp HashSpec β}
    (h : Only oa) (hnext : ∀ value, Only (next value)) : Only (oa >>= next) := by
  have := isQueryBoundP_bind (n := 0) (m := 0) h (fun value _ => hnext value)
  simpa [Only] using this

theorem Only.map {α β : Type} {oa : OracleComp HashSpec α} (f : α → β) (h : Only oa) :
    Only (f <$> oa) := by
  rw [Only, isQueryBoundP_map_iff]
  exact h

theorem Only.ite {α : Type} (condition : Prop) [Decidable condition]
    {left right : OracleComp HashSpec α} (hleft : Only left) (hright : Only right) :
    Only (if condition then left else right) := by
  split
  · exact hleft
  · exact hright

theorem Only.query {input : HashInput} (h : IsShort input) :
    Only (oracleHash input : OracleComp HashSpec HashOutput) := by
  simp only [Only, oracleHash, HasQuery.query]
  rw [isQueryBoundP_query_iff]
  intro hlong
  exact absurd h hlong

theorem fieldBytes_length (fields : TweakFields) : (fieldBytes fields).length = 16 := by
  simp [fieldBytes, bytesLE_length]

theorem tweakableHashInput_length (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    (tweakableHashInput parameter domain payload).length = 32 + payload.length := by
  simp only [tweakableHashInput, tweakBytes, List.length_append, fieldBytes_length, bytesLE_length]

theorem keygenHashInput_length (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : (keygenHashInput parameter domain seed).length = 64 := by
  simp [keygenHashInput, fieldBytes_length, bytesLE_length]

theorem Only.tweakableHash (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) (h : payload.length ≤ 1024) :
    Only (Concrete.tweakableHash parameter domain payload : OracleComp HashSpec Digest) := by
  unfold Concrete.tweakableHash
  refine Only.bind (Only.query ?_) (fun _ => Only.pure' _)
  simp only [IsShort, bound, tweakableHashInput_length]
  omega

theorem schemeSeedInput_length (seed : MasterSeed) : (schemeSeedInput seed).length = 43 := by
  simp [schemeSeedInput, seedTag, bytesLE_length]

theorem Only.schemeSeed (seed : MasterSeed) :
    Only (Sphincs.schemeSeed seed : OracleComp HashSpec MasterSeed) := by
  refine Only.query ?_
  simp [IsShort, bound, schemeSeedInput_length]

theorem Only.deriveKey (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    Only (Sphincs.deriveKey parameter domain seed : OracleComp HashSpec Digest) := by
  unfold Sphincs.deriveKey
  refine Only.bind (Only.query ?_) (fun _ => Only.pure' _)
  simp [IsShort, bound, keygenHashInput_length]

theorem Only.deriveOutput (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    Only (Sphincs.deriveOutput parameter domain seed : OracleComp HashSpec HashOutput) := by
  unfold Sphincs.deriveOutput
  refine Only.query ?_
  simp [IsShort, bound, keygenHashInput_length]

theorem Only.sequenceFin {α : Type} {n : Nat} (computation : Fin n → OracleComp HashSpec α)
    (h : ∀ i, Only (computation i)) : Only (Concrete.sequenceFin computation) := by
  induction n with
  | zero => exact Only.pure' _
  | succ n ih =>
      rw [Concrete.sequenceFin]
      exact Only.bind (h 0) (fun _ => Only.bind (ih _ (fun i => h i.succ)) (fun _ => Only.pure' _))

theorem bytes16_length (value : Digest) : (bytesLE 16 value).length = 16 := bytesLE_length _ _

theorem nodePayload_length (left right : Digest) : (nodePayload left right).length = 32 := by
  simp [nodePayload, bytesLE_length]

theorem flatMap_bytes_length' {n : Nat} (values : Fin n → BitVec (8 * 16)) :
    ((List.ofFn values).flatMap (bytesLE 16)).length = 16 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.flatMap_cons, List.length_append, bytesLE_length,
        ih (fun i => values i.succ)]
      ring

theorem flatMap_bytes_length {n : Nat} (values : Fin n → Digest) :
    ((List.ofFn values).flatMap (bytesLE 16)).length = 16 * n := flatMap_bytes_length' values

theorem leafPayload_length (endpoints : ChainIndex → Digest) :
    (leafPayload endpoints).length = 1024 := by
  rw [leafPayload, flatMap_bytes_length]
  rfl

theorem rootsPayload_length (tops : Coord → Digest × Digest) :
    (rootsPayload tops).length = 256 := by
  simp [rootsPayload, nodePayload, bytesLE_length, forestCoords]

theorem superPayload_length (tops : SubIdx → Digest × Digest) :
    (superPayload tops).length = 64 := by
  simp [superPayload, nodePayload, bytesLE_length]

theorem childPayload_length (ends : FChain → Digest) :
    (childPayload ends).length = 96 := by
  rw [childPayload, flatMap_bytes_length]
  rfl

theorem messageDigestPayload_length (root : Digest) (message : Message) (randomness : Randomness) :
    (messageDigestPayload root message randomness).length = 48 := by
  simp [messageDigestPayload, bytesLE_length]

theorem Only.chainWalk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start : Nat) :
    ∀ steps value, Only (Concrete.chainWalk parameter lay tree leaf chainIdx start steps value :
      OracleComp HashSpec Digest)
  | 0, value => Only.pure' _
  | steps + 1, value => by
      rw [Concrete.chainWalk]
      refine Only.bind (Only.chainWalk parameter lay tree leaf chainIdx start steps value) ?_
      intro previous
      split
      · exact Only.tweakableHash _ _ _ (by rw [bytes16_length]; omega)
      · exact Only.pure' _

theorem Only.leafHash (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (endpoints : ChainIndex → Digest) :
    Only (Concrete.leafHash parameter lay tree leaf endpoints : OracleComp HashSpec Digest) :=
  Only.tweakableHash _ _ _ (by rw [leafPayload_length])

theorem Only.encode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : Digest) (counter : Counter) :
    Only (Concrete.encode parameter lay tree leaf message counter :
      OracleComp HashSpec (Option Encoding)) := by
  unfold Concrete.encode
  exact Only.bind (Only.tweakableHash _ _ _ (by simp [bytesLE_length])) (fun _ => Only.pure' _)

theorem Only.otsLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : Digest) (counter : Counter) (values : ChainIndex → Digest) :
    Only (Concrete.otsLeaf parameter lay tree leaf message counter values :
      OracleComp HashSpec (Option Digest)) := by
  unfold Concrete.otsLeaf
  refine Only.bind (Only.encode _ _ _ _ _ _) ?_
  intro encoding
  cases encoding with
  | none => exact Only.pure' _
  | some encoding =>
      exact Only.bind (Only.sequenceFin _ fun chainIdx => Only.chainWalk _ _ _ _ _ _ _ _)
        (fun _ => Only.bind (Only.leafHash _ _ _ _ _) (fun _ => Only.pure' _))

theorem Only.treeFold (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (path : Nat → Digest) :
    ∀ levels value, Only (Concrete.treeFold parameter lay tree leaf path levels value :
      OracleComp HashSpec Digest)
  | 0, value => Only.pure' _
  | levels + 1, value => by
      rw [Concrete.treeFold]
      refine Only.bind (Only.treeFold parameter lay tree leaf path levels value) ?_
      intro current
      split <;> exact Only.tweakableHash _ _ _ (by rw [nodePayload_length]; omega)

theorem Only.forestWalk (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (j : SubIdx) (a : ChildIdx) (i : FChain) (start : Nat) :
    ∀ steps value, Only (Concrete.forestWalk parameter index c s j a i start steps value :
      OracleComp HashSpec Digest)
  | 0, value => Only.pure' _
  | steps + 1, value => by
      rw [Concrete.forestWalk]
      refine Only.bind (Only.forestWalk parameter index c s j a i start steps value) ?_
      intro previous
      split
      · exact Only.tweakableHash _ _ _ (by rw [bytes16_length]; omega)
      · exact Only.pure' _

theorem Only.childLeafHash (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (j : SubIdx) (a : ChildIdx) (ends : FChain → Digest) :
    Only (Concrete.childLeafHash parameter index c s j a ends : OracleComp HashSpec Digest) :=
  Only.tweakableHash _ _ _ (by rw [childPayload_length]; omega)

theorem Only.subFold (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (j : SubIdx) (a : ChildIdx) (path : Fin subHeight → Digest) :
    ∀ levels value, Only (Concrete.subFold parameter index c s j a path levels value :
      OracleComp HashSpec Digest)
  | 0, value => Only.pure' _
  | levels + 1, value => by
      rw [Concrete.subFold]
      refine Only.bind (Only.subFold parameter index c s j a path levels value) ?_
      intro current
      dsimp only
      split_ifs
      · exact Only.tweakableHash _ _ _ (by rw [nodePayload_length]; omega)
      · exact Only.tweakableHash _ _ _ (by rw [nodePayload_length]; omega)
      · exact Only.pure' _

theorem Only.topFold (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (path : Fin topHeight → Digest) :
    ∀ levels value, Only (Concrete.topFold parameter index c s path levels value :
      OracleComp HashSpec Digest)
  | 0, value => Only.pure' _
  | levels + 1, value => by
      rw [Concrete.topFold]
      refine Only.bind (Only.topFold parameter index c s path levels value) ?_
      intro current
      dsimp only
      split_ifs
      · exact Only.tweakableHash _ _ _ (by rw [nodePayload_length]; omega)
      · exact Only.tweakableHash _ _ _ (by rw [nodePayload_length]; omega)
      · exact Only.pure' _

theorem Only.forestRecover (parameter : PublicParameter) (index : Index)
    (marks : Coord → CoordMark) (opening : Coord → CoordOpening) :
    Only (Concrete.forestRecover parameter index marks opening : OracleComp HashSpec Digest) := by
  unfold Concrete.forestRecover Concrete.coordRecover
  refine Only.bind (Only.sequenceFin _ fun c => ?_) ?_
  · refine Only.bind (Only.sequenceFin _ fun j => ?_) (fun tops => ?_)
    · unfold Concrete.childRecover Concrete.forestRecoverChain
      exact Only.bind (Only.bind (Only.sequenceFin _ fun _ => Only.forestWalk _ _ _ _ _ _ _ _ _ _)
        (fun _ => Only.childLeafHash _ _ _ _ _ _ _))
        (fun _ => Only.bind (Only.subFold _ _ _ _ _ _ _ _ _) (fun _ => Only.pure' _))
    · unfold Concrete.superHash
      exact Only.bind (Only.tweakableHash _ _ _ (by rw [superPayload_length]; omega))
        (fun _ => Only.bind (Only.topFold _ _ _ _ _ _ _) (fun _ => Only.pure' _))
  · intro tops
    exact Only.tweakableHash _ _ _ (by rw [rootsPayload_length]; omega)

theorem Only.messageDigestCall (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) :
    Only (Concrete.messageDigestCall parameter root message randomness :
      OracleComp HashSpec HashOutput) := by
  unfold Concrete.messageDigestCall
  apply Only.query
  simp only [IsShort, bound, tweakableHashInput_length, messageDigestPayload_length]
  omega

theorem Only.messageDigest (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) :
    Only (Concrete.messageDigest parameter root message randomness :
      OracleComp HashSpec MessageDigest) := by
  unfold Concrete.messageDigest
  exact Only.bind (Only.messageDigestCall _ _ _ _) (fun _ => Only.pure' _)

attribute [local irreducible] Concrete.treeFold Concrete.chainWalk
  Concrete.otsLeaf Concrete.forestRecover Concrete.messageDigest

theorem Only.verify (publicKey : PublicKey) (message : Message) (signature : Signature) :
    Only (Concrete.verify publicKey message signature : OracleComp HashSpec Bool) := by
  rw [verify_eq_single_layer]
  refine Only.bind (Only.messageDigest _ _ _ _) ?_
  intro digest
  refine Only.bind (Only.forestRecover _ _ _ _) ?_
  intro key
  refine Only.bind (Only.otsLeaf _ _ _ _ _ _ _) ?_
  intro value
  cases value with
  | none => exact Only.pure' _
  | some value =>
      exact Only.bind (Only.treeFold publicKey.parameter topLayer rootTree _ _ totalHeight value)
        (fun _ => Only.pure' _)

namespace Seeded
open Sphincs.Seeded

theorem Only.otsSecrets (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) :
    Only (otsSecrets parameter lay tree leaf seed :
      OracleComp HashSpec (ChainIndex → Digest)) :=
  Short.Only.bind (Short.Only.sequenceFin _ fun _ => Short.Only.deriveOutput _ _ _)
    (fun _ => Short.Only.pure' _)

theorem Only.oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) :
    Only (oneTimePublicKey parameter lay tree leaf seed :
      OracleComp HashSpec (ChainIndex → Digest)) :=
  Short.Only.bind (Only.otsSecrets _ _ _ _ _) (fun _ =>
    Short.Only.sequenceFin _ fun _ => Short.Only.chainWalk _ _ _ _ _ _ _ _)

theorem Only.otsSignFrom (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) (message : Digest) :
    ∀ attempts counter, Short.Only (otsSignFrom parameter lay tree leaf seed message attempts counter :
      OracleComp HashSpec (Option (Counter × (ChainIndex → Digest))))
  | 0, _ => Short.Only.pure' _
  | attempts + 1, counter => by
      rw [Sphincs.Seeded.otsSignFrom]
      refine Short.Only.bind (Short.Only.encode _ _ _ _ _ _) ?_
      intro encoding
      cases encoding with
      | none => exact Only.otsSignFrom parameter lay tree leaf seed message attempts (counter + 1)
      | some encoding =>
          exact Short.Only.bind (Only.otsSecrets _ _ _ _ _) (fun _ =>
            Short.Only.bind (Short.Only.sequenceFin _ fun _ => Short.Only.chainWalk _ _ _ _ _ _ _ _)
              (fun _ => Short.Only.pure' _))

theorem Only.treeNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) : ∀ level nodeIdx, Short.Only (treeNode parameter lay tree seed level nodeIdx :
      OracleComp HashSpec Digest)
  | 0, nodeIdx => by
      rw [Sphincs.Seeded.treeNode]
      exact Short.Only.bind (Only.oneTimePublicKey _ _ _ _ _) (fun _ => Short.Only.leafHash _ _ _ _ _)
  | level + 1, nodeIdx => by
      rw [Sphincs.Seeded.treeNode]
      exact Short.Only.bind (Only.treeNode parameter lay tree seed level _) (fun _ =>
        Short.Only.bind (Only.treeNode parameter lay tree seed level _) (fun _ =>
          Short.Only.tweakableHash _ _ _ (by rw [nodePayload_length]; omega)))

theorem Only.chainValue (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (j : SubIdx) (a : ChildIdx) (i : FChain) (seed : MasterSeed) (pos : Nat) :
    Short.Only (chainValue parameter index c s j a i seed pos : OracleComp HashSpec Digest) :=
  Short.Only.bind (Short.Only.bind (Short.Only.deriveOutput _ _ _) (fun _ => Short.Only.pure' _))
    (fun _ => Short.Only.forestWalk _ _ _ _ _ _ _ _ _ _)

theorem Only.forestSecrets (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (j : SubIdx) (a : ChildIdx) (seed : MasterSeed) :
    Short.Only (forestSecrets parameter index c s j a seed : OracleComp HashSpec (FChain → Digest)) :=
  Short.Only.bind (Short.Only.sequenceFin _ fun _ => Short.Only.deriveOutput _ _ _)
    (fun _ => Short.Only.pure' _)

theorem Only.subNode (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (j : SubIdx) (seed : MasterSeed) : ∀ level node, Short.Only (subNode parameter index c s j seed level node :
      OracleComp HashSpec Digest)
  | 0, node => by
      rw [Sphincs.Seeded.subNode]
      exact Short.Only.bind (Only.forestSecrets _ _ _ _ _ _ _) (fun _ =>
        Short.Only.bind (Short.Only.sequenceFin _ fun _ => Short.Only.forestWalk _ _ _ _ _ _ _ _ _ _)
          (fun _ => Short.Only.childLeafHash _ _ _ _ _ _ _))
  | level + 1, node => by
      rw [Sphincs.Seeded.subNode]
      refine Short.Only.bind (Only.subNode parameter index c s j seed level _) (fun _ =>
        Short.Only.bind (Only.subNode parameter index c s j seed level _) (fun _ => ?_))
      split
      · exact Short.Only.tweakableHash _ _ _ (by rw [nodePayload_length]; omega)
      · exact Short.Only.pure' _

theorem Only.superNode (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (seed : MasterSeed) : Short.Only (superNode parameter index c s seed : OracleComp HashSpec Digest) := by
  unfold Sphincs.Seeded.superNode Concrete.superHash
  exact Short.Only.bind (Short.Only.sequenceFin _ fun _ =>
      Short.Only.bind (Only.subNode _ _ _ _ _ _ _ _) (fun _ =>
        Short.Only.bind (Only.subNode _ _ _ _ _ _ _ _) (fun _ => Short.Only.pure' _)))
    (fun _ => Short.Only.tweakableHash _ _ _ (by rw [Short.superPayload_length]; omega))

theorem Only.topNode (parameter : PublicParameter) (index : Index) (c : Coord)
    (seed : MasterSeed) : ∀ level node, Short.Only (topNode parameter index c seed level node :
      OracleComp HashSpec Digest)
  | 0, node => by
      rw [Sphincs.Seeded.topNode]
      exact Only.superNode _ _ _ _ _
  | level + 1, node => by
      rw [Sphincs.Seeded.topNode]
      refine Short.Only.bind (Only.topNode parameter index c seed level _) (fun _ =>
        Short.Only.bind (Only.topNode parameter index c seed level _) (fun _ => ?_))
      split
      · exact Short.Only.tweakableHash _ _ _ (by rw [nodePayload_length]; omega)
      · exact Short.Only.pure' _

theorem Only.forestKey (parameter : PublicParameter) (index : Index) (seed : MasterSeed) :
    Short.Only (forestKey parameter index seed : OracleComp HashSpec Digest) := by
  have htop : ∀ c, Short.Only (do
      let left ← Sphincs.Seeded.topNode parameter index c seed (topHeight - 1) 0
      let right ← Sphincs.Seeded.topNode parameter index c seed (topHeight - 1) 1
      return (left, right) : OracleComp HashSpec (Digest × Digest)) :=
    fun c => Short.Only.bind (Only.topNode parameter index c seed _ _) (fun _ =>
      Short.Only.bind (Only.topNode parameter index c seed _ _) (fun _ => Short.Only.pure' _))
  have hroots : ∀ tops : Coord → Digest × Digest,
      Short.Only (Concrete.tweakableHash parameter (.roots index) (rootsPayload tops) :
        OracleComp HashSpec Digest) := fun tops =>
    Short.Only.tweakableHash _ _ _ (by rw [rootsPayload_length]; omega)
  unfold Sphincs.Seeded.forestKey
  exact Short.Only.bind (Short.Only.sequenceFin _ htop) hroots

theorem Only.forestOpen (parameter : PublicParameter) (index : Index) (marks : Coord → CoordMark)
    (seed : MasterSeed) :
    Short.Only (forestOpen parameter index marks seed : OracleComp HashSpec (Coord → CoordOpening)) := by
  unfold Sphincs.Seeded.forestOpen Sphincs.Seeded.coordOpen
  exact Short.Only.sequenceFin _ fun _ =>
    Short.Only.bind (Short.Only.sequenceFin _ fun _ =>
      Short.Only.bind (Only.forestSecrets _ _ _ _ _ _ _) (fun _ =>
        Short.Only.bind (Short.Only.sequenceFin _ fun _ => Short.Only.forestWalk _ _ _ _ _ _ _ _ _ _) (fun _ =>
          Short.Only.bind (Short.Only.sequenceFin _ fun _ => Only.subNode _ _ _ _ _ _ _ _)
            (fun _ => Short.Only.pure' _)))) (fun _ =>
      Short.Only.bind (Short.Only.sequenceFin _ fun _ => Only.topNode _ _ _ _ _ _)
        (fun _ => Short.Only.pure' _))

variable [Params]

omit [Params] in
theorem Only.surrogate (parameter : PublicParameter) (seed : MasterSeed) (level : Nat) :
    Short.Only (surrogate parameter seed level : OracleComp HashSpec Digest) := by
  unfold Sphincs.Seeded.surrogate
  split
  · exact Short.Only.deriveKey _ _ _
  · exact Short.Only.pure' _

theorem Only.spineNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) : ∀ steps, Short.Only (spineNode parameter lay tree seed steps :
      OracleComp HashSpec Digest)
  | 0 => by
      rw [Sphincs.Seeded.spineNode]
      exact Only.treeNode _ _ _ _ _ _
  | steps + 1 => by
      rw [Sphincs.Seeded.spineNode]
      refine Short.Only.bind (Only.spineNode parameter lay tree seed steps) (fun _ =>
        Short.Only.bind (Only.surrogate _ _ _) (fun _ => ?_))
      dsimp only
      exact Short.Only.ite _ (Short.Only.tweakableHash _ _ _ (by rw [nodePayload_length]; omega))
        (Short.Only.tweakableHash _ _ _ (by rw [nodePayload_length]; omega))

theorem Only.treeRoot (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) : Short.Only (treeRoot parameter lay tree seed : OracleComp HashSpec Digest) :=
  Only.spineNode _ _ _ _ _

theorem Only.treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) :
    Short.Only (treePath parameter lay tree seed leaf :
      OracleComp HashSpec (Fin (layerHeight lay) → Digest)) :=
  Short.Only.sequenceFin _ fun level => by
    split
    · exact Only.treeNode _ _ _ _ _ _
    · exact Only.surrogate _ _ _

theorem Only.keygenFromMaster (seed : MasterSeed) :
    Short.Only (keygenFromMaster seed : OracleComp HashSpec (PublicKey × SecretKey)) := by
  unfold Sphincs.Seeded.keygenFromMaster
  exact Short.Only.bind (Short.Only.deriveKey _ _ _) (fun _ =>
    Short.Only.bind (Only.treeRoot _ _ _ _) (fun _ => Short.Only.pure' _))

theorem Only.keygenFromSeed (seed : MasterSeed) :
    Short.Only (keygenFromSeed seed : OracleComp HashSpec (PublicKey × SecretKey)) := by
  unfold Sphincs.Seeded.keygenFromSeed
  exact Short.Only.bind (Short.Only.schemeSeed _) (fun _ => Only.keygenFromMaster _)

theorem Only.signAttempt (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    Short.Only (signAttempt secretKey message randomness : OracleComp HashSpec (Option Index)) := by
  unfold Sphincs.Seeded.signAttempt
  exact Short.Only.bind (Short.Only.messageDigestCall _ _ _ _) (fun _ =>
    Short.Only.ite _ (Short.Only.pure' _) (Short.Only.pure' _))

attribute [local irreducible] Sphincs.Seeded.treeNode Sphincs.Seeded.subNode
  Sphincs.Seeded.topNode Sphincs.Seeded.otsSignFrom Sphincs.Seeded.forestKey
  Sphincs.Seeded.treePath

theorem Only.signLayer (secretKey : SecretKey) (index : Index) (lay : Layer) :
    Short.Only (signLayer secretKey index lay : OracleComp HashSpec (Option (LayerSignature lay))) := by
  unfold Sphincs.Seeded.signLayer Sphincs.Seeded.layerMessage Sphincs.Seeded.otsSign
  dsimp only
  generalize treeIndexAt index lay = tree
  generalize leafIndexAt index lay = leaf
  refine Short.Only.bind (Only.forestKey _ _ _) (fun _ => ?_)
  refine Short.Only.bind (Only.otsSignFrom _ _ _ _ _ _ _ _) (fun result => ?_)
  rcases result with _ | ⟨counter, values⟩
  · exact Short.Only.pure' _
  · exact Short.Only.bind (Only.treePath _ _ _ _ _) (fun _ => Short.Only.pure' _)

end Seeded

variable [Params]

attribute [local irreducible] Sphincs.Seeded.signLayer Sphincs.Seeded.forestOpen

theorem Only.finishSign (secretKey : Sphincs.Seeded.SecretKey) (message : Message)
    (randomness : Randomness) :
    Only (Randomized.finishSign secretKey message randomness :
      OracleComp HashSpec (Option Signature)) := by
  unfold Randomized.finishSign
  refine Only.bind (Only.messageDigest _ _ _ _) (fun digest => ?_)
  dsimp only
  generalize digestIndex digest = index
  generalize digestMarks digest = marks
  refine Only.bind (Seeded.Only.forestOpen _ _ _ _) (fun _ => ?_)
  unfold sequenceLayers
  refine Only.bind ?_ (fun layers => ?_)
  · exact Only.bind (Seeded.Only.signLayer secretKey index topLayer) (fun top => by
      rcases top with _ | top <;> exact Only.pure' _)
  · rcases layers with _ | layers <;> exact Only.pure' _

end Sphincs.Security.Short
