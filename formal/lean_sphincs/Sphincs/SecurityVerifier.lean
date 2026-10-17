import Sphincs.SecurityChainWitness
import Sphincs.Correctness

/-! The actual one-layer verifier exposes its WOTS leaf and Merkle fold in its query trace. -/

open OracleComp OracleSpec

namespace Sphincs.Security
open Concrete

attribute [local semireducible] Concrete.verify
attribute [local irreducible] messageDigest forestRecover otsLeaf treeFold

theorem verify_eq_single_layer (pk : PublicKey) (message : Message) (signature : Signature) :
    (Concrete.verify pk message signature : OracleComp HashSpec Bool) = (do
      let digest ← messageDigest pk.parameter pk.root message signature.randomness
      let index := digestIndex digest
      let fts ← forestRecover pk.parameter index (digestMarks digest) signature.forest
      let some value ← otsLeaf pk.parameter topLayer rootTree index fts
        (signature.layers topLayer).counter (signature.layers topLayer).chainValues | return false
      let root ← treeFold pk.parameter topLayer rootTree index (signaturePath signature topLayer)
        totalHeight value
      return decide (root = pk.root)) := by
  simp only [Concrete.verify, numLayers, verifyLayers]
  simp only [show (0 : Nat) < 1 by decide, ↓reduceDIte, Completeness.treeIndexAt_eq,
    Completeness.leafIndexAt_eq, bind_assoc]
  apply bind_congr
  intro digest
  apply bind_congr
  intro fts
  apply bind_congr
  intro result
  cases result with
  | none => simp
  | some value =>
      simp only [bind_assoc, pure_bind]
      rfl

/-- Digest used by the verifier, from its single digest call. -/
def verificationDigest (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) : MessageDigest :=
  evalWithAnswerFn f (messageDigest pk.parameter pk.root message signature.randomness :
    OracleComp HashSpec MessageDigest)

/-- The candidate forest key recovered before WOTS verification. -/
def verificationForest (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) : Digest :=
  let digest := verificationDigest f pk message signature
  evalWithAnswerFn f (forestRecover pk.parameter (digestIndex digest) (digestMarks digest)
    signature.forest : OracleComp HashSpec Digest)

theorem verification_forest_run (f : QueryImpl HashSpec Id) (pk : PublicKey)
    (message : Message) (signature : Signature) :
    ContainsRun f (queriedInputs f (Concrete.verify pk message signature : OracleComp HashSpec Bool))
      (forestRecover pk.parameter (digestIndex (verificationDigest f pk message signature))
        (digestMarks (verificationDigest f pk message signature)) signature.forest) := by
  have hrun : ContainsRun f
      (queriedInputs f (Concrete.verify pk message signature : OracleComp HashSpec Bool))
      (Concrete.verify pk message signature : OracleComp HashSpec Bool) := fun _ hi => hi
  rw [verify_eq_single_layer] at hrun
  simpa only [← verify_eq_single_layer pk message signature, verificationDigest] using
    hrun.bind_right.bind_left

/-- Successful verification contains a WOTS recovery and a root-matching Merkle fold. -/
theorem verified_tree (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature)
    (hverified : evalWithAnswerFn f (Concrete.verify pk message signature : OracleComp HashSpec Bool) = true) :
    ∃ value,
      evalWithAnswerFn f (otsLeaf pk.parameter topLayer rootTree
        (digestIndex (verificationDigest f pk message signature))
        (verificationForest f pk message signature)
        (signature.layers topLayer).counter (signature.layers topLayer).chainValues :
        OracleComp HashSpec (Option Digest)) = some value ∧
      evalWithAnswerFn f (treeFold pk.parameter topLayer rootTree
        (digestIndex (verificationDigest f pk message signature)) (signaturePath signature topLayer)
        totalHeight value : OracleComp HashSpec Digest) = pk.root ∧
      ContainsRun f (queriedInputs f (Concrete.verify pk message signature : OracleComp HashSpec Bool))
        (otsLeaf pk.parameter topLayer rootTree (digestIndex (verificationDigest f pk message signature))
          (verificationForest f pk message signature)
          (signature.layers topLayer).counter (signature.layers topLayer).chainValues) ∧
      ContainsRun f (queriedInputs f (Concrete.verify pk message signature : OracleComp HashSpec Bool))
        (treeFold pk.parameter topLayer rootTree (digestIndex (verificationDigest f pk message signature))
          (signaturePath signature topLayer) totalHeight value) := by
  have hrun : ContainsRun f
      (queriedInputs f (Concrete.verify pk message signature : OracleComp HashSpec Bool))
      (Concrete.verify pk message signature : OracleComp HashSpec Bool) := fun _ hi => hi
  rw [verify_eq_single_layer] at hrun hverified
  simp only [evalWithAnswerFn_bind] at hverified
  have htail := hrun.bind_right.bind_right
  change ContainsRun f _ (otsLeaf pk.parameter topLayer rootTree
    (digestIndex (verificationDigest f pk message signature))
    (verificationForest f pk message signature)
    (signature.layers topLayer).counter (signature.layers topLayer).chainValues >>= _) at htail
  cases hleaf : evalWithAnswerFn f (otsLeaf pk.parameter topLayer rootTree
      (digestIndex (verificationDigest f pk message signature)) (verificationForest f pk message signature)
      (signature.layers topLayer).counter (signature.layers topLayer).chainValues : OracleComp HashSpec _) with
  | none =>
      have hleaf' := hleaf
      simp only [verificationDigest, verificationForest] at hleaf'
      simp only [hleaf', evalWithAnswerFn_pure, Bool.false_eq_true] at hverified
  | some value =>
      refine ⟨value, rfl, ?_, ?_, ?_⟩
      · have hleaf' := hleaf
        simp only [verificationDigest, verificationForest] at hleaf'
        simpa only [verificationDigest, hleaf', evalWithAnswerFn_bind,
          evalWithAnswerFn_pure, decide_eq_true_eq] using hverified
      · simpa only [← verify_eq_single_layer pk message signature] using htail.bind_left
      · have hrest := htail.bind_right
        rw [hleaf] at hrest
        simpa only [← verify_eq_single_layer pk message signature, verificationDigest] using hrest.bind_left

variable [Params]

/-- All structural exceptions at the single pruned Merkle layer. -/
def TreeException (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed)
    (leaf : LeafIndex) (path : Nat → Digest) (value : Digest) : Prop :=
  (∃ reference : LeafIndex, Landed parameter reference ∧ ∃ level, level < totalHeight ∧
    MerkleMatch f parameter (fun height index => .node topLayer rootTree height index)
      leaf.val reference.val path (canonicalTreePath f parameter topLayer rootTree seed reference)
      value (Completeness.node f parameter topLayer rootTree seed 0 reference.val) level) ∨
  ∃ level, level < totalHeight ∧
    SurrogatePreimage f parameter topLayer rootTree seed leaf path value level

end Sphincs.Security
