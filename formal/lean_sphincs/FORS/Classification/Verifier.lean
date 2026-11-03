import FORS.Classification.Chain
import FORS.Scheme.Correctness

/-! The verifier's walk up the layers exposes, at every layer, its WOTS+C leaf and its Merkle fold in
its query trace: the bottom layer's key signs the recovered FORS key, each layer above signs the
fold of the layer below, and the top layer's fold is the public root. -/

open OracleComp OracleSpec

namespace FORS.Security

variable [Params]

open Concrete

attribute [local semireducible] Concrete.verify
attribute [local irreducible] messageDigest forsRecover otsLeaf treeFold

theorem layerUp_top : layerUp (numLayers - 1) = topLayer := by
  apply Fin.ext
  simp [layerUp, topLayer]

theorem verify_eq_layers (pk : PublicKey) (message : Message) (signature : Signature) :
    (Concrete.verify pk message signature : OracleComp HashSpec Bool) = (do
      let digest ← messageDigest pk.parameter pk.root message signature.randomness
      let index := digestIndex digest
      let fts ← forsRecover pk.parameter index (digestLeaves digest) signature.fors
      let some root ← verifyLayers pk.parameter index signature numLayers (rootsPayload fts)
        | return false
      return decide (root = pk.root)) := rfl

/-- Digest used by the verifier, from its single digest call. -/
def verificationDigest (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) : MessageDigest :=
  evalWithAnswerFn f (messageDigest pk.parameter pk.root message signature.randomness :
    OracleComp HashSpec MessageDigest)

/-- The candidate FORS key recovered before WOTS verification. -/
def verificationFors (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) : ForsKey :=
  let digest := verificationDigest f pk message signature
  evalWithAnswerFn f (forsRecover pk.parameter (digestIndex digest) (digestLeaves digest)
    signature.fors : OracleComp HashSpec ForsKey)

/-! ### The walk up the layers -/

section Walk

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)
  (signature : Signature)

/-- The one-time leaf the verifier recovers at a layer from its message, if the counter is admissible. -/
def layerLeaf (lay : Layer) (msg : HashInput) : Option Digest :=
  evalWithAnswerFn f (otsLeaf parameter lay (treeIndexAt index lay) (leafIndexAt index lay) msg
    (signature.layers lay).counter (signature.layers lay).chainValues : OracleComp HashSpec (Option Digest))

/-- The node the verifier folds a layer's leaf to with the layer's path. -/
def layerFold (lay : Layer) (value : Digest) : Digest :=
  evalWithAnswerFn f (treeFold parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
    (signaturePath signature lay) (layerHeight lay) value : OracleComp HashSpec Digest)

/-- The message the verifier gives the key of the layer `k` steps above the bottom: the FORS key
at the bottom, then the fold of the layer below. -/
def walkMessage (key : ForsKey) : Nat → HashInput
  | 0 => rootsPayload key
  | k + 1 => rootPayload (layerFold f parameter index signature (layerUp k)
      ((layerLeaf f parameter index signature (layerUp k) (walkMessage key k)).getD 0))

/-- The fold of the layer `k` steps above the bottom. -/
def walkFold (key : ForsKey) (k : Nat) : Digest :=
  layerFold f parameter index signature (layerUp k)
    ((layerLeaf f parameter index signature (layerUp k) (walkMessage f parameter index signature key k)).getD 0)

theorem walkMessage_succ (key : ForsKey) (k : Nat) :
    walkMessage f parameter index signature key (k + 1) =
      rootPayload (walkFold f parameter index signature key k) := rfl

/-- An accepted walk from the layer `k` steps above the bottom succeeds at every layer above, ends at
the top layer's fold, and runs the leaf recovery and the fold of every layer in its trace. -/
theorem walk_spec (key : ForsKey) (trace : List HashInput) :
    ∀ n k, k + n = numLayers → 0 < n → ∀ root,
      evalWithAnswerFn f (verifyLayers parameter index signature n
        (walkMessage f parameter index signature key k) : OracleComp HashSpec (Option Digest)) =
          some root →
      ContainsRun f trace (verifyLayers parameter index signature n
        (walkMessage f parameter index signature key k) : OracleComp HashSpec (Option Digest)) →
      root = walkFold f parameter index signature key (numLayers - 1) ∧
      ∀ j, k ≤ j → j < numLayers →
        (∃ value, layerLeaf f parameter index signature (layerUp j)
            (walkMessage f parameter index signature key j) = some value) ∧
        ContainsRun f trace (otsLeaf parameter (layerUp j) (treeIndexAt index (layerUp j))
          (leafIndexAt index (layerUp j)) (walkMessage f parameter index signature key j)
          (signature.layers (layerUp j)).counter (signature.layers (layerUp j)).chainValues) ∧
        ContainsRun f trace (treeFold parameter (layerUp j) (treeIndexAt index (layerUp j))
          (leafIndexAt index (layerUp j)) (signaturePath signature (layerUp j)) (layerHeight (layerUp j))
          ((layerLeaf f parameter index signature (layerUp j)
            (walkMessage f parameter index signature key j)).getD 0)) := by
  intro n
  induction n with
  | zero => intro k _ hn; exact absurd hn (Nat.lt_irrefl 0)
  | succ n ih =>
      intro k hkn _ root hroot hrun
      have hn : n < numLayers := by omega
      have hlay : (⟨n, hn⟩ : Layer) = layerUp k := by
        apply Fin.ext; simp only [layerUp]; omega
      rw [verifyLayers, dif_pos hn] at hroot hrun
      rw [hlay] at hroot hrun
      simp only [evalWithAnswerFn_bind] at hroot
      have hrunLeaf := hrun.bind_left
      have hrest := hrun.bind_right
      cases hleaf : layerLeaf f parameter index signature (layerUp k)
          (walkMessage f parameter index signature key k) with
      | none =>
          simp only [layerLeaf] at hleaf
          rw [hleaf] at hroot
          simp at hroot
      | some value =>
          have hleaf' := hleaf
          simp only [layerLeaf] at hleaf'
          rw [hleaf'] at hroot hrest
          simp only [evalWithAnswerFn_bind] at hroot
          have hrunFold := hrest.bind_left
          have hrest2 := hrest.bind_right
          have hfoldEq : walkFold f parameter index signature key k =
              evalWithAnswerFn f (treeFold parameter (layerUp k) (treeIndexAt index (layerUp k))
                (leafIndexAt index (layerUp k)) (signaturePath signature (layerUp k))
                (layerHeight (layerUp k)) value : OracleComp HashSpec Digest) := by
            simp only [walkFold, layerFold, hleaf, Option.getD_some]
          have hcur : ∀ j, k ≤ j → j < k + 1 → j < numLayers →
              (∃ value, layerLeaf f parameter index signature (layerUp j)
                  (walkMessage f parameter index signature key j) = some value) ∧
              ContainsRun f trace (otsLeaf parameter (layerUp j) (treeIndexAt index (layerUp j))
                (leafIndexAt index (layerUp j)) (walkMessage f parameter index signature key j)
                (signature.layers (layerUp j)).counter (signature.layers (layerUp j)).chainValues) ∧
              ContainsRun f trace (treeFold parameter (layerUp j) (treeIndexAt index (layerUp j))
                (leafIndexAt index (layerUp j)) (signaturePath signature (layerUp j))
                (layerHeight (layerUp j))
                ((layerLeaf f parameter index signature (layerUp j)
                  (walkMessage f parameter index signature key j)).getD 0)) := by
            intro j hj1 hj2 _
            have hj : j = k := by omega
            subst hj
            refine ⟨⟨value, hleaf⟩, hrunLeaf, ?_⟩
            rw [hleaf, Option.getD_some]
            exact hrunFold
          by_cases hzero : n = 0
          · subst hzero
            simp only [↓reduceIte, evalWithAnswerFn_pure, Option.some.injEq] at hroot
            have hk : k = numLayers - 1 := by omega
            subst hk
            refine ⟨hroot.symm.trans hfoldEq.symm, fun j hj1 hj2 => hcur j hj1 (by omega) hj2⟩
          · simp only [if_neg hzero] at hroot hrest2
            have hmsg : rootPayload (evalWithAnswerFn f (treeFold parameter (layerUp k)
                (treeIndexAt index (layerUp k)) (leafIndexAt index (layerUp k))
                (signaturePath signature (layerUp k)) (layerHeight (layerUp k)) value
                  : OracleComp HashSpec Digest)) =
                walkMessage f parameter index signature key (k + 1) := by
              rw [walkMessage_succ, hfoldEq]
            rw [hmsg] at hroot hrest2
            obtain ⟨hr, hall⟩ := ih (k + 1) (by omega) (Nat.pos_of_ne_zero hzero) root hroot hrest2
            refine ⟨hr, fun j hj1 hj2 => ?_⟩
            by_cases hjk : j = k
            · exact hcur j hj1 (by omega) hj2
            · exact hall j (by omega) hj2

end Walk

/-- The index the verifier reads from its digest. -/
def verificationIndex (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) : Index :=
  digestIndex (verificationDigest f pk message signature)

/-- The message the verifier gives the key of the layer `k` steps above the bottom. -/
def verificationMessage (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (k : Nat) : HashInput :=
  walkMessage f pk.parameter (verificationIndex f pk message signature) signature
    (verificationFors f pk message signature) k

/-- Successful verification recovers a leaf at every layer, folds the top layer's leaf to the
public root, and runs every layer's leaf recovery and fold in its trace. -/
theorem verified_layers (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature)
    (hverified : evalWithAnswerFn f (Concrete.verify pk message signature : OracleComp HashSpec Bool) = true) :
    walkFold f pk.parameter (verificationIndex f pk message signature) signature
        (verificationFors f pk message signature) (numLayers - 1) = pk.root ∧
    ∀ k, k < numLayers →
      (∃ value, layerLeaf f pk.parameter (verificationIndex f pk message signature) signature
          (layerUp k) (verificationMessage f pk message signature k) = some value) ∧
      ContainsRun f (queriedInputs f (Concrete.verify pk message signature : OracleComp HashSpec Bool))
        (otsLeaf pk.parameter (layerUp k)
          (treeIndexAt (verificationIndex f pk message signature) (layerUp k))
          (leafIndexAt (verificationIndex f pk message signature) (layerUp k))
          (verificationMessage f pk message signature k)
          (signature.layers (layerUp k)).counter (signature.layers (layerUp k)).chainValues) ∧
      ContainsRun f (queriedInputs f (Concrete.verify pk message signature : OracleComp HashSpec Bool))
        (treeFold pk.parameter (layerUp k)
          (treeIndexAt (verificationIndex f pk message signature) (layerUp k))
          (leafIndexAt (verificationIndex f pk message signature) (layerUp k))
          (signaturePath signature (layerUp k)) (layerHeight (layerUp k))
          ((layerLeaf f pk.parameter (verificationIndex f pk message signature) signature
            (layerUp k) (verificationMessage f pk message signature k)).getD 0)) := by
  have hrun : ContainsRun f
      (queriedInputs f (Concrete.verify pk message signature : OracleComp HashSpec Bool))
      (Concrete.verify pk message signature : OracleComp HashSpec Bool) := fun _ hi => hi
  rw [verify_eq_layers] at hrun hverified
  simp only [evalWithAnswerFn_bind] at hverified
  have htail := hrun.bind_right.bind_right
  have hstart : rootsPayload (verificationFors f pk message signature) =
      walkMessage f pk.parameter (verificationIndex f pk message signature) signature
        (verificationFors f pk message signature) 0 := rfl
  change ContainsRun f _ (verifyLayers pk.parameter (verificationIndex f pk message signature) signature
    numLayers (rootsPayload (verificationFors f pk message signature)) >>= _) at htail
  rw [hstart] at htail
  have hwalkRun := htail.bind_left
  cases hwalk : evalWithAnswerFn f (verifyLayers pk.parameter (verificationIndex f pk message signature)
      signature numLayers (walkMessage f pk.parameter (verificationIndex f pk message signature) signature
        (verificationFors f pk message signature) 0) : OracleComp HashSpec (Option Digest)) with
  | none =>
      have hwalk' := hwalk
      simp only [walkMessage, verificationIndex, verificationFors] at hwalk'
      simp only [verificationDigest] at hwalk'
      simp only [hwalk', evalWithAnswerFn_pure, Bool.false_eq_true] at hverified
  | some root =>
      have hwalk' := hwalk
      simp only [walkMessage, verificationIndex, verificationFors] at hwalk'
      simp only [verificationDigest] at hwalk'
      simp only [hwalk', evalWithAnswerFn_pure, decide_eq_true_eq] at hverified
      obtain ⟨hr, hall⟩ := walk_spec f pk.parameter (verificationIndex f pk message signature) signature
        (verificationFors f pk message signature) _ numLayers 0 (Nat.zero_add _) numLayers_pos root hwalk
        (by simpa only [← verify_eq_layers pk message signature] using hwalkRun)
      exact ⟨hr.symm.trans hverified, fun k hk => hall k (Nat.zero_le k) hk⟩

end FORS.Security
