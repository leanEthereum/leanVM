import SphincsSecurity.Scheme
import Mathlib.Data.Nat.Bitwise

/-!
# Recovery: what the signer produces, the verifier accepts

The specification's §sec:ver argues that each one-time recovery returns the leaf the signer built
and each authentication path returns its root, so verification accepts whenever signing succeeds.
This file is that argument.

Everything is deterministic once the oracle is fixed, so the whole file works under an answer
function `f`: `evalWithAnswerFn f` reads each algorithm as a plain function of the seed. Nothing
here is probabilistic, and nothing depends on the answers being uniform.
-/

open OracleComp

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace SphincsSecurity.Completeness

open Concrete Seeded

-- the attempt limits are `2 ^ 32`; unfolding them unfolds the loops that many times
attribute [local irreducible] digestAttemptLimit encodingAttemptLimit

variable (f : QueryImpl HashSpec Id)

/-! ## Evaluating the hash wrappers -/

@[simp] theorem eval_oracleHash (input : HashInput) :
    evalWithAnswerFn f (oracleHash input : OracleComp HashSpec HashOutput) = f input := by
  simp only [oracleHash, HasQuery.query]
  exact simulateQ_spec_query f input

@[simp] theorem eval_tweakableHash (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    evalWithAnswerFn f (tweakableHash parameter domain payload : OracleComp HashSpec Digest)
      = truncateHash (f (tweakableHashInput parameter domain payload)) := by
  simp [tweakableHash]

@[simp] theorem eval_deriveKey (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) :
    evalWithAnswerFn f (deriveKey parameter domain seed : OracleComp HashSpec Digest)
      = truncateHash (f (keygenHashInput parameter domain seed)) := by
  simp [deriveKey]

@[simp] theorem eval_sequenceFin {α : Type} {n : Nat} (computation : Fin n → OracleComp HashSpec α) :
    evalWithAnswerFn f (sequenceFin computation)
      = fun index => evalWithAnswerFn f (computation index) := by
  induction n with
  | zero => funext index; exact index.elim0
  | succ n ih =>
      funext index
      simp only [sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure, ih]
      cases index using Fin.cases <;> rfl

/-! ## The chain

Steps compose, so the verifier's half of a chain, walked from the digit the encoding names, reaches
the same endpoint the signer's full walk does. -/

theorem chainWalk_add (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start a b : Nat) (value : Digest) :
    chainWalk (m := OracleComp HashSpec) parameter lay tree leaf chainIdx start (a + b) value
      = (do
          let mid ← chainWalk (m := OracleComp HashSpec) parameter lay tree leaf chainIdx start a value
          chainWalk parameter lay tree leaf chainIdx (start + a) b mid) := by
  induction b with
  | zero => simp [chainWalk]
  | succ b ih =>
      show chainWalk (m := OracleComp HashSpec) parameter lay tree leaf chainIdx start (a + b + 1) value = _
      simp only [chainWalk, ih, bind_assoc, Nat.add_assoc]

/-- The value the signer's chain reaches after `steps` steps from position `start`. -/
def walk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (start steps : Nat) (value : Digest) : Digest :=
  evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start steps value)

theorem walk_add (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (start a b : Nat) (value : Digest) :
    walk f parameter lay tree leaf chainIdx start (a + b) value
      = walk f parameter lay tree leaf chainIdx (start + a) b
          (walk f parameter lay tree leaf chainIdx start a value) := by
  simp only [walk, chainWalk_add, evalWithAnswerFn_bind]

/-- The verifier's recovery of a signed chain value reaches the public endpoint. -/
theorem eval_recoverChain_walk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) (secret : Digest) :
    evalWithAnswerFn f (recoverChain parameter lay tree leaf chainIdx digit
        (walk f parameter lay tree leaf chainIdx 0 digit.val secret))
      = walk f parameter lay tree leaf chainIdx 0 (chainLength - 1) secret := by
  have hdigit : digit.val ≤ chainLength - 1 := Nat.le_of_lt_succ digit.isLt
  have hsplit : chainLength - 1 = digit.val + (chainLength - 1 - digit.val) :=
    (Nat.add_sub_cancel' hdigit).symm
  rw [show walk f parameter lay tree leaf chainIdx 0 (chainLength - 1) secret
      = walk f parameter lay tree leaf chainIdx 0 (digit.val + (chainLength - 1 - digit.val)) secret
      from by rw [← hsplit]]
  rw [walk_add, Nat.zero_add]
  rfl

/-! ## The one-time signature

The signer walks each chain to the digit the encoding names; the verifier walks the rest. -/

/-- One chain's secret, as the seed derives it. -/
def otsSecret (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (seed : MasterSeed) (chainIdx : ChainIndex) : Digest :=
  evalWithAnswerFn f (deriveKey parameter (.ots lay tree leaf chainIdx) seed : OracleComp HashSpec Digest)

/-- One chain's public endpoint. -/
def otsEndpoint (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (seed : MasterSeed) (chainIdx : ChainIndex) : Digest :=
  walk f parameter lay tree leaf chainIdx 0 (chainLength - 1)
    (otsSecret f parameter lay tree leaf seed chainIdx)

@[simp] theorem eval_oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) :
    evalWithAnswerFn f (oneTimePublicKey parameter lay tree leaf seed
        : OracleComp HashSpec (ChainIndex → Digest))
      = otsEndpoint f parameter lay tree leaf seed := by
  funext chainIdx
  simp only [oneTimePublicKey, otsEndpoint, otsSecret, walk, eval_sequenceFin,
    evalWithAnswerFn_bind]

/-- What a successful counter search produced: the counter encodes the message, and every chain value is the signer's partial walk from the derived secret. -/
theorem otsSignFrom_spec (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) (message : Digest) :
    ∀ (attempts start : Nat) {counter : Counter} {values : ChainIndex → Digest},
      evalWithAnswerFn f (otsSignFrom parameter lay tree leaf seed message attempts start
          : OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) = some (counter, values) →
      ∃ encoding, evalWithAnswerFn f (encode parameter lay tree leaf message counter
            : OracleComp HashSpec (Option Encoding)) = some encoding ∧
        ∀ chainIdx, values chainIdx = walk f parameter lay tree leaf chainIdx 0
          (encoding chainIdx).val (otsSecret f parameter lay tree leaf seed chainIdx) := by
  intro attempts
  induction attempts with
  | zero => intro start counter values h; simp [otsSignFrom] at h
  | succ attempts ih =>
      intro start counter values h
      rw [otsSignFrom, evalWithAnswerFn_bind] at h
      cases hencode : evalWithAnswerFn f (encode parameter lay tree leaf message
          (BitVec.ofNat counterBits start) : OracleComp HashSpec (Option Encoding)) with
      | none => rw [hencode] at h; exact ih (start + 1) h
      | some encoding =>
          rw [hencode] at h
          simp only [eval_sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
            Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hcounter, hvalues⟩ := h
          refine ⟨encoding, ?_, ?_⟩
          · rw [← hcounter]; exact hencode
          · intro chainIdx
            rw [← hvalues]
            simp only [walk, otsSecret]

/-- The verifier's leaf is the leaf the signer's tree was built from. -/
theorem eval_otsLeaf_of_otsSign (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) (message : Digest) {counter : Counter}
    {values : ChainIndex → Digest}
    (h : evalWithAnswerFn f (otsSign parameter lay tree leaf seed message
        : OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) = some (counter, values)) :
    evalWithAnswerFn f (otsLeaf parameter lay tree leaf message counter values
        : OracleComp HashSpec (Option Digest))
      = some (evalWithAnswerFn f (leafHash parameter lay tree leaf
          (otsEndpoint f parameter lay tree leaf seed) : OracleComp HashSpec Digest)) := by
  obtain ⟨encoding, hencode, hvalues⟩ :=
    otsSignFrom_spec f parameter lay tree leaf seed message encodingAttemptLimit 0 h
  have hendpoints : (fun chainIdx => evalWithAnswerFn f
      (recoverChain parameter lay tree leaf chainIdx (encoding chainIdx) (values chainIdx)
        : OracleComp HashSpec Digest))
      = otsEndpoint f parameter lay tree leaf seed := by
    funext chainIdx
    rw [hvalues chainIdx, eval_recoverChain_walk]
    rfl
  rw [otsLeaf, evalWithAnswerFn_bind, hencode]
  simp only [eval_sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure, hendpoints]

/-! ## A layer's Merkle tree

The signer's authentication path is the sibling at every level, so folding the signed leaf through
it climbs the honest tree: one level at a time, the pair the verifier hashes is exactly the pair the
signer's node hashed. -/

private theorem even_parts (value : Nat) (hbit : value.testBit 0 = false) :
    value = 2 * (value / 2) ∧ Nat.xor value 1 = 2 * (value / 2) + 1 := by
  have heven : Even value := Nat.even_iff.mpr (Nat.mod_two_eq_zero_iff_testBit_zero.mpr hbit)
  have hmod : value % 2 = 0 := Nat.even_iff.mp heven
  refine ⟨by omega, ?_⟩
  show value ^^^ 1 = _
  rw [Nat.xor_one_of_even heven]
  omega

private theorem odd_parts (value : Nat) (hbit : value.testBit 0 = true) :
    value = 2 * (value / 2) + 1 ∧ Nat.xor value 1 = 2 * (value / 2) := by
  have hodd : Odd value := Nat.odd_iff.mpr (Nat.mod_two_eq_one_iff_testBit_zero.mpr hbit)
  have hmod : value % 2 = 1 := Nat.odd_iff.mp hodd
  refine ⟨by omega, ?_⟩
  show value ^^^ 1 = _
  rw [Nat.xor_one_of_odd hodd]
  omega

private theorem testBit_div_pow (value level : Nat) :
    (value / 2 ^ level).testBit 0 = value.testBit level := by
  simpa only [Nat.zero_add] using (Nat.testBit_add value 0 level).symm

private theorem div_pow_succ (value level : Nat) :
    value / 2 ^ (level + 1) = value / 2 ^ level / 2 := by
  rw [pow_succ, Nat.div_div_eq_div_mul]

private theorem parts_odd (value level : Nat) (hbit : value.testBit level = true) :
    value / 2 ^ level = 2 * (value / 2 ^ (level + 1)) + 1
      ∧ Nat.xor (value / 2 ^ level) 1 = 2 * (value / 2 ^ (level + 1)) := by
  have hdiv : value / 2 ^ (level + 1) = value / 2 ^ level / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [hdiv]
  exact odd_parts (value / 2 ^ level) (by rw [testBit_div_pow, hbit])

private theorem parts_even (value level : Nat) (hbit : value.testBit level = false) :
    value / 2 ^ level = 2 * (value / 2 ^ (level + 1))
      ∧ Nat.xor (value / 2 ^ level) 1 = 2 * (value / 2 ^ (level + 1)) + 1 := by
  have hdiv : value / 2 ^ (level + 1) = value / 2 ^ level / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [hdiv]
  exact even_parts (value / 2 ^ level) (by rw [testBit_div_pow, hbit])

theorem leafOfNat_val (leaf : LeafIndex) : leafOfNat leaf.val = leaf :=
  Fin.ext (Nat.mod_eq_of_lt leaf.isLt)

/-- The honest value at a node of a layer's tree. -/
def node (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (seed : MasterSeed)
    (level nodeIdx : Nat) : Digest :=
  evalWithAnswerFn f (Seeded.treeNode parameter lay tree seed level nodeIdx)

theorem node_succ (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (level nodeIdx : Nat) :
    node f parameter lay tree seed (level + 1) nodeIdx
      = truncateHash (f (tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx)
          (nodePayload (node f parameter lay tree seed level (2 * nodeIdx))
            (node f parameter lay tree seed level (2 * nodeIdx + 1))))) := by
  simp only [node, Seeded.treeNode, evalWithAnswerFn_bind, eval_tweakableHash]

theorem node_zero (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) :
    node f parameter lay tree seed 0 leaf.val
      = evalWithAnswerFn f (leafHash parameter lay tree leaf
          (otsEndpoint f parameter lay tree leaf seed) : OracleComp HashSpec Digest) := by
  simp only [node, Seeded.treeNode, evalWithAnswerFn_bind, leafOfNat_val, eval_oneTimePublicKey]

theorem eval_treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) (level : Fin (layerHeight lay)) :
    evalWithAnswerFn f (Seeded.treePath parameter lay tree seed leaf
        : OracleComp HashSpec (Fin (layerHeight lay) → Digest)) level
      = node f parameter lay tree seed level.val (Nat.xor (leaf.val / 2 ^ level.val) 1) := by
  simp only [Seeded.treePath, eval_sequenceFin, node]

/-- Folding the honest leaf through the honest siblings reaches the honest node above it. -/
theorem eval_treeFold_path (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) (path : Nat → Digest) :
    ∀ levels : Nat, (∀ level, level < levels →
        path level = node f parameter lay tree seed level (Nat.xor (leaf.val / 2 ^ level) 1)) →
      evalWithAnswerFn f (treeFold parameter lay tree leaf path levels
          (node f parameter lay tree seed 0 leaf.val) : OracleComp HashSpec Digest)
        = node f parameter lay tree seed levels (leaf.val / 2 ^ levels) := by
  intro levels
  induction levels with
  | zero => intro _; simp [treeFold]
  | succ levels ih =>
      intro hpath
      rw [treeFold, evalWithAnswerFn_bind,
        ih (fun level hlevel => hpath level (Nat.lt_succ_of_lt hlevel))]
      rw [hpath levels (Nat.lt_succ_self levels), node_succ]
      cases hbit : leaf.val.testBit levels with
      | true =>
          obtain ⟨hcur, hsib⟩ := parts_odd leaf.val levels hbit
          simp only [if_true, eval_tweakableHash]
          rw [hsib, hcur]
      | false =>
          obtain ⟨hcur, hsib⟩ := parts_even leaf.val levels hbit
          simp only [Bool.false_eq_true, if_false, eval_tweakableHash]
          rw [hsib, hcur]

/-! ## The few-time signature

The forest repeats the layer argument at height `a = 10`: the signer opens one secret per tree with
its siblings, so each recovered root is the honest root and the hash of the `k-1` roots is the
few-time public key the bottom layer signed. -/

/-- The honest value at a node of one few-time tree. -/
def ftsNodeValue (parameter : PublicParameter) (index : Index) (tree : FtsTree) (seed : MasterSeed)
    (level nodeIdx : Nat) : Digest :=
  evalWithAnswerFn f (Seeded.ftsNode parameter index tree seed level nodeIdx)

/-- One few-time secret, as the seed derives it. -/
def ftsSecret (parameter : PublicParameter) (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (seed : MasterSeed) : Digest :=
  evalWithAnswerFn f (deriveKey parameter (.fts index tree leaf) seed : OracleComp HashSpec Digest)

theorem ftsLeafOfNat_val (leaf : FtsLeaf) : ftsLeafOfNat leaf.val = leaf :=
  Fin.ext (Nat.mod_eq_of_lt leaf.isLt)

theorem ftsNodeValue_succ (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (seed : MasterSeed) (level nodeIdx : Nat) :
    ftsNodeValue f parameter index tree seed (level + 1) nodeIdx
      = truncateHash (f (tweakableHashInput parameter (.ftsNode index tree (level + 1) nodeIdx)
          (nodePayload (ftsNodeValue f parameter index tree seed level (2 * nodeIdx))
            (ftsNodeValue f parameter index tree seed level (2 * nodeIdx + 1))))) := by
  simp only [ftsNodeValue, Seeded.ftsNode, evalWithAnswerFn_bind, eval_tweakableHash]

theorem ftsNodeValue_zero (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (seed : MasterSeed) (leaf : FtsLeaf) :
    ftsNodeValue f parameter index tree seed 0 leaf.val
      = evalWithAnswerFn f (ftsLeafHash parameter index tree leaf
          (ftsSecret f parameter index tree leaf seed) : OracleComp HashSpec Digest) := by
  simp only [ftsNodeValue, Seeded.ftsNode, evalWithAnswerFn_bind, ftsLeafOfNat_val, ftsSecret]

theorem eval_ftsOpen (parameter : PublicParameter) (index : Index) (seed : MasterSeed)
    (leaves : IndexGroup → FtsLeaf) (tree : FtsTree) (level : Fin ftsTreeHeight) :
    evalWithAnswerFn f (Seeded.ftsOpen parameter index leaves seed
        : OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest)) tree level
      = ftsNodeValue f parameter index tree seed level.val
          (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1) := by
  simp only [Seeded.ftsOpen, eval_sequenceFin, ftsNodeValue]

/-- Folding an opened secret through its siblings reaches the honest node above it. -/
theorem eval_ftsFold_path (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (seed : MasterSeed) (leaf : FtsLeaf) (path : Fin ftsTreeHeight → Digest) :
    ∀ levels : Nat, levels ≤ ftsTreeHeight →
      (∀ (level : Nat) (hlevel : level < ftsTreeHeight), level < levels →
        path ⟨level, hlevel⟩ = ftsNodeValue f parameter index tree seed level
          (Nat.xor (leaf.val / 2 ^ level) 1)) →
      evalWithAnswerFn f (ftsFold parameter index tree leaf path levels
          (ftsNodeValue f parameter index tree seed 0 leaf.val) : OracleComp HashSpec Digest)
        = ftsNodeValue f parameter index tree seed levels (leaf.val / 2 ^ levels) := by
  intro levels
  induction levels with
  | zero => intro _ _; simp [ftsFold]
  | succ levels ih =>
      intro hheight hpath
      have hlevels : levels < ftsTreeHeight := Nat.lt_of_succ_le hheight
      rw [ftsFold, evalWithAnswerFn_bind,
        ih (Nat.le_of_succ_le hheight)
          (fun level hlevel hlt => hpath level hlevel (Nat.lt_succ_of_lt hlt))]
      rw [dif_pos hlevels, hpath levels hlevels (Nat.lt_succ_self levels), ftsNodeValue_succ]
      cases hbit : leaf.val.testBit levels with
      | true =>
          obtain ⟨hcur, hsib⟩ := parts_odd leaf.val levels hbit
          simp only [if_true, eval_tweakableHash]
          rw [hsib, hcur]
      | false =>
          obtain ⟨hcur, hsib⟩ := parts_even leaf.val levels hbit
          simp only [Bool.false_eq_true, if_false, eval_tweakableHash]
          rw [hsib, hcur]

/-- The verifier recovers the few-time public key the signer's bottom layer signed. -/
theorem eval_ftsRecover (parameter : PublicParameter) (index : Index) (seed : MasterSeed)
    (leaves : IndexGroup → FtsLeaf) :
    evalWithAnswerFn f (ftsRecover parameter index leaves
        (fun tree => ftsSecret f parameter index tree (leaves (ftsIndexOf tree)) seed)
        (evalWithAnswerFn f (Seeded.ftsOpen parameter index leaves seed
          : OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest)))
        : OracleComp HashSpec Digest)
      = evalWithAnswerFn f (Seeded.ftsKey parameter index seed : OracleComp HashSpec Digest) := by
  have hroot : ∀ tree : FtsTree,
      evalWithAnswerFn f (ftsFold parameter index tree (leaves (ftsIndexOf tree))
          (evalWithAnswerFn f (Seeded.ftsOpen parameter index leaves seed
            : OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest)) tree)
          ftsTreeHeight
          (evalWithAnswerFn f (ftsLeafHash parameter index tree (leaves (ftsIndexOf tree))
            (ftsSecret f parameter index tree (leaves (ftsIndexOf tree)) seed)
            : OracleComp HashSpec Digest)) : OracleComp HashSpec Digest)
        = ftsNodeValue f parameter index tree seed ftsTreeHeight 0 := by
    intro tree
    rw [← ftsNodeValue_zero]
    rw [eval_ftsFold_path f parameter index tree seed (leaves (ftsIndexOf tree)) _ ftsTreeHeight
      (Nat.le_refl _) (fun level hlevel _ => eval_ftsOpen f parameter index seed leaves tree
        ⟨level, hlevel⟩)]
    congr 1
    exact Nat.div_eq_of_lt (leaves (ftsIndexOf tree)).isLt
  simp only [ftsRecover, Seeded.ftsKey, eval_sequenceFin, evalWithAnswerFn_bind, hroot,
    ftsNodeValue]

/-! ## A layer

One layer signs the root of the tree below it, or the few-time public key at the bottom. -/

/-- The root of the tree layer `lay` carries, on the route `index` selects. -/
def layerRootValue (secretKey : Seeded.SecretKey) (index : Index) (lay : Layer) : Digest :=
  node f secretKey.parameter lay (treeIndexAt index lay) secretKey.seed (layerHeight lay) 0

/-- The message layer `lay` signs. -/
def layerMessageValue (secretKey : Seeded.SecretKey) (index : Index) (lay : Layer) : Digest :=
  evalWithAnswerFn f (Seeded.layerMessage secretKey index lay : OracleComp HashSpec Digest)

theorem layerMessage_eq_root (secretKey : Seeded.SecretKey) (index : Index) (lay : Layer)
    (hbelow : lay.val + 1 < numLayers) :
    layerMessageValue f secretKey index lay
      = layerRootValue f secretKey index ⟨lay.val + 1, hbelow⟩ := by
  simp only [layerMessageValue, Seeded.layerMessage, dif_pos hbelow, layerRootValue,
    Seeded.treeRoot, node]

theorem leafIndexAt_lt (index : Index) (lay : Layer) :
    (leafIndexAt index lay).val < 2 ^ layerHeight lay :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-- What one layer's signature is: a counter search on the layer message, and the signer's path. -/
theorem signLayer_spec (secretKey : Seeded.SecretKey) (index : Index) (lay : Layer)
    {part : LayerSignature lay}
    (h : evalWithAnswerFn f (Seeded.signLayer secretKey index lay
        : OracleComp HashSpec (Option (LayerSignature lay))) = some part) :
    evalWithAnswerFn f (otsSign secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) secretKey.seed (layerMessageValue f secretKey index lay)
        : OracleComp HashSpec (Option (Counter × (ChainIndex → Digest))))
        = some (part.counter, part.chainValues)
      ∧ part.path = evalWithAnswerFn f (Seeded.treePath secretKey.parameter lay
          (treeIndexAt index lay) secretKey.seed (leafIndexAt index lay)
          : OracleComp HashSpec (Fin (layerHeight lay) → Digest)) := by
  simp only [layerMessageValue, Seeded.signLayer, evalWithAnswerFn_bind] at h ⊢
  cases hots : evalWithAnswerFn f (otsSign secretKey.parameter lay (treeIndexAt index lay)
      (leafIndexAt index lay) secretKey.seed
      (evalWithAnswerFn f (Seeded.layerMessage secretKey index lay : OracleComp HashSpec Digest))
      : OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) with
  | none =>
      rw [hots] at h
      simp at h
  | some result =>
      rw [hots] at h
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩

/-- One layer verifies: the counter recovers the signer's leaf and the path climbs to the layer's root. -/
theorem eval_layer (secretKey : Seeded.SecretKey) (index : Index) (lay : Layer)
    (signature : Signature)
    (h : evalWithAnswerFn f (Seeded.signLayer secretKey index lay
        : OracleComp HashSpec (Option (LayerSignature lay))) = some (signature.layers lay)) :
    evalWithAnswerFn f (otsLeaf secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (layerMessageValue f secretKey index lay)
        (signature.layers lay).counter (signature.layers lay).chainValues
        : OracleComp HashSpec (Option Digest))
      = some (node f secretKey.parameter lay (treeIndexAt index lay) secretKey.seed 0
          (leafIndexAt index lay).val)
    ∧ evalWithAnswerFn f (treeFold secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (signaturePath signature lay) (layerHeight lay)
        (node f secretKey.parameter lay (treeIndexAt index lay) secretKey.seed 0
          (leafIndexAt index lay).val) : OracleComp HashSpec Digest)
      = layerRootValue f secretKey index lay := by
  obtain ⟨hots, hpath⟩ := signLayer_spec f secretKey index lay h
  refine ⟨?_, ?_⟩
  · rw [eval_otsLeaf_of_otsSign f secretKey.parameter lay (treeIndexAt index lay)
      (leafIndexAt index lay) secretKey.seed _ hots, node_zero]
  · rw [eval_treeFold_path f secretKey.parameter lay (treeIndexAt index lay) secretKey.seed
      (leafIndexAt index lay) _ (layerHeight lay) ?_]
    · rw [layerRootValue]
      congr 1
      exact Nat.div_eq_of_lt (leafIndexAt_lt index lay)
    · intro level hlevel
      rw [signaturePath, dif_pos hlevel, hpath]
      exact eval_treePath f secretKey.parameter lay (treeIndexAt index lay) secretKey.seed
        (leafIndexAt index lay) ⟨level, hlevel⟩

/-! ## The hypertree

Layer `lay` signs the root of the tree below it, so the value the verifier carries up is the message
the next layer signed, and layer `0`'s root is the public key. -/

theorem treeIndexAt_top (index : Index) : treeIndexAt index topLayer = rootTree := by
  apply Fin.ext
  have hindex : index.val < 2 ^ totalHeight := index.isLt
  simp only [treeIndexAt, heightAbove, topLayer, rootTree]
  norm_num

/-- The message entering the verifier's walk with `remaining` layers left to check. -/
def enterMessage (secretKey : Seeded.SecretKey) (index : Index) : Nat → Digest
  | 0 => layerRootValue f secretKey index topLayer
  | r + 1 => if h : r < numLayers then layerMessageValue f secretKey index ⟨r, h⟩ else 0

theorem layerRootValue_eq_enterMessage (secretKey : Seeded.SecretKey) (index : Index)
    (r : Nat) (h : r < numLayers) :
    layerRootValue f secretKey index ⟨r, h⟩ = enterMessage f secretKey index r := by
  cases r with
  | zero => rfl
  | succ r =>
      rw [enterMessage, dif_pos (Nat.lt_of_succ_lt h)]
      exact (layerMessage_eq_root f secretKey index ⟨r, Nat.lt_of_succ_lt h⟩ h).symm

/-- The verifier's walk up the hypertree ends at the public root. -/
theorem eval_verifyLayers (secretKey : Seeded.SecretKey) (index : Index) (signature : Signature)
    (hlayers : ∀ lay : Layer, evalWithAnswerFn f (Seeded.signLayer secretKey index lay
        : OracleComp HashSpec (Option (LayerSignature lay))) = some (signature.layers lay)) :
    ∀ remaining : Nat, remaining ≤ numLayers →
      evalWithAnswerFn f (verifyLayers secretKey.parameter index signature remaining
          (enterMessage f secretKey index remaining) : OracleComp HashSpec (Option Digest))
        = some (layerRootValue f secretKey index topLayer) := by
  intro remaining
  induction remaining with
  | zero => intro _; rw [verifyLayers]; rfl
  | succ r ih =>
      intro hrem
      have hlayer : r < numLayers := Nat.lt_of_succ_le hrem
      obtain ⟨hleaf, hfold⟩ := eval_layer f secretKey index ⟨r, hlayer⟩ signature (hlayers _)
      rw [verifyLayers, dif_pos hlayer]
      rw [enterMessage, dif_pos hlayer]
      simp only [evalWithAnswerFn_bind, hleaf, hfold]
      rw [layerRootValue_eq_enterMessage f secretKey index r hlayer]
      exact ih (Nat.le_of_succ_le hrem)

/-! ## The signature

The digest loop stops at an admissible digest, and that digest is what the verifier recomputes from
the randomizer the signature carries. -/

attribute [local semireducible] Concrete.verify

/-- The digest the signer accepted. -/
def digestValue (secretKey : Seeded.SecretKey) (message : Message) (randomness : Randomness) :
    MessageDigest :=
  evalWithAnswerFn f (messageDigest secretKey.parameter secretKey.root message randomness
    : OracleComp HashSpec MessageDigest)

theorem signDigestLoop_spec (secretKey : Seeded.SecretKey) (message : Message) :
    ∀ (attempts trial : Nat) {randomness : Randomness} {index : Index}
      {leaves : IndexGroup → FtsLeaf},
      evalWithAnswerFn f (Seeded.signDigestLoop secretKey message attempts trial
          : OracleComp HashSpec (Option (Randomness × Index × (IndexGroup → FtsLeaf))))
          = some (randomness, index, leaves) →
      Admissible (digestValue f secretKey message randomness)
        ∧ index = digestIndex (digestValue f secretKey message randomness)
        ∧ leaves = digestLeaves (digestValue f secretKey message randomness) := by
  intro attempts
  induction attempts with
  | zero => intro trial randomness index leaves h; simp [Seeded.signDigestLoop] at h
  | succ attempts ih =>
      intro trial randomness index leaves h
      simp only [Seeded.signDigestLoop, Seeded.signAttempt, evalWithAnswerFn_bind] at h
      by_cases hadmissible : Admissible (digestValue f secretKey
          (message := message) (randomness := truncateHash (f (randomizerHashInput
            secretKey.parameter secretKey.seed message (BitVec.ofNat 32 trial)))))
      · rw [digestValue] at hadmissible
        simp only [deriveRandomizer, evalWithAnswerFn_bind, eval_oracleHash,
          evalWithAnswerFn_pure, if_pos hadmissible, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨hrand, hindex, hleaves⟩ := h
        subst hrand
        exact ⟨hadmissible, hindex.symm, hleaves.symm⟩
      · rw [digestValue] at hadmissible
        simp only [deriveRandomizer, evalWithAnswerFn_bind, eval_oracleHash,
          evalWithAnswerFn_pure, if_neg hadmissible] at h
        exact ih (trial + 1) h

theorem sequenceLayers_spec {α : Layer → Type}
    (computation : (lay : Layer) → OracleComp HashSpec (Option (α lay)))
    {layers : (lay : Layer) → α lay}
    (h : evalWithAnswerFn f (sequenceLayers computation) = some layers) :
    ∀ lay, evalWithAnswerFn f (computation lay) = some (layers lay) := by
  simp only [sequenceLayers, evalWithAnswerFn_bind] at h
  cases hb : evalWithAnswerFn f (computation bottomLayer) with
  | none =>
      change evalWithAnswerFn f (computation ⟨4, by decide⟩) = none at hb
      rw [hb] at h
      simp at h
  | some bottom =>
      change evalWithAnswerFn f (computation ⟨4, by decide⟩) = some bottom at hb
      rw [hb] at h
      simp only [evalWithAnswerFn_bind] at h
      cases h3 : evalWithAnswerFn f (computation ⟨3, by decide⟩) with
      | none => simp [h3] at h
      | some third =>
          simp only [h3, evalWithAnswerFn_bind] at h
          cases h2 : evalWithAnswerFn f (computation ⟨2, by decide⟩) with
          | none => simp [h2] at h
          | some second =>
              simp only [h2, evalWithAnswerFn_bind] at h
              cases hm : evalWithAnswerFn f (computation middleLayer) with
              | none => simp [hm] at h
              | some middle =>
                  simp only [hm, evalWithAnswerFn_bind] at h
                  cases ht : evalWithAnswerFn f (computation topLayer) with
                  | none => simp [ht] at h
                  | some top =>
                      simp only [ht, evalWithAnswerFn_pure, Option.some.injEq] at h
                      subst h
                      intro lay
                      fin_cases lay
                      · exact ht
                      · exact hm
                      · exact h2
                      · exact h3
                      · exact hb

-- Below, only the shape of `sign` matters, never the trees it walks; sealing them keeps the
-- unfolding shallow.
attribute [local irreducible] Seeded.signDigestLoop Seeded.signLayer Seeded.ftsOpen
  Seeded.treePath Seeded.treeNode Seeded.ftsNode sequenceFin

/-- What a successful signing produced: an admissible digest, the derived few-time secrets and
openings, and one layer signature per layer. -/
theorem sign_spec (secretKey : Seeded.SecretKey) (message : Message) {signature : Signature}
    (h : evalWithAnswerFn f (Seeded.sign secretKey message
        : OracleComp HashSpec (Option Signature)) = some signature) :
    Admissible (digestValue f secretKey message signature.randomness)
      ∧ signature.ftsSecret = (fun tree => ftsSecret f secretKey.parameter
          (digestIndex (digestValue f secretKey message signature.randomness)) tree
          (digestLeaves (digestValue f secretKey message signature.randomness) (ftsIndexOf tree))
          secretKey.seed)
      ∧ signature.ftsPath = evalWithAnswerFn f (Seeded.ftsOpen secretKey.parameter
          (digestIndex (digestValue f secretKey message signature.randomness))
          (digestLeaves (digestValue f secretKey message signature.randomness)) secretKey.seed
          : OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest))
      ∧ ∀ lay : Layer, evalWithAnswerFn f (Seeded.signLayer secretKey
          (digestIndex (digestValue f secretKey message signature.randomness)) lay
          : OracleComp HashSpec (Option (LayerSignature lay))) = some (signature.layers lay) := by
  rw [Seeded.sign, evalWithAnswerFn_bind] at h
  split at h
  next randomness index leaves hloop =>
      obtain ⟨hadmissible, hindex, hleaves⟩ :=
        signDigestLoop_spec f secretKey message digestAttemptLimit 0 hloop
      rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind] at h
      split at h
      next layers hlayers =>
          rw [evalWithAnswerFn_bind] at h
          simp only [evalWithAnswerFn_pure, Option.some.injEq] at h
          subst h
          subst hindex
          subst hleaves
          exact ⟨hadmissible, by simp only [eval_sequenceFin]; rfl, rfl,
            fun lay => sequenceLayers_spec f _ hlayers lay⟩
      next => exact absurd h (by simp)
  next => exact absurd h (by simp)

/-- **Recovery.** A signature the signer produced is one the verifier accepts: `doc/sphincs` §sec:ver. -/
theorem verify_of_sign (secretKey : Seeded.SecretKey) (message : Message) {signature : Signature}
    (hroot : secretKey.root = evalWithAnswerFn f (Seeded.treeRoot secretKey.parameter topLayer
      rootTree secretKey.seed : OracleComp HashSpec Digest))
    (h : evalWithAnswerFn f (Seeded.sign secretKey message
        : OracleComp HashSpec (Option Signature)) = some signature) :
    evalWithAnswerFn f (Concrete.verify ⟨secretKey.root, secretKey.parameter⟩ message signature
      : OracleComp HashSpec Bool) = true := by
  obtain ⟨hadmissible, hsecrets, hpaths, hlayers⟩ := sign_spec f secretKey message h
  set digest := digestValue f secretKey message signature.randomness with hdigest
  set index := digestIndex digest with hindex
  have hbottom : enterMessage f secretKey index numLayers
      = evalWithAnswerFn f (Seeded.ftsKey secretKey.parameter index secretKey.seed
        : OracleComp HashSpec Digest) := by
    rw [show numLayers = 4 + 1 from rfl, enterMessage, dif_pos (by decide : 4 < numLayers),
      layerMessageValue, Seeded.layerMessage, dif_neg (by decide : ¬ 4 + 1 < numLayers)]
  have hkey : evalWithAnswerFn f (ftsRecover secretKey.parameter index (digestLeaves digest)
      signature.ftsSecret signature.ftsPath : OracleComp HashSpec Digest)
      = enterMessage f secretKey index numLayers := by
    rw [hbottom, hsecrets, hpaths, eval_ftsRecover]
  have hroot' : layerRootValue f secretKey index topLayer = secretKey.root := by
    rw [layerRootValue, treeIndexAt_top, hroot, Seeded.treeRoot, node]
  have hdig : evalWithAnswerFn f (messageDigest secretKey.parameter secretKey.root message
      signature.randomness : OracleComp HashSpec MessageDigest) = digest := rfl
  rw [Concrete.verify]
  simp only [evalWithAnswerFn_bind, hdig, ← hindex, if_neg (not_not_intro hadmissible), hkey,
    eval_verifyLayers f secretKey index signature hlayers numLayers (Nat.le_refl _),
    hroot', evalWithAnswerFn_pure, decide_true]

end SphincsSecurity.Completeness
