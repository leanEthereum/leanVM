module

public import FORS.Scheme.Lemmas
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

/-!
# Recovery: what the signer produces, the verifier accepts

One-time recovery returns the leaf the signer built,
and each FORS path returns its node. Scheme/Pruning.lean adds the surrogate spine;
Scheme/Correctness.lean composes these facts into signer/verifier correctness.

Everything is deterministic once the oracle is fixed, so the whole file works under an answer
function `f`: `evalWithAnswerFn f` reads each algorithm as a plain function of the seed. Nothing
here is probabilistic, and nothing depends on the answers being uniform.
-/

open OracleComp

set_option maxRecDepth 100000

namespace FORS.Completeness

variable [Params]

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

/-- One chain's secret, as the seed derives it: its own derivation. -/
def otsSecret (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (seed : MasterSeed) (chainIdx : ChainIndex) : Digest :=
  evalWithAnswerFn f (otsStart parameter lay tree leaf chainIdx seed : OracleComp HashSpec Digest)

theorem otsSecret_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (seed : MasterSeed) (chainIdx : ChainIndex) :
    otsSecret f parameter lay tree leaf seed chainIdx =
      truncateHash (f (keygenHashInput parameter (.ots lay tree leaf chainIdx) seed)) := by
  simp only [otsSecret, otsStart, eval_deriveKey]

/-- The 64 derivations of a one-time key give the secret of each of its 64 chains. -/
@[simp] theorem eval_otsSecrets (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) :
    evalWithAnswerFn f (otsSecrets parameter lay tree leaf seed : OracleComp HashSpec (ChainIndex → Digest))
      = otsSecret f parameter lay tree leaf seed := by
  funext chainIdx
  simp only [otsSecrets, otsSecret_eq, eval_sequenceFin, eval_deriveKey]

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
  simp only [oneTimePublicKey, otsEndpoint, walk, eval_sequenceFin,
    evalWithAnswerFn_bind, eval_otsSecrets]

/-- What a successful counter search produced: the counter encodes the message, and every chain value is the signer's partial walk from the derived secret. -/
theorem otsSignFrom_spec (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) (message : HashInput) :
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
            simp only [walk, eval_otsSecrets]

/-- The verifier's leaf is the leaf the signer's tree was built from. -/
theorem eval_otsLeaf_of_otsSign (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) (message : HashInput) {counter : Counter}
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
          simp only [ite_true, eval_tweakableHash]
          rw [hsib, hcur]
      | false =>
          obtain ⟨hcur, hsib⟩ := parts_even leaf.val levels hbit
          simp only [Bool.false_eq_true, ite_false, eval_tweakableHash]
          rw [hsib, hcur]

/-! ## FORS

The opened secret hashes to the honest leaf, the fold climbs the honest tree up to its root, and
`T_k` of the `k` roots is the FORS public key the bottom layer signed. -/

section Tree

variable (parameter : PublicParameter) (index : Index) (κ : FTree) (seed : MasterSeed)

/-- The secret of a FORS leaf, as the seed derives it. -/
def forsSecretValue (leaf : FLeaf) : Digest :=
  evalWithAnswerFn f (Seeded.forsSecret parameter index κ leaf seed : OracleComp HashSpec Digest)

theorem forsSecretValue_eq (leaf : FLeaf) :
    forsSecretValue f parameter index κ seed leaf =
      truncateHash (f (keygenHashInput parameter (.fors index κ leaf) seed)) := by
  simp only [forsSecretValue, Seeded.forsSecret, eval_deriveKey]

/-- The honest value of a FORS node at tree level `level`. -/
def forsNodeValue (level node : Nat) : Digest :=
  evalWithAnswerFn f (Seeded.forsNode parameter index κ seed level node : OracleComp HashSpec Digest)

/-- The honest leaf of a FORS tree: the hash of its secret. -/
def forsLeafValue (leaf : FLeaf) : Digest :=
  truncateHash (f (tweakableHashInput parameter (.forsLeaf index κ leaf)
    (bytesLE 16 (forsSecretValue f parameter index κ seed leaf))))

private theorem forsNodeValue_zero_mod (node : Nat) :
    forsNodeValue f parameter index κ seed 0 node =
      forsLeafValue f parameter index κ seed ⟨node % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ := by
  simp only [forsNodeValue, Seeded.forsNode, forsLeafHash, evalWithAnswerFn_bind,
    eval_tweakableHash, forsLeafValue, forsSecretValue]

theorem forsNodeValue_zero (leaf : FLeaf) :
    forsNodeValue f parameter index κ seed 0 leaf.val = forsLeafValue f parameter index κ seed leaf := by
  have hl : (⟨leaf.val % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : FLeaf) = leaf :=
    Fin.ext (Nat.mod_eq_of_lt leaf.isLt)
  rw [forsNodeValue_zero_mod, hl]

theorem forsNodeValue_succ (level node : Nat) (hlevel : level < forsHeight) :
    forsNodeValue f parameter index κ seed (level + 1) node
      = truncateHash (f (tweakableHashInput parameter
          (.forsNode index κ ⟨level, hlevel⟩ ⟨node % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩)
          (nodePayload (forsNodeValue f parameter index κ seed level (2 * node))
            (forsNodeValue f parameter index κ seed level (2 * node + 1))))) := by
  simp only [forsNodeValue, Seeded.forsNode, evalWithAnswerFn_bind, dite_eq_left hlevel, eval_tweakableHash]

/-- Folding the honest leaf through the honest siblings reaches the honest node above it. -/
theorem eval_forsFold_path (leaf : FLeaf) (path : Fin forsHeight → Digest) :
    ∀ levels : Nat, levels ≤ forsHeight →
      (∀ (level : Nat) (hlevel : level < forsHeight), level < levels →
        path ⟨level, hlevel⟩ = forsNodeValue f parameter index κ seed level (Nat.xor (leaf.val / 2 ^ level) 1)) →
      evalWithAnswerFn f (forsFold parameter index κ leaf path levels
          (forsNodeValue f parameter index κ seed 0 leaf.val) : OracleComp HashSpec Digest)
        = forsNodeValue f parameter index κ seed levels (leaf.val / 2 ^ levels) := by
  intro levels
  induction levels with
  | zero => intro _ _; simp [forsFold]
  | succ levels ih =>
      intro hheight hpath
      have hlevels : levels < forsHeight := Nat.lt_of_succ_le hheight
      rw [forsFold, evalWithAnswerFn_bind,
        ih (Nat.le_of_succ_le hheight) (fun level hlevel hlt => hpath level hlevel (Nat.lt_succ_of_lt hlt))]
      rw [dite_eq_left hlevels, hpath levels hlevels (Nat.lt_succ_self levels),
        forsNodeValue_succ f parameter index κ seed levels _ hlevels]
      have hnode : (⟨leaf.val / 2 ^ (levels + 1), Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leaf.isLt⟩ : FLeaf)
          = ⟨leaf.val / 2 ^ (levels + 1) % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ :=
        Fin.ext (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leaf.isLt)).symm
      cases hbit : leaf.val.testBit levels with
      | true =>
          obtain ⟨hcur, hsib⟩ := parts_odd leaf.val levels hbit
          simp only [ite_true, eval_tweakableHash, hnode]
          rw [hsib, hcur]
      | false =>
          obtain ⟨hcur, hsib⟩ := parts_even leaf.val levels hbit
          simp only [Bool.false_eq_true, ite_false, eval_tweakableHash, hnode]
          rw [hsib, hcur]

end Tree

section Key

variable (parameter : PublicParameter) (index : Index) (seed : MasterSeed)

/-- The honest root of a FORS tree, its node at level `a`: its part of the FORS key. -/
def rootValue (κ : FTree) : Digest :=
  forsNodeValue f parameter index κ seed forsHeight 0

@[simp] theorem eval_forsPublicKey (roots : ForsKey) :
    evalWithAnswerFn f (forsPublicKey parameter index roots : OracleComp HashSpec Digest)
      = truncateHash (f (tweakableHashInput parameter (.forsRoots index) (rootsPayload roots))) := by
  simp [forsPublicKey]

/-- The FORS public key is `T_k` of the honest roots. -/
theorem forsKey_eq :
    evalWithAnswerFn f (Seeded.forsKey parameter index seed : OracleComp HashSpec Digest) =
      evalWithAnswerFn f (forsPublicKey parameter index fun κ => rootValue f parameter index seed κ
        : OracleComp HashSpec Digest) := by
  simp only [Seeded.forsKey, evalWithAnswerFn_bind, eval_sequenceFin]
  rfl

/-- The honest opening of one tree. -/
theorem eval_treeOpen (κ : FTree) (leaf : FLeaf) :
    evalWithAnswerFn f (Seeded.treeOpen parameter index κ leaf seed : OracleComp HashSpec TreeOpening)
      = ⟨forsSecretValue f parameter index κ seed leaf,
          fun level => forsNodeValue f parameter index κ seed level.val
            (Nat.xor (leaf.val / 2 ^ level.val) 1)⟩ := by
  simp only [Seeded.treeOpen, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_sequenceFin]
  rfl

/-- The verifier recovers the honest root of every tree. -/
theorem eval_treeRecover (κ : FTree) (leaf : FLeaf) :
    evalWithAnswerFn f (treeRecover parameter index κ leaf
        (evalWithAnswerFn f (Seeded.treeOpen parameter index κ leaf seed : OracleComp HashSpec TreeOpening))
        : OracleComp HashSpec Digest)
      = rootValue f parameter index seed κ := by
  rw [eval_treeOpen]
  have hleaf : evalWithAnswerFn f (forsLeafHash parameter index κ leaf
      (forsSecretValue f parameter index κ seed leaf) : OracleComp HashSpec Digest) =
      forsNodeValue f parameter index κ seed 0 leaf.val := by
    rw [forsNodeValue_zero, forsLeafHash, eval_tweakableHash]
    rfl
  simp only [treeRecover, evalWithAnswerFn_bind, hleaf]
  rw [eval_forsFold_path f parameter index κ seed leaf _ forsHeight le_rfl (fun level hlevel _ => rfl),
    Nat.div_eq_of_lt leaf.isLt]
  rfl

/-- The verifier recovers the honest roots. -/
theorem eval_forsRecover (leaves : FTree → FLeaf) :
    evalWithAnswerFn f (forsRecover parameter index leaves
        (evalWithAnswerFn f (Seeded.forsOpen parameter index leaves seed
          : OracleComp HashSpec (FTree → TreeOpening))) : OracleComp HashSpec ForsKey)
      = fun κ => rootValue f parameter index seed κ := by
  simp only [forsRecover, Seeded.forsOpen, eval_sequenceFin, eval_treeRecover]

/-- **The verifier recovers the FORS public key the bottom layer signed.** -/
theorem eval_forsPublicKey_forsRecover (leaves : FTree → FLeaf) :
    evalWithAnswerFn f (forsPublicKey parameter index
        (evalWithAnswerFn f (forsRecover parameter index leaves
          (evalWithAnswerFn f (Seeded.forsOpen parameter index leaves seed
            : OracleComp HashSpec (FTree → TreeOpening))) : OracleComp HashSpec ForsKey))
        : OracleComp HashSpec Digest)
      = evalWithAnswerFn f (Seeded.forsKey parameter index seed : OracleComp HashSpec Digest) := by
  rw [eval_forsRecover, forsKey_eq]

end Key

end FORS.Completeness
