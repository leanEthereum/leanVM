import FORS.Scheme.Lemmas
import Mathlib.Data.Nat.Bitwise

/-!
# Recovery: what the signer produces, the verifier accepts

Adapted from leanVM b7a107256. One-time recovery returns the leaf the signer built,
and each FORS path returns its node. Scheme/Pruning.lean adds the surrogate spine;
Scheme/Correctness.lean composes these facts into signer/verifier correctness.

Everything is deterministic once the oracle is fixed, so the whole file works under an answer
function `f`: `evalWithAnswerFn f` reads each algorithm as a plain function of the seed. Nothing
here is probabilistic, and nothing depends on the answers being uniform.
-/

open OracleComp

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

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

@[simp] theorem eval_deriveOutput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) :
    evalWithAnswerFn f (deriveOutput parameter domain seed : OracleComp HashSpec HashOutput)
      = f (keygenHashInput parameter domain seed) := by
  simp [deriveOutput]

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

/-- One chain's secret, as the seed derives it: a half of the derivation of its pair of chains. -/
def otsSecret (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (seed : MasterSeed) (chainIdx : ChainIndex) : Digest :=
  evalWithAnswerFn f (otsStart parameter lay tree leaf chainIdx seed : OracleComp HashSpec Digest)

theorem otsSecret_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (seed : MasterSeed) (chainIdx : ChainIndex) :
    otsSecret f parameter lay tree leaf seed chainIdx =
      hashHalf chainIdx.val (f (keygenHashInput parameter (.ots lay tree leaf (chainPair chainIdx)) seed)) := by
  simp only [otsSecret, otsStart, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_deriveOutput]

/-- The 32 derivations of a one-time key give the secret of each of its 64 chains. -/
@[simp] theorem eval_otsSecrets (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) :
    evalWithAnswerFn f (otsSecrets parameter lay tree leaf seed : OracleComp HashSpec (ChainIndex → Digest))
      = otsSecret f parameter lay tree leaf seed := by
  funext chainIdx
  simp only [otsSecrets, otsSecret_eq, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_sequenceFin,
    eval_deriveOutput]

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
          simp only [if_true, eval_tweakableHash]
          rw [hsib, hcur]
      | false =>
          obtain ⟨hcur, hsib⟩ := parts_even leaf.val levels hbit
          simp only [Bool.false_eq_true, if_false, eval_tweakableHash]
          rw [hsib, hcur]

/-! ## FORS

The opened secret hashes to the honest leaf, the fold climbs the honest tree up to its two top
nodes, and the `2k` top nodes are the FORS key the bottom layer signed. -/

section Tree

variable (parameter : PublicParameter) (index : Index) (κ : FTree) (seed : MasterSeed)

/-- The secret of a FORS leaf, as the seed derives it. -/
def forsSecretValue (leaf : FLeaf) : Digest :=
  evalWithAnswerFn f (Seeded.forsSecret parameter index κ leaf seed : OracleComp HashSpec Digest)

theorem forsSecretValue_eq (leaf : FLeaf) :
    forsSecretValue f parameter index κ seed leaf =
      hashHalf leaf.val (f (keygenHashInput parameter (.fors index κ (leafPair leaf)) seed)) := by
  simp only [forsSecretValue, Seeded.forsSecret, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    eval_deriveOutput]

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

/-- The two leaves below a level-1 node are the even and the odd leaf of one pair. -/
private theorem forsPair_leaves (node : Nat) :
    2 * node % 2 ^ forsHeight % 2 = 0 ∧ (2 * node + 1) % 2 ^ forsHeight % 2 = 1 ∧
      (2 * node + 1) % 2 ^ forsHeight / 2 = 2 * node % 2 ^ forsHeight / 2 := by
  have ha := Params.forsHeight_ge
  have hpow : 2 ^ forsHeight = 2 * 2 ^ (forsHeight - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hM : 0 < 2 ^ (forsHeight - 1) := Nat.two_pow_pos _
  rw [hpow]
  generalize 2 ^ (forsHeight - 1) = M at hM ⊢
  have heven : 2 * node % (2 * M) = 2 * (node % M) := Nat.mul_mod_mul_left 2 node M
  have hodd : (2 * node + 1) % (2 * M) = 2 * (node % M) + 1 := by
    have hlt : 2 * (node % M) + 1 < 2 * M := by have := Nat.mod_lt node hM; omega
    conv_lhs => rw [← Nat.div_add_mod node M]
    rw [show 2 * (M * (node / M) + node % M) + 1 = 2 * (node % M) + 1 + 2 * M * (node / M) by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  rw [heven, hodd]
  omega

/-- The sibling of a leaf is in its pair. -/
private theorem forsSibling_pair (leaf : FLeaf) :
    Nat.xor leaf.val 1 % 2 ^ forsHeight / 2 = leaf.val / 2 := by
  have hl := leaf.isLt
  have ha := Params.forsHeight_ge
  have hpow : 2 ^ forsHeight = 2 * 2 ^ (forsHeight - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  cases hbit : leaf.val.testBit 0 with
  | true =>
      obtain ⟨h1, h2⟩ := odd_parts leaf.val hbit
      rw [h2, Nat.mod_eq_of_lt (by omega)]
      omega
  | false =>
      obtain ⟨h1, h2⟩ := even_parts leaf.val hbit
      rw [h2, Nat.mod_eq_of_lt (by omega)]
      omega

theorem forsNodeValue_succ (level node : Nat) (hlevel : level < forsHeight) :
    forsNodeValue f parameter index κ seed (level + 1) node
      = truncateHash (f (tweakableHashInput parameter
          (.forsNode index κ ⟨level, hlevel⟩ ⟨node % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩)
          (nodePayload (forsNodeValue f parameter index κ seed level (2 * node))
            (forsNodeValue f parameter index κ seed level (2 * node + 1))))) := by
  cases level with
  | zero =>
      obtain ⟨hleft, hright, hpair⟩ := forsPair_leaves node
      have hp : leafPair ⟨(2 * node + 1) % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ =
          leafPair ⟨2 * node % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ := Fin.ext hpair
      rw [forsNodeValue_zero_mod, forsNodeValue_zero_mod]
      rw [forsLeafValue, forsLeafValue, forsSecretValue_eq, forsSecretValue_eq, hp]
      simp only [forsNodeValue, Seeded.forsNode, forsLeafHash, evalWithAnswerFn_bind, eval_deriveOutput,
        eval_tweakableHash, hashHalf, Nat.reduceMod, one_ne_zero, ↓reduceIte]
      rw [if_pos hleft, if_neg (by rw [hright]; decide)]
  | succ level =>
      simp only [forsNodeValue, Seeded.forsNode, evalWithAnswerFn_bind, dif_pos hlevel, eval_tweakableHash]


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
      rw [dif_pos hlevels, hpath levels hlevels (Nat.lt_succ_self levels),
        forsNodeValue_succ f parameter index κ seed levels _ hlevels]
      have hnode : (⟨leaf.val / 2 ^ (levels + 1), Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leaf.isLt⟩ : FLeaf)
          = ⟨leaf.val / 2 ^ (levels + 1) % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ :=
        Fin.ext (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leaf.isLt)).symm
      cases hbit : leaf.val.testBit levels with
      | true =>
          obtain ⟨hcur, hsib⟩ := parts_odd leaf.val levels hbit
          simp only [if_true, eval_tweakableHash, hnode]
          rw [hsib, hcur]
      | false =>
          obtain ⟨hcur, hsib⟩ := parts_even leaf.val levels hbit
          simp only [Bool.false_eq_true, if_false, eval_tweakableHash, hnode]
          rw [hsib, hcur]

end Tree

section Tops

/-- The two top nodes of a tree in index order: the fold reaches the top node above the leaf and the
last path element is the other one. -/
theorem orderTops_eq_iff (value : Nat → Digest) (leaf level : Nat) (hleaf : leaf / 2 ^ level < 2)
    (current sibling : Digest) :
    orderTops (leaf.testBit level) current sibling = (value 0, value 1) ↔
      current = value (leaf / 2 ^ level) ∧ sibling = value (Nat.xor (leaf / 2 ^ level) 1) := by
  have hbit : leaf.testBit level = (leaf / 2 ^ level).testBit 0 := (testBit_div_pow leaf level).symm
  rw [hbit]
  generalize leaf / 2 ^ level = node at hleaf ⊢
  obtain h | h : node = 0 ∨ node = 1 := by omega
  · subst h
    simp only [orderTops, Nat.testBit_zero, Nat.zero_mod, zero_ne_one, decide_false, Bool.false_eq_true,
      ↓reduceIte, Prod.mk.injEq]
    exact Iff.rfl
  · subst h
    simp only [orderTops, Nat.testBit_zero, Nat.one_mod, decide_true, ↓reduceIte, Prod.mk.injEq]
    exact and_comm

variable (parameter : PublicParameter) (index : Index) (seed : MasterSeed)

/-- The two honest level-`(a - 1)` nodes of a FORS tree, its part of the FORS key. -/
def topsValue (κ : FTree) : Digest × Digest :=
  (forsNodeValue f parameter index κ seed (forsHeight - 1) 0,
    forsNodeValue f parameter index κ seed (forsHeight - 1) 1)

theorem forsKey_eq :
    evalWithAnswerFn f (Seeded.forsKey parameter index seed : OracleComp HashSpec ForsKey) =
      fun κ => topsValue f parameter index seed κ := by
  simp only [Seeded.forsKey, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_sequenceFin]
  rfl

end Tops

section Key

variable (parameter : PublicParameter) (index : Index) (seed : MasterSeed)

/-- The honest opening of one tree. -/
theorem eval_treeOpen (κ : FTree) (leaf : FLeaf) :
    evalWithAnswerFn f (Seeded.treeOpen parameter index κ leaf seed : OracleComp HashSpec TreeOpening)
      = ⟨forsSecretValue f parameter index κ seed leaf,
          fun level => forsNodeValue f parameter index κ seed level.val
            (Nat.xor (leaf.val / 2 ^ level.val) 1)⟩ := by
  have hp : leafPair ⟨Nat.xor leaf.val 1 % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ = leafPair leaf :=
    Fin.ext (forsSibling_pair leaf)
  simp only [Seeded.treeOpen, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_sequenceFin,
    eval_deriveOutput, forsSecretValue_eq]
  congr 1
  funext level
  by_cases h0 : level.val = 0
  · simp only [h0, if_true, evalWithAnswerFn_pure, pow_zero, Nat.div_one, forsNodeValue, Seeded.forsNode,
      Seeded.forsSecret, evalWithAnswerFn_bind, eval_deriveOutput, hp]
  · simp only [h0, if_false, forsNodeValue]

/-- The verifier recovers the two honest top nodes of every tree. -/
theorem eval_treeRecover (κ : FTree) (leaf : FLeaf) :
    evalWithAnswerFn f (treeRecover parameter index κ leaf
        (evalWithAnswerFn f (Seeded.treeOpen parameter index κ leaf seed : OracleComp HashSpec TreeOpening))
        : OracleComp HashSpec (Digest × Digest))
      = topsValue f parameter index seed κ := by
  have ha := Params.forsHeight_ge
  rw [eval_treeOpen]
  have hleaf : evalWithAnswerFn f (forsLeafHash parameter index κ leaf
      (forsSecretValue f parameter index κ seed leaf) : OracleComp HashSpec Digest) =
      forsNodeValue f parameter index κ seed 0 leaf.val := by
    rw [forsNodeValue_zero, forsLeafHash, eval_tweakableHash]
    rfl
  simp only [treeRecover, evalWithAnswerFn_bind, evalWithAnswerFn_pure, hleaf]
  rw [eval_forsFold_path f parameter index κ seed leaf _ (forsHeight - 1) (by omega)
    (fun level hlevel _ => rfl)]
  refine (orderTops_eq_iff (fun node => forsNodeValue f parameter index κ seed (forsHeight - 1) node)
    leaf.val (forsHeight - 1) ?_ _ _).mpr ⟨rfl, rfl⟩
  have hl := leaf.isLt
  have : 2 ^ forsHeight = 2 * 2 ^ (forsHeight - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  exact Nat.div_lt_of_lt_mul (by omega)

/-- **The verifier recovers the FORS key the bottom layer signed.** -/
theorem eval_forsRecover (leaves : FTree → FLeaf) :
    evalWithAnswerFn f (forsRecover parameter index leaves
        (evalWithAnswerFn f (Seeded.forsOpen parameter index leaves seed
          : OracleComp HashSpec (FTree → TreeOpening))) : OracleComp HashSpec ForsKey)
      = evalWithAnswerFn f (Seeded.forsKey parameter index seed : OracleComp HashSpec ForsKey) := by
  rw [forsKey_eq]
  simp only [forsRecover, Seeded.forsOpen, eval_sequenceFin, eval_treeRecover]

end Key

end FORS.Completeness
