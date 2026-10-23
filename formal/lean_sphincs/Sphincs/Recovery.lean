import Sphincs.Scheme
import Mathlib.Data.Nat.Bitwise

/-!
# Recovery: what the signer produces, the verifier accepts

Adapted from leanVM b7a107256. One-time recovery returns the leaf the signer built,
and each FORS authentication path returns its root. Pruning.lean adds the surrogate spine;
Correctness.lean composes these facts into signer/verifier correctness.

Everything is deterministic once the oracle is fixed, so the whole file works under an answer
function `f`: `evalWithAnswerFn f` reads each algorithm as a plain function of the seed. Nothing
here is probabilistic, and nothing depends on the answers being uniform.
-/

open OracleComp

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Sphincs.Completeness

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
            simp only [walk, eval_otsSecrets]

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

/-- Every codeword has deficit sum 5. -/
theorem lut_sum (t : LutIdx) : ∑ i, (lut t i).val = codewordSum := by
  revert t
  decide +kernel

/-! ## The forest

Each opened chain is the signer's partial walk from the derived secret, so the verifier's `d_i` steps
reach the chain top; the child leaf, the sub-tree fold, the super-child and the top-tree fold then
climb the honest trees up to their two top nodes, and the hash of the top nodes of the 8 trees is the
forest key the bottom layer signed. -/

section Chain

variable (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
  (a : ChildIdx) (i : FChain)

theorem forestWalk_add (start x y : Nat) (value : Digest) :
    forestWalk (m := OracleComp HashSpec) parameter index c s j a i start (x + y) value
      = (do
          let mid ← forestWalk (m := OracleComp HashSpec) parameter index c s j a i start x value
          forestWalk parameter index c s j a i (start + x) y mid) := by
  induction y with
  | zero => simp [forestWalk]
  | succ y ih =>
      show forestWalk (m := OracleComp HashSpec) parameter index c s j a i start (x + y + 1) value = _
      simp only [forestWalk, ih, bind_assoc, Nat.add_assoc]

/-- The value a forest chain reaches after `steps` steps from position `start`. -/
def fwalk (start steps : Nat) (value : Digest) : Digest :=
  evalWithAnswerFn f (forestWalk parameter index c s j a i start steps value)

theorem fwalk_add (start x y : Nat) (value : Digest) :
    fwalk f parameter index c s j a i start (x + y) value
      = fwalk f parameter index c s j a i (start + x) y (fwalk f parameter index c s j a i start x value) := by
  simp only [fwalk, forestWalk_add, evalWithAnswerFn_bind]

/-- The secret `x_{i,0}` of a forest chain, as the seed derives it: a half of the derivation of its
pair of chains. -/
def forestSecret (seed : MasterSeed) : Digest :=
  evalWithAnswerFn f (Seeded.forestStart parameter index c s j a i seed : OracleComp HashSpec Digest)

theorem forestSecret_eq (seed : MasterSeed) :
    forestSecret f parameter index c s j a i seed =
      hashHalf i.val (f (keygenHashInput parameter (.forest index c s j a (fchainPair i)) seed)) := by
  simp only [forestSecret, Seeded.forestStart, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    eval_deriveOutput]

omit i in
/-- The 3 derivations of a child give the secret of each of its 6 chains. -/
@[simp] theorem eval_forestSecrets (seed : MasterSeed) :
    evalWithAnswerFn f (Seeded.forestSecrets parameter index c s j a seed : OracleComp HashSpec (FChain → Digest))
      = fun i => forestSecret f parameter index c s j a i seed := by
  funext i
  simp only [Seeded.forestSecrets, forestSecret_eq, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    eval_sequenceFin, eval_deriveOutput]

/-- The honest forest chain value `x_{i,pos}`. -/
def chainValueOf (seed : MasterSeed) (pos : Nat) : Digest :=
  fwalk f parameter index c s j a i 0 pos (forestSecret f parameter index c s j a i seed)

theorem eval_chainValue (seed : MasterSeed) (pos : Nat) :
    evalWithAnswerFn f (Seeded.chainValue parameter index c s j a i seed pos : OracleComp HashSpec Digest)
      = chainValueOf f parameter index c s j a i seed pos := by
  simp only [Seeded.chainValue, chainValueOf, fwalk, forestSecret, evalWithAnswerFn_bind]

/-- The verifier's half of an opened forest chain reaches the chain top. -/
theorem eval_forestRecoverChain (seed : MasterSeed) (deficit : FPos) :
    evalWithAnswerFn f (forestRecoverChain parameter index c s j a i deficit
        (chainValueOf f parameter index c s j a i seed (chainTop - deficit.val)) : OracleComp HashSpec Digest)
      = chainValueOf f parameter index c s j a i seed chainTop := by
  have hd : deficit.val ≤ chainTop := Nat.le_of_lt_succ deficit.isLt
  have hsplit : chainTop = (chainTop - deficit.val) + deficit.val := (Nat.sub_add_cancel hd).symm
  simp only [chainValueOf]
  conv_rhs => rw [hsplit, fwalk_add, Nat.zero_add]
  rfl

end Chain

section Child

variable (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
  (seed : MasterSeed)

/-- The honest chain tops of a child. -/
def childEnds (a : ChildIdx) : FChain → Digest :=
  fun i => chainValueOf f parameter index c s j a i seed chainTop

/-- The honest leaf of a child. -/
def childLeafValue (a : ChildIdx) : Digest :=
  truncateHash (f (tweakableHashInput parameter (.childLeaf index c s j a)
    (childPayload (childEnds f parameter index c s j seed a))))

theorem eval_childLeaf (a : ChildIdx) :
    evalWithAnswerFn f (Seeded.childLeaf parameter index c s j a seed : OracleComp HashSpec Digest)
      = childLeafValue f parameter index c s j seed a := by
  simp only [Seeded.childLeaf, childLeafHash, childLeafValue, evalWithAnswerFn_bind,
    eval_sequenceFin, eval_forestSecrets, eval_tweakableHash]
  rfl

/-- An honest opening of a child at any codeword recovers the honest leaf. -/
theorem eval_childRecover (a : ChildIdx) (word : Codeword) :
    evalWithAnswerFn f (childRecover parameter index c s j a word
        (fun i => chainValueOf f parameter index c s j a i seed (chainTop - (word i).val))
        : OracleComp HashSpec Digest)
      = childLeafValue f parameter index c s j seed a := by
  simp only [childRecover, childLeafHash, childLeafValue, evalWithAnswerFn_bind,
    eval_sequenceFin, eval_forestRecoverChain, eval_tweakableHash]
  rfl

end Child

section Sub

variable (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
  (seed : MasterSeed)

/-- The honest value of a sub-tree node at tree level `level`. -/
def subNodeValue (level node : Nat) : Digest :=
  evalWithAnswerFn f (Seeded.subNode parameter index c s j seed level node : OracleComp HashSpec Digest)

theorem subNodeValue_succ (level node : Nat) (hlevel : level < subHeight) :
    subNodeValue f parameter index c s j seed (level + 1) node
      = truncateHash (f (tweakableHashInput parameter
          (.subNode index c s j ⟨level, hlevel⟩ ⟨node % 2 ^ subHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩)
          (nodePayload (subNodeValue f parameter index c s j seed level (2 * node))
            (subNodeValue f parameter index c s j seed level (2 * node + 1))))) := by
  simp only [subNodeValue, Seeded.subNode, evalWithAnswerFn_bind, dite_eq_left hlevel, eval_tweakableHash]

theorem subNodeValue_zero (a : ChildIdx) :
    subNodeValue f parameter index c s j seed 0 a.val = childLeafValue f parameter index c s j seed a := by
  have ha : (⟨a.val % 2 ^ subHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : ChildIdx) = a :=
    Fin.ext (Nat.mod_eq_of_lt a.isLt)
  simp only [subNodeValue, Seeded.subNode, ha, eval_childLeaf]

/-- Folding the honest child leaf through the honest siblings reaches the honest node above it. -/
theorem eval_subFold_path (a : ChildIdx) (path : Fin subHeight → Digest) :
    ∀ levels : Nat, levels ≤ subHeight →
      (∀ (level : Nat) (hlevel : level < subHeight), level < levels →
        path ⟨level, hlevel⟩ = subNodeValue f parameter index c s j seed level (Nat.xor (a.val / 2 ^ level) 1)) →
      evalWithAnswerFn f (subFold parameter index c s j a path levels
          (subNodeValue f parameter index c s j seed 0 a.val) : OracleComp HashSpec Digest)
        = subNodeValue f parameter index c s j seed levels (a.val / 2 ^ levels) := by
  intro levels
  induction levels with
  | zero => intro _ _; simp [subFold]
  | succ levels ih =>
      intro hheight hpath
      have hlevels : levels < subHeight := Nat.lt_of_succ_le hheight
      rw [subFold, evalWithAnswerFn_bind,
        ih (Nat.le_of_succ_le hheight) (fun level hlevel hlt => hpath level hlevel (Nat.lt_succ_of_lt hlt))]
      rw [dite_eq_left hlevels, hpath levels hlevels (Nat.lt_succ_self levels),
        subNodeValue_succ f parameter index c s j seed levels _ hlevels]
      have hnode : (⟨a.val / 2 ^ (levels + 1), Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt⟩ : ChildIdx)
          = ⟨a.val / 2 ^ (levels + 1) % 2 ^ subHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ :=
        Fin.ext (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt)).symm
      cases hbit : a.val.testBit levels with
      | true =>
          obtain ⟨hcur, hsib⟩ := parts_odd a.val levels hbit
          simp only [ite_true, eval_tweakableHash, hnode]
          rw [hsib, hcur]
      | false =>
          obtain ⟨hcur, hsib⟩ := parts_even a.val levels hbit
          simp only [Bool.false_eq_true, ite_false, eval_tweakableHash, hnode]
          rw [hsib, hcur]

end Sub

section Top

variable (parameter : PublicParameter) (index : Index) (c : Coord) (seed : MasterSeed)

/-- The honest value of a super-child. -/
def superValue (s : SuperIdx) : Digest :=
  evalWithAnswerFn f (Seeded.superNode parameter index c s seed : OracleComp HashSpec Digest)

/-- The honest value of a top-tree node at tree level `level`. -/
def topNodeValue (level node : Nat) : Digest :=
  evalWithAnswerFn f (Seeded.topNode parameter index c seed level node : OracleComp HashSpec Digest)

theorem topNodeValue_succ (level node : Nat) (hlevel : level < topHeight) :
    topNodeValue f parameter index c seed (level + 1) node
      = truncateHash (f (tweakableHashInput parameter
          (.topNode index c ⟨level, hlevel⟩ ⟨node % 2 ^ topHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩)
          (nodePayload (topNodeValue f parameter index c seed level (2 * node))
            (topNodeValue f parameter index c seed level (2 * node + 1))))) := by
  simp only [topNodeValue, Seeded.topNode, evalWithAnswerFn_bind, dite_eq_left hlevel, eval_tweakableHash]

theorem topNodeValue_zero (s : SuperIdx) :
    topNodeValue f parameter index c seed 0 s.val = superValue f parameter index c seed s := by
  have hs : (⟨s.val % 2 ^ topHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : SuperIdx) = s :=
    Fin.ext (Nat.mod_eq_of_lt s.isLt)
  simp only [topNodeValue, Seeded.topNode, hs, superValue]

theorem eval_topFold_path (s : SuperIdx) (path : Fin topHeight → Digest) :
    ∀ levels : Nat, levels ≤ topHeight →
      (∀ (level : Nat) (hlevel : level < topHeight), level < levels →
        path ⟨level, hlevel⟩ = topNodeValue f parameter index c seed level (Nat.xor (s.val / 2 ^ level) 1)) →
      evalWithAnswerFn f (topFold parameter index c s path levels
          (topNodeValue f parameter index c seed 0 s.val) : OracleComp HashSpec Digest)
        = topNodeValue f parameter index c seed levels (s.val / 2 ^ levels) := by
  intro levels
  induction levels with
  | zero => intro _ _; simp [topFold]
  | succ levels ih =>
      intro hheight hpath
      have hlevels : levels < topHeight := Nat.lt_of_succ_le hheight
      rw [topFold, evalWithAnswerFn_bind,
        ih (Nat.le_of_succ_le hheight) (fun level hlevel hlt => hpath level hlevel (Nat.lt_succ_of_lt hlt))]
      rw [dite_eq_left hlevels, hpath levels hlevels (Nat.lt_succ_self levels),
        topNodeValue_succ f parameter index c seed levels _ hlevels]
      have hnode : (⟨s.val / 2 ^ (levels + 1), Nat.lt_of_le_of_lt (Nat.div_le_self _ _) s.isLt⟩ : SuperIdx)
          = ⟨s.val / 2 ^ (levels + 1) % 2 ^ topHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ :=
        Fin.ext (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) s.isLt)).symm
      cases hbit : s.val.testBit levels with
      | true =>
          obtain ⟨hcur, hsib⟩ := parts_odd s.val levels hbit
          simp only [ite_true, eval_tweakableHash, hnode]
          rw [hsib, hcur]
      | false =>
          obtain ⟨hcur, hsib⟩ := parts_even s.val levels hbit
          simp only [Bool.false_eq_true, ite_false, eval_tweakableHash, hnode]
          rw [hsib, hcur]

end Top

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

variable (parameter : PublicParameter) (index : Index) (c : Coord) (seed : MasterSeed)

/-- The two honest level-2 nodes of a sub-tree, the inputs of its super-child. -/
def subTopsValue (s : SuperIdx) (j : SubIdx) : Digest × Digest :=
  (subNodeValue f parameter index c s j seed (subHeight - 1) 0,
    subNodeValue f parameter index c s j seed (subHeight - 1) 1)

/-- The two honest level-3 nodes of a top tree, the inputs of the forest key. -/
def topTopsValue : Digest × Digest :=
  (topNodeValue f parameter index c seed (topHeight - 1) 0,
    topNodeValue f parameter index c seed (topHeight - 1) 1)

theorem superValue_eq (s : SuperIdx) :
    superValue f parameter index c seed s =
      truncateHash (f (tweakableHashInput parameter (.superChild index c s)
        (superPayload (subTopsValue f parameter index c seed s)))) := by
  simp only [superValue, Seeded.superNode, superHash, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    eval_sequenceFin, eval_tweakableHash]
  rfl

theorem forestKey_eq :
    evalWithAnswerFn f (Seeded.forestKey parameter index seed : OracleComp HashSpec Digest) =
      truncateHash (f (tweakableHashInput parameter (.roots index)
        (rootsPayload fun c => topTopsValue f parameter index c seed))) := by
  simp only [Seeded.forestKey, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_sequenceFin,
    eval_tweakableHash]
  rfl

end Tops

section Key

variable (parameter : PublicParameter) (index : Index) (seed : MasterSeed)

/-- The honest opening of one coordinate, component by component. -/
theorem eval_coordOpen (c : Coord) (mark : CoordMark) :
    evalWithAnswerFn f (Seeded.coordOpen parameter index c mark seed : OracleComp HashSpec CoordOpening)
      = ⟨fun j => ⟨fun i => chainValueOf f parameter index c mark.super j (mark.child j) i seed
            (chainTop - (lut (mark.word j) i).val),
          fun level => subNodeValue f parameter index c mark.super j seed level.val
            (Nat.xor ((mark.child j).val / 2 ^ level.val) 1)⟩,
        fun level => topNodeValue f parameter index c seed level.val
          (Nat.xor (mark.super.val / 2 ^ level.val) 1)⟩ := by
  simp only [Seeded.coordOpen, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_sequenceFin,
    eval_forestSecrets, chainValueOf, fwalk, subNodeValue, topNodeValue]

/-- The verifier recovers the two honest level-3 nodes of every coordinate. -/
theorem eval_coordRecover (c : Coord) (mark : CoordMark) :
    evalWithAnswerFn f (coordRecover parameter index c mark
        (evalWithAnswerFn f (Seeded.coordOpen parameter index c mark seed : OracleComp HashSpec CoordOpening))
        : OracleComp HashSpec (Digest × Digest))
      = topTopsValue f parameter index c seed := by
  have hsub : ∀ jj : SubIdx,
      orderTops ((mark.child jj).val.testBit (subHeight - 1))
        (evalWithAnswerFn f (subFold parameter index c mark.super jj (mark.child jj)
          (fun level => subNodeValue f parameter index c mark.super jj seed level.val
            (Nat.xor ((mark.child jj).val / 2 ^ level.val) 1)) (subHeight - 1)
          (evalWithAnswerFn f (childRecover parameter index c mark.super jj (mark.child jj) (lut (mark.word jj))
            (fun i => chainValueOf f parameter index c mark.super jj (mark.child jj) i seed
              (chainTop - (lut (mark.word jj) i).val)) : OracleComp HashSpec Digest)) : OracleComp HashSpec Digest))
        (subNodeValue f parameter index c mark.super jj seed subTopLevel.val
          (Nat.xor ((mark.child jj).val / 2 ^ subTopLevel.val) 1))
        = subTopsValue f parameter index c seed mark.super jj := by
    intro jj
    rw [eval_childRecover, ← subNodeValue_zero,
      eval_subFold_path f parameter index c mark.super jj seed (mark.child jj) _ (subHeight - 1) (by decide)
        (fun level hlevel _ => rfl)]
    refine (orderTops_eq_iff (fun node => subNodeValue f parameter index c mark.super jj seed (subHeight - 1) node)
      (mark.child jj).val (subHeight - 1) ?_ _ _).mpr ⟨rfl, rfl⟩
    have := (mark.child jj).isLt
    simp only [subHeight] at this ⊢
    omega
  have hsuper : evalWithAnswerFn f (superHash parameter index c mark.super
      (subTopsValue f parameter index c seed mark.super) : OracleComp HashSpec Digest)
      = superValue f parameter index c seed mark.super := by
    rw [superValue_eq, superHash, eval_tweakableHash]
  rw [eval_coordOpen]
  simp only [coordRecover, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_sequenceFin, hsub]
  rw [hsuper, ← topNodeValue_zero,
    eval_topFold_path f parameter index c seed mark.super _ (topHeight - 1) (by decide) (fun level hlevel _ => rfl)]
  refine (orderTops_eq_iff (fun node => topNodeValue f parameter index c seed (topHeight - 1) node)
    mark.super.val (topHeight - 1) ?_ _ _).mpr ⟨rfl, rfl⟩
  have := mark.super.isLt
  simp only [topHeight] at this ⊢
  omega

/-- **The verifier recovers the forest key the bottom layer signed.** -/
theorem eval_forestRecover (marks : Coord → CoordMark) :
    evalWithAnswerFn f (forestRecover parameter index marks
        (evalWithAnswerFn f (Seeded.forestOpen parameter index marks seed
          : OracleComp HashSpec (Coord → CoordOpening))) : OracleComp HashSpec Digest)
      = evalWithAnswerFn f (Seeded.forestKey parameter index seed : OracleComp HashSpec Digest) := by
  rw [forestKey_eq]
  simp only [forestRecover, Seeded.forestOpen, evalWithAnswerFn_bind, eval_sequenceFin,
    eval_coordRecover, eval_tweakableHash]

end Key

end Sphincs.Completeness
