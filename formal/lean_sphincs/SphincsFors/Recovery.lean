import SphincsFors.Scheme
import Mathlib.Data.Nat.Bitwise

/-!
# Recovery: what the signer produces, the verifier accepts

Adapted from leanVM b7a107256. One-time recovery returns the leaf the signer built,
and each FORS authentication path returns the two top nodes of its tree. Pruning.lean adds the surrogate spine;
Correctness.lean composes these facts into signer/verifier correctness.

Everything is deterministic once the oracle is fixed, so the whole file works under an answer
function `f`: `evalWithAnswerFn f` reads each algorithm as a plain function of the seed. Nothing
here is probabilistic, and nothing depends on the answers being uniform.
-/

open OracleComp

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace SphincsFors

/-! ## Two secrets for one derivation -/

open Seeded in
theorem evenChain_chainPair {chainIdx : ChainIndex} (h : chainIdx.val % 2 = 0) :
    evenChain (chainPair chainIdx) = chainIdx :=
  Fin.ext (by simp only [evenChain, chainPair]; omega)

open Seeded in
theorem oddChain_chainPair {chainIdx : ChainIndex} (h : chainIdx.val % 2 = 1) :
    oddChain (chainPair chainIdx) = chainIdx :=
  Fin.ext (by simp only [oddChain, chainPair]; omega)

/-- The first and the second secret of a hash are its two halves. -/
theorem secretHalf_of_not_second {domain : KeygenDomain} (h : domain.second = false)
    (output : HashOutput) : secretHalf domain output = truncateHash output := by
  simp [secretHalf, h]

theorem secretHalf_of_second {domain : KeygenDomain} (h : domain.second = true)
    (output : HashOutput) : secretHalf domain output = truncateHashHigh output := by
  simp [secretHalf, h]

@[simp] theorem secretHalf_parameter (output : HashOutput) :
    secretHalf .parameter output = truncateHash output := rfl

@[simp] theorem secretHalf_surrogate (level : Fin totalHeight) (output : HashOutput) :
    secretHalf (.surrogate level) output = truncateHash output := rfl

open Seeded in
@[simp] theorem secretHalf_evenChain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (pair : Fin (numChains / 2)) (output : HashOutput) :
    secretHalf (.ots lay tree leaf (evenChain pair)) output = truncateHash output :=
  secretHalf_of_not_second (by simp [KeygenDomain.second, evenChain]) output

open Seeded in
@[simp] theorem secretHalf_oddChain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (pair : Fin (numChains / 2)) (output : HashOutput) :
    secretHalf (.ots lay tree leaf (oddChain pair)) output = truncateHashHigh output :=
  secretHalf_of_second (by simp [KeygenDomain.second, oddChain]) output

open Seeded in
/-- Chains `2 t` and `2 t + 1` are derived by the same hash. -/
theorem keygenHashInput_oddChain (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (pair : Fin (numChains / 2)) (seed : MasterSeed) :
    keygenHashInput parameter (.ots lay tree leaf (oddChain pair)) seed =
      keygenHashInput parameter (.ots lay tree leaf (evenChain pair)) seed := by
  simp only [keygenHashInput, keygenDomainFields, oddChain, evenChain]
  rw [show (2 * pair.val + 1) / 2 = 2 * pair.val / 2 by omega]

theorem ftsLeafOfNat_two_mul_val (nodeIdx : Nat) :
    (Concrete.ftsLeafOfNat (2 * nodeIdx)).val % 2 = 0 := by
  simp only [Concrete.ftsLeafOfNat, ftsTreeHeight]; omega

theorem ftsLeafOfNat_two_mul_add_one_val (nodeIdx : Nat) :
    (Concrete.ftsLeafOfNat (2 * nodeIdx + 1)).val % 2 = 1 := by
  simp only [Concrete.ftsLeafOfNat, ftsTreeHeight]; omega

@[simp] theorem secretHalf_fts_even (index : Index) (tree : FtsTree) (nodeIdx : Nat)
    (output : HashOutput) :
    secretHalf (.fts index tree (Concrete.ftsLeafOfNat (2 * nodeIdx))) output = truncateHash output :=
  secretHalf_of_not_second (by simp [KeygenDomain.second, ftsLeafOfNat_two_mul_val]) output

@[simp] theorem secretHalf_fts_odd (index : Index) (tree : FtsTree) (nodeIdx : Nat)
    (output : HashOutput) :
    secretHalf (.fts index tree (Concrete.ftsLeafOfNat (2 * nodeIdx + 1))) output =
      truncateHashHigh output :=
  secretHalf_of_second (by simp [KeygenDomain.second, ftsLeafOfNat_two_mul_add_one_val]) output

/-- FORS leaves `2 t` and `2 t + 1` are derived by the same hash. -/
theorem keygenHashInput_fts_odd (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (nodeIdx : Nat) (seed : MasterSeed) :
    keygenHashInput parameter (.fts index tree (Concrete.ftsLeafOfNat (2 * nodeIdx + 1))) seed =
      keygenHashInput parameter (.fts index tree (Concrete.ftsLeafOfNat (2 * nodeIdx))) seed := by
  simp only [keygenHashInput, keygenDomainFields, Concrete.ftsLeafOfNat, ftsTreeHeight]
  rw [show (2 * nodeIdx + 1) % 2 ^ 10 / 2 = 2 * nodeIdx % 2 ^ 10 / 2 by omega]

end SphincsFors

namespace SphincsFors.Completeness

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
      = secretHalf domain (f (keygenHashInput parameter domain seed)) := by
  simp [deriveKey]

@[simp] theorem eval_derivePair (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) :
    evalWithAnswerFn f (derivePair parameter domain seed : OracleComp HashSpec (Digest × Digest))
      = (truncateHash (f (keygenHashInput parameter domain seed)),
          truncateHashHigh (f (keygenHashInput parameter domain seed))) := by
  simp [derivePair]

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

/-- The paired derivation gives every chain the value its own derivation would: chain `i` is walked
from the half of the hash at address `i / 2` that `deriveKey` selects. -/
theorem eval_otsValues (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) (steps : ChainIndex → Nat) :
    evalWithAnswerFn f (otsValues parameter lay tree leaf seed steps
        : OracleComp HashSpec (ChainIndex → Digest))
      = fun chainIdx => evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 (steps chainIdx)
          (otsSecret f parameter lay tree leaf seed chainIdx) : OracleComp HashSpec Digest) := by
  funext chainIdx
  simp only [otsValues, otsSecret, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_sequenceFin,
    eval_derivePair, eval_deriveKey, unpairChains]
  rcases Nat.mod_two_eq_zero_or_one chainIdx.val with h | h
  · rw [if_pos h]
    have hc := evenChain_chainPair h
    conv_rhs => rw [← hc]
    rw [secretHalf_evenChain, hc]
  · rw [if_neg (by omega)]
    have hc := oddChain_chainPair h
    conv_rhs => rw [← hc]
    rw [secretHalf_oddChain, keygenHashInput_oddChain, hc]

@[simp] theorem eval_oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) :
    evalWithAnswerFn f (oneTimePublicKey parameter lay tree leaf seed
        : OracleComp HashSpec (ChainIndex → Digest))
      = otsEndpoint f parameter lay tree leaf seed := by
  funext chainIdx
  simp only [oneTimePublicKey, otsEndpoint, walk, eval_otsValues]

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
          simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_otsValues,
            Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hcounter, hvalues⟩ := h
          refine ⟨encoding, ?_, ?_⟩
          · rw [← hcounter]; exact hencode
          · intro chainIdx
            rw [← hvalues]
            simp only [walk]

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
          simp only [if_true, eval_tweakableHash]
          rw [hsib, hcur]
      | false =>
          obtain ⟨hcur, hsib⟩ := parts_even leaf.val levels hbit
          simp only [Bool.false_eq_true, if_false, eval_tweakableHash]
          rw [hsib, hcur]

/-! ## The few-time signature

The forest repeats the layer argument at height `a - 1 = 9`: the signer opens one secret per tree
with its siblings, so each recovered top node is the honest one, the last path element is the other
honest top node, and the hash of the `2 k` top nodes is the few-time public key the bottom layer
signed. -/

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
  cases level with
  | zero =>
      simp only [ftsNodeValue, Seeded.ftsNode, evalWithAnswerFn_bind, eval_tweakableHash,
        eval_derivePair]
      rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, eval_deriveKey, eval_deriveKey,
        secretHalf_fts_even, secretHalf_fts_odd, keygenHashInput_fts_odd]
  | succ level =>
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

omit f in
/-- The top node on the side of a leaf and the other top node, put in node order, are the nodes
`0` and `1` of level `a - 1`. -/
theorem ftsTopPair_eq_iff (g : Nat → Digest) (leaf : FtsLeaf) (node other : Digest) :
    ftsTopPair leaf node other = (g 0, g 1) ↔
      node = g (leaf.val / 2 ^ ftsTopLevel) ∧ other = g (Nat.xor (leaf.val / 2 ^ ftsTopLevel) 1) := by
  have hlt : leaf.val / 2 ^ ftsTopLevel < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    simp [ftsTopLevel, ftsTreeHeight]
  unfold ftsTopPair
  rw [Nat.testBit_eq_decide_div_mod_eq]
  obtain h | h : leaf.val / 2 ^ ftsTopLevel = 0 ∨ leaf.val / 2 ^ ftsTopLevel = 1 := by
    generalize leaf.val / 2 ^ ftsTopLevel = d at hlt
    omega
  · rw [h]
    simp [Prod.ext_iff]
  · rw [h]
    simp [Prod.ext_iff, and_comm]

omit f in
theorem ftsTopPair_canonical (g : Nat → Digest) (leaf : FtsLeaf) :
    ftsTopPair leaf (g (leaf.val / 2 ^ ftsTopLevel)) (g (Nat.xor (leaf.val / 2 ^ ftsTopLevel) 1)) =
      (g 0, g 1) :=
  (ftsTopPair_eq_iff g leaf _ _).mpr ⟨rfl, rfl⟩

/-- The honest two top nodes (level `a - 1`) of one few-time tree. -/
def ftsTopsValue (parameter : PublicParameter) (index : Index) (seed : MasterSeed)
    (tree : FtsTree) : Digest × Digest :=
  (ftsNodeValue f parameter index tree seed ftsTopLevel 0,
    ftsNodeValue f parameter index tree seed ftsTopLevel 1)

/-- The honest few-time key is the hash of the honest top nodes. -/
theorem eval_ftsKey (parameter : PublicParameter) (index : Index) (seed : MasterSeed) :
    evalWithAnswerFn f (Seeded.ftsKey parameter index seed : OracleComp HashSpec Digest) =
      truncateHash (f (tweakableHashInput parameter (.ftsRoots index)
        (ftsTopsPayload (ftsTopsValue f parameter index seed)))) := by
  simp only [Seeded.ftsKey, eval_sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    eval_tweakableHash]
  rfl

/-- The verifier recovers the few-time public key the signer's bottom layer signed. -/
theorem eval_ftsRecover (parameter : PublicParameter) (index : Index) (seed : MasterSeed)
    (leaves : IndexGroup → FtsLeaf) :
    evalWithAnswerFn f (ftsRecover parameter index leaves
        (fun tree => ftsSecret f parameter index tree (leaves (ftsIndexOf tree)) seed)
        (evalWithAnswerFn f (Seeded.ftsOpen parameter index leaves seed
          : OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest)))
        : OracleComp HashSpec Digest)
      = evalWithAnswerFn f (Seeded.ftsKey parameter index seed : OracleComp HashSpec Digest) := by
  have htop : ∀ tree : FtsTree,
      evalWithAnswerFn f (ftsFold parameter index tree (leaves (ftsIndexOf tree))
          (evalWithAnswerFn f (Seeded.ftsOpen parameter index leaves seed
            : OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest)) tree)
          ftsTopLevel
          (evalWithAnswerFn f (ftsLeafHash parameter index tree (leaves (ftsIndexOf tree))
            (ftsSecret f parameter index tree (leaves (ftsIndexOf tree)) seed)
            : OracleComp HashSpec Digest)) : OracleComp HashSpec Digest)
        = ftsNodeValue f parameter index tree seed ftsTopLevel
            ((leaves (ftsIndexOf tree)).val / 2 ^ ftsTopLevel) := by
    intro tree
    rw [← ftsNodeValue_zero]
    exact eval_ftsFold_path f parameter index tree seed (leaves (ftsIndexOf tree)) _ ftsTopLevel
      (by decide) (fun level hlevel _ => eval_ftsOpen f parameter index seed leaves tree
        ⟨level, hlevel⟩)
  rw [eval_ftsKey]
  simp only [ftsRecover, eval_sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure, htop,
    eval_ftsOpen, eval_tweakableHash]
  refine congrArg (fun tops => truncateHash (f (tweakableHashInput parameter (.ftsRoots index)
    (ftsTopsPayload tops)))) (funext fun tree => ?_)
  exact ftsTopPair_canonical (ftsNodeValue f parameter index tree seed ftsTopLevel) _

end SphincsFors.Completeness
