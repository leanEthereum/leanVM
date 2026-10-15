import SphincsFors.Pruning
import SphincsFors.Landing
import SphincsFors.Bytes

/-!
Deterministic Merkle extraction, adapted from leanVM b7a107256's first-divergence argument.
Two paths reaching the same root either agree, cross into the other path's sibling, or make a
different queried input hit a canonical node value. Crossing is essential for a pruned key:
the sibling may be a surrogate rather than the root of a constructed subtree.
-/

open OracleComp OracleSpec

namespace SphincsFors.Security
open Concrete

/-- Inputs on the actual deterministic execution path selected by `f`. -/
def queriedInputs {α : Type} (f : QueryImpl HashSpec Id) (oa : OracleComp HashSpec α) :
    List HashInput :=
  ((simulateQ f.withLogging oa).run).2.map Sigma.fst

@[simp] theorem queriedInputs_pure {α : Type} (f : QueryImpl HashSpec Id) (x : α) :
    queriedInputs f (pure x) = [] := rfl

@[simp] theorem queriedInputs_query_bind {α : Type} (f : QueryImpl HashSpec Id)
    (input : HashInput) (next : HashOutput → OracleComp HashSpec α) :
    queriedInputs f (liftM (HashSpec.query input) >>= next) =
      input :: queriedInputs f (next (f input)) := rfl

theorem queriedInputs_bind {α β : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec α) (next : α → OracleComp HashSpec β) :
    queriedInputs f (oa >>= next) =
      queriedInputs f oa ++ queriedInputs f (next (evalWithAnswerFn f oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind input rest ih =>
      rw [bind_assoc, queriedInputs_query_bind, queriedInputs_query_bind, ih,
        evalWithAnswerFn_bind,
        show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from
          simulateQ_spec_query f input, List.cons_append]

@[simp] theorem queriedInputs_tweakableHash (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    queriedInputs f (tweakableHash parameter domain payload : OracleComp HashSpec Digest) =
      [tweakableHashInput parameter domain payload] := by
  change queriedInputs f (liftM (HashSpec.query (tweakableHashInput parameter domain payload)) >>=
    fun answer => pure (truncateHash answer)) = _
  rw [queriedInputs_query_bind, queriedInputs_pure]

theorem nodePayload_injective {left right left' right' : Digest}
    (h : nodePayload left right = nodePayload left' right') : left = left' ∧ right = right' := by
  obtain ⟨hl, hr⟩ := List.append_inj h (by simp [bytesLE_length])
  exact ⟨bytesLE_injective hl, bytesLE_injective hr⟩

def orderedPayload (bit : Bool) (current sibling : Digest) : HashInput :=
  if bit then nodePayload sibling current else nodePayload current sibling

theorem orderedPayload_injective (bit : Bool) {current sibling current' sibling' : Digest}
    (h : orderedPayload bit current sibling = orderedPayload bit current' sibling') :
    current = current' ∧ sibling = sibling' := by
  cases bit with
  | false => exact nodePayload_injective h
  | true => exact (nodePayload_injective h).symm

theorem orderedPayload_cross {bit bit' : Bool} (hne : bit ≠ bit')
    {current sibling current' sibling' : Digest}
    (h : orderedPayload bit current sibling = orderedPayload bit' current' sibling') :
    current = sibling' ∧ sibling = current' := by
  cases bit <;> cases bit' <;> simp only [ne_eq, not_true_eq_false] at hne
  · exact nodePayload_injective h
  · exact (nodePayload_injective h).symm

/-- The shared binary fold used by the XMSS tree and each FORS tree. -/
def merkleFold (parameter : PublicParameter) (domain : Nat → Nat → HashDomain)
    (index : Nat) (path : Nat → Digest) : Nat → Digest → OracleComp HashSpec Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← merkleFold parameter domain index path levels value
      tweakableHash parameter (domain (levels + 1) (index / 2 ^ (levels + 1)))
        (orderedPayload (index.testBit levels) current (path levels))

def merkleValue (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (domain : Nat → Nat → HashDomain) (index : Nat) (path : Nat → Digest)
    (value : Digest) (levels : Nat) : Digest :=
  evalWithAnswerFn f (merkleFold parameter domain index path levels value)

def merkleInput (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (domain : Nat → Nat → HashDomain) (index : Nat) (path : Nat → Digest)
    (value : Digest) (level : Nat) : HashInput :=
  tweakableHashInput parameter (domain (level + 1) (index / 2 ^ (level + 1)))
    (orderedPayload (index.testBit level)
      (merkleValue f parameter domain index path value level) (path level))

@[simp] theorem merkleValue_zero (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (domain : Nat → Nat → HashDomain) (index : Nat) (path : Nat → Digest) (value : Digest) :
    merkleValue f parameter domain index path value 0 = value := rfl

theorem merkleValue_succ (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (domain : Nat → Nat → HashDomain) (index : Nat) (path : Nat → Digest)
    (value : Digest) (level : Nat) :
    merkleValue f parameter domain index path value (level + 1) =
      truncateHash (f (merkleInput f parameter domain index path value level)) := by
  simp only [merkleValue, merkleFold, evalWithAnswerFn_bind, Completeness.eval_tweakableHash]
  rfl

theorem merkleInput_mem (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (domain : Nat → Nat → HashDomain) (index : Nat) (path : Nat → Digest) (value : Digest)
    (levels level : Nat) (hlevel : level < levels) :
    merkleInput f parameter domain index path value level ∈
      queriedInputs f (merkleFold parameter domain index path levels value) := by
  induction levels with
  | zero => omega
  | succ levels ih =>
      rw [merkleFold, queriedInputs_bind, queriedInputs_tweakableHash, List.mem_append]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlevel with hlt | rfl
      · exact Or.inl (ih hlt)
      · exact Or.inr (by simp only [List.mem_singleton]; rfl)

theorem merkleFold_treeFold (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (path : Nat → Digest) (levels : Nat) (value : Digest) :
    merkleFold parameter (fun level index => .node lay tree level index) leaf.val path levels value =
      (treeFold parameter lay tree leaf path levels value : OracleComp HashSpec Digest) := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      rw [merkleFold, treeFold, ih]
      apply bind_congr
      intro current
      cases leaf.val.testBit levels <;> rfl

theorem quotient_eq_of_parent_bit_eq (index reference level : Nat)
    (hparent : index / 2 ^ (level + 1) = reference / 2 ^ (level + 1))
    (hbit : index.testBit level = reference.testBit level) :
    index / 2 ^ level = reference / 2 ^ level := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at hparent
  have hbit' : (index / 2 ^ level).testBit 0 = (reference / 2 ^ level).testBit 0 := by
    have hx : (index / 2 ^ level).testBit 0 = index.testBit level := by
      simpa only [Nat.zero_add] using (Nat.testBit_add index 0 level).symm
    have hy : (reference / 2 ^ level).testBit 0 = reference.testBit level := by
      simpa only [Nat.zero_add] using (Nat.testBit_add reference 0 level).symm
    rw [hx, hy]
    exact hbit
  have hmod : index / 2 ^ level % 2 = reference / 2 ^ level % 2 := by
    cases hi : (index / 2 ^ level).testBit 0 with
    | false =>
        have hr : (reference / 2 ^ level).testBit 0 = false := hbit'.symm.trans hi
        rw [Nat.mod_two_eq_zero_iff_testBit_zero.mpr hi,
          Nat.mod_two_eq_zero_iff_testBit_zero.mpr hr]
    | true =>
        have hr : (reference / 2 ^ level).testBit 0 = true := hbit'.symm.trans hi
        rw [Nat.mod_two_eq_one_iff_testBit_zero.mpr hi,
          Nat.mod_two_eq_one_iff_testBit_zero.mpr hr]
  have hx := Nat.div_add_mod (index / 2 ^ level) 2
  have hy := Nat.div_add_mod (reference / 2 ^ level) 2
  omega

/-- A different input at the same node address hits the reference value at that address. -/
def MerkleMatch (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (domain : Nat → Nat → HashDomain) (index reference : Nat) (path referencePath : Nat → Digest)
    (value referenceValue : Digest) (level : Nat) : Prop :=
  index / 2 ^ (level + 1) = reference / 2 ^ (level + 1) ∧
  merkleInput f parameter domain index path value level ≠
    merkleInput f parameter domain reference referencePath referenceValue level ∧
  truncateHash (f (merkleInput f parameter domain index path value level)) =
    merkleValue f parameter domain reference referencePath referenceValue (level + 1)

/-- At the first branch separating two paths, the candidate recovers the reference sibling. -/
def MerkleCrossing (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (domain : Nat → Nat → HashDomain) (index reference : Nat) (path referencePath : Nat → Digest)
    (value : Digest) (level : Nat) : Prop :=
  index / 2 ^ (level + 1) = reference / 2 ^ (level + 1) ∧
  index.testBit level ≠ reference.testBit level ∧
  merkleValue f parameter domain index path value level = referencePath level

/-- Backwards extraction without a collision-freeness assumption. Every exceptional node
input lies on the concrete fold's actual query path by `merkleInput_mem`. -/
theorem merkleFold_classification (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (domain : Nat → Nat → HashDomain) (index reference : Nat) (path referencePath : Nat → Digest)
    (value referenceValue : Digest) :
    ∀ levels,
      index / 2 ^ levels = reference / 2 ^ levels →
      merkleValue f parameter domain index path value levels =
        merkleValue f parameter domain reference referencePath referenceValue levels →
      (index = reference ∧ value = referenceValue ∧
        ∀ level, level < levels → path level = referencePath level) ∨
      (∃ level, level < levels ∧
        MerkleCrossing f parameter domain index reference path referencePath value level) ∨
      (∃ level, level < levels ∧
        MerkleMatch f parameter domain index reference path referencePath value referenceValue level) := by
  intro levels
  induction levels with
  | zero =>
      intro hparent hfold
      exact Or.inl ⟨by simpa using hparent, hfold, fun _ h => by omega⟩
  | succ levels ih =>
      intro hparent hfold
      by_cases hinput : merkleInput f parameter domain index path value levels =
          merkleInput f parameter domain reference referencePath referenceValue levels
      · have hpayload : orderedPayload (index.testBit levels)
            (merkleValue f parameter domain index path value levels) (path levels) =
          orderedPayload (reference.testBit levels)
            (merkleValue f parameter domain reference referencePath referenceValue levels)
            (referencePath levels) := by
          unfold merkleInput at hinput
          rw [hparent] at hinput
          exact List.append_cancel_left hinput
        by_cases hbit : index.testBit levels = reference.testBit levels
        · rw [hbit] at hpayload
          obtain ⟨hvalue, hpath⟩ := orderedPayload_injective _ hpayload
          rcases ih (quotient_eq_of_parent_bit_eq _ _ _ hparent hbit) hvalue with
            ⟨hindex, hstart, hpaths⟩ | ⟨level, hlevel, hcross⟩ | ⟨level, hlevel, hmatch⟩
          · refine Or.inl ⟨hindex, hstart, fun level hlevel => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hlevel with hlt | rfl
            · exact hpaths level hlt
            · exact hpath
          · exact Or.inr (Or.inl ⟨level, Nat.lt_succ_of_lt hlevel, hcross⟩)
          · exact Or.inr (Or.inr ⟨level, Nat.lt_succ_of_lt hlevel, hmatch⟩)
        · exact Or.inr (Or.inl ⟨levels, Nat.lt_succ_self _, hparent, hbit,
            (orderedPayload_cross hbit hpayload).1⟩)
      · refine Or.inr (Or.inr ⟨levels, Nat.lt_succ_self _, hparent, hinput, ?_⟩)
        rwa [← merkleValue_succ]

theorem merkleFold_same_index (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (domain : Nat → Nat → HashDomain) (index : Nat) (path referencePath : Nat → Digest)
    (value referenceValue : Digest) (levels : Nat)
    (hfold : merkleValue f parameter domain index path value levels =
      merkleValue f parameter domain index referencePath referenceValue levels) :
    (value = referenceValue ∧ ∀ level, level < levels → path level = referencePath level) ∨
    ∃ level, level < levels ∧
      MerkleMatch f parameter domain index index path referencePath value referenceValue level := by
  rcases merkleFold_classification f parameter domain index index path referencePath value
      referenceValue levels rfl hfold with hgood | ⟨level, _, _, hbit, _⟩ | hmatch
  · exact Or.inl hgood.2
  · exact False.elim (hbit rfl)
  · exact Or.inr hmatch

theorem quotient_eq_above {index reference lower upper : Nat} (hlevels : lower ≤ upper)
    (hquotient : index / 2 ^ lower = reference / 2 ^ lower) :
    index / 2 ^ upper = reference / 2 ^ upper := by
  have hsplit : upper = lower + (upper - lower) := (Nat.add_sub_of_le hlevels).symm
  rw [hsplit, Nat.pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hquotient]

variable [Params]

/-- The actual authentication path of a retained leaf, extended by zero beyond its height. -/
def canonicalTreePath (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) (leaf : LeafIndex) (level : Nat) : Digest :=
  if hlevel : level < layerHeight lay then
    evalWithAnswerFn f (Seeded.treePath parameter lay tree seed leaf :
      OracleComp HashSpec (Fin (layerHeight lay) → Digest)) ⟨level, hlevel⟩
  else 0

theorem canonicalTreePath_surrogate (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) (leaf : LeafIndex) (level : Nat)
    (hlow : subtreeHeight ≤ level) (hhigh : level < totalHeight) :
    canonicalTreePath f parameter lay tree seed leaf level =
      evalWithAnswerFn f (Seeded.surrogate parameter seed level : OracleComp HashSpec Digest) := by
  have hheight : level < layerHeight lay := hhigh
  rw [canonicalTreePath, dif_pos hheight, Completeness.eval_treePath,
    if_neg (Nat.not_lt.mpr hlow)]

theorem canonicalTreePath_root (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) (leaf : LeafIndex)
    (hland : Landed parameter leaf) :
    merkleValue f parameter (fun level index => .node lay tree level index) leaf.val
      (canonicalTreePath f parameter lay tree seed leaf)
      (Completeness.node f parameter lay tree seed 0 leaf.val) totalHeight =
        evalWithAnswerFn f (Seeded.treeRoot parameter lay tree seed : OracleComp HashSpec Digest) := by
  rw [merkleValue, merkleFold_treeFold]
  apply Completeness.eval_treeFold_pruned_path f parameter lay tree seed leaf hland
  intro level hlevel
  exact dif_pos hlevel

/-- A concrete query below a surrogate's level produces that surrogate. Unlike `MerkleMatch`,
the target has no honest node-domain preimage: the key generated it by seed derivation. -/
def SurrogatePreimage (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) (leaf : LeafIndex)
    (path : Nat → Digest) (value : Digest) (level : Nat) : Prop :=
  subtreeHeight ≤ level ∧ 0 < level ∧
  truncateHash (f (merkleInput f parameter (fun height index => .node lay tree height index)
    leaf.val path value (level - 1))) =
      evalWithAnswerFn f (Seeded.surrogate parameter seed level : OracleComp HashSpec Digest)

/-- Within the retained subtree the only alternatives are the exact canonical opening or a
different queried input producing a canonical node value. -/
theorem inside_subtree_treeFold_witness (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (seed : MasterSeed)
    (leaf : LeafIndex) (path : Nat → Digest) (value : Digest) (hland : Landed parameter leaf)
    (hfold : evalWithAnswerFn f (treeFold parameter lay tree leaf path totalHeight value :
      OracleComp HashSpec Digest) =
      evalWithAnswerFn f (Seeded.treeRoot parameter lay tree seed : OracleComp HashSpec Digest)) :
    (value = Completeness.node f parameter lay tree seed 0 leaf.val ∧
      ∀ level, level < totalHeight → path level = canonicalTreePath f parameter lay tree seed leaf level) ∨
    ∃ level, level < totalHeight ∧
      MerkleMatch f parameter (fun height index => .node lay tree height index)
        leaf.val leaf.val path (canonicalTreePath f parameter lay tree seed leaf)
        value (Completeness.node f parameter lay tree seed 0 leaf.val) level := by
  apply merkleFold_same_index
  rw [canonicalTreePath_root f parameter lay tree seed leaf hland,
    merkleValue, merkleFold_treeFold]
  exact hfold

end SphincsFors.Security
