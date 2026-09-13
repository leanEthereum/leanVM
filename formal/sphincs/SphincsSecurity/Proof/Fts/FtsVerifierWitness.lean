import SphincsSecurity.Proof.Reference.VerifierTraceDescent
import SphincsSecurity.Proof.Hypertree.TreeFoldBound
import SphincsSecurity.Proof.Hypertree.GraphPayloadInputs
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalPayloadInputs

def QueriedOutputMatch (f : QueryImpl HashSpec Id) (key : SecretKey) (position : Position) (trace : Trace) : Prop :=
  position.TreeBound ∧ ∃ payload, payload ∈ canonicalPayloadInputs ∧
    (tweakableHashInput key.parameter position.domain payload, f (tweakableHashInput key.parameter position.domain payload)) ∈ trace.toList ∧
    payload ≠ honestPayload f key.parameter key.otsSecret key.ftsSecret position ∧
    truncateHash (f (tweakableHashInput key.parameter position.domain payload)) = honestValue f key.parameter key.otsSecret key.ftsSecret position

namespace FtsVerifierWitness

variable (f : QueryImpl HashSpec Id) (key : SecretKey) (index : Index)

def AtIndex : Position → Prop
  | .ftsLeaf actual _ _ | .ftsNode actual _ _ _ | .ftsRoots actual => actual = index
  | _ => False

def Exception (trace : Trace) : Prop := ∃ position, AtIndex index position ∧ QueriedOutputMatch f key position trace

def Opening (leaves : IndexGroup → FtsLeaf) (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest) : Prop :=
  ∀ tree, secrets tree = key.ftsSecret index tree (leaves (ftsIndexOf tree)) ∧
    ∀ level (hlevel : level < ftsTreeHeight), paths tree ⟨level, hlevel⟩ =
      honestFtsNode f key.parameter index tree (key.ftsSecret index tree) level (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level) 1)

def TrueSecretQuery (tree : FtsTree) (leaf : FtsLeaf) (trace : Trace) : Prop :=
  let input := tweakableHashInput key.parameter (.ftsLeaf index tree leaf) (digestBytes (key.ftsSecret index tree leaf))
  (input, f input) ∈ trace.toList

theorem tree_reference (leaves : IndexGroup → FtsLeaf) (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest)
    (trace : Trace) (hclean : ¬Exception f key index trace) (tree : FtsTree)
    (hfold : ftsFoldValue f key.parameter index tree (leaves (ftsIndexOf tree)) (paths tree)
      (truncateHash (f (tweakableHashInput key.parameter (.ftsLeaf index tree (leaves (ftsIndexOf tree))) (digestBytes (secrets tree))))) ftsTreeHeight =
        honestFtsNode f key.parameter index tree (key.ftsSecret index tree) ftsTreeHeight 0)
    (hrun : ContainsRun f trace (ftsRecover key.parameter index leaves secrets paths)) :
    secrets tree = key.ftsSecret index tree (leaves (ftsIndexOf tree)) ∧
      ∀ level (hlevel : level < ftsTreeHeight), paths tree ⟨level, hlevel⟩ =
        honestFtsNode f key.parameter index tree (key.ftsSecret index tree) level (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level) 1) := by
  let leaf := leaves (ftsIndexOf tree)
  let value := truncateHash (f (tweakableHashInput key.parameter (.ftsLeaf index tree leaf) (digestBytes (secrets tree))))
  have hroot : leaf.val / 2 ^ ftsTreeHeight = 0 := Nat.div_eq_of_lt leaf.isLt
  rcases ftsFold_extract f key.parameter index tree (key.ftsSecret index tree) leaf (paths tree) value ftsTreeHeight (le_refl _)
      (by simpa only [leaf, value, hroot] using hfold) with ⟨hv, hp⟩ | ⟨level, hl, hh⟩
  · rcases ftsLeaf_extract f key.parameter index tree (key.ftsSecret index tree) leaf (secrets tree) hv with hs | hh
    · refine ⟨hs, ?_⟩
      intro level hl
      simpa only [ftsSibling, dif_pos hl, leaf] using hp level hl
    · apply False.elim
      apply hclean
      refine ⟨.ftsLeaf index tree leaf, rfl, trivial, digestBytes (secrets tree), digestBytes_mem_canonicalPayloadInputs _,
        hrun _ (ftsRecover_leaf_query_mem f key.parameter index leaves secrets paths tree), ?_, ?_⟩
      · exact fun he => hh.1 (digestBytes_injective he)
      · simpa only [Position.domain, honestValue_ftsLeaf] using hh.2
  · have hn : leaf.val / 2 ^ (level + 1) < 2 ^ ftsTreeHeight := (Nat.div_le_self _ _).trans_lt leaf.isLt
    apply False.elim
    apply hclean
    refine ⟨.ftsNode index tree ⟨level, hl⟩ ⟨_, hn⟩, rfl,
      fold_node_bound ftsTreeHeight level leaf.val hl leaf.isLt, ftsFoldPayload f key.parameter index tree leaf (paths tree) value level,
      orderedPayload_mem_canonicalPayloadInputs _ _ _,
      hrun _ (ftsRecover_fold_query_mem f key.parameter index leaves secrets paths tree level hl), hh.1, ?_⟩
    simpa only [Position.domain, honestValue_ftsNode] using hh.2

theorem recover_reference (leaves : IndexGroup → FtsLeaf) (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest)
    (trace : Trace) (hclean : ¬Exception f key index trace)
    (hrecover : evalWithAnswerFn f (ftsRecover key.parameter index leaves secrets paths) = honestFtsKey f key.parameter index (key.ftsSecret index))
    (hrun : ContainsRun f trace (ftsRecover key.parameter index leaves secrets paths)) : Opening f key index leaves secrets paths := by
  let roots : FtsTree → Digest := fun tree => evalWithAnswerFn f
    (ftsFold key.parameter index tree (leaves (ftsIndexOf tree)) (paths tree) ftsTreeHeight
      (evalWithAnswerFn f (ftsLeafHash key.parameter index tree (leaves (ftsIndexOf tree)) (secrets tree))))
  by_cases hp : ftsRootsPayload roots = honestPayload f key.parameter key.otsSecret key.ftsSecret (.ftsRoots index)
  · have hr : roots = fun tree => honestFtsNode f key.parameter index tree (key.ftsSecret index tree) ftsTreeHeight 0 := by
      apply TargetSum.ftsRootsPayload_injective
      exact hp
    intro tree
    apply tree_reference f key index leaves secrets paths trace hclean tree _ hrun
    simpa only [roots, evalWithAnswerFn_bind, ftsLeafHash, eval_tweakableHash, ftsFoldValue] using congrFun hr tree
  · apply False.elim
    apply hclean
    refine ⟨.ftsRoots index, rfl, trivial, ftsRootsPayload roots, ftsRootsPayload_mem_canonicalPayloadInputs _, ?_, hp, ?_⟩
    · exact hrun _ (ftsRecover_roots_query_mem f key.parameter index leaves secrets paths)
    · rw [honestValue_ftsRoots]
      simp only [ftsRecover, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, eval_tweakableHash] at hrecover
      change truncateHash (f (tweakableHashInput key.parameter (.ftsRoots index) (ftsRootsPayload roots))) = _
      simpa only [roots, evalWithAnswerFn_bind] using hrecover

theorem opening_trueSecretQuery (leaves : IndexGroup → FtsLeaf) (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest)
    (trace : Trace) (hopening : Opening f key index leaves secrets paths)
    (hrun : ContainsRun f trace (ftsRecover key.parameter index leaves secrets paths)) (tree : FtsTree) :
    TrueSecretQuery f key index tree (leaves (ftsIndexOf tree)) trace := by
  apply hrun
  simpa only [(hopening tree).1] using ftsRecover_leaf_query_mem f key.parameter index leaves secrets paths tree

theorem recover_classification (leaves : IndexGroup → FtsLeaf) (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest)
    (trace : Trace)
    (hrecover : evalWithAnswerFn f (ftsRecover key.parameter index leaves secrets paths) = honestFtsKey f key.parameter index (key.ftsSecret index))
    (hrun : ContainsRun f trace (ftsRecover key.parameter index leaves secrets paths)) :
    (Opening f key index leaves secrets paths ∧ ∀ tree, TrueSecretQuery f key index tree (leaves (ftsIndexOf tree)) trace) ∨ Exception f key index trace := by
  by_cases he : Exception f key index trace
  · exact Or.inr he
  · have ho := recover_reference f key index leaves secrets paths trace he hrecover hrun
    exact Or.inl ⟨ho, opening_trueSecretQuery f key index leaves secrets paths trace ho hrun⟩

end FtsVerifierWitness

end SphincsSecurity.Concrete
