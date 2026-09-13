import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Scheme.Eval
import SphincsSecurity.Proof.Ots.ExtractChain
import SphincsSecurity.Proof.Fts.ExtractFts
import SphincsSecurity.Proof.Scheme.Support
/-!
# Queries made by verification

The deterministic extraction identifies a particular hash call inside a chain or fold. These lemmas
locate that call in the answer-function execution log used by the support bridge.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter)

theorem sequenceFin_component_query_mem {alpha : Type} {n : Nat}
    (computation : Fin n → OracleComp HashSpec alpha) (index : Fin n) {input : HashInput}
    (hinput : input ∈ queriedInputs f (computation index)) :
    input ∈ queriedInputs f (sequenceFin computation) := by
  induction n with
  | zero => exact index.elim0
  | succ n ih =>
      cases index using Fin.cases with
      | zero =>
          rw [sequenceFin]
          exact queriedInputs_mono_bind_left f (computation 0) _ hinput
      | succ index =>
          rw [sequenceFin]
          apply queriedInputs_mono_bind_right f (computation 0)
          apply queriedInputs_mono_bind_left
          exact ih (fun index : Fin n => computation index.succ) index hinput

theorem chainWalk_query_mem (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (start steps : Nat) (value : Digest) (offset : Nat)
    (hoffset : offset < steps) (hrange : start + offset < chainLength - 1) :
    tweakableHashInput parameter (.chain lay tree leafIdx chainIdx ⟨start + offset, hrange⟩)
        (digestBytes (walkValue f parameter lay tree leafIdx chainIdx start value offset))
      ∈ queriedInputs f (chainWalk parameter lay tree leafIdx chainIdx start steps value) := by
  induction steps generalizing offset with
  | zero => omega
  | succ steps ih =>
      rw [chainWalk]
      split_ifs with hstep
      · rw [queriedInputs_bind]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hoffset with hlt | heq
        · exact List.mem_append_left _ (ih offset hlt hrange)
        · subst offset
          apply List.mem_append_right _
          simp only [walkValue, queriedInputs_tweakableHash, List.mem_singleton]
      · rw [queriedInputs_bind]
        apply List.mem_append_left
        simp only [chainLength, winternitzBits] at hstep hrange
        exact ih offset (by omega) hrange

theorem leafHash_query_mem (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (endpoints : ChainIndex → Digest) :
    tweakableHashInput parameter (.leaf lay tree leafIdx) (leafPayload endpoints)
      ∈ queriedInputs f (leafHash parameter lay tree leafIdx endpoints) := by
  simp [leafHash]

theorem otsLeaf_leaf_query_mem (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leafIdx message counter)
      = some codeword) :
    tweakableHashInput parameter (.leaf lay tree leafIdx)
        (leafPayload fun chainIdx => walkValue f parameter lay tree leafIdx chainIdx
          (codeword chainIdx).val (values chainIdx) (chainLength - 1 - (codeword chainIdx).val))
      ∈ queriedInputs f (otsLeaf parameter lay tree leafIdx message counter values) := by
  simp only [otsLeaf]
  apply queriedInputs_mono_bind_right
  rw [hencode]
  apply queriedInputs_mono_bind_right
  apply queriedInputs_mono_bind_left
  simpa only [evalWithAnswerFn_sequenceFin, recoverChain, walkValue] using
    leafHash_query_mem f parameter lay tree leafIdx
      (fun chainIdx => evalWithAnswerFn f
        (recoverChain parameter lay tree leafIdx chainIdx (codeword chainIdx) (values chainIdx)))

theorem otsLeaf_chain_query_mem (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leafIdx message counter)
      = some codeword) (chainIdx : ChainIndex) (offset : Nat)
    (hoffset : offset < chainLength - 1 - (codeword chainIdx).val)
    (hrange : (codeword chainIdx).val + offset < chainLength - 1) :
    tweakableHashInput parameter
        (.chain lay tree leafIdx chainIdx ⟨(codeword chainIdx).val + offset, hrange⟩)
        (digestBytes (walkValue f parameter lay tree leafIdx chainIdx (codeword chainIdx).val
          (values chainIdx) offset))
      ∈ queriedInputs f (otsLeaf parameter lay tree leafIdx message counter values) := by
  simp only [otsLeaf]
  apply queriedInputs_mono_bind_right
  rw [hencode]
  apply queriedInputs_mono_bind_left
  apply sequenceFin_component_query_mem f _ chainIdx
  exact chainWalk_query_mem f parameter lay tree leafIdx chainIdx (codeword chainIdx).val
    (chainLength - 1 - (codeword chainIdx).val) (values chainIdx) offset hoffset hrange

theorem ftsLeafHash_query_mem (index : Index) (tree : FtsTree) (leafIdx : FtsLeaf)
    (secret : Digest) :
    tweakableHashInput parameter (.ftsLeaf index tree leafIdx) (digestBytes secret)
      ∈ queriedInputs f (ftsLeafHash parameter index tree leafIdx secret) := by
  simp [ftsLeafHash]

theorem treeFold_query_mem (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (path : Nat → Digest) (value : Digest) (levels offset : Nat) (hoffset : offset < levels) :
    tweakableHashInput parameter
        (.node lay tree (offset + 1) (leafIdx.val / 2 ^ (offset + 1)))
        (foldPayload f parameter lay tree leafIdx path value offset)
      ∈ queriedInputs f (treeFold parameter lay tree leafIdx path levels value) := by
  induction levels generalizing offset with
  | zero => omega
  | succ levels ih =>
      rw [treeFold_succ_eq, queriedInputs_bind]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hoffset with hlt | heq
      · exact List.mem_append_left _ (ih offset hlt)
      · subst offset
        apply List.mem_append_right _
        simp only [foldValue, foldPayload]
        cases leafIdx.val.testBit levels <;> simp

theorem ftsFold_query_mem (index : Index) (tree : FtsTree) (leafIdx : FtsLeaf)
    (path : Fin ftsTreeHeight → Digest) (value : Digest) (levels offset : Nat)
    (hlevels : levels ≤ ftsTreeHeight) (hoffset : offset < levels) :
    tweakableHashInput parameter
        (.ftsNode index tree (offset + 1) (leafIdx.val / 2 ^ (offset + 1)))
        (ftsFoldPayload f parameter index tree leafIdx path value offset)
      ∈ queriedInputs f (ftsFold parameter index tree leafIdx path levels value) := by
  induction levels generalizing offset with
  | zero => omega
  | succ levels ih =>
      rw [ftsFold_succ_eq, queriedInputs_bind]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hoffset with hlt | heq
      · exact List.mem_append_left _ (ih offset (by omega) hlt)
      · subst offset
        have hlevel : levels < ftsTreeHeight := by omega
        apply List.mem_append_right _
        simp only [ftsFoldValue, ftsFoldPayload, ftsSibling, dif_pos hlevel]
        cases leafIdx.val.testBit levels <;> simp

theorem ftsRecover_leaf_query_mem (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest)
    (tree : FtsTree) :
    tweakableHashInput parameter (.ftsLeaf index tree (leaves (ftsIndexOf tree)))
        (digestBytes (secrets tree))
      ∈ queriedInputs f (ftsRecover parameter index leaves secrets paths) := by
  simp only [ftsRecover]
  apply queriedInputs_mono_bind_left
  apply sequenceFin_component_query_mem f _ tree
  apply queriedInputs_mono_bind_left
  exact ftsLeafHash_query_mem f parameter index tree (leaves (ftsIndexOf tree)) (secrets tree)

theorem ftsRecover_fold_query_mem (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest)
    (tree : FtsTree) (offset : Nat) (hoffset : offset < ftsTreeHeight) :
    tweakableHashInput parameter
        (.ftsNode index tree (offset + 1)
          ((leaves (ftsIndexOf tree)).val / 2 ^ (offset + 1)))
        (ftsFoldPayload f parameter index tree (leaves (ftsIndexOf tree)) (paths tree)
          (truncateHash (f (tweakableHashInput parameter
            (.ftsLeaf index tree (leaves (ftsIndexOf tree))) (digestBytes (secrets tree))))) offset)
      ∈ queriedInputs f (ftsRecover parameter index leaves secrets paths) := by
  simp only [ftsRecover]
  apply queriedInputs_mono_bind_left
  apply sequenceFin_component_query_mem f _ tree
  apply queriedInputs_mono_bind_right
  simpa only [ftsLeafHash, eval_tweakableHash] using
    ftsFold_query_mem f parameter index tree (leaves (ftsIndexOf tree)) (paths tree)
      (truncateHash (f (tweakableHashInput parameter
        (.ftsLeaf index tree (leaves (ftsIndexOf tree))) (digestBytes (secrets tree)))))
      ftsTreeHeight offset (le_refl _) hoffset

theorem ftsRecover_roots_query_mem (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest) :
    tweakableHashInput parameter (.ftsRoots index)
        (ftsRootsPayload fun tree => evalWithAnswerFn f
          (ftsFold parameter index tree (leaves (ftsIndexOf tree)) (paths tree) ftsTreeHeight
            (evalWithAnswerFn f
              (ftsLeafHash parameter index tree (leaves (ftsIndexOf tree)) (secrets tree)))))
      ∈ queriedInputs f (ftsRecover parameter index leaves secrets paths) := by
  simp only [ftsRecover]
  apply queriedInputs_mono_bind_right
  simp only [evalWithAnswerFn_sequenceFin, evalWithAnswerFn_bind, queriedInputs_tweakableHash,
    List.mem_singleton]

end SphincsSecurity.Concrete
