import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.Position
import SphincsSecurity.Proof.Scheme.Support
/-!
# The key-generation cache contains no message query

Key generation evaluates only structural hashes. Consequently its cache, which starts empty, cannot
already contain a message-digest input when the adversary begins.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

/-- Every query on the selected execution path is the honest query at a structural position. -/
def QueriesAtPositions {alpha : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (oa : OracleComp HashSpec alpha) : Prop :=
  ∀ input, input ∈ queriedInputs f oa →
    ∃ p : Position, ∃ payload : HashInput,
      input = tweakableHashInput parameter p.domain payload

theorem QueriesAtPositions.pure {alpha : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (value : alpha) :
    QueriesAtPositions parameter f (pure value) := by
  simp [QueriesAtPositions]

theorem QueriesAtPositions.bind {alpha beta : Type} {parameter : PublicParameter}
    {f : QueryImpl HashSpec Id} {oa : OracleComp HashSpec alpha}
    {next : alpha → OracleComp HashSpec beta}
    (hleft : QueriesAtPositions parameter f oa)
    (hright : QueriesAtPositions parameter f (next (evalWithAnswerFn f oa))) :
    QueriesAtPositions parameter f (oa >>= next) := by
  intro input hinput
  rw [queriedInputs_bind] at hinput
  rcases List.mem_append.mp hinput with hinput | hinput
  · exact hleft input hinput
  · exact hright input hinput

theorem QueriesAtPositions.tweakableHash (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (p : Position) (payload : HashInput) :
    QueriesAtPositions parameter f
      (Concrete.tweakableHash parameter p.domain payload) := by
  intro input hinput
  simp only [queriedInputs_tweakableHash, List.mem_singleton] at hinput
  subst input
  exact ⟨p, payload, rfl⟩

namespace Concrete

theorem queriesAtPositions_sequenceFin {alpha : Type} {n : Nat}
    (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (computation : Fin n → OracleComp HashSpec alpha)
    (hcomputation : ∀ index, QueriesAtPositions parameter f (computation index)) :
    QueriesAtPositions parameter f (sequenceFin computation) := by
  induction n with
  | zero => exact QueriesAtPositions.pure parameter f _
  | succ n ih =>
      rw [sequenceFin]
      apply QueriesAtPositions.bind (hcomputation 0)
      apply QueriesAtPositions.bind
      · exact ih (fun index : Fin n => computation index.succ)
          (fun index => hcomputation index.succ)
      · exact QueriesAtPositions.pure parameter f _

theorem queriesAtPositions_chainWalk (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (start steps : Nat) (value : Digest) :
    QueriesAtPositions parameter f
      (chainWalk parameter lay tree leafIdx chainIdx start steps value) := by
  induction steps with
  | zero => exact QueriesAtPositions.pure parameter f value
  | succ steps ih =>
      rw [chainWalk]
      apply QueriesAtPositions.bind ih
      split_ifs with hstep
      · exact QueriesAtPositions.tweakableHash parameter f
          (.chain lay tree leafIdx chainIdx ⟨start + steps, hstep⟩) _
      · exact QueriesAtPositions.pure parameter f _

theorem queriesAtPositions_oneTimePublicKey (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (secret : ChainIndex → Digest) :
    QueriesAtPositions parameter f
      (oneTimePublicKey parameter lay tree leafIdx secret) := by
  apply queriesAtPositions_sequenceFin
  intro chainIdx
  exact queriesAtPositions_chainWalk parameter f lay tree leafIdx chainIdx 0
    (chainLength - 1) (secret chainIdx)

def RootTreeRange (level nodeIdx : Nat) : Prop :=
  2 ^ level * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight

private theorem RootTreeRange.index_lt {level nodeIdx : Nat}
    (h : RootTreeRange level nodeIdx) : nodeIdx < 2 ^ maxLayerHeight := by
  have hpow : 1 ≤ 2 ^ level := one_le_pow₀ (by omega)
  simp only [RootTreeRange] at h
  nlinarith

private theorem RootTreeRange.left {level nodeIdx : Nat}
    (h : RootTreeRange (level + 1) nodeIdx) : RootTreeRange level (2 * nodeIdx) := by
  simp only [RootTreeRange, pow_succ] at h ⊢
  nlinarith [Nat.zero_le (2 ^ level), Nat.zero_le nodeIdx]

private theorem RootTreeRange.right {level nodeIdx : Nat}
    (h : RootTreeRange (level + 1) nodeIdx) : RootTreeRange level (2 * nodeIdx + 1) := by
  simp only [RootTreeRange, pow_succ] at h ⊢
  nlinarith [Nat.zero_le (2 ^ level), Nat.zero_le nodeIdx]

theorem queriesAtPositions_treeNode (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (level nodeIdx : Nat)
    (hlevel : level ≤ maxLayerHeight) (hrange : RootTreeRange level nodeIdx) :
    QueriesAtPositions parameter f (treeNode parameter lay tree secret level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [treeNode_zero_eq]
      apply QueriesAtPositions.bind
      · exact queriesAtPositions_oneTimePublicKey parameter f lay tree (leafOfNat nodeIdx)
          (secret (leafOfNat nodeIdx))
      · exact QueriesAtPositions.tweakableHash parameter f
          (.leaf lay tree (leafOfNat nodeIdx)) _
  | succ level ih =>
      rw [treeNode_succ_eq]
      apply QueriesAtPositions.bind
      · exact ih (2 * nodeIdx) (by omega) (RootTreeRange.left hrange)
      apply QueriesAtPositions.bind
      · exact ih (2 * nodeIdx + 1) (by omega) (RootTreeRange.right hrange)
      · exact QueriesAtPositions.tweakableHash parameter f
          (.node lay tree ⟨level, by omega⟩ ⟨nodeIdx, hrange.index_lt⟩) _

theorem queriesAtPositions_treeRoot (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) :
    QueriesAtPositions parameter f (treeRoot parameter lay tree secret) := by
  apply queriesAtPositions_treeNode parameter f lay tree secret (layerHeight lay) 0
  · exact layerHeight_le lay
  · simp only [RootTreeRange, zero_add, mul_one]
    exact pow_le_pow_right' (by omega) (layerHeight_le lay)

theorem messageInput_not_mem_queriedInputs_treeRoot (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (payload : HashInput) :
    tweakableHashInput parameter .message payload ∉
      queriedInputs f (treeRoot parameter lay tree secret) := by
  intro hmem
  obtain ⟨p, structuralPayload, heq⟩ :=
    queriesAtPositions_treeRoot parameter f lay tree secret _ hmem
  have hdomain := (tweakableHashInput_injective parameter
    (show HashDomain.message.InRange from trivial) p.domain_inRange heq).1
  cases p <;> simp [Position.domain] at hdomain

theorem treeRoot_cache_message_none (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest)
    (root : Digest) (rootCache : QueryCache HashSpec)
    (hroot : (root, rootCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeRoot parameter lay tree secret)).run ∅))
    (payload : HashInput) :
    rootCache (tweakableHashInput parameter .message payload) = none := by
  obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn (spec := HashSpec) rootCache
  apply cache_eq_none_of_not_mem_queriedInputs
    (treeRoot parameter lay tree secret) ∅ root rootCache hroot f hf
  · simp
  · exact messageInput_not_mem_queriedInputs_treeRoot parameter f lay tree secret payload

end Concrete

end SphincsSecurity
