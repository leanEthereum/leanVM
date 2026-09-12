import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Scheme.Arith
import SphincsSecurity.Proof.Scheme.Bytes
import SphincsSecurity.Proof.Scheme.StatementLemmas
/-!
# Extracting the first divergence

The deterministic half of the reduction, for one layer's tree. If a fold on values an adversary
supplies reaches the honest node above the leaf, then either every value it supplied was the honest
one, or at some level it hashed something other than the honest payload to the honest value. The
second is what the union bound charges; the first is what makes the adversary's signature the honest
one, and so no forgery.
-/

namespace SphincsSecurity.Concrete

open OracleComp

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
  (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) (path : Nat → Digest)

/-- The value the honest tree carries at a position. -/
def honestNode (level nodeIdx : Nat) : Digest :=
  evalWithAnswerFn f (treeNode parameter lay tree secret level nodeIdx)

/-- What the fold has reached after `levels` steps. -/
def foldValue (value : Digest) (levels : Nat) : Digest :=
  evalWithAnswerFn f (treeFold parameter lay tree leaf path levels value)

/-- Two children in the order the bit dictates. Written with `Bool.rec` rather than `if`, so that
both cases hold by `rfl` and rewriting the bit needs no reasoning about `Decidable` instances. -/
def orderedPayload (bit : Bool) (current sibling : Digest) : HashInput :=
  bit.rec (nodePayload current sibling) (nodePayload sibling current)

@[simp] theorem orderedPayload_false (current sibling : Digest) :
    orderedPayload false current sibling = nodePayload current sibling := rfl

@[simp] theorem orderedPayload_true (current sibling : Digest) :
    orderedPayload true current sibling = nodePayload sibling current := rfl

/-- The payload the fold hashes on its way from `level` to `level + 1`. -/
def foldPayload (value : Digest) (level : Nat) : HashInput :=
  orderedPayload (leaf.val.testBit level)
    (foldValue f parameter lay tree leaf path value level) (path level)

theorem eval_tweakableHash (domain : HashDomain) (payload : HashInput) :
    evalWithAnswerFn f (tweakableHash parameter domain payload)
      = truncateHash (f (tweakableHashInput parameter domain payload)) := by
  simp only [tweakableHash, oracleHash, evalWithAnswerFn_bind, evalWithAnswerFn_query,
    evalWithAnswerFn_pure]

theorem honestNode_succ (level nodeIdx : Nat) :
    honestNode f parameter lay tree secret (level + 1) nodeIdx
      = truncateHash (f (tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx)
          (nodePayload (honestNode f parameter lay tree secret level (2 * nodeIdx))
            (honestNode f parameter lay tree secret level (2 * nodeIdx + 1))))) := by
  simp only [honestNode, treeNode_succ_eq, evalWithAnswerFn_bind, eval_tweakableHash]

theorem foldValue_succ (value : Digest) (level : Nat) :
    foldValue f parameter lay tree leaf path value (level + 1)
      = truncateHash (f (tweakableHashInput parameter
          (.node lay tree (level + 1) (leaf.val / 2 ^ (level + 1)))
          (foldPayload f parameter lay tree leaf path value level))) := by
  simp only [foldValue, foldPayload, treeFold_succ_eq, evalWithAnswerFn_bind, orderedPayload]
  cases leaf.val.testBit level <;> rfl

/-- A hit at a node position: something other than the honest payload hashing to the honest value
there. Domain separation makes the target a function of the position alone, which is what lets the
union bound charge it. -/
def NodeHit (level nodeIdx : Nat) (payload : HashInput) : Prop :=
  payload ≠ nodePayload (honestNode f parameter lay tree secret level (2 * nodeIdx))
      (honestNode f parameter lay tree secret level (2 * nodeIdx + 1))
    ∧ truncateHash (f (tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx) payload))
      = honestNode f parameter lay tree secret (level + 1) nodeIdx

/-- **The first divergence.** A fold that reaches the honest node above the leaf either used the
honest leaf and the honest siblings throughout, or hit a node value somewhere along the way. -/
theorem treeFold_extract (value : Digest) (levels : Nat)
    (hfold : foldValue f parameter lay tree leaf path value levels
      = honestNode f parameter lay tree secret levels (leaf.val / 2 ^ levels)) :
    (value = honestNode f parameter lay tree secret 0 leaf.val
        ∧ ∀ level, level < levels → path level
            = honestNode f parameter lay tree secret level (Nat.xor (leaf.val / 2 ^ level) 1))
      ∨ ∃ level, level < levels
          ∧ NodeHit f parameter lay tree secret level (leaf.val / 2 ^ (level + 1))
              (foldPayload f parameter lay tree leaf path value level) := by
  induction levels with
  | zero =>
      left
      refine ⟨?_, fun level hlevel => absurd hlevel (by omega)⟩
      simpa [foldValue] using hfold
  | succ levels ih =>
      obtain ⟨j, hcase⟩ := index_sibling_cases (leaf.val / 2 ^ levels)
      have hj : leaf.val / 2 ^ (levels + 1) = j := by
        rw [div_pow_succ]
        rcases hcase with ⟨hc, _, _⟩ | ⟨hc, _, _⟩ <;> omega
      have hhash : truncateHash (f (tweakableHashInput parameter
            (.node lay tree (levels + 1) (leaf.val / 2 ^ (levels + 1)))
            (foldPayload f parameter lay tree leaf path value levels)))
          = honestNode f parameter lay tree secret (levels + 1) (leaf.val / 2 ^ (levels + 1)) := by
        rw [← foldValue_succ]
        exact hfold
      by_cases hagree : foldPayload f parameter lay tree leaf path value levels
          = nodePayload (honestNode f parameter lay tree secret levels (2 * j))
              (honestNode f parameter lay tree secret levels (2 * j + 1))
      · have hstep : foldValue f parameter lay tree leaf path value levels
              = honestNode f parameter lay tree secret levels (leaf.val / 2 ^ levels)
            ∧ path levels = honestNode f parameter lay tree secret levels
              (Nat.xor (leaf.val / 2 ^ levels) 1) := by
          rw [foldPayload] at hagree
          rcases hcase with ⟨hc, hsibling, hmod⟩ | ⟨hc, hsibling, hmod⟩
          · rw [show leaf.val.testBit levels = false by
              rw [Bool.eq_false_iff, ne_eq, testBit_iff_div_mod]; omega] at hagree
            obtain ⟨hcur, hsib⟩ := nodePayload_injective hagree
            exact ⟨by rw [hcur, hc], by rw [hsib, hsibling]⟩
          · rw [show leaf.val.testBit levels = true by
              rw [testBit_iff_div_mod]; omega] at hagree
            obtain ⟨hsib, hcur⟩ := nodePayload_injective hagree
            exact ⟨by rw [hcur, hc], by rw [hsib, hsibling]⟩
        rcases ih hstep.1 with ⟨hvalue, hpaths⟩ | ⟨level, hlevel, hnode⟩
        · left
          refine ⟨hvalue, fun level hlevel => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlevel with hlt | heq
          · exact hpaths level hlt
          · subst heq; exact hstep.2
        · exact Or.inr ⟨level, by omega, hnode⟩
      · right
        exact ⟨levels, by omega, by rw [hj]; exact hagree, hhash⟩

end SphincsSecurity.Concrete
