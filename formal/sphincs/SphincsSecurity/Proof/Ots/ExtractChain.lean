import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.Extract
/-!
# Extracting the first divergence in a chain

The same argument as for a layer's tree, on a hash chain. If walking from a value the adversary
supplied reaches the honest endpoint, then either that value was the honest one at its position, or
somewhere along the walk it hashed something other than the honest predecessor to the honest
successor.
-/

namespace SphincsSecurity.Concrete

open OracleComp

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
  (leaf : LeafIndex) (chainIdx : ChainIndex) (secret : Digest)

/-- The honest chain value at a position. -/
def honestChain (position : Nat) : Digest :=
  evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 position secret)

/-- What the walk has reached after `steps` steps from `start`. -/
def walkValue (start : Nat) (value : Digest) (steps : Nat) : Digest :=
  evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start steps value)

theorem honestChain_succ (position : Nat) (hposition : position < chainLength - 1) :
    honestChain f parameter lay tree leaf chainIdx secret (position + 1)
      = truncateHash (f (tweakableHashInput parameter
          (.chain lay tree leaf chainIdx ⟨position, hposition⟩)
          (digestBytes (honestChain f parameter lay tree leaf chainIdx secret position)))) := by
  simp only [honestChain, chainWalk, evalWithAnswerFn_bind, Nat.zero_add, dif_pos hposition,
    eval_tweakableHash]

theorem walkValue_succ (start : Nat) (value : Digest) (steps : Nat)
    (hrange : start + steps < chainLength - 1) :
    walkValue f parameter lay tree leaf chainIdx start value (steps + 1)
      = truncateHash (f (tweakableHashInput parameter
          (.chain lay tree leaf chainIdx ⟨start + steps, hrange⟩)
          (digestBytes (walkValue f parameter lay tree leaf chainIdx start value steps)))) := by
  simp only [walkValue, chainWalk, evalWithAnswerFn_bind, dif_pos hrange, eval_tweakableHash]

/-- A hit at a chain step: something other than the honest value at `position` hashing to the honest
value at `position + 1`. -/
def ChainHit (position : Nat) (hposition : position < chainLength - 1) (payload : Digest) : Prop :=
  payload ≠ honestChain f parameter lay tree leaf chainIdx secret position
    ∧ truncateHash (f (tweakableHashInput parameter
        (.chain lay tree leaf chainIdx ⟨position, hposition⟩) (digestBytes payload)))
      = honestChain f parameter lay tree leaf chainIdx secret (position + 1)

/-- **The first divergence in a chain.** -/
theorem chainWalk_extract (start : Nat) (value : Digest) (steps : Nat)
    (hrange : start + steps ≤ chainLength - 1)
    (hwalk : walkValue f parameter lay tree leaf chainIdx start value steps
      = honestChain f parameter lay tree leaf chainIdx secret (start + steps)) :
    value = honestChain f parameter lay tree leaf chainIdx secret start
      ∨ ∃ (offset : Nat) (hoffset : start + offset < chainLength - 1), offset < steps
          ∧ ChainHit f parameter lay tree leaf chainIdx secret (start + offset) hoffset
              (walkValue f parameter lay tree leaf chainIdx start value offset) := by
  induction steps with
  | zero =>
      left
      simpa [walkValue, chainWalk] using hwalk
  | succ steps ih =>
      have hlt : start + steps < chainLength - 1 := by omega
      by_cases hagree : walkValue f parameter lay tree leaf chainIdx start value steps
          = honestChain f parameter lay tree leaf chainIdx secret (start + steps)
      · rcases ih (by omega) hagree with hvalue | ⟨offset, hoffset, hlt', hhit⟩
        · exact Or.inl hvalue
        · exact Or.inr ⟨offset, hoffset, by omega, hhit⟩
      · refine Or.inr ⟨steps, hlt, by omega, hagree, ?_⟩
        rw [← walkValue_succ f parameter lay tree leaf chainIdx start value steps hlt, hwalk,
          show start + (steps + 1) = start + steps + 1 by omega]

end SphincsSecurity.Concrete
