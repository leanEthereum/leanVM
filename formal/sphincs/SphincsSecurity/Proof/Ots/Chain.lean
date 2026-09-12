import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Statement

/-!
# The hash chain

Walking `a` steps from `start` and then `b` more is walking `a + b` steps. Everything the one-time
signature needs follows: the verifier's half of a chain, `recoverChain`, composes with the signer's
half to reach the public value the leaf is built from.
-/

namespace SphincsSecurity.Concrete

variable {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery HashSpec m]

/-- Steps compose. Positions past the last chain step are the constant `0` on both sides, so no
range hypothesis is needed. -/
theorem chainWalk_add (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start a b : Nat) (value : Digest) :
    chainWalk (m := m) parameter lay tree leaf chainIdx start (a + b) value
      = (do
          let mid ← chainWalk (m := m) parameter lay tree leaf chainIdx start a value
          chainWalk parameter lay tree leaf chainIdx (start + a) b mid) := by
  induction b with
  | zero => simp [chainWalk]
  | succ b ih =>
      show chainWalk (m := m) parameter lay tree leaf chainIdx start (a + b + 1) value = _
      simp only [chainWalk, ih, bind_assoc, Nat.add_assoc]

end SphincsSecurity.Concrete
