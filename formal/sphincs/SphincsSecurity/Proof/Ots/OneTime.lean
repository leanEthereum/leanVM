import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.Chain
import SphincsSecurity.Proof.Scheme.Eval
/-!
# The one-time signature

`Ots.leaf` recovers the leaf `Ots.sign` committed to. The counter matters only through the codeword
it produces: correctness holds for *any* admissible counter, not just the least one the signer
takes, which is why a second admissible counter for the same codeword is a strong forgery rather
than a break.
-/

namespace SphincsSecurity.Concrete

open OracleComp

variable {α : Type} (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
  (tree : TreeIndex) (leaf : LeafIndex)

/-- Steps compose under evaluation. -/
theorem eval_chainWalk_add (chainIdx : ChainIndex) (start a b : Nat) (value : Digest) :
    evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start (a + b) value)
      = evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx (start + a) b
          (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start a value))) := by
  rw [chainWalk_add, evalWithAnswerFn_bind]

/-- Revealing a chain at its codeword digit and walking the rest reaches the public value. -/
theorem eval_recoverChain (chainIdx : ChainIndex) (digit : Digit) (value : Digest) :
    evalWithAnswerFn f (recoverChain parameter lay tree leaf chainIdx digit
        (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 digit.val value)))
      = evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) value) := by
  have hdigit : digit.val + (chainLength - 1 - digit.val) = chainLength - 1 := by
    have hlt := digit.isLt
    simp only [chainLength, winternitzBits] at hlt
    simp only [chainLength, winternitzBits]
    omega
  calc evalWithAnswerFn f (recoverChain parameter lay tree leaf chainIdx digit
          (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 digit.val value)))
      = evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx
          (0 + digit.val) (chainLength - 1 - digit.val)
          (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 digit.val value))) := by
        rw [recoverChain, Nat.zero_add]
    _ = evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0
          (digit.val + (chainLength - 1 - digit.val)) value) := (eval_chainWalk_add ..).symm
    _ = evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) value) := by
        rw [hdigit]

/-- The honest one-time public value of one chain. -/
theorem eval_oneTimePublicKey (secret : ChainIndex → Digest) :
    evalWithAnswerFn f (oneTimePublicKey parameter lay tree leaf secret)
      = fun chainIdx => evalWithAnswerFn f
          (chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secret chainIdx)) := by
  simp [oneTimePublicKey]

end SphincsSecurity.Concrete
