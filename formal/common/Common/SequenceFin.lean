module

public import Statement.HashSignatures

/-!
# `sequenceFin` by `Fin.cases`

The statement's `sequenceFin` reads its result at an index directly, for compiled speed; the proofs
take it, and their own copies of it, in the form `Fin.cases head tail`.
-/

namespace Common

/-- `sequenceFin`'s result is `Fin.cases` of the first result and the rest's. -/
public theorem sequenceFin_succ {m : Type → Type} [Monad m] {α : Type} {n : ℕ}
    (c : Fin (n + 1) → m α) :
    HashSig.OverPermutation.sequenceFin c = do
      let head ← c 0
      let tail ← HashSig.OverPermutation.sequenceFin fun index : Fin n => c index.succ
      return Fin.cases head tail := by
  simp only [HashSig.OverPermutation.sequenceFin]
  congr 1; funext head; congr 1; funext tail; congr 1; funext i
  induction i using Fin.cases <;> simp

end Common
