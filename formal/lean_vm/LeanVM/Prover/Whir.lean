/-
  LeanVM.Prover.Whir

  The executable WHIR opening makes the specification's moves.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Prover.WhirBasis
public import LeanVM.Prover.Corr

/-!
# The opening

`corr_openingFast`: the executable opening on claim descriptions,
`openingFast μ R q.values.toArray claims`, is the specification's
`honestOpening μ R q (claims.map ClaimDesc.denote)` (`openingFast_eq`): both run the statement's
levels `levelsA`, from the same stack table (`toList_stackTableA`) and the same weight table
(`toList_basisTableA`), so it makes the same moves.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Complete LeanVM.Protocol.EndToEnd
open LeanVM.Prover.Enc

@[expose] public section

/-- **The executable opening is the specification's.** -/
theorem openingFast_eq {μ : ℕ} (R : ℕ) (q : Column μ) (claims : List ClaimDesc) :
    openingFast μ R q.values.toArray claims = honestOpening μ R q (claims.map ClaimDesc.denote) := by
  have h1 : stackTableA μ q.values.toArray = (stackTable μ q).toArray := by
    rw [← toList_stackTableA q, Array.toArray_toList]
  have h2 : ∀ scales, basisTableA μ scales claims =
      (basisTable μ scales (claims.map ClaimDesc.denote)).toArray := fun scales ↦ by
    rw [← toList_basisTableA μ scales claims, Array.toArray_toList]
  simp only [openingFast, honestOpening, List.length_map, h1, h2]
  rfl

/-- **The executable opening makes the specification's moves.** -/
theorem corr_openingFast {μ : ℕ} (R : ℕ) (q : Column μ) (claims : List ClaimDesc) :
    Corr (fun _ _ ↦ True) (openingFast μ R q.values.toArray claims)
      (honestOpening μ R q (claims.map ClaimDesc.denote)) := by
  rw [openingFast_eq]
  exact Corr.mono (fun _ _ _ ↦ trivial) _ _ (Corr.refl _)

end
end LeanVM.Prover
