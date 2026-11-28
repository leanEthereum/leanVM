/-
  LeanVM.Prover.Complete.Link.Index

  The index side's identity on the honest witness.
-/

module

public import LeanVM.Prover.Complete.Link.State
public import LeanVM.Prover.Complete.Link.Balance

/-!
# The index side's identity

`linkIndexIdentity_honest`: on every admitted execution's witness, the index side's cube sum is
`eq(ζ, 0)·ŝ_init + eq(ζ, T)·ŝ_fin`, the state chain telescoping (`indexStateIdentity_of`) and the
lookups balancing (`indexBalance_of`).
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Semantics LeanVM.Prover

theorem linkIndexIdentity_honest {prog : LeanIsaProgram} {input : PublicInput}
    {t : Execution prog} {ρ : ℕ} {W : Witness} (hA : Admitted prog input t ρ W) :
    LinkIndexIdentity W :=
  linkIndexIdentity_of (indexStateIdentity_of hA) (indexBalance_of hA)

end LeanVM.Prover.Complete

end
