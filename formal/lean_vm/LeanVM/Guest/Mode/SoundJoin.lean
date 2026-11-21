module

public import LeanVM.Guest.Mode.SoundHint

/-!
# Residuals

`ResHolds`: a residual, a value fact about the cells, which the reference's agreement with the memory
gives from a fact about the reference (`SubF`: a run inside known runs).
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-- Every cell of run `a` is a cell of one of the runs `bs`, whatever their words: `a`'s exponents
have values, and each cell's index in `a` has one in some run of `bs`. -/
def SubF (s : St) (a : Rng) (bs : List Rng) : Prop :=
  ∃ xlo xhi, IdxVal s a.lo xlo ∧ IdxVal s a.hi xhi ∧ ∀ vq, MonoVal s a.q vq → ∀ j, xlo ≤ j → j < xhi →
    ∃ b ∈ bs, ∀ vb ylo yhi, MonoVal s b.q vb → IdxVal s b.lo ylo → IdxVal s b.hi yhi →
      ∃ j', ylo ≤ j' ∧ j' < yhi ∧ vq * ofK (g ^ (a.S * j + a.d)) = vb * ofK (g ^ (b.S * j' + b.d))

/-- What a residual states, of the memory. -/
def ResHolds (s : St) : Res → Prop
  | .lt a b => LTF s a b
  | .nz o => NzAt s o
  | .sub a bs => SubF s a bs
  | .name _ => True

end

end LeanVM.Guest.Mode
