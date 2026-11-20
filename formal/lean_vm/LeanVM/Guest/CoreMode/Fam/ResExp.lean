/-
  LeanVM.Guest.CoreMode.Fam.ResExp

  The families of a product's factors (`Res.expFamB`), sound at the honest frames.
-/

module

public import LeanVM.Guest.CoreMode.Fam.ResF
public import LeanVM.Guest.CoreMode.Fam.ExpDefs

/-!
# A constant's power of `g`

`powOf1_sound`: `powOf1 c = some z` makes `c = g^z`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (fsN cellJ namedOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (Wit witOk powOf powOf1 cellLt holdsBase inFr frEx kVal1 kVal pw0 pw mulAt eqX mulX
  expHi expShiftB expFacB expPtB expFamB)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

theorem powOf1_sound {c : E} {z : ℕ} (h : powOf1 c = some z) : c = ofK (Parameters.g ^ z) := by
  unfold powOf1 at h
  split_ifs at h with h1
  · obtain rfl := (Option.some.inj h).symm
    rw [eq_ofK_limb h1.1, h1.2, pow_zero]
  · exact powOf_sound h

section

variable {M : ℕ → E} {fp : ℕ}

end

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ} {w : Wit}

end

end

end LeanVM.Guest.EndExec
