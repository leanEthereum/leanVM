/-
  LeanVM.Guest.Bridge.FrAlLink

  The frame hints' flags check of compiled function `j`, by index, from its pack's check by name.
-/

module

public import LeanVM.Guest.Bridge.FrAl
public import LeanVM.Guest.Bridge.ProgAlDefs

namespace LeanVM.Guest.Bridge

open LeanVM.Guest.Core

@[expose] public section

/-- **Compiled function `j` passes the frame hints' flags check** at the flags `al`. -/
def FrAlJ (al : String → Bool) (j : ℕ) : Prop :=
  frAlChk al (B2C.plumbOf j) (coreOf j).body (adviceOf j) = true

end

public section

theorem frAlJ_of {al : String → Bool} {j : ℕ} {cf : Core.Fn} {P : B2C.Plumb} {ex : List (ℕ × ℕ)}
    {en : List (String × ℕ)} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hcf : coreOf j = cf)
    (hP : B2C.plumbOf j = P) (ht : (extraOf j, entsOf j, adviceOf j) = (ex, en, d))
    (h : frAlChk al P cf.body d = true) : FrAlJ al j := by
  simp only [Prod.mk.injEq] at ht
  rw [FrAlJ, hcf, hP, ht.2.2]
  exact h

end

end LeanVM.Guest.Bridge
