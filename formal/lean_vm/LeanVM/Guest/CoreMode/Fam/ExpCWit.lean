/-
  LeanVM.Guest.CoreMode.Fam.ExpCWit

  The exponent bounds' carrying check (`CoreMode.carryExpB`) from its witnessed check: the listed callees read through
  their table, each constant searched among the events the generator names.
-/

module

public import LeanVM.Guest.CoreMode.Fam.ExpCDefs
public import LeanVM.Guest.CoreMode.Fam.Wit

/-!
# The exponent bounds carried, witnessed

`carryExpW T fn b`: `carryExpB L fn` with the list `L` read through its table `T` (`Res.tabOk`) and each argument's
constant searched over the sub-spine at the set bits of `b` (`Res.pickB`) before the arms (`armExpB`). The search over
the sub-spine succeeds over the spine (`constExpS` scans its events), so `carryExpB_of_wit` gives the check.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Res (NTab pickB tabOk)

@[expose] public section

/-- **`carryExpB`, witnessed**: the table of the listed callees, the sub-spine's bitset `b`. -/
noncomputable def carryExpW (T : NTab (ℕ × ℕ × ℕ)) (fn : Fn) (b : ℕ) : Bool :=
  Res.sitesB (fun f args _ ↦ (T.at (encS f)).all fun c ↦ match args[c.1]? with
    | some a => constExpS a c.2.1 c.2.2 (pickB b (spineE fn.body)) || armExpB a c.2.1 c.2.2 fn.body
    | none => false) fn.body

end

public section

/-- **The exponent bounds' carrying check, from its witnessed check.** -/
theorem carryExpB_of_wit {L : List (String × ℕ × ℕ × ℕ)} {T : NTab (ℕ × ℕ × ℕ)} (hT : tabOk L T id = true)
    {fn : Fn} {b : ℕ} (h : carryExpW T fn b = true) : carryExpB L fn = true := by
  unfold carryExpW at h
  unfold carryExpB
  refine Res.sitesB_imp (fun f args rets hq ↦ ?_) fn.body h
  refine Res.tab_all (Res.tabOk.all hT) (φ := id)
    (P := fun c ↦ match args[c.1]? with | some a => valExpB fn.body a c.2.1 c.2.2 | none => false) (fun c hc ↦ ?_) hq
  revert hc
  obtain ⟨i, lo, hi⟩ := c
  show (match args[i]? with
      | some a => constExpS a lo hi (pickB b (spineE fn.body)) || armExpB a lo hi fn.body
      | none => false) = true →
    (match args[i]? with | some a => valExpB fn.body a lo hi | none => false) = true
  cases args[i]? with
  | none => exact id
  | some a =>
    intro h
    unfold valExpB
    unfold constExpS at h ⊢
    simp only [Bool.or_eq_true] at h ⊢
    exact h.imp (Res.any_sub fun _ ↦ Res.mem_pickB) id

end

end LeanVM.Guest.CoreMode
