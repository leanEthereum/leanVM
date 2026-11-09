import Rv64Verifier.Machine

/-!
# Runs of the machine

Ported from sig.golf's `SigGolfCandidate.Rv`, where `Steps` was an inductive charging cycles;
here it is the machine's own `Rv64Verifier.Steps` (`n` steps of `Rv64Verifier.step`), and these
are its composition laws.
-/

namespace Rv64Verifier.Sym
open RiscvZkvm.Rv64

theorem Steps.refl (code : Code) (s : MachineState) : Steps code 0 s s := rfl

theorem Steps.cons {code : Code} {s t u : MachineState} {n : Nat}
    (h : Rv64Verifier.step code s = some t) (tail : Steps code n t u) : Steps code (n + 1) s u :=
  ⟨t, h, tail⟩

theorem Steps.of_eq {code : Code} {s t : MachineState} {k k' : Nat} (h : Steps code k s t)
    (hk : k = k') : Steps code k' s t := by
  subst hk; exact h

theorem Steps.trans {code : Code} {s t u : MachineState} {k₁ k₂ : Nat}
    (h₁ : Steps code k₁ s t) (h₂ : Steps code k₂ t u) : Steps code (k₁ + k₂) s u := by
  induction k₁ generalizing s with
  | zero =>
    have h : s = t := h₁
    subst h
    simpa using h₂
  | succ k ih =>
    obtain ⟨s', hs, h'⟩ := h₁
    rw [Nat.succ_add]
    exact ⟨s', hs, ih h'⟩

/-- A run that ends at a `HALT` call with `a0 = verdict` halts with that verdict. -/
theorem Steps.haltsWith {code : Code} {s t : MachineState} {n : Nat} {verdict : Word}
    (h : Steps code n s t) (hhalt : Halting code t) (ha0 : t.getReg .x10 = verdict) :
    HaltsWith code s n verdict :=
  ⟨t, h, hhalt, ha0⟩

end Rv64Verifier.Sym
