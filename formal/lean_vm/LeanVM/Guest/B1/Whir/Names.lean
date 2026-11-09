/-
  LeanVM.Guest.B1.Whir.Names

  The kernel-evaluated decimal names of the specializations are `toString`'s.
-/

module

public import LeanVM.Guest.B1.Whir.Config
public import Mathlib.Tactic.IntervalCases

/-!
# Names

`toString` on `Nat` (`Nat.repr`) is not exposed to the kernel of importing modules, so the
templates name the specializations with `natStr` (`Whir/Config.lean`), which the kernel evaluates;
`natStr_eq` proves it is `toString`, so that the callees' statements (`"…__L" ++ toString n`)
apply to the templates' calls.
-/

namespace LeanVM.Guest.B1.Whir

@[expose] public section

theorem digitLit_eq {d : Nat} (h : d < 10) : Nat.digitChar d = digitLit d := by
  interval_cases d <;> simp [digitLit]

theorem natStrAux_eq : ∀ (f n : Nat), n < f → natStrAux f n = Nat.repr n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, n, h => by
    unfold natStrAux
    split_ifs with h10
    · rw [Nat.repr_of_lt h10, digitLit_eq h10]
    · rw [Nat.repr_of_ge (by omega), natStrAux_eq f (n / 10) (by omega),
        digitLit_eq (Nat.mod_lt n (by decide))]

/-- **`natStr` is `toString`.** -/
theorem natStr_eq (n : Nat) : natStr n = toString n := natStrAux_eq (n + 1) n (by omega)

end
end LeanVM.Guest.B1.Whir
