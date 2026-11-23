/-
  LeanVM.Guest.B1.Opening.QueriesPlaced10

  The region `opening_queries`' loop reads, and when it is entered.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced9
import LeanVM.Guest.Value.FieldBits

/-!
# The loop's region

`oqLoopR`: the loop reads the caller's region and the chain buffer. `one_add_gen_pow`: the loop is
entered (`1 + g^N ≠ 0`) exactly when `N ≠ 0`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The region of the loop: the caller's and the chain buffer. -/
def oqLoopR (R : ℕ → Prop) (b n : ℕ) (i : ℕ) : Prop := R i ∨ (b ≤ i ∧ i < b + n)

theorem one_add_gen_pow {N : ℕ} (hN : N + 1 < ordG) : (1 + gen ^ N ≠ 0 ↔ N ≠ 0) := by
  constructor
  · intro h hN0
    subst hN0
    exact h (by rw [pow_zero]; exact e_add_self 1)
  · intro hN0 h
    have h' : gen ^ 0 = gen ^ N := by rw [pow_zero]; exact e_add_eq_zero_iff.mp h
    have := gen_pow_inj (a := 0) (b := N) (by decide) (lt_trans (Nat.lt_succ_self N) hN) h'
    omega

end
end LeanVM.Guest.B1
