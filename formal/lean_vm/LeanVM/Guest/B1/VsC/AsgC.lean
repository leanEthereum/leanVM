/-
  LeanVM.Guest.B1.VsC.AsgC

  `assert_small_g_power` completes, layout-free.
-/

module

public import LeanVM.Guest.B1.VsC.Quiet
public import LeanVM.Guest.B1.Bits.SmallGPower
public import LeanVM.Guest.Memory.LowDef
import LeanVM.Guest.CoreRef

/-!
# `assert_small_g_power`, complete

`assert_small_g_power(x, g_squares)` hints nine digits of `x`'s exponent, range checks each below
`16` and multiplies their shares from the exponent table. On `x = g^e`, `e < 2^36`, a memory
defined below `2^k`, `k ≥ 4` (the range checks read there), holding the table at `q`: the guest
stream's honest valuation (`asg_holds_ofD`) holds the body, its digits `e`'s
(`asgHint_exact`), so the call completes, popping nothing, exact
(`assert_small_g_power_complete`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The shares `assert_small_g_power` reads, from the exponent table. -/
theorem asg_shares {rd : Reader} {q : E} (ht : ExpTables rd q) (e : ℕ) :
    ∀ j < 9, LoadHolds rd (q * gen ^ (e / 16 ^ j % 16)) (34 + 16 * j)
      (gen ^ (e / 16 ^ j % 16 * 16 ^ j)) := fun _ hj ↦ asg_load ht hj (Nat.mod_lt _ (by decide))

/-- A digit's range check against `g^15` on a memory defined below `2^k`, `4 ≤ k`. -/
theorem asg_rc_low {k : ℕ} (hk4 : 4 ≤ k) {rd : Reader} (hlow : LowDef k rd) {n : ℕ}
    (hn : n < 16) : ∃ y t1 t2 : E, LoadHolds rd (gen ^ n) 0 t1 ∧
      word (2 ^ (16 - 1)) 0 = gen ^ n * y ∧ LoadHolds rd y 0 t2 := by
  obtain ⟨a, b, c⟩ := rc_complete_low hlow (K := 16)
    (le_trans (by decide) (Nat.pow_le_pow_right (by decide) hk4)) hn
  refine ⟨_, _, _, by rw [gen_pow_eq_ofK]; exact a, ?_, c⟩
  rw [word_two_pow (by norm_num), gen_pow_eq_ofK, gen_pow_eq_ofK]
  exact b

/-- **The digits hint is exact** on a valuation holding `g^e`'s digits. -/
theorem asgHint_exact {rd : Reader} {σ : Val} {e : ℕ} (he : e < 2 ^ 36) (e0 : σ (.n 0) = gen ^ e)
    (ed : ∀ j < 9, σ (.n (j + 2)) = gen ^ (e / 16 ^ j % 16)) :
    (Atom.hint (.digitsExp (.n 0) 36 9 4 0 none (.stack [.n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8,
      .n 9, .n 10]))).Exact rd σ := by
  refine ⟨e, 0, he, by rw [e0, gen_pow_eq_ofK], rfl, ?_⟩
  have hl : Dest.words rd σ (.stack [.n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10]) =
      (List.range 9).map fun j => σ (.n (j + 2)) := rfl
  rw [hl]
  refine List.map_congr_left fun j hj => ?_
  have hj : j < 9 := List.mem_range.mp hj
  rw [ed j hj, gen_pow_eq_ofK, ite_neg' (show ¬ 128 ≤ 0 + 4 * j by omega), Nat.zero_add,
    Nat.shiftRight_eq_div_pow, show 2 ^ (4 * j) = 16 ^ j by rw [pow_mul]; rfl]
  rfl

/-- **`assert_small_g_power` completes**: on `g^e`, `e < 2^36`, and a memory defined below
`2^k`, `4 ≤ k`, holding the exponent table at `q`. -/
theorem assert_small_g_power_complete (k : ℕ) (hk : 4 ≤ k) {e : ℕ} (he : e < 2 ^ 36) (q : E) :
    CallCompletes k "assert_small_g_power" [gen ^ e, q] [] (fun rd => ExpTables rd q) PostQuiet := by
  refine callCompletes_straight_ex find_assert_small_g_power (by decide +kernel) fun rd hl ht => ?_
  obtain ⟨σ, e0, e1, -, ed, hh⟩ := asg_holds_ofD (C := coreProgram.Rel rd) (rd := rd) (q := q)
    (by simpa using he) (fun j => asg_rc_low hk hl (Nat.mod_lt _ (by decide))) (asg_shares ht e)
  rw [← assert_small_g_power_body] at hh
  have hr : retOf (fn% «assert_small_g_power»).body = some [] := by decide +kernel
  have hA := atoms_of_holdsList hr hh
  refine ⟨σ, ?_, fun vs hvs => by rw [hr] at hvs; cases hvs; rfl, fun a ha => ⟨hA a ha, ?_⟩⟩
  · show [σ (.n 0), σ (.n 1)] = _
    rw [e0, e1]
  have hsplit : (fn% «assert_small_g_power»).body =
      .atom (.hint (.digitsExp (.n 0) 36 9 4 0 none (.stack [.n 2, .n 3, .n 4, .n 5, .n 6, .n 7,
        .n 8, .n 9, .n 10]))) :: (fn% «assert_small_g_power»).body.tail := rfl
  rw [hsplit] at ha
  rcases List.mem_cons.mp ha with he' | ha
  · cases he'
    exact asgHint_exact he e0 fun j hj => ed j hj
  · have hnc : (atomsOf (fn% «assert_small_g_power»).body.tail).all (fun a => !isComputed a) = true := by
      decide +kernel
    exact exact_of_not_computed (by simpa using List.all_eq_true.mp hnc a (mem_atomsOf' ha))

end
end LeanVM.Guest.B1.VsC
