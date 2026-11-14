/-
  LeanVM.Guest.B1.Sig.Shifts

  `shifts` (`lean_ethereum.py:3500-3506` at leanVM `1a379148`) over bits pinned Boolean: output
  `l` is the integer of the bits shifted right by `l`, as a word.
-/

module

public import LeanVM.Guest.B1.Sig.Merkle
public import LeanVM.Guest.Value.Bits

/-!
# Shifts of bits

`shifts_sound`: on bits pinned Boolean (`IsBit`), the cell `outBase + 3 (n - 1 - l)` holds
`eOfNat (N >>> l)` for `N` the bits' integer (`bitsOf`), each step one Horner step
`bit + x · out` without reduction (`gen_mul_eOfNat`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The integer of the `n` bits from `bitBase`, the cell holding `1` a set bit. -/
noncomputable def bitsOf (σ : Val) (bitBase n : Nat) : Nat :=
  bitsVal (fun j => decide (σ (.n (bitBase + j)) = 1)) n

theorem bit_eOfNat {x : E} (h : IsBit x) : x = eOfNat (decide (x = 1)).toNat := by
  rcases isBit_cases h with h0 | h1
  · subst h0; simp [Value.eOfNat_zero]
  · subst h1; simp [Value.eOfNat_one]

theorem shiftRight_split (N k : Nat) : N >>> k = 2 * (N >>> (k + 1)) + (N.testBit k).toNat := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.testBit, Nat.shiftRight_eq_div_pow,
    pow_succ, ← Nat.div_div_eq_div_mul]
  have := Nat.div_add_mod (N / 2 ^ k) 2
  rcases Nat.mod_two_eq_zero_or_one (N / 2 ^ k) with h | h <;> simp [h] <;> omega

theorem mem_shifts_step {bitBase n outBase r : Nat} (hr : 1 ≤ r) (hrn : r < n) :
    ∀ x ∈ [cst (outBase + 3 * r - 2) (word 2 0),
      mulS (.n (outBase + 3 * r - 1)) (.n (outBase + 3 * r - 2)) (.n (outBase + 3 * r - 3)),
      addS (.n (outBase + 3 * r)) (.n (bitBase + n - 1 - r)) (.n (outBase + 3 * r - 1))],
      x ∈ shifts bitBase n outBase := by
  intro x hx
  simp only [shifts, List.mem_cons, List.mem_flatMap, List.mem_range]
  refine Or.inr ⟨r - 1, by omega, ?_⟩
  rw [show r - 1 + 1 = r by omega]
  simpa using hx

/-- **`shifts`, sound**: the cell `outBase + 3 r` holds the bits' integer shifted right by
`n - 1 - r`. -/
theorem shifts_sound {bitBase n outBase : Nat} (hn : 0 < n) (hn63 : n ≤ 63)
    (hbits : ∀ j < n, IsBit (σ (.n (bitBase + j)))) (h : AtomsHold rd σ (shifts bitBase n outBase)) :
    ∀ r < n, σ (.n (outBase + 3 * r)) = eOfNat (bitsOf σ bitBase n >>> (n - 1 - r)) := by
  have hN : bitsOf σ bitBase n < 2 ^ n := bitsVal_lt _ _
  have htb : ∀ k < n, (bitsOf σ bitBase n).testBit k = decide (σ (.n (bitBase + k)) = 1) := by
    intro k hk
    rw [bitsOf, testBit_bitsVal]
    simp [hk]
  intro r hr
  induction r with
  | zero =>
      have e := h.atom (List.mem_cons_self ..)
      simp only [Atom.Holds] at e
      rw [Nat.mul_zero, Nat.add_zero, e]
      rw [show bitBase + n - 1 = bitBase + (n - 1) by omega, bit_eOfNat (hbits (n - 1) (by omega)),
        ← htb (n - 1) (by omega)]
      congr 1
      rw [Nat.sub_zero]
      have h1 : bitsOf σ bitBase n >>> (n - 1) < 2 := by
        rw [Nat.shiftRight_eq_div_pow]
        exact Nat.div_lt_of_lt_mul (by rw [← pow_succ, show n - 1 + 1 = n by omega]; exact hN)
      rw [shiftRight_split, show bitsOf σ bitBase n >>> (n - 1 + 1) = 0 by
        rw [Nat.shiftRight_eq_div_pow, show n - 1 + 1 = n by omega]; exact Nat.div_eq_of_lt hN]
      simp
  | succ r ih =>
      have hm := mem_shifts_step (bitBase := bitBase) (outBase := outBase) (show 1 ≤ r + 1 by omega) hr
      have e1 := h.atom (hm _ (List.mem_cons_self ..))
      have e2 := h.atom (hm _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      have e3 := h.atom (hm _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
      simp only [Atom.Holds] at e1 e2 e3
      rw [e3, e2, e1, word_two, show outBase + 3 * (r + 1) - 3 = outBase + 3 * r by omega, ih (by omega),
        Value.gen_mul_eOfNat (by
          have : bitsOf σ bitBase n >>> (n - 1 - r) ≤ bitsOf σ bitBase n := Nat.shiftRight_le _ _
          have h63 : 2 ^ n ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) hn63
          omega),
        show bitBase + n - 1 - (r + 1) = bitBase + (n - 1 - (r + 1)) by omega,
        bit_eOfNat (hbits (n - 1 - (r + 1)) (by omega)),
        ← htb _ (by omega), add_comm,
        show (2 : Nat) * (bitsOf σ bitBase n >>> (n - 1 - r)) =
          2 ^ 1 * (bitsOf σ bitBase n >>> (n - 1 - r)) by ring,
        Value.eOfNat_add_of_lt (by cases (bitsOf σ bitBase n).testBit (n - 1 - (r + 1)) <;> simp)]
      congr 1
      rw [shiftRight_split _ (n - 1 - (r + 1)), show n - 1 - (r + 1) + 1 = n - 1 - r by omega]
      ring

end
end LeanVM.Guest.B1.Sig
