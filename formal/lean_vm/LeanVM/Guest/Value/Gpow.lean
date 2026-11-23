/-
  LeanVM.Guest.Value.Gpow

  Pointer arithmetic in powers of `g`: addresses, the limb a pointer reads, `K`-membership, and
  injectivity below the order of `g`.
-/

module

public import LeanVM.Guest.Value.Bits
public import LeanVM.Guest.Value.FieldBits
public import LeanVM.Guest.Value.GpowAttr

/-!
# Powers of `g`

A pointer is a power of `g` (`gen ^ a`, in `K` as `addressOfIndex a`), and the guest moves along
memory by multiplying pointers. The lemmas tagged `gpow_simps` rewrite a product of pointers to one
power whose exponent is a sum, so that pointer equalities reduce to equalities of exponents:
the `gpow` tactic runs `simp only [gpow_simps]` and closes what is left by `omega` or `ring`.

`isInK_add`, `isInK_mul`, `gen_pow_isInK` and `ofK_isInK` close `IsInK` goals by `grind`;
`gen_pow_inj` (`LeanVM.Guest.Value.Bits`) is injectivity below the order of `g`.
-/

namespace LeanVM.Guest.Value

open LeanVM.Parameters

@[expose] public section

/-! ## Addresses -/

@[gpow_simps] theorem addressOfIndex_mul_addressOfIndex (a b : ℕ) :
    addressOfIndex a * addressOfIndex b = addressOfIndex (a + b) :=
  (pow_add _ _ _).symm

@[gpow_simps] theorem limb0_ofK_addressOfIndex (a : ℕ) :
    (ofK (addressOfIndex a)).limb 0 = addressOfIndex a := by
  simp

theorem limb0_ofK_addressOfIndex_mul (a b : ℕ) :
    (ofK (addressOfIndex a)).limb 0 * addressOfIndex b = addressOfIndex (a + b) := by
  simp only [gpow_simps]

@[gpow_simps] theorem ofK_addressOfIndex_mul_gen_pow (a b : ℕ) :
    ofK (addressOfIndex a) * gen ^ b = ofK (addressOfIndex (a + b)) := by
  rw [gen_pow_eq_ofK, ← ofK_mul, addressOfIndex_mul_addressOfIndex]

/-- The address a load through `g^b·g^e` at offset `t` reads. -/
theorem limb0_ofK_mul_gen_pow_mul (b e t : ℕ) :
    (ofK (addressOfIndex b) * gen ^ e).limb 0 * addressOfIndex t = addressOfIndex (b + e + t) := by
  simp only [gpow_simps]

/-! ## Products of powers -/

@[gpow_simps] theorem gen_pow_mul_gen_pow (a b : ℕ) : gen ^ a * gen ^ b = gen ^ (a + b) :=
  (pow_add _ _ _).symm

@[gpow_simps] theorem mul_gen_pow_mul_gen_pow (x : E) (a b : ℕ) :
    x * gen ^ a * gen ^ b = x * gen ^ (a + b) := by
  rw [mul_assoc, gen_pow_mul_gen_pow]

@[gpow_simps] theorem gen_pow_mul_gen (a : ℕ) : gen ^ a * gen = gen ^ (a + 1) := (pow_succ _ _).symm

@[gpow_simps] theorem mul_gen_pow_mul_gen (x : E) (a : ℕ) : x * gen ^ a * gen = x * gen ^ (a + 1) := by
  rw [mul_assoc, gen_pow_mul_gen]

@[gpow_simps] theorem gen_pow_pow (a b : ℕ) : (gen ^ a) ^ b = gen ^ (b * a) := (pow_mul' _ _ _).symm

/-! ## Membership in `K` -/

@[grind ←] theorem isInK_add {a b : E} (ha : IsInK a) (hb : IsInK b) : IsInK (a + b) := by
  obtain ⟨a, rfl⟩ := (isInK_iff _).mp ha
  obtain ⟨b, rfl⟩ := (isInK_iff _).mp hb
  rw [← ofK_add]; exact ofK_isInK _

@[grind ←] theorem isInK_mul {a b : E} (ha : IsInK a) (hb : IsInK b) : IsInK (a * b) := by
  obtain ⟨a, rfl⟩ := (isInK_iff _).mp ha
  obtain ⟨b, rfl⟩ := (isInK_iff _).mp hb
  rw [← ofK_mul]; exact ofK_isInK _

@[grind .] theorem gen_pow_isInK (j : ℕ) : IsInK (gen ^ j) := by
  rw [gen_pow_eq_ofK]; exact ofK_isInK _

attribute [grind .] ofK_isInK

theorem one_add_gen_pow_isInK (k : ℕ) : IsInK (1 + gen ^ k) :=
  isInK_add (by simpa using gen_pow_isInK 0) (gen_pow_isInK k)

/-! ## Powers below the order of `g` -/

/-- A loop guard `1 + g^a` vanishes only at `a = 0`, below the order of `g`. -/
theorem one_add_gen_pow_ne_zero_iff {a : ℕ} (ha : a < 2 ^ 64 - 1) : 1 + gen ^ a ≠ 0 ↔ a ≠ 0 := by
  rw [Ne, e_add_eq_zero_iff, eq_comm, gen_pow_eq_one_iff ha]

/-- Pointer equalities: one power of `g` per side by `gpow_simps`, then the exponents by `omega`
or `ring`. -/
macro "gpow" : tactic =>
  `(tactic| (simp only [gpow_simps]; try (first | rfl | (congr 1; first | omega | ring))))

end
end LeanVM.Guest.Value
