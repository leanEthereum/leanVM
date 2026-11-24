/-
  LeanVM.Guest.Value.Gpow

  Pointer arithmetic in powers of `g`: addresses, the limb a pointer reads, `K`-membership, and
  injectivity below the order of `g`.
-/

module

public import LeanVM.Guest.Value.Bits
public import LeanVM.Guest.Value.FieldBits

/-!
# Powers of `g`

A pointer is a power of `g` (`gen ^ a`, in `K` as `addressOfIndex a`), and the guest moves along
memory by multiplying pointers. This is the one home of the facts the proofs share about them:
products of addresses and of powers, the address a load through a pointer reads
(`limb0_ofK_mul_gen_pow_mul`), `K`-membership (`isInK_add`, `isInK_mul`, `gen_pow_isInK`), and the
loop guard `1 + g^a` (`one_add_gen_pow_ne_zero_iff`). Injectivity below the order of `g` is
`gen_pow_inj` (`LeanVM.Guest.Value.Bits`).
-/

namespace LeanVM.Guest.Value

open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Addresses -/

theorem addressOfIndex_mul_addressOfIndex (a b : ℕ) :
    addressOfIndex a * addressOfIndex b = addressOfIndex (a + b) := by
  simp [addressOfIndex, pow_add]

theorem limb0_ofK_addressOfIndex (a : ℕ) :
    (ofK (addressOfIndex a)).limb 0 = addressOfIndex a := by
  simp

theorem limb0_ofK_addressOfIndex_mul (a b : ℕ) :
    (ofK (addressOfIndex a)).limb 0 * addressOfIndex b = addressOfIndex (a + b) := by
  rw [limb0_ofK_addressOfIndex, addressOfIndex_mul_addressOfIndex]

theorem ofK_addressOfIndex_mul_gen_pow (a b : ℕ) :
    ofK (addressOfIndex a) * gen ^ b = ofK (addressOfIndex (a + b)) := by
  rw [gen_pow_eq_ofK, ← ofK_mul, addressOfIndex_mul_addressOfIndex]

/-- The address a load through `g^b·g^e` at offset `t` reads. -/
theorem limb0_ofK_mul_gen_pow_mul (b e t : ℕ) :
    (ofK (addressOfIndex b) * gen ^ e).limb 0 * addressOfIndex t = addressOfIndex (b + e + t) := by
  rw [ofK_addressOfIndex_mul_gen_pow, limb0_ofK_addressOfIndex_mul]

/-! ## Products of powers -/

theorem gen_pow_mul_gen (a : ℕ) : gen ^ a * gen = gen ^ (a + 1) := (pow_succ _ _).symm

theorem gen_pow_pow (a b : ℕ) : (gen ^ a) ^ b = gen ^ (b * a) := (pow_mul' _ _ _).symm

/-! ## Membership in `K` -/

theorem isInK_add {a b : E} (ha : IsInK a) (hb : IsInK b) : IsInK (a + b) := by
  obtain ⟨a, rfl⟩ := (isInK_iff _).mp ha
  obtain ⟨b, rfl⟩ := (isInK_iff _).mp hb
  rw [← ofK_add]; exact ofK_isInK _

theorem isInK_mul {a b : E} (ha : IsInK a) (hb : IsInK b) : IsInK (a * b) := by
  obtain ⟨a, rfl⟩ := (isInK_iff _).mp ha
  obtain ⟨b, rfl⟩ := (isInK_iff _).mp hb
  rw [← ofK_mul]; exact ofK_isInK _

theorem gen_pow_isInK (j : ℕ) : IsInK (gen ^ j) := by
  rw [gen_pow_eq_ofK]; exact ofK_isInK _

theorem one_add_gen_pow_isInK (k : ℕ) : IsInK (1 + gen ^ k) :=
  isInK_add (by simpa using gen_pow_isInK 0) (gen_pow_isInK k)

/-! ## Powers below the order of `g` -/

/-- A loop guard `1 + g^a` vanishes only at `a = 0`, below the order of `g`. -/
theorem one_add_gen_pow_ne_zero_iff {a : ℕ} (ha : a < 2 ^ 64 - 1) : 1 + gen ^ a ≠ 0 ↔ a ≠ 0 := by
  rw [Ne, e_add_eq_zero_iff, eq_comm, gen_pow_eq_one_iff ha]

end
end LeanVM.Guest.Value
