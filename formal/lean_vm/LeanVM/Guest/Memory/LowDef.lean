/-
  LeanVM.Guest.Memory.LowDef

  The memory defined below `2^k` and the range checks that pass there, apart from the placement
  machinery (`Uniform`), so that a module reading only range checks' words can name them without
  importing the guest's bodies.
-/

module

public import LeanVM.Guest.Core
public import LeanVM.Guest.Value.Bits

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

theorem addr_ofK (b k : ℕ) : (ofK (addressOfIndex b)).limb 0 * addressOfIndex k = addressOfIndex (b
    + k) := by
  rw [limb_ofK]; exact (pow_add _ _ _).symm

end
end LeanVM.Guest.B1.Main

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- The memory is defined at the addresses below `2^k`, where range checks `log x < K ≤ 2^k`
read (any memory image of at least `2^k` words). -/
def LowDef (k : ℕ) (rd : Reader) : Prop := ∀ i < 2 ^ k, (rd (addressOfIndex i)).isSome

theorem LowDef.mono {k k' : ℕ} {rd : Reader} (h : LowDef k rd) (hk : k' ≤ k) : LowDef k' rd :=
  fun i hi => h i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by decide) hk))

/-! ## Range checks on a memory defined below `2^k` -/

/-- A range check's auxiliary words for `x = g^e` against `g^(K-1)`: the complement `g^(K-1-e)`
and the words the memory holds at both. -/
noncomputable def rcLow (rd : Reader) (e K : ℕ) : E × E × E :=
  (ofK (addressOfIndex (K - 1 - e)), (rd (addressOfIndex e)).getD 0, (rd (addressOfIndex (K - 1 -
      e))).getD 0)

theorem loadHolds_low {k : ℕ} {rd : Reader} (hl : LowDef k rd) {i : ℕ} (hi : i < 2 ^ k) :
    LoadHolds rd (ofK (addressOfIndex i)) 0 ((rd (addressOfIndex i)).getD 0) := by
  refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
  rw [Main.addr_ofK, Nat.add_zero]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hl i hi)
  rw [hv]; rfl

/-- **A range check passes** on a memory defined below `2^k`, for `x = g^e`, `e < K ≤ 2^k`. -/
theorem rc_complete_low {k : ℕ} {rd : Reader} (hl : LowDef k rd) {K e : ℕ} (hK : K ≤ 2 ^ k)
    (he : e < K) :
    LoadHolds rd (ofK (addressOfIndex e)) 0 (rcLow rd e K).2.1 ∧
      ofK (addressOfIndex (K - 1)) = ofK (addressOfIndex e) * (rcLow rd e K).1 ∧
      LoadHolds rd (rcLow rd e K).1 0 (rcLow rd e K).2.2 := by
  refine ⟨loadHolds_low hl (by omega), ?_, loadHolds_low hl (by omega)⟩
  rw [rcLow, ← ofK_mul, addressOfIndex, addressOfIndex, ← pow_add]
  congr 2
  omega

end
end LeanVM.Guest.B1
