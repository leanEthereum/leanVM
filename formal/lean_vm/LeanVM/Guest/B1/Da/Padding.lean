/-
  LeanVM.Guest.B1.Da.Padding

  `da_padding`'s core IR gives its meaning (TRIAGE G #91).
-/

module

public import LeanVM.Guest.B1.Main.Loops
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Consts
import LeanVM.Guest.B1.Common.Vc

/-!
# `da_padding`

`da_padding(n_blob_g)`: `n_blob_g ≠ 1` (an inverse), `n_blob_g = g^r` with `r ≤ M` (a range check
against `g^M`, `M = DA_MAX_ROWS`), and the returned `gap_g` with `gap_g · n_blob_g = g^M`, so
`gap_g = g^(M - r)`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

/-- `x = y · z`, by any `MUL` of the list. -/
def isMulAt (x y z : V) : Atom → Bool
  | .mul d a b => decide (d = x) && decide (a = y) && decide (b = z)
  | _ => false

theorem mulAt_sound {rd : Reader} {σ : Val} {atoms : List Atom} {x y z : V}
    (h : atoms.any (isMulAt x y z) = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    σ x = σ y * σ z := by
  obtain ⟨a, hp, ha⟩ := any_holds h hat
  cases a <;> simp only [isMulAt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp
  exact ha

/-- `x ≠ 0`, by an `assert_ne` through `inv`, `p`. -/
def isNeAt (x : V) : Atom → Bool
  | .assertNe d _ _ => decide (d = x)
  | _ => false

theorem ne_sound {rd : Reader} {σ : Val} {atoms : List Atom} {x : V}
    (h : atoms.any (isNeAt x) = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) : σ x ≠ 0 := by
  obtain ⟨a, hp, ha⟩ := any_holds h hat
  cases a <;> simp only [isNeAt, Bool.false_eq_true, decide_eq_true_eq] at hp
  subst hp
  intro h0
  obtain ⟨h1, h2⟩ := ha
  rw [h1, h0, zero_mul] at h2
  exact zero_ne_one h2

/-- The range check's bound `g^M`, a word of one limb below `g^64`. -/
theorem word_gMax : word (2 ^ guest_const% DA_MAX_ROWS) 0 = gen ^ guest_const% DA_MAX_ROWS := word_two_pow (by decide)

theorem da_padding_holds : da_padding_sound_Spec := by
  intro rd hm args rets
  rw [rel_iff_fnSem find_da_padding]
  vc
  rw [show (4294967296 : ℕ) = 2 ^ guest_const% DA_MAX_ROWS by decide, word_gMax]
  rintro ⟨nb, rfl, inv, hinv, y, t1, l1, hk, t2, l2, x, hx, rfl⟩
  obtain ⟨r, hr, rfl⟩ := rc_const hm (c := guest_const% DA_MAX_ROWS) (by decide) rfl ⟨l1, hk, l2⟩
  have hr1 : r ≠ 0 := by
    rintro rfl
    rw [pow_zero, word_one, e_add_self, zero_mul] at hinv
    exact zero_ne_one hinv
  have hx' : x = gen ^ (guest_const% DA_MAX_ROWS - r) := by
    refine mul_right_cancel₀ (gen_pow_ne_zero r) ?_
    rw [← hx, ← pow_add]
    congr 1
    omega
  refine ⟨r, by omega, by rw [maxRows_eq]; omega, rfl, ?_⟩
  rw [hx', maxRows_eq]

end
end LeanVM.Guest.B1.Da
