/-
  LeanVM.Guest.B1.Da.Padding

  `da_padding`'s core IR gives its meaning (TRIAGE G #91).
-/

module

public import LeanVM.Guest.B1.Main.Loops
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Source

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

/-- **`da_padding`'s body, checked.** -/
def padOk (fn : Fn) : Bool :=
  decide (fn.params = [.n 0]) &&
  match splitBody fn.body with
  | some (A, vs) =>
    decide (vs = [.n 11]) &&
    A.any (isConstAt (.n 1) 1 0) && A.any (isAddAt (.n 2) (.n 0) (.n 1)) && A.any (isNeAt (.n 2)) &&
    rcConstOk A (.n 0) (2 ^ guest_const% DA_MAX_ROWS) &&
    A.any (isConstAt (.n 9) (2 ^ guest_const% DA_MAX_ROWS) 0) && A.any (isMulAt (.n 9) (.n 10) (.n 0)) &&
    A.any (isCopyAt (.n 11) (.n 10))
  | none => false

set_option maxRecDepth 100000 in
theorem pad_ok : padOk fn% «da_padding» = true := by decide +kernel

theorem da_padding_holds : da_padding_sound_Spec := by
  intro rd hm args rets hrel
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_da_padding _ _).mp hrel
  have hok := pad_ok
  unfold padOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hparams, hok⟩ := hok
  split at hok
  · rename_i A vs hsp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨rfl, hc1⟩, ha2⟩, hne⟩, hr0⟩, hc9⟩, hm9⟩, hcp11⟩ := hok
    rw [splitBody_eq hsp, holdsList_atoms_ret] at hb
    obtain ⟨hat, hret⟩ := hb
    rw [hparams] at hpar
    subst hpar
    simp only [List.map_cons, List.map_nil, MeaningDaPadding]
    obtain ⟨r, hr, h0⟩ := rcConst_sound hm (by norm_num) word_gMax hr0 hat
    have hr1 : r ≠ 0 := by
      intro hr0'
      have := ne_sound hne hat
      rw [add_sound ha2 hat, h0, hr0', pow_zero, const_sound hc1 hat, word_one] at this
      exact this (e_add_eq_zero_iff.mpr rfl)
    have h10 : σ (.n 10) = gen ^ (guest_const% DA_MAX_ROWS - r) := by
      have e := mulAt_sound hm9 hat
      rw [const_sound hc9 hat, word_gMax, h0] at e
      refine mul_right_cancel₀ (gen_pow_ne_zero r) ?_
      rw [← e, ← pow_add]
      congr 1
      omega
    refine ⟨r, by omega, by rw [maxRows_eq]; omega, h0, ?_⟩
    have hret' : [σ (.n 11)] = rets := hret
    rw [← hret', copy_sound hcp11 hat, h10, maxRows_eq]
  · exact absurd hok (by simp)

end
end LeanVM.Guest.B1.Da
