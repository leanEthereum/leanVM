/-
  LeanVM.Guest.B1.Da.RowShape

  `da_row_shape`'s core IR gives its meaning (TRIAGE G #91).
-/

module

public import LeanVM.Guest.B1.Main.Loops
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Source

/-!
# `da_row_shape`

`da_row_shape(n_blob_g, g_log_pad, g_squares)`: `n_blob_g ≠ 1` (an inverse),
`n_blob_g = g^r` with `r ≤ M`, `g_log_pad = g^L` with `L ≤ log M` (range checks against `g^M`,
`g^(log M)`, for `M = DA_MAX_ROWS` and `log M = DA_LOG_MAX_ROWS`), `n_pad_g = g_squares[L] = g^(2^L)`,
`gap_g = n_pad_g / n_blob_g = g^d` (`d ≤ M`), and `n_blob_g² = f · n_pad_g · g` with `f = g^e`,
`e ≤ M - 1`. So
`r + d = 2^L` and `2r = e + 2^L + 1`: `2^(L-1) < r ≤ 2^L`, the padded count `LeanDa.nPad r`.
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

/-- The range checks' bounds: `g^M`, `g^(M - 1)` and `g^(log M)`, words of one limb below `g^64`. -/
theorem word_gMax : word (2 ^ guest_const% DA_MAX_ROWS) 0 = gen ^ guest_const% DA_MAX_ROWS := word_two_pow (by decide)

theorem word_gMaxPred : word (2 ^ (guest_const% DA_MAX_ROWS - 1)) 0 = gen ^ (guest_const% DA_MAX_ROWS - 1) := word_two_pow (by decide)

theorem word_gLog : word (2 ^ guest_const% DA_LOG_MAX_ROWS) 0 = gen ^ guest_const% DA_LOG_MAX_ROWS := word_two_pow (by decide)

/-- **`da_row_shape`'s body, checked.** -/
def rsOk (fn : Fn) : Bool :=
  decide (fn.params = [.n 0, .n 1, .n 2]) &&
  match splitBody fn.body with
  | some (A, vs) =>
    decide (vs = [.n 30, .n 31]) &&
    A.any (isConstAt (.n 3) 1 0) && A.any (isAddAt (.n 4) (.n 0) (.n 3)) && A.any (isNeAt (.n 4)) &&
    rcConstOk A (.n 0) (2 ^ guest_const% DA_MAX_ROWS) && rcConstOk A (.n 1) (2 ^ guest_const% DA_LOG_MAX_ROWS) &&
    A.any (isMulAt (.n 15) (.n 2) (.n 1)) && A.any (isLoadAt (.n 16) (.n 15) 0) &&
    A.any (isMulAt (.n 16) (.n 17) (.n 0)) && rcConstOk A (.n 17) (2 ^ guest_const% DA_MAX_ROWS) &&
    A.any (isMulAt (.n 23) (.n 0) (.n 0)) && A.any (isConstAt (.n 24) 2 0) &&
    A.any (isMulAt (.n 25) (.n 16) (.n 24)) && A.any (isMulAt (.n 23) (.n 26) (.n 25)) &&
    rcConstOk A (.n 26) (2 ^ (guest_const% DA_MAX_ROWS - 1)) &&
    A.any (isCopyAt (.n 30) (.n 16)) && A.any (isCopyAt (.n 31) (.n 17))
  | none => false

set_option maxRecDepth 100000 in
theorem rs_ok : rsOk fn% «da_row_shape» = true := by decide +kernel

/-- The padded count: `2^L` when `2^L < 2r ≤ 2^(L+1)`. -/
theorem nPad_of {r L : ℕ} (h1 : r ≤ 2 ^ L) (h2 : 2 ^ L < 2 * r) : LeanDa.paddedRowCount r = 2 ^ L := by
  unfold LeanDa.paddedRowCount LeanDa.logPaddedRowCount
  congr 1
  apply le_antisymm
  · exact Nat.clog_le_of_le_pow h1
  · rcases Nat.eq_zero_or_pos L with rfl | hL
    · exact Nat.zero_le _
    · have : 2 ^ (L - 1) < r := by
        have : 2 ^ L = 2 * 2 ^ (L - 1) := by rw [← pow_succ']; congr 1; omega
        omega
      have := Nat.lt_clog_iff_pow_lt (b := 2) (by norm_num) |>.mpr this
      omega

theorem da_row_shape_holds : da_row_shape_sound_Spec := by
  intro rd hm args rets hrel
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_da_row_shape _ _).mp hrel
  have hok := rs_ok
  unfold rsOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hparams, hok⟩ := hok
  split at hok
  · rename_i A vs hsp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨rfl, hc3⟩, ha4⟩, hne⟩, hr0⟩, hr1⟩, hm15⟩, hl16⟩, hm16⟩, hr17⟩, hm23⟩,
      hc24⟩, hm25⟩, hm23'⟩, hr26⟩, hcp30⟩, hcp31⟩ := hok
    rw [splitBody_eq hsp, holdsList_atoms_ret] at hb
    obtain ⟨hat, hret⟩ := hb
    rw [hparams] at hpar
    subst hpar
    simp only [List.map_cons, List.map_nil, MeaningDaRowShape]
    intro hsq
    obtain ⟨r, hr, h0⟩ := rcConst_sound hm (by norm_num) word_gMax hr0 hat
    obtain ⟨L, hL, h1⟩ := rcConst_sound hm (by norm_num) word_gLog hr1 hat
    obtain ⟨d, hd, h17⟩ := rcConst_sound hm (by norm_num) word_gMax hr17 hat
    obtain ⟨e, he, h26⟩ := rcConst_sound hm (by norm_num) word_gMaxPred hr26 hat
    -- n_pad = g^(2^L)
    have h16 : σ (.n 16) = gen ^ 2 ^ L := by
      have hl := load_sound hl16 hat
      rw [mulAt_sound hm15 hat, h1] at hl
      exact loadHolds_unique ((loadHolds_mul_gen_pow rd _ L 0 _).mp hl) (hsq L (by omega))
    have hL2 : 2 ^ L ≤ guest_const% DA_MAX_ROWS := by
      calc 2 ^ L ≤ 2 ^ guest_const% DA_LOG_MAX_ROWS := Nat.pow_le_pow_right (by norm_num) hL
        _ = guest_const% DA_MAX_ROWS := by norm_num
    -- r + d = 2^L
    have hrd : d + r = 2 ^ L := by
      have := mulAt_sound hm16 hat
      rw [h16, h17, h0, ← pow_add] at this
      exact (gen_pow_inj' (by omega) (by omega) this).symm
    -- 2r = e + 2^L + 1
    have hre : r + r = e + (2 ^ L + 1) := by
      have e1 := mulAt_sound hm23 hat
      have e2 := mulAt_sound hm23' hat
      rw [mulAt_sound hm25 hat, h16, const_sound hc24 hat, word_gen, h26, ← pow_succ,
        ← pow_add] at e2
      rw [e1, h0, ← pow_add] at e2
      exact gen_pow_inj' (by omega) (by omega) e2
    -- r ≠ 0
    have hr1' : r ≠ 0 := by
      intro hr0'
      have := ne_sound hne hat
      rw [add_sound ha4 hat, h0, hr0', pow_zero, const_sound hc3 hat, word_one] at this
      exact this (e_add_eq_zero_iff.mpr rfl)
    refine ⟨r, L, by omega, by rw [maxRows_eq]; omega, hL, h0, h1,
      (nPad_of (by omega) (by omega)).symm, ?_⟩
    have hret' : [σ (.n 30), σ (.n 31)] = rets := hret
    rw [← hret', copy_sound hcp30 hat, copy_sound hcp31 hat, h16, h17, show d = 2 ^ L - r by omega]
  · exact absurd hok (by simp)

end
end LeanVM.Guest.B1.Da
