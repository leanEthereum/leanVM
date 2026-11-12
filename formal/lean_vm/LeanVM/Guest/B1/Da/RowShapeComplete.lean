/-
  LeanVM.Guest.B1.Da.RowShapeComplete

  `da_row_shape`, completely: a row count `1 ≤ r ≤ 1024` and its padded count's log give the core IR
  relation (TRIAGE G #91).
-/

module

public import LeanVM.Guest.B1.Da.RowShape
public import LeanVM.Guest.B1.Digest.CompleteSmall

/-!
# `da_row_shape`, completely

On a memory image (its range checks read below `2^16`) with the exponent table at `g_squares`,
`da_row_shape(g^r, g^L, g_squares)` holds for `1 ≤ r ≤ 1024` and `2^L = LeanDa.nPad r`, returning
`g^(2^L)` and `g^(2^L - r)`: the hinted inverse of `g^r + 1` (nonzero, `r ≠ 0`), the quotients
`g^(2^L - r)` and `g^(2r - 2^L - 1)`, every range check within its bound.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

/-- `da_row_shape`'s meaning gives its core IR, on a memory defined below `2^16`. -/
def da_row_shape_complete_Spec : Prop :=
  ∀ (rd : Reader), Sig.MemOK rd (2 ^ 16) → ∀ gsq : E, SquaresAt rd gsq → ∀ r L : ℕ, 1 ≤ r →
    r ≤ LeanDa.maxRows → 2 ^ L = LeanDa.paddedRowCount r →
      coreProgram.Rel rd "da_row_shape" [gen ^ r, gen ^ L, gsq] [gen ^ 2 ^ L, gen ^ (2 ^ L - r)]

theorem core25_body : Fn.body Data.core28 = [
    .atom (.const (.n 3) (word 1 0)), .atom (.add (.n 4) (.n 0) (.n 3)),
    .atom (.hint (.inverse (.n 4) (.n 5))), .atom (.assertNe (.n 4) (.n 5) (.n 6)),
    .atom (.const (.n 7) (word 281474976776218 0)),
    .atom (.rangeCheck (.n 0) (.n 8) (.n 9) (.n 10) (.n 7)),
    .atom (.const (.n 11) (word 1024 0)),
    .atom (.rangeCheck (.n 1) (.n 12) (.n 13) (.n 14) (.n 11)),
    .atom (.mul (.n 15) (.n 2) (.n 1)), .atom (.load (.n 16) (.n 15) 0),
    .atom (.mul (.n 16) (.n 17) (.n 0)), .atom (.const (.n 18) (word 281474976776218 0)),
    .atom (.rangeCheck (.n 17) (.n 19) (.n 20) (.n 21) (.n 18)),
    .atom (.const (.n 22) (word 140737488388109 0)), .atom (.mul (.n 23) (.n 0) (.n 0)),
    .atom (.const (.n 24) (word 2 0)), .atom (.mul (.n 25) (.n 16) (.n 24)),
    .atom (.mul (.n 23) (.n 26) (.n 25)),
    .atom (.rangeCheck (.n 26) (.n 27) (.n 28) (.n 29) (.n 22)),
    .atom (.copy (.n 30) (.n 16)), .atom (.copy (.n 31) (.n 17)), .ret [.n 30, .n 31]] :=
  stmtsEqb_sound (by decide +kernel)

/-- The padded count is between `r` and `2r`. -/
theorem nPad_bounds {r : ℕ} (hr : 1 ≤ r) : r ≤ LeanDa.paddedRowCount r ∧ LeanDa.paddedRowCount r < 2 * r := by
  unfold LeanDa.paddedRowCount LeanDa.logPaddedRowCount
  refine ⟨Nat.le_pow_clog (by norm_num) r, ?_⟩
  rcases Nat.lt_or_ge 1 r with h | h
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    have h2 : 0 < Nat.clog 2 r := Nat.clog_pos (by norm_num) h
    have : 2 ^ Nat.clog 2 r = 2 * 2 ^ (Nat.clog 2 r).pred := by
      rw [← pow_succ']; congr 1; exact (Nat.succ_pred_eq_of_pos h2).symm
    omega
  · have : r = 1 := by omega
    subst this
    simp

set_option maxRecDepth 10000 in
/-- **`da_row_shape` is complete** on a memory defined below `2^16`, reading `g^(2^L)` at
`g_squares·g^L`. -/
theorem da_row_shape_complete' (rd : Reader) (hm : Sig.MemOK rd (2 ^ 16)) (gsq : E) (r L : ℕ)
    (hsq : LoadHolds rd gsq L (gen ^ 2 ^ L)) (hr1 : 1 ≤ r) (hr : r ≤ LeanDa.maxRows)
    (hL : 2 ^ L = LeanDa.paddedRowCount r) :
    coreProgram.Rel rd "da_row_shape" [gen ^ r, gen ^ L, gsq] [gen ^ 2 ^ L, gen ^ (2 ^ L - r)] := by
  unfold LeanDa.maxRows at hr
  obtain ⟨hlo, hhi⟩ := nPad_bounds hr1
  have hlo' : r ≤ 2 ^ L := hL ▸ hlo
  have hhi' : 2 ^ L < 2 * r := hL ▸ hhi
  have hlt : 2 ^ L < 2 ^ 11 := by
    calc 2 ^ L < 2 * r := hhi'
      _ ≤ 2 ^ 11 := by norm_num; omega
  have hL10 : L ≤ 10 := by
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
    omega
  have hpow : 2 ^ L ≤ 1024 := by
    calc 2 ^ L ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) hL10
      _ = 1024 := by norm_num
  obtain ⟨t9, t10, h9, e8, h10⟩ := rc_holds' hm (k := r) (K := 1024) (by omega) (by norm_num)
  obtain ⟨t13, t14, h13, e12, h14⟩ := rc_holds' hm (k := L) (K := 10) (by omega) (by norm_num)
  obtain ⟨t20, t21, h20, e19, h21⟩ := rc_holds' hm (k := 2 ^ L - r) (K := 1024) (by omega)
    (by norm_num)
  obtain ⟨t28, t29, h28, e27, h29⟩ := rc_holds' hm (k := 2 * r - 2 ^ L - 1) (K := 1023) (by omega)
    (by norm_num)
  have hne : gen ^ r + word 1 0 ≠ 0 := by
    rw [word_one, Ne, e_add_eq_zero_iff, ← pow_zero gen]
    intro h
    have := gen_pow_inj' (by omega) (by omega) h
    omega
  refine (rel_iff_sem find_da_row_shape _ _).mpr ⟨Val.ofArgs [gen ^ r, gen ^ L, gsq, word 1 0,
    gen ^ r + word 1 0, (gen ^ r + word 1 0)⁻¹, (gen ^ r + word 1 0) * (gen ^ r + word 1 0)⁻¹,
    word 281474976776218 0, gen ^ (1024 - r), t9, t10, word 1024 0, gen ^ (10 - L), t13, t14,
    gsq * gen ^ L, gen ^ 2 ^ L, gen ^ (2 ^ L - r), word 281474976776218 0,
    gen ^ (1024 - (2 ^ L - r)), t20, t21, word 140737488388109 0, gen ^ r * gen ^ r, word 2 0,
    gen ^ 2 ^ L * word 2 0, gen ^ (2 * r - 2 ^ L - 1), gen ^ (1023 - (2 * r - 2 ^ L - 1)), t28, t29,
    gen ^ 2 ^ L, gen ^ (2 ^ L - r)], rfl, ?_⟩
  rw [core25_body]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, ofArgs_n,
    List.getD_cons_succ, List.getD_cons_zero]
  refine ⟨trivial, trivial, trivial, ⟨trivial, mul_inv_cancel₀ hne⟩, trivial,
    ⟨h9, by rw [word_g1024]; exact e8, h10⟩, trivial, ⟨h13, by rw [word_g10]; exact e12, h14⟩,
    trivial, ?_, ?_, trivial, ⟨h20, by rw [word_g1024]; exact e19, h21⟩, trivial, trivial, trivial,
    trivial, ?_, ⟨h28, by rw [word_g1023]; exact e27, h29⟩, trivial, trivial, trivial⟩
  · rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hsq
  · rw [← pow_add]; congr 1; omega
  · rw [word_gen, ← pow_succ, ← pow_add, ← pow_add]; congr 1; omega

/-- **`da_row_shape` is complete.** -/
theorem da_row_shape_complete : da_row_shape_complete_Spec := by
  intro rd hm gsq hsq r L hr1 hr hL
  have hL10 : L ≤ 10 := by
    unfold LeanDa.maxRows at hr
    obtain ⟨-, hhi⟩ := nPad_bounds hr1
    have hlt : 2 ^ L < 2 ^ 11 := by
      calc 2 ^ L < 2 * r := hL ▸ hhi
        _ ≤ 2 ^ 11 := by norm_num; omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
    omega
  exact da_row_shape_complete' rd hm gsq r L (hsq L (by omega)) hr1 hr hL

end
end LeanVM.Guest.B1.Da
