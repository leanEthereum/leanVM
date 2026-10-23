/-
  LeanVM.Guest.B1.Da.RowShape

  B1 for `da_row_shape` (G:2981-2990; TRIAGE #67): the row count of a DA matrix and its padding.
-/

module

public import LeanVM.Guest.B1.Digest.ScaledLog
public import LeanDa.Scheme

/-!
# `da_row_shape`

`da_row_shape(n_blob_g, g_log_pad, g_squares)`: `n_blob_g = g^r` with `1 ≤ r ≤ 1024`,
`g_log_pad = g^lp` with `lp = ⌈log₂ r⌉` (`LeanDa.logPad`), certified by `r ≤ 2^lp < 2r`; it returns
the padded count `g^(2^lp)` and the gap `g^(2^lp - r)`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **`da_row_shape`**. -/
def Meaning_da_row_shape (args rets : List E) : Prop :=
  ∃ n_blob glp gsq n_pad gap, args = [n_blob, glp, gsq] ∧ rets = [n_pad, gap] ∧
    ∃ r, 1 ≤ r ∧ r ≤ LeanDa.maxRows ∧ n_blob = gen ^ r ∧ glp = gen ^ LeanDa.logPad r ∧
      n_pad = gen ^ LeanDa.nPad r ∧ gap = gen ^ (LeanDa.nPad r - r)

/-- `⌈log₂ r⌉` by its two bounds. -/
theorem logPad_iff {r lp : ℕ} (hr : 1 ≤ r) : lp = LeanDa.logPad r ↔ r ≤ 2 ^ lp ∧ 2 ^ lp < 2 * r := by
  unfold LeanDa.logPad
  constructor
  · rintro rfl
    refine ⟨Nat.le_pow_clog (by norm_num) r, ?_⟩
    rcases Nat.eq_or_lt_of_le hr with rfl | h
    · simp
    · have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
      rw [Nat.pred_eq_sub_one] at this
      have hc : 0 < Nat.clog 2 r := Nat.clog_pos (by norm_num) h
      calc 2 ^ Nat.clog 2 r = 2 * 2 ^ (Nat.clog 2 r - 1) := by
            rw [← pow_succ']; congr 1; omega
        _ < 2 * r := by omega
  · rintro ⟨h1, h2⟩
    have hle := Nat.clog_le_of_le_pow h1
    by_contra hne
    have hlt : Nat.clog 2 r < lp := by omega
    have := Nat.le_pow_clog (b := 2) (by norm_num) r
    have : 2 * 2 ^ Nat.clog 2 r ≤ 2 ^ lp := by
      rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) hlt
    omega

/-- `da_row_shape`'s body. -/
def drsBody : List Stmt :=
  ([.const (.n 3) (word 1 0 0), .add (.n 4) (.n 0) (.n 3), .hint (.inverse (.n 4) (.n 5)),
    .assertNe (.n 4) (.n 5) (.n 6), .const (.n 7) (word 281474976776218 0 0),
    .rangeCheck (.n 0) (.n 8) (.n 9) (.n 10) (.n 7), .const (.n 11) (word 1024 0 0),
    .rangeCheck (.n 1) (.n 12) (.n 13) (.n 14) (.n 11), .mul (.n 15) (.n 2) (.n 1),
    .load (.n 16) (.n 15) 0, .mul (.n 16) (.n 17) (.n 0), .const (.n 18) (word 281474976776218 0 0),
    .rangeCheck (.n 17) (.n 19) (.n 20) (.n 21) (.n 18), .const (.n 22) (word 140737488388109 0 0),
    .mul (.n 23) (.n 0) (.n 0), .const (.n 24) (word 2 0 0), .mul (.n 25) (.n 16) (.n 24),
    .mul (.n 23) (.n 26) (.n 25), .rangeCheck (.n 26) (.n 27) (.n 28) (.n 29) (.n 22),
    .copy (.n 30) (.n 16), .copy (.n 31) (.n 17)] : List Atom).map .atom ++ [.ret [.n 30, .n 31]]

set_option maxRecDepth 100000 in
theorem find_da_row_shape : coreProgram.find? "da_row_shape" =
    some ⟨"da_row_shape", [.n 0, .n 1, .n 2], drsBody⟩ :=
  Program.find?_of_indexOf? (j := 24) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem word_g1024 : word 281474976776218 0 0 = gen ^ 1024 := by
  rw [word_eq_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound; omega)]
  congr 1

set_option maxRecDepth 100000 in
theorem word_g1023 : word 140737488388109 0 0 = gen ^ 1023 := by
  rw [word_eq_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound; omega)]
  congr 1

theorem word_g10 : word 1024 0 0 = gen ^ 10 := by
  rw [gen_pow_eq_eOfNat (by omega), word_eq_eOfNat]; rfl

/-- **`da_row_shape` is complete** on a memory defined below `2^16` holding the squares table. -/
theorem da_row_shape_complete {rd : Reader} (hl : Low16 rd) {gsq : E} (hT : SquaresAt rd gsq)
    (n_blob glp : E) (rets : List E) (h : Meaning_da_row_shape [n_blob, glp, gsq] rets) :
    coreProgram.Rel rd "da_row_shape" [n_blob, glp, gsq] rets := by
  rw [rel_of_find find_da_row_shape]
  simp only [Fn.Sem, drsBody, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and]
  revert h
  rintro ⟨_, _, _, n_pad, gap, hargs, rfl, r, hr1, hr2, rfl, rfl, rfl, rfl⟩
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl⟩ := hargs
  unfold LeanDa.maxRows at hr2
  obtain ⟨lp, hlp⟩ : ∃ lp, lp = LeanDa.logPad r := ⟨_, rfl⟩
  rw [LeanDa.nPad, ← hlp]
  obtain ⟨hb1, hb2⟩ := (logPad_iff hr1).mp hlp
  have hlp10 : lp ≤ 10 := by
    by_contra h
    have : 2 ^ 11 ≤ 2 ^ lp := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hpow : 2 ^ lp ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) hlp10
  obtain ⟨t1, t2, l9, -, l10⟩ := rangeCheck_complete_low hl (e := r) (e' := 1024 - r) (by omega) (by omega)
  obtain ⟨t3, t4, l13, -, l14⟩ := rangeCheck_complete_low hl (e := lp) (e' := 10 - lp) (by omega) (by omega)
  obtain ⟨t5, t6, l20, -, l21⟩ := rangeCheck_complete_low hl (e := 2 ^ lp - r)
    (e' := 1024 - (2 ^ lp - r)) (by omega) (by omega)
  obtain ⟨t7, t8, l28, -, l29⟩ := rangeCheck_complete_low hl (e := 2 * r - 2 ^ lp - 1)
    (e' := 1023 - (2 * r - 2 ^ lp - 1)) (by omega) (by omega)
  have hne := gen_pow_ne_one hr1 (by omega)
  rw [← word_one] at hne
  refine ⟨listVal [gen ^ r, gen ^ lp, gsq, word 1 0 0, gen ^ r + word 1 0 0,
    (gen ^ r + word 1 0 0)⁻¹, (gen ^ r + word 1 0 0) * (gen ^ r + word 1 0 0)⁻¹,
    word 281474976776218 0 0, gen ^ (1024 - r), t1, t2, word 1024 0 0, gen ^ (10 - lp), t3, t4,
    gsq * gen ^ lp, gen ^ (2 ^ lp), gen ^ (2 ^ lp - r), word 281474976776218 0 0,
    gen ^ (1024 - (2 ^ lp - r)), t5, t6, word 140737488388109 0 0, gen ^ r * gen ^ r, word 2 0 0,
    gen ^ (2 ^ lp) * word 2 0 0, gen ^ (2 * r - 2 ^ lp - 1),
    gen ^ (1023 - (2 * r - 2 ^ lp - 1)), t7, t8, gen ^ (2 ^ lp), gen ^ (2 ^ lp - r)], rfl, ?_⟩
  simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, true_and]
  rw [word_g1024, word_g10, word_g1023, word_gen, mul_inv_cancel₀ hne]
  refine ⟨rfl, ⟨l9, by rw [← pow_add]; congr 1; omega, l10⟩,
    ⟨l13, by rw [← pow_add]; congr 1; omega, l14⟩, ?_, by rw [← pow_add]; congr 1; omega,
    ⟨l20, by rw [← pow_add]; congr 1; omega, l21⟩, ?_, ⟨l28, by rw [← pow_add]; congr 1; omega,
      l29⟩, trivial⟩
  · rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hT lp (by omega)
  · rw [← pow_succ, ← pow_add, ← pow_add]; congr 1; omega


/-- **`da_row_shape`**, on the squares table. -/
theorem da_row_shape_iff {rd : Reader} (hm : MemOk rd) {gsq : E} (hT : SquaresAt rd gsq)
    (n_blob glp : E) (rets : List E) :
    coreProgram.Rel rd "da_row_shape" [n_blob, glp, gsq] rets ↔
      Meaning_da_row_shape [n_blob, glp, gsq] rets := by
  refine ⟨fun h => ?_, da_row_shape_complete hm.low16 hT _ _ _⟩
  rw [rel_of_find find_da_row_shape] at h
  simp only [Fn.Sem, drsBody, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, Meaning_da_row_shape] at h ⊢
  revert h
  rintro ⟨σ, hp, c3, a4, ⟨ne1, ne2⟩, c7, rc0, c11, rc1, m15, l16, m16, c18, rc17, c22, m23, c24,
    m25, m23', rc26, h30, h31, hr⟩
  simp only [List.cons.injEq, and_true] at hp
  obtain ⟨rfl, rfl, rfl⟩ := hp
  obtain ⟨r, e1, hr32, he1, h0, -, hk0⟩ := rangeCheck_sound hm rc0
  rw [c7, word_g1024] at hk0
  have hr1024 := gen_pow_inj' (by norm_num) (by omega) hk0
  obtain ⟨lp, e2, hlp32, he2, h1, -, hk1⟩ := rangeCheck_sound hm rc1
  rw [c11, word_g10] at hk1
  have hlp := gen_pow_inj' (by norm_num) (by omega) hk1
  have hr0 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [a4, c3, word_one, h0, h, pow_zero, e_add_self, zero_mul] at ne1
      rw [ne1] at ne2
      exact absurd ne2 zero_ne_one
    · exact h
  rw [m15, h1, loadHolds_mul_gen_pow, Nat.add_zero] at l16
  have h16 := loadHolds_unique l16 (hT lp (by omega))
  obtain ⟨a, e3, ha32, he3, h17, -, hk17⟩ := rangeCheck_sound hm rc17
  rw [c18, word_g1024] at hk17
  have ha := gen_pow_inj' (by norm_num) (by omega) hk17
  rw [h16, h17, h0, ← pow_add] at m16
  have hpow : 2 ^ lp < 2 ^ 11 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have e16 := gen_pow_inj' (by omega) (by omega) m16
  obtain ⟨b, e4, hb32, he4, h26, -, hk26⟩ := rangeCheck_sound hm rc26
  rw [c22, word_g1023] at hk26
  have hb := gen_pow_inj' (by norm_num) (by omega) hk26
  rw [m23, m25, c24, word_gen, h0, h16, h26, ← pow_add, ← pow_succ, ← pow_add] at m23'
  have e23 := gen_pow_inj' (by omega) (by omega) m23'
  have hlog := (logPad_iff (lp := lp) hr0).mpr ⟨by omega, by omega⟩
  refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 30), σ (.n 31), rfl, hr.symm, r, hr0,
    by unfold LeanDa.maxRows; omega, h0, by rw [h1, hlog], ?_, ?_⟩
  · rw [h30, h16, LeanDa.nPad, ← hlog]
  · rw [h31, h17, LeanDa.nPad, ← hlog]; congr 1; omega

end
end LeanVM.Guest.B1.Digest
