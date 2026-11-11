/-
  LeanVM.Guest.B1.Bits.Log2

  B1 for `log2_ceil_in_the_exponent`: the hinted `log2Ceil`, pinned by two small g-powers, at both
  floors the guest compiles.
-/

module

public import LeanVM.Guest.B1.Bits.SmallGPower

/-!
# `log2_ceil_in_the_exponent` (lean_ethereum.py:779-794 at leanVM `40f877dc`)

`log2_ceil_in_the_exponent(g_N, g_squares, floor, 34)` hints `N`'s bits into a fresh run (only
the hint reads them) and the log `g^L`, range checks `L < 34` and `L - floor < 34`, and asserts
`g^(2^L) / g_N` a small g-power (`assert_small_g_power`, an exponent below `2^36`); unless
`L = floor` also `g_N · g⁻¹ / g^(2^(L-1))`. It returns `g^L` (`MeaningLog2CeilExp`,
`log2_holds`). On `g_N = g^N`, `N < 2^60`, the two bounds are `N ≤ 2^L` and `2^(L-1) < N`, so
`L = max floor (log2Ceil N)` (`meaningLog2CeilExp_pow`, V:661).

The expansion is `lcBody floor` (`lcMin` the check above the floor), equal to both
specializations (`__L0_L34`, `__L16_L34`) by kernel evaluation.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `g⁻¹` -/

/-- `g⁻¹`, the guest's `INV_GEN`, as the data writes it. -/
abbrev invGenWord : E := word 9223372036854775821 0 0

/-- `INV_GEN` is `g⁻¹`. -/
theorem gen_mul_invGenWord : gen * invGenWord = 1 := by
  rw [show gen = ofK (K.ofBits 2) from rfl, show invGenWord = ofK (K.ofBits 9223372036854775821)
    from word_eOfNat _, ← ofK_mul, show K.ofBits 2 * K.ofBits 9223372036854775821 = 1 by
      decide +kernel, ofK_one]

theorem gen_pow_mul_invGen (L : ℕ) : gen ^ (L + 1) * invGenWord = gen ^ L := by
  rw [pow_succ, mul_assoc, gen_mul_invGenWord, mul_one]

/-! ## The template -/

/-- The check above the floor: `g_N · g⁻¹ / g_squares[g^(L-1)]` a small g-power. -/
def lcMin : List Stmt :=
  [.atom (.const (.n 20) invGenWord), .atom (.mul (.n 21) (.n 0) (.n 20)),
    .atom (.const (.n 22) invGenWord), .atom (.mul (.n 23) (.n 4) (.n 22)),
    .atom (.mul (.n 24) (.n 1) (.n 23)), .atom (.load (.n 25) (.n 24) 0),
    .atom (.mul (.n 21) (.n 26) (.n 25)), .call "assert_small_g_power" [.n 26, .n 1] []]

/-- The expansion of `log2_ceil_in_the_exponent` at the floor `fl`, 34 bits. -/
def lcBody (fl : ℕ) : List Stmt :=
  [.atom (.const (.n 2) (word (2 ^ 34) 0 0)), .atom (.hint (.allocDyn (.n 3) (.n 2))),
    .atom (.hint (.bitsExp (.n 0) 34 (.heap (.n 3) 0 34))),
    .atom (.hint (.log2Ceil (.heap (.n 3) 0 34) 34 fl (.n 4))),
    .atom (.const (.n 5) (word (2 ^ 33) 0 0)),
    .atom (.rangeCheck (.n 4) (.n 6) (.n 7) (.n 8) (.n 5)),
    .atom (.const (.n 9) (word (2 ^ 33) 0 0)), .atom (.const (.n 10) (word (2 ^ fl) 0 0)),
    .atom (.mul (.n 4) (.n 11) (.n 10)),
    .atom (.rangeCheck (.n 11) (.n 12) (.n 13) (.n 14) (.n 9)),
    .atom (.mul (.n 15) (.n 1) (.n 4)), .atom (.load (.n 16) (.n 15) 0),
    .atom (.mul (.n 16) (.n 17) (.n 0)), .call "assert_small_g_power" [.n 17, .n 1] [],
    .atom (.const (.n 18) (word (2 ^ fl) 0 0)), .atom (.add (.n 19) (.n 4) (.n 18)),
    .ite (.n 19) [] lcMin, .atom (.copy (.n 27) (.n 4)), .ret [.n 27]]

theorem core300_body : Fn.body Data.core308 = lcBody 0 := stmtsEqb_sound (by decide +kernel)

theorem core301_body : Fn.body Data.core309 = lcBody 16 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem find_lce_L0 : coreProgram.find? "log2_ceil_in_the_exponent__L0_L34" = some Data.core308 :=
  Program.find?_of_indexOf? (j := 308) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem find_lce_L16 :
    coreProgram.find? "log2_ceil_in_the_exponent__L16_L34" = some Data.core309 :=
  Program.find?_of_indexOf? (j := 309) (by decide +kernel) rfl

/-- The body, unfolded to its conditions. -/
theorem lc_unfold {name : String} {f : Fn} (fl : ℕ) (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1]) (hbody : f.body = lcBody fl) (rd : Reader)
    (args rets : List E) :
    coreProgram.Rel rd name args rets ↔ ∃ σ : Val, [σ (.n 0), σ (.n 1)] = args ∧
      σ (.n 2) = word (2 ^ 34) 0 0 ∧ σ (.n 5) = word (2 ^ 33) 0 0 ∧
      (LoadHolds rd (σ (.n 4)) 0 (σ (.n 7)) ∧ σ (.n 5) = σ (.n 4) * σ (.n 6) ∧
        LoadHolds rd (σ (.n 6)) 0 (σ (.n 8))) ∧
      σ (.n 9) = word (2 ^ 33) 0 0 ∧ σ (.n 10) = word (2 ^ fl) 0 0 ∧
      σ (.n 4) = σ (.n 11) * σ (.n 10) ∧
      (LoadHolds rd (σ (.n 11)) 0 (σ (.n 13)) ∧ σ (.n 9) = σ (.n 11) * σ (.n 12) ∧
        LoadHolds rd (σ (.n 12)) 0 (σ (.n 14))) ∧
      σ (.n 15) = σ (.n 1) * σ (.n 4) ∧ LoadHolds rd (σ (.n 15)) 0 (σ (.n 16)) ∧
      σ (.n 16) = σ (.n 17) * σ (.n 0) ∧
      coreProgram.Rel rd "assert_small_g_power" [σ (.n 17), σ (.n 1)] [] ∧
      σ (.n 18) = word (2 ^ fl) 0 0 ∧ σ (.n 19) = σ (.n 4) + σ (.n 18) ∧
      (IsInK (σ (.n 19)) ∧ (σ (.n 19) ≠ 0 →
        σ (.n 20) = invGenWord ∧ σ (.n 21) = σ (.n 0) * σ (.n 20) ∧ σ (.n 22) = invGenWord ∧
        σ (.n 23) = σ (.n 4) * σ (.n 22) ∧ σ (.n 24) = σ (.n 1) * σ (.n 23) ∧
        LoadHolds rd (σ (.n 24)) 0 (σ (.n 25)) ∧ σ (.n 21) = σ (.n 26) * σ (.n 25) ∧
        coreProgram.Rel rd "assert_small_g_power" [σ (.n 26), σ (.n 1)] [])) ∧
      σ (.n 27) = σ (.n 4) ∧ [σ (.n 27)] = rets := by
  rw [rel_iff_sem hfind, hbody, hparams, lcBody]
  simp only [Stmt.HoldsList]
  simp only [holds_ite_noRet (.n 19) [] lcMin rfl rfl]
  simp only [lcMin, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and,
    and_true, implies_true]

/-! ## The meaning on `g^N` -/

/-- **On `g_N = g^N`, the meaning is `max floor (log2Ceil N)`** (V:661), for `N < 2^60` (any
count the guest sums: below the order of `g` with room for the small exponents). -/
theorem meaningLog2CeilExp_pow {fl N : ℕ} (hfl : fl < 34) (hN : N < 2 ^ 60) (q : E)
    (rets : List E) :
    MeaningLog2CeilExp fl [gen ^ N, q] rets ↔
      max fl (log2Ceil N) < 34 ∧ rets = [gen ^ max fl (log2Ceil N)] := by
  simp only [MeaningLog2CeilExp]
  constructor
  · rintro ⟨L, hfL, hL, ⟨e, he, h1⟩, h2, rfl⟩
    rw [← pow_add] at h1
    have hNL : 2 ^ L = N + e := gen_pow_inj (lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) hL)
      (by decide)) (by omega) h1
    have hmax : L = max fl (log2Ceil N) := by
      refine log2Ceil_certified hfL (by omega) fun hne ↦ ?_
      obtain ⟨e', he', h'⟩ := h2 hne
      have h2L : 2 ^ (L - 1) < 2 ^ 34 := Nat.pow_lt_pow_right (by decide) (by omega)
      have := gen_pow_inj (by omega) (by omega) h'
      omega
    exact ⟨hmax ▸ hL, by rw [← hmax]⟩
  · rintro ⟨hL, rfl⟩
    set L := max fl (log2Ceil N) with hLdef
    have hle : N ≤ 2 ^ L := log2Ceil_le_iff.mp (le_max_right _ _)
    have h2L : 2 ^ L < 2 ^ 34 := Nat.pow_lt_pow_right (by decide) hL
    refine ⟨L, le_max_left _ _, hL, ⟨2 ^ L - N, by omega, ?_⟩, fun hne ↦ ?_, rfl⟩
    · rw [← pow_add]; congr 1; omega
    · have hlt : L - 1 < log2Ceil N := by
        have : L = log2Ceil N := by
          rcases max_choice fl (log2Ceil N) with h | h
          · exact absurd h.symm (by rw [← hLdef] at h; exact fun _ ↦ hne h)
          · rw [← hLdef] at h; exact h
        omega
      have hlow : 2 ^ (L - 1) < N := lt_log2Ceil_iff.mp hlt
      have h33 : N ≤ 2 ^ 33 := le_trans hle (Nat.pow_le_pow_right (by decide) (by omega))
      exact ⟨N - (2 ^ (L - 1) + 1), lt_of_le_of_lt (Nat.sub_le _ _) (by omega),
        by congr 1; omega⟩

/-! ## Soundness and completeness -/

/-- A range check against `g^33`, on a memory of `2^κ ≥ 34` words. -/
theorem rangeCheck34_iff {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemoryImage κ) (x : E) :
    (∃ y t1 t2 : E, LoadHolds Lm.read x 0 t1 ∧ word (2 ^ 33) 0 0 = x * y ∧
      LoadHolds Lm.read y 0 t2) ↔ ∃ e < 34, x = gen ^ e :=
  rangeCheck_gen_iff hκ Lm x (K := 34) (by decide)
    (le_trans (by decide) (Nat.pow_le_pow_right (by decide) hκ6)) (by decide)

/-- The square `g^(2^L)` read at `q·g^L`, `L < 34`. -/
theorem lc_square {rd : Reader} {q s : E} (ht : ExpTables rd q) {L : ℕ} (hL : L < 34)
    (h : LoadHolds rd (q * gen ^ L) 0 s) : s = gen ^ 2 ^ L := by
  rw [loadHolds_mul_gen_pow, Nat.add_zero] at h
  exact loadHolds_unique h (ht.1 L hL)

theorem log2_iff {name : String} {f : Fn} (fl : ℕ) (hfl : fl < 34)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1])
    (hbody : f.body = lcBody fl) {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemoryImage κ)
    {gN q : E} (ht : ExpTables Lm.read q) (rets : List E) :
    coreProgram.Rel Lm.read name [gN, q] rets ↔ MeaningLog2CeilExp fl [gN, q] rets := by
  have hsmall := fun x ↦ assert_small_g_power_holds hκ hκ6 Lm x q ht []
  have wfl : word (2 ^ fl) 0 0 = gen ^ fl := word_two_pow (by omega)
  rw [lc_unfold fl hfind hparams hbody]
  constructor
  · rintro ⟨σ, hp, -, h5, r1, h9, h10, m4, r2, h15, l16, m16, c17, h18, h19, ⟨-, hmin⟩, h27,
      hret⟩
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨rfl, rfl⟩ := hp
    obtain ⟨L, hL, hxL⟩ := (rangeCheck34_iff hκ hκ6 Lm _).1
      ⟨_, _, _, r1.1, by rw [← h5]; exact r1.2.1, r1.2.2⟩
    obtain ⟨c, hc, hxc⟩ := (rangeCheck34_iff hκ hκ6 Lm _).1
      ⟨_, _, _, r2.1, by rw [← h9]; exact r2.2.1, r2.2.2⟩
    have hLc : L = c + fl := by
      rw [hxL, hxc, h10, wfl, ← pow_add] at m4
      exact gen_pow_inj (by omega) (by omega) m4
    obtain ⟨⟨e, he, h17⟩, -⟩ := ((hsmall _).1 c17)
    rw [h15, hxL] at l16
    have hs := lc_square ht hL l16
    refine ⟨L, by omega, hL, ⟨e, he, ?_⟩, fun hne ↦ ?_, ?_⟩
    · rw [← hs, m16, h17, mul_comm]
    · have h19' : σ (.n 19) ≠ 0 := by
        rw [h19, h18, hxL, wfl]
        intro h0
        exact hne (gen_pow_inj (by omega) (by omega) (e_add_eq_zero_iff.mp h0))
      obtain ⟨h20, h21, h22, h23, h24, l25, m21, c26⟩ := hmin h19'
      obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
      rw [h24, h23, h22, hxL, gen_pow_mul_invGen] at l25
      have hs' := lc_square ht (by omega) l25
      obtain ⟨⟨e', he', h26⟩, -⟩ := ((hsmall _).1 c26)
      refine ⟨e', he', ?_⟩
      have key : σ (.n 0) * invGenWord * gen = gen ^ e' * gen ^ 2 ^ L' * gen := by
        rw [← h20, ← h21, m21, h26, hs']
      rw [mul_assoc, mul_comm invGenWord, gen_mul_invGenWord, mul_one] at key
      rw [key, ← pow_add, ← pow_succ, Nat.add_sub_cancel]
      congr 1
      omega
    · rw [← hret, h27, hxL]
  · rintro ⟨L, hfL, hL, ⟨e, he, h1⟩, h2, rfl⟩
    obtain ⟨y1, t1, t2, r1⟩ := (rangeCheck34_iff hκ hκ6 Lm (gen ^ L)).2 ⟨L, hL, rfl⟩
    obtain ⟨y2, u1, u2, r2⟩ := (rangeCheck34_iff hκ hκ6 Lm (gen ^ (L - fl))).2
      ⟨L - fl, by omega, rfl⟩
    have hsq : LoadHolds Lm.read (q * gen ^ L) 0 (gen ^ 2 ^ L) := by
      rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact ht.1 L hL
    -- the check above the floor, when it runs
    have hmin : L ≠ fl → ∃ e' : ℕ, e' < 2 ^ 36 ∧ gN * invGenWord = gen ^ e' * gen ^ 2 ^ (L - 1) ∧
        LoadHolds Lm.read (q * (gen ^ L * invGenWord)) 0 (gen ^ 2 ^ (L - 1)) := fun hne ↦ by
      obtain ⟨e', he', h'⟩ := h2 hne
      obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
      refine ⟨e', he', ?_, ?_⟩
      · rw [h', Nat.add_sub_cancel, show 2 ^ L' + 1 + e' = (e' + 2 ^ L') + 1 by omega,
          gen_pow_mul_invGen, pow_add]
      · rw [gen_pow_mul_invGen, loadHolds_mul_gen_pow, Nat.add_zero, Nat.add_sub_cancel]
        exact ht.1 L' (show L' < 34 by omega)
    obtain ⟨e', hm'⟩ : ∃ e' : ℕ, L ≠ fl → e' < 2 ^ 36 ∧
        gN * invGenWord = gen ^ e' * gen ^ 2 ^ (L - 1) ∧
        LoadHolds Lm.read (q * (gen ^ L * invGenWord)) 0 (gen ^ 2 ^ (L - 1)) := by
      by_cases hne : L = fl
      · exact ⟨0, fun h ↦ absurd hne h⟩
      · obtain ⟨e', h⟩ := hmin hne
        exact ⟨e', fun _ ↦ h⟩
    let w : ℕ → E := fun i ↦ [gN, q, word (2 ^ 34) 0 0, 0, gen ^ L, word (2 ^ 33) 0 0, y1, t1, t2,
      word (2 ^ 33) 0 0, word (2 ^ fl) 0 0, gen ^ (L - fl), y2, u1, u2, q * gen ^ L,
      gen ^ 2 ^ L, gen ^ e, word (2 ^ fl) 0 0, gen ^ L + word (2 ^ fl) 0 0, invGenWord,
      gN * invGenWord, invGenWord, gen ^ L * invGenWord, q * (gen ^ L * invGenWord),
      gen ^ 2 ^ (L - 1), gen ^ e', gen ^ L].getD i 0
    refine ⟨fun v ↦ w v.idx, rfl, rfl, rfl, r1, rfl, rfl, ?_, r2, rfl, hsq, ?_, ?_, rfl, rfl,
      ⟨?_, fun h0 ↦ ?_⟩, rfl, rfl⟩
    · show gen ^ L = gen ^ (L - fl) * word (2 ^ fl) 0 0
      rw [wfl, ← pow_add, Nat.sub_add_cancel hfL]
    · show gen ^ 2 ^ L = gen ^ e * gN
      rw [h1, mul_comm]
    · exact (hsmall _).2 ⟨⟨e, he, rfl⟩, rfl⟩
    · show IsInK (gen ^ L + word (2 ^ fl) 0 0)
      rw [wfl, gen_pow_eq_ofK, gen_pow_eq_ofK, ← ofK_add]
      exact ofK_isInK _
    · have hne : L ≠ fl := fun h ↦ h0 (by
        show gen ^ L + word (2 ^ fl) 0 0 = 0
        rw [wfl, h]; exact e_add_self _)
      obtain ⟨he', hm, hl⟩ := hm' hne
      exact ⟨rfl, rfl, rfl, rfl, rfl, hl, hm, (hsmall _).2 ⟨⟨_, he', rfl⟩, rfl⟩⟩

/-- **`log2_ceil_in_the_exponent`'s core IR is its meaning**, at both floors. -/
theorem log2_holds : log2_Spec :=
  ⟨fun hκ hκ6 Lm _ _ ht rets => log2_iff 0 (by decide) find_lce_L0 rfl core300_body hκ hκ6 Lm ht rets,
    fun hκ hκ6 Lm _ _ ht rets =>
      log2_iff 16 (by decide) find_lce_L16 rfl core301_body hκ hκ6 Lm ht rets⟩

end
end LeanVM.Guest.B1
