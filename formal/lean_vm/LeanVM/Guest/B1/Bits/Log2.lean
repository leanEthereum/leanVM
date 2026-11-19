/-
  LeanVM.Guest.B1.Bits.Log2

  B1 for `log2_ceil_in_the_exponent`: the hinted `log2Ceil`, pinned by two small g-powers, at both
  floors the guest compiles.
-/

module

public import LeanVM.Guest.B1.Bits.SmallGPower

/-!
# `log2_ceil_in_the_exponent` (lean_ethereum.py)

`log2_ceil_in_the_exponent(g_N, g_squares, floor, 34)` hints `N`'s bits into a run of its frame
(only the hint reads them) and the log `g^L`, range checks `L < 34` and `L - floor < 34`, and asserts
`g^(2^L) / g_N` a small g-power (`assert_small_g_power`, an exponent below `2^36`); unless
`L = floor` also `g_N · g⁻¹ / g^(2^(L-1))`. It returns `g^L` (`MeaningLog2CeilExp`,
`log2_holds`). On `g_N = g^N`, `N < 2^60`, the two bounds are `N ≤ 2^L` and `2^(L-1) < N`, so
`L = max floor (log2Ceil N)` (`meaningLog2CeilExp_pow`).

The expansion is `lcBody floor` (`lcMin` the check above the floor), equal to both
specializations (`__L0_L34`, `__L16_L34`) by kernel evaluation.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `g⁻¹` -/

/-- `g⁻¹`, the guest's `INV_GEN`, as the data writes it. -/
abbrev invGenWord : E := word 9223372036854775821 0

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
  [.atom (.const (.n 52) invGenWord), .atom (.mul (.n 53) (.n 0) (.n 52)),
    .atom (.const (.n 54) invGenWord), .atom (.mul (.n 55) (.n 36) (.n 54)),
    .atom (.mul (.n 56) (.n 1) (.n 55)), .atom (.load (.n 57) (.n 56) 0),
    .atom (.mul (.n 53) (.n 58) (.n 57)), .call "assert_small_g_power" [.n 58, .n 1] []]

/-- The expansion of `log2_ceil_in_the_exponent` at the floor `fl`, 34 bits. -/
def lcBody (fl : ℕ) : List Stmt :=
  [.atom (.hint (.bitsExp (.n 0) 34 (.stack ((List.range 34).map fun k => .n (2 + k))))),
    .atom (.hint (.log2Ceil (.stack ((List.range 34).map fun k => .n (2 + k))) 34 fl (.n 36))),
    .atom (.const (.n 37) (word (2 ^ 33) 0)),
    .atom (.rangeCheck (.n 36) (.n 38) (.n 39) (.n 40) (.n 37)),
    .atom (.const (.n 41) (word (2 ^ 33) 0)), .atom (.const (.n 42) (word (2 ^ fl) 0)),
    .atom (.mul (.n 36) (.n 43) (.n 42)),
    .atom (.rangeCheck (.n 43) (.n 44) (.n 45) (.n 46) (.n 41)),
    .atom (.mul (.n 47) (.n 1) (.n 36)), .atom (.load (.n 48) (.n 47) 0),
    .atom (.mul (.n 48) (.n 49) (.n 0)), .call "assert_small_g_power" [.n 49, .n 1] [],
    .atom (.const (.n 50) (word (2 ^ fl) 0)), .atom (.add (.n 51) (.n 36) (.n 50)),
    .ite (.n 51) [] lcMin, .atom (.copy (.n 59) (.n 36)), .ret [.n 59]]

theorem log2_ceil_in_the_exponent_L0_L34_body : Fn.body fn% «log2_ceil_in_the_exponent__L0_L34» =
    lcBody 0 := stmtsEqb_sound (by decide +kernel)

theorem log2_ceil_in_the_exponent_L16_L34_body : Fn.body fn% «log2_ceil_in_the_exponent__L16_L34» =
    lcBody 16 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem find_lce_L0 : coreProgram.find? "log2_ceil_in_the_exponent__L0_L34" = some
    fn% «log2_ceil_in_the_exponent__L0_L34» :=
  coreProgram_find?_at (j := idx% «log2_ceil_in_the_exponent__L0_L34») rfl

set_option maxRecDepth 100000 in
theorem find_lce_L16 :
    coreProgram.find? "log2_ceil_in_the_exponent__L16_L34" = some
        fn% «log2_ceil_in_the_exponent__L16_L34» :=
  coreProgram_find?_at (j := idx% «log2_ceil_in_the_exponent__L16_L34») rfl

/-- The body, unfolded to its conditions. -/
theorem lc_unfold {name : String} {f : Fn} (fl : ℕ) (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1]) (hbody : f.body = lcBody fl) (rd : Reader)
    (args rets : List E) :
    coreProgram.Rel rd name args rets ↔ ∃ σ : Val, [σ (.n 0), σ (.n 1)] = args ∧
      σ (.n 37) = word (2 ^ 33) 0 ∧
      (LoadHolds rd (σ (.n 36)) 0 (σ (.n 39)) ∧ σ (.n 37) = σ (.n 36) * σ (.n 38) ∧
        LoadHolds rd (σ (.n 38)) 0 (σ (.n 40))) ∧
      σ (.n 41) = word (2 ^ 33) 0 ∧ σ (.n 42) = word (2 ^ fl) 0 ∧
      σ (.n 36) = σ (.n 43) * σ (.n 42) ∧
      (LoadHolds rd (σ (.n 43)) 0 (σ (.n 45)) ∧ σ (.n 41) = σ (.n 43) * σ (.n 44) ∧
        LoadHolds rd (σ (.n 44)) 0 (σ (.n 46))) ∧
      σ (.n 47) = σ (.n 1) * σ (.n 36) ∧ LoadHolds rd (σ (.n 47)) 0 (σ (.n 48)) ∧
      σ (.n 48) = σ (.n 49) * σ (.n 0) ∧
      coreProgram.Rel rd "assert_small_g_power" [σ (.n 49), σ (.n 1)] [] ∧
      σ (.n 50) = word (2 ^ fl) 0 ∧ σ (.n 51) = σ (.n 36) + σ (.n 50) ∧
      (IsInK (σ (.n 51)) ∧ (σ (.n 51) ≠ 0 →
        σ (.n 52) = invGenWord ∧ σ (.n 53) = σ (.n 0) * σ (.n 52) ∧ σ (.n 54) = invGenWord ∧
        σ (.n 55) = σ (.n 36) * σ (.n 54) ∧ σ (.n 56) = σ (.n 1) * σ (.n 55) ∧
        LoadHolds rd (σ (.n 56)) 0 (σ (.n 57)) ∧ σ (.n 53) = σ (.n 58) * σ (.n 57) ∧
        coreProgram.Rel rd "assert_small_g_power" [σ (.n 58), σ (.n 1)] [])) ∧
      σ (.n 59) = σ (.n 36) ∧ [σ (.n 59)] = rets := by
  rw [rel_iff_sem hfind, hbody, hparams, lcBody]
  simp only [Stmt.HoldsList]
  simp only [holds_ite_noRet (.n 51) [] lcMin rfl rfl]
  simp only [lcMin, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and,
    and_true, implies_true]

/-! ## The meaning on `g^N` -/

/-- **On `g_N = g^N`, the meaning is `max floor (log2Ceil N)`**, for `N < 2^60` (any
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
    (∃ y t1 t2 : E, LoadHolds Lm.read x 0 t1 ∧ word (2 ^ 33) 0 = x * y ∧
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
  have wfl : word (2 ^ fl) 0 = gen ^ fl := word_two_pow (by omega)
  rw [lc_unfold fl hfind hparams hbody]
  constructor
  · rintro ⟨σ, hp, h5, r1, h9, h10, m4, r2, h15, l16, m16, c17, h18, h19, ⟨-, hmin⟩, h27,
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
    · have h19' : σ (.n 51) ≠ 0 := by
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
    let w : ℕ → E := fun i ↦ ([gN, q] ++ List.replicate 34 0 ++ [gen ^ L, word (2 ^ 33) 0, y1, t1, t2,
      word (2 ^ 33) 0, word (2 ^ fl) 0, gen ^ (L - fl), y2, u1, u2, q * gen ^ L,
      gen ^ 2 ^ L, gen ^ e, word (2 ^ fl) 0, gen ^ L + word (2 ^ fl) 0, invGenWord,
      gN * invGenWord, invGenWord, gen ^ L * invGenWord, q * (gen ^ L * invGenWord),
      gen ^ 2 ^ (L - 1), gen ^ e', gen ^ L]).getD i 0
    refine ⟨fun v ↦ w v.idx, rfl, rfl, r1, rfl, rfl, ?_, r2, rfl, hsq, ?_, ?_, rfl, rfl,
      ⟨?_, fun h0 ↦ ?_⟩, rfl, rfl⟩
    · show gen ^ L = gen ^ (L - fl) * word (2 ^ fl) 0
      rw [wfl, ← pow_add, Nat.sub_add_cancel hfL]
    · show gen ^ 2 ^ L = gen ^ e * gN
      rw [h1, mul_comm]
    · exact (hsmall _).2 ⟨⟨e, he, rfl⟩, rfl⟩
    · show IsInK (gen ^ L + word (2 ^ fl) 0)
      rw [wfl, gen_pow_eq_ofK, gen_pow_eq_ofK, ← ofK_add]
      exact ofK_isInK _
    · have hne : L ≠ fl := fun h ↦ h0 (by
        show gen ^ L + word (2 ^ fl) 0 = 0
        rw [wfl, h]; exact e_add_self _)
      obtain ⟨he', hm, hl⟩ := hm' hne
      exact ⟨rfl, rfl, rfl, rfl, rfl, hl, hm, (hsmall _).2 ⟨⟨_, he', rfl⟩, rfl⟩⟩

/-- **`log2_ceil_in_the_exponent`'s core IR is its meaning**, at both floors. -/
theorem log2_holds : log2_Spec :=
  ⟨fun hκ hκ6 Lm _ _ ht rets => log2_iff 0 (by decide) find_lce_L0 rfl
      log2_ceil_in_the_exponent_L0_L34_body hκ hκ6 Lm ht rets,
    fun hκ hκ6 Lm _ _ ht rets =>
      log2_iff 16 (by decide) find_lce_L16 rfl log2_ceil_in_the_exponent_L16_L34_body hκ hκ6 Lm ht
          rets⟩

end
end LeanVM.Guest.B1
