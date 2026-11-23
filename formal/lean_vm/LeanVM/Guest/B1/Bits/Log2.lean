/-
  LeanVM.Guest.B1.Bits.Log2

  B1 for `log2_ceil_in_the_exponent`: the hinted `log2Ceil`, pinned by two small g-powers, at both
  floors the guest compiles.
-/

module

public import LeanVM.Guest.B1.Bits.SmallGPower
import LeanVM.Guest.B1.Common.Vc

/-!
# `log2_ceil_in_the_exponent` (lean_ethereum.py)

`log2_ceil_in_the_exponent(g_N, g_squares, floor, 34)` hints `N`'s bits into a run of its frame
(only the hint reads them) and the log `g^L`, range checks `L < 34` and `L - floor < 34`, and asserts
`g^(2^L) / g_N` a small g-power (`assert_small_g_power`, an exponent below `2^36`); unless
`L = floor` also `g_N · g⁻¹ / g^(2^(L-1))`. It returns `g^L` (`MeaningLog2CeilExp`,
`log2_holds`). On `g_N = g^N`, `N < 2^60`, the two bounds are `N ≤ 2^L` and `2^(L-1) < N`, so
`L = max floor (log2Ceil N)` (`meaningLog2CeilExp_pow`).

Each specialization (`__L0_L34`, `__L16_L34`) is its forward condition `LcCond floor` by `vc`
(`lc_L0_iff`, `lc_L16_iff`), which `lc_iff` takes to the meaning. The expansion as a template
(`lcBody`), which the placed run walks, is in `Log2Placed.lean`.
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

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem find_lce_L0 : coreProgram.find? "log2_ceil_in_the_exponent__L0_L34" = some
    fn% «log2_ceil_in_the_exponent__L0_L34» :=
  coreProgram_find?_at (j := idx% «log2_ceil_in_the_exponent__L0_L34») rfl

set_option maxRecDepth 100000 in
theorem find_lce_L16 :
    coreProgram.find? "log2_ceil_in_the_exponent__L16_L34" = some
        fn% «log2_ceil_in_the_exponent__L16_L34» :=
  coreProgram_find?_at (j := idx% «log2_ceil_in_the_exponent__L16_L34») rfl

/-- The condition `vc` computes of `log2_ceil_in_the_exponent` at the floor `fl`, on `[gN, q]`:
the log `gL` and `gL / g^fl` range checked (`word (2^33) = x·y`), the square read at `q·gL` a small
g-power times `gN`, and above the floor the square at `q·gL·g⁻¹` one times `gN·g⁻¹`. -/
def LcCond (fl : ℕ) (rd : Reader) (gN q : E) (rets : List E) : Prop :=
  ∃ gL y1 t1, LoadHolds rd gL 0 t1 ∧ word (2 ^ 33) 0 = gL * y1 ∧
    ∃ t2, LoadHolds rd y1 0 t2 ∧ ∃ gc, gL = gc * word (2 ^ fl) 0 ∧
      ∃ y2 u1, LoadHolds rd gc 0 u1 ∧ word (2 ^ 33) 0 = gc * y2 ∧
        ∃ u2, LoadHolds rd y2 0 u2 ∧ ∃ s, LoadHolds rd (q * gL) 0 s ∧
          ∃ e, s = e * gN ∧ coreProgram.Rel rd "assert_small_g_power" [e, q] [] ∧
            IsInK (gL + word (2 ^ fl) 0) ∧ (gL + word (2 ^ fl) 0 = 0 → [gL] = rets) ∧
            (gL + word (2 ^ fl) 0 ≠ 0 → ∃ s', LoadHolds rd (q * (gL * invGenWord)) 0 s' ∧
              ∃ e', gN * invGenWord = e' * s' ∧
                coreProgram.Rel rd "assert_small_g_power" [e', q] [] ∧ [gL] = rets)

theorem lc_L0_iff (rd : Reader) (gN q : E) (rets : List E) :
    coreProgram.Rel rd "log2_ceil_in_the_exponent__L0_L34" [gN, q] rets ↔ LcCond 0 rd gN q rets := by
  rw [rel_iff_fnSem find_lce_L0]
  vc
  exact Iff.rfl

theorem lc_L16_iff (rd : Reader) (gN q : E) (rets : List E) :
    coreProgram.Rel rd "log2_ceil_in_the_exponent__L16_L34" [gN, q] rets ↔ LcCond 16 rd gN q rets := by
  rw [rel_iff_fnSem find_lce_L16]
  vc
  exact Iff.rfl

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

theorem lc_iff (fl : ℕ) (hfl : fl < 34) {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemoryImage κ)
    {gN q : E} (ht : ExpTables Lm.read q) (rets : List E) :
    LcCond fl Lm.read gN q rets ↔ MeaningLog2CeilExp fl [gN, q] rets := by
  have hsmall := fun x ↦ assert_small_g_power_holds hκ hκ6 Lm x q ht []
  have wfl : word (2 ^ fl) 0 = gen ^ fl := word_two_pow (by omega)
  constructor
  · rintro ⟨gL, y1, t1, l1, r1, t2, l2, gc, m4, y2, u1, l3, r2, u2, l4, s, ls, e, ms, ce, -, h0,
      hmin⟩
    obtain ⟨L, hL, rfl⟩ := (rangeCheck34_iff hκ hκ6 Lm _).1 ⟨y1, t1, t2, l1, r1, l2⟩
    obtain ⟨c, hc, rfl⟩ := (rangeCheck34_iff hκ hκ6 Lm _).1 ⟨y2, u1, u2, l3, r2, l4⟩
    have hLc : L = c + fl := by
      rw [wfl, ← pow_add] at m4
      exact gen_pow_inj (by omega) (by omega) m4
    obtain ⟨⟨e1, he, h17⟩, -⟩ := (hsmall _).1 ce
    have hs := lc_square ht hL ls
    have hret : [gen ^ L] = rets := by
      by_cases h : gen ^ L + word (2 ^ fl) 0 = 0
      · exact h0 h
      · obtain ⟨_, _, _, _, _, h⟩ := hmin h
        exact h
    refine ⟨L, by omega, hL, ⟨e1, he, ?_⟩, fun hne ↦ ?_, hret.symm⟩
    · rw [← hs, ms, h17, mul_comm]
    · have hne' : gen ^ L + word (2 ^ fl) 0 ≠ 0 := by
        rw [wfl]
        intro h0
        exact hne (gen_pow_inj (by omega) (by omega) (e_add_eq_zero_iff.mp h0))
      obtain ⟨s', l25, e2, m21, c26, -⟩ := hmin hne'
      obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
      rw [gen_pow_mul_invGen] at l25
      have hs' := lc_square ht (by omega) l25
      obtain ⟨⟨e', he', h26⟩, -⟩ := (hsmall _).1 c26
      refine ⟨e', he', ?_⟩
      have key : gN * invGenWord * gen = gen ^ e' * gen ^ 2 ^ L' * gen := by rw [m21, h26, hs']
      rw [mul_assoc, mul_comm invGenWord, gen_mul_invGenWord, mul_one] at key
      rw [key, ← pow_add, ← pow_succ, Nat.add_sub_cancel]
      congr 1
      omega
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
    refine ⟨gen ^ L, y1, t1, r1.1, r1.2.1, t2, r1.2.2, gen ^ (L - fl), ?_, y2, u1, r2.1, r2.2.1, u2,
      r2.2.2, gen ^ 2 ^ L, hsq, gen ^ e, ?_, (hsmall _).2 ⟨⟨e, he, rfl⟩, rfl⟩, ?_, fun _ ↦ rfl,
      fun h0 ↦ ?_⟩
    · rw [wfl, ← pow_add, Nat.sub_add_cancel hfL]
    · rw [h1, mul_comm]
    · rw [wfl, gen_pow_eq_ofK, gen_pow_eq_ofK, ← ofK_add]
      exact ofK_isInK _
    · have hne : L ≠ fl := fun h ↦ h0 (by rw [wfl, h]; exact e_add_self _)
      obtain ⟨e', he', hm, hl⟩ := hmin hne
      exact ⟨_, hl, _, hm, (hsmall _).2 ⟨⟨_, he', rfl⟩, rfl⟩, rfl⟩

/-- **`log2_ceil_in_the_exponent`'s core IR is its meaning**, at both floors. -/
theorem log2_holds : log2_Spec :=
  ⟨fun hκ hκ6 Lm _ _ ht rets => (lc_L0_iff _ _ _ rets).trans (lc_iff 0 (by decide) hκ hκ6 Lm ht rets),
    fun hκ hκ6 Lm _ _ ht rets =>
      (lc_L16_iff _ _ _ rets).trans (lc_iff 16 (by decide) hκ hκ6 Lm ht rets)⟩

end
end LeanVM.Guest.B1
