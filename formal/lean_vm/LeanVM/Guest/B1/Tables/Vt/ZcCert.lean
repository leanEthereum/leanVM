/-
  LeanVM.Guest.B1.Tables.Vt.ZcCert

  `verify_tables`' table sumcheck's round count: the hinted `g^n` is `g^(max τ_t)`, below the bus
  point's length.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Fresh
public import LeanVM.Guest.B1.Tables.Vt.Sort
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# The table sumcheck's rounds

`g_zc_n` is hinted; every `τ_t` is at most `n` (a range-checked quotient), some `τ_t` is `n` (the
product of `g^n + g^τ_t` is zero), and `n ≤ μ` (`vt_zc_n`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `g^32`, as the data writes it. -/
abbrev vtW32 : E := word 4294967296 0

theorem vtW32_eq : vtW32 = ofK (Parameters.addressOfIndex 32) := by
  rw [vtW32, show (4294967296 : ℕ) = 2 ^ 32 by norm_num, tb_word_two_pow (by norm_num),
    gen_pow_eq_ofK]

section
variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ)
include hμ

/-- **The round count.** -/
theorem vt_zc_n {σ : Val} (h : VtH Lm.read σ) {τ : ℕ → ℕ} (hτ : ∀ t < 6, τ t < 33)
    (hkbt : ∀ t < 6, σ (.n ((val% «verify_tables» "kb[2]") + t)) = gen ^ τ t) {m : ℕ} (hm : m < 33)
    (hmu : σ (.n (val% «verify_tables» "g_bus_mu")) = gen ^ m) :
    ∃ n, σ (.n (val% «verify_tables» "g_zc_n")) = gen ^ n ∧ (∀ t < 6, τ t ≤ n) ∧ (∃ t < 6, τ t = n) ∧ n ≤ m := by
  have a5154 := h.atomAt 2287 (.const (.n (val% «verify_tables» "s57.u0.s1#0")) (word 4294967296 0)) (by decide +kernel)
  have a5155 := h.atomAt 2288 (.mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "s57.u0.s1#1")) (.n (val% «verify_tables» "kb[2]"))) (by decide +kernel)
  have a5156 := h.atomAt 2289 (.rangeCheck (.n (val% «verify_tables» "s57.u0.s1#1")) (.n (val% «verify_tables» "s57.u0.s1#2")) (.n (val% «verify_tables» "s57.u0.s1#3")) (.n (val% «verify_tables» "s57.u0.s1#4")) (.n (val% «verify_tables» "s57.u0.s1#0"))) (by decide +kernel)
  have a5157 := h.atomAt 2290 (.add (.n (val% «verify_tables» "zc_is_a_tau@1")) (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "kb[2]"))) (by decide +kernel)
  have a5159 := h.atomAt 2291 (.const (.n (val% «verify_tables» "s57.u1.s1#0")) (word 4294967296 0)) (by decide +kernel)
  have a5160 := h.atomAt 2292 (.mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "s57.u1.s1#1")) (.n (val% «verify_tables» "kb[3]"))) (by decide +kernel)
  have a5161 := h.atomAt 2293 (.rangeCheck (.n (val% «verify_tables» "s57.u1.s1#1")) (.n (val% «verify_tables» "s57.u1.s1#2")) (.n (val% «verify_tables» "s57.u1.s1#3")) (.n (val% «verify_tables» "s57.u1.s1#4")) (.n (val% «verify_tables» "s57.u1.s1#0"))) (by decide +kernel)
  have a5162 := h.atomAt 2294 (.add (.n (val% «verify_tables» "zc_is_a_tau@2~0")) (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "kb[3]"))) (by decide +kernel)
  have a5163 := h.atomAt 2295 (.mul (.n (val% «verify_tables» "zc_is_a_tau@2")) (.n (val% «verify_tables» "zc_is_a_tau@1")) (.n (val% «verify_tables» "zc_is_a_tau@2~0"))) (by decide +kernel)
  have a5165 := h.atomAt 2296 (.const (.n (val% «verify_tables» "s57.u2.s1#0")) (word 4294967296 0)) (by decide +kernel)
  have a5166 := h.atomAt 2297 (.mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "s57.u2.s1#1")) (.n (val% «verify_tables» "kb[4]"))) (by decide +kernel)
  have a5167 := h.atomAt 2298 (.rangeCheck (.n (val% «verify_tables» "s57.u2.s1#1")) (.n (val% «verify_tables» "s57.u2.s1#2")) (.n (val% «verify_tables» "s57.u2.s1#3")) (.n (val% «verify_tables» "s57.u2.s1#4")) (.n (val% «verify_tables» "s57.u2.s1#0"))) (by decide +kernel)
  have a5168 := h.atomAt 2299 (.add (.n (val% «verify_tables» "zc_is_a_tau@3~0")) (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "kb[4]"))) (by decide +kernel)
  have a5169 := h.atomAt 2300 (.mul (.n (val% «verify_tables» "zc_is_a_tau@3")) (.n (val% «verify_tables» "zc_is_a_tau@2")) (.n (val% «verify_tables» "zc_is_a_tau@3~0"))) (by decide +kernel)
  have a5171 := h.atomAt 2301 (.const (.n (val% «verify_tables» "s57.u3.s1#0")) (word 4294967296 0)) (by decide +kernel)
  have a5172 := h.atomAt 2302 (.mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "s57.u3.s1#1")) (.n (val% «verify_tables» "kb[5]"))) (by decide +kernel)
  have a5173 := h.atomAt 2303 (.rangeCheck (.n (val% «verify_tables» "s57.u3.s1#1")) (.n (val% «verify_tables» "s57.u3.s1#2")) (.n (val% «verify_tables» "s57.u3.s1#3")) (.n (val% «verify_tables» "s57.u3.s1#4")) (.n (val% «verify_tables» "s57.u3.s1#0"))) (by decide +kernel)
  have a5174 := h.atomAt 2304 (.add (.n (val% «verify_tables» "zc_is_a_tau@4~0")) (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "kb[5]"))) (by decide +kernel)
  have a5175 := h.atomAt 2305 (.mul (.n (val% «verify_tables» "zc_is_a_tau@4")) (.n (val% «verify_tables» "zc_is_a_tau@3")) (.n (val% «verify_tables» "zc_is_a_tau@4~0"))) (by decide +kernel)
  have a5177 := h.atomAt 2306 (.const (.n (val% «verify_tables» "s57.u4.s1#0")) (word 4294967296 0)) (by decide +kernel)
  have a5178 := h.atomAt 2307 (.mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "s57.u4.s1#1")) (.n (val% «verify_tables» "kb[6]"))) (by decide +kernel)
  have a5179 := h.atomAt 2308 (.rangeCheck (.n (val% «verify_tables» "s57.u4.s1#1")) (.n (val% «verify_tables» "s57.u4.s1#2")) (.n (val% «verify_tables» "s57.u4.s1#3")) (.n (val% «verify_tables» "s57.u4.s1#4")) (.n (val% «verify_tables» "s57.u4.s1#0"))) (by decide +kernel)
  have a5180 := h.atomAt 2309 (.add (.n (val% «verify_tables» "zc_is_a_tau@5~0")) (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "kb[6]"))) (by decide +kernel)
  have a5181 := h.atomAt 2310 (.mul (.n (val% «verify_tables» "zc_is_a_tau@5")) (.n (val% «verify_tables» "zc_is_a_tau@4")) (.n (val% «verify_tables» "zc_is_a_tau@5~0"))) (by decide +kernel)
  have a5183 := h.atomAt 2311 (.const (.n (val% «verify_tables» "s57.u5.s1#0")) (word 4294967296 0)) (by decide +kernel)
  have a5184 := h.atomAt 2312 (.mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "s57.u5.s1#1")) (.n (val% «verify_tables» "kb[7]"))) (by decide +kernel)
  have a5185 := h.atomAt 2313 (.rangeCheck (.n (val% «verify_tables» "s57.u5.s1#1")) (.n (val% «verify_tables» "s57.u5.s1#2")) (.n (val% «verify_tables» "s57.u5.s1#3")) (.n (val% «verify_tables» "s57.u5.s1#4")) (.n (val% «verify_tables» "s57.u5.s1#0"))) (by decide +kernel)
  have a5186 := h.atomAt 2314 (.add (.n (val% «verify_tables» "zc_is_a_tau@6~0")) (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "kb[7]"))) (by decide +kernel)
  have a5187 := h.atomAt 2315 (.mul (.n (val% «verify_tables» "zc_is_a_tau@6")) (.n (val% «verify_tables» "zc_is_a_tau@5")) (.n (val% «verify_tables» "zc_is_a_tau@6~0"))) (by decide +kernel)
  have a5188 := h.atomAt 2316 (.const (.n (val% «verify_tables» "s58#0")) (word 0 0)) (by decide +kernel)
  have a5189 := h.atomAt 2317 (.assertEq (.n (val% «verify_tables» "zc_is_a_tau@6")) (.n (val% «verify_tables» "s58#0"))) (by decide +kernel)
  have a5190 := h.atomAt 2318 (.const (.n (val% «verify_tables» "s59#0")) (word 4294967296 0)) (by decide +kernel)
  have a5191 := h.atomAt 2319 (.mul (.n (val% «verify_tables» "g_bus_mu")) (.n (val% «verify_tables» "s59#1")) (.n (val% «verify_tables» "g_zc_n"))) (by decide +kernel)
  have a5192 := h.atomAt 2320 (.rangeCheck (.n (val% «verify_tables» "s59#1")) (.n (val% «verify_tables» "s59#2")) (.n (val% «verify_tables» "s59#3")) (.n (val% «verify_tables» "s59#4")) (.n (val% «verify_tables» "s59#0"))) (by decide +kernel)
  simp only [Atom.Holds] at a5154 a5155 a5157 a5159 a5160 a5162 a5163
  simp only [Atom.Holds] at a5165 a5166 a5168 a5169 a5171 a5172 a5174 a5175
  simp only [Atom.Holds] at a5177 a5178 a5180 a5181 a5183 a5184 a5186 a5187 a5188 a5189
  simp only [Atom.Holds] at a5190 a5191
  have v0 : σ (.n (val% «verify_tables» "kb[2]")) = gen ^ τ 0 := hkbt 0 (by norm_num)
  have v1 : σ (.n (val% «verify_tables» "kb[3]")) = gen ^ τ 1 := hkbt 1 (by norm_num)
  have v2 : σ (.n (val% «verify_tables» "kb[4]")) = gen ^ τ 2 := hkbt 2 (by norm_num)
  have v3 : σ (.n (val% «verify_tables» "kb[5]")) = gen ^ τ 3 := hkbt 3 (by norm_num)
  have v4 : σ (.n (val% «verify_tables» "kb[6]")) = gen ^ τ 4 := hkbt 4 (by norm_num)
  have v5 : σ (.n (val% «verify_tables» "kb[7]")) = gen ^ τ 5 := hkbt 5 (by norm_num)
  have rc := fun {x y t1 t2 k : V} (hk : σ k = vtW32)
      (hh : (Atom.rangeCheck x y t1 t2 k).Holds Lm.read σ) =>
    vt_rc hμ Lm (K := 33) (by omega) (by norm_num) (by rw [hk, vtW32_eq]) hh
  obtain ⟨d0, hd0, r0⟩ := rc a5154 a5156
  obtain ⟨d1, hd1, r1⟩ := rc a5159 a5161
  obtain ⟨d2, hd2, r2⟩ := rc a5165 a5167
  obtain ⟨d3, hd3, r3⟩ := rc a5171 a5173
  obtain ⟨d4, hd4, r4⟩ := rc a5177 a5179
  obtain ⟨d5, hd5, r5⟩ := rc a5183 a5185
  obtain ⟨d6, hd6, r6⟩ := rc a5190 a5192
  have hb := fun t (ht : t < 6) => hτ t ht
  rw [r0, v0, ← pow_add] at a5155
  rw [r1, v1, ← pow_add] at a5160
  rw [r2, v2, ← pow_add] at a5166
  rw [r3, v3, ← pow_add] at a5172
  rw [r4, v4, ← pow_add] at a5178
  rw [r5, v5, ← pow_add] at a5184
  have hb0 := hb 0 (by norm_num); have hb1 := hb 1 (by norm_num); have hb2 := hb 2 (by norm_num)
  have hb3 := hb 3 (by norm_num); have hb4 := hb 4 (by norm_num); have hb5 := hb 5 (by norm_num)
  have i1 := gen_pow_inj (by omega) (by omega) (a5155.symm.trans a5160)
  have i2 := gen_pow_inj (by omega) (by omega) (a5155.symm.trans a5166)
  have i3 := gen_pow_inj (by omega) (by omega) (a5155.symm.trans a5172)
  have i4 := gen_pow_inj (by omega) (by omega) (a5155.symm.trans a5178)
  have i5 := gen_pow_inj (by omega) (by omega) (a5155.symm.trans a5184)
  rw [hmu, r6, a5155, ← pow_add] at a5191
  have im := gen_pow_inj (by omega) (by omega) a5191
  refine ⟨d0 + τ 0, a5155, fun t ht => ?_, ?_, by omega⟩
  · interval_cases t <;> omega
  · rw [tb_word_zero] at a5188
    have hz : σ (.n (val% «verify_tables» "zc_is_a_tau@6")) = 0 := by rw [← a5188]; exact e_add_eq_zero_iff.mp a5189
    rw [a5187, a5181, a5175, a5169, a5163, a5157, a5162, a5168, a5174, a5180, a5186] at hz
    have key : ∀ t < 6, ∀ v : E, v = gen ^ τ t → σ (.n (val% «verify_tables» "g_zc_n")) + v = 0 → τ t = d0 + τ 0 :=
      fun t ht v hv h0 => by
        rw [a5155, hv] at h0
        exact (gen_pow_inj (by omega) (by have := hb t ht; omega)
          (e_add_eq_zero_iff.mp h0)).symm
    rcases mul_eq_zero.mp hz with hz | h5
    · rcases mul_eq_zero.mp hz with hz | h4
      · rcases mul_eq_zero.mp hz with hz | h3
        · rcases mul_eq_zero.mp hz with hz | h2
          · rcases mul_eq_zero.mp hz with h0 | h1
            · exact ⟨0, by norm_num, key 0 (by norm_num) _ v0 h0⟩
            · exact ⟨1, by norm_num, key 1 (by norm_num) _ v1 h1⟩
          · exact ⟨2, by norm_num, key 2 (by norm_num) _ v2 h2⟩
        · exact ⟨3, by norm_num, key 3 (by norm_num) _ v3 h3⟩
      · exact ⟨4, by norm_num, key 4 (by norm_num) _ v4 h4⟩
    · exact ⟨5, by norm_num, key 5 (by norm_num) _ v5 h5⟩
end

end
end LeanVM.Guest.B1.Tables
