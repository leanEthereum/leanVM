/-
  LeanVM.Guest.B1.Tables.Vt.ZcRun

  `verify_tables`' table sumcheck from its target: the batching challenge's powers, the target
  from the three sides' totals, the first record, the rounds, the last record, the challenges'
  running products and the prefix equality weights.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Rounds
public import LeanVM.Guest.B1.Eq.EqPrefix
public import LeanVM.Guest.Data.NameStrings

/-!
# The table sumcheck

`vt_xi`: `ξ = zc_xi` is squeezed with the bytecode's value waiting (`vtXiFs`). `vt_zc_run`: with
the sides' totals `T_s`, the target `ξ²·T_0 + ξ³·T_1 + ξ⁴·T_2` runs `n` plain rounds from the sponge
after `ξ`, reading `3n` words after the bytecode's value; the
last record holds the sponge, the cursor and the final claim; the challenges are in `chi` from
its top; `cprod[g^j]` is the product of the first `j`; `peq` holds the prefix equality weights of
`chi` against `1 + ζ`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem vt_chi_index {n j : ℕ} {y : E} (hj : j < n) (hy : gen ^ n * vtWInvGen = y * gen ^ j) :
    y = gen ^ (n - 1 - j) := by
  have h1 : gen ^ n * vtWInvGen * gen = gen ^ n := by rw [mul_assoc, vtWInvGen_mul, mul_one]
  rw [hy, mul_assoc, ← pow_succ] at h1
  have e : y * gen ^ (j + 1) = gen ^ (n - 1 - j) * gen ^ (j + 1) := by
    rw [h1, ← pow_add, show n - 1 - j + (j + 1) = n by omega]
  exact mul_right_cancel₀ (pow_ne_zero _ gen_ne_zero) e

/-- The sponge `ξ` is squeezed from: the bytecode sumcheck's last capacity, its value waiting. -/
def vtXiFs (σ : Val) : Fs :=
  (⟨(List.range 5).map fun k ↦ σ (.n (1545 + k)), []⟩ : Fs).absorb (σ (.n 1558)) dsObserve

/-- **The batching challenge `ξ`** (`XI_GRIND_BITS = 0`: a plain squeeze, the bytecode's value
waiting) and the capacity after it. -/
theorem vt_xi {rd : Reader} {σ : Val} (h : VtH rd σ) :
    σ (.n 2250) = (vtXiFs σ).squeeze.1 ∧
      (vtXiFs σ).squeeze.2 = ⟨(List.range 5).map fun k ↦ σ (.n (2258 + k)), []⟩ := by
  have c0 := h.atomAt 1587 (.copy (.n 1553) (.n 1545)) (by decide +kernel)
  have c1 := h.atomAt 1588 (.copy (.n 1554) (.n 1546)) (by decide +kernel)
  have c2 := h.atomAt 1589 (.copy (.n 1555) (.n 1547)) (by decide +kernel)
  have c3 := h.atomAt 1590 (.copy (.n 1556) (.n 1548)) (by decide +kernel)
  have c4 := h.atomAt 1591 (.copy (.n 1557) (.n 1549)) (by decide +kernel)
  have c6 := h.atomAt 1593 (.copy (.n 1559) (.n 1558)) (by decide +kernel)
  have d7 := h.atomAt 1594 (.const (.n 1560) (word 0 1)) (by decide +kernel)
  have z3 := h.atomAt 2268 (.const (.n 2246) (word 0 0)) (by decide +kernel)
  have z4 := h.atomAt 2269 (.const (.n 2247) (word 0 0)) (by decide +kernel)
  have z5 := h.atomAt 2270 (.const (.n 2248) (word 0 0)) (by decide +kernel)
  have z6 := h.atomAt 2271 (.const (.n 2249) (word 0 0)) (by decide +kernel)
  have k := h.atomAt 2272 (.keccak [.n 1559, .n 1560, .n 2246, .n 2246, .n 2246, .n 2247,
    .n 2248, .n 2249, .n 1553, .n 1554, .n 1555, .n 1556, .n 1557] (vtOuts 2250) false false)
    (by decide +kernel)
  simp only [Atom.Holds, tb_word_zero] at c0 c1 c2 c3 c4 c6 d7 z3 z4 z5 z6
  obtain ⟨hP, hC⟩ := vt_keccak k
  have hs : vtXiFs σ = ⟨(List.range 5).map fun k ↦ σ (.n (1545 + k)),
      [(σ (.n 1558), dsObserve)]⟩ := by
    simp [vtXiFs, Fs.absorb, rateScalars]
  have hin : ([.n 1559, .n 1560, .n 2246, .n 2246, .n 2246, .n 2247, .n 2248, .n 2249, .n 1553,
      .n 1554, .n 1555, .n 1556, .n 1557] : List V).map σ =
      rateOf (vtXiFs σ).pend ++ (vtXiFs σ).cap := by
    rw [hs, rateOf_eq_cells _ (by simp)]
    simp only [List.map_cons, List.map_nil, pendCells, List.flatMap_cons, List.flatMap_nil,
      List.length_cons, List.length_nil, List.cons_append, List.nil_append, List.append_nil,
      List.range_succ, List.range_zero, c0, c1, c2, c3, c4, c6, d7, z3, z4, z5, z6]
    rfl
  rw [hin] at hP hC
  refine ⟨?_, ?_⟩
  · simp only [Fs.squeeze, Fs.perm]
    exact challengeT_value (s0 := .n 2250) (b := 2250) rfl (hP 0 (by omega))
  · simp only [Fs.squeeze, Fs.perm]
    have e : ∀ k, 2250 + 8 + k = 2258 + k := fun k => by omega
    simp only [e] at hC
    rw [hC]

/-- **The table sumcheck.** -/
theorem vt_zc_run {rd : Reader} {σ : Val} (h : VtH rd σ) {n : ℕ} (hn : n < 33)
    (hgn : σ (.n 2197) = gen ^ n) :
    σ (.n 2272) = σ (.n 2250) ^ 2 * σ (.n 2095) + σ (.n 2250) ^ 3 * σ (.n 2141) +
      σ (.n 2250) ^ 4 * σ (.n 2196) ∧
    ∃ (xs pts : List E) (claimN : E),
      RunsTo (sumcheck (σ (.n 2272)) 4 (List.replicate n none))
        ⟨(List.range 5).map fun k ↦ σ (.n (2258 + k)), []⟩ xs (pts, claimN)
        ⟨(List.range 5).map fun k ↦ σ (.n (2294 + k)), []⟩ ∧
      ReadsAt rd (σ (.n 1550) * gen) xs ∧ xs.length = 3 * n ∧ pts.length = n ∧
      σ (.n 2299) = σ (.n 1550) * gen * gen ^ (3 * n) ∧ σ (.n 2300) = claimN ∧
      (∀ i < n, LoadHolds rd (σ (.n 16)) (n - 1 - i) (pts.getD i 0)) ∧
      (∀ j ≤ n, LoadHolds rd (σ (.n 2282)) j ((pts.take j).prod)) ∧
      EqPrefix rd (σ (.n 2303)) 1 (σ (.n 16)) (σ (.n 699)) n := by
  have a5207 := h.atomAt 2273 (.const (.n 2263) (word 1 0)) (by decide +kernel)
  have a5208 := h.atomAt 2274 (.mul (.n 2264) (.n 2263) (.n 2250)) (by decide +kernel)
  have a5209 := h.atomAt 2275 (.mul (.n 2265) (.n 2264) (.n 2250)) (by decide +kernel)
  have a5210 := h.atomAt 2276 (.mul (.n 2266) (.n 2265) (.n 2250)) (by decide +kernel)
  have a5211 := h.atomAt 2277 (.mul (.n 2267) (.n 2266) (.n 2250)) (by decide +kernel)
  have a5212 := h.atomAt 2278 (.mul (.n 2268) (.n 2265) (.n 2095)) (by decide +kernel)
  have a5213 := h.atomAt 2279 (.mul (.n 2269) (.n 2266) (.n 2141)) (by decide +kernel)
  have a5214 := h.atomAt 2280 (.add (.n 2270) (.n 2268) (.n 2269)) (by decide +kernel)
  have a5215 := h.atomAt 2281 (.mul (.n 2271) (.n 2267) (.n 2196)) (by decide +kernel)
  have a5216 := h.atomAt 2282 (.add (.n 2272) (.n 2270) (.n 2271)) (by decide +kernel)
  have a5217 := h.atomAt 2283 (.const (.n 2273) (word 2 0)) (by decide +kernel)
  have a5218 := h.atomAt 2284 (.mul (.n 2274) (.n 2197) (.n 2273)) (by decide +kernel)
  have a5219 := h.atomAt 2285 (.mul (.n 2275) (.n 2274) (.n 2274)) (by decide +kernel)
  have a5220 := h.atomAt 2286 (.mul (.n 2276) (.n 2275) (.n 2274)) (by decide +kernel)
  have a5221 := h.atomAt 2287 (.mul (.n 2277) (.n 2276) (.n 2276)) (by decide +kernel)
  have a5222 := h.atomAt 2288 (.mul (.n 2278) (.n 2277) (.n 2274)) (by decide +kernel)
  have a5224 := h.atomAt 2290 (.const (.n 2280) (word 2 0)) (by decide +kernel)
  have a5225 := h.atomAt 2291 (.mul (.n 2281) (.n 2197) (.n 2280)) (by decide +kernel)
  have a5227 := h.atomAt 2293 (.load (.n 2258) (.n 2279) 0) (by decide +kernel)
  have a5228 := h.atomAt 2294 (.load (.n 2259) (.n 2279) 1) (by decide +kernel)
  have a5229 := h.atomAt 2295 (.load (.n 2260) (.n 2279) 2) (by decide +kernel)
  have a5230 := h.atomAt 2296 (.load (.n 2261) (.n 2279) 3) (by decide +kernel)
  have a5231 := h.atomAt 2297 (.load (.n 2262) (.n 2279) 4) (by decide +kernel)
  have a5232 := h.atomAt 2298 (.const (.n 2283) (word 2 0)) (by decide +kernel)
  have a5233 := h.atomAt 2299 (.mul (.n 2284) (.n 1550) (.n 2283)) (by decide +kernel)
  have a5234 := h.atomAt 2300 (.load (.n 2284) (.n 2279) 5) (by decide +kernel)
  have a5235 := h.atomAt 2301 (.load (.n 2272) (.n 2279) 6) (by decide +kernel)
  have a5236 := h.atomAt 2302 (.const (.n 2285) (word 1 0)) (by decide +kernel)
  have a5237 := h.atomAt 2303 (.load (.n 2285) (.n 2282) 0) (by decide +kernel)
  have a5238 := h.atomAt 2304 (.const (.n 2286) (word 1 0)) (by decide +kernel)
  have a5239 := h.atomAt 2305 (.add (.n 2287) (.n 2286) (.n 2197)) (by decide +kernel)
  have a5240 := h.atomAt 2306 (.const (.n 2288) (word 1 0)) (by decide +kernel)
  have a5242 := h.atomAt 2308 (.mul (.n 2289) (.n 2197) (.n 2197)) (by decide +kernel)
  have a5243 := h.atomAt 2309 (.mul (.n 2290) (.n 2289) (.n 2197)) (by decide +kernel)
  have a5244 := h.atomAt 2310 (.mul (.n 2291) (.n 2290) (.n 2290)) (by decide +kernel)
  have a5245 := h.atomAt 2311 (.mul (.n 2292) (.n 2291) (.n 2197)) (by decide +kernel)
  have a5246 := h.atomAt 2312 (.mul (.n 2293) (.n 2279) (.n 2292)) (by decide +kernel)
  have a5247 := h.atomAt 2313 (.load (.n 2294) (.n 2293) 0) (by decide +kernel)
  have a5248 := h.atomAt 2314 (.load (.n 2295) (.n 2293) 1) (by decide +kernel)
  have a5249 := h.atomAt 2315 (.load (.n 2296) (.n 2293) 2) (by decide +kernel)
  have a5250 := h.atomAt 2316 (.load (.n 2297) (.n 2293) 3) (by decide +kernel)
  have a5251 := h.atomAt 2317 (.load (.n 2298) (.n 2293) 4) (by decide +kernel)
  have a5252 := h.atomAt 2318 (.load (.n 2299) (.n 2293) 5) (by decide +kernel)
  have a5253 := h.atomAt 2319 (.load (.n 2300) (.n 2293) 6) (by decide +kernel)
  have a5254 := h.atomAt 2320 (.const (.n 2301) (word 2 0)) (by decide +kernel)
  have a5255 := h.atomAt 2321 (.mul (.n 2302) (.n 2197) (.n 2301)) (by decide +kernel)
  have a5257 := h.atomAt 2323 (.const (.n 2304) (word 1 0)) (by decide +kernel)
  have hloop := h.callIfAt 2307 (.n 2287) name% «verify_tables_loop0» [.n 2288, .n 2197, .n 2279,
      .n 18,
    .n 16, .n 2197, .n 2282] (by decide +kernel)
  have hchain := h.callAt 2324 "eq_prefix_chain" [.n 2303, .n 2304, .n 16, .n 699, .n 2197] []
    (by decide +kernel)
  simp only [Atom.Holds] at a5207 a5208 a5209 a5210 a5211 a5212 a5213 a5214 a5215 a5216
  simp only [Atom.Holds] at a5217 a5218 a5219 a5220 a5221 a5222 a5224 a5225 a5227 a5228
  simp only [Atom.Holds] at a5229 a5230 a5231 a5232 a5233 a5234 a5235 a5236 a5237 a5238
  simp only [Atom.Holds] at a5239 a5240 a5242 a5243 a5244 a5245 a5246 a5247 a5248 a5249
  simp only [Atom.Holds] at a5250 a5251 a5252 a5253 a5254 a5255 a5257
  simp only [List.map_cons, List.map_nil] at hloop hchain
  refine ⟨by rw [a5216, a5214, a5212, a5213, a5215, a5211, a5210, a5209, a5208, a5207,
    tb_word_one]; ring, ?_⟩
  have hB : ∀ j < n, L10B rd (σ (.n 2279)) (σ (.n 18)) (σ (.n 16)) (gen ^ n) (σ (.n 2282)) (gen ^ j) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · intro j hj; omega
    · have hne : σ (.n 2287) ≠ 0 := by
        rw [a5239, a5238, tb_word_one, hgn]
        intro h0
        have := gen_pow_inj (by omega) (by omega)
          ((e_add_eq_zero_iff.mp h0).symm.trans (pow_zero gen).symm)
        omega
      have hr := hloop.2 hne
      rw [a5240, tb_word_one, hgn] at hr
      exact l10_loop hn0 (by omega) hr
  have hc0 : CapAt rd (σ (.n 2279) * gen ^ (7 * 0)) 0 1
      ((List.range 5).map fun k ↦ σ (.n (2258 + k))) := by
    refine ⟨by simp, fun j hj => ?_⟩
    simp only [List.length_map, List.length_range] at hj
    simp only [Nat.mul_zero, pow_zero, mul_one, Nat.zero_add, List.getElem_map,
      List.getElem_range]
    interval_cases j
    · exact a5227
    · exact a5228
    · exact a5229
    · exact a5230
    · exact a5231
  have hcur0 : LoadHolds rd (σ (.n 2279) * gen ^ (7 * 0)) 5 (σ (.n 1550) * gen) := by
    rw [Nat.mul_zero, pow_zero, mul_one, ← tb_word_gen, ← a5232, ← a5233]
    exact a5234
  have hcl0 : LoadHolds rd (σ (.n 2279) * gen ^ (7 * 0)) 6 (σ (.n 2272)) := by
    rw [Nat.mul_zero, pow_zero, mul_one]; exact a5235
  obtain ⟨xs, pts, claimN, capN, hrun, hxs, hxl, hpl, hcN, hcurN, hclN, hchi⟩ :=
    l10_chain (by omega) hB n le_rfl 0 (by omega) _ _ _ hc0 hcur0 hcl0
  have e5926 : σ (.n 2293) = σ (.n 2279) * gen ^ (7 * n) := by
    rw [a5246, a5245, a5244, a5243, a5242, hgn]; ring
  have hcF : CapAt rd (σ (.n 2279) * gen ^ (7 * n)) 0 1
      ((List.range 5).map fun k ↦ σ (.n (2294 + k))) := by
    refine ⟨by simp, fun j hj => ?_⟩
    simp only [List.length_map, List.length_range] at hj
    simp only [Nat.zero_add, mul_one, List.getElem_map, List.getElem_range, ← e5926]
    interval_cases j
    · exact a5247
    · exact a5248
    · exact a5249
    · exact a5250
    · exact a5251
  obtain rfl := capAt_unique' hcN hcF
  rw [← e5926] at hcurN hclN
  refine ⟨xs, pts, claimN, hrun, by simpa using hxs, hxl, hpl,
    tb_loadHolds_unique a5252 hcurN, tb_loadHolds_unique a5253 hclN,
    fun i hi => by simpa using hchi i hi, ?_, ?_⟩
  · intro j hj
    induction j with
    | zero =>
      rw [a5236, tb_word_one] at a5237
      simpa using a5237
    | succ j ih =>
      obtain ⟨-, -, -, -, rk, -, -, -, -, -, ⟨y, hy, hrk⟩, cp, hcp, hcp1⟩ := hB j (by omega)
      rw [vt_chi_index (by omega) hy, tb_loadHolds_mul_gen_pow, Nat.add_zero] at hrk
      have erk : rk = pts.getD j 0 := tb_loadHolds_unique hrk (by simpa using hchi j (by omega))
      rw [tb_loadHolds_mul_gen_pow, Nat.add_zero] at hcp
      rw [tb_loadHolds_mul_gen_pow] at hcp1
      rw [tb_loadHolds_unique hcp (ih (by omega)), erk] at hcp1
      rw [List.prod_take_succ _ _ (by omega), ← List.getD_eq_getElem _ 0 (by omega)]
      exact hcp1
  · have hm := (eq_prefix_chain_holds rd _ _).mp hchain
    simp only [MeaningEqPrefixChain] at hm
    obtain ⟨-, -, n', hn', hn'v, hep⟩ := hm
    rw [hgn] at hn'v
    obtain rfl := gen_pow_inj (by omega) (by omega) hn'v
    rw [a5257, tb_word_one] at hep
    exact hep

end
end LeanVM.Guest.B1.Tables
