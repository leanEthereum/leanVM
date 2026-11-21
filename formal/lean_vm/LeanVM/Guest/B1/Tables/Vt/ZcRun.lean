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
  (⟨(List.range 5).map fun k ↦ σ (.n (1593 + k)), []⟩ : Fs).absorb (σ (.n 1606)) dsObserve

/-- **The batching challenge `ξ`** (`XI_GRIND_BITS = 0`: a plain squeeze, the bytecode's value
waiting) and the capacity after it. -/
theorem vt_xi {rd : Reader} {σ : Val} (h : VtH rd σ) :
    σ (.n 2298) = (vtXiFs σ).squeeze.1 ∧
      (vtXiFs σ).squeeze.2 = ⟨(List.range 5).map fun k ↦ σ (.n (2306 + k)), []⟩ := by
  have c0 := h.atomAt 1647 (.copy (.n 1601) (.n 1593)) (by decide +kernel)
  have c1 := h.atomAt 1648 (.copy (.n 1602) (.n 1594)) (by decide +kernel)
  have c2 := h.atomAt 1649 (.copy (.n 1603) (.n 1595)) (by decide +kernel)
  have c3 := h.atomAt 1650 (.copy (.n 1604) (.n 1596)) (by decide +kernel)
  have c4 := h.atomAt 1651 (.copy (.n 1605) (.n 1597)) (by decide +kernel)
  have c6 := h.atomAt 1653 (.copy (.n 1607) (.n 1606)) (by decide +kernel)
  have d7 := h.atomAt 1654 (.const (.n 1608) (word 0 1)) (by decide +kernel)
  have z3 := h.atomAt 2328 (.const (.n 2294) (word 0 0)) (by decide +kernel)
  have z4 := h.atomAt 2329 (.const (.n 2295) (word 0 0)) (by decide +kernel)
  have z5 := h.atomAt 2330 (.const (.n 2296) (word 0 0)) (by decide +kernel)
  have z6 := h.atomAt 2331 (.const (.n 2297) (word 0 0)) (by decide +kernel)
  have k := h.atomAt 2332 (.keccak [.n 1607, .n 1608, .n 2294, .n 2294, .n 2294, .n 2295,
    .n 2296, .n 2297, .n 1601, .n 1602, .n 1603, .n 1604, .n 1605] (vtOuts 2298) false false)
    (by decide +kernel)
  simp only [Atom.Holds, tb_word_zero] at c0 c1 c2 c3 c4 c6 d7 z3 z4 z5 z6
  obtain ⟨hP, hC⟩ := vt_keccak k
  have hs : vtXiFs σ = ⟨(List.range 5).map fun k ↦ σ (.n (1593 + k)),
      [(σ (.n 1606), dsObserve)]⟩ := by
    simp [vtXiFs, Fs.absorb, rateScalars]
  have hin : ([.n 1607, .n 1608, .n 2294, .n 2294, .n 2294, .n 2295, .n 2296, .n 2297, .n 1601,
      .n 1602, .n 1603, .n 1604, .n 1605] : List V).map σ =
      rateOf (vtXiFs σ).pend ++ (vtXiFs σ).cap := by
    rw [hs, rateOf_eq_cells _ (by simp)]
    simp only [List.map_cons, List.map_nil, pendCells, List.flatMap_cons, List.flatMap_nil,
      List.length_cons, List.length_nil, List.cons_append, List.nil_append, List.append_nil,
      List.range_succ, List.range_zero, c0, c1, c2, c3, c4, c6, d7, z3, z4, z5, z6]
    rfl
  rw [hin] at hP hC
  refine ⟨?_, ?_⟩
  · simp only [Fs.squeeze, Fs.perm]
    exact challengeT_value (s0 := .n 2298) (b := 2298) rfl (hP 0 (by omega))
  · simp only [Fs.squeeze, Fs.perm]
    have e : ∀ k, 2298 + 8 + k = 2306 + k := fun k => by omega
    simp only [e] at hC
    rw [hC]

/-- **The table sumcheck.** -/
theorem vt_zc_run {rd : Reader} {σ : Val} (h : VtH rd σ) {n : ℕ} (hn : n < 33)
    (hgn : σ (.n 2245) = gen ^ n) :
    σ (.n 2320) = σ (.n 2298) ^ 2 * σ (.n 2143) + σ (.n 2298) ^ 3 * σ (.n 2189) +
      σ (.n 2298) ^ 4 * σ (.n 2244) ∧
    ∃ (xs pts : List E) (claimN : E),
      RunsTo (sumcheck (σ (.n 2320)) 4 (List.replicate n none))
        ⟨(List.range 5).map fun k ↦ σ (.n (2306 + k)), []⟩ xs (pts, claimN)
        ⟨(List.range 5).map fun k ↦ σ (.n (2342 + k)), []⟩ ∧
      ReadsAt rd (σ (.n 1598) * gen) xs ∧ xs.length = 3 * n ∧ pts.length = n ∧
      σ (.n 2347) = σ (.n 1598) * gen * gen ^ (3 * n) ∧ σ (.n 2348) = claimN ∧
      (∀ i < n, LoadHolds rd (σ (.n 16)) (n - 1 - i) (pts.getD i 0)) ∧
      (∀ j ≤ n, LoadHolds rd (σ (.n 2330)) j ((pts.take j).prod)) ∧
      EqPrefix rd (σ (.n 2351)) 1 (σ (.n 16)) (σ (.n 699)) n := by
  have a5207 := h.atomAt 2333 (.const (.n 2311) (word 1 0)) (by decide +kernel)
  have a5208 := h.atomAt 2334 (.mul (.n 2312) (.n 2311) (.n 2298)) (by decide +kernel)
  have a5209 := h.atomAt 2335 (.mul (.n 2313) (.n 2312) (.n 2298)) (by decide +kernel)
  have a5210 := h.atomAt 2336 (.mul (.n 2314) (.n 2313) (.n 2298)) (by decide +kernel)
  have a5211 := h.atomAt 2337 (.mul (.n 2315) (.n 2314) (.n 2298)) (by decide +kernel)
  have a5212 := h.atomAt 2338 (.mul (.n 2316) (.n 2313) (.n 2143)) (by decide +kernel)
  have a5213 := h.atomAt 2339 (.mul (.n 2317) (.n 2314) (.n 2189)) (by decide +kernel)
  have a5214 := h.atomAt 2340 (.add (.n 2318) (.n 2316) (.n 2317)) (by decide +kernel)
  have a5215 := h.atomAt 2341 (.mul (.n 2319) (.n 2315) (.n 2244)) (by decide +kernel)
  have a5216 := h.atomAt 2342 (.add (.n 2320) (.n 2318) (.n 2319)) (by decide +kernel)
  have a5217 := h.atomAt 2343 (.const (.n 2321) (word 2 0)) (by decide +kernel)
  have a5218 := h.atomAt 2344 (.mul (.n 2322) (.n 2245) (.n 2321)) (by decide +kernel)
  have a5219 := h.atomAt 2345 (.mul (.n 2323) (.n 2322) (.n 2322)) (by decide +kernel)
  have a5220 := h.atomAt 2346 (.mul (.n 2324) (.n 2323) (.n 2322)) (by decide +kernel)
  have a5221 := h.atomAt 2347 (.mul (.n 2325) (.n 2324) (.n 2324)) (by decide +kernel)
  have a5222 := h.atomAt 2348 (.mul (.n 2326) (.n 2325) (.n 2322)) (by decide +kernel)
  have a5224 := h.atomAt 2350 (.const (.n 2328) (word 2 0)) (by decide +kernel)
  have a5225 := h.atomAt 2351 (.mul (.n 2329) (.n 2245) (.n 2328)) (by decide +kernel)
  have a5227 := h.atomAt 2353 (.load (.n 2306) (.n 2327) 0) (by decide +kernel)
  have a5228 := h.atomAt 2354 (.load (.n 2307) (.n 2327) 1) (by decide +kernel)
  have a5229 := h.atomAt 2355 (.load (.n 2308) (.n 2327) 2) (by decide +kernel)
  have a5230 := h.atomAt 2356 (.load (.n 2309) (.n 2327) 3) (by decide +kernel)
  have a5231 := h.atomAt 2357 (.load (.n 2310) (.n 2327) 4) (by decide +kernel)
  have a5232 := h.atomAt 2358 (.const (.n 2331) (word 2 0)) (by decide +kernel)
  have a5233 := h.atomAt 2359 (.mul (.n 2332) (.n 1598) (.n 2331)) (by decide +kernel)
  have a5234 := h.atomAt 2360 (.load (.n 2332) (.n 2327) 5) (by decide +kernel)
  have a5235 := h.atomAt 2361 (.load (.n 2320) (.n 2327) 6) (by decide +kernel)
  have a5236 := h.atomAt 2362 (.const (.n 2333) (word 1 0)) (by decide +kernel)
  have a5237 := h.atomAt 2363 (.load (.n 2333) (.n 2330) 0) (by decide +kernel)
  have a5238 := h.atomAt 2364 (.const (.n 2334) (word 1 0)) (by decide +kernel)
  have a5239 := h.atomAt 2365 (.add (.n 2335) (.n 2334) (.n 2245)) (by decide +kernel)
  have a5240 := h.atomAt 2366 (.const (.n 2336) (word 1 0)) (by decide +kernel)
  have a5242 := h.atomAt 2368 (.mul (.n 2337) (.n 2245) (.n 2245)) (by decide +kernel)
  have a5243 := h.atomAt 2369 (.mul (.n 2338) (.n 2337) (.n 2245)) (by decide +kernel)
  have a5244 := h.atomAt 2370 (.mul (.n 2339) (.n 2338) (.n 2338)) (by decide +kernel)
  have a5245 := h.atomAt 2371 (.mul (.n 2340) (.n 2339) (.n 2245)) (by decide +kernel)
  have a5246 := h.atomAt 2372 (.mul (.n 2341) (.n 2327) (.n 2340)) (by decide +kernel)
  have a5247 := h.atomAt 2373 (.load (.n 2342) (.n 2341) 0) (by decide +kernel)
  have a5248 := h.atomAt 2374 (.load (.n 2343) (.n 2341) 1) (by decide +kernel)
  have a5249 := h.atomAt 2375 (.load (.n 2344) (.n 2341) 2) (by decide +kernel)
  have a5250 := h.atomAt 2376 (.load (.n 2345) (.n 2341) 3) (by decide +kernel)
  have a5251 := h.atomAt 2377 (.load (.n 2346) (.n 2341) 4) (by decide +kernel)
  have a5252 := h.atomAt 2378 (.load (.n 2347) (.n 2341) 5) (by decide +kernel)
  have a5253 := h.atomAt 2379 (.load (.n 2348) (.n 2341) 6) (by decide +kernel)
  have a5254 := h.atomAt 2380 (.const (.n 2349) (word 2 0)) (by decide +kernel)
  have a5255 := h.atomAt 2381 (.mul (.n 2350) (.n 2245) (.n 2349)) (by decide +kernel)
  have a5257 := h.atomAt 2383 (.const (.n 2352) (word 1 0)) (by decide +kernel)
  have hloop := h.callIfAt 2367 (.n 2335) name% «verify_tables_loop0» [.n 2336, .n 2245, .n 2327,
      .n 18,
    .n 16, .n 2245, .n 2330] (by decide +kernel)
  have hchain := h.callAt 2384 "eq_prefix_chain" [.n 2351, .n 2352, .n 16, .n 699, .n 2245] []
    (by decide +kernel)
  simp only [Atom.Holds] at a5207 a5208 a5209 a5210 a5211 a5212 a5213 a5214 a5215 a5216
  simp only [Atom.Holds] at a5217 a5218 a5219 a5220 a5221 a5222 a5224 a5225 a5227 a5228
  simp only [Atom.Holds] at a5229 a5230 a5231 a5232 a5233 a5234 a5235 a5236 a5237 a5238
  simp only [Atom.Holds] at a5239 a5240 a5242 a5243 a5244 a5245 a5246 a5247 a5248 a5249
  simp only [Atom.Holds] at a5250 a5251 a5252 a5253 a5254 a5255 a5257
  simp only [List.map_cons, List.map_nil] at hloop hchain
  refine ⟨by rw [a5216, a5214, a5212, a5213, a5215, a5211, a5210, a5209, a5208, a5207,
    tb_word_one]; ring, ?_⟩
  have hB : ∀ j < n, L10B rd (σ (.n 2327)) (σ (.n 18)) (σ (.n 16)) (gen ^ n) (σ (.n 2330)) (gen ^ j) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · intro j hj; omega
    · have hne : σ (.n 2335) ≠ 0 := by
        rw [a5239, a5238, tb_word_one, hgn]
        intro h0
        have := gen_pow_inj (by omega) (by omega)
          ((e_add_eq_zero_iff.mp h0).symm.trans (pow_zero gen).symm)
        omega
      have hr := hloop.2 hne
      rw [a5240, tb_word_one, hgn] at hr
      exact l10_loop hn0 (by omega) hr
  have hc0 : CapAt rd (σ (.n 2327) * gen ^ (7 * 0)) 0 1
      ((List.range 5).map fun k ↦ σ (.n (2306 + k))) := by
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
  have hcur0 : LoadHolds rd (σ (.n 2327) * gen ^ (7 * 0)) 5 (σ (.n 1598) * gen) := by
    rw [Nat.mul_zero, pow_zero, mul_one, ← tb_word_gen, ← a5232, ← a5233]
    exact a5234
  have hcl0 : LoadHolds rd (σ (.n 2327) * gen ^ (7 * 0)) 6 (σ (.n 2320)) := by
    rw [Nat.mul_zero, pow_zero, mul_one]; exact a5235
  obtain ⟨xs, pts, claimN, capN, hrun, hxs, hxl, hpl, hcN, hcurN, hclN, hchi⟩ :=
    l10_chain (by omega) hB n le_rfl 0 (by omega) _ _ _ hc0 hcur0 hcl0
  have e5926 : σ (.n 2341) = σ (.n 2327) * gen ^ (7 * n) := by
    rw [a5246, a5245, a5244, a5243, a5242, hgn]; ring
  have hcF : CapAt rd (σ (.n 2327) * gen ^ (7 * n)) 0 1
      ((List.range 5).map fun k ↦ σ (.n (2342 + k))) := by
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
