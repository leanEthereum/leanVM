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
# The table sumcheck (G:2546-2587)

`vt_xi`: `ξ = zc_xi` is squeezed with the bytecode's value waiting (`vtXiFs`). `vt_zc_run`: with
the sides' totals `T_s`, the target `ξ²·T_0 + ξ³·T_1 + ξ⁴·T_2` runs `n` plain rounds from the sponge
after `ξ`, reading `3n` words after the bytecode's value; the
last record holds the sponge, the cursor and the final claim; the challenges are in `chi` from
its top; `cprod[g^j]` is the product of the first `j`; `peq` holds the prefix equality weights of
`chi` against `1 + ζ`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
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
  (⟨(List.range 5).map fun k ↦ σ (.n (1893 + k)), []⟩ : Fs).absorb (σ (.n 1906)) dsObserve

/-- **The batching challenge `ξ`** (`XI_GRIND_BITS = 0`: a plain squeeze, the bytecode's value
waiting) and the capacity after it. -/
theorem vt_xi {rd : Reader} {σ : Val} (h : VtH rd σ) :
    σ (.n 2611) = (vtXiFs σ).squeeze.1 ∧
      (vtXiFs σ).squeeze.2 = ⟨(List.range 5).map fun k ↦ σ (.n (2606 + k)), []⟩ := by
  have c0 := h.atomAt 1946 (.copy (.n 1901) (.n 1893)) (by decide +kernel)
  have c1 := h.atomAt 1947 (.copy (.n 1902) (.n 1894)) (by decide +kernel)
  have c2 := h.atomAt 1948 (.copy (.n 1903) (.n 1895)) (by decide +kernel)
  have c3 := h.atomAt 1949 (.copy (.n 1904) (.n 1896)) (by decide +kernel)
  have c4 := h.atomAt 1950 (.copy (.n 1905) (.n 1897)) (by decide +kernel)
  have c6 := h.atomAt 1952 (.copy (.n 1907) (.n 1906)) (by decide +kernel)
  have d7 := h.atomAt 1953 (.const (.n 1908) (word 0 1)) (by decide +kernel)
  have z3 := h.atomAt 2627 (.const (.n 2594) (word 0 0)) (by decide +kernel)
  have z4 := h.atomAt 2628 (.const (.n 2595) (word 0 0)) (by decide +kernel)
  have z5 := h.atomAt 2629 (.const (.n 2596) (word 0 0)) (by decide +kernel)
  have z6 := h.atomAt 2630 (.const (.n 2597) (word 0 0)) (by decide +kernel)
  have k := h.atomAt 2631 (.keccak [.n 1907, .n 1908, .n 2594, .n 2594, .n 2594, .n 2595,
    .n 2596, .n 2597, .n 1901, .n 1902, .n 1903, .n 1904, .n 1905] (vtOuts 2598) false false)
    (by decide +kernel)
  obtain ⟨_, hch⟩ := h.sliceAt 2632 (challengeT (.n 2598) 2611) (by decide +kernel)
  rw [holds_challengeT] at hch
  simp only [Atom.Holds, tb_word_zero] at c0 c1 c2 c3 c4 c6 d7 z3 z4 z5 z6
  obtain ⟨hP, hC⟩ := vt_keccak k
  have hs : vtXiFs σ = ⟨(List.range 5).map fun k ↦ σ (.n (1893 + k)),
      [(σ (.n 1906), dsObserve)]⟩ := by
    simp [vtXiFs, Fs.absorb, rateScalars]
  have hin : ([.n 1907, .n 1908, .n 2594, .n 2594, .n 2594, .n 2595, .n 2596, .n 2597, .n 1901,
      .n 1902, .n 1903, .n 1904, .n 1905] : List V).map σ =
      rateOf (vtXiFs σ).pend ++ (vtXiFs σ).cap := by
    rw [hs, rateOf_eq_cells _ (by simp)]
    simp only [List.map_cons, List.map_nil, pendCells, List.flatMap_cons, List.flatMap_nil,
      List.length_cons, List.length_nil, List.cons_append, List.nil_append, List.append_nil,
      List.range_succ, List.range_zero, c0, c1, c2, c3, c4, c6, d7, z3, z4, z5, z6]
    rfl
  rw [hin] at hP hC
  refine ⟨?_, ?_⟩
  · simp only [Fs.squeeze, Fs.perm]
    exact challengeT_value hch.1 (hP 0 (by omega))
  · simp only [Fs.squeeze, Fs.perm]
    have e : ∀ k, 2598 + 8 + k = 2606 + k := fun k => by omega
    simp only [e] at hC
    rw [hC]

/-- **The table sumcheck.** -/
theorem vt_zc_run {rd : Reader} {σ : Val} (h : VtH rd σ) {n : ℕ} (hn : n < 34)
    (hgn : σ (.n 2545) = gen ^ n) :
    σ (.n 2621) = σ (.n 2611) ^ 2 * σ (.n 2443) + σ (.n 2611) ^ 3 * σ (.n 2489) +
      σ (.n 2611) ^ 4 * σ (.n 2544) ∧
    ∃ (xs pts : List E) (claimN : E),
      RunsTo (sumcheck (σ (.n 2621)) 4 (List.replicate n none))
        ⟨(List.range 5).map fun k ↦ σ (.n (2606 + k)), []⟩ xs (pts, claimN)
        ⟨(List.range 5).map fun k ↦ σ (.n (2647 + k)), []⟩ ∧
      ReadsAt rd (σ (.n 1898) * gen) xs ∧ xs.length = 3 * n ∧ pts.length = n ∧
      σ (.n 2652) = σ (.n 1898) * gen * gen ^ (3 * n) ∧ σ (.n 2653) = claimN ∧
      (∀ i < n, LoadHolds rd (σ (.n 16)) (n - 1 - i) (pts.getD i 0)) ∧
      (∀ j ≤ n, LoadHolds rd (σ (.n 2631)) j ((pts.take j).prod)) ∧
      EqPrefix rd (σ (.n 2656)) 1 (σ (.n 16)) (σ (.n 700)) n := by
  have a5207 := h.atomAt 2633 (.const (.n 2612) (word 1 0)) (by decide +kernel)
  have a5208 := h.atomAt 2634 (.mul (.n 2613) (.n 2612) (.n 2611)) (by decide +kernel)
  have a5209 := h.atomAt 2635 (.mul (.n 2614) (.n 2613) (.n 2611)) (by decide +kernel)
  have a5210 := h.atomAt 2636 (.mul (.n 2615) (.n 2614) (.n 2611)) (by decide +kernel)
  have a5211 := h.atomAt 2637 (.mul (.n 2616) (.n 2615) (.n 2611)) (by decide +kernel)
  have a5212 := h.atomAt 2638 (.mul (.n 2617) (.n 2614) (.n 2443)) (by decide +kernel)
  have a5213 := h.atomAt 2639 (.mul (.n 2618) (.n 2615) (.n 2489)) (by decide +kernel)
  have a5214 := h.atomAt 2640 (.add (.n 2619) (.n 2617) (.n 2618)) (by decide +kernel)
  have a5215 := h.atomAt 2641 (.mul (.n 2620) (.n 2616) (.n 2544)) (by decide +kernel)
  have a5216 := h.atomAt 2642 (.add (.n 2621) (.n 2619) (.n 2620)) (by decide +kernel)
  have a5217 := h.atomAt 2643 (.const (.n 2622) (word 2 0)) (by decide +kernel)
  have a5218 := h.atomAt 2644 (.mul (.n 2623) (.n 2545) (.n 2622)) (by decide +kernel)
  have a5219 := h.atomAt 2645 (.mul (.n 2624) (.n 2623) (.n 2623)) (by decide +kernel)
  have a5220 := h.atomAt 2646 (.mul (.n 2625) (.n 2624) (.n 2623)) (by decide +kernel)
  have a5221 := h.atomAt 2647 (.mul (.n 2626) (.n 2625) (.n 2625)) (by decide +kernel)
  have a5222 := h.atomAt 2648 (.mul (.n 2627) (.n 2626) (.n 2623)) (by decide +kernel)
  have a5224 := h.atomAt 2650 (.const (.n 2629) (word 2 0)) (by decide +kernel)
  have a5225 := h.atomAt 2651 (.mul (.n 2630) (.n 2545) (.n 2629)) (by decide +kernel)
  have a5227 := h.atomAt 2653 (.load (.n 2606) (.n 2628) 0) (by decide +kernel)
  have a5228 := h.atomAt 2654 (.load (.n 2607) (.n 2628) 1) (by decide +kernel)
  have a5229 := h.atomAt 2655 (.load (.n 2608) (.n 2628) 2) (by decide +kernel)
  have a5230 := h.atomAt 2656 (.load (.n 2609) (.n 2628) 3) (by decide +kernel)
  have a5231 := h.atomAt 2657 (.load (.n 2610) (.n 2628) 4) (by decide +kernel)
  have a5232 := h.atomAt 2658 (.const (.n 2632) (word 2 0)) (by decide +kernel)
  have a5233 := h.atomAt 2659 (.mul (.n 2633) (.n 1898) (.n 2632)) (by decide +kernel)
  have a5234 := h.atomAt 2660 (.load (.n 2633) (.n 2628) 5) (by decide +kernel)
  have a5235 := h.atomAt 2661 (.load (.n 2621) (.n 2628) 6) (by decide +kernel)
  have a5236 := h.atomAt 2662 (.const (.n 2634) (word 1 0)) (by decide +kernel)
  have a5237 := h.atomAt 2663 (.load (.n 2634) (.n 2631) 0) (by decide +kernel)
  have a5238 := h.atomAt 2665 (.const (.n 2636) (word 1 0)) (by decide +kernel)
  have a5239 := h.atomAt 2666 (.add (.n 2637) (.n 2636) (.n 2545)) (by decide +kernel)
  have a5240 := h.atomAt 2667 (.const (.n 2638) (word 1 0)) (by decide +kernel)
  have a5238' := h.atomAt 2669 (.const (.n 2639) (word 1 0)) (by decide +kernel)
  have a5239' := h.atomAt 2670 (.add (.n 2640) (.n 2639) (.n 2545)) (by decide +kernel)
  have a5240' := h.atomAt 2671 (.const (.n 2641) (word 1 0)) (by decide +kernel)
  have a5242 := h.atomAt 2673 (.mul (.n 2642) (.n 2545) (.n 2545)) (by decide +kernel)
  have a5243 := h.atomAt 2674 (.mul (.n 2643) (.n 2642) (.n 2545)) (by decide +kernel)
  have a5244 := h.atomAt 2675 (.mul (.n 2644) (.n 2643) (.n 2643)) (by decide +kernel)
  have a5245 := h.atomAt 2676 (.mul (.n 2645) (.n 2644) (.n 2545)) (by decide +kernel)
  have a5246 := h.atomAt 2677 (.mul (.n 2646) (.n 2628) (.n 2645)) (by decide +kernel)
  have a5247 := h.atomAt 2678 (.load (.n 2647) (.n 2646) 0) (by decide +kernel)
  have a5248 := h.atomAt 2679 (.load (.n 2648) (.n 2646) 1) (by decide +kernel)
  have a5249 := h.atomAt 2680 (.load (.n 2649) (.n 2646) 2) (by decide +kernel)
  have a5250 := h.atomAt 2681 (.load (.n 2650) (.n 2646) 3) (by decide +kernel)
  have a5251 := h.atomAt 2682 (.load (.n 2651) (.n 2646) 4) (by decide +kernel)
  have a5252 := h.atomAt 2683 (.load (.n 2652) (.n 2646) 5) (by decide +kernel)
  have a5253 := h.atomAt 2684 (.load (.n 2653) (.n 2646) 6) (by decide +kernel)
  have a5254 := h.atomAt 2685 (.const (.n 2654) (word 2 0)) (by decide +kernel)
  have a5255 := h.atomAt 2686 (.mul (.n 2655) (.n 2545) (.n 2654)) (by decide +kernel)
  have a5257 := h.atomAt 2688 (.const (.n 2657) (word 1 0)) (by decide +kernel)
  have hloop := h.callIfAt 2668 (.n 2637) name% «verify_tables_loop0» [.n 2638, .n 2545, .n 2628,
      .n 18, .n 2635, .n 2631] (by decide +kernel)
  have hcopy := h.callIfAt 2672 (.n 2640) name% «verify_tables_loop1» [.n 2641, .n 2545, .n 16,
      .n 2635, .n 2545] (by decide +kernel)
  have hchain := h.callAt 2689 "eq_prefix_chain" [.n 2656, .n 2657, .n 16, .n 700, .n 2545] []
    (by decide +kernel)
  simp only [Atom.Holds] at a5207 a5208 a5209 a5210 a5211 a5212 a5213 a5214 a5215 a5216
  simp only [Atom.Holds] at a5217 a5218 a5219 a5220 a5221 a5222 a5224 a5225 a5227 a5228
  simp only [Atom.Holds] at a5229 a5230 a5231 a5232 a5233 a5234 a5235 a5236 a5237 a5238
  simp only [Atom.Holds] at a5239 a5240 a5242 a5243 a5244 a5245 a5246 a5247 a5248 a5249
  simp only [Atom.Holds] at a5250 a5251 a5252 a5253 a5254 a5255 a5257 a5238' a5239' a5240'
  simp only [List.map_cons, List.map_nil] at hloop hcopy hchain
  refine ⟨by rw [a5216, a5214, a5212, a5213, a5215, a5211, a5210, a5209, a5208, a5207,
    tb_word_one]; ring, ?_⟩
  have hne : 0 < n → ∀ a b : E, a = 1 → b = a + gen ^ n → b ≠ 0 := by
    intro hn0 a b ha hb h0
    rw [hb, ha] at h0
    have := gen_pow_inj (by omega) (by omega)
      ((e_add_eq_zero_iff.mp h0).symm.trans (pow_zero gen).symm)
    omega
  have hB : ∀ j < n, L10B rd (σ (.n 2628)) (σ (.n 18)) (σ (.n 2635)) (σ (.n 2631)) (gen ^ j) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · intro j hj; omega
    · have hr := hloop.2 (hne hn0 (σ (.n 2636)) _ (by rw [a5238, tb_word_one]) (by rw [a5239, hgn]))
      rw [a5240, tb_word_one, hgn] at hr
      exact l10_loop hn0 (by omega) hr
  have hC : ∀ x < n, ∃ v, LoadHolds rd (σ (.n 2635)) (n - 1 - x) v ∧ LoadHolds rd (σ (.n 16)) x v := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · intro x hx; omega
    · have hr := hcopy.2 (hne hn0 (σ (.n 2639)) _ (by rw [a5238', tb_word_one]) (by rw [a5239', hgn]))
      rw [a5240', tb_word_one, hgn] at hr
      exact l11_loop hn0 (by omega) hr
  have hc0 : CapAt rd (σ (.n 2628) * gen ^ (7 * 0)) 0 1
      ((List.range 5).map fun k ↦ σ (.n (2606 + k))) := by
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
  have hcur0 : LoadHolds rd (σ (.n 2628) * gen ^ (7 * 0)) 5 (σ (.n 1898) * gen) := by
    rw [Nat.mul_zero, pow_zero, mul_one, ← tb_word_gen, ← a5232, ← a5233]
    exact a5234
  have hcl0 : LoadHolds rd (σ (.n 2628) * gen ^ (7 * 0)) 6 (σ (.n 2621)) := by
    rw [Nat.mul_zero, pow_zero, mul_one]; exact a5235
  obtain ⟨xs, pts, claimN, capN, hrun, hxs, hxl, hpl, hcN, hcurN, hclN, hchi⟩ :=
    l10_chain (by omega) hB n le_rfl 0 (by omega) _ _ _ hc0 hcur0 hcl0
  have e5926 : σ (.n 2646) = σ (.n 2628) * gen ^ (7 * n) := by
    rw [a5246, a5245, a5244, a5243, a5242, hgn]; ring
  have hcF : CapAt rd (σ (.n 2628) * gen ^ (7 * n)) 0 1
      ((List.range 5).map fun k ↦ σ (.n (2647 + k))) := by
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
    tb_loadHolds_unique a5252 hcurN, tb_loadHolds_unique a5253 hclN, fun i hi => ?_, ?_, ?_⟩
  · obtain ⟨v, hv, hcv⟩ := hC (n - 1 - i) (by omega)
    rw [show n - 1 - (n - 1 - i) = i by omega] at hv
    rw [tb_loadHolds_unique hv (by simpa using hchi i hi)] at hcv
    exact hcv
  · intro j hj
    induction j with
    | zero =>
      rw [a5236, tb_word_one] at a5237
      simpa using a5237
    | succ j ih =>
      obtain ⟨-, -, -, -, rk, -, -, -, -, -, hrk, cp, hcp, hcp1⟩ := hB j (by omega)
      rw [tb_loadHolds_mul_gen_pow, Nat.add_zero] at hrk
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
