/-
  LeanVM.Guest.B1.Tables.Vt.ZcRun

  `verify_tables`' table sumcheck from its target: the batching challenge's powers, the target
  from the three sides' totals, the first record, the rounds, the last record, the challenges'
  running products and the prefix equality weights.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Rounds
public import LeanVM.Guest.B1.Eq.EqPrefix

/-!
# The table sumcheck (G:2366-2413)

`vt_zc_run`: with `ξ = zc_xi` and the sides' totals `T_s`, the target `ξ²·T_0 + ξ³·T_1 + ξ⁴·T_2`
runs `n` plain rounds from the sponge after the bus words, reading `3n` words after the five; the
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

/-- **The table sumcheck.** -/
theorem vt_zc_run {rd : Reader} {σ : Val} (h : VtH rd σ) {n : ℕ} (hn : n < 33)
    (hgn : σ (.n 2516) = gen ^ n) :
    σ (.n 2598) = σ (.n 2588) ^ 2 * σ (.n 1820) + σ (.n 2588) ^ 3 * σ (.n 2073) +
      σ (.n 2588) ^ 4 * σ (.n 2515) ∧
    ∃ (xs pts : List E) (claimN : E),
      RunsTo (sumcheck (σ (.n 2598)) 4 (List.replicate n none))
        ⟨(List.range 5).map fun k ↦ σ (.n (2577 + k)), []⟩ xs (pts, claimN)
        ⟨(List.range 5).map fun k ↦ σ (.n (2620 + k)), []⟩ ∧
      ReadsAt rd (σ (.n 5) * gen ^ 5) xs ∧ xs.length = 3 * n ∧ pts.length = n ∧
      σ (.n 2625) = σ (.n 5) * gen ^ 5 * gen ^ (3 * n) ∧ σ (.n 2626) = claimN ∧
      (∀ i < n, LoadHolds rd (σ (.n 16)) (n - 1 - i) (pts.getD i 0)) ∧
      (∀ j ≤ n, LoadHolds rd (σ (.n 2608)) j ((pts.take j).prod)) ∧
      EqPrefix rd (σ (.n 2629)) 1 (σ (.n 16)) (σ (.n 703)) n := by
  have a5207 := h.atomAt 2636 (.const (.n 2589) (word 1 0 0)) (by decide +kernel)
  have a5208 := h.atomAt 2637 (.mul (.n 2590) (.n 2589) (.n 2588)) (by decide +kernel)
  have a5209 := h.atomAt 2638 (.mul (.n 2591) (.n 2590) (.n 2588)) (by decide +kernel)
  have a5210 := h.atomAt 2639 (.mul (.n 2592) (.n 2591) (.n 2588)) (by decide +kernel)
  have a5211 := h.atomAt 2640 (.mul (.n 2593) (.n 2592) (.n 2588)) (by decide +kernel)
  have a5212 := h.atomAt 2641 (.mul (.n 2594) (.n 2591) (.n 1820)) (by decide +kernel)
  have a5213 := h.atomAt 2642 (.mul (.n 2595) (.n 2592) (.n 2073)) (by decide +kernel)
  have a5214 := h.atomAt 2643 (.add (.n 2596) (.n 2594) (.n 2595)) (by decide +kernel)
  have a5215 := h.atomAt 2644 (.mul (.n 2597) (.n 2593) (.n 2515)) (by decide +kernel)
  have a5216 := h.atomAt 2645 (.add (.n 2598) (.n 2596) (.n 2597)) (by decide +kernel)
  have a5217 := h.atomAt 2646 (.const (.n 2599) (word 2 0 0)) (by decide +kernel)
  have a5218 := h.atomAt 2647 (.mul (.n 2600) (.n 2516) (.n 2599)) (by decide +kernel)
  have a5219 := h.atomAt 2648 (.mul (.n 2601) (.n 2600) (.n 2600)) (by decide +kernel)
  have a5220 := h.atomAt 2649 (.mul (.n 2602) (.n 2601) (.n 2600)) (by decide +kernel)
  have a5221 := h.atomAt 2650 (.mul (.n 2603) (.n 2602) (.n 2602)) (by decide +kernel)
  have a5222 := h.atomAt 2651 (.mul (.n 2604) (.n 2603) (.n 2600)) (by decide +kernel)
  have a5224 := h.atomAt 2653 (.const (.n 2606) (word 2 0 0)) (by decide +kernel)
  have a5225 := h.atomAt 2654 (.mul (.n 2607) (.n 2516) (.n 2606)) (by decide +kernel)
  have a5227 := h.atomAt 2656 (.load (.n 2577) (.n 2605) 0) (by decide +kernel)
  have a5228 := h.atomAt 2657 (.load (.n 2578) (.n 2605) 1) (by decide +kernel)
  have a5229 := h.atomAt 2658 (.load (.n 2579) (.n 2605) 2) (by decide +kernel)
  have a5230 := h.atomAt 2659 (.load (.n 2580) (.n 2605) 3) (by decide +kernel)
  have a5231 := h.atomAt 2660 (.load (.n 2581) (.n 2605) 4) (by decide +kernel)
  have a5232 := h.atomAt 2661 (.const (.n 2609) (word 32 0 0)) (by decide +kernel)
  have a5233 := h.atomAt 2662 (.mul (.n 2610) (.n 5) (.n 2609)) (by decide +kernel)
  have a5234 := h.atomAt 2663 (.load (.n 2610) (.n 2605) 5) (by decide +kernel)
  have a5235 := h.atomAt 2664 (.load (.n 2598) (.n 2605) 6) (by decide +kernel)
  have a5236 := h.atomAt 2665 (.const (.n 2611) (word 1 0 0)) (by decide +kernel)
  have a5237 := h.atomAt 2666 (.load (.n 2611) (.n 2608) 0) (by decide +kernel)
  have a5238 := h.atomAt 2667 (.const (.n 2612) (word 1 0 0)) (by decide +kernel)
  have a5239 := h.atomAt 2668 (.add (.n 2613) (.n 2612) (.n 2516)) (by decide +kernel)
  have a5240 := h.atomAt 2669 (.const (.n 2614) (word 1 0 0)) (by decide +kernel)
  have a5242 := h.atomAt 2671 (.mul (.n 2615) (.n 2516) (.n 2516)) (by decide +kernel)
  have a5243 := h.atomAt 2672 (.mul (.n 2616) (.n 2615) (.n 2516)) (by decide +kernel)
  have a5244 := h.atomAt 2673 (.mul (.n 2617) (.n 2616) (.n 2616)) (by decide +kernel)
  have a5245 := h.atomAt 2674 (.mul (.n 2618) (.n 2617) (.n 2516)) (by decide +kernel)
  have a5246 := h.atomAt 2675 (.mul (.n 2619) (.n 2605) (.n 2618)) (by decide +kernel)
  have a5247 := h.atomAt 2676 (.load (.n 2620) (.n 2619) 0) (by decide +kernel)
  have a5248 := h.atomAt 2677 (.load (.n 2621) (.n 2619) 1) (by decide +kernel)
  have a5249 := h.atomAt 2678 (.load (.n 2622) (.n 2619) 2) (by decide +kernel)
  have a5250 := h.atomAt 2679 (.load (.n 2623) (.n 2619) 3) (by decide +kernel)
  have a5251 := h.atomAt 2680 (.load (.n 2624) (.n 2619) 4) (by decide +kernel)
  have a5252 := h.atomAt 2681 (.load (.n 2625) (.n 2619) 5) (by decide +kernel)
  have a5253 := h.atomAt 2682 (.load (.n 2626) (.n 2619) 6) (by decide +kernel)
  have a5254 := h.atomAt 2683 (.const (.n 2627) (word 2 0 0)) (by decide +kernel)
  have a5255 := h.atomAt 2684 (.mul (.n 2628) (.n 2516) (.n 2627)) (by decide +kernel)
  have a5257 := h.atomAt 2686 (.const (.n 2630) (word 1 0 0)) (by decide +kernel)
  have hloop := h.callIfAt 2670 (.n 2613) "__loop9" [.n 2614, .n 2516, .n 2605, .n 16, .n 2516,
    .n 2608] (by decide +kernel)
  have hchain := h.callAt 2687 "eq_prefix_chain" [.n 2629, .n 2630, .n 16, .n 703, .n 2516] []
    (by decide +kernel)
  simp only [Atom.Holds] at a5207 a5208 a5209 a5210 a5211 a5212 a5213 a5214 a5215 a5216
  simp only [Atom.Holds] at a5217 a5218 a5219 a5220 a5221 a5222 a5224 a5225 a5227 a5228
  simp only [Atom.Holds] at a5229 a5230 a5231 a5232 a5233 a5234 a5235 a5236 a5237 a5238
  simp only [Atom.Holds] at a5239 a5240 a5242 a5243 a5244 a5245 a5246 a5247 a5248 a5249
  simp only [Atom.Holds] at a5250 a5251 a5252 a5253 a5254 a5255 a5257
  simp only [List.map_cons, List.map_nil] at hloop hchain
  refine ⟨by rw [a5216, a5214, a5212, a5213, a5215, a5211, a5210, a5209, a5208, a5207,
    tb_word_one]; ring, ?_⟩
  have hB : ∀ j < n, L10B rd (σ (.n 2605)) (σ (.n 16)) (gen ^ n) (σ (.n 2608)) (gen ^ j) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · intro j hj; omega
    · have hne : σ (.n 2613) ≠ 0 := by
        rw [a5239, a5238, tb_word_one, hgn]
        intro h0
        have := gen_pow_inj (by omega) (by omega)
          ((e_add_eq_zero_iff.mp h0).symm.trans (pow_zero gen).symm)
        omega
      have hr := hloop.2 hne
      rw [a5240, tb_word_one, hgn] at hr
      exact l10_loop hn0 (by omega) hr
  have hc0 : CapAt rd (σ (.n 2605) * gen ^ (7 * 0)) 0 1
      ((List.range 5).map fun k ↦ σ (.n (2577 + k))) := by
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
  have hcur0 : LoadHolds rd (σ (.n 2605) * gen ^ (7 * 0)) 5 (σ (.n 5) * gen ^ 5) := by
    rw [Nat.mul_zero, pow_zero, mul_one, ← tb_word_two_pow (by norm_num),
      show (2 : ℕ) ^ 5 = 32 by norm_num, ← a5232, ← a5233]
    exact a5234
  have hcl0 : LoadHolds rd (σ (.n 2605) * gen ^ (7 * 0)) 6 (σ (.n 2598)) := by
    rw [Nat.mul_zero, pow_zero, mul_one]; exact a5235
  obtain ⟨xs, pts, claimN, capN, hrun, hxs, hxl, hpl, hcN, hcurN, hclN, hchi⟩ :=
    l10_chain (by omega) hB n le_rfl 0 (by omega) _ _ _ hc0 hcur0 hcl0
  have e5926 : σ (.n 2619) = σ (.n 2605) * gen ^ (7 * n) := by
    rw [a5246, a5245, a5244, a5243, a5242, hgn]; ring
  have hcF : CapAt rd (σ (.n 2605) * gen ^ (7 * n)) 0 1
      ((List.range 5).map fun k ↦ σ (.n (2620 + k))) := by
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
