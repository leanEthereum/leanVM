/-
  LeanVM.Guest.B1.Opening.NovelEval

  The guest's `novel_eval` over the unnormalized subspace chain, its coefficients carrying the
  normalizers, is the verifier's `novelEval` at `subspaceAt`.
-/

module

public import LeanVM.Guest.B1.Opening.NovelSum
public import LeanVM.Guest.B1.Opening.Residual
public import LeanVM.Protocol.Whir.Sound.Novel

/-!
# `novel_eval` against the verifier's `novelEval`

The verifier evaluates coefficients `cs` at `x` as `novelEval cs (subspaceAt μ x)`, the
normalized `Ŵ_i(x) = W_i(x)/W_i(β_i)`. The guest folds them over the unnormalized chain
`W_0 = x`, `W_(i+1) = W_i (W_i + W_i(β_i))` (`wsChain` in `opening_query`, `residualChain` in
`residual_query`), coefficient `c` scaled by `Π_(i < bits, c_i = 1) W_i(β_i)⁻¹` (`hsNorm`, from
`LIG_VANISH_INVS`, `open_stacked`'s `hs`), possibly times one more scalar `s` (the high part's
`W_μ(β_μ)⁻¹`):

* `chain_vanishing`: a chain by the roots of `subspaceRoots μ` is `W_i(x)`, `i ≤ μ`
  (`wsChain_vanishing`, `residualChain_vanishing`);
* `novelSum_eq_novelEval_mul`: `novelSum hsv ws n bits = s · novelEval cs (subspaceAt μ x)` for
  `n = |cs| ≤ 2^bits`, `bits ≤ μ + 1`;
* `novelSum_eq_novelEval`: the final level's check (`s = 1`, `bits = μ + 1`, `wsChain`);
* `residual_high_eq`: the residual pass's high share, `W_μ(x)` times the fold, is
  `novelEval cs (subspaceAt μ x) · Ŵ_μ(x)` (`LevelFacts`' high term).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Sound

@[expose] public section

/-- The normalizer coefficient `c` carries: `Π_(i < bits, c_i = 1) W_i(β_i)⁻¹`, the roots of
`subspaceRoots mu`. -/
def hsNorm (mu bits c : ℕ) : K :=
  ∏ i ∈ Finset.range bits, if c.testBit i then ((Verifier.subspaceRoots mu).getD i 0)⁻¹ else 1

/-- Root `i ≤ mu` of `subspaceRoots mu` is `W_i(β_i)`. -/
theorem subspaceRoots_getD {mu i : ℕ} (h : i ≤ mu) :
    (Verifier.subspaceRoots mu).getD i 0 = vanishingAt i (basisVec i) := by
  rw [verifier_subspaceRoots_eq, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range (by omega), Option.map_some, Option.getD_some]

/-- **The unnormalized chain**: `ws 0 = x`, `ws (i + 1) = ws i (ws i + W_i(β_i))` is `W_i(x)`. -/
theorem chain_vanishing {mu : ℕ} (x : K) (ws : ℕ → E) (h0 : ws 0 = ofK x)
    (hs : ∀ i < mu, ws (i + 1) = ws i * (ws i + ofK ((Verifier.subspaceRoots mu).getD i 0))) :
    ∀ i ≤ mu, ws i = ofK (vanishingAt i x)
  | 0, _ => by rw [h0]; simp [vanishingAt]
  | i + 1, h => by
    rw [hs i (by omega), chain_vanishing x ws h0 hs i (by omega), subspaceRoots_getD (by omega),
      vanishingAt_succ, ← ofK_add, ← ofK_mul]
    congr 1
    ring

/-- `opening_query`'s chain over the roots is `W_i(x)`. -/
theorem wsChain_vanishing {mu : ℕ} (x : K) (vs : List K)
    (hvs : ∀ i < mu, vs.getD i 0 = (Verifier.subspaceRoots mu).getD i 0) :
    ∀ i ≤ mu, wsChain vs (ofK x) i = ofK (vanishingAt i x) :=
  chain_vanishing x _ rfl fun i hi ↦ by rw [wsChain, hvs i hi]

/-- `residual_query`'s chain over the roots (as words) is `W_i(x)`. -/
theorem residualChain_vanishing {mu : ℕ} (x : K) (vals : List E)
    (hv : ∀ i < mu, vals.getD i 0 = ofK ((Verifier.subspaceRoots mu).getD i 0)) :
    ∀ i ≤ mu, residualChain vals (ofK x) i = ofK (vanishingAt i x) :=
  chain_vanishing x _ rfl fun i hi ↦ by rw [residualChain, hv i hi]

/-- `X_c(x)`, `c < 2^bits`, is its normalizer times the chain's product. -/
theorem novelAt_eq_hsNorm {mu bits c : ℕ} (hmu : mu < 64) (hb : bits ≤ mu + 1) (hc : c < 2 ^ bits)
    (x : K) : novelAt c x = hsNorm mu bits c *
      ∏ i ∈ Finset.range bits, if c.testBit i then vanishingAt i x else 1 := by
  unfold novelAt hsNorm
  rw [← Finset.prod_range_mul_prod_Ico _ (show bits ≤ 64 by omega)]
  have h1 : ∏ i ∈ Finset.Ico bits 64, (if c.testBit i then normVanishingAt i x else 1) = 1 :=
    Finset.prod_eq_one fun i hi ↦ by
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hc
        (Nat.pow_le_pow_right (by norm_num) (Finset.mem_Ico.1 hi).1))]
      simp
  rw [h1, mul_one, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  rw [subspaceRoots_getD (by have := Finset.mem_range.1 hi; omega)]
  split <;> simp [normVanishingAt, mul_comm]

/-- **`novel_eval` is the verifier's `novelEval`**, up to the scalar `s` every coefficient
carries besides its normalizer. -/
theorem novelSum_eq_novelEval_mul {mu bits : ℕ} (hmu : mu < 64) (hb : bits ≤ mu + 1) (x : K)
    (cs hsv : List E) (s : E) (hn : cs.length ≤ 2 ^ bits) (hlen : hsv.length = cs.length)
    (ws : ℕ → E) (hws : ∀ i < bits, ws i = ofK (vanishingAt i x))
    (hhs : ∀ c < cs.length, hsv.getD c 0 = cs.getD c 0 * s * ofK (hsNorm mu bits c)) :
    novelSum hsv ws cs.length bits = s * Verifier.novelEval cs (Verifier.subspaceAt mu x) := by
  have hn' : cs.length ≤ 2 ^ (mu + 1) := le_trans hn (Nat.pow_le_pow_right (by norm_num) hb)
  rw [novelSum_eq, novelEval_eq hmu cs hn' x, eval_polyOf, Finset.mul_sum,
    ← Finset.sum_subset (Finset.range_mono hn) fun c _ hc ↦ by
      rw [Finset.mem_range, not_lt] at hc
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega), Option.getD_none,
        zero_mul]]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  have hc' := Finset.mem_range.1 hc
  have hbp : bitProd ws 0 bits c =
      ofK (∏ i ∈ Finset.range bits, if c.testBit i then vanishingAt i x else 1) := by
    show _ = algebraMap K E _
    rw [bitProd, map_prod]
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    split
    · rw [Nat.zero_add, hws i (Finset.mem_range.1 hi)]; rfl
    · simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hc', ← List.getD_eq_getElem?_getD,
    hhs c hc', hbp, novelAt_eq_hsNorm hmu hb (by omega) x, ofK_mul]
  ring

/-- **The final level's check** (`opening_query`, `final = 1`): `novel_eval` of the normalized
coefficients over `wsChain` at `x` is the verifier's `novelEval cs (subspaceAt mu x)`. -/
theorem novelSum_eq_novelEval {mu : ℕ} (hmu : mu < 64) (x : K) (vs : List K)
    (hvs : ∀ i < mu, vs.getD i 0 = (Verifier.subspaceRoots mu).getD i 0) (cs hsv : List E)
    (hn : cs.length ≤ 2 ^ (mu + 1)) (hlen : hsv.length = cs.length)
    (hhs : ∀ c < cs.length, hsv.getD c 0 = cs.getD c 0 * ofK (hsNorm mu (mu + 1) c)) :
    novelSum hsv (wsChain vs (ofK x)) cs.length (mu + 1) =
      Verifier.novelEval cs (Verifier.subspaceAt mu x) := by
  rw [novelSum_eq_novelEval_mul hmu le_rfl x cs hsv 1 hn hlen _
    (fun i hi ↦ wsChain_vanishing x vs hvs i (by omega)) (fun c hc ↦ by rw [mul_one]; exact hhs c hc),
    one_mul]

/-- **The residual pass's high share** (`residual_query`): `W_μ(x)` times `novel_eval` of the
high coefficients, each carrying `W_μ(β_μ)⁻¹` and its normalizer, is
`novelEval cs (subspaceAt μ x) · Ŵ_μ(x)`. -/
theorem residual_high_eq {mu bits : ℕ} (hmu : mu < 64) (hb : bits ≤ mu + 1) (x : K)
    (vals : List E) (hv : ∀ i < mu, vals.getD i 0 = ofK ((Verifier.subspaceRoots mu).getD i 0))
    (cs hsv : List E) (hn : cs.length ≤ 2 ^ bits) (hlen : hsv.length = cs.length)
    (hhs : ∀ c < cs.length, hsv.getD c 0 =
      cs.getD c 0 * ofK ((Verifier.subspaceRoots mu).getD mu 0)⁻¹ * ofK (hsNorm mu bits c)) :
    residualChain vals (ofK x) mu * novelSum hsv (residualChain vals (ofK x)) cs.length bits =
      Verifier.novelEval cs (Verifier.subspaceAt mu x) * ofK ((Verifier.subspaceAt mu x).getD mu 0) := by
  rw [novelSum_eq_novelEval_mul hmu hb x cs hsv _ hn hlen _
    (fun i hi ↦ residualChain_vanishing x vals hv i (by omega)) hhs,
    residualChain_vanishing x vals hv mu le_rfl, subspaceRoots_getD le_rfl, subspaceAt_eq,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega), Option.map_some,
    Option.getD_some, normVanishingAt, ofK_mul]
  ring

end
end LeanVM.Guest.B1
