/-
  LeanVM.Protocol.Whir.Complete.Rounds

  One honest affine fold round on the prover's tables: its lanes fold as the verifier folds an
  opened row, and its table carries the running claim.
-/

module

public import LeanVM.Protocol.Whir.Complete.MulX
public import LeanVM.Prover.WhirTables

/-!
# An honest fold round

The prover's tables (`Statement/Prover/Whir.lean`) hold `2^(m+1)` lanes, coefficient `c` of lane
`l` at `c·2^(m+1) + l`; a round pairs lanes `2l` and `2l + 1` (`F`, `G`), and since the stride
halves, every read is at an adjacent pair: `H[i] = f[2i] + θ f[2i+1]` (`getD_premixA`), the folded
`f'[i] = f[2i+1] + α H[i] + β (XH)[i]` (`getD_foldLanesA`), `(XH)[c·2^m + l]` the rule of
`mul_x` on lane `l` of `H` (`getD_mulXA`).

* `laneVal t m l x`: lane `l` of a table of `2^m` lanes at the domain point `x`, `Σ_c t[c·2^m + l]
  X_c(x)`. `laneVal_fold`: the folded lane is `G(x) + (α + β x)(F(x) + θ G(x))`, by `lem:mulx`
  (`sum_mxE`), which is how the verifier folds an opened row (`getD_foldLanes`).
* `claim_fold`: if the running claim is `Σ w·f` over the weight's coefficients, the verifier's
  next claim from the round's table, `(1 + γ)(u₀ + α v₀ + β c₀) + γ (u₁ + α v₁ + β c₁)` with
  `u₁ = claim + v₀ + θ u₀`, is `Σ w'·f'` for the folded tables.
-/

namespace LeanVM.Protocol.Whir.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
  LeanVM.Protocol.Whir LeanVM.Prover LeanVM.Prover.Enc Finset

@[expose] public section

/-! ## Index arithmetic -/

theorem two_pow_succ_div_two (m : ℕ) : 2 ^ (m + 1) / 2 = 2 ^ m := by
  rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]

theorem idx_two (i m : ℕ) : i / 2 ^ m * 2 ^ (m + 1) + 2 * (i % 2 ^ m) = 2 * i := by
  rw [pow_succ]
  have := Nat.div_add_mod i (2 ^ m)
  calc i / 2 ^ m * (2 ^ m * 2) + 2 * (i % 2 ^ m) = 2 * (2 ^ m * (i / 2 ^ m) + i % 2 ^ m) := by ring
    _ = 2 * i := by rw [this]

theorem getD_of_size_le {a : Array E} {i : ℕ} (h : a.size ≤ i) : a.getD i 0 = 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]

theorem getD_ofFn_ge {n : ℕ} (f : Fin n → E) {i : ℕ} (h : n ≤ i) : (Array.ofFn f).getD i 0 = 0 :=
  getD_of_size_le (by simpa using h)

/-! ## The tables -/

theorem size_premixA (f : Array E) {m cols : ℕ} (hf : f.size = cols * 2 ^ (m + 1)) (θ : E) :
    (premixA f (2 ^ (m + 1)) θ).size = cols * 2 ^ m := by
  simp [premixA, hf, two_pow_succ_div_two, Nat.mul_div_cancel _ (Nat.two_pow_pos (m + 1))]

theorem getD_premixA (f : Array E) {m cols : ℕ} (hf : f.size = cols * 2 ^ (m + 1)) (θ : E)
    (i : ℕ) :
    (premixA f (2 ^ (m + 1)) θ).getD i 0 = f.getD (2 * i) 0 + θ * f.getD (2 * i + 1) 0 := by
  by_cases hi : i < cols * 2 ^ m
  · have hn : i < f.size / 2 ^ (m + 1) * (2 ^ (m + 1) / 2) := by
      rwa [hf, Nat.mul_div_cancel _ (Nat.two_pow_pos _), two_pow_succ_div_two]
    rw [premixA, Enc.getD_ofFn _ _ _ hn]
    simp only [two_pow_succ_div_two, idx_two]
  · have hs := size_premixA f hf θ
    have e : f.size = 2 * (cols * 2 ^ m) := by rw [hf, pow_succ]; ring
    rw [getD_of_size_le (by omega), getD_of_size_le (by omega), getD_of_size_le (by omega)]
    ring

theorem size_mulXA (h : Array E) (s : ℕ) : (mulXA h s).size = (h.size / s + 1) * s := by
  simp [mulXA]

/-- The trailing zeros of a `c ≤ 2^62` are below `64`. -/
theorem trailingZeros_lt {c : ℕ} (hc : c ≠ 0) (hc' : c ≤ 2 ^ 62) : trailingZeros c < 64 := by
  obtain ⟨v, o, rfl⟩ := exists_two_pow_mul_odd hc
  rw [trailingZeros_two_pow_mul_odd]
  by_contra h
  have : 2 ^ 64 ≤ 2 ^ v * (2 * o + 1) :=
    (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (Nat.le_mul_of_pos_right _ (by omega))
  have : (2 : ℕ) ^ 62 < 2 ^ 64 := by norm_num
  omega

theorem getD_mulXA (h : Array E) {m cols : ℕ} (hh : h.size = cols * 2 ^ m) (hcols : cols ≤ 2 ^ 62)
    {c l : ℕ} (hc : c ≤ cols) (hl : l < 2 ^ m) :
    (mulXA h (2 ^ m)).getD (c * 2 ^ m + l) 0 = mxE (fun c' ↦ h.getD (c' * 2 ^ m + l) 0) c := by
  have hpos := Nat.two_pow_pos m
  have hi : c * 2 ^ m + l < (h.size / 2 ^ m + 1) * 2 ^ m := by
    rw [hh, Nat.mul_div_cancel _ hpos]; nlinarith
  rw [mulXA, Enc.getD_ofFn _ _ _ hi]
  have hdiv : (c * 2 ^ m + l) / 2 ^ m = c := by
    rw [add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hl, zero_add]
  have hmod : (c * 2 ^ m + l) % 2 ^ m = l := by
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]
  simp only [hdiv, hmod, mxE]
  by_cases h0 : c = 0
  · simp [h0]
  · simp only [h0, ite_false]
    rw [xmulConsts_getD (trailingZeros_lt h0 (hc.trans hcols))]

/-- **`lem:mulx` on a lane of the prover's table.** -/
theorem sum_lane_mulXA (H : Array E) {m cols : ℕ} (hH : H.size = cols * 2 ^ m)
    (hcols : cols ≤ 2 ^ 62) {l : ℕ} (hl : l < 2 ^ m) (x : K) :
    ∑ c ∈ range (cols + 1), (mulXA H (2 ^ m)).getD (c * 2 ^ m + l) 0 * ofK (novelAt c x) =
      ofK x * ∑ c ∈ range cols, H.getD (c * 2 ^ m + l) 0 * ofK (novelAt c x) := by
  rw [sum_congr rfl fun c hc ↦ by
    rw [getD_mulXA H hH hcols (Nat.lt_succ_iff.mp (mem_range.mp hc)) hl]]
  refine sum_mxE _ cols hcols (fun c hc ↦ getD_of_size_le ?_) x
  rw [hH]; nlinarith [Nat.two_pow_pos m]

theorem getD_foldLanesA (f : Array E) (m : ℕ) (H XH : Array E) (α β : E) {i : ℕ}
    (hi : i < XH.size) :
    (foldLanesA f (2 ^ (m + 1)) H XH α β).getD i 0 =
      f.getD (2 * i + 1) 0 + α * H.getD i 0 + β * XH.getD i 0 := by
  rw [foldLanesA, Enc.getD_ofFn _ _ _ hi]
  simp only [two_pow_succ_div_two, idx_two]

/-! ## Lanes -/

/-- Lane `l` of a table of `2^m` lanes at the domain point `x`. -/
noncomputable def laneVal (t : Array E) (m l : ℕ) (x : K) : E :=
  ∑ c ∈ range (t.size / 2 ^ m), t.getD (c * 2 ^ m + l) 0 * ofK (novelAt c x)

/-- **The folded lane** is `G(x) + (α + β x)(F(x) + θ G(x))`. -/
theorem laneVal_fold (f : Array E) {m cols : ℕ} (hf : f.size = cols * 2 ^ (m + 1))
    (hcols : cols ≤ 2 ^ 62) (θ α β : E) {l : ℕ} (hl : l < 2 ^ m) (x : K) :
    laneVal (foldLanesA f (2 ^ (m + 1)) (premixA f (2 ^ (m + 1)) θ)
        (mulXA (premixA f (2 ^ (m + 1)) θ) (2 ^ m)) α β) m l x =
      laneVal f (m + 1) (2 * l + 1) x +
        (α + β * ofK x) * (laneVal f (m + 1) (2 * l) x + θ * laneVal f (m + 1) (2 * l + 1) x) := by
  set H := premixA f (2 ^ (m + 1)) θ
  have hH := size_premixA f hf θ
  have hpos := Nat.two_pow_pos m
  have hXH : (mulXA H (2 ^ m)).size = (cols + 1) * 2 ^ m := by
    rw [size_mulXA, hH, Nat.mul_div_cancel _ hpos]
  have hsz : (foldLanesA f (2 ^ (m + 1)) H (mulXA H (2 ^ m)) α β).size = (cols + 1) * 2 ^ m := by
    rw [← hXH]; simp [foldLanesA]
  have hidx : ∀ c, 2 * (c * 2 ^ m + l) = c * 2 ^ (m + 1) + 2 * l := fun c ↦ by rw [pow_succ]; ring
  have hfdiv : f.size / 2 ^ (m + 1) = cols := by rw [hf, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  -- The three sums, over `cols + 1` columns (the last one empty for `f` and `H`).
  have hG : ∑ c ∈ range (cols + 1), f.getD (c * 2 ^ (m + 1) + (2 * l + 1)) 0 * ofK (novelAt c x) =
      laneVal f (m + 1) (2 * l + 1) x := by
    rw [laneVal, hfdiv, sum_range_succ, getD_of_size_le (by rw [hf]; omega), zero_mul, add_zero]
  have hHc : ∑ c ∈ range cols, H.getD (c * 2 ^ m + l) 0 * ofK (novelAt c x) =
      laneVal f (m + 1) (2 * l) x + θ * laneVal f (m + 1) (2 * l + 1) x := by
    rw [laneVal, laneVal, hfdiv, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun c _ ↦ ?_
    rw [getD_premixA f hf θ, hidx, ← add_assoc]
    ring
  have hH1 : ∑ c ∈ range (cols + 1), H.getD (c * 2 ^ m + l) 0 * ofK (novelAt c x) =
      laneVal f (m + 1) (2 * l) x + θ * laneVal f (m + 1) (2 * l + 1) x := by
    rw [sum_range_succ, getD_of_size_le (by rw [hH]; omega), zero_mul, add_zero, hHc]
  have hX := sum_lane_mulXA H hH hcols hl x
  rw [laneVal, hsz, Nat.mul_div_cancel _ hpos]
  calc ∑ c ∈ range (cols + 1), (foldLanesA f (2 ^ (m + 1)) H (mulXA H (2 ^ m)) α β).getD
          (c * 2 ^ m + l) 0 * ofK (novelAt c x)
      = ∑ c ∈ range (cols + 1), (f.getD (c * 2 ^ (m + 1) + (2 * l + 1)) 0 * ofK (novelAt c x) +
          α * (H.getD (c * 2 ^ m + l) 0 * ofK (novelAt c x)) +
          β * ((mulXA H (2 ^ m)).getD (c * 2 ^ m + l) 0 * ofK (novelAt c x))) := by
        refine sum_congr rfl fun c hc ↦ ?_
        have hc' : c * 2 ^ m + l < (mulXA H (2 ^ m)).size := by
          rw [hXH]; have := mem_range.mp hc; nlinarith
        rw [getD_foldLanesA f m H _ α β hc', hidx, ← add_assoc]
        ring
    _ = _ := by
        rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, hG, hH1, hX, hHc]
        ring

/-! ## The verifier's lane fold -/

theorem length_foldLanes (x : K) (r : FoldRound) : ∀ v : List E,
    (foldLanes x r v).length = v.length / 2
  | f :: g :: rest => by
    rw [foldLanes, List.length_cons, length_foldLanes x r rest]; simp; omega
  | [] => rfl
  | [_] => by simp [foldLanes]

theorem getD_foldLanes (x : K) (r : FoldRound) : ∀ (v : List E) (l : ℕ), 2 * l + 1 < v.length →
    (foldLanes x r v).getD l 0 = v.getD (2 * l + 1) 0 +
      (r.alpha + r.beta * ofK x) * (v.getD (2 * l) 0 + r.theta * v.getD (2 * l + 1) 0)
  | f :: g :: rest, 0, _ => by simp [foldLanes]
  | f :: g :: rest, l + 1, h => by
    rw [foldLanes, List.getD_cons_succ, getD_foldLanes x r rest l (by simp at h; omega)]
    simp only [show 2 * (l + 1) = 2 * l + 1 + 1 by ring, List.getD_cons_succ]
  | [], _, h => by simp at h
  | [_], _, h => by simp at h

/-! ## The claim -/

/-- **The running claim through a round.** -/
theorem claim_fold (f w : Array E) {m cols k : ℕ} (hf : f.size = cols * 2 ^ (m + 1))
    (hw : w.size = 2 ^ k * 2 ^ (m + 1)) (hk : 2 ^ k ≤ cols) (θ γ α β claim : E)
    (hclaim : claim = ∑ i ∈ range w.size, w.getD i 0 * f.getD i 0) (u₀ v₀ c₀ v₁ c₁ : E)
    (ht : roundTableA f w (2 ^ (m + 1)) (premixA f (2 ^ (m + 1)) θ)
      (mulXA (premixA f (2 ^ (m + 1)) θ) (2 ^ m)) = [u₀, v₀, c₀, v₁, c₁]) :
    (1 + γ) * (u₀ + α * v₀ + β * c₀) + γ * ((claim + v₀ + θ * u₀) + α * v₁ + β * c₁) =
      ∑ i ∈ range (foldPairsA γ w).size, (foldPairsA γ w).getD i 0 *
        (foldLanesA f (2 ^ (m + 1)) (premixA f (2 ^ (m + 1)) θ)
          (mulXA (premixA f (2 ^ (m + 1)) θ) (2 ^ m)) α β).getD i 0 := by
  set H := premixA f (2 ^ (m + 1)) θ
  set XH := mulXA H (2 ^ m)
  set n := 2 ^ k * 2 ^ m with hn
  have hpos := Nat.two_pow_pos m
  have hH := size_premixA f hf θ
  have hXH : XH.size = (cols + 1) * 2 ^ m := by
    rw [size_mulXA, hH, Nat.mul_div_cancel _ hpos]
  have hw2 : w.size = 2 * n := by rw [hw, hn, pow_succ]; ring
  have hnw : w.size / 2 ^ (m + 1) * 2 ^ m = n := by
    rw [hw, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  have hwsz : (foldPairsA γ w).size = n := by simp [foldPairsA, hw2]
  simp only [roundTableA, two_pow_succ_div_two, idx_two, sumRange_eq, List.cons.injEq,
    and_true, hnw] at ht
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := ht
  have hin : ∀ i ∈ range n, i < XH.size := fun i hi ↦ by
    rw [hXH]; have := mem_range.mp hi
    calc i < 2 ^ k * 2 ^ m := this
      _ ≤ (cols + 1) * 2 ^ m := Nat.mul_le_mul_right _ (by omega)
  rw [hclaim, hw2, sum_range_two_mul, hwsz]
  have key : ∀ i ∈ range n, (foldPairsA γ w).getD i 0 *
      (foldLanesA f (2 ^ (m + 1)) H XH α β).getD i 0 =
      (1 + γ) * (w.getD (2 * i) 0 * f.getD (2 * i + 1) 0 + α * (w.getD (2 * i) 0 * H.getD i 0) +
          β * (w.getD (2 * i) 0 * XH.getD i 0)) +
        γ * (((w.getD (2 * i) 0 * f.getD (2 * i) 0 + w.getD (2 * i + 1) 0 * f.getD (2 * i + 1) 0) +
          w.getD (2 * i) 0 * H.getD i 0 + θ * (w.getD (2 * i) 0 * f.getD (2 * i + 1) 0)) +
          α * (w.getD (2 * i + 1) 0 * H.getD i 0) + β * (w.getD (2 * i + 1) 0 * XH.getD i 0)) := by
    intro i hi
    rw [getD_foldPairsA γ w (by rw [hw2]; simpa using mem_range.mp hi),
      getD_foldLanesA f m H XH α β (hin i hi), getD_premixA f hf θ]
    have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
    linear_combination (-(γ * w.getD (2 * i) 0 * (f.getD (2 * i) 0 + θ * f.getD (2 * i + 1) 0))) * h2
  rw [sum_congr rfl key]
  simp only [sum_add_distrib, ← mul_sum]

end
end LeanVM.Protocol.Whir.Complete
