module

public import Quantum.StdModel.Qrom.EncSaltFirst

@[expose] public section

/-!
# EncTCR$ in the QROM: reads that move later weights

A refinement of the step bounds of `EncSaltFirst` for weights that a read may move.

* **A cell read with slack** (`re_trace_gramW_le_slack`, `sum_ofReal_readH_le_slack`): if every
  outcome's weight after the read of an unhardwired cell, at every content `a` of the cell, is at
  most `H` of the state before plus `κ` when `a` is neither empty nor the outcome, the weights
  after the read are at most the weight of `H + κ/N + κ · [the cell is recorded]`. The compressed
  outcome `o` carries at most `1/N` of its mass off `{⊥, o}`, and the decompressed-`⊥` outcome at
  most the recorded mass of the cell (`re_cellV_none_le`).
* **A grind with moving weights** (`step₂_grind_slack`): stage potentials `Pt c` at the trials,
  each trial's read paying its weight `f c` and the slack `κ c` of the later stages.
-/

open IPFunctor Matrix
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.StdModel.Qrom.EncSalt.Code

open Quantum QuantumRuntime Quantum.Sponge

/-! ## A cell read with slack -/

section gramSlack

open Quantum.Xmss.Assembly (gramW_apply gramW_off sum_cr_mul_cr re_cross_le)

variable {n Y R M0 : Type} [Fintype n] [DecidableEq n] [Fintype Y] [DecidableEq Y]
  [Fintype R] [DecidableEq R] [Fintype M0] [DecidableEq M0]
  {e : n ≃ Option Y × R} {act : R → Prop} [DecidablePred act] {μ : R → M0}
  {τ : Option Y → R → R} {K : Option Y × M0 → Matrix n n ℂ} {idx : n → Option Y × M0}
  {φ : n → n}

omit [Fintype n] [DecidableEq n] in
/-- **The decompressed-`⊥` outcome weighs at most the recorded mass of the cell.** -/
theorem re_cellV_none_le [Nonempty Y] {σ : Matrix n n ℂ} (hσ : σ.PosSemidef)
    (f : Option Y → n) :
    (∑ a', ∑ a, ((cr none a' * cr a none : ℝ) : ℂ) * σ (f a') (f a)).re ≤
      ∑ a, (if a = none then 0 else 1) * (σ (f a) (f a)).re := by
  have hN : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.2 Fintype.card_pos
  have h1 : ∑ a', ∑ a, ((cr none a' * cr a none : ℝ) : ℂ) * σ (f a') (f a) =
      ∑ y', ∑ y, (((Fintype.card Y : ℝ)⁻¹ : ℝ) : ℂ) * σ (f (some y')) (f (some y)) := by
    rw [Fintype.sum_option]
    simp only [cr, zero_mul, Complex.ofReal_zero, Finset.sum_const_zero, zero_add]
    refine Finset.sum_congr rfl fun y' _ ↦ ?_
    rw [Fintype.sum_option]
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [inv_sqrt_mul_inv_sqrt_card]
  have h2 : ∑ a, (if a = none then (0 : ℝ) else 1) * (σ (f a) (f a)).re =
      ∑ y, (σ (f (some y)) (f (some y))).re := by
    rw [Fintype.sum_option]
    simp
  rw [h1, h2]
  have hc : ∀ y' y, (σ (f (some y')) (f (some y)) + σ (f (some y)) (f (some y'))).re ≤
      (σ (f (some y')) (f (some y'))).re + (σ (f (some y)) (f (some y))).re := fun y' y ↦ by
    simpa using re_cross_le hσ (f (some y')) (f (some y)) 1
  have hswap : ∑ y', ∑ y, (σ (f (some y)) (f (some y'))).re =
      ∑ y', ∑ y, (σ (f (some y')) (f (some y))).re := Finset.sum_comm
  have hL : ∑ y', ∑ y, (σ (f (some y')) (f (some y)) + σ (f (some y)) (f (some y'))).re =
      2 * (∑ y', ∑ y, σ (f (some y')) (f (some y))).re := by
    simp only [Complex.add_re, Finset.sum_add_distrib, Complex.re_sum]
    linarith [hswap]
  have hR : ∑ y', ∑ y, ((σ (f (some y')) (f (some y'))).re + (σ (f (some y)) (f (some y))).re) =
      2 * (Fintype.card Y * ∑ y, (σ (f (some y)) (f (some y))).re) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum]
    ring
  have hsum := Finset.sum_le_sum fun y' (_ : y' ∈ Finset.univ) ↦
    Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) ↦ hc y' y
  rw [hL, hR] at hsum
  have hX : (∑ y', ∑ y, (((Fintype.card Y : ℝ)⁻¹ : ℝ) : ℂ) * σ (f (some y')) (f (some y))).re =
      (Fintype.card Y : ℝ)⁻¹ * (∑ y', ∑ y, σ (f (some y')) (f (some y))).re := by
    simp only [← Finset.mul_sum, Complex.re_ofReal_mul]
  rw [hX, inv_mul_le_iff₀ hN]
  linarith

/-- **A cell read with outcome-dependent weights and slack**: if on every active rest every
outcome's weight after the read, through the compression's column, is at most `H` at every content
of the cell before the read, plus `κ/N`, plus `κ` at the decompressed-`⊥` outcome, and the
hardwired columns' classical moves are at most `H`, the weights after the read are at most the
weight of `H + κ/N + κ · [the cell is recorded]`. -/
theorem re_trace_gramW_le_slack [Nonempty Y] (h : CellRead e act μ τ K)
    (hc : ClsOff e act K idx φ) (w : Option Y → n → ℝ) (H : n → ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hact : ∀ r, act r → ∀ o a', ∑ a, cr a o ^ 2 * w o (e.symm (a, τ o r)) ≤
      H (e.symm (a', r)) + κ / Fintype.card Y + if o = none then κ else 0)
    (hoff : ∀ s, ¬ act (e s).2 → w (idx s).1 (φ s) ≤ H s)
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    ((∑ i, (K i)ᴴ * diagonal (fun u ↦ ((w i.1 u : ℝ) : ℂ)) * K i) * σ).trace.re ≤
      ∑ s, (H s + κ / Fintype.card Y + if (e s).1 = none then 0 else κ) * (σ s s).re := by
  have hκN : 0 ≤ κ / Fintype.card Y := div_nonneg hκ (Nat.cast_nonneg _)
  obtain ⟨G, hG⟩ : ∃ G : Matrix n n ℂ,
      G = ∑ i, (K i)ᴴ * diagonal (fun u ↦ ((w i.1 u : ℝ) : ℂ)) * K i := ⟨_, rfl⟩
  rw [← hG]
  have hGa : ∀ s, act (e s).2 → ∀ t, G t s = if (e t).2 = (e s).2 then
      ((∑ o, cr (e t).1 o * (∑ a, cr a o ^ 2 * w o (e.symm (a, τ o (e s).2))) *
        cr o (e s).1 : ℝ) : ℂ) else 0 :=
    fun s hs t ↦ by rw [hG]; exact gramW_apply h w hs t
  have hGo : ∀ s, ¬ act (e s).2 → ∀ t,
      G t s = if t = s then ((w (idx s).1 (φ s) : ℝ) : ℂ) else 0 :=
    fun s hs t ↦ by rw [hG]; exact gramW_off h hc w hs t
  have hre : ∀ s, 0 ≤ (σ s s).re := fun s ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have htr : (G * σ).trace = ∑ s, ∑ t, G t s * σ s t := by
    rw [Matrix.trace]
    simp only [diag_apply, Matrix.mul_apply]
    exact Finset.sum_comm
  have hsplit : ∀ f : n → ℝ, ∑ s, f s = ∑ r, ∑ a, f (e.symm (a, r)) := fun f ↦ by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rw [htr, Complex.re_sum, hsplit, hsplit]
  refine Finset.sum_le_sum fun r _ ↦ ?_
  simp only [Equiv.apply_symm_apply]
  by_cases hr : act r
  · obtain ⟨S, hS⟩ : ∃ S : Matrix (Option Y) (Option Y) ℂ,
        ∀ a' a, σ (e.symm (a', r)) (e.symm (a, r)) = S a' a := ⟨fun a' a ↦ _, fun _ _ ↦ rfl⟩
    obtain ⟨g, hg⟩ : ∃ g : Option Y → ℝ,
        ∀ o, ∑ b, cr b o ^ 2 * w o (e.symm (b, τ o r)) = g o := ⟨_, fun _ ↦ rfl⟩
    have hF : ∀ a', ∑ t, G t (e.symm (a', r)) * σ (e.symm (a', r)) t =
        ∑ a, ((∑ o, cr a o * g o * cr o a' : ℝ) : ℂ) * S a' a := fun a' ↦ by
      have hs : act (e (e.symm (a', r))).2 := by rw [Equiv.apply_symm_apply]; exact hr
      rw [sum_rest_eq (e := e) r fun t ht ↦ by
        rw [hGa _ hs, Equiv.apply_symm_apply, ite_eq_right ht, zero_mul]]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [hGa _ hs]
      simp only [Equiv.apply_symm_apply, ↓reduceIte, hg, hS]
    have hVc : ∑ a', ∑ a, ((∑ o, cr a o * g o * cr o a' : ℝ) : ℂ) * S a' a =
        ∑ o, (g o : ℂ) * ∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a := by
      simp only [Complex.ofReal_sum, Finset.sum_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a' _ ↦ ?_
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun o _ ↦ ?_
      push_cast
      ring
    have hVsum : ∑ o, ∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a = ∑ a, S a a := by
      calc ∑ o, ∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a
          = ∑ a', ∑ a, ∑ o, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun a' _ ↦ Finset.sum_comm
        _ = ∑ a', ∑ a, (if a = a' then 1 else 0) * S a' a := by
            refine Finset.sum_congr rfl fun a' _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
            rw [← Finset.sum_mul, sum_cr_mul_cr]
        _ = ∑ a', S a' a' := by
            refine Finset.sum_congr rfl fun a' _ ↦ ?_
            simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
              ↓reduceIte]
    have hVnn : ∀ o, 0 ≤ (∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a).re := fun o ↦ by
      have hSm := (hσ.submatrix fun a : Option Y ↦ e.symm (a, r)).dotProduct_mulVec_nonneg
        (fun a ↦ ((cr a o : ℝ) : ℂ))
      have key : star (fun a ↦ ((cr a o : ℝ) : ℂ)) ⬝ᵥ
          ((σ.submatrix (fun a : Option Y ↦ e.symm (a, r)) fun a ↦ e.symm (a, r)) *ᵥ
            fun a ↦ ((cr a o : ℝ) : ℂ)) =
          ∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a := by
        simp only [dotProduct, mulVec, submatrix_apply, Pi.star_apply, Complex.star_def,
          Complex.conj_ofReal, hS, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a' _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
        rw [cr_comm o a']
        push_cast
        ring
      rw [key] at hSm
      exact (Complex.nonneg_iff.1 hSm).1
    have hVn : (∑ a', ∑ a, ((cr none a' * cr a none : ℝ) : ℂ) * S a' a).re ≤
        ∑ a, (if a = none then 0 else 1) * (S a a).re := by
      have h0 := re_cellV_none_le hσ fun a : Option Y ↦ e.symm (a, r)
      simp only [hS] at h0
      exact h0
    set m := Finset.univ.inf' Finset.univ_nonempty fun a' : Option Y ↦ H (e.symm (a', r))
    have hgm : ∀ o, g o ≤ m + κ / Fintype.card Y + if o = none then κ else 0 := fun o ↦ by
      have h0 : g o - κ / Fintype.card Y - (if o = none then κ else 0) ≤ m :=
        Finset.le_inf' _ _ fun a' _ ↦ by
          have := hact r hr o a'
          rw [hg] at this
          show _ ≤ H (e.symm (a', r))
          linarith
      linarith
    simp only [hF]
    rw [← Complex.re_sum, hVc, Complex.re_sum]
    simp only [Complex.re_ofReal_mul, hS]
    have hRHS : ∑ a, (S a a).re =
        ∑ o, (∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a).re := by
      have h1 := congrArg Complex.re hVsum
      rw [Complex.re_sum, Complex.re_sum] at h1
      exact h1.symm
    calc ∑ o, g o * (∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a).re
        ≤ ∑ o, (m + κ / Fintype.card Y + if o = none then κ else 0) *
            (∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a).re :=
          Finset.sum_le_sum fun o _ ↦ mul_le_mul_of_nonneg_right (hgm o) (hVnn o)
      _ = (m + κ / Fintype.card Y) *
            ∑ o, (∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a).re +
          κ * (∑ a', ∑ a, ((cr none a' * cr a none : ℝ) : ℂ) * S a' a).re := by
          simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ite_mul, zero_mul,
            Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      _ ≤ (m + κ / Fintype.card Y) * ∑ a, (S a a).re +
          κ * ∑ a, (if a = none then 0 else 1) * (S a a).re := by
          rw [hRHS]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hVn hκ)
      _ ≤ ∑ a, (H (e.symm (a, r)) + κ / Fintype.card Y + if a = none then 0 else κ) *
            (S a a).re := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun a _ ↦ ?_
          have hm : m ≤ H (e.symm (a, r)) := Finset.inf'_le _ (Finset.mem_univ a)
          have h0 : 0 ≤ (S a a).re := by rw [← hS]; exact hre _
          split_ifs <;> nlinarith
  · refine Finset.sum_le_sum fun a _ ↦ ?_
    have hs : ¬ act (e (e.symm (a, r))).2 := by rw [Equiv.apply_symm_apply]; exact hr
    rw [Finset.sum_eq_single (e.symm (a, r))]
    · rw [hGo _ hs, ite_eq_left rfl, Complex.re_ofReal_mul]
      refine mul_le_mul_of_nonneg_right ((hoff _ hs).trans ?_) (hre _)
      have h0 : 0 ≤ (if a = none then 0 else κ) := by split_ifs <;> linarith
      linarith
    · intro t _ ht
      rw [hGo _ hs, ite_eq_right ht, zero_mul]
    · simp

end gramSlack

/-! ## A read of `h` with slack -/

section readSlack

open Quantum.Xmss.Assembly (sum_dW_conj_dep)

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Fintype M]
  [DecidableEq M]

/-- The mass of a column of the compression off the empty content and the outcome: at most
`1/N`, plus `1` at the decompressed-`⊥` outcome. -/
theorem sum_cr_sq_slack [Nonempty X] {κ : ℝ} (hκ : 0 ≤ κ) (o : Option X) :
    ∑ a, cr a o ^ 2 * (if a = none ∨ a = o then 0 else κ) ≤
      κ / Fintype.card X + if o = none then κ else 0 := by
  have hN : (0 : ℝ) < Fintype.card X := Nat.cast_pos.2 Fintype.card_pos
  rcases o with _ | y
  · calc ∑ a : Option X, cr a none ^ 2 * (if a = none ∨ a = none then 0 else κ)
        ≤ ∑ a : Option X, cr a none ^ 2 * κ :=
          Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left (by split_ifs <;> linarith)
            (sq_nonneg _)
      _ = κ := by rw [← Finset.sum_mul, EncSalt.sum_cr_sq_all, one_mul]
      _ ≤ _ := by
          rw [ite_eq_left rfl]
          linarith [div_nonneg hκ hN.le]
  · have ht : ∀ a, cr a (some y) ^ 2 * (if a = none ∨ a = some y then 0 else κ) ≤
        if a = none then 0 else ((Fintype.card X : ℝ)⁻¹) ^ 2 * κ := by
      intro a
      rcases a with _ | y'
      · simp
      · by_cases h : y' = y
        · subst h
          rw [ite_eq_left (Or.inr rfl), ite_eq_right (Option.some_ne_none _), mul_zero]
          exact mul_nonneg (sq_nonneg _) hκ
        · have hcr : cr (some y') (some y) = -(Fintype.card X : ℝ)⁻¹ := by simp [cr, h]
          have hne : ¬ (some y' = none ∨ some y' = some y) := by simp [h]
          rw [ite_eq_right hne, ite_eq_right (Option.some_ne_none _), hcr, neg_sq]
    refine (Finset.sum_le_sum fun a _ ↦ ht a).trans (le_of_eq ?_)
    rw [Fintype.sum_option, ite_eq_left rfl, ite_eq_right (Option.some_ne_none _), add_zero,
      zero_add]
    simp only [Option.some_ne_none, ite_false, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [sq, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul, div_eq_inv_mul]

/-- **A read of `h` with outcome-dependent weights and slack**: if every outcome's weight after
the read of the unhardwired cell `z`, at every content `a` of the cell, is at most `H` before plus
`κ` when `a` is neither empty nor the outcome, and the classical move of a hardwired cell is at
most `H`, the weights after the read are at most the weight of `H + κ/N + κ · [z recorded]`. -/
theorem sum_ofReal_readH_le_slack [Nonempty X] (z : Z) (u : M → Option X → M)
    (U : Option X → HwReg X Z M → ℝ) (hU : ∀ o s, 0 ≤ U o s) (H : HwReg X Z M → ℝ) {κ : ℝ}
    (hκ : 0 ≤ κ)
    (hact : ∀ s : HwReg X Z M, s.2.1.1 z = none → ∀ o a,
      U o ((Function.update s.1.1 z a, s.1.2), s.2.1, u s.2.2 o) ≤
        H s + if a = none ∨ a = o then 0 else κ)
    (hoff : ∀ s : HwReg X Z M, s.2.1.1 z ≠ none →
      U (s.2.1.1 z) (s.1, s.2.1, u s.2.2 (s.2.1.1 z)) ≤ H s)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    ∑ r : Option X × M, ENNReal.ofReal (∑ q, U r.1 q.2 *
      ((MatrixMap.conj (hwReadKraus (.readH z u) r) σ) q q).re) ≤
      ENNReal.ofReal (∑ q, (H q.2 + κ / Fintype.card X +
        if q.2.1.1 z = none then 0 else κ) * (σ q q).re) := by
  rw [← ENNReal.ofReal_sum_of_nonneg fun r _ ↦ Finset.sum_nonneg fun q _ ↦ mul_nonneg (hU _ _)
    (Complex.nonneg_iff.1
      ((MatrixMap.isCP_conj (hwReadKraus (.readH z u) r)).posSemidef hσ).diag_nonneg).1]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := sum_dW_conj_dep (fun r ↦ hwReadKraus (.readH z u) r) (fun r q ↦ U r.1 q.2) σ
  refine (le_of_eq h1).trans ?_
  refine re_trace_gramW_le_slack (cellRead_readH (z := z) u) (clsOff_readH z u)
    (fun o q ↦ U o q.2) (fun q ↦ H q.2) hκ (fun r hr o a' ↦ ?_) (fun q hq ↦ hoff q.2 hq) hσ
  set q := (splitH' z).symm (a', r) with hq
  have hr' : (splitH' z q).2 = r := by rw [hq, Equiv.apply_symm_apply]
  have hz : q.2.2.1.1 z = none := by
    rw [← hr'] at hr
    exact hr
  calc ∑ a, cr a o ^ 2 * U o ((splitH' z).symm (a, tauH z u o r)).2
      = ∑ a, cr a o ^ 2 *
          U o ((Function.update q.2.1.1 z a, q.2.1.2), q.2.2.1, u q.2.2.2 o) := by
        rw [← hr']
        simp only [splitH'_symm_tau]
    _ ≤ ∑ a, cr a o ^ 2 * (H q.2 + if a = none ∨ a = o then 0 else κ) :=
        Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left (hact q.2 hz o a) (sq_nonneg _)
    _ = H q.2 + ∑ a, cr a o ^ 2 * (if a = none ∨ a = o then 0 else κ) := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, EncSalt.sum_cr_sq_all,
          one_mul]
    _ ≤ H q.2 + κ / Fintype.card X + if o = none then κ else 0 := by
        have := sum_cr_sq_slack hκ o
        linarith

end readSlack

/-! ## A trial read and a grind with slack -/

section calls

open Quantum.Qrom HashSig Props OracleComp OracleSpec
open Quantum.Xmss.Hybrid (runtime2 runtime2_branch)

variable {Sx M' : Type} [Fintype Sx] [DecidableEq Sx] [Fintype M'] [DecidableEq M']

/-- One step of a step bound: normalize the program's head. -/
local macro "step_whnf" : tactic => `(tactic| (conv => arg 4; whnf))

/-- A local operation of a step bound keeping the potential. -/
local macro "step_prim" : tactic => `(tactic| (
  step_whnf;
  refine stepQ_liftBind_prim _ _ (fun _ ↦ _) (fun _ ↦ ?_)
    (fun ρ hρ ↦ tsum_potential_frame_le _ _ hρ)))

/-- The local operations up to the leaf, keeping the potential. -/
local macro "step_finish" : tactic => `(tactic| (
  repeat step_prim
  step_whnf
  exact stepQ_pure' _ _))

variable (m₀ : Finset Sx × M')
  (wt : ∀ i, Matrix ((hwSpec HashOutput HashDomain (Finset Sx × M')).In i ×
    HwReg HashOutput HashDomain (Finset Sx × M'))
    ((hwSpec HashOutput HashDomain (Finset Sx × M')).In i ×
      HwReg HashOutput HashDomain (Finset Sx × M')) ℂ → ℝ≥0∞)

/-- **The read of a trial at a call, with slack** (`sum_ofReal_readH_le_slack`). -/
theorem query_readH_le_slack (x : HashDomain)
    (u : Finset Sx × M' → Option HashOutput → Finset Sx × M')
    (U : HashOutput → HwReg HashOutput HashDomain (Finset Sx × M') → ℝ) (hU : ∀ v s, 0 ≤ U v s)
    (Lf H : HwReg HashOutput HashDomain (Finset Sx × M') → ℝ) (hL : ∀ s, 0 ≤ Lf s)
    (hH : ∀ s, 0 ≤ H s) {κ : ℝ} (hκ : 0 ≤ κ)
    (hd : ∀ σ : Matrix ((hwSpec HashOutput HashDomain (Finset Sx × M')).In
        (.inl (.inr (.readH x u))) × HwReg HashOutput HashDomain (Finset Sx × M'))
        ((hwSpec HashOutput HashDomain (Finset Sx × M')).In
          (.inl (.inr (.readH x u))) × HwReg HashOutput HashDomain (Finset Sx × M')) ℂ,
      σ.PosSemidef → wt (.inl (.inr (.readH x u))) σ ≤ ENNReal.ofReal (∑ q, Lf q.2 * (σ q q).re))
    (hact : ∀ s : HwReg HashOutput HashDomain (Finset Sx × M'), s.2.1.1 x = none → ∀ o a,
      U (o.getD 0) ((Function.update s.1.1 x a, s.1.2), s.2.1, u s.2.2 o) ≤
        H s + if a = none ∨ a = o then 0 else κ)
    (hoff : ∀ s : HwReg HashOutput HashDomain (Finset Sx × M'), s.2.1.1 x ≠ none →
      U ((s.2.1.1 x).getD 0) (s.1, s.2.1, u s.2.2 (s.2.1.1 x)) ≤ H s)
    {A E : QReg} (ℓ : A ≃ (hwSpec HashOutput HashDomain (Finset Sx × M')).In
      (.inl (.inr (.readH x u))) × E)
    {ρ : Matrix (A × HwReg HashOutput HashDomain (Finset Sx × M'))
      (A × HwReg HashOutput HashDomain (Finset Sx × M')) ℂ} (hρ : ρ.PosSemidef) :
    wt (.inl (.inr (.readH x u))) (callInput ℓ _ ρ) +
      ∑' r : Option HashOutput × (Finset Sx × M'), potential (wPot (U (r.1.getD 0)))
        (((runtime2 HashOutput HashDomain m₀).queryStep (.inl (.inr (.readH x u))) E ℓ).branch
          r ρ) ≤
      potential (wPot fun s ↦ Lf s + (H s + κ / Fintype.card HashOutput +
        if s.1.1 x = none then 0 else κ)) ρ := by
  have hσ := posSemidef_callInput (D := HwReg HashOutput HashDomain (Finset Sx × M')) ℓ hρ
  have hH' : ∀ s : HwReg HashOutput HashDomain (Finset Sx × M'),
      0 ≤ H s + κ / Fintype.card HashOutput + if s.1.1 x = none then 0 else κ := fun s ↦ by
    have h0 : 0 ≤ (if s.1.1 x = none then 0 else κ) := by split_ifs <;> linarith
    exact add_nonneg (add_nonneg (hH s) (div_nonneg hκ (Nat.cast_nonneg _))) h0
  rw [potential_wPot_add hL hH' hρ, ← potential_callInput (wPot Lf) ℓ ρ,
    ← potential_callInput (wPot fun s ↦ H s + κ / Fintype.card HashOutput +
      if s.1.1 x = none then 0 else κ) ℓ ρ]
  refine add_le_add ((hd _ hσ).trans_eq (potential_wPot hL _).symm) ?_
  have hsum : ∑' r : Option HashOutput × (Finset Sx × M'), potential (wPot (U (r.1.getD 0)))
      (((runtime2 HashOutput HashDomain m₀).queryStep (.inl (.inr (.readH x u))) E ℓ).branch
        r ρ) =
      ∑ r : Option HashOutput × (Finset Sx × M'), ENNReal.ofReal (∑ q, U (r.1.getD 0) q.2 *
        ((MatrixMap.conj (hwReadKraus (.readH x u) r) (callInput ℓ _ ρ)) q q).re) := by
    rw [tsum_fintype]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    exact (potential_queryStep (runtime2 HashOutput HashDomain m₀) (wPot (U (r.1.getD 0)))
      (.inl (.inr (.readH x u))) E ℓ r ρ).trans ((congrArg (potential _)
        (LinearMap.congr_fun (runtime2_branch m₀ (.inl (.inr (.readH x u))) r) _)).trans
          (potential_wPot (hU _) _))
  rw [hsum]
  exact (sum_ofReal_readH_le_slack x u (fun o s ↦ U (o.getD 0) s) (fun _ _ ↦ hU _ _) H hκ hact
    hoff hσ).trans_eq (potential_wPot hH' _).symm

/-- **A trial read of the challenger, with slack**: its weight `Lf` and the leaves' weights
`U v` after the read, bounded by `H` before plus `κ` off the empty content and the outcome. -/
theorem step₂_call_read_slack
    (upd : Caller → HashDomain → Finset Sx × M' → Option HashOutput → Finset Sx × M')
    (B : QReg) (x : HashDomain)
    (U : HashOutput → HwReg HashOutput HashDomain (Finset Sx × M') → ℝ) (hU : ∀ v s, 0 ≤ U v s)
    (Lf H : HwReg HashOutput HashDomain (Finset Sx × M') → ℝ) (hL : ∀ s, 0 ≤ Lf s)
    (hH : ∀ s, 0 ≤ H s) {κ : ℝ} (hκ : 0 ≤ κ)
    (hd : ∀ σ : Matrix ((hwSpec HashOutput HashDomain (Finset Sx × M')).In
        (.inl (.inr (.readH x (upd .answer x)))) × HwReg HashOutput HashDomain (Finset Sx × M'))
        ((hwSpec HashOutput HashDomain (Finset Sx × M')).In
          (.inl (.inr (.readH x (upd .answer x)))) ×
            HwReg HashOutput HashDomain (Finset Sx × M')) ℂ,
      σ.PosSemidef → wt (.inl (.inr (.readH x (upd .answer x)))) σ ≤
        ENNReal.ofReal (∑ q, Lf q.2 * (σ q q).re))
    (hact : ∀ s : HwReg HashOutput HashDomain (Finset Sx × M'), s.2.1.1 x = none → ∀ o a,
      U (o.getD 0) ((Function.update s.1.1 x a, s.1.2), s.2.1, upd .answer x s.2.2 o) ≤
        H s + if a = none ∨ a = o then 0 else κ)
    (hoff : ∀ s : HwReg HashOutput HashDomain (Finset Sx × M'), s.2.1.1 x ≠ none →
      U ((s.2.1.1 x).getD 0) (s.1, s.2.1, upd .answer x s.2.2 (s.2.1.1 x)) ≤ H s) :
    Step₂ (runtime2 HashOutput HashDomain m₀) .instruments wt
      (readProgOf upd (mixImpl .answer B (.inr x))) (fun v ↦ wPot (U v))
      (wPot fun s ↦ Lf s + (H s + κ / Fintype.card HashOutput +
        if s.1.1 x = none then 0 else κ)) := by
  refine (step₂_iff_stepQ _ _ _).2 ?_
  step_prim
  step_whnf
  refine stepQ_liftBind_query (R := runtime2 HashOutput HashDomain m₀) (I := .instruments)
    (wt := wt) (.inl (.inr (.readH x (upd .answer x)))) _ _ _
    (fun r : Option HashOutput × (Finset Sx × M') ↦ wPot (U (r.1.getD 0))) (fun r ↦ ?_)
    (fun ρ hρ ↦ query_readH_le_slack m₀ wt x (upd .answer x) U hU Lf H hL hH hκ hd hact hoff _
      hρ)
  step_finish

end calls

section grind

open Quantum.Qrom HashSig Props OracleComp OracleSpec
open Quantum.Xmss.Hybrid (runtime2)
open Tcr (Mem)

variable {Par Tw Msg Salt Dig : Type} {e : SaltEnc Par Tw Msg Salt Dig}
  (m₀ : Mem) {K : (hwSpec HashOutput HashDomain Mem).Port → Type} [∀ i, Fintype (K i)]
  {Φ : ∀ i, MatrixMap ((hwSpec HashOutput HashDomain Mem).In i ×
    HwReg HashOutput HashDomain Mem) (K i)} (hΦ : ∀ i, (Φ i).IsCP)
include hΦ

/-- **A grind with moving weights**: the stage potential `Pt c` pays the read of trial `c < L`
(at most `f c`), the slack `κ c` of its read, and the rest `Hc c`; the potential of the next
stage after the read of a non-codeword outcome, at a content `a` of the trial's cell, is at most
`Hc c` plus `κ c` when `a` is neither empty nor the outcome. -/
theorem step₂_grind_slack (hlen : e.hash.LengthLe maxLen) (B : QReg) (P : Par) (t : Tw)
    (M : Msg) (r0 : Salt) (f Hc Pt : ℕ → HwReg HashOutput HashDomain Mem → ℝ) (κ : ℕ → ℝ)
    (hf : ∀ c s, 0 ≤ f c s) (hHc : ∀ c s, 0 ≤ Hc c s) (hκ : ∀ c, 0 ≤ κ c)
    (hPt : ∀ c s, 0 ≤ Pt c s) (L : ℕ)
    (hd : ∀ c, c < L → ∀ (σ : Matrix ((hwSpec HashOutput HashDomain Mem).In
        (.inl (.inr (.readH (cell e P t (M, e.shift r0 c))
          (upd e .answer (cell e P t (M, e.shift r0 c)))))) × HwReg HashOutput HashDomain Mem)
        ((hwSpec HashOutput HashDomain Mem).In
          (.inl (.inr (.readH (cell e P t (M, e.shift r0 c))
            (upd e .answer (cell e P t (M, e.shift r0 c)))))) ×
              HwReg HashOutput HashDomain Mem) ℂ),
      σ.PosSemidef → ENNReal.ofReal (Φ (.inl (.inr (.readH (cell e P t (M, e.shift r0 c))
          (upd e .answer (cell e P t (M, e.shift r0 c)))))) σ).trace.re ≤
        ENNReal.ofReal (∑ q, f c q.2 * (σ q q).re))
    (hle : ∀ c, c < L → ∀ s : HwReg HashOutput HashDomain Mem,
      f c s + (Hc c s + κ c / Fintype.card HashOutput +
        if s.1.1 (cell e P t (M, e.shift r0 c)) = none then 0 else κ c) ≤ Pt c s)
    (hinv : ∀ c, c < L → ∀ s : HwReg HashOutput HashDomain Mem,
      s.2.1.1 (cell e P t (M, e.shift r0 c)) = none → ∀ a o,
      e.isCode (e.hash.trunc (o.getD 0)) = false →
      Pt (c + 1) ((Function.update s.1.1 (cell e P t (M, e.shift r0 c)) a, s.1.2), s.2.1,
        upd e .answer (cell e P t (M, e.shift r0 c)) s.2.2 o) ≤
        Hc c s + if a = none ∨ a = o then 0 else κ c)
    (hoff : ∀ c, c < L → ∀ s : HwReg HashOutput HashDomain Mem,
      s.2.1.1 (cell e P t (M, e.shift r0 c)) ≠ none →
      e.isCode (e.hash.trunc ((s.2.1.1 (cell e P t (M, e.shift r0 c))).getD 0)) = false →
      Pt (c + 1) (s.1, s.2.1, upd e .answer (cell e P t (M, e.shift r0 c)) s.2.2
        (s.2.1.1 (cell e P t (M, e.shift r0 c)))) ≤ Hc c s) :
    ∀ n c, c + n = L → Step₂ (runtime2 HashOutput HashDomain m₀) .instruments
      (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re)
      (readProgOf (upd e) ((e.grind romWorld P t M r0 c n).toQuantumAt (mixImpl .answer B)))
      (fun _ ↦ wPot fun _ ↦ 0) (wPot (Pt c)) := by
  intro n
  induction n with
  | zero =>
    intro c _
    exact step₂_mono (step₂_pure _ none) fun ρ hρ ↦
      potential_wPot_mono (fun _ ↦ le_rfl) (fun s ↦ hPt c s) hρ
  | succ n ih =>
    intro c hcL
    rw [EncSalt.toQuantumAt_grind_succ hlen, readProgOf_bind₂]
    have hG := hPt (c + 1)
    set x := cell e P t (M, e.shift r0 c)
    have hH' : ∀ s, 0 ≤ Hc c s + κ c / Fintype.card HashOutput +
        if s.1.1 x = none then 0 else κ c := fun s ↦ by
      have h0 : 0 ≤ (if s.1.1 x = none then 0 else κ c) := by
        split_ifs
        · exact le_rfl
        · exact hκ c
      exact add_nonneg (add_nonneg (hHc c s) (div_nonneg (hκ c) (Nat.cast_nonneg _))) h0
    refine step₂_mono (step₂_bind hΦ _ _ (fun v ↦ wPot fun s ↦
        if e.isCode (e.hash.trunc v) then 0 else Pt (c + 1) s)
      (step₂_call_read_slack m₀ _ (upd e) B x _ (fun v s ↦ by split_ifs <;> simp [hG]) (f c)
        (Hc c) (hf c) (hHc c) (hκ c) (hd c (by omega)) (fun s hs o a ↦ ?_) (fun s hs ↦ ?_))
      fun v ↦ ?_) fun ρ hρ ↦ potential_wPot_mono (fun s ↦ add_nonneg (hf c s) (hH' s))
        (hle c (by omega)) hρ
    · by_cases hv : e.isCode (e.hash.trunc (o.getD 0)) = true
      · rw [ite_eq_left hv]
        have h0 : 0 ≤ (if a = none ∨ a = o then 0 else κ c) := by
          split_ifs
          · exact le_rfl
          · exact hκ c
        have := hHc c s
        linarith
      · rw [ite_eq_right hv]
        exact hinv c (by omega) s hs a o (Bool.not_eq_true _ ▸ hv)
    · split_ifs with hv
      · exact hHc c s
      · exact hoff c (by omega) s hs (Bool.not_eq_true _ ▸ hv)
    · by_cases hv : e.isCode (e.hash.trunc v) = true
      · simp only [hv, ↓reduceIte]
        exact step₂_pure _ _
      · simp only [hv, Bool.false_eq_true, ↓reduceIte]
        exact ih (c + 1) (by omega)

end grind

end Quantum.StdModel.Qrom.EncSalt.Code

end
