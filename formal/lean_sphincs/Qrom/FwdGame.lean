module

public import Qrom.FwdOracle
public import Qrom.OvEvent
public import Qrom.OvBridge

@[expose] public section

/-!
# The forward block of a game with overrides, on reachable databases

The forward block of the compressed oracle for the search event, cut to reachable queried cells,
is the phase-basis one conjugated by the Fourier transform of the response register
(`Qrom.stdFwd_eq`), so its squared norm is at most `λ (2 + 4 λ)` (`Qrom.norm_stdFwd_sq_le`). The
compressed oracle with overrides agrees with it off the overridden inputs, where it leaves the
database alone, so its forward block obeys the same bound (`Qrom.OvGame.norm_fwd_compOracle_sq_le`).
Every database reached by tabulating a function and compressing every cell is reachable
(`Qrom.OvGame.reachS_mul_tab`).
-/

open Matrix
open scoped Kronecker ComplexOrder Matrix.Norms.L2Operator

namespace Qrom

open Quantum

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-! ## The standard basis -/

theorem queryFourier_mul_reachQ :
    queryFourier X Y * reachQ (X := X) (Y := Y) Y = reachQ (AddChar Y ℂ) * queryFourier X Y := by
  ext ⟨⟨x', χ⟩, D'⟩ ⟨⟨x, y⟩, D⟩
  rw [mul_apply, mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  simp only [queryFourier_apply, reachQ, of_apply, Prod.mk.injEq]
  rw [Finset.sum_eq_single x', Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single y, Finset.sum_eq_single χ]
    · rw [Finset.sum_eq_single D', Finset.sum_eq_single D]
      · by_cases hx : x' = x
        · subst hx
          by_cases hD : ∀ j ≠ x', D' j = D j <;> simp [hD, mul_comm]
        · simp [hx]
      · intro b _ hb
        simp [hb]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    · intro b _ hb
      refine Finset.sum_eq_zero fun D₁ _ ↦ ?_
      simp [Ne.symm hb]
    · simp
    · intro b _ hb
      refine Finset.sum_eq_zero fun D₁ _ ↦ ?_
      simp [hb]
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun c _ ↦ Finset.sum_eq_zero fun D₁ _ ↦ ?_
    simp [hb]
  · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun c _ ↦ Finset.sum_eq_zero fun D₁ _ ↦ ?_
    simp [Ne.symm hb]
  · simp

variable [Nonempty Y]
variable (good : X → Y → Prop) [∀ z, DecidablePred (good z)]

/-- The forward block of the compressed oracle for the search event, on reachable databases. -/
noncomputable def stdFwd : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ :=
  labelProjector (fun m : (X × Y) × Database X Y ↦ searchEvent good m.2) true *
    compressedOracle X Y *
    labelProjector (fun m : (X × Y) × Database X Y ↦ searchEvent good m.2) false * reachQ Y

theorem stdFwd_eq :
    stdFwd good = (queryFourier X Y)ᴴ * phFwd good * queryFourier X Y := by
  have hU : ∀ a b, (queryFourier X Y)ᴴ a b ≠ 0 →
      (fun m : (X × Y) × Database X Y ↦ searchEvent good m.2) a =
        (fun m : (X × AddChar Y ℂ) × Database X Y ↦ searchEvent good m.2) b := by
    rintro ⟨⟨x, y⟩, D⟩ ⟨⟨x', χ⟩, D'⟩ h
    rw [conjTranspose_apply, queryFourier_apply] at h
    by_cases hc : x' = x ∧ D' = D
    · simp [hc.2]
    · simp only [hc, ↓reduceIte, star_zero, ne_eq, not_true_eq_false] at h
  have hV : ∀ a b, queryFourier X Y a b ≠ 0 →
      (fun m : (X × AddChar Y ℂ) × Database X Y ↦ searchEvent good m.2) a =
        (fun m : (X × Y) × Database X Y ↦ searchEvent good m.2) b := fun a b h ↦
    (hU b a (by rw [conjTranspose_apply]; exact star_ne_zero.mpr h)).symm
  have e₁ := mul_labelProjector_eq_labelProjector_mul _ _ hU true
  have e₂ := mul_labelProjector_eq_labelProjector_mul _ _ hV false
  rw [stdFwd, phFwd, ← truncatedOracle_card, truncatedOracle_eq]
  simp only [← Matrix.mul_assoc]
  rw [← e₁]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (queryFourier X Y), e₂, Matrix.mul_assoc, queryFourier_mul_reachQ]

/-- **The forward block of the compressed oracle, on reachable databases.** -/
theorem norm_stdFwd_sq_le (s : ℕ) (hs : ∀ z, (Finset.univ.filter (good z)).card ≤ s) :
    ‖stdFwd good‖ ^ 2 ≤ (s / Fintype.card Y : ℝ) * (2 + 4 * (s / Fintype.card Y)) := by
  rw [stdFwd_eq]
  exact (pow_le_pow_left₀ (norm_nonneg _) (l2_opNorm_conjTranspose_mul_mul_le
    (queryFourier_mul_conjTranspose X Y) _) 2).trans (norm_phFwd_sq_le good s hs)

/-! ## Games with overrides -/

namespace OvGame

variable {S P : Type} [Fintype S] [DecidableEq S] {Res : P → Type} [∀ j, Fintype (Res j)]
  [∀ j, DecidableEq (Res j)]
variable (g : OvGame X Y S P Res)

/-- The projector onto the joint states whose queried cell is reachable, beside the side state. -/
noncomputable def reachS : Matrix ((X × Y) × (S × Database X Y)) ((X × Y) × (S × Database X Y)) ℂ :=
  of fun p' p ↦ if p'.2.1 = p.2.1 then reachQ Y (p'.1, p'.2.2) (p.1, p.2.2) else 0

omit [AddCommGroup Y] [Nonempty Y] in
theorem reachS_eq :
    reachS (X := X) (Y := Y) (S := S) = (blk fun _ : S ↦ reachQ (X := X) Y).submatrix swapE swapE := by
  ext ⟨m, s, D⟩ ⟨m', s', D'⟩
  simp only [reachS, of_apply, submatrix_apply, swapE, Equiv.coe_fn_mk, blk_apply]

/-- The forward block of one side state: off the overrides, the compressed oracle's. -/
theorem fwd_cOs_eq (s : S) :
    ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ eventProj (searchEvent good)) * g.cOs s *
        ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ (1 - eventProj (searchEvent good))) * reachQ Y =
      (1 - diagonal (g.ovDiag s)) * stdFwd good := by
  set Qh := (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ eventProj (searchEvent good) with hQh
  set Pr := diagonal (g.ovDiag s) with hPr
  set U := oracleUnitary (g.ovVal s) ⊗ₖ (1 : Matrix (Database X Y) (Database X Y) ℂ) with hU
  have hQPr : Qh * Pr = Pr * Qh := by
    rw [hPr, hQh, ← ovProj_kronecker_one, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
  have hQU : Qh * U = U * Qh := by
    rw [hQh, hU, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_one]
  have hQPrc : Qh * (1 - Pr) = (1 - Pr) * Qh := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hQPr, Matrix.mul_one, Matrix.one_mul]
  have hc : (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ (1 - eventProj (searchEvent good)) = 1 - Qh := by
    have := kronecker_add (1 : Matrix (X × Y) (X × Y) ℂ) (1 - eventProj (searchEvent good))
      (eventProj (searchEvent good))
    rw [sub_add_cancel, one_kronecker_one] at this
    rw [hQh, this, add_sub_cancel_right]
  have hQQ : Qh * (1 - Qh) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hQh, ← mul_kronecker_mul, Matrix.one_mul,
      eventProj_mul_self, sub_self]
  have hlt : Qh = labelProjector (fun m : (X × Y) × Database X Y ↦ searchEvent good m.2) true := by
    rw [hQh, one_kronecker_eventProj]
  have hlf : 1 - Qh =
      labelProjector (fun m : (X × Y) × Database X Y ↦ searchEvent good m.2) false := by
    rw [hlt, one_sub_labelProjector_bool]
    rfl
  rw [cOs_eq, hc, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  have h1 : Qh * (Pr * U) * (1 - Qh) = 0 := by
    rw [← Matrix.mul_assoc, hQPr, Matrix.mul_assoc Pr, hQU, Matrix.mul_assoc, Matrix.mul_assoc,
      hQQ, Matrix.mul_zero, Matrix.mul_zero]
  have h2 : Qh * ((1 - Pr) * compressedOracle X Y) = (1 - Pr) * (Qh * compressedOracle X Y) := by
    rw [← Matrix.mul_assoc, hQPrc, Matrix.mul_assoc]
  rw [h1, Matrix.zero_mul, zero_add, h2, stdFwd, ← hlt, ← hlf]
  simp only [Matrix.mul_assoc]

/-- **The forward block of the compressed oracle with overrides, on reachable databases.** -/
theorem norm_fwd_compOracle_sq_le (s : ℕ) (hs : ∀ z, (Finset.univ.filter (good z)).card ≤ s) :
    ‖((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ eventProj (searchEvent good))) *
        g.compOracle * ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
          ((1 : Matrix S S ℂ) ⊗ₖ (1 - eventProj (searchEvent good)))) * reachS‖ ^ 2 ≤
      (s / Fintype.card Y : ℝ) * (2 + 4 * (s / Fintype.card Y)) := by
  rw [compOracle_eq, one_kronecker_one_kronecker_eq, one_kronecker_one_kronecker_eq, reachS_eq,
    submatrix_mul_equiv, submatrix_mul_equiv, submatrix_mul_equiv, l2_opNorm_submatrix_equiv,
    blk_mul, blk_mul, blk_mul, blk, l2_opNorm_sum_single_kronecker]
  have h0 : 0 ≤ (s / Fintype.card Y : ℝ) * (2 + 4 * (s / Fintype.card Y)) := by positivity
  have hPrc : ∀ s', ‖(1 - diagonal (g.ovDiag s') :
      Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ)‖ ≤ 1 := fun s' ↦ by
    rw [← diagonal_one, diagonal_sub, l2_opNorm_diagonal]
    refine pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun p ↦ ?_
    by_cases h : (g.ov s' p.1.1).isSome <;> simp [ovDiag, h]
  have hblock : ∀ s', ‖((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ eventProj (searchEvent good)) *
      g.cOs s' * ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ (1 - eventProj (searchEvent good))) *
        reachQ Y‖ ≤ √((s / Fintype.card Y : ℝ) * (2 + 4 * (s / Fintype.card Y))) := by
    intro s'
    rw [fwd_cOs_eq]
    refine (l2_opNorm_mul _ _).trans ?_
    calc ‖(1 - diagonal (g.ovDiag s') :
          Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ)‖ * ‖stdFwd good‖
        ≤ 1 * ‖stdFwd good‖ := by gcongr; exact hPrc s'
      _ ≤ _ := by
          rw [one_mul]
          exact Real.le_sqrt_of_sq_le (norm_stdFwd_sq_le good s hs)
  have hsup := Real.iSup_le hblock (Real.sqrt_nonneg _)
  calc _ ≤ √((s / Fintype.card Y : ℝ) * (2 + 4 * (s / Fintype.card Y))) ^ 2 :=
        pow_le_pow_left₀ (Real.iSup_nonneg fun _ ↦ norm_nonneg _) hsup 2
    _ = _ := Real.sq_sqrt h0

end OvGame

end Qrom
