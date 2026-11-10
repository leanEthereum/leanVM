module

public import Qrom.Cells
public import Qrom.Sphincs.Bound.DigCells
public import Qrom.Sphincs.Bound.LamCov2

@[expose] public section

/-!
# Covered digests, searched cell by cell

On corresponding digests, a covered forgery digest is covered by the leaves of all the presampled
digests. With the digest calls of one prefix as the components of one cell, that is a search for
a cell whose value, a whole digest, is covered, checking the one cell of the forgery's digest, so
for presampled digests `δ` covering a fraction `λ_δ` of the digests, the covered digests weigh at
most `λ_δ (√(2 + 4 λ_δ) (n + 1) + 2)² tr ρ` (`Qrom.Sphincs.sum_covF_search_le`), which is at most
`(λ_δ + 3 λ_δ²) (√2 (n + 1) + 2)² tr ρ`. Averaged over the data and `G`, with the first and second
moments of `λ_δ` (`Qrom.Sphincs.avg_le_lamS`, `Qrom.Sphincs.avg_sq_le`), they weigh at most
`(lamS + 3 (lamS² + lamS2)) (√2 (n + 1) + 2)² tr ρ` (`Qrom.Sphincs.avg_covF_le`).
-/

open OracleComp OracleSpec FORS FORS.Security Concrete Quantum
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

variable [Params]

/-- The cell of the forgery's digest calls. -/
def outF (r : Data) (a : PublicKey × Forgery) : Finset Cell :=
  {(cellOf (digestInputX r a.2.message a.2.signature.randomness firstCall)).1}

open Classical in
/-- The cell of the forgery's digest calls holds a covered digest. -/
def evBc (r : Data) (G : Input → HashOutput) (δ : Fin signatureLimit → DigV)
    (p : Σ u, QuantumComp₂.Leaf (QReg.of Unit) (PublicKey × Forgery) u) (_ : Log) : Bool :=
  decide (∃ c ∈ outF r p.2.2,
    ∀ v : DigV, (∀ x, (cellOf x).1 = c → v (cellOf x).2 = G x) →
      Covered (leavesAll δ) (fullDigestView (truncateMessageDigest v)))

theorem cellOf_digestInputX_fst (d : Data) (m : Message) (R : Randomness) (c c' : DigestCall) :
    (cellOf (digestInputX d m R c)).1 = (cellOf (digestInputX d m R c')).1 := by
  rw [cellOf_of_isDig (isDig_digestInputX d m R c), cellOf_of_isDig (isDig_digestInputX d m R c')]
  exact congrArg Sum.inl (Subtype.ext ((pre_digestInputX d m R c).trans (pre_digestInputX d m R c').symm))

open Classical in
theorem evA_evBc (r : Data) (G : Input → HashOutput) (Dg : Message → DigV) (δ : Fin signatureLimit → DigV)
    (p : Σ u, QuantumComp₂.Leaf (QReg.of Unit) (PublicKey × Forgery) u) (s : Log)
    (hc : OvGame.Corr (sig s) Dg δ) (h : evA r G Dg p s = true) : evBc r G δ p s = true := by
  simp only [evA, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hcov, hpk⟩ := h
  rw [evCov_iff] at hcov
  obtain ⟨-, hcv⟩ := hcov
  unfold evBc
  rw [decide_eq_true_iff]
  set F := p.2.2.2
  refine ⟨_, Finset.mem_singleton_self _, fun v hvx ↦ ?_⟩
  have hvf : v = fun call ↦ G (digestInputX r F.message F.signature.randomness call) := by
    funext call
    have h1 := hvx (digestInputX r F.message F.signature.randomness call)
      (cellOf_digestInputX_fst r _ _ call firstCall)
    rwa [cellOf_of_isDig (isDig_digestInputX r _ _ call)] at h1
  rw [hvf]
  exact covered_mono (revealedLeaves_sub r hc) hcv

open Classical in
/-- **The search for a covered cell**, in the deferred game. -/
theorem sum_covF_search_le (r : Data) (δ : Fin signatureLimit → DigV) {A : QReg} (adv : Adversary A)
    {n : ℕ} (hadv : ∀ pk, (adv pk).IsTotalQueryBound n) (ρ : SubState A) :
    ∑ G : Input → HashOutput, (Fintype.card (Input → HashOutput) : ℝ≥0∞)⁻¹ *
      OvGame.sideW (gB r δ) G .instruments (withKey adv) ρ (evBc r G δ) ≤
      ENNReal.ofReal (((sbF δ : ℝ) / Fintype.card DigV) *
        (√(2 + 4 * ((sbF δ : ℝ) / Fintype.card DigV)) * (1 + n : ℕ) + 2) ^ 2) *
        ENNReal.ofReal ρ.matrix.trace.re := by
  have h := OvGame.search_cells_le (gB r δ) cellOf cellOf_injective
    (fun s ↦ cellOv ((gB r δ).ov s)) (gB_ov_spec r δ)
    (fun _ v ↦ Covered (leavesAll δ) (fullDigestView (truncateMessageDigest v))) (sbF δ)
    (fun _ ↦ le_rfl) (withKey adv) (outF r) 1 (fun _ ↦ (Finset.card_singleton _).le) (1 + n)
    (isTotalQueryBound_withKey hadv) ρ
  simp only [Nat.cast_one, mul_one] at h
  exact h

/-- The constant `2 + 4 λ` against `2`, for a fraction `λ ≤ 1`. -/
theorem mul_sq_sqrt_le {l a b : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    l * (√(2 + 4 * l) * a + b) ^ 2 ≤ (l + 3 * l ^ 2) * (√2 * a + b) ^ 2 := by
  have h2 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg 2
  have hs : √(2 + 4 * l) ≤ √2 * (1 + l) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    nlinarith
  have hx : √(2 + 4 * l) * a + b ≤ (1 + l) * (√2 * a + b) := by
    nlinarith [mul_le_mul_of_nonneg_right hs ha, mul_nonneg hl0 hb]
  have hx0 : 0 ≤ √(2 + 4 * l) * a + b := by positivity
  calc l * (√(2 + 4 * l) * a + b) ^ 2 ≤ l * ((1 + l) * (√2 * a + b)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx 2) hl0
    _ = (l + 2 * l ^ 2 + l ^ 3) * (√2 * a + b) ^ 2 := by ring
    _ ≤ (l + 3 * l ^ 2) * (√2 * a + b) ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        nlinarith [mul_le_mul_of_nonneg_left hl1 (sq_nonneg l)]

theorem lamS_nonneg : 0 ≤ lamS := by
  unfold lamS
  positivity

/-- The fraction of covered digests is at most one. -/
theorem sbF_div_le_one (δ : Fin signatureLimit → DigV) : (sbF δ : ℝ) / Fintype.card DigV ≤ 1 := by
  have hD : (0 : ℝ) < Fintype.card DigV := Nat.cast_pos.mpr Fintype.card_pos
  rw [div_le_one hD]
  exact_mod_cast (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ])

/-- The average covered fraction, in the reals. -/
theorem avg_sbF_le : (Fintype.card (Fin signatureLimit → DigV) : ℝ)⁻¹ *
    ∑ δ, (sbF δ : ℝ) / Fintype.card DigV ≤ lamS := by
  have hΔ : (0 : ℝ) < Fintype.card (Fin signatureLimit → DigV) := Nat.cast_pos.mpr Fintype.card_pos
  have h := avg_le_lamS (fun δ ↦ (sbF δ : ℝ) / Fintype.card DigV) (fun δ ↦ by positivity) sbF_le
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hΔ,
    ← ENNReal.ofReal_sum_of_nonneg fun δ _ ↦ by positivity,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hΔ.le)] at h
  exact (ENNReal.ofReal_le_ofReal_iff lamS_nonneg).mp h

open Classical in
/-- **Covered digests**, averaged over the data and `G`. -/
theorem avg_covF_le {A : QReg} (adv : Adversary A) {n : ℕ}
    (hadv : ∀ pk, (adv pk).IsTotalQueryBound n) (ρ : SubState A) :
    ∑ d, ∑ G, ((Fintype.card Data : ℝ≥0∞) * Fintype.card (Input → HashOutput))⁻¹ *
      OvGame.sideW (hidGame d) G .instruments (withKey adv) ρ (fun p s ↦ evCov d s G p.2.2.2) ≤
      ENNReal.ofReal ((lamS + 3 * (lamS ^ 2 + lamS2)) * (√2 * (1 + n : ℕ) + 2) ^ 2) *
        ENNReal.ofReal ρ.matrix.trace.re := by
  set cD := (Fintype.card Data : ℝ≥0∞)
  set cG := (Fintype.card (Input → HashOutput) : ℝ≥0∞)
  set cM := (Fintype.card (Message → DigV) : ℝ≥0∞)
  set cΔ := (Fintype.card (Fin signatureLimit → DigV) : ℝ≥0∞)
  set K := (√2 * (1 + n : ℕ) + 2) ^ 2
  set T := ENNReal.ofReal ρ.matrix.trace.re
  have hW : ∀ r G Dg, OvGame.sideW (hidGame (withDig r Dg)) G .instruments (withKey adv) ρ
      (fun p s ↦ evCov (withDig r Dg) s G p.2.2.2) =
      OvGame.sideW (hidGame (withDig r Dg)) G .instruments (withKey adv) ρ (evA r G Dg) :=
    fun r G Dg ↦ sideW_pk_restrict (withDig r Dg) G adv ρ _
  have hinv : (cD * cG)⁻¹ = cD⁻¹ * cG⁻¹ :=
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))
  let f : Data → ℝ≥0∞ := fun d ↦ ∑ G, (cD * cG)⁻¹ *
    OvGame.sideW (hidGame d) G .instruments (withKey adv) ρ (fun p s ↦ evCov d s G p.2.2.2)
  calc ∑ d, f d = cM⁻¹ * ∑ r, ∑ Dg, f (withDig r Dg) := by
        rw [sum_withDig f, nsmul_eq_mul, ← mul_assoc,
          ENNReal.inv_mul_cancel (card_ne_zero_enn _) (ENNReal.natCast_ne_top _), one_mul]
    _ = ∑ r, ∑ G, (cD * cG)⁻¹ * (cM⁻¹ *
          ∑ Dg, OvGame.sideW (hidGame (withDig r Dg)) G .instruments (withKey adv) ρ (evA r G Dg)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        simp only [f, ← hW]
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun G _ ↦ ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun Dg _ ↦ ?_
        ring
    _ ≤ ∑ r, ∑ G, (cD * cG)⁻¹ * (cΔ⁻¹ *
          ∑ δ, OvGame.sideW (gB r δ) G .instruments (withKey adv) ρ (evBc r G δ)) :=
        Finset.sum_le_sum fun r _ ↦ Finset.sum_le_sum fun G _ ↦ mul_le_mul_right
          (deferral_dig r (evA r G) (evBc r G) (evA_evBc r G) G adv ρ) _
    _ = ∑ r, cD⁻¹ * (cΔ⁻¹ * ∑ δ, ∑ G, cG⁻¹ *
          OvGame.sideW (gB r δ) G .instruments (withKey adv) ρ (evBc r G δ)) := by
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun δ _ ↦ Finset.sum_congr rfl fun G _ ↦ ?_
        rw [hinv]
        ring
    _ ≤ ∑ r : Data, cD⁻¹ * (cΔ⁻¹ * ∑ δ, ENNReal.ofReal
          (((sbF δ : ℝ) / Fintype.card DigV) + 3 * ((sbF δ : ℝ) / Fintype.card DigV) ^ 2) *
            ENNReal.ofReal K * T) := by
        refine Finset.sum_le_sum fun r _ ↦ mul_le_mul_right (mul_le_mul_right
          (Finset.sum_le_sum fun δ _ ↦ (sum_covF_search_le r δ adv hadv ρ).trans
            (mul_le_mul' ?_ le_rfl)) _) _
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal
          (mul_sq_sqrt_le (by positivity) (sbF_div_le_one δ) (by positivity) (by norm_num))
    _ = cΔ⁻¹ * ∑ δ, ENNReal.ofReal
          (((sbF δ : ℝ) / Fintype.card DigV) + 3 * ((sbF δ : ℝ) / Fintype.card DigV) ^ 2) *
            ENNReal.ofReal K * T := by
        rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.mul_inv_cancel (card_ne_zero_enn _) (ENNReal.natCast_ne_top _), one_mul]
    _ ≤ ENNReal.ofReal ((lamS + 3 * (lamS ^ 2 + lamS2)) * K) * T := by
        have hΔ : (0 : ℝ) < Fintype.card (Fin signatureLimit → DigV) :=
          Nat.cast_pos.mpr Fintype.card_pos
        have hK : 0 ≤ K := sq_nonneg _
        have havg : (Fintype.card (Fin signatureLimit → DigV) : ℝ)⁻¹ *
            ∑ δ, (((sbF δ : ℝ) / Fintype.card DigV) + 3 * ((sbF δ : ℝ) / Fintype.card DigV) ^ 2) ≤
            lamS + 3 * (lamS ^ 2 + lamS2) := by
          rw [Finset.sum_add_distrib, mul_add, ← Finset.mul_sum, mul_left_comm]
          exact add_le_add avg_sbF_le (mul_le_mul_of_nonneg_left (avg_sq_le _ (fun δ ↦ by positivity)
            sbF_le) (by norm_num))
        have e : cΔ⁻¹ * ∑ δ, ENNReal.ofReal
            (((sbF δ : ℝ) / Fintype.card DigV) + 3 * ((sbF δ : ℝ) / Fintype.card DigV) ^ 2) *
              ENNReal.ofReal K * T =
            ENNReal.ofReal ((Fintype.card (Fin signatureLimit → DigV) : ℝ)⁻¹ *
              ∑ δ, (((sbF δ : ℝ) / Fintype.card DigV) +
                3 * ((sbF δ : ℝ) / Fintype.card DigV) ^ 2)) * ENNReal.ofReal K * T := by
          rw [← Finset.sum_mul, ← Finset.sum_mul,
            ← ENNReal.ofReal_sum_of_nonneg (fun δ _ ↦ by positivity),
            ENNReal.ofReal_mul (inv_nonneg.mpr hΔ.le), ENNReal.ofReal_inv_of_pos hΔ,
            ENNReal.ofReal_natCast]
          ring
        rw [e, ENNReal.ofReal_mul (p := lamS + 3 * (lamS ^ 2 + lamS2)) (q := K)
          (by have := lamS_nonneg; have := lamS2_nonneg; positivity)]
        gcongr

end Qrom.Sphincs
