module

public import Qrom.Sphincs.Bound.Defer

@[expose] public section

/-!
# Covered digests

On corresponding digests, a covered forgery digest is covered by the leaves of all the presampled
digests, and its first digest call is an input the verifier reads whose `G` value some second call
output completes to such a digest (`Qrom.Sphincs.Coverable`). In the deferred game that is a search,
so averaged over the data and `G` the covered digests weigh at most
`λ_cov (√6 (n + 1 + verifyQueries) + 2 verifyQueries)² tr ρ` (`Qrom.Sphincs.avg_cov_le`), where
`λ_cov` is the probability, over uniform presampled digests and a uniform first call output, that the
output is coverable (`Qrom.Sphincs.lamCov`).
-/

open OracleComp OracleSpec FORS FORS.Security Concrete Quantum
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

variable [Params]

open Classical in
/-- The FORS leaves all the presampled digests open. -/
def leavesAll (δ : Fin signatureLimit → DigV) : Disclosures := fun index κ ↦
  Finset.univ.filter fun leaf ↦ ∃ i, digestIndex (truncateMessageDigest (δ i)) = index ∧
    digestLeaves (truncateMessageDigest (δ i)) κ = leaf

/-- A first digest call output that some second output completes to a digest those leaves cover. -/
def Coverable (δ : Fin signatureLimit → DigV) (y : HashOutput) : Prop :=
  ∃ ys : DigV, ys firstCall = y ∧ Covered (leavesAll δ)
    (digestIndex (truncateMessageDigest ys), digestLeaves (truncateMessageDigest ys))

/-- A coverable output at a first digest call input. -/
def goodC (r : Data) (δ : Fin signatureLimit → DigV) (z : Input) (y : HashOutput) : Prop :=
  (∃ m R, z = digestInputX r m R firstCall) ∧ Coverable δ y

open Classical in
/-- The number of coverable outputs. -/
def sbC (δ : Fin signatureLimit → DigV) : ℕ := (Finset.univ.filter (Coverable δ)).card

/-- **`λ_cov`**: the probability, over uniform presampled digests and a uniform first digest call
output, that the output is coverable. -/
def lamCov : ℝ≥0∞ := (Fintype.card (Fin signatureLimit → DigV) : ℝ≥0∞)⁻¹ *
  ∑ δ, ENNReal.ofReal ((sbC δ : ℝ) / Fintype.card HashOutput)

theorem revealedLeaves_sub (r : Data) {Dg : Message → DigV} {δ : Fin signatureLimit → DigV} {s : Log}
    (hc : OvGame.Corr (sig s) Dg δ) (index : Index) (κ : FTree) :
    revealedLeaves (withDig r Dg) s index κ ⊆ leavesAll δ index κ := by
  intro leaf hl
  simp only [revealedLeaves, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  obtain ⟨e, he, hi, hk⟩ := hl
  have hm : e.1 ∈ sig s := mem_sig.mpr ⟨e, he, rfl⟩
  have hdg := dgOf_corr (length_sig_le s) hc hm
  have hq : (sig s).idxOf e.1 < signatureLimit :=
    lt_of_lt_of_le (List.idxOf_lt_length_iff.mpr hm) (length_sig_le s)
  rw [dgOf, dite_eq_left hq] at hdg
  have hD : digestH (hOf (withDig r Dg)) e.1 = truncateMessageDigest (δ ⟨_, hq⟩) := by
    rw [← hdg]
    rfl
  simp only [leavesAll, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hD] at hi hk
  exact ⟨_, hi, hk⟩

theorem covered_mono {R R' : Disclosures} (h : ∀ i κ, R i κ ⊆ R' i κ) {v : FullDigestView}
    (hv : Covered R v) : Covered R' v := fun κ ↦ h _ _ (hv κ)

open Classical in
/-- The covered event, with the data's public key. -/
def evA (r : Data) (G : Input → HashOutput) (Dg : Message → DigV)
    (p : Σ u, QuantumComp₂.Leaf (QReg.of Unit) (PublicKey × Forgery) u) (s : Log) : Bool :=
  evCov (withDig r Dg) s G p.2.2.2 && decide (p.2.2.1 = pkD (withDig r Dg))

open Classical in
/-- The verifier of the deferred game reads a coverable first digest call. -/
def evB (r : Data) (G : Input → HashOutput) (δ : Fin signatureLimit → DigV)
    (p : Σ u, QuantumComp₂.Leaf (QReg.of Unit) (PublicKey × Forgery) u) (s : Log) : Bool :=
  decide (∃ z ∈ outK (evalWithAnswerFn (QueryImpl.ofFn ((gB r δ).answer s G)) (verifier p.2.2)),
    goodC r δ z (G z))

theorem digestInput_mem_trace (f : Input → HashOutput) (d : Data) (F : Forgery) :
    digestInputX d F.message F.signature.randomness firstCall ∈
      outK (evalWithAnswerFn (QueryImpl.ofFn f) (verifier (pkD d, F))) := by
  rw [outK_verifier, mem_outOf, eval_verifier]
  exact digestInputs_mem' (QueryImpl.ofFn (extend f)) (pkD d) F.message F.signature firstCall

open Classical in
theorem evA_evB (r : Data) (G : Input → HashOutput) (Dg : Message → DigV) (δ : Fin signatureLimit → DigV)
    (p : Σ u, QuantumComp₂.Leaf (QReg.of Unit) (PublicKey × Forgery) u) (s : Log)
    (hc : OvGame.Corr (sig s) Dg δ) (h : evA r G Dg p s = true) : evB r G δ p s = true := by
  simp only [evA, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hcov, hpk⟩ := h
  rw [evCov_iff] at hcov
  obtain ⟨-, hcv⟩ := hcov
  have hv : p.2.2 = (pkD (withDig r Dg), p.2.2.2) := Prod.ext hpk rfl
  unfold evB
  rw [decide_eq_true_iff, hv]
  refine ⟨_, digestInput_mem_trace _ (withDig r Dg) p.2.2.2, ⟨⟨_, _, rfl⟩, ?_⟩⟩
  refine ⟨fun call ↦ G (digestInputX r p.2.2.2.message p.2.2.2.signature.randomness call), rfl, ?_⟩
  exact covered_mono (revealedLeaves_sub r hc) hcv

open Classical in
/-- **The search for a coverable first call**, in the deferred game. -/
theorem sum_cov_search_le (r : Data) (δ : Fin signatureLimit → DigV) {A : QReg} (adv : Adversary A)
    {n : ℕ} (hadv : ∀ pk, (adv pk).IsTotalQueryBound n) (ρ : SubState A) :
    ∑ G : Input → HashOutput, (Fintype.card (Input → HashOutput) : ℝ≥0∞)⁻¹ *
      OvGame.sideW (gB r δ) G .instruments (withKey adv) ρ (evB r G δ) ≤
      ENNReal.ofReal (((sbC δ : ℝ) / Fintype.card HashOutput) *
        (√6 * (1 + n + verifyQueries : ℕ) + 2 * verifyQueries) ^ 2) *
        ENNReal.ofReal ρ.matrix.trace.re := by
  have hs : ∀ z, (Finset.univ.filter (goodC r δ z)).card ≤ sbC δ := fun z ↦
    Finset.card_le_card fun y hy ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact hy.2
  exact OvGame.search_withVerifier_le (gB r δ) (goodC r δ) (sbC δ) hs (withKey adv) verifier outK
    verifyQueries card_outK_le (1 + n) verifyQueries (isTotalQueryBound_withKey hadv)
    isTotalQueryBound_verifier ρ

theorem card_ne_zero_enn (α : Type) [Fintype α] [Nonempty α] : (Fintype.card α : ℝ≥0∞) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

open Classical in
/-- **Covered digests**, averaged over the data and `G`. -/
theorem avg_cov_le {A : QReg} (adv : Adversary A) {n : ℕ}
    (hadv : ∀ pk, (adv pk).IsTotalQueryBound n) (ρ : SubState A) :
    ∑ d, ∑ G, ((Fintype.card Data : ℝ≥0∞) * Fintype.card (Input → HashOutput))⁻¹ *
      OvGame.sideW (hidGame d) G .instruments (withKey adv) ρ (fun p s ↦ evCov d s G p.2.2.2) ≤
      lamCov * ENNReal.ofReal ((√6 * (1 + n + verifyQueries : ℕ) + 2 * verifyQueries) ^ 2) *
        ENNReal.ofReal ρ.matrix.trace.re := by
  set cD := (Fintype.card Data : ℝ≥0∞)
  set cG := (Fintype.card (Input → HashOutput) : ℝ≥0∞)
  set cM := (Fintype.card (Message → DigV) : ℝ≥0∞)
  set cΔ := (Fintype.card (Fin signatureLimit → DigV) : ℝ≥0∞)
  set K := (√6 * (1 + n + verifyQueries : ℕ) + 2 * verifyQueries) ^ 2
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
          ∑ δ, OvGame.sideW (gB r δ) G .instruments (withKey adv) ρ (evB r G δ)) :=
        Finset.sum_le_sum fun r _ ↦ Finset.sum_le_sum fun G _ ↦ mul_le_mul_right
          (deferral_dig r (evA r G) (evB r G) (evA_evB r G) G adv ρ) _
    _ = ∑ r, cD⁻¹ * (cΔ⁻¹ * ∑ δ, ∑ G, cG⁻¹ *
          OvGame.sideW (gB r δ) G .instruments (withKey adv) ρ (evB r G δ)) := by
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun δ _ ↦ Finset.sum_congr rfl fun G _ ↦ ?_
        rw [hinv]
        ring
    _ ≤ ∑ r : Data, cD⁻¹ * (cΔ⁻¹ * ∑ δ, ENNReal.ofReal (((sbC δ : ℝ) / Fintype.card HashOutput) * K) * T) :=
        Finset.sum_le_sum fun r _ ↦ mul_le_mul_right (mul_le_mul_right
          (Finset.sum_le_sum fun δ _ ↦ sum_cov_search_le r δ adv hadv ρ) _) _
    _ = cΔ⁻¹ * ∑ δ, ENNReal.ofReal (((sbC δ : ℝ) / Fintype.card HashOutput) * K) * T := by
        rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.mul_inv_cancel (card_ne_zero_enn _) (ENNReal.natCast_ne_top _), one_mul]
    _ = lamCov * ENNReal.ofReal K * T := by
        have hK : 0 ≤ K := sq_nonneg _
        simp only [ENNReal.ofReal_mul (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (q := K)]
        rw [lamCov, ← Finset.sum_mul, ← Finset.sum_mul]
        change cΔ⁻¹ * _ = (cΔ⁻¹ * _) * _ * _
        ring

end Qrom.Sphincs
