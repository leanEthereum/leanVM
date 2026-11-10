module

public import Qrom.Sphincs.Bound.Split

@[expose] public section

/-!
# The protected reads and the hits

Averaged over the data, the verifier reads a protected input of the hidden game with weight at most
`verifyQueries · 2^-128 tr ρ` (`Qrom.Sphincs.sum_prot_le`). Averaged over `G`, it reads an input at
which `G` hits the honest value with weight at most `2^-128 (√6 (n + 1 + verifyQueries) +
2 verifyQueries)² tr ρ` for an adversary making at most `n` calls (`Qrom.Sphincs.sum_hit_le`).
-/

open OracleComp OracleSpec FORS Quantum
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

variable [Params]

/-- A basis call makes one call. -/
theorem isTotalQueryBound_callBasis {β : Type} (j : Spec.Port) (B : QReg) (a : Spec.In j)
    (read : Spec.Out j → Spec.Result j → β) :
    (QComp.callBasis (spec := Spec) j B a read).IsTotalQueryBound 1 := by
  unfold QComp.callBasis
  have hq : (QuantumComp₂.query (L := LocalSig.instruments) (spec := Spec)
      (A := QReg.of ((Spec.In j).carrier × B.carrier)) j B (Equiv.refl _)).IsTotalQueryBound 1 :=
    (QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr ⟨Nat.one_pos, fun _ ↦
      QuantumComp.isTotalQueryBound_pure _ _⟩
  exact (OvGame.isTotalQueryBound_bind₂ (n := 0) (m := 1) _ (OvGame.isTotalQueryBound_act _) fun _ ↦
    OvGame.isTotalQueryBound_bind₂ (n := 1) (m := 0) _ hq fun _ ↦ OvGame.isTotalQueryBound_act _)

/-- The adversary run on the key makes one more call. -/
theorem isTotalQueryBound_withKey {A : QReg} {adv : Adversary A} {n : ℕ}
    (hadv : ∀ pk, (adv pk).IsTotalQueryBound n) : (withKey adv).IsTotalQueryBound (1 + n) := by
  refine OvGame.isTotalQueryBound_bind₂ _ (isTotalQueryBound_callBasis _ _ _ _) fun pk ↦ ?_
  rw [QuantumComp₂.map_eq_bind_pure]
  exact (OvGame.isTotalQueryBound_bind₂ _ (hadv pk) fun _ ↦
    QuantumComp.isTotalQueryBound_pure _ 0).mono (by omega)

theorem isTotalQueryBound_verifier (x : PublicKey × Forgery) :
    OracleComp.IsTotalQueryBound (verifier x) verifyQueries :=
  bound_liftH (bound_traced (bound_verify _ _ _))

open Classical in
/-- **Protected reads**, summed over the data. -/
theorem sum_prot_le (G : Input → HashOutput) {A : QReg} (adv : Adversary A) (ρ : SubState A) :
    ∑ d, OvGame.sideW (hidGame d) G .instruments (gameProg adv) ρ (fun p s ↦ evProt d s p.2.2.2) ≤
      ENNReal.ofReal (verifyQueries * (2 : ℝ)⁻¹ ^ 128) *
        (Fintype.card Data * ENNReal.ofReal ρ.matrix.trace.re) := by
  refine (OvGame.sum_sideW_protHit_le rev hidGame Prot (fun d d' s H ↦ rev_self d d' s H)
    (fun d j s ↦ rev_mono d j s) (fun d d' s H ↦ hidGame_local d d' s H)
    (fun d d' j s H ↦ hidGame_localTr d d' j s H) (fun _ _ ↦ rfl) (by positivity)
    (fun d s x ↦ card_prot_le d s x) .instruments G (gameProg adv) ρ (fun p ↦ outK p.2.2.2)
    verifyQueries (fun p ↦ card_outK_le _)).trans ?_
  gcongr
  refine (Finset.sum_le_sum fun d _ ↦ OvGame.sideW_true_le (hidGame d) G _ _ ρ).trans ?_
  simp

open Classical in
/-- **Hits**, averaged over `G`. -/
theorem sum_hit_le (d : Data) {A : QReg} (adv : Adversary A) {n : ℕ}
    (hadv : ∀ pk, (adv pk).IsTotalQueryBound n) (ρ : SubState A) :
    ∑ G : Input → HashOutput, (Fintype.card (Input → HashOutput) : ℝ≥0∞)⁻¹ *
      OvGame.sideW (hidGame d) G .instruments (withKey adv) ρ (fun p s ↦
        evHit d G (evalWithAnswerFn (hidAns d G s) (verifier p.2.2))) ≤
      ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128 *
        (√6 * (1 + n + verifyQueries : ℕ) + 2 * verifyQueries) ^ 2) *
        ENNReal.ofReal ρ.matrix.trace.re := by
  have h := OvGame.search_withVerifier_le (hidGame d) (good d) (2 ^ 128) (card_good_le d)
    (withKey adv) verifier outK verifyQueries card_outK_le (1 + n) verifyQueries
    (isTotalQueryBound_withKey hadv) isTotalQueryBound_verifier ρ
  have hc : ((2 ^ 128 : ℕ) : ℝ) / Fintype.card HashOutput = (2 : ℝ)⁻¹ ^ 128 := by
    rw [card_hashOutput]
    norm_num
  rw [hc] at h
  exact h

end Qrom.Sphincs
