module

public import Quantum.Xmss.GameReads

@[expose] public section

/-!
# The game in runtime 1

The composition of G1 → G2 (`qrpm_game_eq_reads`: the game's law in the QRPM is the average over
`π` and uniform `t` of the read runtime's law of `gameReads π sch Sch A` after the honest
evaluation of key generation) with G2 → runtime 1 (`spongeEvalDistMap_eq_tableLaw`: that average
over `t` is the mixture, over the law `tableLaw` of the honest evaluation `b` of key generation,
of runtime 1 started with the cells of `b` hardwired, running `gameReads π sch Sch A b`), for a
scheme `sch` of the statement's game that is the hash-query scheme `Sch` over `π`.

* `qrpm_game_eq_runtime1`: the game's observed law in the QRPM is `|Perm|⁻¹ • ∑ π, ∑ b,
  tableLaw b • (runtime 1 with readsHw b.2 hardwired).evalDistMap (gameReads π sch Sch A b)`.
* `prob_game_eq_runtime1`, `winProb_eq_runtime1`: the winning probability (observing the game's
  win bit), at a seed and averaged over the seed law as `winProb` is, in the same form.

The image of key generation's evaluations needs `DecidableEq` on the secret keys, which the
statements take as a hypothesis (`classical` supplies one).

The sums over permutations and over the functions `t` are huge at the Keccak sizes, so the
evaluation of a mixture of measures at a set is proved for abstract index types
(`smul_sum_sum_smul_apply`) and applied with named summands (`keygenImage`, `keygenLaw`,
`runtime1Law`), so that the kernel only compares syntactically equal sums.
-/

open MeasureTheory
open scoped ENNReal

namespace Quantum.SufCma

open Quantum Quantum.Sponge HashSig Common Common.SufCma
open Quantum.Xmss (X Z keccakStateEquiv)

/-- A scaled sum of finite mixtures of measures, evaluated at a set. -/
theorem smul_sum_sum_smul_apply {P B γ : Type*} [MeasurableSpace γ] (c : ℝ≥0∞) (S : Finset P)
    (s : P → Finset B) (w : P → B → ℝ≥0∞) (μ : P → B → Measure γ) (E : Set γ) :
    (c • ∑ p ∈ S, ∑ b ∈ s p, w p b • μ p b) E = c * ∑ p ∈ S, ∑ b ∈ s p, w p b * μ p b E := by
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]

variable {M : Type} [Fintype M] [DecidableEq M] {Seed PK SK Req Resp F : Type}
  (sch : Scheme Seed PK SK Req Resp F) (Sch : SchemeWithHash Seed PK SK Req Resp F)

/-- **The game in the QRPM is runtime 1**: the quantum SUF-CMA game's observed law is the average
over `π` of the mixture, over the law `tableLaw` of the honest evaluation `b` of key generation
against uniform `t`, of runtime 1 started with the honest cells of `b` and their values hardwired
(`readsHw b.2`), running the game's reads `gameReads π sch Sch A b` after key generation. -/
theorem qrpm_game_eq_runtime1 [DecidableEq PK] [DecidableEq SK]
    (hsch : sch = Sch.overPermutation) (m₀ : M) (S0 : Seed)
    (A : Adversary PK Req Resp F (X × Z)) (ρ : SubState (QReg.of Unit)) {γ : Type*}
    [MeasurableSpace γ] (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    qrpmEvalDistMap .instruments (game sch keccakStateEquiv S0 A) ρ (fun _ ↦ f) =
      (Fintype.card (Equiv.Perm (X × Z)) : ℝ≥0∞)⁻¹ • ∑ π : Equiv.Perm (X × Z),
        ∑ b ∈ Finset.univ.image (fun t ↦ honestEval t π (Sch.keygen S0)),
          tableLaw (fun t ↦ honestEval t π (Sch.keygen S0)) b •
            (spongeHardwiredReadRuntime X Z (readsHw b.2) m₀).evalDistMap .instruments
              (gameReads M π sch Sch A b) ρ f :=
  (qrpm_game_eq_reads sch Sch hsch m₀ S0 A ρ f).trans (congrArg (HSMul.hSMul _)
    (Finset.sum_congr rfl fun π _ ↦ spongeEvalDistMap_eq_tableLaw π
      (Sch.keygen S0) m₀ .instruments (gameReads M π sch Sch A) ρ f))

section named

variable [DecidableEq PK] [DecidableEq SK]

/-- The honest evaluations of key generation from `S0` against `π`, over all `t`. -/
noncomputable def keygenImage (S0 : Seed) (π : Equiv.Perm (X × Z)) :
    Finset ((PK × SK) × List (SpongeRead X Z)) :=
  Finset.univ.image fun t ↦ honestEval t π (Sch.keygen S0)

/-- The law `tableLaw` of the honest evaluation of key generation from `S0` against `π`. -/
noncomputable def keygenLaw (S0 : Seed) (π : Equiv.Perm (X × Z))
    (b : (PK × SK) × List (SpongeRead X Z)) : ℝ≥0∞ :=
  tableLaw (fun t ↦ honestEval t π (Sch.keygen S0)) b

variable (M) in
/-- The law of runtime 1 started with the honest cells of `b` hardwired, running the game's
reads after key generation. -/
noncomputable def runtime1Law (m₀ : M) (A : Adversary PK Req Resp F (X × Z))
    (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) (π : Equiv.Perm (X × Z))
    (b : (PK × SK) × List (SpongeRead X Z)) : Measure γ :=
  (spongeHardwiredReadRuntime X Z (readsHw b.2) m₀).evalDistMap .instruments
    (gameReads M π sch Sch A b) ρ f

/-- **The winning probability in runtime 1, at a seed**: `qrpm_game_eq_runtime1` observing the
game's win bit. -/
theorem prob_game_eq_runtime1 (hsch : sch = Sch.overPermutation) (m₀ : M) (S0 : Seed)
    (A : Adversary PK Req Resp F (X × Z)) :
    qrpmEvalDistMap .instruments (game sch keccakStateEquiv S0 A) (SubState.basis ())
        (fun _ p ↦ p.2.2) {true} =
      (Fintype.card (Equiv.Perm (X × Z)) : ℝ≥0∞)⁻¹ * ∑ π : Equiv.Perm (X × Z),
        ∑ b ∈ Finset.univ.image (fun t ↦ honestEval t π (Sch.keygen S0)),
          tableLaw (fun t ↦ honestEval t π (Sch.keygen S0)) b *
            (spongeHardwiredReadRuntime X Z (readsHw b.2) m₀).evalDistMap .instruments
              (gameReads M π sch Sch A b) (SubState.basis ()) (fun p ↦ p.2.2) {true} := by
  have h : qrpmEvalDistMap .instruments (game sch keccakStateEquiv S0 A) (SubState.basis ())
      (fun _ p ↦ p.2.2) =
      (Fintype.card (Equiv.Perm (X × Z)) : ℝ≥0∞)⁻¹ • ∑ π : Equiv.Perm (X × Z),
        ∑ b ∈ keygenImage Sch S0 π, keygenLaw Sch S0 π b •
          runtime1Law M sch Sch m₀ A (SubState.basis ()) (fun p ↦ p.2.2) π b :=
    (qrpm_game_eq_runtime1 sch Sch hsch m₀ S0 A (SubState.basis ()) fun p ↦ p.2.2).trans
      (congrArg (HSMul.hSMul _) (Finset.sum_congr rfl fun π _ ↦
        Finset.sum_congr (rfl : _ = keygenImage Sch S0 π) fun b _ ↦
          congr_arg₂ HSMul.hSMul (rfl : _ = keygenLaw Sch S0 π b)
            (rfl : _ = runtime1Law M sch Sch m₀ A (SubState.basis ()) (fun p ↦ p.2.2) π b)))
  refine (congrArg (fun μ : Measure Bool ↦ μ {true}) h).trans
    ((smul_sum_sum_smul_apply _ _ (keygenImage Sch S0) (keygenLaw Sch S0)
      (runtime1Law M sch Sch m₀ A (SubState.basis ()) fun p ↦ p.2.2) {true}).trans
        (congrArg (HMul.hMul _) (Finset.sum_congr rfl fun π _ ↦
          Finset.sum_congr (rfl : keygenImage Sch S0 π = _) fun b _ ↦
            congr_arg₂ HMul.hMul (rfl : keygenLaw Sch S0 π b = _)
              (congrArg (fun μ : Measure Bool ↦ μ {true})
                (rfl : runtime1Law M sch Sch m₀ A (SubState.basis ()) (fun p ↦ p.2.2) π b =
                  _)))))

/-- **The winning probability in runtime 1**: `qrpm_game_eq_runtime1` observing the game's win
bit, averaged over the seed law as `winProb` is. -/
theorem winProb_eq_runtime1 [Fintype Seed] (hsch : sch = Sch.overPermutation) (m₀ : M)
    (A : Adversary PK Req Resp F (X × Z)) :
    winProb sch keccakStateEquiv A = ∑ S0 : Seed, Pr{let s ← sch.sampleSeed}[s = S0] *
      ((Fintype.card (Equiv.Perm (X × Z)) : ℝ≥0∞)⁻¹ * ∑ π : Equiv.Perm (X × Z),
        ∑ b ∈ Finset.univ.image (fun t ↦ honestEval t π (Sch.keygen S0)),
          tableLaw (fun t ↦ honestEval t π (Sch.keygen S0)) b *
            (spongeHardwiredReadRuntime X Z (readsHw b.2) m₀).evalDistMap .instruments
              (gameReads M π sch Sch A b) (SubState.basis ()) (fun p ↦ p.2.2) {true}) := by
  unfold winProb
  exact Finset.sum_congr rfl fun S0 _ ↦
    congrArg (HMul.hMul _) (prob_game_eq_runtime1 sch Sch hsch m₀ S0 A)

end named

end Quantum.SufCma

end
