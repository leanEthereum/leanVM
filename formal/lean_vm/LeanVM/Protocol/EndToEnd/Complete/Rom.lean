/-
  LeanVM.Protocol.EndToEnd.Complete.Rom

  Completeness of the leanVM verifier in the random-oracle model: the honest prover of a valid
  execution within the budget, run against the random oracle, makes the verifier reject with
  probability at most `completenessError fuel`, below `2^-128` at a fuel of `2^25` nonces per
  proof of work.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.Small
public import LeanVM.Protocol.EndToEnd.Sound.Moves
public import LeanVM.Protocol.Compile.Rom.Complete
public import LeanVM.Protocol.Verifier.Cost

/-!
# Completeness against the random oracle

`honestComp prog input t ρ fuel` is the honest prover of `honestProofOf` as an oracle
computation: the same classically chosen witness of `t`, proved by
`Rom.honestComp` with every hash a query to the random oracle. In the experiment of the
knowledge-soundness theorem with this prover as the adversary, the verifier rejects with
probability at most

  `completenessError fuel = Q · ((1 - 2^-17)^fuel + Q / 2^256)`,

`Q = 3 + 13210 · (2^27 + fuel + 1) + 13213` the queries of the prover and the verifier together
(`romComplete_leanVm`). At `fuel = 2^25`, it is below `2^-128` (`completenessError_le`): the
seventeen-bit proofs of work fail with probability `(1 - 2^-17)^(2^25) ≤ 2^-256` each.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Rom LeanVM.Protocol.Blake2sHash
open OracleComp OracleSpec
open Air.Flat (EnsembleWitness)
open scoped ENNReal

@[expose] public section

open Classical in
/-- **The honest prover against the random oracle**: the honest prover of `honestProofOf`, with
every hash a query to the random oracle; the empty proof when the execution has no witness at
admissible sizes or a proof-of-work search finds no nonce below `fuel`. -/
noncomputable def honestComp (prog : Program) (input : PublicInput) (t : Trace prog)
    (ρ fuel : ℕ) : OracleComp HashSpec Proof :=
  if h : ∃ w s, HonestFor prog input t ρ w s then
    Rom.honestComp (leanVmSeed (bytecodeWords prog) (publicDigest input))
      (leanVmProgram (bytecodeWords prog) (publicDigest input))
      (leanVmProver prog h.choose_spec.choose ρ
        (stackOf Blake2sFlock.blake2sFlockSpec prog h.choose_spec.choose h.choose)) fuel
  else pure ⟨[], []⟩

/-- The queries of the honest prover and the verifier together, at a fuel of `fuel`. -/
def completenessQueries (fuel : ℕ) : ℕ :=
  1 + 2 + leanVmCost * proverFactor costHeight fuel + leanVmQueryBound

/-- **The completeness error** at a fuel of `fuel` nonces per proof of work: every query may
complete a failed proof of work, or meet a digest the log already holds. -/
noncomputable def completenessError (fuel : ℕ) : ℝ≥0∞ :=
  (completenessQueries fuel : ℝ≥0∞) *
    (missProb Whir.queryGrindingBits ^ fuel + (completenessQueries fuel : ℝ≥0∞) / 2 ^ 256)

/-- **Completeness in the random-oracle model.** For a valid execution whose committed size is at
most `2^28`, at a valid rate, and a fuel of at most `2^64` nonces, the verifier rejects the honest
prover's proof with probability at most `completenessError fuel`. -/
theorem romComplete_leanVm {prog : Program} {input : PublicInput} {t : Trace prog} {ρ : ℕ}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ maxMu)
    (hρ : validRate ρ) {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let z ← romExperiment (honestComp prog input t ρ fuel)
        (verifierComp (leanVmSeed (bytecodeWords prog) (publicDigest input))
          (leanVmProgram (bytecodeWords prog) (publicDigest input)))}[z.1.2 = false] ≤
      completenessError fuel := by
  obtain ⟨w, s, hw, hrep, hs, hadm⟩ := exists_admissible_witness hv hbudget
  have hex : ∃ w s, HonestFor prog input t ρ w s := ⟨w, s, hρ, hw, hs, hadm, hrep⟩
  unfold honestComp
  simp only [hex, ↓reduceDIte]
  obtain ⟨-, hw', hs', hadm', -⟩ := hex.choose_spec.choose_spec
  have hq := m3Honest_stackOf (F := Blake2sFlock.blake2sFlockSpec) hw' hs' padLimbs_compress
  have hrun := runI_leanVmProgram hadm' hρ hq walkFaithful_blake2sFlockSpec
  have h := Rom.romComplete (leanVmProgram (bytecodeWords prog) (publicDigest input)) _
    (leanVmSeed (bytecodeWords prog) (publicDigest input)) (bits := Whir.queryGrindingBits)
    (by decide) (by decide) hfuel (fun _ _ _ hg ↦ Sound.grind_bits_eq _ _ hg)
    (fun chal ↦ (hrun chal).1) (fun chal ↦ (hrun chal).2)
    (costLE_leanVmProgram (bytecodeWords prog) (publicDigest input))
  refine h.trans (le_of_eq ?_)
  rfl

/-- **The numbers**: at a fuel of `2^25` nonces per proof of work, the completeness error is
below `2^-128`. -/
theorem completenessError_le : completenessError (2 ^ 25) ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 := by
  have hQ : completenessQueries (2 ^ 25) = 2216270260026 := by decide
  have hmiss : missProb Whir.queryGrindingBits ^ (2 ^ 25) ≤ (2 : ℝ≥0∞)⁻¹ ^ 256 := by
    have := missProb_pow_le Whir.queryGrindingBits 256
    rwa [show 2 ^ Whir.queryGrindingBits * 256 = 2 ^ 25 by decide] at this
  unfold completenessError
  rw [hQ]
  calc ((2216270260026 : ℕ) : ℝ≥0∞) * (missProb Whir.queryGrindingBits ^ 2 ^ 25 +
        ((2216270260026 : ℕ) : ℝ≥0∞) / 2 ^ 256)
      ≤ ((2216270260026 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 256 +
        ((2216270260026 : ℕ) : ℝ≥0∞) / 2 ^ 256) := by gcongr
    _ = ((2216270260026 * (1 + 2216270260026) : ℕ) : ℝ≥0∞) / ((2 ^ 256 : ℕ) : ℝ≥0∞) := by
        rw [← ENNReal.inv_pow, ← one_div, ENNReal.div_add_div_same, ← mul_div_assoc]
        push_cast
        ring_nf
    _ ≤ ((2 ^ 128 : ℕ) : ℝ≥0∞) / ((2 ^ 256 : ℕ) : ℝ≥0∞) := by
        gcongr
        norm_num
    _ = (2 : ℝ≥0∞)⁻¹ ^ 128 := by
        rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
          show (2 : ℝ≥0∞) ^ 256 = 2 ^ 128 * 2 ^ 128 by rw [← pow_add],
          ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
          ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, ENNReal.inv_pow]

end
end LeanVM.Protocol.EndToEnd.Complete
