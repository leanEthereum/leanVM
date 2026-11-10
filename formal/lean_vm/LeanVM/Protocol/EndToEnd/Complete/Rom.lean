/-
  LeanVM.Protocol.EndToEnd.Complete.Rom

  Completeness of the leanVM verifier in the random-oracle model: the honest prover of a valid
  execution within the budget, run against the random oracles, makes the verifier reject with
  probability at most `completenessError fuel`, below `2^-257` at a fuel of `2^33` nonces per
  proof of work.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.Small
public import LeanVM.Protocol.EndToEnd.Complete.BusDepth
public import LeanVM.Protocol.Errors
public import LeanVM.Protocol.EndToEnd.Sound.Moves
public import LeanVM.Protocol.Compile.Rom.Complete
public import LeanVM.Protocol.Verifier.Cost
public import LeanVM.Protocol.WithHash

/-!
# Completeness against the random oracle

`honestComp prog input t ρ fuel` is the honest prover of `honestProofOf` as an oracle
computation: the same classically chosen witness of `t`, proved by `Rom.honestComp` with every
hash a query to the random oracle for Keccak-256 and every permutation one to the random oracle
for Keccak-f[1600]. In the experiment of the knowledge-soundness theorem with this prover as the
adversary, the verifier rejects with probability at most (`Rom.romComplete`)

  `completenessError fuel = Q · (1 - 2^-25)^fuel`,

`Q = (1 + 1) + 53036 · (2^27 + 2·fuel + 2) + 13261` the queries of the prover and the verifier
together (`completenessQueries`): the seed's hash and permutation, `leanVmCost = 53036`
moves of the program each costing the prover at most `proverFactor costHeight fuel =
2^27 + 2·fuel + 2` queries, and the verifier's `leanVmQueryBound = 13261`
(`romComplete_leanVm`). Every proof of work the honest prover meets has at most `25` bits, the
bus's at the widest (`busGrindLE_twentyFive`), WHIR's at most `17`. At `fuel = 2^33`, the error is
below `2^-257` (`completenessError_two_pow_33_le`): `Q ≤ 2^51`, and a proof of work of at most `25`
bits fails with probability `(1 - 2^-25)^(2^33) ≤ e^-256 < 2^-320`.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Rom LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open Air.Flat (EnsembleWitness)
open scoped ENNReal

@[expose] public section

open Classical in
/-- **The honest prover against the random oracle**: the honest prover of `honestProofOf`, with
every hash a query to the random oracle; the empty proof when the execution has no witness at
admissible sizes or a proof-of-work search finds no nonce below `fuel`. -/
noncomputable def honestComp (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog)
    (ρ fuel : ℕ) : OracleComp KeccakCalls Proof :=
  if h : ∃ w s, HonestFor prog input t ρ w s then
    Rom.honestComp (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
      (leanVmProver prog h.choose_spec.choose ρ (stackOf prog h.choose_spec.choose h.choose)) fuel
  else pure ⟨[], []⟩

/-- The queries of the honest prover and the verifier together, at a fuel of `fuel`: the seed's
hash and permutation, the program's moves at the prover's factor, and the verifier's bound. -/
def completenessQueries (fuel : ℕ) : ℕ :=
  1 + 1 + leanVmCost * proverFactor costHeight fuel + leanVmQueryBound

/-- **The completeness error** at a fuel of `fuel` nonces per proof of work: every query may
complete a proof of work of at most `25` bits whose nonces all failed. -/
noncomputable def completenessError (fuel : ℕ) : ℝ≥0∞ :=
  (completenessQueries fuel : ℝ≥0∞) * missProb 25 ^ fuel

/-- **Every layout the verifier builds for the program's bytecode within the stack's cap has its
bus grind at most `25` bits**: the push tree is no deeper than the stack (`busDepth_le_leanIsaμ`),
which has at most `28` variables. -/
theorem busGrindLE_twentyFive {prog : LeanIsaProgram} {logMemory : ℕ} {rows : List ℕ}
    {layout : Verifier.Layout} (h : buildLayout (bytecodeWords prog) logMemory rows = some layout)
    (hmax : layout.stackLog ≤ Whir.maxLogStack) : Sound.BusGrindLE 25 layout := by
  intro _
  have hc : rows.length = 6 ∧ 16 ≤ logMemory := by
    unfold buildLayout at h
    split at h
    · cases h
    · split_ifs at h with hc
      exact ⟨hc.2.2.2.2.2.trans rfl, hc.2.1⟩
  obtain ⟨s, hs1, hs2⟩ : ∃ s : Sizes, s.logMem = logMemory ∧ tableRows s = rows := by
    refine ⟨⟨logMemory, by omega, fun j ↦ rows.getD j 0⟩, rfl, ?_⟩
    apply List.ext_getElem (by simp [tableRows, hc.1])
    intro i h1 h2
    simp only [tableRows, List.getElem_ofFn]
    exact List.getD_eq_getElem _ _ h2
  have hb := buildLayout_eq prog s
  rw [hs1, hs2, h] at hb
  split_ifs at hb
  · simp only [Option.some.injEq] at hb
    subst hb
    rw [busLayout_depth_verifier]
    rw [stackLog_verifierLayout] at hmax
    have hD := (busDepth_le_leanIsaμ prog s).trans hmax
    simp only [Whir.maxLogStack] at hD
    exact Sound.grindingBits_le_of (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- **Every proof of work of the leanVM verifier, on the program's bytecode, has at most `25`
bits.** -/
theorem moves_leanVm_twentyFive (prog : LeanIsaProgram) (publicInput : Digest) :
    Sound.Moves (· ≤ 25) True (fun _ ↦ True) (fun _ ↦ False)
      (leanVmVerifierProgram (bytecodeWords prog) publicInput) :=
  Sound.moves_leanVmProgram_le (by norm_num) _ _ fun _ _ _ ↦ busGrindLE_twentyFive

/-- **Completeness in the random-oracle model, at a witness.** For an honest witness `w` at the
sizes `s` (`HonestFor`) and a fuel of at most `2^64` nonces, the verifier rejects the proof of the
specification's honest prover at that witness with probability at most `completenessError fuel`. -/
theorem romComplete_at {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog} {ρ : ℕ}
    {w : EnsembleWitness (leanIsaEnsemble prog t.logMemorySize)} {s : Sizes}
    (hw : HonestFor prog input t ρ w s)
    {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let z ← romExperiment (Rom.honestComp (leanVmSeed (bytecodeWords prog) (publicInputDigest
        input))
          (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
          (leanVmProver prog s ρ (stackOf prog s w)) fuel)
        (verifierComp (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
          (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)))}[z.1.2 = false] ≤
      completenessError fuel := by
  obtain ⟨hρ, hw', hs', hadm', -⟩ := hw
  have hq := m3Honest_stackOf hw' hs'
  have hrun := runI_leanVmProgram hadm' hρ hq
  -- Unifying through the strategy unfolds it under Lean 4.35: name it first.
  generalize leanVmProver prog s ρ (stackOf prog s w) = S at hrun ⊢
  have h := Rom.romComplete (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) _
    (leanVmSeed (bytecodeWords prog) (publicInputDigest input)) (bits := 25)
    (by norm_num) hfuel (Sound.grindThenSample_leanVmProgram _ _)
    (fun _ _ _ hg _ ↦ ((moves_leanVm_twentyFive prog _).after hg).1)
    (fun chal ↦ (hrun chal).1) (fun chal ↦ (hrun chal).2)
    (costLE_leanVmProgram (bytecodeWords prog) (publicInputDigest input))
  refine h.trans (le_of_eq ?_)
  rfl

/-- **Completeness in the random-oracle model.** For a valid execution whose committed size is at
most `2^28`, at a valid rate, and a fuel of at most `2^64` nonces, the verifier rejects the honest
prover's proof with probability at most `completenessError fuel`. -/
theorem romComplete_leanVm {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    {ρ : ℕ}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ maxMu)
    (hρ : validRate ρ) {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let z ← romExperiment (honestComp prog input t ρ fuel)
        (verifierComp (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
          (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)))}[z.1.2 = false] ≤
      completenessError fuel := by
  obtain ⟨w, s, hw, hrep, hs, hadm⟩ := exists_admissible_witness hv hbudget
  have hex : ∃ w s, HonestFor prog input t ρ w s := ⟨w, s, hρ, hw, hs, hadm, hrep⟩
  unfold honestComp
  simp only [hex, ↓reduceDIte]
  exact romComplete_at hex.choose_spec.choose_spec hfuel

/-- **The numbers**: at a fuel of `2^33` nonces per proof of work, the completeness error is
below `2^-257`: at most `2^51` queries, each missing a proof of work of at most `25` bits with
probability `(1 - 2^-25)^(2^33) ≤ 2^-320` (`missProb_pow_four_le`). -/
theorem completenessError_two_pow_33_le :
    LeanVM.completenessError (2 ^ 33) ≤ (2 : ℝ≥0∞)⁻¹ ^ 257 := by
  have hQ : LeanVM.completenessQueries (2 ^ 33) ≤ 2 ^ 51 := by
    norm_num [LeanVM.completenessQueries]
  have hmiss : (1 - (2 : ℝ≥0∞)⁻¹ ^ 25) ^ (2 ^ 33) ≤ (2 : ℝ≥0∞)⁻¹ ^ (51 + 269) := by
    have := missProb_pow_four_le 25 64
    rwa [missProb, show 2 ^ 25 * 4 * 64 = 2 ^ 33 by norm_num] at this
  unfold LeanVM.completenessError
  calc (LeanVM.completenessQueries (2 ^ 33) : ℝ≥0∞) * (1 - (2 : ℝ≥0∞)⁻¹ ^ 25) ^ 2 ^ 33
      ≤ (2 : ℝ≥0∞) ^ 51 * (2 : ℝ≥0∞)⁻¹ ^ (51 + 269) := by
        gcongr
        exact_mod_cast hQ
    _ = (2 : ℝ≥0∞)⁻¹ ^ 269 := by
        rw [pow_add, ← mul_assoc, ← mul_pow,
          ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 257 :=
        pow_le_pow_of_le_one zero_le (ENNReal.inv_le_one.2 one_le_two) (by norm_num)

end
end LeanVM.Protocol.EndToEnd.Complete
