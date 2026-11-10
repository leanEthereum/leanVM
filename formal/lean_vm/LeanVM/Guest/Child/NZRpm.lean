/-
  LeanVM.Guest.Child.NZRpm

  The child prover against the verifier refusing a zero challenge in the random-permutation model:
  rejected with probability at most `nzCompletenessError fuel + rpmError (completenessPermCalls
  fuel)`, below `2^-126` at a fuel of `2^25`.
-/

import LeanVM.Guest.Child.NZRom
import LeanVM.Guest.Child.RefuseZero
import LeanVM.Guest.Child.Honest
import LeanVM.Protocol.LeanVMRpm
import LeanVM.Protocol.WithHash
import LeanVM.Guest.WithHash
import LeanVM.Guest.AcceptableChild

/-!
# Refusing a zero challenge, in the random-permutation model

`romChild`: against the two random oracles, the child prover's proof (`childComp`) is rejected
by the verifier refusing a zero challenge anywhere (`Budget.verifierRefusingZero`, which is an `NZ` refusal:
`nz_refuseZero`) with probability at most
`nzCompletenessError fuel = Q · ((1 - 2^-17)^fuel + 2^-192)`, `Q = completenessQueries fuel`
(`romCompleteNZ` at leanVM's program and seed: the zero-challenge term is a union bound over
every permutation answer, each a zero challenge with probability `2^-192`, so refusing a zero at
every sampled challenge costs no more than at some). `rpmChild`: in the random-permutation model, at
most that plus `rpmError (completenessPermCalls fuel)`, the transfer of `completenessRpm`: the
prover and the verifier follow the duplex discipline (`duplexVm_childRun`) and make at most
`completenessPermCalls fuel` permutation calls (`isWeightBound_childRun`). `rpmChild_le`: at a
fuel of `2^25`, at most `2^-126`.
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol.Rom LeanVM.Protocol.KeccakHash LeanVM.Rpm OracleComp OracleSpec
open scoped ENNReal

/-! ## The program refusing a zero challenge anywhere -/

/-- The verifier program refusing a zero challenge anywhere
(`VerifierProgram.refusingZeroChallenge`). -/
def rzProgram (bytecode : List K) (publicInput : Digest) : VerifierProgram Bool :=
  (leanVmVerifierProgram bytecode publicInput).refusingZeroChallenge

theorem nz_rzProgram (bytecode : List K) (publicInput : Digest) :
    NZ (rzProgram bytecode publicInput) (leanVmVerifierProgram bytecode publicInput) :=
  nz_refuseZero _

theorem refines_rzProgram (bytecode : List K) (publicInput : Digest) :
    Limits.Refines (rzProgram bytecode publicInput) (leanVmVerifierProgram bytecode publicInput) :=
  refines_refuseZero _

theorem costLE_rzProgram (bytecode : List K) (publicInput : Digest) :
    (rzProgram bytecode publicInput).CostLE costHeight leanVmCost :=
  costs_of_refines (refines_rzProgram bytecode publicInput)
    (costLE_leanVmProgram bytecode publicInput)

/-! ## The run -/

/-- The child prover, then the verifier refusing a zero challenge. -/
noncomputable def childRun (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ fuel : ℕ) :
    OracleComp KeccakCalls Bool :=
  childComp prog input t ρ fuel >>= fun proof ↦ Budget.verifierRefusingZeroWithHash callKeccak256 callKeccakF1600 prog input proof

/-- The verifier refusing a zero challenge is the seeded verifier of `rzProgram`. -/
theorem verifierRZ_eq_comp (prog : LeanIsaProgram) (input : PublicInput) (π : Proof) :
    Budget.verifierRefusingZeroWithHash callKeccak256 callKeccakF1600 prog input π =
      verifierComp (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
        (rzProgram (bytecodeWords prog) (publicInputDigest input)) π := by
  simp only [verifierComp, Rom.verify, Budget.verifierRefusingZeroWithHash, seedRun_leanVmSeed]
  rfl

/-! ## Against the random oracles -/

/-- The completeness error of the verifier refusing a zero challenge, against the random
oracles. -/
noncomputable def nzCompletenessError (fuel : ℕ) : ℝ≥0∞ :=
  (completenessQueries fuel : ℝ≥0∞) * (missProb EndToEnd.Sound.maxGrindingBits ^ fuel + (2 : ℝ≥0∞)⁻¹ ^ 192)

set_option maxHeartbeats 1000000 in
/-- **The specification's honest prover at a witness against the random oracles**, against the
verifier refusing a zero challenge. -/
theorem romChild_at {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog} {ρ : ℕ}
    {w : Air.Flat.EnsembleWitness (leanIsaEnsemble prog t.logMemorySize)} {s : Sizes}
    (hw : HonestFor prog input t ρ w s) {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let z ← romExperiment (Rom.honestComp (leanVmSeed (bytecodeWords prog) (publicInputDigest
        input))
          (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
          (leanVmProver prog s ρ (stackOf prog s w)) fuel)
        (fun π ↦ Budget.verifierRefusingZeroWithHash callKeccak256 callKeccakF1600 prog input π)}[z.1.2 = false] ≤
      nzCompletenessError fuel := by
  obtain ⟨hρ', hw', hs', hadm', -⟩ := hw
  have hq := m3Honest_stackOf hw' hs'
  have hrun := runI_leanVmProgram (input := input) hadm' hρ' hq
  simp only [verifierRZ_eq_comp]
  have h := romCompleteNZ (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
    (rzProgram (bytecodeWords prog) (publicInputDigest input)) (nz_rzProgram _ _) _
    (leanVmSeed (bytecodeWords prog) (publicInputDigest input)) (bits := EndToEnd.Sound.maxGrindingBits)
    (by decide) (by decide) hfuel (fun _ _ _ hg ↦ EndToEnd.Sound.grind_bits_ok _ _ hg)
    (fun chal ↦ (hrun chal).1) (fun chal ↦ (hrun chal).2)
    (costLE_leanVmProgram (bytecodeWords prog) (publicInputDigest input))
    (costLE_rzProgram (bytecodeWords prog) (publicInputDigest input))
  refine h.trans (le_of_eq ?_)
  rfl

/-- **The child prover against the random oracles.** -/
theorem romChild {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog} {ρ : ℕ}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ maxMu)
    (hρ : validRate ρ) {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let z ← romExperiment (childComp prog input t ρ fuel)
        (fun π ↦ Budget.verifierRefusingZeroWithHash callKeccak256 callKeccakF1600 prog input π)}[z.1.2 = false] ≤
      nzCompletenessError fuel := by
  have hex := exists_childFor hv hbudget hρ
  unfold childComp
  simp only [hex, ↓reduceDIte]
  exact romChild_at hex.choose_spec.choose_spec.1 hfuel

/-! ## The discipline and the calls -/

theorem duplexVm_childComp (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog)
    (ρ fuel : ℕ) : DuplexVm (childComp prog input t ρ fuel) [] := by
  unfold childComp
  split
  · exact duplexVm_romHonestComp prog input _ fuel
  · trivial

theorem duplexVm_verifierRZ (prog : LeanIsaProgram) (input : PublicInput) (proof : Proof) :
    DuplexVm (Budget.verifierRefusingZeroWithHash callKeccak256 callKeccakF1600 prog input proof) [] := by
  rw [duplexVm_iff_duplexP]
  simp only [Budget.verifierRefusingZeroWithHash]
  exact (duplexP_seedWith _ _ []).bind fun seed h' hs ↦ duplexP_runProof _ hs _

theorem duplexVm_childRun (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ
    fuel : ℕ) :
    DuplexVm (childRun prog input t ρ fuel) [] :=
  (duplexVm_childComp prog input t ρ fuel).bind fun proof ↦ duplexVm_verifierRZ prog input proof

/-- A refining program commits words no wider. -/
theorem widthsLE_of_refines {α : Type} {W : ℕ} {P' P : VerifierProgram α} (h : Limits.Refines
    P' P) :
    WidthsLE W P → WidthsLE W P' := by
  induction h with
  | fail P => intro _; trivial
  | ret a => intro hc; exact hc
  | read _ ih => intro hc; exact fun x ↦ ih x (hc x)
  | sample _ ih => intro hc; exact fun x ↦ ih x (hc x)
  | grind _ ih => intro hc; exact ih hc
  | commit _ ih => intro hc; exact ⟨hc.1, ih hc.2⟩
  | query _ ih => intro hc; exact fun r ↦ ih r (hc r)

theorem allQ_verifierRZ (prog : LeanIsaProgram) (input : PublicInput) (proof : Proof) :
    AllQueriesSatisfy (Budget.verifierRefusingZeroWithHash callKeccak256 callKeccakF1600 prog input proof) Short := by
  rw [verifierRZ_eq_comp]
  exact allQueriesSatisfy_bind (allQ_seedRun prog input) fun seed ↦
    allQ_runProof _ seed proof (widthsLE_of_refines (refines_rzProgram _ _)
      (widthsLE_leanVmProgram _ _))

set_option maxHeartbeats 1000000 in
theorem allQ_childComp (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ
    fuel : ℕ) :
    AllQueriesSatisfy (childComp prog input t ρ fuel) Short := by
  unfold childComp
  split
  · rename_i hex
    obtain ⟨⟨hρ', hw', hs', hadm', -⟩, -⟩ := hex.choose_spec.choose_spec
    have hq := m3Honest_stackOf hw' hs'
    exact allQ_romHonestComp prog input _ fuel fun chal ↦
      (runI_leanVmProgram (input := input) hadm' hρ' hq chal).2
  · exact allQ_pure _

theorem isTotalQueryBound_childComp (prog : LeanIsaProgram) (input : PublicInput) (t :
    Execution prog)
    (ρ fuel : ℕ) :
    IsTotalQueryBound (childComp prog input t ρ fuel) (2 + 56097 * (2 ^ 31 + 2 * fuel + 2)) := by
  unfold childComp
  split
  · rename_i hex
    have h := Rom.isTotalQueryBound_honestComp
      (costLE_leanVmProgram (bytecodeWords prog) (publicInputDigest input)) (leanVmProver
        prog hex.choose_spec.choose ρ (LeanIsa.stackOf prog hex.choose_spec.choose hex.choose))
      fuel (σ := leanVmSeed (bytecodeWords prog) (publicInputDigest input))
    have hc : leanVmCost = 56097 := by decide
    rw [hc] at h
    exact h
  · trivial

/-- **A prover of at most `2 + 56097 · (2^31 + 2·fuel + 2)` short queries and the verifier
refusing a zero challenge make at most `completenessPermCalls fuel` permutation calls.** -/
theorem isWeightBound_proverNZ {X : OracleComp KeccakCalls Proof} (prog : LeanIsaProgram)
    (input : PublicInput) {fuel : ℕ}
    (hX : IsTotalQueryBound X (2 + 56097 * (2 ^ 31 + 2 * fuel + 2)))
    (hXq : AllQueriesSatisfy X Short) :
    Common.QueryCostAtMost (X >>= fun proof ↦ Budget.verifierRefusingZeroWithHash callKeccak256 callKeccakF1600 prog input proof)
      hashBlocks (completenessPermCalls fuel) := by
  have hN : IsTotalQueryBound (X >>= fun proof ↦ Budget.verifierRefusingZeroWithHash callKeccak256 callKeccakF1600 prog input proof)
      (14028 + 56097 * (2 ^ 31 + 2 * fuel + 2)) := by
    have h := isTotalQueryBound_bind hX
      fun proof ↦ by
        have := isTotalQueryBound_verifierComp
          (costLE_rzProgram (bytecodeWords prog) (publicInputDigest input))
          (leanVmSeed (bytecodeWords prog) (publicInputDigest input)) proof
        rw [← verifierRZ_eq_comp] at this
        exact this
    refine h.mono ?_
    have : leanVmCost / 4 = 12004 := by decide
    simp only [leanVmSeed, List.length_cons, List.length_nil, this]
    omega
  exact isWeightBound_of_isTotalQueryBound hashBlocks (2 ^ 32) hN
    ((allQueriesSatisfy_bind hXq fun proof ↦
      allQ_verifierRZ prog input proof).mono fun _ h ↦ hashBlocks_le_of_short h)

/-- **The child prover and the verifier refusing a zero challenge make at most
`completenessPermCalls fuel` permutation calls.** -/
theorem isWeightBound_childRun (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog)
    (ρ fuel : ℕ) :
    Common.QueryCostAtMost (childRun prog input t ρ fuel) hashBlocks (completenessPermCalls fuel) :=
  isWeightBound_proverNZ prog input (isTotalQueryBound_childComp prog input t ρ fuel)
    (allQ_childComp prog input t ρ fuel)

/-! ## In the random-permutation model -/

-- As for `shaped_of`.
set_option maxHeartbeats 1000000 in
/-- **The specification's honest prover at a witness against the verifier refusing a zero
challenge, in the random-permutation model.** -/
theorem rpmChild_at {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog} {ρ : ℕ}
    {w : Air.Flat.EnsembleWitness (leanIsaEnsemble prog t.logMemorySize)} {s : Sizes}
    (hw : HonestFor prog input t ρ w s) {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let v ← (simulateQ keccakCallsOverRandomPermutation
        (Rom.honestComp (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
          (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
          (leanVmProver prog s ρ (stackOf prog s w)) fuel >>= fun proof ↦
            Budget.verifierRefusingZeroWithHash callKeccak256 callKeccakF1600 prog input proof)).run' []}[v = false] ≤
      nzCompletenessError fuel + rpmError (completenessPermCalls fuel) :=
  rpm_le_of_rom _ _ ((duplexVm_romHonestComp prog input _ fuel).bind fun proof ↦
      duplexVm_verifierRZ prog input proof)
    (isWeightBound_proverNZ prog input (isTotalQueryBound_romHonestComp prog input _ fuel)
      (allQ_romHonestComp prog input _ fuel (shaped_of hw)))
    (romChild_at hw hfuel)

/-- **The child prover against the verifier refusing a zero challenge, in the
random-permutation model.** -/
theorem rpmChild {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog} {ρ : ℕ}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ 28)
    (hρ : 1 ≤ ρ ∧ ρ ≤ 4) {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let v ← (simulateQ keccakCallsOverRandomPermutation (childRun prog input t ρ fuel)).run' []}[v = false] ≤
      nzCompletenessError fuel + rpmError (completenessPermCalls fuel) :=
  rpm_le_of_rom (childComp prog input t ρ fuel)
    (fun proof ↦ Budget.verifierRefusingZeroWithHash callKeccak256 callKeccakF1600 prog input proof)
    (duplexVm_childRun prog input t ρ fuel) (isWeightBound_childRun prog input t ρ fuel)
    (romChild hv hbudget hρ hfuel)

/-! ## The numbers -/

/-- **At a fuel of `2^25` nonces per proof of work, at most `2^-126`**: `completenessRpm_le`'s two
terms, each at most `2^-257`, and `Q · 2^-192 ≤ 2^44 · 2^-192`, each taken at `2^-128`. -/
theorem rpmChild_le :
    nzCompletenessError (2 ^ 25) + rpmError (completenessPermCalls (2 ^ 25)) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 126 := by
  have hQ : completenessQueries (2 ^ 25) ≤ 2 ^ 44 := by decide
  have hz : (completenessQueries (2 ^ 25) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 192 ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 :=
    calc (completenessQueries (2 ^ 25) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 192
        ≤ (2 : ℝ≥0∞) ^ 44 * (2 : ℝ≥0∞)⁻¹ ^ (44 + 148) := by
          gcongr
          exact_mod_cast hQ
      _ = (2 : ℝ≥0∞)⁻¹ ^ 148 := Common.two_pow_mul_inv_pow 44 148
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 := Common.inv_two_pow_le_of_le (by norm_num)
  have e : nzCompletenessError (2 ^ 25) = EndToEnd.Complete.completenessError (2 ^ 25) +
      (completenessQueries (2 ^ 25) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 192 := by
    rw [nzCompletenessError, mul_add]
    rfl
  rw [e]
  calc EndToEnd.Complete.completenessError (2 ^ 25) +
        (completenessQueries (2 ^ 25) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 192 +
        rpmError (completenessPermCalls (2 ^ 25))
      ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 + (2 : ℝ≥0∞)⁻¹ ^ 128 + (2 : ℝ≥0∞)⁻¹ ^ 128 :=
        add_le_add (add_le_add (EndToEnd.Complete.completenessError_le.trans
            (Common.inv_two_pow_le_of_le (by norm_num))) hz)
          (rpmError_completenessPermCalls_le.trans (Common.inv_two_pow_le_of_le (by norm_num)))
    _ ≤ 4 * (2 : ℝ≥0∞)⁻¹ ^ 128 := by
        rw [show (4 : ℝ≥0∞) = 1 + 1 + 1 + 1 by norm_num]
        simp only [add_mul, one_mul]
        exact le_self_add
    _ = (2 : ℝ≥0∞)⁻¹ ^ 126 := by
        rw [show (4 : ℝ≥0∞) = 2 ^ 2 by norm_num, show (128 : ℕ) = 2 + 126 from rfl]
        exact Common.two_pow_mul_inv_pow 2 126

/-- **The child prover in the random-permutation model, at `2^25` nonces**: rejected by the
verifier refusing a zero challenge with probability at most `2^-126`. -/
theorem rpmChild_126 {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog} {ρ : ℕ}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ 28)
    (hρ : 1 ≤ ρ ∧ ρ ≤ 4) :
    Pr{let v ← (simulateQ keccakCallsOverRandomPermutation (childRun prog input t ρ (2 ^ 25))).run' []}[v = false] ≤
      (2 : ℝ≥0∞)⁻¹ ^ 126 :=
  (rpmChild hv hbudget hρ (by norm_num)).trans rpmChild_le

end LeanVM.Guest.Child
