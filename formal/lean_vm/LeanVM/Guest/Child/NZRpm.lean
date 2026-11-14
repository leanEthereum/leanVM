/-
  LeanVM.Guest.Child.NZRpm

  The child prover against the statement's refusing verifier in the random-permutation model:
  rejected with probability at most `childCompletenessError fuel + rpmError (completenessPermCalls
  fuel)`, below `2^-100` at a fuel of `2^33`.
-/

import LeanVM.Guest.Child.NZRom
import LeanVM.Protocol.LeanVMRpm
import LeanVM.Protocol.WithHash
import LeanVM.Guest.WithHash

/-!
# The refusing verifier, in the random-permutation model

`rpmChild_at`: the transfer of `romChild_at` (`rpm_le_of_rom`): the prover and the statement's
refusing verifier (`Budget.verifierRefusingZeroWithHash`) follow the duplex discipline
(`duplexVm_verifierRZ`) and make at most `completenessPermCalls fuel` permutation calls
(`isWeightBound_proverRZ`). `rpmChild_le`: at a fuel of `2^33`, at most `2^-100`.
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol.Rom LeanVM.Protocol.KeccakHash LeanVM.Rpm OracleComp OracleSpec
open scoped ENNReal

/-- The statement's refusing verifier is the seeded verifier of `Limits.refusingZeroProgram`. -/
theorem verifierRZ_eq_comp (prog : LeanIsaProgram) (input : PublicInput) (π : Proof) :
    Budget.verifierRefusingZeroWithHash callKeccak256 callKeccakF1600 prog input π =
      verifierComp (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
        (Limits.refusingZeroProgram (bytecodeWords prog) (publicInputDigest input)) π := by
  simp only [verifierComp, Rom.verify, Budget.verifierRefusingZeroWithHash, seedRun_leanVmSeed]
  rfl

theorem duplexVm_verifierRZ (prog : LeanIsaProgram) (input : PublicInput) (proof : Proof) :
    DuplexVm (Budget.verifierRefusingZeroWithHash callKeccak256 callKeccakF1600 prog input proof)
      [] := by
  rw [duplexVm_iff_duplexP]
  simp only [Budget.verifierRefusingZeroWithHash]
  exact (duplexP_seedWith _ _ []).bind fun seed h' hs ↦ duplexP_runProof _ hs _

/-- A refining program commits words no wider. -/
theorem widthsLE_of_refines {α : Type} {W : ℕ} {P' P : VerifierProgram α}
    (h : Limits.Refines P' P) : WidthsLE W P → WidthsLE W P' := by
  induction h with
  | fail P => intro _; trivial
  | ret a => intro hc; exact hc
  | read _ ih => intro hc; exact fun x ↦ ih x (hc x)
  | sample _ ih => intro hc; exact fun x ↦ ih x (hc x)
  | grind _ ih => intro hc; exact ih hc
  | commit _ ih => intro hc; exact ⟨hc.1, ih hc.2⟩
  | query _ ih => intro hc; exact fun r ↦ ih r (hc r)

theorem allQ_verifierRZ (prog : LeanIsaProgram) (input : PublicInput) (proof : Proof) :
    AllQueriesSatisfy
      (Budget.verifierRefusingZeroWithHash callKeccak256 callKeccakF1600 prog input proof)
      Short := by
  rw [verifierRZ_eq_comp]
  exact allQueriesSatisfy_bind (allQ_seedRun prog input) fun seed ↦
    allQ_runProof _ seed proof (widthsLE_of_refines (Limits.refusingZeroProgram_refines _ _)
      (widthsLE_leanVmProgram _ _))

/-- **A prover of at most `2 + 54825 · (2^29 + 2·fuel + 2)` short queries and the refusing
verifier make at most `completenessPermCalls fuel` permutation calls.** -/
theorem isWeightBound_proverRZ {X : OracleComp KeccakCalls Proof} (prog : LeanIsaProgram)
    (input : PublicInput) {fuel : ℕ}
    (hX : IsTotalQueryBound X (2 + 54825 * (2 ^ 29 + 2 * fuel + 2)))
    (hXq : AllQueriesSatisfy X Short) :
    Common.QueryCostAtMost (X >>= fun proof ↦
      Budget.verifierRefusingZeroWithHash callKeccak256 callKeccakF1600 prog input proof)
      hashBlocks (completenessPermCalls fuel) := by
  have hP := costLE_leanVmProgram (bytecodeWords prog) (publicInputDigest input)
  have hN : IsTotalQueryBound (X >>= fun proof ↦
      Budget.verifierRefusingZeroWithHash callKeccak256 callKeccakF1600 prog input proof)
      (LeanVM.completenessQueries fuel) := by
    have h := isTotalQueryBound_bind hX fun proof ↦ by
      have := isTotalQueryBound_verifierComp
        (costs_of_refines (Limits.refusingZeroProgram_refines (bytecodeWords prog)
          (publicInputDigest input)) hP)
        (leanVmSeed (bytecodeWords prog) (publicInputDigest input)) proof
      rw [← verifierRZ_eq_comp] at this
      exact this
    refine h.mono ?_
    have : leanVmCost / 4 = 13706 := by decide
    simp only [leanVmSeed, List.length_cons, List.length_nil, this, LeanVM.completenessQueries]
    omega
  exact isWeightBound_of_isTotalQueryBound hashBlocks (2 ^ 30) hN
    ((allQueriesSatisfy_bind hXq fun proof ↦
      allQ_verifierRZ prog input proof).mono fun _ h ↦ hashBlocks_le_of_short h)

-- As for `shaped_of`.
set_option maxHeartbeats 1000000 in
/-- **The specification's honest prover at a witness against the statement's refusing verifier,
in the random-permutation model.** -/
theorem rpmChild_at {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog} {ρ : ℕ}
    {w : Air.Flat.EnsembleWitness (leanIsaEnsemble prog t.logMemorySize)} {s : Sizes}
    (hw : HonestFor prog input t ρ w s) {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let v ← (simulateQ keccakCallsOverRandomPermutation
        (Rom.honestComp (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
          (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
          (leanVmProver prog s ρ (stackOf prog s w)) fuel >>= fun proof ↦
            Budget.verifierRefusingZeroWithHash callKeccak256 callKeccakF1600 prog input
              proof)).run' []}[v = false] ≤
      childCompletenessError fuel + rpmError (completenessPermCalls fuel) := by
  refine rpm_le_of_rom _ _ ((duplexVm_romHonestComp prog input _ fuel).bind fun proof ↦
      duplexVm_verifierRZ prog input proof)
    (isWeightBound_proverRZ prog input (isTotalQueryBound_romHonestComp prog input _ fuel)
      (allQ_romHonestComp prog input _ fuel (shaped_of hw))) ?_
  have hV : Budget.verifierRefusingZeroWithHash callKeccak256 callKeccakF1600 prog input =
      verifierComp (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
        (Limits.refusingZeroProgram (bytecodeWords prog) (publicInputDigest input)) :=
    funext fun π ↦ verifierRZ_eq_comp prog input π
  rw [hV]
  exact romChild_at hw hfuel

/-! ## The numbers -/

/-- **At a fuel of `2^35` nonces per proof of work, at most `2^-100`**: the ideal failure at most
`2^14 · 2^-128`, the misses and the transfer below `2^-257` each, the collisions below
`2^-152`. -/
theorem rpmChild_le :
    childCompletenessError (2 ^ 35) + rpmError (completenessPermCalls (2 ^ 35)) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 100 := by
  have hc : leanVmCost = 54825 := by decide
  have hQ : EndToEnd.Complete.completenessQueries (2 ^ 35) = LeanVM.completenessQueries (2 ^ 35) := by
    rw [EndToEnd.Complete.completenessQueries, proverFactor, costHeight, hc, leanVmQueryBound_eq,
      LeanVM.completenessQueries]
    norm_num
  have hQle : LeanVM.completenessQueries (2 ^ 35) ≤ 2 ^ 52 := by
    norm_num [LeanVM.completenessQueries]
  -- the ideal failure
  have h1 : ((leanVmCost / 4 : ℕ) : ℝ≥0∞) * epsE ≤ (2 : ℝ≥0∞)⁻¹ ^ 102 := by
    rw [hc, epsE_eq]
    calc ((54825 / 4 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128
        ≤ (2 : ℝ≥0∞) ^ 14 * (2 : ℝ≥0∞)⁻¹ ^ (14 + 114) := by
          gcongr
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 114 := Common.two_pow_mul_inv_pow 14 114
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 102 := Common.inv_two_pow_le_of_le (by norm_num)
  -- the misses
  have h2 : (leanVmCost : ℝ≥0∞) * missProb 27 ^ (2 ^ 35) ≤ (2 : ℝ≥0∞)⁻¹ ^ 102 := by
    have hle : (leanVmCost : ℝ≥0∞) * missProb 27 ^ (2 ^ 35) ≤ LeanVM.completenessError (2 ^ 35) := by
      rw [completenessError_eq, EndToEnd.Complete.completenessError]
      gcongr
      rw [hQ, hc]
      norm_num [LeanVM.completenessQueries]
    exact hle.trans (completenessError_le.trans (Common.inv_two_pow_le_of_le (by norm_num)))
  -- the collisions
  have h3 : (EndToEnd.Complete.completenessQueries (2 ^ 35) : ℝ≥0∞) *
      ((EndToEnd.Complete.completenessQueries (2 ^ 35) : ℝ≥0∞) * 2⁻¹ ^ 256) ≤
        (2 : ℝ≥0∞)⁻¹ ^ 102 := by
    rw [hQ]
    calc (LeanVM.completenessQueries (2 ^ 35) : ℝ≥0∞) *
          ((LeanVM.completenessQueries (2 ^ 35) : ℝ≥0∞) * 2⁻¹ ^ 256)
        ≤ (2 : ℝ≥0∞) ^ 52 * ((2 : ℝ≥0∞) ^ 52 * (2 : ℝ≥0∞)⁻¹ ^ (52 + (52 + 152))) := by
          gcongr <;> exact_mod_cast hQle
      _ = (2 : ℝ≥0∞)⁻¹ ^ 152 := by
          rw [Common.two_pow_mul_inv_pow 52 (52 + 152), Common.two_pow_mul_inv_pow 52 152]
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 102 := Common.inv_two_pow_le_of_le (by norm_num)
  have h4 : rpmError (completenessPermCalls (2 ^ 35)) ≤ (2 : ℝ≥0∞)⁻¹ ^ 102 :=
    rpmError_completenessPermCalls_le.trans (Common.inv_two_pow_le_of_le (by norm_num))
  unfold childCompletenessError
  calc _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 102 + (2 : ℝ≥0∞)⁻¹ ^ 102 + (2 : ℝ≥0∞)⁻¹ ^ 102 +
        (2 : ℝ≥0∞)⁻¹ ^ 102 := add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = 4 * (2 : ℝ≥0∞)⁻¹ ^ 102 := by ring
    _ = (2 : ℝ≥0∞)⁻¹ ^ 100 := by
        rw [show (4 : ℝ≥0∞) = 2 ^ 2 by norm_num, show (102 : ℕ) = 2 + 100 from rfl]
        exact Common.two_pow_mul_inv_pow 2 100

end LeanVM.Guest.Child
