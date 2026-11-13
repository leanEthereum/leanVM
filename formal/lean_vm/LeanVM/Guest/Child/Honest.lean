/-
  LeanVM.Guest.Child.Honest

  The honest prover of a child: the compiled honest prover of a witness whose sizes are the
  execution's own, so that its stack is the execution's committed size. Its proof with the
  deployed Keccak, when the verifier accepts it, is the pure prover's proof of that witness.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.Rom
public import Statement.LeanVmGuest
public import LeanVM.Guest.Child.Fresh
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.WithHash
public import LeanVM.Guest.AcceptableChild

/-!
# The honest prover of a child

`childComp` is `EndToEnd.Complete.honestComp` with its witness chosen among those whose stacked
size is the execution's committed size (`ChildFor`; one exists within the verifier's cap,
`exists_childFor`, as `exists_admissible_witness` builds it). `Rom.honestComp?` is
`Rom.honestComp` with `none` where it makes no proof; a prover that is it at a child's witness or
makes no proof (`ChildSpec`, as `childProver`) has, with Keccak-256 and Keccak-f[1600]
(`honestProofWithDeployedKeccakWithHash`), the pure prover's proof (`atKeccak_of_eq`,
`prove_of_some`).
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol.KeccakHash OracleComp OracleSpec
open Air.Flat (EnsembleWitness)

@[expose] public section

/-- The witness of a child's proof: an honest witness of the execution whose stacked size is the
execution's committed size. -/
def ChildFor (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ : ℕ)
    (w : EnsembleWitness (leanIsaEnsemble prog t.logMemorySize)) (s : Sizes) : Prop :=
  HonestFor prog input t ρ w s ∧ (LeanIsa.blocks prog s).total = t.committedSize

/-- **A child's witness exists** for a valid execution within the verifier's cap, at a valid
rate: `exists_admissible_witness`'s witness. -/
theorem exists_childFor {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog} {ρ : ℕ}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ maxMu)
    (hρ : validRate ρ) : ∃ w s, ChildFor prog input t ρ w s := by
  have hcount : ∀ op, t.opcodeCount op = t.runRows op := Execution.count_eq_runRows hv.2
  have hheight : ∀ op, 2 ^ Nat.clog 2 (t.opcodeCount op) ≤ t.committedSize := by
    intro op
    have : 0 < 2 ^ prog.logSize := Nat.two_pow_pos _
    have hk : 2 ^ Nat.clog 2 (t.opcodeCount .keccak) ≤ 2 ^ max (Nat.clog 2 (t.opcodeCount
        .keccak)) 9 :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    simp only [Execution.committedSize]
    cases op <;> omega
  have hcap : (2 : ℕ) ^ maxMu ≤ 2 ^ maxLogRows := Nat.pow_le_pow_right (by norm_num) (by decide)
  have hrows : ∀ op, t.runRows op ≤ 2 ^ maxLogRows := fun op ↦ by
    rw [← hcount]
    exact (Nat.le_pow_clog (by norm_num) _).trans (((hheight op).trans hbudget).trans hcap)
  obtain ⟨w, hw, hrep, hlen⟩ := constraintCompleteness_rows hv hrows
  obtain ⟨s, hs⟩ := sizes_of_satisfiedBy hw
  have hs0 := hs
  obtain ⟨hpos, rfl⟩ := eq_of_ofWitness hs
  have hmem : (witnessSizes w hpos).logMem = t.logMemorySize := hrep.κ_eq
  have hr : ∀ j : Fin 6, (witnessSizes w hpos).rows j = t.opcodeCount (tableOpcode j) :=
    fun j ↦ (hlen j).trans (hcount _).symm
  have htotal : (LeanIsa.blocks prog (witnessSizes w hpos)).total = t.committedSize := by
    have e : tableOpcode 0 = .xor ∧ tableOpcode 1 = .mulNative ∧ tableOpcode 2 = .setConstant ∧
        tableOpcode 3 = .deref ∧ tableOpcode 4 = .jump ∧ tableOpcode 5 = .keccak := by decide
    rw [blocks_total_eq, hmem, pow_add 2 _ 6]
    simp only [Sizes.τ, hr, e, Execution.committedSize]
    have f0 : tableLogFloors.getD ((0 : Fin 6) : ℕ) 0 = 0 := rfl
    have f1 : tableLogFloors.getD ((1 : Fin 6) : ℕ) 0 = 0 := rfl
    have f2 : tableLogFloors.getD ((2 : Fin 6) : ℕ) 0 = 0 := rfl
    have f3 : tableLogFloors.getD ((3 : Fin 6) : ℕ) 0 = 0 := rfl
    have f4 : tableLogFloors.getD ((4 : Fin 6) : ℕ) 0 = 0 := rfl
    have f5 : tableLogFloors.getD ((5 : Fin 6) : ℕ) 0 = 9 := rfl
    simp only [f0, f1, f2, f3, f4, f5, Nat.max_zero]
    ring
  refine ⟨w, _, ⟨hρ, hw, hs0, ⟨?_, ?_, fun j ↦ (hr j).trans_le (by rw [hcount]; exact hrows _),
    leanIsaμ_le_of_total_le (htotal ▸ hbudget)⟩, hrep⟩, htotal⟩
  · rw [hmem]
    exact hv.1.1
  · rw [hmem]
    exact hv.1.2.1

open Classical in
/-- **The honest prover of a child**: `honestComp` at a child's witness (`ChildFor`, chosen
classically); the empty proof when there is none. -/
noncomputable def childComp (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog)
    (ρ fuel : ℕ) : OracleComp KeccakCalls Proof :=
  if h : ∃ w s, ChildFor prog input t ρ w s then
    Rom.honestComp (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
      (leanVmProver prog h.choose_spec.choose ρ (stackOf prog h.choose_spec.choose h.choose)) fuel
  else pure ⟨[], []⟩

open Classical in
/-- The honest prover of a child, as an `HonestProverWithHash`: `Rom.honestComp?` at a child's
witness (`ChildFor`, chosen classically); `none` when there is none. -/
noncomputable def childProver : HonestProverWithHash := fun prog input t ρ fuel ↦
  if h : ∃ w s, ChildFor prog input t ρ w s then
    Rom.honestComp? (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
      (leanVmProver prog h.choose_spec.choose ρ (stackOf prog h.choose_spec.choose h.choose)) fuel
  else pure none

/-- `deployedKeccakCalls` is the total implementation at Keccak-256 and Keccak-f[1600]. -/
theorem keccakImpl_eq : Budget.deployedKeccakCalls = totalImpl keccak256 keccakF1600 := by
  funext q
  rcases q with x | s <;> rfl

/-- The specification's honest prover of a child at a witness: `Rom.honestComp?` at leanVM's
seed, program and the witness's strategy, or no proof. -/
abbrev ChildSpec (A : HonestProverWithHash) (prog : LeanIsaProgram) (input : PublicInput)
    (t : Execution prog) (ρ fuel : ℕ) : Prop :=
  A prog input t ρ fuel = pure none ∨ ∃ w s, ChildFor prog input t ρ w s ∧
    A prog input t ρ fuel = Rom.honestComp? (leanVmSeed (bytecodeWords prog) (publicInputDigest
        input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
      (leanVmProver prog s ρ (stackOf prog s w)) fuel

/-- **The child prover is the specification at a child's witness**, or no proof. -/
theorem childSpec_childProver (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog)
    (ρ fuel : ℕ) : ChildSpec childProver prog input t ρ fuel := by
  by_cases h : ∃ w s, ChildFor prog input t ρ w s
  · refine Or.inr ⟨_, _, h.choose_spec.choose_spec, ?_⟩
    unfold childProver
    simp only [h, ↓reduceDIte]
  · refine Or.inl ?_
    unfold childProver
    simp only [h, ↓reduceDIte]

/-- **A prover's proof with Keccak**, where it is the specification's honest prover of a
strategy: the pure prover's proof. -/
theorem atKeccak_of_eq {A : HonestProverWithHash} {prog : LeanIsaProgram} {input : PublicInput}
    {t : Execution prog} {ρ fuel : ℕ} {S : Strategy}
    (hA : A prog input t ρ fuel = Rom.honestComp? (leanVmSeed (bytecodeWords prog)
      (publicInputDigest input)) (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest
          input)) S fuel) :
    Budget.honestProofWithDeployedKeccakWithHash A prog input t ρ fuel =
      prove keccak256 keccakF1600 (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest
          input)) S
        (seed (bytecodeWords prog) (publicInputDigest input)) fuel := by
  unfold Budget.honestProofWithDeployedKeccakWithHash
  rw [hA]
  simp only [keccakImpl_eq, Rom.honestComp?, simulateQ_bind,
    simulateQ_proveM, implH_totalImpl, implF_totalImpl, seedRun_leanVmSeed]
  rw [← proveM_id]
  rfl

/-- The statement's refusing verifier, at Keccak, is the run of `execWith` refusing zero
challenges. -/
theorem verifierRZ_eq (prog : LeanIsaProgram) (input : PublicInput) (π : Proof) :
    Budget.verifierRefusingZeroWithHash (m := Id) keccak256 keccakF1600 prog input π =
      Id.run (runProofWithHash (m := Id) keccak256 keccakF1600
        ((execWith computedBytecodeValue verifyStackedOpening (bytecodeWords prog)
          (publicInputDigest input)).bind fun _ ↦
            VerifierProgram.ret true).refusingZeroChallenge
        (seed (bytecodeWords prog) (publicInputDigest input)) π) := by
  unfold Budget.verifierRefusingZeroWithHash
  rfl

/-- **A proof with Keccak**, of a prover that is the specification at a child's witness or makes
no proof, is the pure prover's proof of a child's witness. -/
theorem prove_of_some {A : HonestProverWithHash} {prog : LeanIsaProgram} {input : PublicInput}
    {t : Execution prog} {ρ fuel : ℕ} (hA : ChildSpec A prog input t ρ fuel) {proof : Proof}
    (hsome : Budget.honestProofWithDeployedKeccakWithHash A prog input t ρ fuel = some proof) :
    ∃ w s, ChildFor prog input t ρ w s ∧
      prove keccak256 keccakF1600 (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest
          input))
        (leanVmProver prog s ρ (stackOf prog s w)) (seed (bytecodeWords prog) (publicInputDigest
            input))
        fuel = some proof := by
  rcases hA with hA | ⟨w, s, hc, hA⟩
  · unfold Budget.honestProofWithDeployedKeccakWithHash at hsome
    rw [hA, simulateQ_pure] at hsome
    cases hsome
  · exact ⟨w, s, hc, (atKeccak_of_eq hA).symm.trans hsome⟩

end
end LeanVM.Guest.Child
