import LeanVM.Protocol.LeanVM

/-!
# The leanVM front page, locked: completeness

Statement locks of `LeanVM/Protocol/LeanVM.lean`: completeness in the two-oracle random-oracle
model (a step of the proof of `LeanVM.Completeness`, locked in `LeanVMTests.Protocol.LeanVMRpm`)
and its numbers, with the axioms each depends on. Knowledge soundness is locked in
`LeanVMTests.Protocol.LeanVMSound`.
-/

open LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol.LeanIsa LeanVM

example {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ 30) {ρ : ℕ}
    (hρ : 1 ≤ ρ ∧ ρ ≤ 4) {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let z ← experiment (honestProver prog input t ρ fuel)}[z.1.2 = false] ≤
      completenessError fuel :=
  completenessRom hv hbudget hρ hfuel

example : completenessError (2 ^ 35) ≤ (2 : ENNReal)⁻¹ ^ 257 := completenessError_le

/-- The queries `completenessError` counts, `Q_f = 13710 + 54825 (2^29 + 2f + 2)` of
`statement.tex`. -/
example (fuel : ℕ) : completenessQueries fuel = 13710 + 54825 * (2 ^ 29 + 2 * fuel + 2) := by
  have hc : Protocol.Verifier.leanVmCost = 54825 := by decide
  rw [completenessQueries, hc, Protocol.Verifier.leanVmQueryBound_eq]
  ring

/-- They are what the honest prover's and the verifier's query bounds add to: the prover's factor
at the commitment height is `2^29 + 2f + 2`. -/
example (fuel : ℕ) :
    completenessQueries fuel = 1 + 1 + Protocol.Verifier.leanVmCost *
      Protocol.Compile.proverFactor Protocol.Verifier.costHeight fuel +
      Protocol.Verifier.leanVmQueryBound :=
  rfl

/-- info: 'LeanVM.completenessRom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms completenessRom

/--
info: 'LeanVM.completenessError_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms completenessError_le

/-! ## The statement of `LeanVM/Protocol/Rom/Statement.lean` -/

example : CompletenessRom := completenessRom_holds

/--
info: 'LeanVM.completenessRom_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms completenessRom_holds
