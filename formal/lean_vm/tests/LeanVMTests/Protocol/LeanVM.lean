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
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ 28) {ρ : ℕ}
    (hρ : 1 ≤ ρ ∧ ρ ≤ 4) {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let z ← experiment (honestProver prog input t ρ fuel)}[z.1.2 = false] ≤
      completenessError fuel :=
  completenessRom hv hbudget hρ hfuel

example : completenessError (2 ^ 25) ≤ (2 : ENNReal)⁻¹ ^ 257 := completenessError_le

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
