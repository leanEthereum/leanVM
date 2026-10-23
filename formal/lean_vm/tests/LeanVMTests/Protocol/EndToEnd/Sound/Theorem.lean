import LeanVM.Protocol.EndToEnd.Sound.Statements

/-!
# The end-to-end knowledge soundness's tests

* **Statement locks** of the knowledge statement and the execution statement for an adversary
  that chooses the statement, the numeric bound, the facts that make the statement a family
  (roots are prefix-free; the bytecode and the digest name the program and the public input),
  and the whole program's specification.
* **The trust audit**: the theorems depend on `propext`, `Classical.choice` and `Quot.sound` only.
* **What is load-bearing.**
  - The stack's shape is "the stack's commitment is the only one": a second commitment breaks it.
  - The error arithmetic: `2^64/|E|` is within `2^-128`, `2^65/|E|` is not.
-/

namespace LeanVMTests.Protocol.EndToEnd.Sound.Theorem

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Sound LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Rom
open LeanVM.Protocol.EndToEnd.Complete (publicDigest)
open OracleComp OracleSpec
open scoped ENNReal

/-! ## Statement locks -/

noncomputable example (prog : Program) (input : PublicInput) :
    Spec (leanVmProgram (bytecodeWords prog) (publicDigest input)) (fun _ ↦ False)
      (fun b _ ↦ b = false) ((2 : ℝ≥0∞)⁻¹ ^ 128) 0 0 :=
  leanVmSpec prog input

example (A : OracleComp HashSpec (Statement × Proof)) (QA : ℕ) (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (verifierFam leanVmSeeds anyProgram)}[z.1.2 = true ∧
      ¬ Extracted z.1.1.1.1 z.1.1.1.2 z.2 z.1.1.2] ≤
      ((QA + 13213 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128 + failBound leanVmSeeds (QA + 13213)) :=
  leanVm_knowledge A QA hA

example (A : OracleComp HashSpec (Statement × Proof)) (QA : ℕ) (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (verifierFam leanVmSeeds anyProgram)}[z.1.2 = true ∧
      SentinelSafe z.1.1.1.1 ∧
      ¬ ∃ (s : Sizes) (q : Column (leanIsaμ z.1.1.1.1 s)),
        extractStack z.1.1.1.1 z.1.1.1.2 z.2 z.1.1.2 =
          some (⟨s, q⟩ : Σ s : Sizes, Column (leanIsaμ z.1.1.1.1 s)) ∧
        ∃ t, AssignmentRepresents (witnessOf Blake2sFlock.blake2sFlockSpec z.1.1.1.1 s q) t ∧
          ValidExecution z.1.1.1.1 z.1.1.1.2 t] ≤
      ((QA + 13213 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128 + failBound leanVmSeeds (QA + 13213)) :=
  leanVm_execution A QA hA

example (QA : ℕ) (hQ : QA ≤ 2 ^ 64) :
    ((QA + 13213 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128 + failBound leanVmSeeds (QA + 13213)) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 63 :=
  leanVm_bound_le hQ

/-- The verifier of a statement and a proof is the deployed verifier of that statement. -/
example (z : Statement × Proof) :
    verifierFam leanVmSeeds anyProgram z =
      verifierComp (leanVmSeed (bytecodeWords z.1.1) (publicDigest z.1.2))
        (leanVmProgram (bytecodeWords z.1.1) (publicDigest z.1.2)) z.2 :=
  verifierFam_leanVm z

example {x x' : Statement} {h : List Ev} (hx : stmtHistory x <+: h)
    (hx' : stmtHistory x' <+: h) : x = x' :=
  stmt_eq_of_prefix hx hx'

example : Function.Injective bytecodeWords := bytecodeWords_injective

example : Function.Injective publicDigest :=
  LeanVM.Protocol.EndToEnd.Complete.publicDigest_injective

/-! ## The trust audit -/

/--
info: 'LeanVM.Protocol.EndToEnd.Sound.leanVm_knowledge' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms leanVm_knowledge

/--
info: 'LeanVM.Protocol.EndToEnd.Sound.leanVm_execution' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms leanVm_execution

/--
info: 'LeanVM.Protocol.EndToEnd.Sound.leanVm_bound_le' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms leanVm_bound_le

/-! ## What is load-bearing -/

/-- A second commitment breaks the stack's shape. -/
example (μ R ht w : ℕ) (W W' : Word) :
    ¬ StackShape μ R [Ev.commit ht w W, Ev.commit ht w W'] := by
  rintro ⟨hlen, -⟩
  simp [commits] at hlen

/-- `2^64` over `|E|` is within `2^-128`. -/
example : ((2 ^ 64 : ℕ) : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞) ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 :=
  le_eps_of_nat le_rfl le_rfl

/-- `2^65` over `|E|` is not. -/
example : ¬ ((2 ^ 65 : ℕ) : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞) ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 := by
  rw [inv_pow_eq_div 128 192 (by norm_num), ENNReal.div_le_iff (by simp) (by simp),
    ENNReal.div_mul_cancel (by simp) (by simp), Nat.cast_le]
  norm_num

end LeanVMTests.Protocol.EndToEnd.Sound.Theorem
