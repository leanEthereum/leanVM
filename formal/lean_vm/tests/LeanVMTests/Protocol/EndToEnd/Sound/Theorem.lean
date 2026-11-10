import LeanVM.Protocol.EndToEnd.Sound.Statements
import LeanVM.Protocol.WithHash

/-!
# The end-to-end knowledge soundness's tests

* **Statement locks** of the whole program's specification, the front phases' interface (built,
  with no hypothesis), the knowledge statement and the execution statement for an adversary that
  chooses the statement, the numeric bound, and the facts that make the statement a family (roots
  are prefix-free; the bytecode and the digest name the program and the public input). The
  stacked opening enters as the interface `O : OpeningIface`.
* **The trust audit**: the theorems depend on `propext`, `Classical.choice` and `Quot.sound` only.
* **What is load-bearing.** The error arithmetic: `8/|E|` is within `2^-125`, `9/|E|` is not.
-/

namespace LeanVMTests.Protocol.EndToEnd.Sound.Theorem

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Sound LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom
open LeanVM (publicInputDigest)
open OracleComp OracleSpec
open scoped ENNReal

/-! ## Statement locks -/

noncomputable example (O : OpeningIface) (prog : LeanIsaProgram) (input : PublicInput) :
    Spec (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) (fun _ ↦ False)
      (fun b _ ↦ b = false) ((2 : ℝ≥0∞)⁻¹ ^ 125) 0 0 :=
  leanVmSpec O (frontIface prog input) (bytecodeWords prog)

noncomputable example (prog : LeanIsaProgram) (input : PublicInput) :
    FrontIface computedBytecodeValue prog input (publicInputDigest input) :=
  frontIface prog input

example (O : OpeningIface) (A : OracleComp KeccakCalls (Statement × Proof)) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (verifierFam leanVmSeeds anyProgram)}[z.1.2 = true ∧
      ¬ Extracted O z.1.1.1.1 z.1.1.1.2 z.2 z.1.1.2] ≤
      ((QA + 13261 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 125 + failBound leanVmSeeds (QA + 13261)) :=
  leanVm_knowledge O A QA hA

example (O : OpeningIface) (A : OracleComp KeccakCalls (Statement × Proof)) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (verifierFam leanVmSeeds anyProgram)}[z.1.2 = true ∧
      ¬ ∃ (s : Sizes) (q : Column (leanIsaμ z.1.1.1.1 s)),
        extractStack O z.1.1.1.1 z.1.1.1.2 z.2 z.1.1.2 =
          some (⟨s, q⟩ : Σ s : Sizes, Column (leanIsaμ z.1.1.1.1 s)) ∧
        ∃ t, AssignmentRepresents (witnessOf z.1.1.1.1 s q) t ∧
          ValidExecution z.1.1.1.1 z.1.1.1.2 t] ≤
      ((QA + 13261 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 125 + failBound leanVmSeeds (QA + 13261)) :=
  leanVm_execution O A QA hA

example (QA : ℕ) (hQ : QA ≤ 2 ^ 64) :
    ((QA + 13261 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 125 + failBound leanVmSeeds (QA + 13261)) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 60 :=
  leanVm_bound_le hQ

/-- The verifier of a statement and a proof is the deployed verifier of that statement. -/
example (z : Statement × Proof) :
    verifierFam leanVmSeeds anyProgram z =
      verifierComp (leanVmSeed (bytecodeWords z.1.1) (publicInputDigest z.1.2))
        (leanVmVerifierProgram (bytecodeWords z.1.1) (publicInputDigest z.1.2)) z.2 :=
  verifierFam_leanVm z

example {x x' : Statement} {h : List Ev} (hx : stmtHistory x <+: h)
    (hx' : stmtHistory x' <+: h) : x = x' :=
  stmt_eq_of_prefix hx hx'

example : Function.Injective bytecodeWords := bytecodeWords_injective

example : Function.Injective publicInputDigest :=
  LeanVM.Protocol.EndToEnd.Complete.publicDigest_injective

/-! ## The trust audit -/

/--
info: 'LeanVM.Protocol.EndToEnd.Sound.frontIface' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms frontIface

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

/-- `8` over `|E|` is within `2^-125`. -/
example : ((8 : ℕ) : ℝ≥0∞) / Fintype.card E ≤ εmsg := le_εmsg rfl le_rfl

/-- `9` over `|E|` is not. -/
example : ¬ ((9 : ℕ) : ℝ≥0∞) / Fintype.card E ≤ εmsg := by
  rw [not_le]
  calc εmsg = ((8 : ℕ) : ℝ≥0∞) / Fintype.card E := by
        rw [LeanVM.Protocol.card_E, εmsg, securityBits, inv_pow_eq_div 125 128 (by norm_num)]
        norm_num
    _ < ((9 : ℕ) : ℝ≥0∞) / Fintype.card E :=
        ENNReal.div_lt_div_right (by simp) (by simp) (by norm_num)

end LeanVMTests.Protocol.EndToEnd.Sound.Theorem
