import LeanVM.Semantics.Executable
import LeanVMTests.Semantics.Execution

/-!
# Executable carrier regressions

Compiled evaluations and kernel checks exercise the actual address search (hinted and
exhaustive), the checked step, and the exact and fuel-bounded checkers. The unstable-read vector is the four-slot Rust execution at
`48a904208d682848dac0e18ef8b01ebfc40df9ad`: XOR reads an unset cell as zero, then SET changes
that cell to one. The returned image violates the first XOR. Its repaired image is an
independent positive control, not a claim that the Rust runner produces that image.
-/

namespace LeanVMTests.Semantics.Executable

open LeanVM.Parameters LeanVM.Semantics
open LeanVMTests.Semantics.Execution

/-- The public boundary of the unstable-read probe. -/
def zeroInput : PublicInput := ⟨![0, 0, 0, 0]⟩

/-- The exact four-slot program of the Rust stale-read counterexample. -/
def staleProgram : Program :=
  ⟨2, by decide, ![.xor (gpow 2) 1 (gpow 3), .setConstant (gpow 2) (E.ofLimbs 1 0 0),
    .setConstant (gpow 4) 0, .setConstant 1 (E.ofLimbs 1 0 0)]⟩

/-- The final image returned by Rust: the XOR output is zero despite its final input being
one. Replacing that output by one gives a valid reference execution. -/
def staleImage (output : E) : MemImage minLogMem := fun i ↦
  if i.val = 2 then E.ofLimbs 1 0 0 else if i.val = 3 then output else 0

/-- The final image violates the first instruction under the reference semantics. -/
theorem stale_step_invalid : step staleProgram (staleImage 0) Regs.initial = none := by
  rw [step_of_fetch_eq_some (r := Regs.initial) (fetch_one staleProgram)]
  change execute (staleImage 0) Regs.initial (.xor (gpow 2) 1 (gpow 3)) = none
  simp only [execute, executeWith, Regs.initial, one_mul, read_lit (staleImage 0) 2,
    read_one (staleImage 0), read_lit (staleImage 0) 3,
    Option.bind_eq_bind, Option.bind_some]
  decide +kernel

/-- The returned Rust image is rejected without trusting the runner's diagnostics. -/
theorem stale_trace_rejected :
    checkTrace staleProgram zeroInput ⟨minLogMem, staleImage 0, 3⟩ = false := by
  apply Bool.eq_false_iff.mpr
  intro hc
  have hv := (checkTrace_eq_true_iff _ _ _ _).mp hc
  have hr : run staleProgram (staleImage 0) 3 Regs.initial = none := by
    rw [run_succ_of_ne (prog := staleProgram) (r := Regs.initial) (by decide +kernel),
      stale_step_invalid]
    rfl
  have hh := hv.2
  rw [hr] at hh
  cases hh

#guard !checkTrace staleProgram zeroInput ⟨minLogMem, staleImage 0, 3⟩
#guard checkTrace staleProgram zeroInput
  ⟨minLogMem, staleImage (E.ofLimbs 1 0 0), 3⟩

#guard checkWithinFuel staleProgram zeroInput (staleImage 0) 3 = .error .invalidStep
#guard checkWithinFuel staleProgram zeroInput (staleImage (E.ofLimbs 1 0 0)) 2 =
  .error .fuelExhausted
#guard checkWithinFuel staleProgram zeroInput (staleImage (E.ofLimbs 1 0 0)) 3 = .ok 3
#guard checkWithinFuel staleProgram zeroInput (staleImage (E.ofLimbs 1 0 0)) 20 = .ok 3
#guard !checkTrace staleProgram zeroInput ⟨minLogMem, staleImage (E.ofLimbs 1 0 0), 20⟩

/-! ## Address bounds and exact public boundary -/

#guard addressIndex 4 [] 0 = none
#guard addressIndex 4 [] (gpow 15) = some ⟨15, by decide⟩
#guard addressIndex 4 [] (gpow 16) = none
#guard fetchInstruction staleProgram [] (gpow 4) = none
#guard checkWithinFuel oneProg zeroInput (fun _ : Fin (2 ^ minLogMem) ↦ (0 : E)) 0 = .ok 0
#guard checkTrace oneJumpProg mulInput ⟨minLogMem, mulImage, 0⟩
#guard checkWithinFuel oneJumpProg mulInput mulImage 0 = .ok 0
#guard checkWithinFuel oneProg zeroInput (fun _ : Fin (2 ^ 4) ↦ (0 : E)) 0 =
  .error .publicBoundary
#guard checkWithinFuel oneProg (⟨![1, 0, 0, 0]⟩ : PublicInput)
  (fun _ : Fin (2 ^ minLogMem) ↦ (0 : E)) 0 = .error .publicBoundary

/-! ## All six opcodes, control-flow and alias boundaries -/

#guard runToHalt mulProg mulImage [] 3 Regs.initial = .ok 3
#guard stepChecked (oneStep (.xor 1 1 1)) ctlImage [] Regs.initial = some ⟨g, 1⟩
#guard stepChecked (oneStep (.xor (gpow 2) (gpow 2) (gpow 2))) ctlImage [] Regs.initial = none
#guard stepChecked (oneStep (.xor 0 1 1)) ctlImage [] Regs.initial = none
#guard stepChecked (oneStep (.xor (gpow 16) 1 1)) ctlImage [] Regs.initial = none
#guard stepChecked (oneStep (.mulNative (gpow 2) (gpow 3) (gpow 4))) ctlImage
  [] Regs.initial = none
#guard stepChecked (oneStep (.setConstant (gpow 2) 0)) ctlImage [] Regs.initial = none
#guard stepChecked (oneStep (.jump (gpow 2) (gpow 3) (gpow 4))) ctlImage [] Regs.initial =
  some ⟨gpow 3, gpow 5⟩
#guard stepChecked (oneStep (.jump (gpow 12) (gpow 3) (gpow 4))) ctlImage [] Regs.initial =
  some ⟨g, 1⟩
#guard stepChecked (oneStep (.jump (gpow 12) (gpow 13) (gpow 4))) ctlImage [] Regs.initial = none
#guard stepChecked (oneStep (.jump (gpow 2) (gpow 13) (gpow 4))) ctlImage [] Regs.initial = none
#guard runToHalt haltProg ctlImage [] 1 Regs.initial = .error .finalFrame
#guard stepChecked (oneStep (.deref (gpow 5) 1 (gpow 6) .pc)) ctlImage [] Regs.initial =
  some ⟨g, 1⟩
#guard stepChecked (oneStep (.deref (gpow 5) 1 (gpow 6) .cell)) derefCellImage
  [] Regs.initial = some ⟨g, 1⟩
#guard stepChecked (oneStep (.deref (gpow 5) 1 (gpow 6) .fp)) derefFpImage
  [] Regs.initial = some ⟨g, 1⟩
#guard stepChecked (oneStep (.deref (gpow 5) 1 (gpow 6) .cell)) ctlImage
  [] Regs.initial = none
#guard stepChecked (oneStep (.deref (gpow 5) 1 (gpow 6) .fp)) ctlImage
  [] Regs.initial = none
#guard stepChecked (oneStep (.deref (gpow 5) 1 (gpow 6) .cell)) nonKPointerImage
  [] Regs.initial = none
#guard stepChecked (oneStep (.deref (gpow 5) 1 (gpow 16) .pc)) ctlImage [] Regs.initial = none
#guard stepChecked (oneStep blakeIns) (blakeImage rustOut1) [] Regs.initial = some ⟨g, 1⟩
#guard stepChecked (oneStep blakeIns)
  (blakeImage (E.ofLimbs (K.ofBits 0xf1b0679a15df60bb) (K.ofBits 0x0228c8d4ed9b3a24) 1)) [] Regs.initial = none

/-! ## Address hints: verified on a hit, exhaustive on a miss -/

#guard addressIndex 4 (hintIndices 4 [0, 0, 3, 16, 1000]) (gpow 3) = some ⟨3, by decide⟩
#guard addressIndex 4 (hintIndices 4 [0, 3]) (gpow 2) = some ⟨2, by decide⟩
#guard addressIndex 4 (hintIndices 4 [16, 1000]) (gpow 15) = some ⟨15, by decide⟩
#guard addressIndex 4 (hintIndices 4 [0, 1]) (gpow 16) = none
#guard readImage (staleImage 0) [99999, 2] (gpow 2) = some (E.ofLimbs 1 0 0)
#guard checkTrace staleProgram zeroInput ⟨minLogMem, staleImage (E.ofLimbs 1 0 0), 3⟩ [1000, 3, 3]
#guard !checkTrace staleProgram zeroInput ⟨minLogMem, staleImage 0, 3⟩ [2, 3]

/-- Useless and duplicate hints cannot change acceptance: both sides are the reference. -/
example : checkTrace staleProgram zeroInput ⟨minLogMem, staleImage 0, 3⟩ [1000, 1, 1] =
    checkTrace staleProgram zeroInput ⟨minLogMem, staleImage 0, 3⟩ :=
  Bool.eq_iff_iff.mpr
    ((checkTrace_eq_true_iff _ _ _ _).trans (checkTrace_eq_true_iff _ _ _ _).symm)

/-- A loop whose condition and target both name the initial program counter. -/
def loopProgram : Program := oneStep (.jump 1 1 1)

#guard runToHalt loopProgram (fun _ : Fin (2 ^ 1) ↦ E.ofLimbs 1 0 0) [] 5 Regs.initial =
  .error .fuelExhausted

end LeanVMTests.Semantics.Executable
