import LeanVM.Protocol.Verifier.DeferredShape

/-!
# Tests: the deferring verifier, its claims true

* `verify_of_verifyDeferred` and `verifyDeferred_shaped` rest on Lean's three standard axioms.
* **The condition doing the work.** A false claim on the bytecode does not refine the computed
  value: with the empty bytecode, whose multilinear extension is `0`, a claim of `1` at the empty
  point is accepted where the computed value is `0`, so `Evaluations.Le` fails and the deferring
  verifier's acceptance says nothing of the deployed one's.
* A true claim, the bytecode `[1]`'s value `1` at the empty point, refines.
-/

namespace LeanVMTests.Protocol.Verifier.Deferred

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-- info: 'LeanVM.Protocol.Verifier.verify_of_verifyDeferred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Verifier.verify_of_verifyDeferred

/-- info: 'LeanVM.Protocol.Verifier.verifyDeferred_shaped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Verifier.verifyDeferred_shaped

theorem le_ret {a b : E} (h : VerifierProgram.Le (VerifierProgram.ret a) (VerifierProgram.ret b)) :
    a = b := by
  cases h; rfl

/-- A claim of `value` on the bytecode at the empty point. -/
def claimAt (value : E) : BytecodeClaim := ⟨[], value⟩

/-- A false claim does not refine: the empty bytecode's value is `0`, the claim `1`. -/
example : ¬ Evaluations.Le [] (claimedBytecodeValue (claimAt 1)) computedBytecodeValue := by
  intro h
  have h0 := h []
  simp only [claimedBytecodeValue, computedBytecodeValue, VerifierProgram.require, claimAt,
      ↓reduceIte] at h0
  have := le_ret h0
  simp [multilinearEval] at this

/-- A true claim on the bytecode: `[1]`'s value at the empty point is `1`. -/
example : multilinearEval ([1].map ofK) (claimAt 1).bytecodePoint = (claimAt 1).bytecodeValue := by
  simp [multilinearEval, claimAt, ofK]

end LeanVMTests.Protocol.Verifier.Deferred
