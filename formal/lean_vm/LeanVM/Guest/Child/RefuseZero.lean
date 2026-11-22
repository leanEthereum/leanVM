/-
  LeanVM.Guest.Child.RefuseZero

  The statement's zero-challenge refusal (`VerifierProgram.refusingZeroChallenge`, a zero refused at
  every sampled challenge): it accepts less than the verifier, and it commutes with sequencing.
-/

module

public import LeanVM.Guest.Child.Fresh
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.WithHashBridge
public import LeanVM.Guest.WithHash
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Guest.Child.Refusing

/-!
# Refusing a zero challenge anywhere

`P.refusingZeroChallenge` is `P` with every sampled challenge `0` a failure (`Statement/LeanVmGuestCompleteness.lean`).

* It only fails more (`refines_refusingZeroChallenge`), so a proof the deferring verifier refusing a zero
  challenge accepts is accepted by the deferring verifier (`Limits.verifyDeferred_of_rz`).
* It commutes with sequencing (`refuseZero_bind`), so a run of the computed verifier refusing zero
  challenges is a run with a true claim (`run_claimed_of_computed_rz`).
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Node

@[expose] public section

variable {α β : Type}

theorem bind_ite_fail (c : Prop) [Decidable c] (P : VerifierProgram α) (f : α → VerifierProgram β) :
    (if c then (VerifierProgram.fail : VerifierProgram α) else P).bind f = if c then VerifierProgram.fail else P.bind f := by
  split <;> rfl

/-- **Refusing zero challenges commutes with sequencing.** -/
theorem refuseZero_bind : ∀ (P : VerifierProgram α) (f : α → VerifierProgram β),
    (P.bind f).refusingZeroChallenge = P.refusingZeroChallenge.bind fun a ↦ (f a).refusingZeroChallenge
  | .ret _, _ => rfl
  | .fail, _ => rfl
  | .read k, f => by
    show VerifierProgram.read (fun x ↦ ((k x).bind f).refusingZeroChallenge) =
      VerifierProgram.read fun x ↦ (k x).refusingZeroChallenge.bind fun a ↦ (f
          a).refusingZeroChallenge
    exact congrArg _ (funext fun x ↦ refuseZero_bind (k x) f)
  | .sample k, f => by
    show VerifierProgram.sample (fun x ↦ if x = 0
        then VerifierProgram.fail else ((k x).bind f).refusingZeroChallenge) =
      VerifierProgram.sample fun x ↦ (if x = 0
          then VerifierProgram.fail else (k x).refusingZeroChallenge).bind
        fun a ↦ (f a).refusingZeroChallenge
    refine congrArg _ (funext fun x ↦ ?_)
    rw [bind_ite_fail, refuseZero_bind (k x) f]
  | .grind _ k, f => by
    show VerifierProgram.grind _ ((k.bind f).refusingZeroChallenge) = VerifierProgram.grind _ (k.refusingZeroChallenge.bind _)
    rw [refuseZero_bind k f]
  | .commit _ _ k, f => by
    show VerifierProgram.commit _ _ ((k.bind f).refusingZeroChallenge) = VerifierProgram.commit _ _ (k.refusingZeroChallenge.bind _)
    rw [refuseZero_bind k f]
  | .query _ _ k, f => by
    show VerifierProgram.query _ _ (fun r ↦ ((k r).bind f).refusingZeroChallenge) =
      VerifierProgram.query _ _ fun r ↦ (k r).refusingZeroChallenge.bind fun a ↦ (f
          a).refusingZeroChallenge
    exact congrArg _ (funext fun r ↦ refuseZero_bind (k r) f)

/-! ## The deferring verifier -/

/-- **The deferring verifier refusing a zero challenge accepts only what the deferring verifier
accepts.** -/
theorem _root_.LeanVM.Guest.Limits.verifyDeferred_of_rz {bytecode : List K} {iv publicInput : Digest}
    {c : BytecodeClaim} {π : Proof}
    (h : Id.run (runProofWithHash (m := Id) keccak256 keccakF1600
      (deferringVerifierProgram c bytecode publicInput).refusingZeroChallenge
      (keccakF1600 (seedInput iv publicInput)) π) = true) :
    verifyDeferred bytecode iv publicInput c π = true := by
  rw [verifyDeferred_eq_withHash]
  unfold verifyDeferredWithHash
  exact runProof_refines (Limits.refines_refusingZeroChallenge _) _ π h

/-! ## The claim a run evaluates -/

/-- **An accepted run with the computed value, refusing zero challenges, is the run with a true
claim**, refusing zero challenges: the claim of the value at the point the run evaluates. -/
theorem run_claimed_of_computed_rz (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState)
    (opening : ℕ → ℕ → List StackClaim → VerifierProgram Unit) (bytecode : List K)
    (publicInput : Digest)
    (k : Unit → VerifierProgram Bool) {st : VerifierProgramState} {r : Bool × VerifierProgramState}
    (h : Compile.runWithHash H F ((execWith computedBytecodeValue opening bytecode
      publicInput).bind k).refusingZeroChallenge st = some r) :
    ∃ c : BytecodeClaim, c.Holds bytecode ∧
      Compile.runWithHash H F ((execWith (claimedBytecodeValue c) opening bytecode
        publicInput).bind k).refusingZeroChallenge st = some r := by
  rw [execSplit, VerifierProgram.bind_assoc, refuseZero_bind, run_bind'] at h
  rcases hp : Compile.runWithHash H F (prefixProg bytecode).refusingZeroChallenge st with
    _ | ⟨y, s1⟩
  · rw [hp] at h; simp at h
  rw [hp] at h
  have hy : y.layout.bytecode = bytecode :=
    prefix_bytecode (VerifierProgram.returns_of_run H F
      (run_refines (H := H) (F := F) (Limits.refines_refusingZeroChallenge _) st (y, s1) hp))
  simp only [Option.bind_some] at h
  rw [hy] at h
  by_cases hv : multilinearEval (bytecode.map ofK) y.bytecodePoint = y.value
  · refine ⟨⟨y.bytecodePoint, y.value⟩, hv, ?_⟩
    rw [execSplit, VerifierProgram.bind_assoc, refuseZero_bind, run_bind', hp]
    simp only [Option.bind_some]
    rw [← h, hy]
    simp only [claimedBytecodeValue, computedBytecodeValue, VerifierProgram.require, hv,
      and_self, ↓reduceIte]
  · exfalso
    simp only [computedBytecodeValue, VerifierProgram.require, hv, ↓reduceIte,
      VerifierProgram.bind, VerifierProgram.refusingZeroChallenge] at h
    simp [Compile.runWithHash] at h

/-- **An accepted proof with the computed value, refusing zero challenges, is accepted with a true
claim**, refusing zero challenges. -/
theorem runProof_claimed_of_computed_rz (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState)
    (opening : ℕ → ℕ → List StackClaim → VerifierProgram Unit) (bytecode : List K)
    (publicInput : Digest) {sd : KeccakState} {π : Proof}
    (h : Id.run (runProofWithHash H F ((execWith computedBytecodeValue opening bytecode
        publicInput).bind fun _ ↦ VerifierProgram.ret true).refusingZeroChallenge sd π) = true) :
    ∃ c : BytecodeClaim, c.Holds bytecode ∧
      Id.run (runProofWithHash H F ((execWith (claimedBytecodeValue c) opening bytecode
          publicInput).bind fun _ ↦ VerifierProgram.ret true).refusingZeroChallenge sd π) =
        true := by
  unfold runProofWithHash at h ⊢
  revert h
  match hr : Compile.runWithHash H F ((execWith computedBytecodeValue opening bytecode
      publicInput).bind fun _ ↦ VerifierProgram.ret true).refusingZeroChallenge
        ⟨⟨sd, [], none⟩, π.stream, π.openings, []⟩ with
  | some (true, s) =>
    intro h
    obtain ⟨c, hc, e⟩ := run_claimed_of_computed_rz H F opening bytecode publicInput _ hr
    refine ⟨c, hc, ?_⟩
    rw [e]
    exact h
  | some (false, _) => intro h; cases h
  | none => intro h; cases h

end
end LeanVM.Guest.Child
