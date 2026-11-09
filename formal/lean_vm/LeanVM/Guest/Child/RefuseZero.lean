/-
  LeanVM.Guest.Child.RefuseZero

  The statement's zero-challenge refusal (`VerifierProgram.refusingZeroChallenge`, a zero refused at every sampled
  challenge) against the guest's (`Limits.verifyDeferredNZ`, `Budget.verifierNZ`, a zero refused
  at the fold, tail and level batching challenges only): it accepts less, and it is a refusal of
  zero challenges in the sense of `NZ`, so the random-oracle bound of the guest's carries over.
-/

module

public import LeanVM.Guest.Child.NZRun
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.WithHashBridge
public import LeanVM.Guest.WithHash
public import LeanVM.Guest.AcceptableChild

/-!
# Refusing a zero challenge anywhere

`P.refusingZeroChallenge` is `P` with every sampled challenge `0` a failure (`Statement/LeanVmGuestCompleteness.lean`).

* It is a refusal of zero challenges of `P` (`nz_refuseZero`) and only fails more
  (`refines_refuseZero`), so the completeness argument of `NZ` programs applies to it as it is.
* It refuses at least what any refusal of zero challenges `Q` of `P` refuses
  (`refines_refuseZero_of_nz`: `NZ Q P → Refines P.refusingZeroChallenge Q`), so a proof the statement's
  refusing verifier accepts is accepted by the guest's (`verifyDeferredNZ_of_rz`,
  `verifierNZ_of_rz`).
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

/-- **Refusing zero challenges anywhere is a refusal of zero challenges.** -/
theorem nz_refuseZero : ∀ P : VerifierProgram α, NZ P.refusingZeroChallenge P
  | .ret a => .ret a
  | .fail => .fail
  | .read k => .read fun x ↦ nz_refuseZero (k x)
  | .sample k => .sample fun c hc ↦ by
      show NZ (if c = 0 then VerifierProgram.fail else (k c).refusingZeroChallenge) (k c)
      simp only [hc, ↓reduceIte]
      exact nz_refuseZero (k c)
  | .grind _ k => .grind (nz_refuseZero k)
  | .commit _ _ k => .commit (nz_refuseZero k)
  | .query _ _ k => .query fun r ↦ nz_refuseZero (k r)

/-- **Refusing zero challenges anywhere only fails more.** -/
theorem refines_refuseZero : ∀ P : VerifierProgram α, Limits.Refines P.refusingZeroChallenge P
  | .ret a => .ret a
  | .fail => .fail _
  | .read k => .read fun x ↦ refines_refuseZero (k x)
  | .sample k => .sample fun c ↦ by
      show Limits.Refines (if c = 0
          then VerifierProgram.fail else (k c).refusingZeroChallenge) (k c)
      split
      · exact .fail _
      · exact refines_refuseZero (k c)
  | .grind _ k => .grind (refines_refuseZero k)
  | .commit _ _ k => .commit (refines_refuseZero k)
  | .query _ _ k => .query fun r ↦ refines_refuseZero (k r)

/-- **Refusing zero challenges anywhere refuses at least what any refusal of zero challenges
does.** -/
theorem refines_refuseZero_of_nz {Q P : VerifierProgram α} (h : NZ Q P) : Limits.Refines P.refusingZeroChallenge Q := by
  induction h with
  | ret a => exact .ret a
  | fail => exact .fail _
  | read _ ih => exact .read ih
  | sample _ ih =>
    refine .sample fun c ↦ ?_
    show Limits.Refines (if c = 0 then VerifierProgram.fail else _) _
    split
    · exact .fail _
    · rename_i hc
      exact ih c hc
  | grind _ ih => exact .grind ih
  | commit _ ih => exact .commit ih
  | query _ ih => exact .query ih

/-! ## The deferring verifier and the verifier -/

/-- **The statement's refusing deferring verifier accepts only what the guest's accepts.** -/
theorem verifyDeferredNZ_of_rz {bytecode : List K} {iv publicInput : Digest} {c : BytecodeClaim}
    {π : Proof} (h : Limits.verifyDeferredRefusingZero bytecode iv publicInput c π = true) :
    Limits.verifyDeferredNZ bytecode iv publicInput c π = true := by
  rw [Limits.verifyDeferredRefusingZero_eq_withHash] at h
  unfold Limits.verifyDeferredNZ
  refine Limits.runProof_refines (refines_refuseZero_of_nz ?_) _ π h
  rw [deferredProgramNZ_eq, deferredProgram_eq]
  exact nz_program (claimedBytecodeValue c) bytecode publicInput

/-- A child the guest program accepts is accepted by the guest's deferring verifier refusing a
zero fold, tail or level batching challenge. -/
theorem _root_.LeanVM.Guest.Limits.verifyDeferredNZ_of_childOk {bytecode : List K} {seed : Digest}
    {c : Child} (h : AcceptableChild bytecode seed c) :
    Limits.verifyDeferredNZ bytecode seed (statementDigest seed c.statement) c.freshClaim c.proof =
      true :=
  verifyDeferredNZ_of_rz h.noZeroChallenge

/-- **The statement's refusing verifier accepts only what the guest's accepts.** -/
theorem verifierNZ_of_rz {prog : LeanIsaProgram} {input : PublicInput} {π : Proof}
    (h : Budget.verifierRefusingZeroWithHash (m := Id) keccak256 keccakF1600 prog input π = true) :
    Budget.verifierNZ (m := Id) keccak256 keccakF1600 prog input π = true := by
  unfold Budget.verifierRefusingZeroWithHash at h
  unfold Budget.verifierNZ
  refine Limits.runProof_refines (refines_refuseZero_of_nz ?_) _ π h
  rw [leanVmProgram_eq]
  exact nz_program computedBytecodeValue (bytecodeWords prog) (publicInputDigest input)

/-! ## The claim a run evaluates -/

/-- **An accepted run with the computed value, refusing zero challenges, is the run with a true
claim**, refusing zero challenges: the claim of the value at the point the run evaluates. -/
theorem run_claimed_of_computed_rz (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState)
    (opening : ℕ → ℕ → List StackClaim → VerifierProgram Unit) (bytecode : List K) (publicInput :
        Digest)
    (k : Unit → VerifierProgram Bool) {st : VerifierProgramState} {r : Bool × VerifierProgramState}
    (h : Compile.runWithHash H F ((execWith computedBytecodeValue opening bytecode publicInput).bind k).refusingZeroChallenge st =
      some r) :
    ∃ c : BytecodeClaim, c.Holds bytecode ∧
      Compile.runWithHash H F ((execWith (claimedBytecodeValue c) opening bytecode publicInput).bind k).refusingZeroChallenge st =
        some r := by
  rw [execSplit, VerifierProgram.bind_assoc, refuseZero_bind, run_bind'] at h
  rcases hp : Compile.runWithHash H F (prefixProg bytecode).refusingZeroChallenge st with _ | ⟨y, s1⟩
  · rw [hp] at h; simp at h
  rw [hp] at h
  have hy : y.layout.bytecode = bytecode :=
    prefix_bytecode (VerifierProgram.returns_of_run H F
      (Limits.run_refines (H := H) (F := F) (refines_refuseZero _) st (y, s1) hp))
  refine ⟨⟨busPoint y, multilinearEval (bytecode.map ofK) (busPoint y)⟩, rfl, ?_⟩
  rw [execSplit, VerifierProgram.bind_assoc, refuseZero_bind, run_bind', hp]
  simp only [Option.bind_some] at h ⊢
  rw [← h, hy]
  simp only [claimedBytecodeValue, computedBytecodeValue, VerifierProgram.require,
      VerifierProgram.bind_eq,
    VerifierProgram.pure_eq, VerifierProgram.ret_bind, ↓reduceIte]

/-- **An accepted proof with the computed value, refusing zero challenges, is accepted with a true
claim**, refusing zero challenges. -/
theorem runProof_claimed_of_computed_rz (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState)
    (opening : ℕ → ℕ → List StackClaim → VerifierProgram Unit) (bytecode : List K) (publicInput :
        Digest)
    {sd : KeccakState} {π : Proof}
    (h : Id.run (runProofWithHash H F ((execWith computedBytecodeValue opening bytecode
        publicInput).bind
      fun _ ↦ VerifierProgram.ret true).refusingZeroChallenge sd π) = true) :
    ∃ c : BytecodeClaim, c.Holds bytecode ∧
      Id.run (runProofWithHash H F ((execWith (claimedBytecodeValue c) opening bytecode
          publicInput).bind
        fun _ ↦ VerifierProgram.ret true).refusingZeroChallenge sd π) = true := by
  unfold runProofWithHash at h ⊢
  revert h
  match hr : Compile.runWithHash H F ((execWith computedBytecodeValue opening bytecode
      publicInput).bind
      fun _ ↦ VerifierProgram.ret true).refusingZeroChallenge ⟨⟨sd, []⟩, π.stream, π.openings,
          []⟩ with
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
