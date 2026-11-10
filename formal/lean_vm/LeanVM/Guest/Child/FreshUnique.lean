/-
  LeanVM.Guest.Child.FreshUnique

  The deferring verifier accepts a proof with at most one true claim on the bytecode.
-/

module

public import LeanVM.Guest.Child.Fresh

/-!
# At most one true fresh claim

The deferring verifier's run is a prefix that does not read the claim (`prefixProg`), the claim's
value at the point the prefix returns (`claimedBytecodeValue`, which fails elsewhere), and a suffix
(`execSplit`). So an accepted run's claim is at the prefix's point, which is the same for every
claim on the same proof (`point_of_verifyDeferred`), and a true claim's value is the bytecode's at
its point: two true claims accepted on one proof are equal (`freshClaim_unique`).
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The deferring program, as a sequence. -/
theorem deferredProgram_execWith (c : BytecodeClaim) (bytecode : List K) (publicInput : Digest) :
    deferringVerifierProgram c bytecode publicInput =
      (execWith (claimedBytecodeValue c) verifyStackedOpening bytecode publicInput).bind
        fun _ ↦ VerifierProgram.ret true := by
  unfold deferringVerifierProgram verifyExecution execWith
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc]

/-- **An accepted run of the deferring program has its claim at the prefix's point.** -/
theorem point_of_run_deferred (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState)
    {c : BytecodeClaim} {bytecode : List K} {publicInput : Digest} {st : VerifierProgramState}
    {r : Bool × VerifierProgramState}
    (h : Compile.runWithHash H F (deferringVerifierProgram c bytecode publicInput) st = some r) :
    ∃ y s1, Compile.runWithHash H F (prefixProg bytecode) st = some (y, s1) ∧
      c.bytecodePoint = busPoint y := by
  rw [deferredProgram_execWith, execSplit, VerifierProgram.bind_assoc, run_bind'] at h
  rcases hp : Compile.runWithHash H F (prefixProg bytecode) st with _ | ⟨y, s1⟩
  · rw [hp] at h
    simp at h
  rw [hp] at h
  refine ⟨y, s1, rfl, ?_⟩
  by_contra hne
  have hne' : ¬ y.bytecodePoint = c.bytecodePoint := fun e ↦ hne e.symm
  simp only [Option.bind_some, claimedBytecodeValue, VerifierProgram.require, hne', false_and,
    ↓reduceIte] at h
  have e : (((VerifierProgram.fail : VerifierProgram Unit).bind
      fun _ ↦ suffixProg verifyStackedOpening publicInput y).bind
      fun _ ↦ VerifierProgram.ret true) = (VerifierProgram.fail : VerifierProgram Bool) := rfl
  rw [e] at h
  simp [Compile.runWithHash] at h

/-- **The deferring verifier's acceptance places its claim at the prefix's point**, from the seed
of `iv` and the public input on the proof, whatever the claim. -/
theorem point_of_verifyDeferred {bytecode : List K} {iv publicInput : Digest} {c : BytecodeClaim}
    {proof : Proof} (h : verifyDeferred bytecode iv publicInput c proof = true) :
    ∃ y s1, Compile.runWithHash (m := Id) keccak256 keccakF1600 (prefixProg bytecode)
        ⟨⟨keccakF1600 (seedInput iv publicInput), [], none⟩, proof.stream, proof.openings, []⟩ =
          some (y, s1) ∧ c.bytecodePoint = busPoint y := by
  rw [verifyDeferred_eq_withHash] at h
  have h2 : Id.run (runProofWithHash (m := Id) keccak256 keccakF1600
      (deferringVerifierProgram c bytecode publicInput) (keccakF1600 (seedInput iv publicInput))
          proof) =
        true := h
  unfold runProofWithHash at h2
  cases hr : Compile.runWithHash (m := Id) keccak256 keccakF1600
      (deferringVerifierProgram c bytecode publicInput)
      ⟨⟨keccakF1600 (seedInput iv publicInput), [], none⟩, proof.stream, proof.openings, []⟩ with
  | none => rw [hr] at h2; cases h2
  | some r => exact point_of_run_deferred _ _ hr

/-- **The deferring verifier accepts a proof with at most one true claim on the bytecode.** -/
theorem freshClaim_unique {bytecode : List K} {iv publicInput : Digest}
    {claim claim' : BytecodeClaim} {proof : Proof}
    (h : verifyDeferred bytecode iv publicInput claim proof = true)
    (h' : verifyDeferred bytecode iv publicInput claim' proof = true)
    (hc : claim.Holds bytecode) (hc' : claim'.Holds bytecode) : claim = claim' := by
  obtain ⟨y, s1, hy, hp⟩ := point_of_verifyDeferred h
  obtain ⟨y', s1', hy', hp'⟩ := point_of_verifyDeferred h'
  rw [hy] at hy'
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hy')
  obtain ⟨z, v⟩ := claim
  obtain ⟨z', v'⟩ := claim'
  dsimp only at hp hp'
  subst hp hp'
  unfold BytecodeClaim.Holds at hc hc'
  dsimp only at hc hc'
  rw [← hc, ← hc']

end
end LeanVM.Guest.Child
