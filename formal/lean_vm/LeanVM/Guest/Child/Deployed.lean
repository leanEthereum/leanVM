/-
  LeanVM.Guest.Child.Deployed

  The deployed half of `GuestChildComplete`: the child prover's proof with Keccak of a guest
  execution of committed size in `[2^22, 2^28]`, when the verifier refusing a zero challenge
  accepts it, is with its statement and the claims its run evaluates a child the guest accepts.
-/

module

public import LeanVM.Guest.Child.Merkle
public import LeanVM.Guest.Child.StackLog
public import LeanVM.Guest.Start
public import LeanVM.Guest.Child.RefuseZero
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.WithHashBridge
public import LeanVM.Guest.WithHash
public import LeanVM.Protocol.EndToEnd.Sound.Moves

/-!
# Honest children at Keccak

`childOk_of_verifierRZ`: from the acceptance of the verifier refusing a zero challenge
(`Budget.verifierRefusingZero`, which accepts only what `Budget.verifierNZ` does) at Keccak, of
the child prover's proof (`childProver`), when it makes one, of a guest execution on a statement's
digest under the deployed seed:

* the deferring verifier refusing a zero challenge accepts it with the claim its run evaluates,
  a true claim (`run_claimed_of_computed`): `noZeroChallenge`, and so `verifies`
  (`Limits.verifyDeferred_of_nz`) and `stream` (`stream_le_of_verifyDeferred`);
* the proof is the pure prover's (`prove_of_some`), whose stream starts with the honest
  sizes, of the execution's committed size (`muMin_le_announced`): `stackLog`;
* its query steps under the deferring program are the verifier program's (`queriesOf_le`, the
  claim being true), which are honest batches in range (`queriesOf_proveFrom`,
  `inRange_leanVmProgram`), which agree (`batchAgrees_honest`): `capsAgree`.
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol.KeccakHash LeanVM.Node LeanVM.Guest.End
open Air.Flat (EnsembleWitness)

@[expose] public section

/-- `Strategy.acceptsFrom_of_runFrom` stated on `runI` and `shapedI` together, for a program equal to
`P'`: under 4.35 a local of type `AcceptsFrom` or `ShapedFrom` on the concrete program makes the
elaborator unfold it, so the honest run's parts are taken here, on any program. -/
private theorem acceptsFrom_of_runI {S : Strategy} {P P' : VerifierProgram Bool} (hP : P = P')
    (h : ∀ chal, runI P S chal = some true ∧ shapedI P S chal) : S.AcceptsFrom P' [] := by
  subst hP
  exact Strategy.acceptsFrom_of_runFrom P [] (fun chal ↦ (h chal).1) (fun chal ↦ (h chal).2)

/-- **An accepted proof of a prover that is the specification at a child's witness (or makes no
proof) is a child the guest accepts.** -/
theorem childOk_of_verifierRZ_of {A : HonestProverWithHash} {s : NodeStatement}
    {t : Execution guestProgram} {ρ fuel : ℕ}
    (hA : ChildSpec A guestProgram (publicInputOf (statementDigest (deployedSeed guestProgram) s)) t ρ fuel)
    (h21 : 2 ^ 21 < t.committedSize) (hsh : s.deferredClaim.HasBytecodeShape bytecode)
    {proof : Proof}
    (hsome : Budget.honestProofWithDeployedKeccakWithHash A guestProgram
      (publicInputOf (statementDigest (deployedSeed guestProgram) s)) t ρ fuel = some proof)
    (hacc : Budget.verifierRefusingZeroWithHash (m := Id) keccak256 keccakF1600 guestProgram
      (publicInputOf (statementDigest (deployedSeed guestProgram) s)) proof = true) :
    ∃ fresh, fresh.Holds bytecode ∧
      LeanVM.Guest.AcceptableChild bytecode (deployedSeed guestProgram) ⟨s, fresh, proof⟩ := by
  set d := statementDigest (deployedSeed guestProgram) s with hd
  have hpd : publicInputDigest (publicInputOf d) = d := publicDigest_publicInputOf d
  -- the claim the run evaluates
  have hacc' := hacc
  rw [verifierRZ_eq] at hacc'
  obtain ⟨c, hc, hrz⟩ := runProof_claimed_of_computed_rz keccak256 keccakF1600
    Completeness.verifyStackedOpeningRefusingZeroCombiner (bytecodeWords guestProgram)
    (publicInputDigest (publicInputOf d)) hacc'
  rw [hpd] at hrz
  have hRZC : Limits.verifyDeferredRefusingZeroCombiner bytecode (deployedSeed guestProgram) d c
      proof = true := by
    rw [verifyDeferredRefusingZeroCombiner_eq_withHash]
    exact hrz
  have hRZ := verifyDeferredRefusingZero_of_rzc hRZC
  have hV := Limits.verifyDeferred_of_nz (verifyDeferredNZ_of_rzc hRZC)
  -- the pure prover's proof
  obtain ⟨w, sz, hchild, hprove⟩ := prove_of_some hA hsome
  obtain ⟨⟨hρ, hw, hs, hadm, -⟩, -⟩ := id hchild
  obtain ⟨rest, hrest⟩ := stream_prefix keccak256 keccakF1600 hprove
  refine ⟨c, hc, ⟨hsh, hV, ?_, stream_le_of_verifyDeferred hV, ?_, hRZ, hRZC⟩⟩
  · -- the stack log
    show ∀ layout r, announcedLayoutAndRate bytecode proof.stream = some (layout, r) → _
    rw [hrest]
    exact muMin_le_announced hchild h21 rest
  · -- the caps
    intro b hb
    have hle : VerifierProgram.Le (deferringVerifierProgram c bytecode d) (leanVmVerifierProgram
        bytecode d) := by
      rw [deferredProgram_eq, leanVmProgram_eq]
      exact .bind (verifyExecution_le (claimed_le_computed hc) d) fun _ ↦ .refl _
    have hb' := queriesOf_le hle hb
    have hq := m3Honest_stackOf hw hs
    unfold prove at hprove
    obtain ⟨tt, htt, he⟩ := Option.map_eq_some_iff.mp hprove
    rw [hpd] at htt
    have hir := inRange_leanVmProgram bytecode d
    have := queriesOf_proveFrom _ fuel (leanVmVerifierProgram bytecode d) [] _ tt.1 tt.2 [] []
      (acceptsFrom_of_runI (P := leanVmVerifierProgram bytecode (publicInputDigest (publicInputOf d)))
        (by rw [hpd]) fun chal ↦ by
        with_reducible exact runI_leanVmProgram (input := publicInputOf d) hadm hρ hq chal)
      (by simp [commits]) (LeanVM.Protocol.EndToEnd.Sound.grindThenSample_leanVmProgram _ _)
      (Or.inl rfl) (by simpa [commits] using hir) htt b
    obtain ⟨ht, word, ps, rfl, hps⟩ := this (by
      have e : proof = ⟨tt.1, tt.2⟩ := he.symm
      simp only [List.append_nil, rootsOf, commits, List.map_nil]
      rw [e] at hb'
      exact hb')
    exact batchAgrees_honest hps

/-- **The child prover's accepted proof is a child the guest accepts.** -/
theorem childOk_of_verifierRZ {s : NodeStatement} {t : Execution guestProgram} {ρ fuel : ℕ}
    (h21 : 2 ^ 21 < t.committedSize) (hsh : s.deferredClaim.HasBytecodeShape bytecode)
    {proof : Proof}
    (hsome : Budget.honestProofWithDeployedKeccakWithHash childProver guestProgram
      (publicInputOf (statementDigest (deployedSeed guestProgram) s)) t ρ fuel = some proof)
    (hacc : Budget.verifierRefusingZeroWithHash (m := Id) keccak256 keccakF1600 guestProgram
      (publicInputOf (statementDigest (deployedSeed guestProgram) s)) proof = true) :
    ∃ fresh, fresh.Holds bytecode ∧
      LeanVM.Guest.AcceptableChild bytecode (deployedSeed guestProgram) ⟨s, fresh, proof⟩ :=
  childOk_of_verifierRZ_of (childSpec_childProver _ _ _ _ _) h21 hsh hsome hacc

end
end LeanVM.Guest.Child
