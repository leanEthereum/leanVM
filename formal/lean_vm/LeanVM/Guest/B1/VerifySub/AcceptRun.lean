/-
  LeanVM.Guest.B1.VerifySub.AcceptRun

  From a child's acceptance by the deferring verifier to runs of its prefix and of its stacked
  opening.
-/

module

public import LeanVM.Guest.B1.VerifySub.NoCommit
public import LeanVM.Guest.B1.VerifySub.RunId
public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.B1.Whir.Split

/-!
# The deferring verifier's runs, split at the stacked opening

`flatPre c bytecode pi`: the deferring verifier up to its stacked opening, its phases grouped as
`verify_sub` runs them (Split.lean's `deferredFlat`), returning the layout, the rate and the
claims. The deferring verifier is `flatPre`, then `verifyStackedOpening` (`deferred_pre`).

`accept_deferred`: an accepted run is a run of `flatPre` from the child's start, then of its
stacked opening to the stream's and the openings' end. `opening_run`: the stacked opening is the
claims' check, the batching challenge, then `Whir.whirOpen`, then the terminal's check.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Verifier.Claims

@[expose] public section

/-! ## The prefix -/

/-- **The deferring verifier up to its stacked opening**, grouped as `verify_sub` runs it. -/
def flatPre (c : BytecodeClaim) (bytecode : List K) (pi : Digest) :
    VerifierProgram (Layout × ℕ × List StackClaim) :=
  (readAnnouncedSizes bytecode).bind fun ls ↦
  (commitStack ls.1.stackLog ls.2).bind fun _ ↦
  (readOod ls.1.stackLog).bind fun ood ↦
  (VerifierProgram.require (busDepth ls.1 < 64)).bind fun _ ↦
  (busChallenges (busDepth ls.1)).bind fun wb ↦
  (Tables.gkrPhase (busDepth ls.1)).bind fun r ↦
  (Tables.tablesSeg (claimedBytecodeValue c) ls.1 pi wb.1 wb.2 r.2.1 r.2.2).bind fun bc ↦
  (keccakPhaseClaims ls.1 bc.2).bind fun kc ↦
  (ringSwitch kc.2.1 kc.2.2).bind fun rs ↦
  VerifierProgram.ret (ls.1, ls.2, stackClaims ls.1 kc.1 rs.1 rs.2 ood)

/-- **The deferring verifier: the prefix, then the stacked opening.** -/
theorem deferred_pre (c : BytecodeClaim) (bytecode : List K) (pi : Digest) :
    deferringVerifierProgram c bytecode pi = (flatPre c bytecode pi).bind fun q ↦
      (verifyStackedOpening q.1.stackLog q.2.1 q.2.2).bind fun _ ↦ VerifierProgram.ret true := by
  rw [deferred_eq]
  simp only [deferredFlat, flatPre, VerifierProgram.bind_assoc, VerifierProgram.ret_bind]

/-! ## The stacked opening -/

/-- The batching's target over the claims at `λ`. -/
def batchTarget (cl : List StackClaim) (lam : E) : E :=
  dot (powers lam cl.length) (cl.map (·.2))

/-- The batching's weight over the claims at `λ`. -/
def batchBasis (cl : List StackClaim) (lam : E) : List E → E :=
  fun point ↦ dot (powers lam cl.length) (cl.map fun c ↦ c.1 point)

theorem verifyStackedOpening_split (μ r : ℕ) (cl : List StackClaim) :
    verifyStackedOpening μ r cl =
      (VerifierProgram.require (StackedOk cl)).bind fun _ ↦
      VerifierProgram.sampleChallenge.bind fun lam ↦
      (Whir.whirOpen μ r (batchTarget cl lam)).bind fun w ↦
        VerifierProgram.require (w.Accepts (batchBasis cl lam)) := by
  rw [verifyStackedOpening_nf]
  simp only [Whir.verifyWhir_split, VerifierProgram.bind_eq]
  rfl

/-! ## From the child's acceptance -/

/-- The deferring verifier's start on a child's proof. -/
def deferStart (seed pi : Digest) (π : Proof) : VerifierProgramState :=
  ⟨⟨keccakF1600 (seedInput seed pi), [], none⟩, π.stream, π.openings, []⟩

theorem runProof_accepts {P : VerifierProgram Bool} {seed : KeccakState} {π : Proof}
    (h : Id.run (runProofWithHash (m := Id) keccak256 keccakF1600 P seed π) = true) :
    ∃ t : VerifierProgramState, runId P ⟨⟨seed, [], none⟩, π.stream, π.openings, []⟩ =
      some (true, t) ∧ t.stream = [] ∧ t.openings = [] := by
  unfold runProofWithHash at h
  revert h
  match hr : Compile.runWithHash (m := Id) keccak256 keccakF1600 P
      ⟨⟨seed, [], none⟩, π.stream, π.openings, []⟩ with
  | some (true, s) =>
    intro h
    change (s.stream.isEmpty && s.openings.isEmpty) = true at h
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    exact ⟨s, hr, h.1, h.2⟩
  | some (false, _) =>
    intro h
    change false = true at h
    exact absurd h Bool.false_ne_true
  | none =>
    intro h
    change false = true at h
    exact absurd h Bool.false_ne_true

/-- A run of `p`, then `ret`, is a run of `p`. -/
theorem runId_bind_ret {α β : Type} {p : VerifierProgram α} {b : β}
    {st : VerifierProgramState} {r : β × VerifierProgramState}
    (h : runId (p.bind fun _ ↦ VerifierProgram.ret b) st = some r) :
    ∃ a, runId p st = some (a, r.2) := by
  obtain ⟨a, st', h1, h2⟩ := runId_bind_some h
  have e : runId (VerifierProgram.ret b) st' = some (b, st') := rfl
  rw [e, Option.some.injEq] at h2
  subst h2
  exact ⟨a, h1⟩

/-- **A proof the deferring verifier accepts**: a run of the prefix, then of its stacked opening,
to the stream's and the openings' end. -/
theorem accept_deferred {bytecode : List K} {seed pi : Digest} {c : BytecodeClaim} {π : Proof}
    (h : verifyDeferred bytecode seed pi c π = true) :
    ∃ q stq t, runId (flatPre c bytecode pi) (deferStart seed pi π) = some (q, stq) ∧
      runId (verifyStackedOpening q.1.stackLog q.2.1 q.2.2) stq = some ((), t) ∧
      t.stream = [] ∧ t.openings = [] := by
  have h' : Id.run (runProofWithHash (m := Id) keccak256 keccakF1600
      (deferringVerifierProgram c bytecode pi) (keccakF1600 (seedInput seed pi)) π) = true := by
    rw [verifyDeferred_eq_withHash] at h
    exact h
  obtain ⟨t, hrun, ht1, ht2⟩ := runProof_accepts h'
  rw [deferred_pre] at hrun
  obtain ⟨q, stq, h1, h2⟩ := runId_bind_some hrun
  obtain ⟨u, h3⟩ := runId_bind_ret h2
  exact ⟨q, stq, t, h1, h3, ht1, ht2⟩

/-- A sample's run. -/
theorem runId_sample_bind {α : Type} (g : E → VerifierProgram α) (st : VerifierProgramState) :
    runId (VerifierProgram.sampleChallenge.bind g) st =
      runId (g (Id.run (squeeze keccakF1600 st.sponge)).1)
        { st with sponge := (Id.run (squeeze keccakF1600 st.sponge)).2 } := rfl

/-- A requirement's run. -/
theorem runId_require_bind {α : Type} {c : Prop} [Decidable c] {k : Unit → VerifierProgram α}
    {st : VerifierProgramState} {r : α × VerifierProgramState}
    (h : runId ((VerifierProgram.require c).bind k) st = some r) : c ∧ runId (k ()) st = some r := by
  unfold VerifierProgram.require at h
  split at h
  · exact ⟨by assumption, h⟩
  · exact absurd h (by rintro ⟨⟩)

/-- **The stacked opening**: the claims' check, the batching challenge, then `whirOpen` to an end
passing the terminal's check. -/
theorem opening_run {μ r : ℕ} {cl : List StackClaim} {st t : VerifierProgramState} {u : Unit}
    (h : runId (verifyStackedOpening μ r cl) st = some (u, t)) :
    cl.length ≤ maxStackedClaims ∧ ∃ w,
      runId (Whir.whirOpen μ r (batchTarget cl (Id.run (squeeze keccakF1600 st.sponge)).1))
        { st with sponge := (Id.run (squeeze keccakF1600 st.sponge)).2 } = some (w, t) ∧
      w.Accepts (batchBasis cl (Id.run (squeeze keccakF1600 st.sponge)).1) := by
  rw [verifyStackedOpening_split] at h
  obtain ⟨hok, h⟩ := runId_require_bind h
  refine ⟨hok.length_le, ?_⟩
  rw [runId_sample_bind] at h
  obtain ⟨w, st3, h3, h4⟩ := runId_bind_some h
  unfold VerifierProgram.require at h4
  split at h4
  · rename_i hacc
    have e : runId (VerifierProgram.ret ()) st3 = some ((), st3) := rfl
    rw [e, Option.some.injEq, Prod.mk.injEq] at h4
    obtain ⟨-, rfl⟩ := h4
    exact ⟨w, h3, hacc⟩
  · exact absurd h4 (by rintro ⟨⟩)

end
end LeanVM.Guest.B1.VerifySub
