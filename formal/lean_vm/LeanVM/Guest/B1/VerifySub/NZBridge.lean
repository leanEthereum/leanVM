/-
  LeanVM.Guest.B1.VerifySub.NZBridge

  From a child's acceptance by the deferring verifier refusing zero challenges (G7's
  `Limits.verifyDeferredNZ`) to the hypotheses of `open_stacked`'s completeness (B1-b's
  `B1.Whir.NoZeroChallenge`, `B1.Whir.CapsAgree`) at the stacked opening.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.B1.VerifySub.NoCommit
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.AcceptableChild

/-!
# The opening's hypotheses from the child's

The deferring verifier (`deferringVerifierProgram`, V:2358) and G7's variant refusing a zero fold,
tail or level batching challenge (`Limits.deferredProgramNZ`) share their run up to the stacked
opening:
`specPre`, the announced sizes, the stack's commitment and the claims (`restClaims`: the bus,
the tables, the public input, the Keccak reduction, the ring switch). Then each squeezes the
batching challenge `λ` and runs B1-b's `whirOpen` (`whirOpenNZ`) and the terminal's check
(`verifyExecution_pre`, `verifyExecutionNZ_pre`, `verifyStackedOpening_split`,
`verifyStackedOpeningNZ_split`).

`nz_open_of_nz`: an accepted run of the NZ variant passes through `specPre` to the opening's
start, the caller's sponge state `S` with nothing waiting, the stream's rest `xsW`, the proof's
openings and the stack's root alone among the commitments (`specPre`'s phases but the stack's
commitment commit nothing, `NoCommit`); there the opening runs (`RunsWith (whirOpen …)`), with no
zero challenge (`B1.Whir.NoZeroChallenge`), and its end passes the terminal's check.
`caps_open_of_caps`: at the same start, the opening's query steps are among the whole run's
(`queriesOf_eq_steps`), so G7's agreement of the run's openings gives B1-b's `CapsAgree`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The shared prefix -/

/-- The claims the stacked opening batches, from the stack's commitment on (`verifyExecution`,
steps 3-7): the bus, the tables, the public input, the Keccak reduction, the ring switch. -/
def restClaims (ev : (List K → List E → VerifierProgram E)) (layout : Layout) (publicInput :
    Digest) :
    VerifierProgram (List StackClaim) := do
  let bus ← verifyBusBalance ev layout
  let claims ← tablePhaseClaims layout bus
  let publicClaims ← publicInputPhase layout publicInput
  let (claims, keccakPoint, keccakSlices) ← keccakPhaseClaims layout (claims ++ publicClaims)
  let (ringTarget, ringWeight) ← ringSwitch keccakPoint keccakSlices
  return ringSwitchClaim layout ringTarget ringWeight :: claims.map (·.stackClaim layout)

/-- **The deferring verifier up to its stacked opening**: the layout, the rate and the claims. -/
def specPre (ev : (List K → List E → VerifierProgram E)) (bytecode : List K) (publicInput :
    Digest) :
    VerifierProgram (Layout × ℕ × List StackClaim) :=
  (readAnnouncedSizes bytecode).bind fun ls ↦
  (commitStack ls.1.stackLog ls.2).bind fun _ ↦
  (restClaims ev ls.1 publicInput).bind fun cl ↦ VerifierProgram.ret (ls.1, ls.2, cl)

theorem verifyExecution_pre (ev : (List K → List E → VerifierProgram E)) (bytecode : List K) (pi :
    Digest) :
    verifyExecutionClaims ev bytecode pi =
      (specPre ev bytecode pi).bind fun q ↦ verifyStackedOpening q.1.stackLog q.2.1 q.2.2 := by
  simp only [verifyExecutionClaims, specPre, restClaims, VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc,
    VerifierProgram.ret_bind]

theorem verifyExecutionNZ_pre (ev : (List K → List E → VerifierProgram E)) (bytecode : List K) (pi :
    Digest) :
    Limits.verifyExecutionNZ ev bytecode pi =
      (specPre ev bytecode pi).bind fun q ↦
        Limits.verifyStackedOpeningNZ q.1.stackLog q.2.1 q.2.2 := by
  simp only [Limits.verifyExecutionNZ, specPre, restClaims, VerifierProgram.bind_eq,
      VerifierProgram.pure_eq,
    VerifierProgram.bind_assoc, VerifierProgram.ret_bind]

/-! ## The opening -/

/-- The batching's target over the claims at `λ`. -/
def batchTarget (cl : List StackClaim) (lam : E) : E :=
  dot (powers lam cl.length) (cl.map (·.2))

/-- The batching's weight over the claims at `λ`. -/
def batchBasis (cl : List StackClaim) (lam : E) : List E → E :=
  fun point ↦ dot (powers lam cl.length) (cl.map fun c ↦ c.1 point)

theorem verifyStackedOpening_split (μ r : ℕ) (cl : List StackClaim) :
    verifyStackedOpening μ r cl = VerifierProgram.sampleChallenge.bind fun lam ↦
      (Whir.whirOpen μ r (batchTarget cl lam)).bind fun w ↦
        VerifierProgram.require (w.Accepts (batchBasis cl lam)) := by
  simp only [verifyStackedOpening, verifyWhir_eq_target, Whir.verifyWhir_split, VerifierProgram.bind_eq, batchTarget]
  rfl

theorem foldRoundsNZ_eq : ∀ (n : ℕ) (s : WhirStateT) (lf : List E),
    Limits.foldRoundsNZ n s lf = Whir.foldRoundsNZ n s lf
  | 0, _, _ => rfl
  | n + 1, s, lf => by
    simp only [Limits.foldRoundsNZ, Whir.foldRoundsNZ, foldRoundsNZ_eq n]

theorem tailRoundsNZ_eq : ∀ (n : ℕ) (t : E) (quad : List E),
    Limits.tailRoundsNZ n t quad = Whir.tailRoundsNZ n t quad
  | 0, _, _ => rfl
  | n + 1, t, quad => by
    simp only [Limits.tailRoundsNZ, Whir.tailRoundsNZ, tailRoundsNZ_eq n]

theorem whirLevelsNZ_split (logN laneFolds : ℕ) (eb : List E → E) :
    ∀ (index : ℕ) (levels : List Whir.Level) (s : WhirStateT),
      Limits.whirLevelsNZ logN laneFolds eb index levels s =
        (Whir.whirLevelsOpenNZ logN laneFolds index levels s).bind fun w ↦
          VerifierProgram.require (w.Accepts eb)
  | _, [], _ => rfl
  | index, [level], s => by
    rw [Limits.whirLevelsNZ, Whir.whirLevelsOpenNZ]
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc,
        VerifierProgram.ret_bind, Whir.WhirEnd.Accepts,
      foldRoundsNZ_eq, tailRoundsNZ_eq]
    repeat refine Whir.prog_bind_congr fun _ ↦ ?_
    rw [Whir.foldl_add_shift _ (eb _), add_comm (eb _)]
    congr 1
  | index, level :: next :: rest, s => by
    rw [Limits.whirLevelsNZ, Whir.whirLevelsOpenNZ]
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc,
        VerifierProgram.ret_bind, foldRoundsNZ_eq,
      whirLevelsNZ_split logN laneFolds eb (index + 1) (next :: rest)]

theorem verifyWhirNZ_split (logN logInvRate : ℕ) (target : E) (eb : List E → E) :
    Limits.verifyWhirNZ logN logInvRate target eb = (do
      let w ← Whir.whirOpenNZ logN logInvRate target
      VerifierProgram.require (w.Accepts eb)) := by
  simp only [Limits.verifyWhirNZ, Whir.whirOpenNZ, VerifierProgram.bind_eq,
      VerifierProgram.bind_assoc,
    whirLevelsNZ_split]

theorem verifyStackedOpeningNZ_split (μ r : ℕ) (cl : List StackClaim) :
    Limits.verifyStackedOpeningNZ μ r cl = VerifierProgram.sampleChallenge.bind fun lam ↦
      (Whir.whirOpenNZ μ r (batchTarget cl lam)).bind fun w ↦
        VerifierProgram.require (w.Accepts (batchBasis cl lam)) := by
  simp only [Limits.verifyStackedOpeningNZ, verifyWhirNZ_split, VerifierProgram.bind_eq,
      batchTarget]
  rfl


/-! ## The prefix commits only the stack -/

theorem noCommit_busRest (c : BytecodeClaim) (L : Layout) (alphas : List E) (beta : E)
    (point tv : List E) : NoCommit (Tables.busRest (claimedBytecodeValue c) L alphas beta point
        tv) := by
  unfold Tables.busRest
  simp only [claimedBytecodeValue]
  nc

theorem noCommit_verifyBusBalance (c : BytecodeClaim) (layout : Layout) :
    NoCommit (verifyBusBalance (claimedBytecodeValue c) layout) := by
  rw [verifyBusBalance_split]
  refine NoCommit.bind ?_ ?_
  · exact noCommit_sampleN _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_sampleE
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_gkrPhase _
  intro _
  exact noCommit_busRest _ _ _ _ _ _

theorem noCommit_publicInputPhase (layout : Layout) (pi : Digest) :
    NoCommit (publicInputPhase layout pi) := by
  unfold publicInputPhase
  nc

theorem noCommit_verifyKeccak (logSteps : ℕ) (inst output : List E) :
    NoCommit (verifyKeccak logSteps inst output) := by
  have h1 : 1 < keccakSegments := by decide
  unfold verifyKeccak
  simp only [h1, ↓reduceIte, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.ret_bind]
  refine NoCommit.bind ?_ ?_
  · exact noCommit_sampleN _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_sampleN _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_readE
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_keccakLayers _ _ _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_keccakOpen _ _ _ _ _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_readE
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_require _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_sumcheck _ _ _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_keccakOpen _ _ _ _ _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_readN _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_require _
  intro _
  exact noCommit_ret _

theorem noCommit_restClaims (c : BytecodeClaim) (layout : Layout) (pi : Digest) :
    NoCommit (restClaims (claimedBytecodeValue c) layout pi) := by
  unfold restClaims keccakPhaseClaims ringSwitch
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc,
      VerifierProgram.ret_bind]
  refine NoCommit.bind ?_ ?_
  · exact noCommit_verifyBusBalance _ _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_tablePhase _ _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_publicInputPhase _ _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_require _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_verifyKeccak _ _ _
  intro x
  rcases x with ⟨cl, kp, ks⟩
  refine NoCommit.bind ?_ ?_
  · exact noCommit_sampleN _
  intro _
  exact noCommit_ret _

/-- **The stack's commitment commits the stack's shape**, alone. -/
theorem commitStack_runF {μ r : ℕ} {st : Whir.FSt} {u : Unit} {st' : Whir.FSt}
    (h : Whir.runF (commitStack μ r) st = some (u, st')) :
    (∃ root, st'.roots = st.roots ++ [(root, Whir.stackShape μ r)]) ∧
      st'.openings = st.openings := by
  cases hc : Whir.ladder μ r with
  | none =>
    unfold commitStack at h
    rw [hc] at h
    exact absurd h (by simp [Verifier.liftOption, VerifierProgram.bind, Whir.runF])
  | some cfg =>
    cases cfg with
    | nil =>
      unfold commitStack at h
      rw [hc] at h
      exact absurd h (by simp [Verifier.liftOption, VerifierProgram.bind, Whir.runF])
    | cons level rest =>
      rw [Whir.commitStack_eq hc] at h
      obtain ⟨s, stream, os, R⟩ := st
      match stream, h with
      | x0 :: x1 :: xs, h =>
        simp only [VerifierProgram.readCommitment, Whir.runF] at h
        split at h
        · rename_i root _
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact ⟨⟨root, rfl⟩, rfl⟩
        · simp at h

/-- **The prefix's commitments**: from no commitment, the stack's root alone, the openings kept. -/
theorem specPre_runF {c : BytecodeClaim} {bytecode : List K} {pi : Digest} {st : Whir.FSt}
    {q : Layout × ℕ × List StackClaim} {st1 : Whir.FSt} (h0 : st.roots = [])
    (h : Whir.runF (specPre (claimedBytecodeValue c) bytecode pi) st = some (q, st1)) :
    (∃ root, st1.roots = [(root, Whir.stackShape q.1.stackLog q.2.1)]) ∧
      st1.openings = st.openings := by
  unfold specPre at h
  obtain ⟨ls, sA, hA, h⟩ := Whir.runF_bind_some h
  obtain ⟨rA, oA⟩ := NoCommit.runF (noCommit_readSizes _) hA
  obtain ⟨u, sB, hB, h⟩ := Whir.runF_bind_some h
  obtain ⟨⟨root, rB⟩, oB⟩ := commitStack_runF hB
  obtain ⟨cl, sC, hC, h⟩ := Whir.runF_bind_some h
  obtain ⟨rC, oC⟩ := NoCommit.runF (noCommit_restClaims _ _ _) hC
  simp only [Whir.runF, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨⟨root, ?_⟩, by rw [oC, oB, oA]⟩
  rw [rC, rB, rA, h0, List.nil_append]

/-! ## From the child's acceptance to the opening -/

theorem runProof_accepts {P : VerifierProgram Bool} {seed : KeccakState} {π : Proof}
    (h : Id.run (runProofWithHash (m := Id) keccak256 keccakF1600 P seed π) = true) :
    ∃ t : VerifierProgramState, runId P ⟨⟨seed, []⟩, π.stream, π.openings, []⟩ = some (true, t) ∧
      t.stream = [] ∧ t.openings = [] := by
  unfold runProofWithHash at h
  revert h
  match hr : Compile.runWithHash (m := Id) keccak256 keccakF1600 P ⟨⟨seed, []⟩, π.stream, π.openings, []⟩ with
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

theorem runF_sample_bind {β : Type} (g : E → VerifierProgram β) (st : Whir.FSt) :
    Whir.runF (VerifierProgram.sampleChallenge.bind g) st =
      Whir.runF (g st.sponge.squeeze.1) { st with sponge := st.sponge.squeeze.2 } := rfl

theorem runF_require_bind {β : Type} {c : Prop} [Decidable c] {k : Unit → VerifierProgram β}
    {st : Whir.FSt} {r : β × Whir.FSt} (h : Whir.runF ((VerifierProgram.require c).bind k) st =
        some r) :
    c ∧ Whir.runF (k ()) st = some r := by
  unfold VerifierProgram.require at h
  split at h
  · exact ⟨by assumption, h⟩
  · simp [VerifierProgram.bind, Whir.runF] at h

/-- The carried state the deferring verifier starts from. -/
def deferStart (seed pi : Digest) (π : Proof) : Whir.FSt :=
  ⟨⟨capOf (keccakF1600 (seedInput seed pi)), []⟩, π.stream, π.openings, []⟩

/-- **The opening's hypotheses from the child's acceptance with no zero challenge**: the
deferring verifier runs `specPre` to the opening's start (the sponge `sq`, the words `xsW` left,
the proof's openings, the stack's root alone); its batching challenge `λ` leaves the state `S`;
there `whirOpen` runs on `xsW` and the openings (`RunsWith`), with no zero challenge
(`B1.Whir.NoZeroChallenge`), to an end passing the terminal's check. -/
theorem nz_open_of_nz {bytecode : List K} {seed pi : Digest} {c : BytecodeClaim} {π : Proof}
    (h : Limits.verifyDeferredNZ bytecode seed pi c π = true) :
    ∃ (q : Layout × ℕ × List StackClaim) (sq : Fs) (root : Digest) (xsW : List E) (w : Whir.WhirEnd)
      (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
      Whir.runF (specPre (claimedBytecodeValue c) bytecode pi) (deferStart seed pi π) =
        some (q, ⟨sq, xsW, π.openings, [(root, Whir.stackShape q.1.stackLog q.2.1)]⟩) ∧
      Whir.RunsWith (Whir.whirOpen q.1.stackLog q.2.1 (batchTarget q.2.2 sq.squeeze.1))
        ⟨capOf sq.perm, []⟩ xsW π.openings [(root, Whir.stackShape q.1.stackLog q.2.1)] w s'
        roots' ∧
      Whir.NoZeroChallenge q.1.stackLog q.2.1 (batchTarget q.2.2 sq.squeeze.1) sq.perm xsW
        π.openings root ∧
      w.Accepts (batchBasis q.2.2 sq.squeeze.1) := by
  obtain ⟨t, hrun, ht1, ht2⟩ := runProof_accepts h
  have hF := Whir.runF_of_runId _ (deferStart seed pi π) ⟨keccakF1600 (seedInput seed pi), []⟩
    ⟨rfl, rfl⟩ true t hrun
  rw [ht1, ht2] at hF
  simp only [Limits.deferredProgramNZ, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      verifyExecutionNZ_pre,
    VerifierProgram.bind_assoc] at hF
  obtain ⟨q, st1, h1, h2⟩ := Whir.runF_bind_some hF
  obtain ⟨⟨root, hr1⟩, ho1⟩ := specPre_runF (by rfl) h1
  rw [verifyStackedOpeningNZ_split, VerifierProgram.bind_assoc, runF_sample_bind] at h2
  simp only [VerifierProgram.bind_assoc] at h2
  obtain ⟨w, st3, h3, h4⟩ := Whir.runF_bind_some h2
  obtain ⟨hacc, h5⟩ := runF_require_bind h4
  simp only [Whir.runF, Option.some.injEq, Prod.mk.injEq] at h5
  obtain ⟨-, rfl⟩ := h5
  obtain ⟨sq, xsW, os1, R1⟩ := st1
  simp only at hr1 ho1
  subst hr1 ho1
  have hsq : sq.squeeze.2 = ⟨capOf sq.perm, []⟩ := rfl
  rw [hsq] at h3
  have hW : Whir.runF (Whir.whirOpen q.1.stackLog q.2.1 (batchTarget q.2.2 sq.squeeze.1))
      ⟨⟨capOf sq.perm, []⟩, xsW, π.openings, [(root, Whir.stackShape q.1.stackLog q.2.1)]⟩ =
      some (w, ⟨Whir.fsOf t.sponge, [], [], t.roots⟩) := (Whir.whirOpenNZ_ref _ _ _ _ _ h3).1
  exact ⟨q, sq, root, xsW, w, _, _, h1, runsWith_of_runF hW, ⟨w, _, _, runsWith_of_runF h3⟩,
    hacc⟩


/-! ## The caps -/

theorem deferredProgram_pre (c : BytecodeClaim) (bytecode : List K) (pi : Digest) :
    deferringVerifierProgram c bytecode pi = (specPre (claimedBytecodeValue c) bytecode pi).bind
        fun q ↦
      (VerifierProgram.sampleChallenge.bind fun lam ↦
        (Whir.whirOpen q.1.stackLog q.2.1 (batchTarget q.2.2 lam)).bind fun w ↦
          VerifierProgram.require (w.Accepts (batchBasis q.2.2 lam))).bind fun _ ↦
              VerifierProgram.ret true := by
  simp only [deferredProgram_eq, verifyExecution_pre, VerifierProgram.bind_assoc,
    verifyStackedOpening_split]

/-- **The opening's caps from the run's**: at the opening's start `nz_open_of_nz` gives, the
opening's query steps are among the deferring verifier's, so their agreement is B1-b's
`CapsAgree`. -/
theorem caps_open_of_caps {bytecode : List K} {seed pi : Digest} {c : BytecodeClaim} {π : Proof}
    {q : Layout × ℕ × List StackClaim} {sq : Fs} {root : Digest} {xsW : List E}
    (hpre : Whir.runF (specPre (claimedBytecodeValue c) bytecode pi) (deferStart seed pi π) =
      some (q, ⟨sq, xsW, π.openings, [(root, Whir.stackShape q.1.stackLog q.2.1)]⟩))
    (hcaps : ∀ b ∈ Limits.queryStepsOf (deferringVerifierProgram c bytecode pi)
      ⟨⟨keccakF1600 (seedInput seed pi), []⟩, π.stream, π.openings, []⟩, Limits.OpeningsAgree b.1 b.2) :
    Whir.CapsAgree q.1.stackLog q.2.1 (batchTarget q.2.2 sq.squeeze.1) sq.perm xsW π.openings
      root := by
  intro b hb
  apply batchAgrees_of
  apply hcaps
  have e : Limits.queryStepsOf (deferringVerifierProgram c bytecode pi)
      ⟨⟨keccakF1600 (seedInput seed pi), []⟩, π.stream, π.openings, []⟩ =
      Whir.queryStepsOf (deferringVerifierProgram c bytecode pi) (deferStart seed pi π) :=
    queriesOf_eq_steps _ (deferStart seed pi π) ⟨keccakF1600 (seedInput seed pi), []⟩ ⟨rfl, rfl⟩
  rw [e, deferredProgram_pre, Whir.queriesOf_bind, hpre]
  refine List.mem_append_right _ ?_
  simp only
  rw [Whir.queriesOf_bind]
  refine List.mem_append_left _ ?_
  show b ∈ Whir.queryStepsOf ((Whir.whirOpen q.1.stackLog q.2.1 (batchTarget q.2.2 sq.squeeze.1)).bind
    fun w ↦ VerifierProgram.require (w.Accepts (batchBasis q.2.2 sq.squeeze.1))) _
  rw [Whir.queriesOf_bind]
  exact List.mem_append_left _ hb

/-! ## For a child -/

/-- **`open_stacked`'s hypotheses for an honest child**: under G7's per-child hypotheses
(acceptance with no zero challenge, openings agreeing in the caps), the deferring verifier runs
`specPre` to the opening's start; there `whirOpen` runs, with no zero challenge and openings
agreeing in the caps, to an end passing the terminal's check. -/
theorem child_open {bytecode : List K} (seed : Digest) (c : Node.Child)
    (hnz : Limits.verifyDeferredNZ bytecode seed (Node.statementDigest seed c.statement) c.freshClaim
      c.proof = true)
    (hcaps : ∀ b ∈ Limits.queryStepsOf
      (deferringVerifierProgram c.freshClaim bytecode (Node.statementDigest seed c.statement))
      (Coverage.childVerifierStart seed c), Limits.OpeningsAgree b.1 b.2) :
    ∃ (q : Layout × ℕ × List StackClaim) (sq : Fs) (root : Digest) (xsW : List E)
      (w : Whir.WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
      Whir.runF (specPre (claimedBytecodeValue c.freshClaim) bytecode (Node.statementDigest seed c.statement))
        (deferStart seed (Node.statementDigest seed c.statement) c.proof) =
        some (q, ⟨sq, xsW, c.proof.openings, [(root, Whir.stackShape q.1.stackLog q.2.1)]⟩) ∧
      Whir.RunsWith (Whir.whirOpen q.1.stackLog q.2.1 (batchTarget q.2.2 sq.squeeze.1))
        ⟨capOf sq.perm, []⟩ xsW c.proof.openings [(root, Whir.stackShape q.1.stackLog q.2.1)] w s'
        roots' ∧
      Whir.NoZeroChallenge q.1.stackLog q.2.1 (batchTarget q.2.2 sq.squeeze.1) sq.perm xsW
        c.proof.openings root ∧
      Whir.CapsAgree q.1.stackLog q.2.1 (batchTarget q.2.2 sq.squeeze.1) sq.perm xsW
        c.proof.openings root ∧
      w.Accepts (batchBasis q.2.2 sq.squeeze.1) := by
  obtain ⟨q, sq, root, xsW, w, s', roots', hpre, hrun, hnz', hacc⟩ := nz_open_of_nz hnz
  exact ⟨q, sq, root, xsW, w, s', roots', hpre, hrun, hnz', caps_open_of_caps hpre hcaps, hacc⟩

end
end LeanVM.Guest.B1.VerifySub
