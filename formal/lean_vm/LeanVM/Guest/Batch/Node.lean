/-
  LeanVM.Guest.Batch.Node

  A node's batching as the statement states it (`NodeRelation`: the program `nodeBatchingProgram` run on the stream
  of the children's claims and the hints) is the guest program's transcript `Node.batch`.
-/

module

public import LeanVM.Guest.Batch.Prog
public import LeanVM.Protocol.Verifier.DeferredShape
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.WithHashBridge
public import LeanVM.Guest.WithHash
public import LeanVM.Guest.AcceptableChild

/-!
# A node's batching

`batchRun_batchOf_iff`: for a deferred claim `d` of the bytecode's shape, the batching program `nodeBatchingProgram (· = d)` accepts the stream of the children's claims and the
hints exactly where `Node.batch` defers `d`. The program reads the sumcheck's `log₂ |bytecode|`
rounds; an accepting run consumes the whole stream, so the hints have that many rounds
(`rounds_length_of_accepts`), and `batch` defers a claim at a point of as many coordinates as the
hints have rounds.
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

theorem rsRun_length : ∀ (rounds : List (E × E)) (claim : E) (sp : Sponge),
    (rsRun rounds claim sp).1.1.length = rounds.length
  | [], _, _ => rfl
  | _ :: rest, _, _ => by simp [rsRun, rsRun_length rest]

/-- **The rounds read their messages**: a run of `k` rounds, then a continuation, on a stream
reads `2k` scalars and runs the continuation on the rest. -/
theorem runD_roundsProg_bind {β : Type} (f : List E × E → VerifierProgram β) :
    ∀ (k : ℕ) (claim : E) (sp : Sponge) (zs : List E) (os : List (List Opening))
      (roots : List (Digest × ℕ × ℕ)) {r : β × VerifierProgramState},
      runD ((sumcheckRoundsProgram claim k).bind f) ⟨sp, zs, os, roots⟩ = some r →
        2 * k ≤ zs.length ∧ ∃ x sp', runD (f x) ⟨sp', zs.drop (2 * k), os, roots⟩ = some r
  | 0, claim, sp, zs, os, roots, r, h => ⟨by omega, _, _, h⟩
  | k + 1, claim, sp, zs, os, roots, r, h => by
    rcases zs with _ | ⟨g1, _ | ⟨gInf, zs⟩⟩
    · exact absurd h (by simp [sumcheckRoundsProgram, VerifierProgram.readScalar, VerifierProgram.bind_eq, VerifierProgram.bind, runD, Compile.runWithHash])
    · exact absurd h (by simp [sumcheckRoundsProgram, VerifierProgram.readScalar, VerifierProgram.bind_eq, VerifierProgram.bind, runD, Compile.runWithHash])
    · simp only [sumcheckRoundsProgram, VerifierProgram.readScalar, VerifierProgram.sampleChallenge, VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc,
        VerifierProgram.ret_bind] at h
      obtain ⟨hlen, x, sp', hx⟩ := runD_roundsProg_bind _ k _ _ zs os roots h
      have e : (g1 :: gInf :: zs).drop (2 * (k + 1)) = zs.drop (2 * k) := by
        rw [show 2 * (k + 1) = 2 * k + 2 by ring]
        rfl
      rw [e]
      exact ⟨by simp; omega, _, sp', hx⟩

/-- The stream of the batching, its parts. -/
theorem batchStream_eq (cs : List ChildClaims) (h : BatchingHints) :
    batchingStream cs h = cellsBeforeChallenge cs ++
      (h.sumcheckMessages.flatMap (fun g ↦ [g.1, g.2]) ++ [h.finalBytecodeValue]) := by
  simp only [batchingStream, List.append_assoc]

theorem length_rounds_flat (rounds : List (E × E)) :
    (rounds.flatMap fun g ↦ [g.1, g.2]).length = 2 * rounds.length := by
  induction rounds with
  | nil => rfl
  | cons g rest ih => simp [ih]; ring

/-- The run of the batching from its seed, with the count's and the children's cells read. -/
theorem runD_batchOf (check : DeferredClaim → Prop) {bytecode : List K} {cs : List ChildClaims}
    (rest : List E) :
    runD (nodeBatchingProgram check bytecode cs)
        ⟨⟨batchSeed, []⟩, cellsBeforeChallenge cs ++ rest, [], []⟩ =
      runD (batchingAfterChildren check bytecode cs) ⟨batchSponge cs, rest, [], []⟩ := by
  rw [nodeBatchingProgram, runD_bind_of_runsTo (runsTo_readN' _ (cellsBeforeChallenge cs) rfl),
    ← List.nil_append rest, runD_bind_of_runsTo (runsTo_require rfl _)]
  rfl

/-- The tail of the batching: the final value read, the check, acceptance. -/
theorem runD_tail_accepts {c : E → Prop} {dc : DecidablePred c} {sp : Sponge} {zs : List E}
    {s : VerifierProgramState} (h : runD (VerifierProgram.readScalar >>= fun bv ↦
        @VerifierProgram.require (c bv) (dc bv) >>= fun _ ↦
      (pure true : VerifierProgram Bool)) ⟨sp, zs, [], []⟩ = some (true, s)) (hs : s.stream = []) :
    zs.length = 1 := by
  rcases zs with _ | ⟨v, ws⟩
  · exact absurd h (by simp [VerifierProgram.readScalar, VerifierProgram.bind_eq, VerifierProgram.bind, runD, Compile.runWithHash])
  · have e := runD_bind_of_runsTo (f := fun bv ↦ @VerifierProgram.require (c bv) (dc bv) >>= fun _ ↦
      (pure true : VerifierProgram Bool)) (runsTo_readE sp v) ws [] []
    simp only [List.singleton_append] at e
    rw [e, @runD_require_true (c v) (dc v)] at h
    split_ifs at h with hc
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      have hw : ws = [] := by rw [← h.2] at hs; exact hs
      rw [hw]
      rfl

/-- **An accepting run reads the hints' rounds as the program's**: the hints have
`log₂ |bytecode|` rounds. -/
theorem rounds_length_of_accepts {check : DeferredClaim → Prop} {bytecode : List K}
    {cs : List ChildClaims} {h : BatchingHints}
    (hacc : Id.run (runBatchingWithHash (m := Id) keccak256 keccakF1600 (nodeBatchingProgram check bytecode cs)
      ⟨batchingStream cs h, []⟩) = true) :
    h.sumcheckMessages.length = Nat.log2 bytecode.length := by
  change (match runD (nodeBatchingProgram check bytecode cs)
      ⟨⟨batchSeed, []⟩, batchingStream cs h, [], []⟩ with
    | some (true, s) => s.stream.isEmpty && s.openings.isEmpty
    | _ => false) = true at hacc
  rw [batchStream_eq, runD_batchOf check, batchingAfterChildren,
    ← List.nil_append (List.flatMap _ _ ++ _), runD_bind_of_runsTo (runsTo_sampleE _)] at hacc
  generalize hR : runD (sumcheckRoundsProgram _ _ >>= _) _ = R at hacc
  rcases R with _ | ⟨_ | _, s⟩
  · simp at hacc
  · simp at hacc
  · simp only [Bool.and_eq_true, List.isEmpty_iff] at hacc
    obtain ⟨hle, x, sp', hx⟩ := runD_roundsProg_bind _ _ _ _ _ _ _ hR
    have h1 := runD_tail_accepts hx hacc.1
    simp only [List.length_drop, List.length_append, length_rounds_flat, List.length_singleton]
      at h1 hle
    omega

/-- **With the program's rounds, a node's batching is `Node.batch`**: for hints of
`log₂ |bytecode|` rounds, the program accepts the stream exactly where `batch`
defers `d`. -/
theorem batchRun_iff_of_rounds {bytecode : List K} {cs : List ChildClaims} {h : BatchingHints}
    {d : DeferredClaim}
    (hr : h.sumcheckMessages.length = Nat.log2 bytecode.length) :
    Id.run (runBatchingWithHash (m := Id) keccak256 keccakF1600 (nodeBatchingProgram (· = d) bytecode cs)
      ⟨batchingStream cs h, []⟩) = true ↔ batch cs h = some d := by
  change (match runD (nodeBatchingProgram (· = d) bytecode cs)
      ⟨⟨batchSeed, []⟩, batchingStream cs h, [], []⟩ with
    | some (true, s) => s.stream.isEmpty && s.openings.isEmpty
    | _ => false) = true ↔ _
  rw [batchStream_eq, runD_batchOf _, batchingAfterChildren,
    ← List.nil_append (List.flatMap _ _ ++ _),
    runD_bind_of_runsTo (runsTo_sampleE _),
    runD_bind_of_runsTo (runsTo_roundsProg h.sumcheckMessages _ _ hr),
    ← List.append_nil [h.finalBytecodeValue],
    runD_bind_of_runsTo (runsTo_readE _ _), runD_require_true, batch_eq']
  simp only [lambdasB, claimB, spB, sqL]
  split_ifs <;> simp_all

/-- `batch` defers a claim at a point of as many coordinates as the hints have rounds. -/
theorem batch_point_length {cs : List ChildClaims} {h : BatchingHints} {d : DeferredClaim}
    (hb : batch cs h = some d) : d.bytecodePoint.length = h.sumcheckMessages.length := by
  have e := hb
  rw [batch_eq'] at e
  split_ifs at e
  have := congrArg (fun c : DeferredClaim ↦ c.bytecodePoint.length) (Option.some.inj e)
  simp only [rsRun_length] at this
  exact this.symm

/-- **An accepting batching defers a claim of the bytecode's shape**: the sumcheck's
`log₂ |bytecode|` challenges. -/
theorem shape_of_batchRun {bytecode : List K} {cs : List ChildClaims} {h : BatchingHints}
    {d : DeferredClaim}
    (hacc : Id.run (runBatchingWithHash (m := Id) keccak256 keccakF1600
      (nodeBatchingProgram (· = d) bytecode cs) ⟨batchingStream cs h, []⟩) = true) :
    d.HasBytecodeShape bytecode := by
  have hr := rounds_length_of_accepts hacc
  rw [DeferredClaim.HasBytecodeShape, batch_point_length ((batchRun_iff_of_rounds hr).mp hacc), hr]

/-- **A node's batching is `Node.batch`**: for a deferred claim of the bytecode's shape, the
program accepts the stream exactly where `batch` defers that claim. -/
theorem batchRun_batchOf_iff {bytecode : List K} {cs : List ChildClaims} {h : BatchingHints}
    {d : DeferredClaim} (hd : d.HasBytecodeShape bytecode) :
    Id.run (runBatchingWithHash (m := Id) keccak256 keccakF1600 (nodeBatchingProgram (· = d) bytecode cs)
      ⟨batchingStream cs h, []⟩) = true ↔ batch cs h = some d := by
  constructor
  · intro hacc
    exact (batchRun_iff_of_rounds (rounds_length_of_accepts hacc)).mp hacc
  · intro hb
    have hr : h.sumcheckMessages.length = Nat.log2 bytecode.length := by
      rw [← batch_point_length hb]
      exact hd
    exact (batchRun_iff_of_rounds hr).mpr hb

/-! ## `NodeRelation` with the guest program's transcript -/

/-- `NodeRelation` with the batching as the guest program's transcript (`Node.batch`). -/
def _root_.LeanVM.Node.NodeRelB (bytecode : List K) (seed : Digest) (s : NodeStatement)
    (w : NodeWitness) : Prop :=
  s.deferredClaim.HasBytecodeShape bytecode ∧
  (∀ c ∈ w.children, c.statement.deferredClaim.HasBytecodeShape bytecode ∧
    verifyDeferred bytecode seed (statementDigest seed c.statement) c.freshClaim c.proof = true) ∧
  SignatureClaimsHeld s w ∧
  (match w.daMatrix with
    | some (c, m) => s.claims.daDigest = daClaimDigest c ∧ m.Opens c.daRoot c.membershipChallenge
    | none => s.claims.daDigest = zeroDigest ∨ ∃ c ∈ w.children, c.statement.claims.daDigest = s.claims.daDigest) ∧
  if w.children = [] then s.deferredClaim.HasZeroPoint bytecode
  else batch (w.children.map fun c ↦
    ⟨statementDigest seed c.statement, c.freshClaim, c.statement.deferredClaim⟩) w.batchingHints = some s.deferredClaim

/-- **The batched deferred claim has the bytecode's shape**: the zero point's, or the batching
sumcheck's challenges. -/
theorem _root_.LeanVM.Node.DeferredClaimBatched.hasBytecodeShape {bytecode : List K}
    {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    (hb : DeferredClaimBatched bytecode seed s w) : s.deferredClaim.HasBytecodeShape bytecode := by
  unfold DeferredClaimBatched at hb
  split at hb
  · unfold DeferredClaim.HasZeroPoint at hb
    rw [DeferredClaim.HasBytecodeShape, hb, List.length_replicate]
  · dsimp only at hb
    rw [LeanVM.Guest.Batch.runBatching_deployed] at hb
    exact shape_of_batchRun hb

/-- **A node's deferred claim has the bytecode's shape**, under `NodeRelation`. -/
theorem _root_.LeanVM.Node.NodeRelation.hasBytecodeShape {bytecode : List K} {seed : Digest}
    {s : NodeStatement} {w : NodeWitness} (h : NodeRelation bytecode seed s w) :
    s.deferredClaim.HasBytecodeShape bytecode :=
  DeferredClaimBatched.hasBytecodeShape h.2.2.2

/-- **`NodeRelation` is `NodeRelB`**: the statement's batching program accepts the node's stream
exactly where the guest program's transcript defers the node's claim. -/
theorem _root_.LeanVM.Node.nodeRel_iff {bytecode : List K} {seed : Digest} {s : NodeStatement}
    {w : NodeWitness} : NodeRelation bytecode seed s w ↔ NodeRelB bytecode seed s w := by
  have key : s.deferredClaim.HasBytecodeShape bytecode →
      (DeferredClaimBatched bytecode seed s w ↔
        if w.children = [] then s.deferredClaim.HasZeroPoint bytecode
        else batch (w.children.map fun c ↦
          ⟨statementDigest seed c.statement, c.freshClaim, c.statement.deferredClaim⟩)
            w.batchingHints = some s.deferredClaim) := by
    intro h1
    unfold DeferredClaimBatched
    split
    · exact Iff.rfl
    · dsimp only
      rw [LeanVM.Guest.Batch.runBatching_deployed]
      exact batchRun_batchOf_iff (h := w.batchingHints) h1
  constructor
  · intro h
    have h1 := h.hasBytecodeShape
    unfold NodeRelation DaDigestHeld at h
    unfold NodeRelB
    obtain ⟨hsig, hda, h2, hb⟩ := h
    exact ⟨h1, h2, hsig, hda, (key h1).mp hb⟩
  · unfold NodeRelation NodeRelB DaDigestHeld
    rintro ⟨h1, h2, hsig, hda, hb⟩
    exact ⟨hsig, hda, h2, (key h1).mpr hb⟩

end
end LeanVM.Guest.Batch
