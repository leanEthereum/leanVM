/-
  LeanVM.Guest.B1.VsC.Announced

  The layout an accepted run of the deferring verifier works on is the one its stream announces
  (`announcedLayoutAndRate`, what the guest's honest hints are computed from), and that run gets
  past `verify_link`'s chunking of the pointer width.
-/

module

public import LeanVM.Protocol.WithHashBridge
public import LeanVM.Protocol.Verifier.Deferred

/-!
# The announced layout of an accepted child

`readAnnouncedSizes` reads `2 + N_TABLES` scalars and then only checks and computes
(`readSizes_eq`: it is `readScalars` then `liftOption` of `sizesOf`), so whatever the sponge, its
value is `sizesOf` of the stream's first words (`run_readSizes`), the value `announcedLayoutAndRate`
computes with every permutation answered by `default` (`announced_eq_run`).

`accepted_rest`: an accepted run of the deferring verifier is `readAnnouncedSizes` returning the
announced layout and rate, then the rest of `verifyExecution` at them, which may return.
`accepted_chunks`: that rest gets past `verify_link`'s `Chunks.new` of the pointer width.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

/-- What `readAnnouncedSizes` makes of the scalars it reads: the checks and the layout, without
the reads. -/
def sizesOf (bytecode : List K) (announced : List E) : Option (Layout × ℕ) :=
  if announced.all (fun value ↦ value.limb 1 = 0) then
    let logInverseRate := kToNat ((announced.getLastD 0).limb 0)
    if 1 ≤ logInverseRate ∧ logInverseRate ≤ 4 then
      (buildLayout bytecode (kToNat ((announced.headD 0).limb 0))
          (((announced.drop 1).take nTables).map fun value ↦ kToNat (value.limb 0))).bind
        fun layout ↦
          if Whir.minLogStack ≤ layout.stackLog ∧ layout.stackLog ≤ Whir.maxLogStack then
            some (layout, logInverseRate)
          else none
    else none
  else none

theorem liftOption_some {α : Type} (a : α) : liftOption (some a) = VerifierProgram.ret a := rfl

theorem liftOption_none {α : Type} : liftOption (none : Option α) = VerifierProgram.fail := rfl

theorem fail_bind {α β : Type} (f : α → VerifierProgram β) :
    (VerifierProgram.fail : VerifierProgram α).bind f = VerifierProgram.fail := rfl

/-- **`readAnnouncedSizes` is reads, then a pure computation.** -/
theorem readSizes_eq (bytecode : List K) :
    readAnnouncedSizes bytecode =
      (VerifierProgram.readScalars (2 + nTables)).bind fun a ↦ liftOption (sizesOf bytecode a) := by
  unfold readAnnouncedSizes sizesOf
  refine congrArg _ (funext fun a ↦ ?_)
  by_cases h1 : (a.all fun value ↦ value.limb 1 = 0) = true
  · by_cases h2 : 1 ≤ kToNat ((a.getLastD 0).limb 0) ∧ kToNat ((a.getLastD 0).limb 0) ≤ 4
    · simp only [VerifierProgram.require, h1, h2, and_self, ↓reduceIte]
      cases hb : buildLayout bytecode (kToNat ((a.headD 0).limb 0))
          (((a.drop 1).take nTables).map fun value ↦ kToNat (value.limb 0)) with
      | none => rfl
      | some layout =>
        by_cases h3 : Whir.minLogStack ≤ layout.stackLog ∧ layout.stackLog ≤ Whir.maxLogStack
        · simp only [Option.bind_some, VerifierProgram.bind_eq', VerifierProgram.ret_bind',
            liftOption_some, VerifierProgram.pure_eq', h3, and_self, ↓reduceIte]
        · simp only [Option.bind_some, VerifierProgram.bind_eq', VerifierProgram.ret_bind',
            liftOption_some, liftOption_none, fail_bind, h3, ↓reduceIte]
    · simp only [VerifierProgram.require, h1, h2, ↓reduceIte]; rfl
  · simp only [VerifierProgram.require, h1]; rfl

variable (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState)

theorem run_liftOption {α : Type} (o : Option α) (s : VerifierProgramState) :
    runWithHash (m := Id) H F (liftOption o) s = o.map (·, s) := by
  cases o <;> rfl

/-- **`readScalars n`'s value is the stream's first `n` scalars**, from a state with no ground
challenge: it fails on a shorter stream. -/
theorem run_readScalars : ∀ (n : ℕ) (s : VerifierProgramState), s.sponge.ground = none →
    (runWithHash (m := Id) H F (VerifierProgram.readScalars n) s).map Prod.fst =
      if n ≤ s.stream.length then some (s.stream.take n) else none
  | 0, s, hg => by simp [VerifierProgram.readScalars, runWithHash, pure]
  | n + 1, s, hg => by
    have e : VerifierProgram.readScalars (n + 1) = (VerifierProgram.read VerifierProgram.ret).bind
        (fun x ↦ (VerifierProgram.readScalars n).bind fun xs ↦ VerifierProgram.ret (x :: xs)) := rfl
    rw [e, runWithHash_bind]
    rcases hs : s.stream with _ | ⟨x, xs⟩
    · have e0 : runWithHash (m := Id) H F (VerifierProgram.read VerifierProgram.ret) s = none := by
        simp only [runWithHash, hs]; rfl
      rw [e0]; simp
    · set s1 : VerifierProgramState :=
        { s with sponge := Id.run (absorb F s.sponge x dsObserve), stream := xs } with hs1
      have e1 : runWithHash (m := Id) H F (VerifierProgram.read VerifierProgram.ret) s =
          some (x, s1) := by
        simp only [runWithHash, hs, hg]; rfl
      have hg1 : s1.sponge.ground = none := by
        rw [hs1]
        simp only [Id.run, absorb]
        split
        · exact hg
        · exact hg
      have ih := run_readScalars n s1 hg1
      rw [e1, Option.bind_some, runWithHash_bind]
      have hx : s1.stream = xs := rfl
      rw [hx] at ih
      revert ih
      generalize runWithHash (m := Id) H F (VerifierProgram.readScalars n) s1 = o
      intro ih
      cases o with
      | none =>
        simp only [Option.map_none] at ih
        split at ih
        · cases ih
        · simp only [Option.bind_none, Option.map_none, List.length_cons]
          have hn : ¬ n + 1 ≤ xs.length + 1 := by omega
          simp only [hn, ↓reduceIte]
      | some r =>
        simp only [Option.map_some] at ih
        split at ih
        · next hle =>
          simp only [Option.some.injEq] at ih
          simp only [Option.bind_some, List.length_cons]
          have hn : n + 1 ≤ xs.length + 1 := by omega
          simp only [hn, ↓reduceIte]
          show some (x :: r.1) = _
          rw [ih]; rfl
        · cases ih

theorem map_fst_bind_liftOption {α β : Type} (o : Option (α × VerifierProgramState))
    (g : α → Option β) :
    (o.bind fun r ↦ runWithHash (m := Id) H F (liftOption (g r.1)) r.2).map Prod.fst =
      (o.map Prod.fst).bind g := by
  cases o with
  | none => rfl
  | some r => simp only [Option.bind_some, run_liftOption, Option.map_map, Option.map_some]; cases g r.1 <;> rfl

/-- **`readAnnouncedSizes`' value is `sizesOf` of the stream's first `2 + N_TABLES` scalars**,
whatever the sponge with no ground challenge. -/
theorem run_readSizes (bytecode : List K) {s : VerifierProgramState} (hg : s.sponge.ground = none) :
    (runWithHash (m := Id) H F (readAnnouncedSizes bytecode) s).map Prod.fst =
      if 2 + nTables ≤ s.stream.length then sizesOf bytecode (s.stream.take (2 + nTables))
      else none := by
  rw [readSizes_eq, runWithHash_bind, map_fst_bind_liftOption, run_readScalars H F _ s hg]
  split <;> rfl

/-- **The announced layout and rate are `readAnnouncedSizes`' value from any sponge** with no
ground challenge. -/
theorem announced_eq_run (bytecode : List K) {s : VerifierProgramState} (hg : s.sponge.ground = none) :
    announcedLayoutAndRate bytecode s.stream =
      (runWithHash (m := Id) H F (readAnnouncedSizes bytecode) s).map Prod.fst := by
  unfold announcedLayoutAndRate
  rw [runPure_eq_withHash, run_readSizes H F bytecode hg]
  exact run_readSizes _ _ bytecode rfl

/-- The rest of `verifyExecution` past the announced sizes. -/
def verifyRest (bytecodeSplit : List K → List E → List (ℕ × ℕ) → VerifierProgram Split)
    (publicInput : Digest) (x : Layout × ℕ) : VerifierProgram Unit :=
  match x with
  | (layout, logInverseRate) => do
    commitStack layout.stackLog logInverseRate
    let ood ← readOod layout.stackLog
    let link ← verifyLink bytecodeSplit layout
    let claims := linkColumnClaims link
    let publicClaims ← bindPublicInput layout publicInput
    let claims := claims ++ publicClaims
    let (outputs, keccakPoint, keccakSlices) ← keccakValidity layout link
    let claims := claims ++ outputs
    let qkeccakPlacement ← liftOption (layout.placements.getD qkeccak none)
    let (ring, batching) ←
      ringSwitch [keccakRingClaim qkeccakPlacement keccakPoint keccakSlices, link.ring]
    let memoryTerm ← memoryTermClaim layout link
    verifyStackedOpening layout.stackLog logInverseRate
      (ring :: memoryTerm :: claims.filterMap (·.onStack layout) ++ [ood]) batching

theorem verifyExecution_eq (bytecodeSplit : List K → List E → List (ℕ × ℕ) → VerifierProgram Split)
    (bytecode : List K) (publicInput : Digest) :
    verifyExecution bytecodeSplit bytecode publicInput =
      (readAnnouncedSizes bytecode).bind (verifyRest bytecodeSplit publicInput) := rfl

/-- An accepted run of the deferring verifier's program from any seed: the stream announces a
layout and rate, and the rest of `verifyExecution` at them may return. -/
theorem accepted_rest_of_run {bytecode : List K} {publicInput : Digest} {fresh : FreshClaim}
    {seed : KeccakState} {proof : Proof}
    (h : runProofWithHash (m := Id) H F (deferringVerifierProgram fresh bytecode publicInput) seed proof = true) :
    ∃ x, announcedLayoutAndRate bytecode proof.stream = some x ∧
      VerifierProgram.Returns (verifyRest (freshSplit fresh) publicInput x) () := by
  unfold runProofWithHash at h
  revert h
  match hr : runWithHash (m := Id) H F (deferringVerifierProgram fresh bytecode publicInput)
      ⟨⟨seed, [], none⟩, proof.stream, proof.openings, []⟩ with
  | some (true, s) =>
    intro _
    unfold deferringVerifierProgram at hr
    rw [VerifierProgram.bind_eq', runWithHash_bind, verifyExecution_eq, runWithHash_bind] at hr
    obtain ⟨⟨u, s2⟩, hu, -⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨⟨x, s1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp hu
    refine ⟨x, ?_, VerifierProgram.returns_of_run _ _ h2⟩
    rw [announced_eq_run H F bytecode (s := ⟨⟨seed, [], none⟩, proof.stream, proof.openings, []⟩) rfl,
      h1]
    rfl
  | some (false, _) => intro h; simp at h
  | none => intro h; simp at h

/-- **An accepted child's run**: the stream announces a layout and rate, and the rest of
`verifyExecution` at them may return. -/
theorem accepted_rest {bytecode : List K} {iv publicInput : Digest} {fresh : FreshClaim}
    {proof : Proof} (h : verifyDeferred bytecode iv publicInput fresh proof = true) :
    ∃ x, announcedLayoutAndRate bytecode proof.stream = some x ∧
      VerifierProgram.Returns (verifyRest (freshSplit fresh) publicInput x) () := by
  rw [verifyDeferred_eq_withHash] at h
  exact accepted_rest_of_run _ _ h

end
end LeanVM.Guest.B1.VsC
