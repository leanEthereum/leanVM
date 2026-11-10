import Rv64Verifier.Model.Walk

/-!
# `walk`'s mirror in the machine's shape

The compiled `walk` runs `walkRust`'s steps in its order. Where a step's shape differs, the lemmas
here restate the mirror's step as the machine runs it:

`KeepsProof m`: `m` leaves the transcript's proof alone, as every method does; `walk`'s run keeps
the proof the memory holds through each call (`Tracks.bind`).

* `walkRust` split where the machine's stages meet: the announced sizes (`announcedRust_eq`,
  `announcedTail`), everything after them (`bodyRest`), `finish` (`finishRust`),
  `walkRust_announced`;
* the stack's root: the machine calls `next_scalars(2)`, then `Digest::from_halves`; `TM.commit`
  reads both scalars in one step and records the root as a ghost (`commit_run`).
-/

namespace Rv64Verifier.Proofs.Walk
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier Rv64Verifier.Model

/-- `TM.commit` is `next_scalars(2)` followed by `Digest::from_halves`, the root appended to the
ghost roots. -/
theorem commit_run (height width : ℕ) (T : TState) :
    (TM.commit height width).run T =
      ((TM.nextScalars 2).run T).bind fun p ↦
        (digestFromHalves (p.1.getD 0 0, p.1.getD 1 0)).map fun root ↦
          (root, { p.2 with roots := T.roots ++ [(root, height, width)] }) := by
  simp only [TM.commit, TM.nextScalars, TM.nextScalar, StateT.run, bind, StateT.bind, pure,
    StateT.pure]
  rcases h0 : T.proof.stream[T.streamOffset]? with _ | x0
  · simp
  rcases h1 : T.proof.stream[T.streamOffset + 1]? with _ | x1
  · simp [h1]
  rcases hd : digestFromHalves (x0, x1) with _ | root
  · simp [h1, hd]
  · simp [h1, hd]

/-! ## `walkRust` in stages -/

/-- `announcedRust` past its high-limb check. -/
def announcedTail (bc : BytecodeRust) (announced : List E) :
    TM (LayoutMirror.LayoutRust × List (BitVec 64) × BitVec 64) := do
  let logMemory := ((announced.getD 0 0).limb 0).toBitVec
  let tableRows := ((announced.drop 1).take LayoutMirror.nTablesRust).map fun value ↦
    (value.limb 0).toBitVec
  let logInverseRate := ((announced.getD (1 + LayoutMirror.nTablesRust) 0).limb 0).toBitVec
  TM.require (1#64 ≤ logInverseRate ∧ logInverseRate ≤ 4#64)
  let layout ← TM.ofOption
    (LayoutMirror.buildLayoutRust (BitVec.ofNat 64 bc.len) logMemory tableRows)
  TM.require (Pcs.minStackedLog ≤ layout.stackLog ∧ layout.stackLog ≤ Pcs.maxStackedLog)
  pure (layout, tableRows, logInverseRate)

theorem announcedRust_eq (bc : BytecodeRust) :
    announcedRust bc = TM.nextScalars (2 + LayoutMirror.nTablesRust) >>= fun announced ↦
      TM.require (announced.all fun value ↦ value.limb 1 = 0 ∧ value.limb 2 = 0) >>= fun _ ↦
        announcedTail bc announced := rfl

/-- `walkBodyRust` after the announced sizes and the layout. -/
def bodyRest (bc : BytecodeRust) (publicInput : List (BitVec 8)) :
    LayoutMirror.LayoutRust × List (BitVec 64) × BitVec 64 → TM SummaryRust
  | (layout, tableRows, logInverseRate) => do
    let _root ← TM.commit (stackShape layout.stackLog logInverseRate.toNat).1
      (stackShape layout.stackLog logInverseRate.toNat).2
    let bus ← verifyBusBalanceM (evaluateRust bc) (layout.toSpec [])
    let evaluations ← tablePhaseRust layout bus
    let claims := bus.claims ++ tableClaimsRust evaluations
    let publicClaims ← publicInputRust layout publicInput
    let claims := claims ++ publicClaims
    let (openings, keccakStart, keccakEnd) ← keccakPhaseRust layout evaluations
    let claims := claims ++
      openings.outputs.toList.map fun pw ↦ (⟨LayoutMirror.qkeccakRust, pw.1, pw.2⟩ : ColumnClaim)
    let (ringTarget, ringWeight) ← Pcs.ringSwitchRust openings.inputs.1 openings.inputs.2
    Pcs.verifyStackedOpeningRust layout.stackLog logInverseRate.toNat
      (⟨.placedRing layout.qkeccak ringWeight, ringTarget⟩ :: claims.filterMap (onStackRust layout))
    pure ⟨layout.logMemory, tableRows, logInverseRate.toNat, bus.bytecodePoint,
      (keccakStart, keccakEnd)⟩

/-- `transcript.finish()?; Ok(summary)`. -/
def finishRust (summary : SummaryRust) : TM SummaryRust := do
  TM.finish
  pure summary

theorem walkRust_eq (bc : BytecodeRust) (publicInput : List (BitVec 8)) :
    walkRust bc publicInput = (announcedRust bc >>= bodyRest bc publicInput) >>= finishRust :=
  rfl

theorem walkRust_announced (bc : BytecodeRust) (publicInput : List (BitVec 8)) :
    walkRust bc publicInput = TM.nextScalars (2 + LayoutMirror.nTablesRust) >>= fun announced ↦
      ((TM.require (announced.all fun value ↦ value.limb 1 = 0 ∧ value.limb 2 = 0) >>= fun _ ↦
        announcedTail bc announced) >>= bodyRest bc publicInput) >>= finishRust := by
  rw [walkRust_eq, announcedRust_eq]
  simp only [bind_assoc]

/-! ## The proof is never changed -/

/-- `m` leaves the transcript's proof as it was. -/
def KeepsProof {α : Type} (m : TM α) : Prop :=
  ∀ {T : TState} {x : α} {T' : TState}, m.run T = some (x, T') → T'.proof = T.proof

namespace KeepsProof
variable {α β : Type}

theorem pure (a : α) : KeepsProof (Pure.pure a : TM α) := fun h ↦ by
  cases h
  rfl

theorem bind {m : TM α} {f : α → TM β} (hm : KeepsProof m) (hf : ∀ a, KeepsProof (f a)) :
    KeepsProof (m >>= f) := fun {T} {x} {T'} h ↦ by
  rw [StateT.run_bind] at h
  rcases e : m.run T with _ | ⟨a, T₁⟩
  · rw [e] at h
    cases h
  · rw [e] at h
    exact (hf a h).trans (hm e)

theorem fail : KeepsProof (TM.fail : TM α) := fun h ↦ by cases h

theorem ofOption (o : Option α) : KeepsProof (TM.ofOption o) := by
  cases o
  · exact fail
  · exact pure _

theorem require (c : Prop) [Decidable c] : KeepsProof (TM.require c) := fun {T} {x} {T'} h ↦ by
  simp only [TM.require, StateT.run] at h
  split_ifs at h
  cases h
  rfl

theorem streamPosition : KeepsProof TM.streamPosition := fun h ↦ by
  cases h
  rfl

theorem finish : KeepsProof TM.finish := fun {T} {x} {T'} h ↦ by
  simp only [TM.finish, StateT.run] at h
  split_ifs at h
  cases h
  rfl

theorem nextScalar : KeepsProof TM.nextScalar := fun {T} {x} {T'} h ↦ by
  simp only [TM.nextScalar, StateT.run] at h
  split at h
  · cases h
    rfl
  · cases h

theorem sample : KeepsProof TM.sample := fun h ↦ by
  cases h
  rfl

theorem nextScalars : ∀ n, KeepsProof (TM.nextScalars n)
  | 0 => pure _
  | n + 1 => bind nextScalar fun _ ↦ bind (nextScalars n) fun _ ↦ pure _

theorem samples : ∀ n, KeepsProof (TM.samples n)
  | 0 => pure _
  | n + 1 => bind sample fun _ ↦ bind (samples n) fun _ ↦ pure _

theorem commit (height width : ℕ) : KeepsProof (TM.commit height width) :=
  fun {T} {x} {T'} h ↦ by
    rw [commit_run] at h
    rcases e : (TM.nextScalars 2).run T with _ | ⟨xs, T₁⟩
    · rw [e] at h
      cases h
    · rw [e] at h
      simp only [Option.bind_some, Option.map_eq_some_iff] at h
      obtain ⟨root, -, h⟩ := h
      cases h
      exact (nextScalars 2 e : T₁.proof = T.proof)

end KeepsProof

end Rv64Verifier.Proofs.Walk
