module

public import LeanVM.Protocol.Extraction.Extractor
public import LeanVM.Protocol.Verifier.Phases

/-!
# The stack's root, without the verifier's free monad

The extractor starts from `afterRoot` (`Extraction/Extractor.lean`): the verifier's steps 1 and 2,
`announceSizesAndRoot`, a `VerifierProgram` run by `runPure` (every permutation answered by
`default`).
`VerifierProgram`'s constructors hold continuations
(`read : (E → VerifierProgram α) → VerifierProgram α`, …), which the cost compiler does not take.
Here the same steps are plain state-passing functions in `Option`:

* `absorbPure`: the sponge's `absorb` with every permutation `default`; `readPure n`: read and
  absorb `n` scalars (`runPure_readScalars`); `commitPure`: read a root;
* `readSizesPure`, `commitStackPure`: `readAnnouncedSizes` (`runPure_readSizes`) and
  `commitStack`.

The lighter layout: the extractor reads of the layout only `logMemory`, `logBytecode`,
`placements`, `stackLog` and `tableLogHeights`. `buildLayoutLite` computes only these (no bus
blocks, no forms, no bytecode copy), and is `buildLayout` followed by `layoutLite`
(`buildLayoutLite_eq`); `afterRootLite` is `afterRoot` with its layout so cut.

The run's algebra: `runPure_bind` (a sequence runs as its first program, then the continuation),
`runPure_readScalars_bind`, `runPure_liftOption`.
-/

namespace LeanVM.Extraction.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Parameters.Whir LeanVM.Protocol.KeccakHash LeanVM.Extraction

public section

/-! ## The run's algebra -/

/-- `runPure` without `Id.run`: the run with every permutation answered by `default`. -/
abbrev runDefault {α : Type} (p : VerifierProgram α) (s : VerifierProgramState) : Option (α ×
    VerifierProgramState) :=
  Compile.run (m := Id) (fun _ ↦ default) p s

/-- A sequence runs as its first program, then the continuation on the first's value. -/
theorem runDefault_bind {α β : Type} (p : VerifierProgram α) (f : α → VerifierProgram β) (s :
    VerifierProgramState) :
    runDefault (p.bind f) s = (runDefault p s).bind fun r ↦ runDefault (f r.1) r.2 := by
  induction p generalizing s with
  | ret a => rfl
  | fail => rfl
  | read k ih =>
    simp only [runDefault, VerifierProgram.bind, Compile.run]
    split
    · exact ih _ _
    · rfl
  | sample k ih => exact ih _ _
  | grind b k ih =>
    simp only [runDefault, VerifierProgram.bind, Compile.run]
    split
    · show (if powOk b _ = true then _ else none) = Option.bind (if powOk b _ = true then _ else none) _
      split
      · exact ih _
      · rfl
    · rfl
  | commit h w k ih =>
    simp only [runDefault, VerifierProgram.bind, Compile.run]
    split
    · exact ih _
    · rfl
  | query i ps k ih =>
    simp only [runDefault, VerifierProgram.bind, Compile.run]
    split
    · simp only [bind]
      split
      · exact ih _ _
      · rfl
    · rfl

/-- **`runPure` of a sequence**: the first program's run, then the continuation's. -/
theorem runPure_bind {α β : Type} (p : VerifierProgram α) (f : α → VerifierProgram β) (s :
    VerifierProgramState) :
    runPure (p >>= f) s = (runPure p s).bind fun r ↦ runPure (f r.1) r.2 :=
  runDefault_bind p f s

theorem runPure_bind_of_some {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} {s s'
    : VerifierProgramState}
    {a : α} (h : runPure p s = some (a, s')) : runPure (p >>= f) s = runPure (f a) s' := by
  have := runPure_bind p f s
  rw [h] at this
  exact this

theorem runPure_liftOption {α : Type} (o : Option α) (s : VerifierProgramState) :
    runPure (liftOption o) s = o.map fun a ↦ (a, s) := by
  cases o <;> rfl

/-! ## The sponge and the reads -/

/-- `absorb` with every permutation answered by `default`: a full queue is replaced by the
default state with an empty queue, then the scalar joins the queue. -/
@[expose] def absorbPure (sp : Compile.Sponge) (x : E) (tag : ℕ) : Compile.Sponge :=
  let sp : Compile.Sponge := if sp.pending.length = rateScalars then ⟨default, [], sp.ground⟩ else sp
  { sp with pending := sp.pending ++ [(x, tag)] }

/-- Read `n` prover scalars, each absorbed with `dsObserve` (`VerifierProgram.readScalars`). -/
@[expose] def readPure : ℕ → VerifierProgramState → Option (List E × VerifierProgramState)
  | 0, s => some ([], s)
  | n + 1, s =>
    match s.stream, s.sponge.ground with
    | x :: xs, none =>
      (readPure n { s with sponge := absorbPure s.sponge x dsObserve, stream := xs }).map
        fun r ↦ (x :: r.1, r.2)
    | _, _ => none

/-- **`readScalars`, run**, is `readPure`. -/
theorem runPure_readScalars (n : ℕ) (s : VerifierProgramState) :
    runPure (VerifierProgram.readScalars n) s = readPure n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rcases s with ⟨⟨st0, pend, gr⟩, _ | ⟨x, xs⟩, os, roots⟩
    · rfl
    · cases gr with
      | some c => rfl
      | none =>
        have h1 : runPure VerifierProgram.readScalar ⟨⟨st0, pend, none⟩, x :: xs, os, roots⟩ =
            some (x, ⟨absorbPure ⟨st0, pend, none⟩ x dsObserve, xs, os, roots⟩) := by
          simp only [runPure, VerifierProgram.readScalar, Compile.run, Compile.absorb,
            Compile.duplex, absorbPure]
          split <;> rfl
        show runPure (VerifierProgram.readScalar >>= fun y ↦ VerifierProgram.readScalars n >>= fun ys
            ↦ pure (y :: ys)) ⟨⟨st0, pend, none⟩, x :: xs, os, roots⟩ = _
        rw [runPure_bind_of_some h1, runPure_bind, ih]
        show _ = (readPure n ⟨absorbPure ⟨st0, pend, none⟩ x dsObserve, xs, os, roots⟩).map
          fun r ↦ (x :: r.1, r.2)
        cases readPure n ⟨absorbPure ⟨st0, pend, none⟩ x dsObserve, xs, os, roots⟩ <;> rfl

theorem runPure_readScalars_bind {β : Type} (n : ℕ) (f : List E → VerifierProgram β) (s :
    VerifierProgramState) :
    runPure (VerifierProgram.readScalars n >>= f) s = (readPure n s).bind fun r ↦ runPure (f r.1)
        r.2 := by
  rw [runPure_bind, runPure_readScalars]

/-- Read a root (`VerifierProgram.readCommitment height width`): two scalars, absorbed, which must encode a
digest; the root is recorded with its shape. -/
@[expose] def commitPure (height width : ℕ) (s : VerifierProgramState) : Option (Unit ×
    VerifierProgramState) :=
  match s.stream, s.sponge.ground with
  | x0 :: x1 :: xs, none =>
    some ((), { s with
      sponge := absorbPure (absorbPure s.sponge x0 dsObserve) x1 dsObserve
      stream := xs
      roots := s.roots ++ [(digestFromHalves (x0, x1), height, width)] })
  | _, _ => none

/-! ## Steps 1 and 2 -/

/-- `readAnnouncedSizes bytecode` (`Statement/LeanVmVerifier.lean`), run: the announced sizes, read and
checked (`sizesOf`), and the layout they give. -/
@[expose] def readSizesPure (bytecode : List K) (s : VerifierProgramState) :
    Option ((Layout × ℕ) × VerifierProgramState) :=
  (readPure (2 + tables.length) s).bind fun r ↦ (sizesOf bytecode r.1).map fun x ↦ (x, r.2)

theorem runPure_readSizes (bytecode : List K) (s : VerifierProgramState) :
    runPure (readAnnouncedSizes bytecode) s = readSizesPure bytecode s := by
  simp only [readAnnouncedSizes_eq, readSizesPure, runPure_readScalars_bind, runPure_liftOption]

/-- `commitStack logN logInvRate`, run: the stack's root, at the shape of the ladder's first
level. -/
@[expose] def commitStackPure (logN logInvRate : ℕ) (s : VerifierProgramState) : Option (Unit ×
    VerifierProgramState) :=
  match Whir.ladder logN logInvRate with
  | some (level :: _) => commitPure (logN - level.fold + level.logInvRate) (2 ^ level.fold) s
  | _ => none

/-- The verifier's state at the start: the sponge's default state, the proof unread, no root. -/
@[expose] def initialState (π : Proof) : VerifierProgramState := ⟨⟨default, [], none⟩, π.stream,
    π.openings, []⟩

/-! ## The lighter layout -/

/-- The fields of a layout the extractor reads. -/
structure LayoutLite where
  logMemory : ℕ
  logBytecode : ℕ
  placements : List (Option Placement)
  stackLog : ℕ
  tableLogHeights : List ℕ

/-- A layout's fields the extractor reads. -/
@[expose] def layoutLite (layout : Layout) : LayoutLite :=
  ⟨layout.logMemory, layout.logBytecode, layout.placements, layout.stackLog,
    layout.tableLogHeights⟩

/-- `buildLayout`, only the fields the extractor reads: no bus blocks, no copy of the bytecode. -/
@[expose] def buildLayoutLite (bytecode : List K) (logMemory : ℕ) (tableRows : List ℕ) :
    Option LayoutLite :=
  match log2Strict bytecode.length with
  | none => none
  | some logLength =>
    if busBits ≤ logLength ∧ 1 ≤ logMemory ∧ logMemory ≤ 30 ∧
        tableRows.all (· ≤ 2 ^ 30) ∧ logLength - busBits ≤ 30 ∧
        tableRows.length = tables.length then
      let logBytecode := logLength - busBits
      let tableLogHeights := List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) tableRows
        tableLogFloors
      let placed := placementsOf (columnKappas logMemory logBytecode tableLogHeights)
      some ⟨logMemory, logBytecode, placed.1, placed.2, tableLogHeights⟩
    else none

/-- **`buildLayoutLite` is `buildLayout`'s fields the extractor reads.** -/
theorem buildLayoutLite_eq (bytecode : List K) (logMemory : ℕ) (tableRows : List ℕ) :
    buildLayoutLite bytecode logMemory tableRows =
      (buildLayout bytecode logMemory tableRows).map layoutLite := by
  unfold buildLayoutLite buildLayout
  cases log2Strict bytecode.length with
  | none => rfl
  | some logLength =>
    dsimp only
    split_ifs <;> rfl

/-- `readSizesPure` with the lighter layout. -/
@[expose] def readSizesLite (bytecode : List K) (s : VerifierProgramState) :
    Option ((LayoutLite × ℕ) × VerifierProgramState) :=
  (readPure (2 + tables.length) s).bind fun r ↦
    if (r.1.all fun value ↦ value.limb 1 = 0) then
      let logMemory := kToNat ((r.1.headD 0).limb 0)
      let tableRows := ((r.1.drop 1).take tables.length).map fun value ↦ kToNat (value.limb 0)
      let logInverseRate := kToNat ((r.1.getLastD 0).limb 0)
      if 1 ≤ logInverseRate ∧ logInverseRate ≤ 4 then
        (buildLayoutLite bytecode logMemory tableRows).bind fun layout ↦
          if Whir.minLogStack ≤ layout.stackLog ∧ layout.stackLog ≤ Whir.maxLogStack then
            some ((layout, logInverseRate), r.2)
          else none
      else none
    else none

/-- `afterRoot` with the lighter layout: the announced sizes, then the stack's root. -/
@[expose] def afterRootLite (bytecode : List K) (π : Proof) :
    Option ((LayoutLite × ℕ) × VerifierProgramState) :=
  (readSizesLite bytecode (initialState π)).bind fun r ↦
    (commitStackPure r.1.1.stackLog r.1.2 r.2).map fun t ↦ (r.1, t.2)

end

end LeanVM.Extraction.Fast
