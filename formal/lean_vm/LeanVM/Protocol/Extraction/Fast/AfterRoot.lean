module

public import LeanVM.Protocol.Extraction.Extractor

/-!
# The stack's root, without the verifier's free monad

The extractor starts from `afterRoot` (`Extraction/Extractor.lean`): the verifier's steps 1 and 2,
`announceSizesAndRoot`, a `VerifierProgram` run by `runPure` (every permutation answered by
`default`).
`VerifierProgram`'s constructors hold continuations
(`read : (E → VerifierProgram α) → VerifierProgram α`, …), which the cost compiler does not take.
Here the same steps are plain state-passing functions in `Option`:

* `absorbPure`: the sponge's `absorb` with every permutation `default`; `readPure n`: read and
  absorb `n` scalars (`runPure_readScalars`); `commitPure`: read a root (`runPure_readCommitment`);
* `readSizesPure`, `commitStackPure`: `readAnnouncedSizes` and `commitStack` (`runPure_readSizes`,
  `runPure_commitStack`);
* **`afterRootDirect_eq`**: `afterRootDirect` is `afterRoot`;
* **`announced_of_afterRoot`**: the layout and the rate `afterRoot` returns are the ones the stream
  announces (`announced`, which the statement's budget reads): `readAnnouncedSizes` reads only the
  sponge and the stream (`readPure_carry`, `readSizesPure_carry`).

The lighter layout: the extractor reads of the layout only `logMemory`, `logBytecode`,
`placements`, `stackLog` and `tableLogHeights`. `buildLayoutLite` computes only these (no bus
blocks, no forms, no bytecode copy), and is `buildLayout` followed by `layoutLite`
(`buildLayoutLite_eq`); `afterRootLite` is `afterRoot` with its layout so cut
(`afterRootLite_eq`).

The run's algebra: `runPure_bind` (a sequence runs as its first program, then the continuation),
`runPure_require_bind`, `runPure_liftOption_bind`, `runPure_readScalars_bind`, `runPure_pure`.
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

theorem runPure_pure {α : Type} (a : α) (s : VerifierProgramState) :
    runPure (pure a : VerifierProgram α) s = some (a, s) := rfl

theorem runPure_require_bind {β : Type} (c : Prop) [Decidable c] (f : Unit → VerifierProgram β)
    (s : VerifierProgramState) :
    runPure (VerifierProgram.require c >>= f) s = if c then runPure (f ()) s else none := by
  by_cases hc : c
  · simp only [VerifierProgram.require, hc, ↓reduceIte]; rfl
  · simp only [VerifierProgram.require, hc, ↓reduceIte]; rfl

theorem runPure_liftOption_bind {α β : Type} (o : Option α) (f : α → VerifierProgram β) (s :
    VerifierProgramState) :
    runPure (liftOption o >>= f) s = o.bind fun a ↦ runPure (f a) s := by
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

theorem runPure_readCommitment (height width : ℕ) (s : VerifierProgramState) :
    runPure (VerifierProgram.readCommitment height width) s = commitPure height width s := by
  rcases s with ⟨⟨st0, pend, gr⟩, _ | ⟨x0, _ | ⟨x1, xs⟩⟩, os, roots⟩
  · simp only [runPure, VerifierProgram.readCommitment, Compile.run, commitPure]; rfl
  · simp only [runPure, VerifierProgram.readCommitment, Compile.run, commitPure]; rfl
  · cases gr with
    | some c => simp only [runPure, VerifierProgram.readCommitment, Compile.run, commitPure]; rfl
    | none =>
      simp only [runPure, VerifierProgram.readCommitment, Compile.run, commitPure, Compile.absorb,
        Compile.duplex, absorbPure]
      simp [Id.run, bind, pure]
      split_ifs <;> simp_all

/-! ## Steps 1 and 2 -/

/-- `readAnnouncedSizes bytecode` (`Statement/LeanVmVerifier.lean`), run: the announced sizes, read and
checked, and the layout they give. -/
@[expose] def readSizesPure (bytecode : List K) (s : VerifierProgramState) :
    Option ((Layout × ℕ) × VerifierProgramState) :=
  (readPure (2 + tables.length) s).bind fun r ↦
    if (r.1.all fun value ↦ value.limb 1 = 0) then
      let logMemory := kToNat ((r.1.headD 0).limb 0)
      let tableRows := ((r.1.drop 1).take tables.length).map fun value ↦ kToNat (value.limb 0)
      let logInverseRate := kToNat ((r.1.getLastD 0).limb 0)
      if 1 ≤ logInverseRate ∧ logInverseRate ≤ 4 then
        (buildLayout bytecode logMemory tableRows).bind fun layout ↦
          if Whir.minLogStack ≤ layout.stackLog ∧ layout.stackLog ≤ Whir.maxLogStack then
            some ((layout, logInverseRate), r.2)
          else none
      else none
    else none

theorem runPure_readSizes (bytecode : List K) (s : VerifierProgramState) :
    runPure (readAnnouncedSizes bytecode) s = readSizesPure bytecode s := by
  simp only [readAnnouncedSizes, readSizesPure, runPure_readScalars_bind, runPure_require_bind,
    runPure_liftOption_bind, runPure_pure]

/-- `commitStack logN logInvRate`, run: the stack's root, at the shape of the ladder's first
level. -/
@[expose] def commitStackPure (logN logInvRate : ℕ) (s : VerifierProgramState) : Option (Unit ×
    VerifierProgramState) :=
  match Whir.ladder logN logInvRate with
  | some (level :: _) => commitPure (logN - level.fold + level.logInvRate) (2 ^ level.fold) s
  | _ => none

theorem runPure_commitStack (logN logInvRate : ℕ) (s : VerifierProgramState) :
    runPure (commitStack logN logInvRate) s = commitStackPure logN logInvRate s := by
  unfold commitStack commitStackPure
  cases Whir.ladder logN logInvRate with
  | none => rfl
  | some config =>
    cases config with
    | nil => rfl
    | cons level _ =>
      exact runPure_readCommitment (logN - level.fold + level.logInvRate) (2 ^ level.fold) s

/-- The verifier's state at the start: the sponge's default state, the proof unread, no root. -/
@[expose] def initialState (π : Proof) : VerifierProgramState := ⟨⟨default, [], none⟩, π.stream,
    π.openings, []⟩

/-- **`afterRoot`, direct**: the announced sizes, then the stack's root. -/
@[expose] def afterRootDirect (bytecode : List K) (π : Proof) :
    Option ((Layout × ℕ) × VerifierProgramState) :=
  (readSizesPure bytecode (initialState π)).bind fun r ↦
    (commitStackPure r.1.1.stackLog r.1.2 r.2).map fun t ↦ (r.1, t.2)

/-- **`afterRootDirect` is `afterRoot`.** -/
theorem afterRootDirect_eq (bytecode : List K) (π : Proof) :
    afterRootDirect bytecode π = afterRoot bytecode π := by
  show _ = runPure (announceSizesAndRoot bytecode) (initialState π)
  unfold announceSizesAndRoot afterRootDirect
  rw [runPure_bind, runPure_readSizes]
  cases readSizesPure bytecode (initialState π) with
  | none => rfl
  | some r =>
    obtain ⟨⟨layout, R⟩, s1⟩ := r
    show (commitStackPure layout.stackLog R s1).map (fun t ↦ ((layout, R), t.2)) =
      runPure (commitStack layout.stackLog R >>= fun _ ↦ pure (layout, R)) s1
    rw [runPure_bind, runPure_commitStack]
    cases commitStackPure layout.stackLog R s1 <;> rfl

theorem afterRootDirect_eq_afterRoot : afterRootDirect = afterRoot := by
  funext bytecode π
  exact afterRootDirect_eq bytecode π

/-! ## The announced shape -/

/-- `readPure` reads only the sponge and the stream: the openings and the roots are carried. -/
theorem readPure_carry (n : ℕ) (sp : Compile.Sponge) (st : List E) (os os' : List (List Opening))
    (rs rs' : List (Digest × ℕ × ℕ)) :
    readPure n ⟨sp, st, os', rs'⟩ =
      (readPure n ⟨sp, st, os, rs⟩).map fun r ↦ (r.1, ⟨r.2.sponge, r.2.stream, os', rs'⟩) := by
  induction n generalizing sp st with
  | zero => rfl
  | succ n ih =>
    obtain ⟨st0, pend, gr⟩ := sp
    cases st with
    | nil => rfl
    | cons x xs =>
      cases gr with
      | some c => rfl
      | none =>
        show (readPure n ⟨absorbPure ⟨st0, pend, none⟩ x dsObserve, xs, os', rs'⟩).map _ =
          ((readPure n ⟨absorbPure ⟨st0, pend, none⟩ x dsObserve, xs, os, rs⟩).map _).map _
        rw [ih]
        cases readPure n ⟨absorbPure ⟨st0, pend, none⟩ x dsObserve, xs, os, rs⟩ <;> rfl

/-- `readSizesPure` reads only the sponge and the stream. -/
theorem readSizesPure_carry (bytecode : List K) (sp : Compile.Sponge) (st : List E)
    (os os' : List (List Opening)) (rs rs' : List (Digest × ℕ × ℕ)) :
    readSizesPure bytecode ⟨sp, st, os', rs'⟩ =
      (readSizesPure bytecode ⟨sp, st, os, rs⟩).map
        fun r ↦ (r.1, ⟨r.2.sponge, r.2.stream, os', rs'⟩) := by
  unfold readSizesPure
  rw [readPure_carry _ sp st os os' rs rs']
  cases readPure (2 + tables.length) ⟨sp, st, os, rs⟩ with
  | none => rfl
  | some r =>
    dsimp only [Option.map_some, Option.bind_some]
    split_ifs
    · cases buildLayout bytecode (kToNat ((r.1.headD 0).limb 0))
          (((r.1.drop 1).take tables.length).map fun value ↦ kToNat (value.limb 0)) with
      | none => rfl
      | some layout =>
        dsimp only [Option.bind_some]
        split_ifs <;> rfl
    all_goals rfl

/-- **The shape `afterRoot` reads is the one the stream announces** (`announced`, which the
statement's budget reads). -/
theorem announced_of_afterRoot {bytecode : List K} {π : Proof} {layout : Layout} {R : ℕ}
    {st : VerifierProgramState} (h : afterRoot bytecode π = some ((layout, R), st)) :
    announcedLayoutAndRate bytecode π.stream = some (layout, R) := by
  rw [← afterRootDirect_eq] at h
  unfold afterRootDirect at h
  obtain ⟨r, hr, hc⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨t, -, ht⟩ := Option.map_eq_some_iff.1 hc
  have h1 : r.1 = (layout, R) := congrArg Prod.fst ht
  unfold initialState at hr
  rw [readSizesPure_carry bytecode ⟨default, [], none⟩ π.stream [] π.openings [] []] at hr
  obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 hr
  unfold announcedLayoutAndRate
  rw [runPure_readSizes, hr']
  exact congrArg some h1

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

/-- An `afterRoot` result with its layout cut to the fields the extractor reads. -/
@[expose] def liteResult (r : (Layout × ℕ) × VerifierProgramState) : (LayoutLite × ℕ) ×
    VerifierProgramState :=
  ((layoutLite r.1.1, r.1.2), r.2)

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

theorem bind_map_layoutLite (o : Option Layout) (R : ℕ) (st : VerifierProgramState) :
    (o.map layoutLite).bind (fun layout ↦
        if Whir.minLogStack ≤ layout.stackLog ∧ layout.stackLog ≤ Whir.maxLogStack then
          some ((layout, R), st)
        else none) =
      Option.map liteResult (o.bind fun layout ↦
        if Whir.minLogStack ≤ layout.stackLog ∧ layout.stackLog ≤ Whir.maxLogStack then
          some ((layout, R), st)
        else none) := by
  cases o with
  | none => rfl
  | some layout =>
    show (if Whir.minLogStack ≤ layout.stackLog ∧ layout.stackLog ≤ Whir.maxLogStack then
        some ((layoutLite layout, R), st) else none) =
      Option.map liteResult (if Whir.minLogStack ≤ layout.stackLog ∧
        layout.stackLog ≤ Whir.maxLogStack then some ((layout, R), st) else none)
    split_ifs <;> rfl

theorem readSizesLite_eq (bytecode : List K) (s : VerifierProgramState) :
    readSizesLite bytecode s = (readSizesPure bytecode s).map liteResult := by
  unfold readSizesLite readSizesPure
  cases readPure (2 + tables.length) s with
  | none => rfl
  | some r =>
    simp only [Option.bind_some]
    split_ifs <;>
      first
      | (rw [buildLayoutLite_eq]; exact bind_map_layoutLite _ _ _)
      | rfl

/-- `afterRootDirect` with the lighter layout. -/
@[expose] def afterRootLite (bytecode : List K) (π : Proof) :
    Option ((LayoutLite × ℕ) × VerifierProgramState) :=
  (readSizesLite bytecode (initialState π)).bind fun r ↦
    (commitStackPure r.1.1.stackLog r.1.2 r.2).map fun t ↦ (r.1, t.2)

/-- **`afterRootLite` is `afterRoot`, its layout cut to the fields the extractor reads.** -/
theorem afterRootLite_eq (bytecode : List K) (π : Proof) :
    afterRootLite bytecode π = (afterRoot bytecode π).map liteResult := by
  rw [← afterRootDirect_eq]
  unfold afterRootLite afterRootDirect
  rw [readSizesLite_eq]
  cases readSizesPure bytecode (initialState π) with
  | none => rfl
  | some r =>
    show Option.map _ (commitStackPure r.1.1.stackLog r.1.2 r.2) =
      Option.map liteResult (Option.map _ (commitStackPure r.1.1.stackLog r.1.2 r.2))
    cases commitStackPure r.1.1.stackLog r.1.2 r.2 <;> rfl

end

end LeanVM.Extraction.Fast
