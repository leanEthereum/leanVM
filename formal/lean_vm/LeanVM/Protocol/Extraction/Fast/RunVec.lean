module

public import LeanVM.Protocol.Extraction.Fast.Address
public import LeanVM.Protocol.Extraction.Fast.AfterRoot

/-!
# The halting search on a memory vector

`candidateExecutionTable` (`Fast/Address.lean`) reads the memory through `memoryImage layout q`, a
function that recomputes three placements and three stack reads per memory read, and compares the
registers with `Registers.final prog` at every step. Here the same search for a cost machine:

* `memoryVec`: the `2^κ` memory words as a vector, the three placement offsets computed once
  (`memoryVec_get`: its entries are `memoryImage`'s);
* `stepVec`, `haltLoopVec`: `stepTable`, `haltLoopTable` reading the vector, with the final
  registers `fin` an argument, computed once (`haltLoopVec_eq`);
* `candidateExecutionVec`: the public boundary checked first, on the two words it reads
  (`boundaryOfStack`), the memory vector built and the halting loop run only when it holds
  (`candidateExecutionVec_eq`, through `filter_boundaryOK_map`);
* `candidateExecutionIn_eq_none`: above `2^30` words a stack has no execution (`boundaryOK`
  fails), so above `2^63` words the fast search returns `none` with no hash map;
* all on the lighter layout (`LayoutLite`, `Fast/AfterRoot.lean`: the fields the extractor reads),
  with `LayoutLite.placement`, `memoryImageLite`, `stepCapLite`, each the statement's at
  `layoutLite layout` by `rfl`;
* `candidateExecutionFastVec` (per stack) and `candidateRunner` (the tables built once, then a
  closure over the stacks), both equal to `candidateExecutionFast`
  (`candidateExecutionFastVec_eq`, `candidateRunner_eq`).

`extractFast` (`Fast/Extract.lean`) and `extractWith` (`Fast/Lookup.lean`) bind
`let execution := candidateExecutionFast prog input layout` and pass it to `findSome?` over the
candidate stacks: whether the tables `powTable layout.logMemory`, `powTable prog.logSize` are
built once or once per stack depends on the compiler sharing the partial application. To build
them once, bind `let execution := candidateRunner prog input layout` there instead, equal by
`candidateRunner_eq`.
-/

namespace LeanVM.Extraction.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol LeanVM.Protocol.Halting
open LeanVM.Extraction LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

public section

/-! ## The memory vector -/

theorem vector_get_ofFn {α : Type _} {n : ℕ} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  exact Vector.getElem_ofFn i.isLt

theorem layoutLite_logMemory (layout : Verifier.Layout) :
    (layoutLite layout).logMemory = layout.logMemory :=
  rfl

theorem layoutLite_stackLog (layout : Verifier.Layout) :
    (layoutLite layout).stackLog = layout.stackLog :=
  rfl

/-- `Layout.placement` on the lighter layout. -/
@[expose] def LayoutLite.placement (layout : LayoutLite) (column : ℕ) : Placement :=
  (layout.placements.getD column none).getD default

/-- `memoryImage` on the lighter layout. -/
@[expose] def memoryImageLite (layout : LayoutLite) {μ : ℕ} (q : Vector K (2 ^ μ)) :
    MemoryImage layout.logMemory :=
  fun i ↦
    let limb (column : ℕ) : K := q.getD ((layout.placement column).index + i) 0
    E.ofLimbs (limb memory0) (limb memory1) (limb memory2)

theorem memoryImageLite_layoutLite (layout : Verifier.Layout) {μ : ℕ} (q : Vector K (2 ^ μ)) :
    memoryImageLite (layoutLite layout) q = memoryImage layout q :=
  rfl

/-- `stepCap` on the lighter layout. -/
@[expose] def stepCapLite (layout : LayoutLite) : ℕ :=
  (layout.tableLogHeights.map (2 ^ ·)).sum + 2 ^ layout.logMemory + 2 ^ layout.logBytecode

theorem stepCapLite_layoutLite (layout : Verifier.Layout) :
    stepCapLite (layoutLite layout) = stepCap layout :=
  rfl

/-- **The memory image of a stack, as a vector**: `memoryImageLite`, the offsets of the placements
of `MEMORY_0`, `MEMORY_1`, `MEMORY_2` computed once. -/
@[expose] def memoryVec (layout : LayoutLite) {μ : ℕ} (q : Vector K (2 ^ μ)) :
    Vector E (2 ^ layout.logMemory) :=
  let o₀ := (layout.placement memory0).index
  let o₁ := (layout.placement memory1).index
  let o₂ := (layout.placement memory2).index
  Vector.ofFn fun i ↦ E.ofLimbs (q.getD (o₀ + i) 0) (q.getD (o₁ + i) 0) (q.getD (o₂ + i) 0)

theorem memoryVec_get (layout : LayoutLite) {μ : ℕ} (q : Vector K (2 ^ μ))
    (i : Fin (2 ^ layout.logMemory)) : (memoryVec layout q).get i = memoryImageLite layout q i := by
  exact vector_get_ofFn (memoryImageLite layout q) i

theorem memoryVec_get_eq (layout : LayoutLite) {μ : ℕ} (q : Vector K (2 ^ μ)) :
    (memoryVec layout q).get = memoryImageLite layout q :=
  funext (memoryVec_get layout q)

/-! ## The halting search on the vector -/

/-- `stepTable`, reading the memory vector. -/
@[expose] def stepVec (memT codeT : Array (ℕ × ℕ)) (prog : LeanIsaProgram) {κ : ℕ}
    (mem : Vector E (2 ^ κ)) (r : Registers K) : Option (Registers K) :=
  (gLogTable codeT prog.logSize r.pc).map prog.instructions >>=
    executeWith (fun a ↦ (gLogTable memT κ a).map mem.get) r

theorem stepVec_eq (memT codeT : Array (ℕ × ℕ)) (prog : LeanIsaProgram) {κ : ℕ}
    (mem : Vector E (2 ^ κ)) (r : Registers K) :
    stepVec memT codeT prog mem r = stepTable memT codeT prog mem.get r :=
  rfl

/-- `haltLoopTable`, reading the memory vector, with the final registers `fin` given. -/
@[expose] def haltLoopVec (memT codeT : Array (ℕ × ℕ)) (prog : LeanIsaProgram) {κ : ℕ}
    (mem : Vector E (2 ^ κ)) (fin : Registers K) : ℕ → ℕ → Registers K → Option ℕ
  | 0, n, r => if r = fin then some n else none
  | fuel + 1, n, r =>
    if r = fin then some n
    else
      match stepVec memT codeT prog mem r with
      | none => none
      | some r' => haltLoopVec memT codeT prog mem fin fuel (n + 1) r'

theorem haltLoopVec_eq (memT codeT : Array (ℕ × ℕ)) (prog : LeanIsaProgram) {κ : ℕ}
    (mem : Vector E (2 ^ κ)) :
    ∀ fuel n r, haltLoopVec memT codeT prog mem (Registers.final prog) fuel n r =
      haltLoopTable memT codeT prog mem.get fuel n r
  | 0, n, r => rfl
  | fuel + 1, n, r => by
    rw [haltLoopVec, haltLoopTable, stepVec_eq]
    split
    · rfl
    · cases stepTable memT codeT prog mem.get r with
      | none => rfl
      | some r' => exact haltLoopVec_eq memT codeT prog mem fuel (n + 1) r'

/-! ## The public boundary, first -/

/-- `boundaryOK` of a stack's execution, read off the stack: it reads only the memory's size and
words `0` and `1`, not the number of steps. -/
@[expose] def boundaryOfStack (input : PublicInput) (layout : LayoutLite) {μ : ℕ}
    (q : Vector K (2 ^ μ)) : Bool :=
  if h : minLogMem ≤ layout.logMemory ∧ layout.logMemory ≤ maxLogMem then
    decide (memoryImageLite layout q ⟨0, Nat.two_pow_pos layout.logMemory⟩ = input.word0) &&
      decide (memoryImageLite layout q ⟨1, Nat.one_lt_two_pow (by unfold minLogMem at h; omega)⟩ =
        input.word1)
  else false

/-- **The boundary filter, checked first**: filtering the runs by `boundaryOK` is checking the
boundary of the stack, then running. -/
theorem filter_boundaryOK_map {prog : LeanIsaProgram} (input : PublicInput) (layout :
    Verifier.Layout)
    {μ : ℕ} (q : Vector K (2 ^ μ)) (o : Option ℕ) :
    (o.map fun n ↦ (⟨layout.logMemory, memoryImage layout q, n⟩ : Execution prog)).filter
        (boundaryOK input) =
      if boundaryOfStack input (layoutLite layout) q then
        o.map fun n ↦ (⟨layout.logMemory, memoryImage layout q, n⟩ : Execution prog)
      else none := by
  cases o with
  | none =>
    simp only [Option.map_none, Option.filter_none, ite_self]
  | some n =>
    rfl

theorem boundaryOfStack_of_lt (input : PublicInput) (layout : LayoutLite) {μ : ℕ}
    (q : Vector K (2 ^ μ)) (h : maxLogMem < layout.logMemory) :
    boundaryOfStack input layout q = false := by
  unfold boundaryOfStack
  split
  · rename_i hc
    exact absurd hc.2 (Nat.not_le.2 h)
  · rfl

/-- **Above `2^30` words a stack has no execution**: its runs fail the boundary. -/
theorem candidateExecutionIn_eq_none (memIdx codeIdx : Std.HashMap UInt64 ℕ) (prog : LeanIsaProgram)
    (input : PublicInput) (layout : Verifier.Layout) (h : maxLogMem < layout.logMemory) {μ : ℕ}
    (q : Vector K (2 ^ μ)) : candidateExecutionIn memIdx codeIdx prog input layout q = none := by
  rewrite [candidateExecutionIn, haltingRunIn, filter_boundaryOK_map,
    boundaryOfStack_of_lt input (layoutLite layout) q h]
  rfl

/-! ## A stack's execution -/

/-- `candidateExecutionTable` on the memory vector: the boundary checked first, then the memory
vector built and the halting loop run, from the final registers `fin` and the step cap `cap`. -/
@[expose] def candidateExecutionVec (memT codeT : Array (ℕ × ℕ)) (prog : LeanIsaProgram)
    (input : PublicInput) (layout : LayoutLite) (fin : Registers K) (cap : ℕ) {μ : ℕ}
    (q : Vector K (2 ^ μ)) : Option (Execution prog) :=
  if boundaryOfStack input layout q then
    let mem := memoryVec layout q
    (haltLoopVec memT codeT prog mem fin cap 0 Registers.initial).map
      fun n ↦ ⟨layout.logMemory, mem.get, n⟩
  else none

theorem candidateExecutionVec_eq (memT codeT : Array (ℕ × ℕ)) (prog : LeanIsaProgram)
    (input : PublicInput) (layout : Verifier.Layout) {μ : ℕ} (q : Vector K (2 ^ μ)) :
    candidateExecutionVec memT codeT prog input (layoutLite layout) (Registers.final prog)
        (stepCap layout) q =
      candidateExecutionTable memT codeT prog input layout q := by
  rewrite [candidateExecutionTable, filter_boundaryOK_map, candidateExecutionVec]
  simp only [haltLoopVec_eq, memoryVec_get_eq, memoryImageLite_layoutLite]
  rfl

/-- **A stack's execution on the memory vector**: the address tables, the final registers and the
step cap computed once per stack; `none` above `2^63` words, where no stack has an execution
(`candidateExecutionIn_eq_none`). -/
@[expose] def candidateExecutionFastVec (prog : LeanIsaProgram) (input : PublicInput)
    (layout : LayoutLite) (q : Vector K (2 ^ layout.stackLog)) : Option (Execution prog) :=
  if layout.logMemory < 64 then
    let memT := powTable layout.logMemory
    let codeT := powTable prog.logSize
    let fin := Registers.final prog
    let cap := stepCapLite layout
    candidateExecutionVec memT codeT prog input layout fin cap q
  else none

theorem candidateExecutionFastVec_apply (prog : LeanIsaProgram) (input : PublicInput)
    (layout : Verifier.Layout) (q : Vector K (2 ^ layout.stackLog)) :
    candidateExecutionFastVec prog input (layoutLite layout) q =
      candidateExecutionFast prog input layout q := by
  rw [candidateExecutionFast_eq]
  unfold candidateExecutionFastVec
  by_cases h : layout.logMemory < 64
  · simp only [layoutLite_logMemory, stepCapLite_layoutLite, h, ↓reduceIte]
    exact (candidateExecutionVec_eq (powTable layout.logMemory) (powTable prog.logSize) prog input
      layout q).trans (candidateExecutionTable_eq h q)
  · simp only [layoutLite_logMemory, h, ↓reduceIte]
    have hl : maxLogMem < layout.logMemory := by unfold maxLogMem; omega
    exact (candidateExecutionIn_eq_none (powIndex layout.logMemory) (powIndex prog.logSize) prog
      input layout hl q).symm

/-- **The fast search on the memory vector is `candidateExecutionFast`.** -/
theorem candidateExecutionFastVec_eq (prog : LeanIsaProgram) (input : PublicInput)
    (layout : Verifier.Layout) :
    candidateExecutionFastVec prog input (layoutLite layout) =
      candidateExecutionFast prog input layout := by
  funext q
  exact candidateExecutionFastVec_apply prog input layout q

/-- **The search over the stacks**: the address tables, the final registers and the step cap
built once, then a closure over the stacks. `extractFast` should bind
`let execution := candidateRunner prog input layout` for `findSome?` (`candidateRunner_eq`). -/
@[expose] def candidateRunner (prog : LeanIsaProgram) (input : PublicInput) (layout : LayoutLite) :
    Vector K (2 ^ layout.stackLog) → Option (Execution prog) :=
  if layout.logMemory < 64 then
    let memT := powTable layout.logMemory
    let codeT := powTable prog.logSize
    let fin := Registers.final prog
    let cap := stepCapLite layout
    fun q ↦ candidateExecutionVec memT codeT prog input layout fin cap q
  else fun _ ↦ none

theorem candidateRunner_eq (prog : LeanIsaProgram) (input : PublicInput) (layout :
    Verifier.Layout) :
    candidateRunner prog input (layoutLite layout) = candidateExecutionFast prog input layout := by
  rw [candidateExecutionFast_eq]
  unfold candidateRunner
  by_cases h : layout.logMemory < 64
  · simp only [layoutLite_logMemory, stepCapLite_layoutLite, h, ↓reduceIte]
    funext q
    exact (candidateExecutionVec_eq (powTable layout.logMemory) (powTable prog.logSize) prog input
      layout q).trans (candidateExecutionTable_eq h q)
  · simp only [layoutLite_logMemory, h, ↓reduceIte]
    funext q
    have hl : maxLogMem < layout.logMemory := by unfold maxLogMem; omega
    exact (candidateExecutionIn_eq_none (powIndex layout.logMemory) (powIndex prog.logSize) prog
      input layout hl q).symm


/-- The runner's tables: the address tables, the final registers and the step cap, built once per
layout (`none` above `2^63` words, where no stack has an execution). -/
@[expose] def runnerTables (prog : LeanIsaProgram) (layout : LayoutLite) :
    Option (Array (ℕ × ℕ) × Array (ℕ × ℕ) × Registers K × ℕ) :=
  if layout.logMemory < 64 then
    some (powTable layout.logMemory, powTable prog.logSize, Registers.final prog, stepCapLite layout)
  else none

/-- A stack's execution from the runner's tables. -/
@[expose] def runWithTables (tabs : Option (Array (ℕ × ℕ) × Array (ℕ × ℕ) × Registers K × ℕ))
    (prog : LeanIsaProgram) (input : PublicInput) (layout : LayoutLite) (q : Vector K (2 ^ layout.stackLog)) :
    Option (Execution prog) :=
  match tabs with
  | some (memT, codeT, fin, cap) => candidateExecutionVec memT codeT prog input layout fin cap q
  | none => none

/-- **The runner, its tables built once**: the closure `runWithTables (runnerTables prog layout)`
is `candidateRunner`. -/
theorem runWithTables_runnerTables (prog : LeanIsaProgram) (input : PublicInput) (layout :
    LayoutLite) :
    runWithTables (runnerTables prog layout) prog input layout = candidateRunner prog input layout := by
  funext q
  unfold runWithTables runnerTables candidateRunner
  split_ifs <;> rfl

end

end LeanVM.Extraction.Fast
