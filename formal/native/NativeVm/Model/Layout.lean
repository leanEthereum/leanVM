module

public import NativeVm.Model.Transcript
public import Statement.Verifier.Layout

/-!
# Phase 1: the announced sizes and the layout

Models `readAnnouncedSizes` and `buildLayout` (`Statement/Verifier/Lib.lean`, `Statement/Verifier/Layout.lean`, `layout.rs`).

**Takes** the bytecode's words and the transcript at the stream's start. **Reads** `2 + 6`
scalars. **Returns** `(LayoutW, logInverseRate)`: the memory's and the bytecode's log-sizes, the
bytecode, the three bus sides' blocks, every global column's placement (`none` for a `KECCAK`
output lane), the stack's log-size and the tables' log-heights.

The instruction tables are fixed data: `tablesW` is the statement's `tables` with every form's
coefficients as lanes (`FormW.ofForm`), its flushes, count columns, constraint count and padding
row; the one table with constraints, `JUMP`, evaluates them by `constraintsW`, the statement's
`jumpConstraints`. `keccakSlotTable` tabulates `keccakSlot` over the global columns. A form
(`FormW`) is the statement's `Form`: its terms in insertion order, each a monomial (sorted column
indices) and a coefficient.
-/

@[expose] public section

namespace NativeVm.Model

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-! ## Forms (`Form`, `layout.rs`) -/

/-- A term: a monomial in the columns, and its coefficient. -/
structure TermW where
  cols : Array Nat
  coeff : EW
  deriving Inhabited

/-- A form: `Σ c · Π column(i)` over its terms, in insertion order. -/
abbrev FormW := Array TermW

namespace FormW

/-- A form of the statement, its coefficients as lanes. -/
def ofForm (f : Form) : FormW := f.terms.toArray.map fun (m, c) ↦ ⟨m.toArray, EW.ofE c⟩

/-- `constant(value)`. -/
def const (value : EW) : FormW := #[⟨#[], value⟩]

/-- `addTerm`: add `c` into the coefficient of `m`, appending the monomial if it is new. -/
def addTerm (f : FormW) (m : Array Nat) (c : EW) : FormW :=
  match f.findIdx? (·.cols == m) with
  | some i => f.modify i fun t ↦ { t with coeff := t.coeff + c }
  | none => f.push ⟨m, 0 + c⟩

/-- `Form::add_scaled`: add `weight · other`. -/
def addScaled (f other : FormW) (weight : EW) : FormW :=
  other.foldl (fun acc t ↦ addTerm acc t.cols (weight * t.coeff)) f

/-- `Form::evaluate` on a row of evaluations, a missing column `0`. -/
def evaluate (f : FormW) (row : Array EW) : EW :=
  sumE (f.map fun t ↦ t.cols.foldl (fun acc i ↦ acc * row.getD i 0) t.coeff)

end FormW

/-! ## The instruction tables (`layout.rs`) -/

/-- One instruction's table as data: its opcode, width, the tuples it pushes and pulls, its count
columns, its constraint count and its padding row. -/
structure TableW where
  opcode : Nat
  width : Nat
  push : Array (Array FormW)
  pull : Array (Array FormW)
  countColumns : Array Nat
  nConstraints : Nat
  padding : Array EW
  deriving Inhabited

/-- A table of the statement as data. -/
def TableW.ofTable (t : Table) : TableW :=
  ⟨t.opcode, t.width, t.flushes.push.toArray.map (·.toArray.map FormW.ofForm),
    t.flushes.pull.toArray.map (·.toArray.map FormW.ofForm), t.countColumns.toArray,
    t.nConstraints, t.padding.toArray.map EW.ofE⟩

/-- `tables()`, in opcode order. -/
def tablesW : Array TableW := tables.toArray.map TableW.ofTable

/-- `N_TABLES`. -/
def nTables : Nat := 6

/-- A table's constraints on a row (`Table.constraints`): `jumpConstraints` for `JUMP`, none
otherwise. -/
def constraintsW (opcode : Nat) (row : Array EW) : Array EW :=
  if opcode = opJump then
    let c := columnIndexByName jumpColumns
    let condition := row.getD (c "v_cond") 0
    let inverse := row.getD (c "w") 0
    let flag := row.getD (c "b") 0
    #[flag + condition * inverse, condition * (flag + 1)]
  else #[]

/-- The global columns: the framework's, then every table's. -/
def columnCount : Nat := globalColumnCount + tableWidths.sum

/-- `keccakSlot`, tabulated over the global columns. -/
def keccakSlotTable : Array (Option Nat) := (Array.range columnCount).map keccakSlot

/-- Whether a global column is a `KECCAK` output lane (`keccakOutputColumns`), tabulated. -/
def keccakOutputTable : Array Bool :=
  (Array.range columnCount).map fun c ↦ decide (c ∈ keccakOutputColumns)

/-- `GLOBAL_COLUMN_BASES`. -/
def globalColumnBasesW : Array Nat := globalColumnBases.toArray

/-! ## Placements (`multilinear.rs`, `bus.rs`) -/

/-- `Placement::stack_point`. -/
def stackPoint (p : Placement) (point : Array EW) (stackLog : Nat) : Array EW :=
  point ++ selectorPoint (p.index >>> p.variableCount) (stackLog - p.variableCount)

/-- `Placement::eq_above`. -/
def eqAbove (p : Placement) (point : Array EW) : EW :=
  eqEval (selectorPoint (p.index >>> p.variableCount) (point.size - p.variableCount))
    (point.extract p.variableCount point.size)

/-- The swap loop of an insertion sort: `xs[j]` swapped down past every predecessor `lt` puts it
before (core's `Array.insertionSort.swapLoop`, which is private). -/
def swapDown {α : Type} [Inhabited α] (lt : α → α → Bool) (xs : Array α) : Nat → Array α
  | 0 => xs
  | j + 1 => if lt xs[j + 1]! xs[j]! then swapDown lt (xs.swapIfInBounds (j + 1) j) j else xs

/-- `Array.insertionSort`: each element in turn swapped down the sorted prefix. -/
def insertionSort {α : Type} [Inhabited α] (lt : α → α → Bool) (xs : Array α) : Array α :=
  (List.range xs.size).foldl (fun acc i ↦ swapDown lt acc i) xs

/-- `stack_offsets(sizes)`: blocks of `2^size` end to end, largest first, ties by index (an
insertion sort by that order); the offsets, and the log-size of the total. -/
def stackOffsets (sizes : Array Nat) : Array Nat × Nat :=
  let size := fun i ↦ sizes.getD i 0
  let order := insertionSort
    (fun i j ↦ decide (size j < size i) || (decide (size i = size j) && decide (i < j)))
    (Array.range sizes.size)
  let placed := order.foldl (fun (acc : Array Nat × Nat) i ↦
    (acc.1.set! i acc.2, acc.2 + 2 ^ size i)) (Array.replicate sizes.size 0, 0)
  (placed.1, log2Ceil placed.2)

/-! ## The bus blocks (`BusBlock`, `layout.rs`) -/

/-- One block of a bus side: its owner's log-height and rows, the tuple it flushes, its owner. -/
structure BusBlockW where
  logRows : Nat
  rows : Nat
  coordinates : Array FormW
  owner : Nat
  deriving Inhabited

/-- `busBlocks`: every table's pushes, pulls and count columns, at its height and rows. -/
def busBlocks (heights rows : Array Nat) : Array BusBlockW × Array BusBlockW × Array BusBlockW :=
  let hn := fun (t : TableW) ↦ (heights.getD t.opcode 0, rows.getD t.opcode 0)
  (tablesW.flatMap fun t ↦ t.push.map fun c ↦ ⟨(hn t).1, (hn t).2, c, t.opcode⟩,
    tablesW.flatMap fun t ↦ t.pull.map fun c ↦ ⟨(hn t).1, (hn t).2, c, t.opcode⟩,
    tablesW.flatMap fun t ↦ t.countColumns.map fun l ↦
      ⟨(hn t).1, (hn t).2, #[FormW.ofForm (Form.col l)], t.opcode⟩)

/-! ## `build_layout` (`layout.rs`) -/

/-- The layout (`Layout`). -/
structure LayoutW where
  logMemory : Nat
  logBytecode : Nat
  bytecode : Array UInt64
  push : Array BusBlockW
  pull : Array BusBlockW
  count : Array BusBlockW
  placements : Array (Option Placement)
  stackLog : Nat
  tableLogHeights : Array Nat
  deriving Inhabited

/-- `Layout.placement`. -/
def LayoutW.placement (layout : LayoutW) (column : Nat) : Placement :=
  ((layout.placements[column]?).getD none).getD default

/-- `columnKappas`: every column's log-size. -/
def columnKappas (logMemory logBytecode : Nat) (heights : Array Nat) : Array Nat :=
  #[logMemory, logMemory, logMemory, logBytecode, heights.getD opKeccak 0 + qkeccakSlotBits] ++
    tablesW.flatMap fun t ↦ Array.replicate t.width (heights.getD t.opcode 0)

/-- `placementsOf`: the committed columns stacked, a column with a `q_keccak` slot inside
`q_keccak`'s block, an output lane nowhere; and the stack's log-size. -/
def placementsOf (kappas : Array Nat) : Array (Option Placement) × Nat :=
  let slotOf := fun c ↦ (keccakSlotTable[c]?).getD none
  let isOutput := fun c ↦ (keccakOutputTable[c]?).getD false
  let blockCols := (Array.range kappas.size).filter fun c ↦ (slotOf c).isNone && !isOutput c
  let (blockOffsets, totalLog) := stackOffsets (blockCols.map (kappas.getD · 0))
  let offsets := (blockCols.zip blockOffsets).foldl (fun (acc : Array Nat) (c, o) ↦ acc.set! c o)
    (Array.replicate kappas.size 0)
  let offsetOf := fun c ↦ offsets.getD c 0
  let placements := kappas.zipIdx.map fun (kappa, column) ↦
    match slotOf column with
    | some slot =>
      some ({ variableCount := kappa, index := offsetOf qkeccak + slot * 2 ^ kappa } : Placement)
    | none =>
      if isOutput column then none else some { variableCount := kappa, index := offsetOf column }
  (placements, max LeanVM.Parameters.Whir.minLogStack totalLog)

/-- `build_layout(bytecode, log_memory, table_rows)`; `none` where the Rust errs. -/
def buildLayout (bytecode : Array UInt64) (logMemory : Nat) (tableRows : Array Nat) :
    Option LayoutW :=
  match log2Strict bytecode.size with
  | none => none
  | some logLength =>
    if busBits ≤ logLength ∧ 1 ≤ logMemory ∧ logMemory ≤ 30 ∧
        tableRows.all (· ≤ 2 ^ 30) ∧ logLength - busBits ≤ 30 ∧ tableRows.size = nTables then
      let logBytecode := logLength - busBits
      let heights := Array.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) tableRows
        tableLogFloors.toArray
      let (push, pull, count) := busBlocks heights tableRows
      let (placements, stackLog) := placementsOf (columnKappas logMemory logBytecode heights)
      some ⟨logMemory, logBytecode, bytecode, push, pull, count, placements, stackLog, heights⟩
    else none

/-- **Phase 1** (`readAnnouncedSizes`): the memory log-size, the tables' row counts and the WHIR
rate exponent, each a scalar in `K`, checked; the layout and the rate exponent. -/
def readAnnouncedSizes (bytecode : Array UInt64) : VM (LayoutW × Nat) := do
  let announced ← readScalars (2 + nTables)
  require (announced.all (·.c1 == 0))
  let logMemory := (announced.getD 0 0).c0.toNat
  let tableRows := (announced.extract 1 (1 + nTables)).map (·.c0.toNat)
  let logInverseRate := (announced.back?.getD 0).c0.toNat
  require (1 ≤ logInverseRate && logInverseRate ≤ 4)
  let layout ← liftOpt (buildLayout bytecode logMemory tableRows)
  require (LeanVM.Parameters.Whir.minLogStack ≤ layout.stackLog &&
    layout.stackLog ≤ LeanVM.Parameters.Whir.maxLogStack)
  pure (layout, logInverseRate)

end NativeVm.Model
