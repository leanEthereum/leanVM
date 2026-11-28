module

public import Statement.Prover.LinkRow

/-!
# The link's prover, executable

The honest prover of `verifyLink` (`prove`, `crates/lean_vm_core/src/link/prove.rs`), in its
moves: the grind for the challenges' error, `θ_0`, the rest eight to a permutation
(`LinkChallenges`); the index side's rounds over the pointer width (`indexProds`); the memory term
`M_1` at the index point `r`; the five fresh coefficients; the row rounds over every table's rows
(`rowProds`) and the pointer-column rounds (`columnProds`); and one packed message: each table's
non-pointer columns at its row point, then the pointer columns' bit-slices summed under
`eq(q*, ·)`.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-- Each table's first pointer column in Hotwire's order across the tables. -/
def pointerStarts : List ℕ :=
  exclusivePrefix (tables.map (·.links.pointers.length))

/-- What the link's prover leaves for the ring switch: the row point `χ`, the pointer-column point
`q*`, and each pointer column at `χ` in Hotwire's order (its slices). -/
structure LinkProverEnd where
  chi : List E
  columnPoint : List E
  columns : List ColumnAt
  deriving Inhabited

/-- **The link's prover** over the witness `W` (`prove`, `prove.rs`). -/
def linkProve (W : Witness) : Script LinkProverEnd := do
  let layout := W.layout
  let heights := layout.tableLogHeights
  let chunks := W.chunks
  let (width, d) := (chunks.width, chunks.d)
  let nRows := heights.foldl max 0
  -- The challenges, after the grind their error asks for.
  Script.grindBits (grindingBits (max (nRows + 3 + bytecodeSlotBits) (width + 1)))
  let theta0 ← Script.sampleE
  let drawn ← Script.samplePackedS (packedChallenges tables nRows width)
  let ch := LinkChallenges.ofDraw tables nRows width d theta0 drawn
  -- The index side, then the memory term at `r` and the fresh coefficients.
  let (r, index) ← prodsSumcheck 3 width (indexProds W ch)
  let below := fun (k : ℕ) ↦ prodE ((r.drop (min k width)).map (1 + ·))
  let rMem := r.take layout.logMemory
  let m1 := (mleK (W.cols.getD memory0 #[]) rMem + eY * mleK (W.cols.getD memory1 #[]) rMem) *
    below layout.logMemory
  Script.sendE m1
  let fresh ← Script.samplePackedS 5
  let maxShift := tables.foldl (fun m t ↦ max m t.links.maxShift) 0
  let inp : RowInputs :=
    { ch := ch, functionals := Functionals.new chunks r maxShift, maxShift := maxShift, m1 := m1
      cert := fresh.getD 0 0, jump := fresh.drop 1, yMem := index.at 3, xBc := index.at 5
      pFp := index.at 12, eqZeta := index.at 6, shiftZeta := index.at 7, eq0 := below 0 }
  -- The row rounds.
  let starts := pointerStarts
  let st : RowState := Array.ofFn (n := nTables) fun t ↦
    let (prods, columnTerms) := rowProds W inp t (starts.getD t 0)
    ⟨prods, heights.getD t 0, 0, 1, columnTerms⟩
  let (rowCount, columnCount) := roundCoefficients d
  let (chi, st) ← sumcheckBy (rowRound rowCount) rowFold (List.replicate nRows none) st
  -- The pointer-column rounds.
  let columns := (List.range nTables).flatMap fun t ↦
    columnsAt W inp t (starts.getD t 0) (st.getD t default) chi
  let base := sumE ((List.range nTables).map fun t ↦ baseAt (st.getD t default))
  let qVars := log2Ceil columns.length
  let (qPoint, _) ← prodsSumcheck columnCount qVars
    (columnProds d maxShift inp.functionals.mirrors columns qVars base)
  -- Each table's non-pointer columns at its row point, then the pointer columns' slices.
  let values := (List.range nTables).flatMap fun t ↦
    let table := tables.getD t default
    let cols := W.tableCols t
    let point := chi.take (heights.getD t 0)
    ((List.range table.width).filter fun c ↦ !table.links.pointers.contains c).map fun c ↦
      mleK (cols.getD c #[]) point
  let eqQ := eqTable qPoint
  let slices := (List.range 64).map fun b ↦
    sumE (columns.zipIdx.map fun (c, q) ↦ eqQ.getD q 0 * c.slices.getD b 0)
  Script.sendPackedS (values ++ slices)
  return ⟨chi, qPoint, columns⟩

end LeanVM.Prover

end
