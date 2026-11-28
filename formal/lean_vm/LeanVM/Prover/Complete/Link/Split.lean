/-
  LeanVM.Prover.Complete.Link.Split

  The link's verifier and its honest prover, each split at the same points: the prefix up to the
  fresh coefficients, the row rounds, the pointer-column rounds, the message and the terminal check.
-/

module

public import LeanVM.Prover.Complete.Prods
public import LeanVM.Prover.Complete.Prefix
public import LeanVM.Protocol.Verifier.Defers

/-!
# The link, split

`linkSufOf_eq`: the verifier's link after the program's split is the row rounds, the pointer-column
rounds, the packed message, then `linkTail` (the terminal check and what the link returns), a
function of the rounds' points and final claim and of the message. `linkProve_eq`: the honest prover
is its prefix (`linkProvePre`: the challenges, the index side, `M_1`, the fresh coefficients) then
its suffix (`linkProveSuf`).
-/

@[expose] public section

namespace LeanVM.Protocol.Verifier.Defers

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

/-- The pointer columns' count. -/
def linkNPointers (layout : Layout) : ℕ :=
  ((layout.tables.map (·.links.pointers)).map List.length).sum

/-- The non-pointer values the link's message carries. -/
def linkNValues (layout : Layout) : ℕ :=
  (layout.tables.zipIdx.map fun (table, t) ↦ ((List.range table.width).filter fun c ↦
    !((layout.tables.map (·.links.pointers)).getD t []).contains c).length).sum

/-- **The link's terminal check and its return**, after the pointer-column rounds' point `qPoint`
and final claim `claim`, the row rounds' point `chi`, and the message (`linkSufOf`). -/
def linkTail (layout : Layout) (y : LinkPre) (ps : E × E) (chi qPoint : List E) (claim : E)
    (message : List E) : VerifierProgram LinkEnd := do
  let tables := layout.tables
  let heights := layout.tableLogHeights
  let rows := layout.tableRows
  let chunks := y.chunks
  let width := chunks.width
  let d := chunks.d
  let pointers := tables.map (·.links.pointers)
  let nPointers := (pointers.map List.length).sum
  let maxShift := tables.foldl (fun m t ↦ max m t.links.maxShift) 0
  let nRows := heights.foldl max 0
  let theta := y.theta0 :: y.drawn.take (nTables - 1)
  let drawn := y.drawn.drop (nTables - 1)
  let gammaState := drawn.take 2
  let drawn := drawn.drop 2
  let g := drawn.take 3
  let drawn := drawn.drop 3
  let gammaMem : List E := [g.getD 0 0, g.getD 1 0, g.getD 1 0 * eY, g.getD 2 0]
  let md := tables.foldl (fun (acc : List (List E) × List E) t ↦
    (acc.1 ++ [acc.2.take t.links.memory.length], acc.2.drop t.links.memory.length)) ([], drawn)
  let mu := md.1
  let drawn := md.2
  let alpha := drawn.take bytecodeSlotBits
  let drawn := drawn.drop bytecodeSlotBits
  let etaMem := drawn.getD 0 0
  let etaBc := drawn.getD 1 0
  let drawn := drawn.drop 2
  let eps := drawn.take nPointers
  let drawn := drawn.drop nPointers
  let tau := drawn.take nRows
  let drawn := drawn.drop nRows
  let zeta := drawn.take width
  let nu := (drawn.drop width).take d
  let slot := eqKernel alpha
  let stateGamma := fun (pc fp : E) ↦ 1 + gammaState.getD 0 0 * pc + gammaState.getD 1 0 * fp
  let r := y.r
  let m1 := y.m1
  let fresh := y.fresh
  let cert := fresh.getD 0 0
  let jump := fresh.drop 1
  let below := fun (k : ℕ) ↦ prodE ((r.drop (min k width)).map (1 + ·))
  let yMem := gammaMem.getD 0 0 * indexMle r + gammaMem.getD 3 0 * below layout.logMemory +
    gammaMem.getD 1 0 * m1
  let bytecodePoint := r.take layout.logBytecode
  let (program, frameProgram) := ps
  let belowBc := below layout.logBytecode
  let xBc := etaBc * slot.getD 1 0 * indexMle r + belowBc * (etaBc * slot.getD 2 0 + program)
  let pFp := belowBc * frameProgram
  let eq0R := below 0
  -- The state identity's weights at `r`: on `A` and on `B`.
  let eqZetaR := eqEval zeta r
  let shiftZetaR := linkShiftEq zeta r
  -- The row side.
  let eqQ := eqKernel qPoint
  -- The values at the row point, then the pointer words' bit-slices, one message read eight
  -- scalars a permutation.
  let nonPointer := fun (t : ℕ) (table : Table) ↦
    (List.range table.width).filter fun c ↦ !(pointers.getD t []).contains c
  let nValues := (tables.zipIdx.map fun (table, t) ↦ (nonPointer t table).length).sum
  let slices := message.drop nValues
  -- What the values make of the summand at the row point.
  let rowSide := tables.zipIdx.foldl (fun (acc : LinkRowSide) (table, t) ↦
    let height := heights.getD t 0
    let tableRows := rows.getD t 0
    let point := chi.take height
    let corner := prodE ((chi.drop height).map (1 + ·))
    let columns := nonPointer t table
    let sent := columns.zip (acc.sent.take columns.length)
    let values := (List.range table.width).map fun c ↦ (sent.lookup c).getD 0
    let col := fun (c : ℕ) ↦ values.getD c 0
    let links := table.links
    let muT := mu.getD t []
    let omega := omegaAt (theta.getD t 0) (tau.take height) point tableRows
    let act := lessThan point tableRows
    let state := links.stateLink
    let sHat := stateGamma (col state.pc) (col state.fp)
    let sNext := stateGamma (state.next.1.evaluate col) (state.next.2.evaluate col)
    -- The base terms: the payload under ω, and `JUMP`'s identities on every row. An access's
    -- committed part: its reads are the pointers' coefficients.
    let accessValue := fun (a : Access) ↦
      gammaMem.getD 0 0 * a.address.evaluate col + gammaMem.getD 3 0 +
        gammaMem.getD 1 0 * a.value.evaluate col
    let bc := links.bytecodeLink
    let rBc := slot.getD 1 0 * col bc.pc + slot.getD 2 0 + slot.getD 3 0 * gpow bc.opcode +
      sumE (bc.operands.map fun (slots, f) ↦ slot.getD (slots.headD 0) 0 * f.evaluate col)
    let gateOf := fun (a : Access) ↦ (a.gate.map col).getD 1
    let memory := sumE ((links.memory.zip muT).map fun (a, m) ↦ m * gateOf a * accessValue a)
    let tableBase := omega * eq0R * (etaMem * memory + etaBc * rBc)
    let tableBase :=
      if 0 < table.nConstraints then
        let identities := table.constraints values
        let eqTau := eqEval (tau.take height) point
        tableBase + eqTau * sumE (List.zipWith (· * ·) jump identities)
      else tableBase
    -- The pointer columns' coefficients.
    let acc := (pointers.getD t []).zipIdx.foldl (fun (acc : LinkRowSide) (pointer, k) ↦
      let e := eqQ.getD acc.q 0 * corner
      let (coef, shifts) :=
        match k with
        | 0 => (acc.coef + e * act * (eqZetaR * sHat + shiftZetaR * sNext), acc.shifts)
        | 1 => (acc.coef + e * omega * (xBc + col state.fp * pFp), acc.shifts)
        | _ =>
          -- The word reads at this pointer weigh `word(r)`, the memory term.
          let coef := (links.memory.zip muT).foldl (fun coef (access, m) ↦
            access.reads.foldl (fun coef read ↦
              match read with
              | .word p scale =>
                if p = pointer then
                  coef + e * omega * etaMem * m * gammaMem.getD 1 0 * m1 * scale.evaluate col
                else coef
              | _ => coef) coef) acc.coef
          ((links.memory.zip muT).filter (·.1.pointer = pointer)).foldl
            (fun (cs : E × List E) (access, m) ↦
              let c := e * omega * gateOf access * etaMem * m * yMem
              match access.shift with
              | 0 => (cs.1 + c, cs.2)
              | s + 1 => (cs.1, addAtSlot cs.2 s c)) (coef, acc.shifts)
      let piece : RingPiece :=
        { placement :=
            some ((layout.placements.getD (globalColumnBases.getD t 0 + pointer) none).getD default)
          point := point
          scale := eqQ.getD acc.q 0 }
      { acc with
        coef := coef
        shifts := shifts
        certWeight := acc.certWeight + e * omega * eps.getD acc.q 0
        pieces := acc.pieces ++ [piece]
        q := acc.q + 1 })
      { acc with base := acc.base + corner * tableBase, sent := acc.sent.drop columns.length }
    { acc with columns := acc.columns ++ [(point, sent)] })
    ⟨0, List.replicate maxShift 0, 0, 0, [], 0, [], message.take nValues⟩
  let functionals := Functionals.new chunks r maxShift
  let values := functionals.values chunks slices
  let eq0Q := prodE (qPoint.map (1 + ·))
  let certs := nu.map fun n ↦ cert * rowSide.certWeight * n
  let last := functionals.summand rowSide.coef rowSide.shifts values certs + eq0Q * rowSide.base
  VerifierProgram.require (last = claim)
  let belowMem := below layout.logMemory
  return {
    memoryPoint := r.take layout.logMemory
    memoryScales := (belowMem, eY * belowMem)
    memoryValue := m1
    columns := rowSide.columns
    ring := ⟨rowSide.pieces, slices⟩
    bytecodePoint := bytecodePoint }


/-- **The link after the program's split, split**: the row rounds, the pointer-column rounds, the
message, `linkTail`. -/
theorem linkSufOf_eq (layout : Layout) (y : LinkPre) (ps : E × E) :
    linkSufOf layout y ps =
      sumcheck y.claim (roundCoefficients y.chunks.d).1
          (List.replicate (layout.tableLogHeights.foldl max 0) none) >>= fun x ↦
        sumcheck x.2 (roundCoefficients y.chunks.d).2
          (List.replicate (log2Ceil (linkNPointers layout)) none) >>= fun z ↦
        VerifierProgram.readScalarsPacked (linkNValues layout + kBits) >>= fun message ↦
        linkTail layout y ps x.1 z.1 z.2 message := by
  unfold linkSufOf linkTail
  rfl

end LeanVM.Protocol.Verifier.Defers

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-- What the honest link prover holds after its prefix: the challenges, the index point, the index
side's folded tables, `M_1` and the fresh coefficients. -/
structure LinkProverPre where
  ch : LinkChallenges
  r : List E
  index : Prods
  m1 : E
  fresh : List E

/-- **The honest link prover's prefix**: the challenges, the index side, `M_1`, the fresh
coefficients (`linkProve`). -/
def linkProvePre (W : Witness) : Script LinkProverPre := do
  let layout := W.layout
  let heights := layout.tableLogHeights
  let chunks := W.chunks
  let (width, d) := (chunks.width, chunks.d)
  let nRows := heights.foldl max 0
  Script.grindBits (grindingBits (max (nRows + 3 + bytecodeSlotBits) (width + 1)))
  let theta0 ← Script.sampleE
  let drawn ← Script.samplePackedS (packedChallenges tables nRows width)
  let ch := LinkChallenges.ofDraw tables nRows width d theta0 drawn
  let (r, index) ← prodsSumcheck 3 width (indexProds W ch)
  let below := fun (k : ℕ) ↦ prodE ((r.drop (min k width)).map (1 + ·))
  let rMem := r.take layout.logMemory
  let m1 := (mleK (W.cols.getD memory0 #[]) rMem + eY * mleK (W.cols.getD memory1 #[]) rMem) *
    below layout.logMemory
  Script.sendE m1
  let fresh ← Script.samplePackedS 5
  return ⟨ch, r, index, m1, fresh⟩

/-- The row rounds' inputs the honest prover reads after its prefix. -/
def linkRowInputs (W : Witness) (x : LinkProverPre) : RowInputs :=
  let width := W.chunks.width
  let below := fun (k : ℕ) ↦ prodE ((x.r.drop (min k width)).map (1 + ·))
  let maxShift := tables.foldl (fun m t ↦ max m t.links.maxShift) 0
  { ch := x.ch, functionals := Functionals.new W.chunks x.r maxShift, maxShift := maxShift,
    m1 := x.m1, cert := x.fresh.getD 0 0, jump := x.fresh.drop 1, yMem := x.index.at 3,
    xBc := x.index.at 5, pFp := x.index.at 12, eqZeta := x.index.at 6,
    shiftZeta := x.index.at 7, eq0 := below 0 }

/-- The row rounds' initial state. -/
def linkRowStart (W : Witness) (x : LinkProverPre) : RowState :=
  let heights := W.layout.tableLogHeights
  Array.ofFn (n := nTables) fun t ↦
    let (prods, columnTerms) := rowProds W (linkRowInputs W x) t (pointerStarts.getD t 0)
    ⟨prods, heights.getD t 0, 0, 1, columnTerms⟩

/-- The pointer columns at the row point. -/
def linkColumns (W : Witness) (x : LinkProverPre) (chi : List E) (st : RowState) : List ColumnAt :=
  (List.range nTables).flatMap fun t ↦
    columnsAt W (linkRowInputs W x) t (pointerStarts.getD t 0) (st.getD t default) chi

/-- The base terms' total at the row point. -/
def linkBase (st : RowState) : E := sumE ((List.range nTables).map fun t ↦ baseAt (st.getD t default))

/-- The pointer-column rounds' sum. -/
def linkColumnProds (W : Witness) (x : LinkProverPre) (chi : List E) (st : RowState) : Prods :=
  let maxShift := tables.foldl (fun m t ↦ max m t.links.maxShift) 0
  columnProds W.chunks.d maxShift (linkRowInputs W x).functionals.mirrors (linkColumns W x chi st)
    (log2Ceil (linkColumns W x chi st).length) (linkBase st)

/-- The packed message: each table's non-pointer columns at its row point, then the pointer
columns' slices summed under `eq(q*, ·)`. -/
def linkMessage (W : Witness) (x : LinkProverPre) (chi qPoint : List E) (st : RowState) : List E :=
  let heights := W.layout.tableLogHeights
  let columns := linkColumns W x chi st
  let values := (List.range nTables).flatMap fun t ↦
    let table := tables.getD t default
    let cols := W.tableCols t
    let point := chi.take (heights.getD t 0)
    ((List.range table.width).filter fun c ↦ !table.links.pointers.contains c).map fun c ↦
      mleK (cols.getD c #[]) point
  let eqQ := eqTable qPoint
  let slices := (List.range 64).map fun b ↦
    sumE (columns.zipIdx.map fun (c, q) ↦ eqQ.getD q 0 * c.slices.getD b 0)
  values ++ slices

/-- **The honest link prover's suffix**: the row rounds, the pointer-column rounds, the message. -/
def linkProveSuf (W : Witness) (x : LinkProverPre) : Script LinkProverEnd := do
  let (rowCount, columnCount) := roundCoefficients W.chunks.d
  let nRows := W.layout.tableLogHeights.foldl max 0
  let (chi, st) ← sumcheckBy (rowRound rowCount) rowFold (List.replicate nRows none)
    (linkRowStart W x)
  let columns := linkColumns W x chi st
  let (qPoint, _) ← prodsSumcheck columnCount (log2Ceil columns.length)
    (linkColumnProds W x chi st)
  Script.sendPackedS (linkMessage W x chi qPoint st)
  return ⟨chi, qPoint, columns⟩

theorem linkProve_eq (W : Witness) : linkProve W = linkProvePre W >>= linkProveSuf W := by
  unfold linkProve linkProvePre linkProveSuf linkRowStart linkColumns linkColumnProds linkMessage
    linkBase linkRowInputs
  simp only [Complete.Keccak.sbind_eq, Script.pure_eq, Script.bind_assoc,
    Complete.Keccak.sret_bind]
  rfl

end LeanVM.Prover

end
