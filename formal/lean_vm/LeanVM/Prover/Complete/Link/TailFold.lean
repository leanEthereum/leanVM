/-
  LeanVM.Prover.Complete.Link.TailFold

  `tailOut` through its challenges and its row side as named functions.
-/

module

public import LeanVM.Prover.Complete.Link.TailShape

/-!
# The link's tail, its row side named

`verCh`: the challenges as `linkTail` splits them; `rowSideOf`: its fold over the tables, given the
challenges and the scalars it reads; `tailVia`: `tailOut` through them, equal by `rfl`
(`tailOut_eq_tailVia`).
-/

@[expose] public section

namespace LeanVM.Protocol.Verifier.Defers

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Prover

/-- The challenges as `linkTail` splits them. -/
def verCh (layout : Layout) (y : LinkPre) : LinkChallenges :=
  let tables := layout.tables
  let heights := layout.tableLogHeights
  let chunks := y.chunks
  let width := chunks.width
  let d := chunks.d
  let pointers := tables.map (·.links.pointers)
  let nPointers := (pointers.map List.length).sum
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
  ⟨theta, gammaState, gammaMem, mu, alpha, slot, etaMem, etaBc, eps, tau, zeta, nu⟩

/-- **The verifier's row side** (`linkTail`'s fold over the tables), its challenges `ch`. -/
def rowSideOf (layout : Layout) (ch : LinkChallenges) (chi jump : List E)
    (eqZetaR shiftZetaR xBc pFp yMem m1 eq0R : E) (eqQ : List E) (maxShift : ℕ) (sent0 : List E) :
    LinkRowSide :=
  let tables := layout.tables
  let heights := layout.tableLogHeights
  let rows := layout.tableRows
  let pointers := tables.map (·.links.pointers)
  let theta := ch.theta
  let gammaState := ch.gammaState
  let gammaMem := ch.gammaMem
  let mu := ch.mu
  let slot := ch.slot
  let etaMem := ch.etaMem
  let etaBc := ch.etaBc
  let eps := ch.eps
  let tau := ch.tau
  let stateGamma := fun (pc fp : E) ↦ 1 + gammaState.getD 0 0 * pc + gammaState.getD 1 0 * fp
  let nonPointer := fun (t : ℕ) (table : Table) ↦
    (List.range table.width).filter fun c ↦ !(pointers.getD t []).contains c
tables.zipIdx.foldl (fun (acc : LinkRowSide) (table, t) ↦
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
    ⟨0, List.replicate maxShift 0, 0, 0, [], 0, [], sent0⟩

/-- The non-pointer values the message carries, `linkTail`'s `nValues`. -/
def tailNValues (layout : Layout) : ℕ :=
  let tables := layout.tables
  let pointers := tables.map (·.links.pointers)
  let nonPointer := fun (t : ℕ) (table : Table) ↦
    (List.range table.width).filter fun c ↦ !(pointers.getD t []).contains c
  (tables.zipIdx.map fun (table, t) ↦ (nonPointer t table).length).sum

/-- The row side `linkTail` folds, through `rowSideOf`. -/
def tailRowSide (layout : Layout) (y : LinkPre) (ps : E × E) (chi qPoint message : List E) :
    LinkRowSide :=
  let ch := verCh layout y
  let width := y.chunks.width
  let r := y.r
  let below := fun (k : ℕ) ↦ prodE ((r.drop (min k width)).map (1 + ·))
  let yMem := ch.gammaMem.getD 0 0 * indexMle r + ch.gammaMem.getD 3 0 * below layout.logMemory +
    ch.gammaMem.getD 1 0 * y.m1
  let belowBc := below layout.logBytecode
  let xBc := ch.etaBc * ch.slot.getD 1 0 * indexMle r + belowBc * (ch.etaBc * ch.slot.getD 2 0 + ps.1)
  let pFp := belowBc * ps.2
  rowSideOf layout ch chi (y.fresh.drop 1) (eqEval ch.zeta r) (linkShiftEq ch.zeta r) xBc pFp yMem
    y.m1 (below 0) (eqKernel qPoint) (layout.tables.foldl (fun m t ↦ max m t.links.maxShift) 0)
    (message.take (tailNValues layout))

/-- `tailOut` through `verCh` and `rowSideOf`. -/
def tailVia (layout : Layout) (y : LinkPre) (ps : E × E) (chi qPoint message : List E) :
    E × LinkEnd :=
  let ch := verCh layout y
  let rs := tailRowSide layout y ps chi qPoint message
  let r := y.r
  let below := fun (k : ℕ) ↦ prodE ((r.drop (min k y.chunks.width)).map (1 + ·))
  let maxShift := layout.tables.foldl (fun m t ↦ max m t.links.maxShift) 0
  let slices := message.drop (tailNValues layout)
  let functionals := Functionals.new y.chunks r maxShift
  let values := functionals.values y.chunks slices
  let certs := ch.nu.map fun n ↦ y.fresh.getD 0 0 * rs.certWeight * n
  (functionals.summand rs.coef rs.shifts values certs + prodE (qPoint.map (1 + ·)) * rs.base,
    { memoryPoint := r.take layout.logMemory
      memoryScales := (below layout.logMemory, eY * below layout.logMemory)
      memoryValue := y.m1
      columns := rs.columns
      ring := ⟨rs.pieces, slices⟩
      bytecodePoint := r.take layout.logBytecode })

theorem tailOut_eq_tailVia (layout : Layout) (y : LinkPre) (ps : E × E) (chi qPoint message : List E) :
    tailOut layout y ps chi qPoint message = tailVia layout y ps chi qPoint message :=
  rfl

/-- **The verifier's challenges are the prover's** (`LinkChallenges.ofDraw`). -/
theorem verCh_eq (layout : Layout) (y : LinkPre) (h : layout.tables = tables) :
    verCh layout y = LinkChallenges.ofDraw tables (layout.tableLogHeights.foldl max 0) y.chunks.width
      y.chunks.d y.theta0 y.drawn := by
  unfold verCh LinkChallenges.ofDraw
  rw [h]
  simp only [List.map_map, Function.comp_def]

end LeanVM.Protocol.Verifier.Defers

end
