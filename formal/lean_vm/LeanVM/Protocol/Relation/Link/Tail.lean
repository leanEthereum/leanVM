/-
  LeanVM.Protocol.Relation.Link.Tail

  `verify_link`'s last step, after the pointer columns' sum-check, as a packed read, a check and a
  return of pure functions of the message.
-/

module

public import LeanVM.Protocol.Link.Skeleton

/-!
# The link's tail

`linkTail` (`Link/Skeleton.lean`) reads the values at the row point and the bit-slices in one packed
message, computes from them the summand at the final point (`last`) and the `LinkEnd`, checks
`last` against the claim and returns the `LinkEnd`. `tailValues` copies those `let`s as one pure
function of the message, and `linkTail_eq` checks by `rfl` that `linkTail` is the packed read, the
check and the return (`tailLen` is the message's length).
-/

namespace LeanVM.Protocol.Link

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The packed message's length, `verifyLink`'s `nValues + kBits`. -/
def tailLen (layout : Layout) : ℕ :=
  let tables := layout.tables
  let pointers := tables.map (·.links.pointers)
  let nonPointer := fun (t : ℕ) (table : Table) ↦
    (List.range table.width).filter fun c ↦ !(pointers.getD t []).contains c
  let nValues := (tables.zipIdx.map fun (table, t) ↦ (nonPointer t table).length).sum
  nValues + kBits

/-- What `linkTail` computes from its packed message: the summand at the final point (`last`)
and the `LinkEnd` (`linkTail`'s `let`s, copied). -/
def tailValues (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E) (m1 : E)
    (fresh : List E) (split : Split) (chi qPoint : List E)
    (message : List E) : E × LinkEnd :=
  let tables := layout.tables
  let heights := layout.tableLogHeights
  let rows := layout.tableRows
  let width := chunks.width
  let d := chunks.d
  let pointers := tables.map (·.links.pointers)
  let nPointers := (pointers.map List.length).sum
  let maxShift := tables.foldl (fun m t ↦ max m t.links.maxShift) 0
  let nRows := heights.foldl max 0
  let theta := theta0 :: drawn.take (nTables - 1)
  let drawn := drawn.drop (nTables - 1)
  let gammaState := drawn.take 2
  let drawn := drawn.drop 2
  -- On the address, the word and the presence coordinate; a word `lo + y·hi` takes `γ_word·y` on
  -- its high limb.
  let g := drawn.take 3
  let drawn := drawn.drop 3
  let gammaMem : List E := [g.getD 0 0, g.getD 1 0, g.getD 1 0 * eY, g.getD 2 0]
  let (mu, drawn) := tables.foldl (fun (acc : List (List E) × List E) t ↦
    (acc.1 ++ [acc.2.take t.links.memory.length], acc.2.drop t.links.memory.length)) ([], drawn)
  let alpha := drawn.take bytecodeSlotBits
  let drawn := drawn.drop bytecodeSlotBits
  let etaMem := drawn.getD 0 0
  let etaBc := drawn.getD 1 0
  let drawn := drawn.drop 2
  -- The mirror certificates' coefficients: pointer column `q`'s chunk `c` takes `ε_q·ν_c`.
  let eps := drawn.take nPointers
  let drawn := drawn.drop nPointers
  let tau := drawn.take nRows
  let drawn := drawn.drop nRows
  let zeta := drawn.take width
  let nu := (drawn.drop width).take d
  let slot := eqKernel alpha
  -- `ŝ_γ = 1 + γ_pc·pc + γ_fp·fp`: the constant component counts the rows on each cycle.
  let stateGamma := fun (pc fp : E) ↦ 1 + gammaState.getD 0 0 * pc + gammaState.getD 1 0 * fp
  -- The index side, then the memory term at `r` and the fresh coefficients.
  let cert := fresh.getD 0 0
  let jump := fresh.drop 1
  let below := fun (k : ℕ) ↦ prodE ((r.drop (min k width)).map (1 + ·))
  let yMem := gammaMem.getD 0 0 * indexMle r + gammaMem.getD 3 0 * below layout.logMemory +
    gammaMem.getD 1 0 * m1
  let bytecodePoint := r.take layout.logBytecode
  -- The program side's targets at `r`: `X_ω` on the rows' weight, `P_fp` on `ω·fp`. Both weigh an
  -- instruction's slots by its opcode.
  let weights := slotWeights tables slot (gammaMem.getD 0 0, gammaMem.getD 1 0) mu etaMem etaBc
  let (program, frameProgram) := (List.range nTables).foldl (fun (acc : E × E) t ↦
    let omega := weights.omega.getD t []
    let pc := weights.pc.getD t []
    let frame := weights.frame.getD t []
    let slots := split.slots.getD t []
    let pcs := split.pc.getD t []
    let program := acc.1 + omega.getD 3 0 * gpow t * split.count.getD t 0
    ((List.range (2 ^ bytecodeSlotBits - 4)).map (· + 4)).foldl (fun (acc : E × E) s ↦
      (acc.1 + (omega.getD s 0 * slots.getD s 0 + pc.getD s 0 * pcs.getD s 0),
        acc.2 + frame.getD s 0 * slots.getD s 0)) (program, acc.2)) (0, 0)
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
  let belowMem := below layout.logMemory
  (last, {
    memoryPoint := r.take layout.logMemory
    memoryScales := (belowMem, eY * belowMem)
    memoryValue := m1
    columns := rowSide.columns
    ring := ⟨rowSide.pieces, slices⟩
    bytecodePoint := bytecodePoint })


/-- **`linkTail` is a packed read, a check and a return**, by `rfl`. -/
theorem linkTail_eq (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E) (m1 : E)
    (fresh : List E) (split : Split) (chi qPoint : List E) (claim : E) :
    linkTail layout chunks theta0 drawn r m1 fresh split chi qPoint claim =
      (VerifierProgram.readScalarsPacked (tailLen layout) >>= fun message ↦
        VerifierProgram.require
            ((tailValues layout chunks theta0 drawn r m1 fresh split chi qPoint message).1 = claim) >>=
          fun _ ↦ pure (tailValues layout chunks theta0 drawn r m1 fresh split chi qPoint message).2) :=
  rfl

end

end LeanVM.Protocol.Link
