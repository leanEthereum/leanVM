/-
  LeanVM.Protocol.Relation.Link.Fold

  `tailValues` in named pieces: the drawn challenges' slices, the index side's scalars at `r`, the
  row side's step and the summand at the final point, equal to `tailValues` by `rfl`.
-/

module

public import LeanVM.Protocol.Relation.Link.Tail

/-!
# The link's tail in pieces

`tailValues` (`Link/Tail.lean`) copies `verify_link`'s `let`s as one term. Here the same term is cut
into named functions, so that facts about one piece are stated once:

* `linkCh`: the drawn challenges `θ`, `γ_state`, `γ_mem`, `μ`, `α`, `η_mem`, `η_bc`, `ε`, `τ`, `ζ`,
  `ν`, sliced as `verify_link` slices them;
* `IdxAt`, `idxAt`: the scalars the row side reads of the index point `r` (`eq(0, r)`, `eq(ζ, r)`,
  the shift, `X_bc`, `P_fp`, `y_mem`, the memory term `m1`);
* `rowStep`: one table of the row side's fold;
* `lastOf`: the summand at the final point from the fold's result and the bit-slices.

`tailValuesF` assembles them, and `tailValues_eq_F` checks by `rfl` that it is `tailValues`.
-/

namespace LeanVM.Protocol.Link

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The link's drawn challenges, named. -/
structure LinkCh where
  theta : List E
  gammaState : List E
  gammaMem : List E
  mu : List (List E)
  alpha : List E
  etaMem : E
  etaBc : E
  eps : List E
  tau : List E
  zeta : List E
  nu : List E

/-- `verify_link`'s slices of `θ_0` and the drawn challenges. -/
def linkCh (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn : List E) : LinkCh :=
  let tables := layout.tables
  let heights := layout.tableLogHeights
  let width := chunks.width
  let d := chunks.d
  let pointers := tables.map (·.links.pointers)
  let nPointers := (pointers.map List.length).sum
  let nRows := heights.foldl max 0
  let theta := theta0 :: drawn.take (nTables - 1)
  let drawn := drawn.drop (nTables - 1)
  let gammaState := drawn.take 2
  let drawn := drawn.drop 2
  let g := drawn.take 3
  let drawn := drawn.drop 3
  let gammaMem : List E := [g.getD 0 0, g.getD 1 0, g.getD 1 0 * eY, g.getD 2 0]
  let mud := tables.foldl (fun (acc : List (List E) × List E) t ↦
    (acc.1 ++ [acc.2.take t.links.memory.length], acc.2.drop t.links.memory.length)) ([], drawn)
  let mu := mud.1
  let drawn := mud.2
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
  ⟨theta, gammaState, gammaMem, mu, alpha, etaMem, etaBc, eps, tau, zeta, nu⟩

/-- `ŝ_γ = 1 + γ_pc·pc + γ_fp·fp`. -/
def LinkCh.stateGamma (ch : LinkCh) (pc fp : E) : E :=
  1 + ch.gammaState.getD 0 0 * pc + ch.gammaState.getD 1 0 * fp

/-- The scalars the row side reads of the index point. -/
structure IdxAt where
  eq0R : E
  eqZetaR : E
  shiftZetaR : E
  xBc : E
  pFp : E
  yMem : E
  m1 : E

/-- `Π_{h ≥ k} (1 + r_h)`, `verify_link`'s `below`. -/
def belowAt (chunks : Chunks) (r : List E) (k : ℕ) : E :=
  prodE ((r.drop (min k chunks.width)).map (1 + ·))

/-- The program side's sums at `r` (`program`, `frame_program`). -/
def programSums (layout : Layout) (ch : LinkCh) (split : Split) : E × E :=
  let tables := layout.tables
  let slot := eqKernel ch.alpha
  let weights := slotWeights tables slot (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0) ch.mu
    ch.etaMem ch.etaBc
  (List.range nTables).foldl (fun (acc : E × E) t ↦
    let omega := weights.omega.getD t []
    let pc := weights.pc.getD t []
    let frame := weights.frame.getD t []
    let slots := split.slots.getD t []
    let pcs := split.pc.getD t []
    let program := acc.1 + omega.getD 3 0 * gpow t * split.count.getD t 0
    ((List.range (2 ^ bytecodeSlotBits - 4)).map (· + 4)).foldl (fun (acc : E × E) s ↦
      (acc.1 + (omega.getD s 0 * slots.getD s 0 + pc.getD s 0 * pcs.getD s 0),
        acc.2 + frame.getD s 0 * slots.getD s 0)) (program, acc.2)) (0, 0)

/-- The index side's scalars at `r`. -/
def idxAt (layout : Layout) (chunks : Chunks) (ch : LinkCh) (r : List E) (m1 : E)
    (split : Split) : IdxAt :=
  let slot := eqKernel ch.alpha
  let yMem := ch.gammaMem.getD 0 0 * indexMle r +
    ch.gammaMem.getD 3 0 * belowAt chunks r layout.logMemory + ch.gammaMem.getD 1 0 * m1
  let ps := programSums layout ch split
  let belowBc := belowAt chunks r layout.logBytecode
  let xBc := ch.etaBc * slot.getD 1 0 * indexMle r + belowBc * (ch.etaBc * slot.getD 2 0 + ps.1)
  let pFp := belowBc * ps.2
  ⟨belowAt chunks r 0, eqEval ch.zeta r, linkShiftEq ch.zeta r, xBc, pFp, yMem, m1⟩

/-- Table `t`'s non-pointer columns, as `verify_link`'s `nonPointer` lists them. -/
def nonPointerOf (layout : Layout) (t : ℕ) (table : Table) : List ℕ :=
  (List.range table.width).filter fun c ↦ !((layout.tables.map (·.links.pointers)).getD t []).contains c

/-- One pointer column of the row side's fold. -/
def ptrStep (layout : Layout) (ch : LinkCh) (a : IdxAt) (eqQ point : List E) (corner omega act sHat
    sNext : E) (table : Table) (t : ℕ) (col : ℕ → E) : LinkRowSide → ℕ × ℕ → LinkRowSide :=
  fun (acc : LinkRowSide) (pointer, k) ↦
    let links := table.links
    let muT := ch.mu.getD t []
    let state := links.stateLink
    let gateOf := fun (a : Access) ↦ (a.gate.map col).getD 1
    let e := eqQ.getD acc.q 0 * corner
    let (coef, shifts) :=
      match k with
      | 0 => (acc.coef + e * act * (a.eqZetaR * sHat + a.shiftZetaR * sNext), acc.shifts)
      | 1 => (acc.coef + e * omega * (a.xBc + col state.fp * a.pFp), acc.shifts)
      | _ =>
        let coef := (links.memory.zip muT).foldl (fun coef (access, m) ↦
          access.reads.foldl (fun coef read ↦
            match read with
            | .word p scale =>
              if p = pointer then
                coef + e * omega * ch.etaMem * m * ch.gammaMem.getD 1 0 * a.m1 * scale.evaluate col
              else coef
            | _ => coef) coef) acc.coef
        ((links.memory.zip muT).filter (·.1.pointer = pointer)).foldl
          (fun (cs : E × List E) (access, m) ↦
            let c := e * omega * gateOf access * ch.etaMem * m * a.yMem
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
      certWeight := acc.certWeight + e * omega * ch.eps.getD acc.q 0
      pieces := acc.pieces ++ [piece]
      q := acc.q + 1 }

/-- Table `t`'s base terms: the payload under `ω`, and `JUMP`'s identities. -/
def tableBaseOf (ch : LinkCh) (a : IdxAt) (jump : List E) (point : List E) (height : ℕ)
    (omega : E) (table : Table) (t : ℕ) (values : List E) : E :=
  let col := fun (c : ℕ) ↦ values.getD c 0
  let links := table.links
  let muT := ch.mu.getD t []
  let slot := eqKernel ch.alpha
  let accessValue := fun (a : Access) ↦
    ch.gammaMem.getD 0 0 * a.address.evaluate col + ch.gammaMem.getD 3 0 +
      ch.gammaMem.getD 1 0 * a.value.evaluate col
  let bc := links.bytecodeLink
  let rBc := slot.getD 1 0 * col bc.pc + slot.getD 2 0 + slot.getD 3 0 * gpow bc.opcode +
    sumE (bc.operands.map fun (slots, f) ↦ slot.getD (slots.headD 0) 0 * f.evaluate col)
  let gateOf := fun (a : Access) ↦ (a.gate.map col).getD 1
  let memory := sumE ((links.memory.zip muT).map fun (a, m) ↦ m * gateOf a * accessValue a)
  let tableBase := omega * a.eq0R * (ch.etaMem * memory + ch.etaBc * rBc)
  if 0 < table.nConstraints then
    let identities := table.constraints values
    let eqTau := eqEval (ch.tau.take height) point
    tableBase + eqTau * sumE (List.zipWith (· * ·) jump identities)
  else tableBase

/-- One table of the row side's fold. -/
def rowStep (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump eqQ chi : List E) :
    LinkRowSide → Table × ℕ → LinkRowSide :=
  fun (acc : LinkRowSide) (table, t) ↦
    let height := layout.tableLogHeights.getD t 0
    let tableRows := layout.tableRows.getD t 0
    let point := chi.take height
    let corner := prodE ((chi.drop height).map (1 + ·))
    let columns := nonPointerOf layout t table
    let sent := columns.zip (acc.sent.take columns.length)
    let values := (List.range table.width).map fun c ↦ (sent.lookup c).getD 0
    let col := fun (c : ℕ) ↦ values.getD c 0
    let state := table.links.stateLink
    let omega := omegaAt (ch.theta.getD t 0) (ch.tau.take height) point tableRows
    let act := lessThan point tableRows
    let sHat := ch.stateGamma (col state.pc) (col state.fp)
    let sNext := ch.stateGamma (state.next.1.evaluate col) (state.next.2.evaluate col)
    let tableBase := tableBaseOf ch a jump point height omega table t values
    let acc := (((layout.tables.map (·.links.pointers)).getD t []).zipIdx.foldl
      (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col))
      { acc with base := acc.base + corner * tableBase, sent := acc.sent.drop columns.length }
    { acc with columns := acc.columns ++ [(point, sent)] }

/-- The row side's start: no coefficients, the values to read. -/
def rowStart (layout : Layout) (message : List E) : LinkRowSide :=
  ⟨0, List.replicate (layout.tables.foldl (fun m t ↦ max m t.links.maxShift) 0) 0, 0, 0, [], 0, [],
    message.take ((layout.tables.zipIdx.map fun (table, t) ↦ (nonPointerOf layout t table).length).sum)⟩

/-- The row side after every table. -/
def rowSideOf (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump eqQ chi message : List E) :
    LinkRowSide :=
  layout.tables.zipIdx.foldl (rowStep layout ch a jump eqQ chi) (rowStart layout message)

/-- The summand at the final point, from the row side and the bit-slices. -/
def lastOf (layout : Layout) (chunks : Chunks) (ch : LinkCh) (r : List E) (cert : E)
    (qPoint slices : List E) (rs : LinkRowSide) : E :=
  let functionals := Functionals.new chunks r (layout.tables.foldl (fun m t ↦ max m t.links.maxShift) 0)
  let values := functionals.values chunks slices
  let eq0Q := prodE (qPoint.map (1 + ·))
  let certs := ch.nu.map fun n ↦ cert * rs.certWeight * n
  functionals.summand rs.coef rs.shifts values certs + eq0Q * rs.base

/-- The values the packed message holds before the bit-slices. -/
def nValuesOf (layout : Layout) : ℕ :=
  (layout.tables.zipIdx.map fun (table, t) ↦ (nonPointerOf layout t table).length).sum

/-- `tailValues` from its pieces. -/
def tailValuesF (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E) (m1 : E)
    (fresh : List E) (split : Split) (chi qPoint : List E) (message : List E) : E × LinkEnd :=
  let ch := linkCh layout chunks theta0 drawn
  let a := idxAt layout chunks ch r m1 split
  let rs := rowSideOf layout ch a (fresh.drop 1) (eqKernel qPoint) chi message
  let slices := message.drop (nValuesOf layout)
  let belowMem := belowAt chunks r layout.logMemory
  (lastOf layout chunks ch r (fresh.getD 0 0) qPoint slices rs, {
    memoryPoint := r.take layout.logMemory
    memoryScales := (belowMem, eY * belowMem)
    memoryValue := m1
    columns := rs.columns
    ring := ⟨rs.pieces, slices⟩
    bytecodePoint := r.take layout.logBytecode })

set_option maxRecDepth 100000 in
/-- **`tailValues` is its pieces**, by `rfl`. -/
theorem tailValues_eq_F (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E)
    (m1 : E) (fresh : List E) (split : Split) (chi qPoint message : List E) :
    tailValues layout chunks theta0 drawn r m1 fresh split chi qPoint message =
      tailValuesF layout chunks theta0 drawn r m1 fresh split chi qPoint message :=
  rfl

end

end LeanVM.Protocol.Link
