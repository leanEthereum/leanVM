/-
  LeanVM.Protocol.Link.Skeleton

  `verify_link` (`Statement/Verifier/Link.lean`'s `verifyLink`) cut at its prover messages and
  challenges: the index side's claim, the row phase and the terminal check as their own
  definitions, the program unchanged (`verifyLink_eq_linkSkeleton`, by `rfl`).
-/

module

public import Statement.Verifier.Lib

/-!
# `verify_link`, cut at its moves

The soundness argument (`LeanVM.Protocol.Link.Sound`) follows `verifyLink` move by move. Its pure
parts are named here, each a copy of `verifyLink`'s own `let`s (`Statement/Verifier/Link.lean`,
transcribing `crates/verifier/src/link.rs`'s `verify_link`), with the values the moves return as
arguments:

* `linkWidth`, `linkRows`, `linkQVars`, `linkDrawn`: the pointer width, the tallest table's row
  variables, the pointer columns' variables, the challenges drawn eight to a permutation after
  `θ_0`;
* `indexClaim`: the index side's claim, `eq(ζ, 0)·ŝ_init + eq(ζ, T)·ŝ_fin`, from the drawn
  challenges;
* `linkTail`: after the pointer columns' sum-check, the packed message of the values at the row
  point and the bit-slices, the terminal check and the `LinkEnd`;
* `linkRowPhase`: after the index side, the memory term `m1`, the five fresh coefficients, the
  program's split, the row and pointer-column sum-checks, then `linkTail`;
* `linkSkeleton`: the chunks, the grind, `θ_0`, the drawn challenges, the index side's sum-check,
  then `linkRowPhase`.

`verifyLink_eq_linkSkeleton` checks by `rfl` that nothing was changed: the copies unfold to
`verifyLink`'s own terms.
-/

namespace LeanVM.Protocol.Link

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The rows over all tables, the cycle count `T` (`verify_link`'s `cycles`). -/
def linkCycles (layout : Layout) : ℕ := layout.tableRows.foldl (· + ·) 0

/-- The pointer width `verify_link` reads its chunks at. -/
def linkWidth (layout : Layout) : ℕ :=
  pointerWidth layout.logMemory layout.logBytecode (linkCycles layout)

/-- The tallest table's row variables, `m` (`verify_link`'s `n_rows`). -/
def linkRows (layout : Layout) : ℕ := layout.tableLogHeights.foldl max 0

/-- The pointer columns' variables, `m_Q = ⌈log₂ Q⌉` (`verify_link`'s `q_vars`). -/
def linkQVars (layout : Layout) : ℕ :=
  log2Ceil ((layout.tables.map (·.links.pointers)).map List.length).sum

/-- The challenges drawn eight to a permutation after `θ_0` (`packed_challenges`). -/
def linkDrawn (layout : Layout) (chunks : Chunks) : ℕ :=
  packedChallenges layout.tables (linkRows layout) chunks.width

/-- The index side's claim, `eq(ζ, 0)·ŝ_init + eq(ζ, T)·ŝ_fin`, from the drawn challenges
(`verifyLink`'s `let`s up to its first `claim`, the unused ones left out). -/
def indexClaim (layout : Layout) (chunks : Chunks) (drawn : List E) : E :=
  let tables := layout.tables
  let heights := layout.tableLogHeights
  let rows := layout.tableRows
  let cycles := rows.foldl (· + ·) 0
  let width := chunks.width
  let pointers := tables.map (·.links.pointers)
  let nPointers := (pointers.map List.length).sum
  let nRows := heights.foldl max 0
  let drawn := drawn.drop (nTables - 1)
  let gammaState := drawn.take 2
  let drawn := drawn.drop 2
  let drawn := drawn.drop 3
  let (_, drawn) := tables.foldl (fun (acc : List (List E) × List E) t ↦
    (acc.1 ++ [acc.2.take t.links.memory.length], acc.2.drop t.links.memory.length)) ([], drawn)
  let drawn := drawn.drop bytecodeSlotBits
  let drawn := drawn.drop 2
  let drawn := drawn.drop nPointers
  let drawn := drawn.drop nRows
  let zeta := drawn.take width
  -- `ŝ_γ = 1 + γ_pc·pc + γ_fp·fp`: the constant component counts the rows on each cycle.
  let stateGamma := fun (pc fp : E) ↦ 1 + gammaState.getD 0 0 * pc + gammaState.getD 1 0 * fp
  let sInit := stateGamma 1 1
  let sFin := stateGamma (gpow (2 ^ layout.logBytecode - 1)) 1
  let claim := linkEqAt zeta 0 * sInit + linkEqAt zeta cycles * sFin
  claim

/-- `verifyLink` after the pointer columns' sum-check: the values at the row point and the
pointer words' bit-slices in one packed message, the terminal check against `claim`, and the
`LinkEnd` (`verifyLink`'s `let`s, the moves' results as arguments, the unused ones left out). -/
def linkTail (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E) (m1 : E)
    (fresh : List E) (split : Split) (chi qPoint : List E) (claim : E) :
    VerifierProgram LinkEnd := do
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
  let message ← VerifierProgram.readScalarsPacked (nValues + kBits)
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

open LeanVM.Semantics LeanVM.Protocol.KeccakHash


/-- `verifyLink` after the index side, from the index point `r` and the claim there: the memory
term, the fresh coefficients, the program's split, the row and pointer-column sum-checks. -/
def linkRowPhase (bytecodeSplit : List K → List E → List (ℕ × ℕ) → VerifierProgram Split)
    (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E) (claim : E) :
    VerifierProgram LinkEnd := do
  let m1 ← VerifierProgram.readScalar
  let fresh ← VerifierProgram.sampleChallengesPacked 5
  let split ← bytecodeSplit layout.bytecode (r.take layout.logBytecode) (pcSlots layout.tables)
  let (chi, claim) ← sumcheck claim (roundCoefficients chunks.d).1
    (List.replicate (linkRows layout) none)
  let (qPoint, claim) ← sumcheck claim (roundCoefficients chunks.d).2
    (List.replicate (linkQVars layout) none)
  linkTail layout chunks theta0 drawn r m1 fresh split chi qPoint claim

/-- `verifyLink`, cut at its moves. -/
def linkSkeleton (bytecodeSplit : List K → List E → List (ℕ × ℕ) → VerifierProgram Split)
    (layout : Layout) : VerifierProgram LinkEnd := do
  let chunks ← liftOption (Chunks.new (linkWidth layout))
  VerifierProgram.grindProofOfWork
    (grindingBits (max (linkRows layout + 3 + bytecodeSlotBits) (chunks.width + 1)))
  let theta0 ← VerifierProgram.sampleChallenge
  let drawn ← VerifierProgram.sampleChallengesPacked (linkDrawn layout chunks)
  let (r, claim) ← sumcheck (indexClaim layout chunks drawn) 3 (List.replicate chunks.width none)
  linkRowPhase bytecodeSplit layout chunks theta0 drawn r claim

/-- **Nothing was changed**: `verifyLink` is its skeleton. -/
theorem verifyLink_eq_linkSkeleton
    (bytecodeSplit : List K → List E → List (ℕ × ℕ) → VerifierProgram Split) (layout : Layout) :
    verifyLink bytecodeSplit layout = linkSkeleton bytecodeSplit layout := rfl

end

end LeanVM.Protocol.Link
