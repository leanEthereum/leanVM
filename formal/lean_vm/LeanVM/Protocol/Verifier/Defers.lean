/-
  LeanVM.Protocol.Verifier.Defers

  A proof the leanVM verifier accepts is accepted by the deferring verifier, under the IV the
  verifier hashes, with a true fresh claim, and with no claim at another point; conversely, a proof
  the deferring verifier accepts under that IV with a true fresh claim, the leanVM verifier accepts.
-/

module

public import LeanVM.Protocol.Verifier.Deferred
public import Statement.LeanVm
import LeanVM.Protocol.WithHashBridge

/-!
# The claim an accepted proof defers

The verifier meets the program once, where the link calls the program's split at its point over
the instructions (`verifyLink`'s `bytecodeSplit layout.bytecode r[..log_bytecode] (pc_slots tables)`).
`verifyExecution bs` is a prefix (`execPre`: the sizes, the stack's commitment and its out-of-domain
sample, the link up to its five fresh coefficients), the call of `bs` at the point the prefix
returns, and a suffix (`execSuf`) that reads the split only through the link's program side
(`programSide`, `verifyExecution_split`). The deployed verifier computes the split
(`computedSplit`); the deferring verifier takes it from a fresh claim (`freshSplit`), whose point
must be the link's. The fresh claim of the split columns' values at the link's point
(`FreshClaim.Holds`) gives the computed split's program side (`programSide_ofColumns_splitValues`),
so:

* an accepted run with the computed split is the run with that claim
  (`run_fresh_of_computed`), and a run with a claim that returns has the link's point as the
  claim's (the same theorem): the claims a proof is accepted with share one point, and one claim at
  that point holds;
* an accepted run with a true claim is the run with the computed split
  (`run_computed_of_fresh`): the true claim's point is the link's, so the computed split's checks
  (`MultilinearSize`) pass, the program being the layout's.

`LeanVM.verifyDeferredWith_of_leanVmVerifier` and `LeanVM.verifyDeferred_of_leanVmVerifier` state
the first over any permutation function in `Id` and at Keccak-f[1600],
`LeanVM.leanVmVerifier_of_verifyDeferred` the second. Unlike the bus era's single claimed value,
the fresh claim's values reach the verifier only through the link's terminal check, a linear form
in them: other values at the same point may pass it, so the claim the deferring verifier accepts is
unique only among true claims.
-/

namespace LeanVM.Protocol.Verifier.Defers

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Node

@[expose] public section

/-! ## The verifier, split at its call of the program's split -/

/-- What the link has read and drawn when it calls the program's split: the chunks, `θ_0`, the
packed draw, the index side's point `r` and claim, the memory term `m1` and the five fresh
coefficients. -/
structure LinkPre where
  chunks : Chunks
  theta0 : E
  drawn : List E
  r : List E
  claim : E
  m1 : E
  fresh : List E

/-- `verify_link` up to its call of the program's split (`link.rs`). -/
def linkPre (layout : Layout) : VerifierProgram LinkPre := do
  let tables := layout.tables
  let heights := layout.tableLogHeights
  let rows := layout.tableRows
  let cycles := rows.foldl (· + ·) 0
  let chunks ← liftOption (Chunks.new (pointerWidth layout.logMemory layout.logBytecode cycles))
  let width := chunks.width
  let pointers := tables.map (·.links.pointers)
  let nPointers := (pointers.map List.length).sum
  let nRows := heights.foldl max 0
  VerifierProgram.grindProofOfWork (grindingBits (max (nRows + 3 + bytecodeSlotBits) (width + 1)))
  let theta0 ← VerifierProgram.sampleChallenge
  let drawn0 ← VerifierProgram.sampleChallengesPacked (packedChallenges tables nRows width)
  let drawn := drawn0.drop (nTables - 1)
  let gammaState := drawn.take 2
  let drawn := drawn.drop 2
  let drawn := drawn.drop 3
  let md := tables.foldl (fun (acc : List (List E) × List E) t ↦
    (acc.1 ++ [acc.2.take t.links.memory.length], acc.2.drop t.links.memory.length)) ([], drawn)
  let drawn := md.2
  let drawn := drawn.drop bytecodeSlotBits
  let drawn := drawn.drop 2
  let drawn := drawn.drop nPointers
  let drawn := drawn.drop nRows
  let zeta := drawn.take width
  let stateGamma := fun (pc fp : E) ↦ 1 + gammaState.getD 0 0 * pc + gammaState.getD 1 0 * fp
  let sInit := stateGamma 1 1
  let sFin := stateGamma (gpow (2 ^ layout.logBytecode - 1)) 1
  let claim := linkEqAt zeta 0 * sInit + linkEqAt zeta cycles * sFin
  let rc ← sumcheck claim 3 (List.replicate width none)
  let m1 ← VerifierProgram.readScalar
  let fresh ← VerifierProgram.sampleChallengesPacked 5
  return ⟨chunks, theta0, drawn0, rc.1, rc.2, m1, fresh⟩

/-- The slot weights `verify_link` gives its program side, from what the prefix drew. -/
def linkWeights (layout : Layout) (y : LinkPre) : SlotWeights :=
  let tables := layout.tables
  let drawn := y.drawn.drop (nTables - 1)
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
  slotWeights tables (eqKernel alpha) (gammaMem.getD 0 0, gammaMem.getD 1 0) mu etaMem etaBc

/-- `verify_link` after its program side `ps = (program, frameProgram)` (`link.rs`). -/
def linkSufOf (layout : Layout) (y : LinkPre) (ps : E × E) : VerifierProgram LinkEnd := do
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
  let claim := y.claim
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
  let (rowCount, columnCount) := roundCoefficients d
  let (chi, claim) ← sumcheck claim rowCount (List.replicate nRows none)
  let qVars := log2Ceil nPointers
  let (qPoint, claim) ← sumcheck claim columnCount (List.replicate qVars none)
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

/-- `verify_link` after its call of the program's split, the split `split` (`link.rs`). -/
def linkSuf (layout : Layout) (y : LinkPre) (split : Split) : VerifierProgram LinkEnd :=
  linkSufOf layout y (programSide (linkWeights layout y) split)

/-- **`verify_link`, split at its call of the program's split.** -/
theorem verifyLink_split (bs : List K → List E → List (ℕ × ℕ) → VerifierProgram Split)
    (layout : Layout) :
    verifyLink bs layout = (linkPre layout).bind fun y ↦
      (bs layout.bytecode (y.r.take layout.logBytecode) (pcSlots layout.tables)).bind
        (linkSuf layout y) := by
  unfold verifyLink linkPre linkSuf linkSufOf programSide linkWeights
  simp only [VerifierProgram.bind_eq', VerifierProgram.pure_eq', VerifierProgram.bind_assoc',
    VerifierProgram.ret_bind']
  rfl

/-- What the verifier has read when the link calls the program's split. -/
structure ExecPre where
  layout : Layout
  rate : ℕ
  ood : StackClaim
  link : LinkPre

/-- `verify_execution` up to the link's call of the program's split (`walk`, `lib.rs`). -/
def execPre (bytecode : List K) : VerifierProgram ExecPre := do
  let sizes ← readAnnouncedSizes bytecode
  commitStack sizes.1.stackLog sizes.2
  let ood ← readOod sizes.1.stackLog
  let y ← linkPre sizes.1
  return ⟨sizes.1, sizes.2, ood, y⟩

/-- `verify_execution` after the link's call of the program's split, the split `split`. -/
def execSuf (publicInput : Digest) (z : ExecPre) (split : Split) : VerifierProgram Unit := do
  let layout := z.layout
  let logInverseRate := z.rate
  let ood := z.ood
  let link ← linkSuf layout z.link split
  let claims := linkColumnClaims link
  -- 4] binding the public input
  let publicClaims ← bindPublicInput layout publicInput
  let claims := claims ++ publicClaims
  -- 5] KECCAK validity, by GKR over the rounds, on the link's KECCAK columns
  let (outputs, keccakPoint, keccakSlices) ← keccakValidity layout link
  let claims := claims ++ outputs
  -- 6] ring switching: the Keccak reduction's input slices, then the pointer columns' slices
  let qkeccakPlacement ← liftOption (layout.placements.getD qkeccak none)
  let (ring, batching) ←
    ringSwitch [keccakRingClaim qkeccakPlacement keccakPoint keccakSlices, link.ring]
  let memoryTerm ← memoryTermClaim layout link
  -- 7] one opening of the stack for every claim with a placement
  verifyStackedOpening layout.stackLog logInverseRate
    (ring :: memoryTerm :: claims.filterMap (·.onStack layout) ++ [ood]) batching

/-- **`verify_execution`, split at the link's call of the program's split.** -/
theorem verifyExecution_split (bs : List K → List E → List (ℕ × ℕ) → VerifierProgram Split)
    (bytecode : List K) (publicInput : Digest) :
    verifyExecution bs bytecode publicInput = (execPre bytecode).bind fun z ↦
      (bs z.layout.bytecode (z.link.r.take z.layout.logBytecode) (pcSlots z.layout.tables)).bind
        (execSuf publicInput z) := by
  unfold verifyExecution execPre
  simp only [verifyLink_split, VerifierProgram.bind_eq', VerifierProgram.pure_eq',
    VerifierProgram.bind_assoc', VerifierProgram.ret_bind']
  rfl

/-! ## The prefix's facts -/

/-- The link's index point has at least the program's log-size coordinates: its width, the
pointer width, is at least `log_bytecode` (`pointer_width`). -/
theorem linkPre_r {layout : Layout} {y : LinkPre}
    (h : VerifierProgram.Returns (linkPre layout) y) : layout.logBytecode ≤ y.r.length := by
  unfold linkPre at h
  obtain ⟨chunks, hc, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨rc, hrc, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  rw [VerifierProgram.returns_ret h]
  have hw := Chunks.new_width (returns_liftOption hc)
  have hl := returns_sumcheck hrc
  rw [List.length_replicate, hw] at hl
  show layout.logBytecode ≤ rc.1.length
  rw [hl]
  unfold pointerWidth
  omega

/-- What the prefix returns: a layout of the program and of `tables()`, the program
`2^(BYTECODE_SLOT_BITS + log_bytecode)` words, `log_bytecode ≤ MAX_LOG_BYTECODE`, and the link's index point
at least `log_bytecode` long. -/
theorem execPre_facts {bytecode : List K} {z : ExecPre}
    (h : VerifierProgram.Returns (execPre bytecode) z) :
    z.layout.bytecode = bytecode ∧ z.layout.tables = tables ∧
      bytecode.length >>> bytecodeSlotBits = 2 ^ z.layout.logBytecode ∧
      z.layout.logBytecode ≤ maxLogBytecode ∧ z.layout.logBytecode ≤ z.link.r.length := by
  unfold execPre at h
  obtain ⟨sizes, hs, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨y, hy, h⟩ := VerifierProgram.returns_bind h
  rw [VerifierProgram.returns_ret h]
  obtain ⟨h1, h2, h3, h4⟩ := readSizes_facts hs
  exact ⟨h1, h2, h3, h4, linkPre_r hy⟩

/-- The suffix reads the split only through the link's program side. -/
theorem execSuf_congr (publicInput : Digest) (z : ExecPre) {s1 s2 : Split}
    (h : programSide (linkWeights z.layout z.link) s1 = programSide (linkWeights z.layout z.link) s2) :
    execSuf publicInput z s1 = execSuf publicInput z s2 := by
  simp only [execSuf, linkSuf, h]

/-- The program side of the true fresh claim's split at the link's point is the computed split's,
on a layout of the program and of `tables()`. -/
theorem programSide_claim {bytecode : List K} {z : ExecPre} (hb : z.layout.bytecode = bytecode)
    (ht : z.layout.tables = tables) (point : List E) :
    programSide (linkWeights z.layout z.link) (Split.ofColumns tables (splitValues bytecode point)) =
      programSide (linkWeights z.layout z.link)
        (splitAt z.layout.bytecode point (pcSlots z.layout.tables)) := by
  obtain ⟨sl, ga, mu, em, eb, hw⟩ : ∃ sl ga mu em eb,
      linkWeights z.layout z.link = slotWeights z.layout.tables sl ga mu em eb :=
    ⟨_, _, _, _, _, rfl⟩
  rw [hw, hb, ht]
  exact programSide_ofColumns_splitValues bytecode point sl ga mu em eb

/-! ## The splits -/

theorem computedSplit_bind {β : Type} (bytecode : List K) (point : List E) (pc : List (ℕ × ℕ))
    (g : Split → VerifierProgram β) :
    (computedSplit bytecode point pc).bind g =
      if point.length < 64 ∧ bytecode.length >>> bytecodeSlotBits = 2 ^ point.length then
        g (splitAt bytecode point pc) else .fail := by
  unfold computedSplit VerifierProgram.require
  split <;> rfl

theorem freshSplit_bind {β : Type} (fresh : FreshClaim) (bytecode : List K) (point : List E)
    (pc : List (ℕ × ℕ)) (g : Split → VerifierProgram β) :
    (freshSplit fresh bytecode point pc).bind g =
      if point = fresh.point ∧ fresh.values.length = (splitColumns tables).length then
        g (Split.ofColumns tables fresh.values) else .fail := by
  unfold freshSplit VerifierProgram.require
  split <;> rfl

/-- The fresh claim of the program's split columns at `point` (`FreshClaim::at`). -/
def claimAt (bytecode : List K) (point : List E) : FreshClaim := ⟨point, splitValues bytecode point⟩

theorem claimAt_holds (bytecode : List K) (point : List E) :
    (claimAt bytecode point).Holds bytecode := by
  simp only [claimAt, FreshClaim.Holds]

theorem leanVmVerifierProgram_eq (bytecode : List K) (publicInput : Digest) :
    leanVmVerifierProgram bytecode publicInput =
      (verifyExecution computedSplit bytecode publicInput).bind fun _ ↦ .ret true := rfl

theorem deferringVerifierProgram_eq (fresh : FreshClaim) (bytecode : List K) (publicInput : Digest) :
    deferringVerifierProgram fresh bytecode publicInput =
      (verifyExecution (freshSplit fresh) bytecode publicInput).bind fun _ ↦ .ret true := rfl

/-! ## The runs -/

section Run

variable (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState) (bytecode : List K)
  (publicInput : Digest)

/-- A run of the verifier with the split `bs`, split at the link's call. -/
theorem run_split (bs : List K → List E → List (ℕ × ℕ) → VerifierProgram Split)
    (k : Unit → VerifierProgram Bool) (st : VerifierProgramState) :
    runWithHash H F ((verifyExecution bs bytecode publicInput).bind k) st =
      (runWithHash H F (execPre bytecode) st).bind fun zs ↦
        runWithHash H F ((bs zs.1.layout.bytecode (zs.1.link.r.take zs.1.layout.logBytecode)
          (pcSlots zs.1.layout.tables)).bind fun s ↦ (execSuf publicInput zs.1 s).bind k) zs.2 := by
  rw [verifyExecution_split, VerifierProgram.bind_assoc', runWithHash_bind]
  simp only [VerifierProgram.bind_assoc']

/-- **A run with the computed split that returns is the run with the true fresh claim at the
link's point**, and a run with any fresh claim that returns has that point as its claim's. -/
theorem run_fresh_of_computed (k : Unit → VerifierProgram Bool) {st : VerifierProgramState}
    {r : Bool × VerifierProgramState}
    (h : runWithHash H F ((verifyExecution computedSplit bytecode publicInput).bind k) st =
      some r) :
    ∃ point : List E,
      runWithHash H F ((verifyExecution (freshSplit (claimAt bytecode point)) bytecode
        publicInput).bind k) st = some r ∧
      ∀ (c : FreshClaim) (r' : Bool × VerifierProgramState),
        runWithHash H F ((verifyExecution (freshSplit c) bytecode publicInput).bind k) st =
          some r' → c.point = point := by
  rw [run_split] at h
  rcases hp : runWithHash H F (execPre bytecode) st with _ | ⟨z, s1⟩
  · simp [hp] at h
  simp only [hp, Option.bind_some] at h
  obtain ⟨hb, ht, -, -, -⟩ := execPre_facts (VerifierProgram.returns_of_run H F hp)
  rw [computedSplit_bind] at h
  split at h
  · refine ⟨z.link.r.take z.layout.logBytecode, ?_, fun c r' h' ↦ ?_⟩
    · rw [run_split]
      simp only [hp, Option.bind_some]
      rw [freshSplit_bind, ite_eq_left ⟨rfl, by simp [claimAt, splitValues]⟩, ← h]
      simp only [claimAt]
      rw [execSuf_congr publicInput z (programSide_claim hb ht _)]
    · rw [run_split] at h'
      simp only [hp, Option.bind_some] at h'
      rw [freshSplit_bind] at h'
      split at h'
      · next hc => exact hc.1.symm
      · simp [runWithHash] at h'
  · simp [runWithHash] at h

/-- **A run with a true fresh claim that returns is the run with the computed split.** -/
theorem run_computed_of_fresh {c : FreshClaim} (hc : c.Holds bytecode)
    (k : Unit → VerifierProgram Bool) {st : VerifierProgramState}
    {r : Bool × VerifierProgramState}
    (h : runWithHash H F ((verifyExecution (freshSplit c) bytecode publicInput).bind k) st =
      some r) :
    runWithHash H F ((verifyExecution computedSplit bytecode publicInput).bind k) st = some r := by
  rw [run_split] at h ⊢
  rcases hp : runWithHash H F (execPre bytecode) st with _ | ⟨z, s1⟩
  · simp [hp] at h
  simp only [hp, Option.bind_some] at h ⊢
  obtain ⟨hb, ht, hlen, hmax, hr⟩ := execPre_facts (VerifierProgram.returns_of_run H F hp)
  rw [freshSplit_bind] at h
  split at h
  · next hc' =>
    obtain ⟨hpt, -⟩ := hc'
    have hl : (z.link.r.take z.layout.logBytecode).length = z.layout.logBytecode := by
      rw [List.length_take]; omega
    have hmax' : maxLogBytecode = 30 := rfl
    rw [computedSplit_bind, ite_eq_left ⟨by omega, by rw [hl, hb]; exact hlen⟩, ← h,
      show c.values = splitValues bytecode (z.link.r.take z.layout.logBytecode) by
        rw [hpt]; exact hc,
      execSuf_congr publicInput z (programSide_claim hb ht _)]
  · simp [runWithHash] at h

/-- **A proof accepted with the computed split is accepted with a true fresh claim**, and every
fresh claim it is accepted with has that claim's point. -/
theorem runProof_fresh_of_computed {sd : KeccakState} {π : Proof}
    (h : Id.run (runProofWithHash H F (leanVmVerifierProgram bytecode publicInput) sd π) =
      true) :
    ∃ c : FreshClaim, c.Holds bytecode ∧
      Id.run (runProofWithHash H F (deferringVerifierProgram c bytecode publicInput) sd π) =
        true ∧
      ∀ c', Id.run (runProofWithHash H F (deferringVerifierProgram c' bytecode publicInput) sd
        π) = true → c'.point = c.point := by
  rw [leanVmVerifierProgram_eq] at h
  unfold runProofWithHash at h
  revert h
  match hr : runWithHash H F ((verifyExecution computedSplit bytecode publicInput).bind
      fun _ ↦ VerifierProgram.ret true) ⟨⟨sd, [], none⟩, π.stream, π.openings, []⟩ with
  | some (true, s) =>
    intro h
    obtain ⟨point, hrun, hu⟩ := run_fresh_of_computed H F bytecode publicInput _ hr
    refine ⟨claimAt bytecode point, claimAt_holds bytecode point, ?_, fun c' h' ↦ ?_⟩
    · unfold runProofWithHash
      rw [deferringVerifierProgram_eq, hrun]
      exact h
    · unfold runProofWithHash at h'
      rw [deferringVerifierProgram_eq] at h'
      generalize hr' : runWithHash H F ((verifyExecution (freshSplit c') bytecode
        publicInput).bind fun _ ↦ VerifierProgram.ret true)
          ⟨⟨sd, [], none⟩, π.stream, π.openings, []⟩ = o at h'
      rcases o with _ | ⟨_ | _, _⟩
      · cases h'
      · cases h'
      · exact hu c' _ hr'
  | some (false, _) => intro h; cases h
  | none => intro h; cases h

/-- **A proof accepted with a true fresh claim is accepted with the computed split.** -/
theorem runProof_computed_of_fresh {c : FreshClaim} (hc : c.Holds bytecode) {sd : KeccakState}
    {π : Proof}
    (h : Id.run (runProofWithHash H F (deferringVerifierProgram c bytecode publicInput) sd π) =
      true) :
    Id.run (runProofWithHash H F (leanVmVerifierProgram bytecode publicInput) sd π) = true := by
  rw [deferringVerifierProgram_eq] at h
  rw [leanVmVerifierProgram_eq]
  unfold runProofWithHash at h ⊢
  generalize hr : runWithHash H F ((verifyExecution (freshSplit c) bytecode publicInput).bind
    fun _ ↦ VerifierProgram.ret true) ⟨⟨sd, [], none⟩, π.stream, π.openings, []⟩ = o at h
  rcases o with _ | ⟨_ | _, s⟩
  · cases h
  · cases h
  · rw [run_computed_of_fresh H F bytecode publicInput hc _ hr]
    exact h

end Run

end
end LeanVM.Protocol.Verifier.Defers

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash LeanVM.Node Defers

@[expose] public section

section Hash

variable (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState)

/-- A true fresh claim is fixed by its point. -/
theorem FreshClaim.eq_of_holds {bytecode : List K} {c c' : FreshClaim} (hc : c.Holds bytecode)
    (hc' : c'.Holds bytecode) (h : c'.point = c.point) : c' = c := by
  obtain ⟨p, v⟩ := c
  obtain ⟨p', v'⟩ := c'
  simp only [FreshClaim.Holds] at hc hc' h
  subst h
  rw [hc, hc']

/-- **A proof the verifier accepts, the deferring verifier accepts under the verifier's IV with a
true fresh claim**, and with no claim at another point, so with no other true claim, at any hash
and permutation. -/
theorem verifyDeferredWithHash_of_verifyWithHash {bytecode : List K} {publicInput : Digest}
    {π : Proof} (h : Id.run (verifyWithHash H F bytecode publicInput π) = true) :
    ∃ c : FreshClaim, c.Holds bytecode ∧
      Id.run (verifyDeferredWithHash H F bytecode (Id.run (fiatShamirIvWithHash H bytecode))
        publicInput c π) = true ∧
      ∀ c', Id.run (verifyDeferredWithHash H F bytecode (Id.run (fiatShamirIvWithHash H bytecode))
        publicInput c' π) = true → c'.point = c.point ∧ (c'.Holds bytecode → c' = c) := by
  have h0 : Id.run (runProofWithHash H F (leanVmVerifierProgram bytecode publicInput)
      (Id.run (seedWithHash H F bytecode publicInput)) π) = true := h
  obtain ⟨c, hc, hacc, hu⟩ := runProof_fresh_of_computed H F bytecode publicInput h0
  exact ⟨c, hc, hacc, fun c' h' ↦ ⟨hu c' h', fun hc' ↦ FreshClaim.eq_of_holds hc hc' (hu c' h')⟩⟩

/-- **A proof the deferring verifier accepts under the verifier's IV with a true fresh claim, the
verifier accepts**, at any hash and permutation. -/
theorem verifyWithHash_of_verifyDeferredWithHash {bytecode : List K} {publicInput : Digest}
    {c : FreshClaim} {π : Proof} (hc : c.Holds bytecode)
    (h : Id.run (verifyDeferredWithHash H F bytecode (Id.run (fiatShamirIvWithHash H bytecode))
      publicInput c π) = true) :
    Id.run (verifyWithHash H F bytecode publicInput π) = true :=
  runProof_computed_of_fresh H F bytecode publicInput hc h

end Hash

end
end LeanVM.Protocol.Verifier

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **A proof the leanVM verifier accepts is deferred**: over any permutation function `π` in
`Id`, the deferring verifier accepts it, under the IV the verifier hashes, with a true fresh claim
(the split columns' values at the link's point over the instructions), and every fresh claim it
accepts it with has that point, so no other true one. -/
theorem verifyDeferredWith_of_leanVmVerifier (π : KeccakState → Id KeccakState)
    {prog : LeanIsaProgram} {input : PublicInput} {proof : Proof}
    (h : Id.run (leanVmVerifier π prog input proof) = true) :
    ∃ c : FreshClaim, c.Holds (bytecodeWords prog) ∧
      Id.run (verifyDeferredWith π (bytecodeWords prog)
        (Id.run (fiatShamirIvWith π (bytecodeWords prog))) (publicInputDigest input) c proof) =
          true ∧
      ∀ c', Id.run (verifyDeferredWith π (bytecodeWords prog)
        (Id.run (fiatShamirIvWith π (bytecodeWords prog))) (publicInputDigest input) c' proof) =
          true → c'.point = c.point ∧ (c'.Holds (bytecodeWords prog) → c' = c) := by
  have h' : Id.run (verifyWithHash (keccak256With π) π (bytecodeWords prog) (publicInputDigest input)
      proof) = true := by
    rw [← verifyWith_eq_withHash]
    exact h
  simp only [verifyDeferredWith_eq_withHash]
  exact verifyDeferredWithHash_of_verifyWithHash _ _ h'

/-- **A proof the deployed leanVM verifier accepts is deferred**: the deployed deferring verifier
accepts it, under the deployed IV, with a true fresh claim, and every fresh claim it accepts it with
has that claim's point, so no other true one. -/
theorem verifyDeferred_of_leanVmVerifier {prog : LeanIsaProgram} {input : PublicInput}
    {proof : Proof} (h : leanVmVerifier (m := Id) keccakF1600 prog input proof = true) :
    ∃ c : FreshClaim, c.Holds (bytecodeWords prog) ∧
      verifyDeferred (bytecodeWords prog) (fiatShamirIv (bytecodeWords prog))
        (publicInputDigest input) c proof = true ∧
      ∀ c', verifyDeferred (bytecodeWords prog) (fiatShamirIv (bytecodeWords prog))
        (publicInputDigest input) c' proof = true →
          c'.point = c.point ∧ (c'.Holds (bytecodeWords prog) → c' = c) :=
  verifyDeferredWith_of_leanVmVerifier keccakF1600 h

/-- **A proof the deferring verifier accepts with a true fresh claim, the leanVM verifier
accepts**: over any permutation function `π` in `Id`, under the IV the verifier hashes. -/
theorem leanVmVerifier_of_verifyDeferredWith (π : KeccakState → Id KeccakState)
    {prog : LeanIsaProgram} {input : PublicInput} {proof : Proof} {c : FreshClaim}
    (hc : c.Holds (bytecodeWords prog))
    (h : Id.run (verifyDeferredWith π (bytecodeWords prog)
      (Id.run (fiatShamirIvWith π (bytecodeWords prog))) (publicInputDigest input) c proof) =
        true) :
    Id.run (leanVmVerifier π prog input proof) = true := by
  rw [verifyDeferredWith_eq_withHash] at h
  rw [leanVmVerifier, verifyWith_eq_withHash]
  exact verifyWithHash_of_verifyDeferredWithHash _ _ hc h

/-- **The deployed verifier accepts exactly the proofs the deployed deferring verifier accepts,
under the deployed IV, with a true fresh claim.** -/
theorem leanVmVerifier_iff_verifyDeferred {prog : LeanIsaProgram} {input : PublicInput}
    {proof : Proof} :
    leanVmVerifier (m := Id) keccakF1600 prog input proof = true ↔
      ∃ c : FreshClaim, c.Holds (bytecodeWords prog) ∧
        verifyDeferred (bytecodeWords prog) (fiatShamirIv (bytecodeWords prog))
          (publicInputDigest input) c proof = true :=
  ⟨fun h ↦ (verifyDeferred_of_leanVmVerifier h).imp fun _ h ↦ ⟨h.1, h.2.1⟩,
    fun ⟨_, hc, h⟩ ↦ leanVmVerifier_of_verifyDeferredWith keccakF1600 hc h⟩

end
end LeanVM
