import Rv64Verifier.Proofs.Walk.Calls
import Rv64Verifier.Proofs.Bus.Contracts
import Rv64Verifier.Proofs.Pcs.Contracts

/-!
# `walk` at `0x800035f0`, past `verify_bus_balance` and its `Err` branch

`AtR17 OI s u layout rows lir bus`: the bus's `Ok` result is in the frame at `S - 928` (`sp + 1728`)
the claims' words in registers, the `Layout` at `S - 2080` (`sp + 576`) holds `layout`, and
the code runs `tailRust`, what is left of `walkRust` from the table phase on, from a transcript
whose one root is the one at `S - 1800` (`TracksR`).

Frame slots read from here on (offsets from `sp = S - 2656`): `72` the rate exponent, `80..104`
the public input's words, `168` the result's address, `192` the heights' buffer, `200` the tables'
buffer, `208` the transcript, `576..784` the `Layout` (`placements` at `+96`, `log_memory` at
`+152`, `qkeccak` at `+168`, `stack_log` at `+184`, the keccak shape at `+192`), `856` the root.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript

/-- What is left of `walkRust` once the bus has returned `bus`: the table phase on, and `finish`. -/
def tailRust (publicInput : List (BitVec 8)) (layout : LayoutMirror.LayoutRust)
    (tableRows : List (BitVec 64)) (logInverseRate : BitVec 64) (bus : BusResultRust) :
    TM SummaryRust :=
  (do
    let evaluations ← tablePhaseRust layout bus
    let claims := bus.claims ++ tableClaimsRust evaluations
    let publicClaims ← publicInputRust layout publicInput
    let claims := claims ++ publicClaims
    let (openings, keccakStart, keccakEnd) ← keccakPhaseRust layout evaluations
    let claims := claims ++
      openings.outputs.toList.map fun pw ↦ (⟨LayoutMirror.qkeccakRust, pw.1, pw.2⟩ : ColumnClaim)
    let (ringTarget, ringWeight) ← Pcs.ringSwitchRust openings.inputs.1 openings.inputs.2
    Pcs.verifyStackedOpeningRust layout.stackLog logInverseRate.toNat
      (⟨.placedRing layout.qkeccak ringWeight, ringTarget⟩ :: claims.filterMap (onStackRust layout))
    pure ⟨layout.logMemory, tableRows, logInverseRate.toNat, bus.bytecodePoint,
      (keccakStart, keccakEnd)⟩) >>= finishRust

/-- `bodyRest` then `finish` is the root, the bus, then `tailRust`. -/
theorem bodyRest_tail (bc : BytecodeRust) (publicInput : List (BitVec 8))
    (layout : LayoutMirror.LayoutRust) (tableRows : List (BitVec 64)) (lir : BitVec 64) :
    bodyRest bc publicInput (layout, tableRows, lir) >>= finishRust =
      TM.commit (stackShape layout.stackLog lir.toNat).1 (stackShape layout.stackLog lir.toNat).2 >>=
        fun _ ↦ verifyBusBalanceM (evaluateRust bc) (layout.toSpec []) >>= fun bus ↦
          tailRust publicInput layout tableRows lir bus := by
  simp only [bodyRest, tailRust, bind_assoc]

/-- `Tracks`, the transcript's roots being `[root]`. -/
def TracksR (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (root : Digest × ℕ × ℕ) (C : TM SummaryRust) : Prop :=
  ∀ proof, ProofIn OI s (s.getReg .x13) proof → ∃ T, T.proof = proof ∧ T.roots = [root] ∧
    TranscriptAt u (tp s) T ∧ (prog s).run (initT s proof) = C.run T

/-- `n` bytes from `p`, allocated by `walk` before `u`: aligned, ending below `NEXT` at `u`, and
from `NEXT` at the entry on unless empty (an empty buffer's dangling pointer is small). -/
@[rv_addr] def Old (s u : MachineState) (p : Word) (n : Nat) : Prop :=
  p.toNat % 8 = 0 ∧ p.toNat + n ≤ heapNext u ∧ (n = 0 ∨ heapNext s ≤ p.toNat)

theorem Old.newBuf {s u : MachineState} {p : Word} {n : Nat} (h : Old s u p n) :
    NewBuf s u p n 8 :=
  ⟨h.1, h.2.2.elim Or.inl fun h' ↦ Or.inr ⟨h', h.2.1⟩⟩

/-- The `k` `Vec<Form>`s from `a`: their buffers, every form's terms, allocated by `walk`. -/
structure FormRowsOld (s u : MachineState) (a : Word) (k : Nat) : Prop where
  forms : ∀ i < k, Old s u (vecPtr u (a + BitVec.ofNat 64 (24 * i)))
    (24 * (vecLen u (a + BitVec.ofNat 64 (24 * i))).toNat)
  terms : ∀ i < k, ∀ j < (vecLen u (a + BitVec.ofNat 64 (24 * i))).toNat,
    Old s u (vecPtr u (vecPtr u (a + BitVec.ofNat 64 (24 * i)) + BitVec.ofNat 64 (24 * j)))
      (48 * (vecLen u (vecPtr u (a + BitVec.ofNat 64 (24 * i)) + BitVec.ofNat 64 (24 * j))).toNat)

/-- The `Layout` at `S - 2080` holds what the rest of `walk` reads of `layout`; the tables' and the
heights' buffers are at `S - 2456` and `S - 2464`. -/
structure LayoutIn (s u : MachineState) (layout : LayoutMirror.LayoutRust) : Prop where
  tables : Old s u (u.getMem (s.getReg .x2 - 2456)) 480
  /-- The `Layout`'s `tables` `Vec` (read by its drop glue) is that buffer, six of them. -/
  tablesVec : vecPtr u (s.getReg .x2 - 2080) = u.getMem (s.getReg .x2 - 2456) ∧
    vecLen u (s.getReg .x2 - 2080) = 6
  opcodes : ∀ i < 6, u.getMem (u.getMem (s.getReg .x2 - 2456) + BitVec.ofNat 64 (80 * i + 72)) =
    BitVec.ofNat 64 i
  heights : Old s u (u.getMem (s.getReg .x2 - 2464)) 48
  heightsVal : Bus.natsAt u (u.getMem (s.getReg .x2 - 2464)) 6 = layout.tableLogHeights
  placements : Old s u (vecPtr u (s.getReg .x2 - 1984)) (24 * (vecLen u (s.getReg .x2 - 1984)).toNat)
  placementsVal : PcsContracts.placementsAt u (vecPtr u (s.getReg .x2 - 1984))
    (vecLen u (s.getReg .x2 - 1984)).toNat = layout.placements
  logMemory : (u.getMem (s.getReg .x2 - 1928)).toNat = layout.logMemory
  qkeccakVars : (u.getMem (s.getReg .x2 - 1912)).toNat = layout.qkeccak.variableCount
  qkeccakIndex : u.getMem (s.getReg .x2 - 1904) = layout.qkeccak.index
  stackLog : (u.getMem (s.getReg .x2 - 1896)).toNat = layout.stackLog
  keccakLogSteps : (u.getMem (s.getReg .x2 - 1888)).toNat = layout.keccakLogSteps
  keccakDepth : u.getMem (s.getReg .x2 - 1880) = 12

/-- At `0x800035f0`, the bus's `Ok` result at `S - 928`. -/
structure AtR17 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64)) (lir : BitVec 64)
    (bus : BusResultRust) : Prop where
  pc : u.pc = 0x800035f0
  inv : Inv s u
  proofPtr : u.getMem (tp s) = s.getReg .x13
  checked : byteAt u (tp s + 360) = 1
  /-- `s5` the result's address, `s6` = `sp + 2144`, `s7` the sponge, `s11` the heights' count. -/
  x21 : u.getReg .x21 = s.getReg .x10
  x22 : u.getReg .x22 = s.getReg .x2 - 512
  x23 : u.getReg .x23 = tp s + 8
  x27 : u.getReg .x27 = 6
  /-- The bus result's capacity, pointer and length of `claims`, as `0x800035dc..0x800035ec`
  load them. -/
  x19 : u.getReg .x19 = u.getMem (s.getReg .x2 - 928)
  x11 : u.getReg .x11 = u.getMem (s.getReg .x2 - 920)
  x25 : u.getReg .x25 = u.getMem (s.getReg .x2 - 912)
  /-- The rate exponent at `sp + 72`, the result's address at `sp + 168`. -/
  rate : u.getMem (s.getReg .x2 - 2584) = lir
  sret : u.getMem (s.getReg .x2 - 2488) = s.getReg .x10
  /-- The public input's words at `sp + 88`, `104`, `80`, `96`. -/
  pi0 : u.getMem (s.getReg .x2 - 2568) = s.getMem (s.getReg .x12)
  pi1 : u.getMem (s.getReg .x2 - 2552) = s.getMem (s.getReg .x12 + 8)
  pi2 : u.getMem (s.getReg .x2 - 2576) = s.getMem (s.getReg .x12 + 16)
  pi3 : u.getMem (s.getReg .x2 - 2560) = s.getMem (s.getReg .x12 + 24)
  /-- The bus's `Ok` result at `S - 928`, allocated by `walk`. -/
  busOk : vecCap u (s.getReg .x2 - 928) ≠ errNiche
  busAt : Bus.BusResultAt s u (s.getReg .x2 - 928) bus
  forms : FormRowsOld s u (vecPtr u (s.getReg .x2 - 856)) (vecLen u (s.getReg .x2 - 856)).toNat
  /-- The bus point's and the claims' buffers, the claims' points' (beyond `BusResultAt`: their
  pointers when empty). -/
  pointOld : Old s u (vecPtr u (s.getReg .x2 - 880)) (24 * (vecLen u (s.getReg .x2 - 880)).toNat)
  claimsOld : Old s u (vecPtr u (s.getReg .x2 - 928)) (56 * (vecCap u (s.getReg .x2 - 928)).toNat)
  claimPoints : ∀ i < (vecLen u (s.getReg .x2 - 928)).toNat,
    Old s u (vecPtr u (vecPtr u (s.getReg .x2 - 928) + BitVec.ofNat 64 (56 * i)))
      (24 * (vecLen u (vecPtr u (s.getReg .x2 - 928) + BitVec.ofNat 64 (56 * i))).toNat)
  formsBuf : Old s u (vecPtr u (s.getReg .x2 - 856)) (24 * (vecLen u (s.getReg .x2 - 856)).toNat)
  /-- Each claim's point misses the claims' buffer, whose spare room the table claims fill. -/
  claimsApart : ∀ i < (vecLen u (s.getReg .x2 - 928)).toNat,
    Apart (vecPtr u (vecPtr u (s.getReg .x2 - 928) + BitVec.ofNat 64 (56 * i)))
      (24 * (vecLen u (vecPtr u (s.getReg .x2 - 928) + BitVec.ofNat 64 (56 * i))).toNat)
      (vecPtr u (s.getReg .x2 - 928)) (56 * (vecCap u (s.getReg .x2 - 928)).toNat)
  layoutIn : LayoutIn s u layout
  /-- What `announcedRust` established. -/
  build : rows.length = 6 ∧ ∃ len lm, LayoutMirror.buildLayoutRust len lm rows = some layout
  stack : Pcs.minStackedLog ≤ layout.stackLog ∧ layout.stackLog ≤ Pcs.maxStackedLog
  rateOk : 1 ≤ lir.toNat ∧ lir.toNat ≤ 4
  tracks : TracksR OI s u
    (PcsContracts.digestAt u (s.getReg .x2 - 1800), stackShape layout.stackLog lir.toNat)
    (tailRust (bytesAt s (s.getReg .x12) 32) layout rows lir bus)

end Rv64Verifier.Proofs.Walk
