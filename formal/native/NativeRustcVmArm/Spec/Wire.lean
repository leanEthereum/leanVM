module

public import NativeRustcVmArm.Code.Vm.ClimbLevel.Names
public import NativeRustcVmArm.Code.Vm.Decode.Names
public import NativeRustcVmArm.Code.Vm.Find.Names
public import NativeRustcVmArm.Code.Vm.InsD.Names
public import NativeRustcVmArm.Code.Vm.PhaseM.Names
public import NativeRustcVmArm.Code.Vm.RdRows.Names
public import NativeRustcVmArm.Code.Vm.ReaderDigest.Names
public import NativeRustcVmArm.Code.Vm.ReaderLe.Names
public import NativeRustcVmArm.Code.Vm.ReaderWords.Names
public import NativeRustcVmArm.Code.Vm.WriteOpenings.Names
public import NativeRustcVmArm.Spec.Keccak
public import NativeRustcVm.Wire.Rep

/-!
# The contracts of `wire.rs`'s functions on AArch64

Each function uses the stack below SP (`<fn>Stack` bytes, its callees' included; `StackOk` in its
precondition) and returns with the callee-saved registers and SP kept (`Saved`), no byte changed
outside its outputs and that stack. Regions are `NativeRustcVm.Region`s, data memory not wrapping
(`Region.Ok`), pairwise apart where listed (`Disjoint`). The reader at `r` is
`NativeRustcVm.Wire.ReaderAt`; a read moves only its cursor word (`curRegion r`). Results follow
the model `NativeVm.Wire.decodeM` (an `Option` tag in X0, `1` for `Some`, `0` for `None`):

- `Reader::le(r, n)` (X0, X1; rustc reads at least four bytes: `n` is `4` or `8`): `rdLe B c n`,
  the word in X1.
- `Reader::digest(out, r)` (X0 the `Option<Digest>`, 40 bytes; X1): `rdDigest`.
- `Reader::words(r, out, n)` (X0, X1, X2): `rdWords`, the words at `out`.
- `ins_d(sorted, n, x)` (X0, X1, X2): `insD` of the first `n < 256` words; the new count in X0.
- `find(nodes, len, key)` (X0, X1, X2): the index of the first node of key `key` in X1.
- `rd_rows(r, n, lw, rw, leaves)` (X0 to X4, `0 < n ≤ 256`, `rw ≤ lw ≤ 64`; rustc assumes a row,
  as `phase_m` always has one): `rdRows`, each row `paddedLeaf` at `leaves + 512 i`; X0 `1` if
  every row's first word is zero, `0` if not, `2` for `None`.
- `climb_level(r, nodes, len, sibs, next)` (X0 to X4, `len ≤ 256`): `sibsM` and `parentsOf`, the
  parents' count in X1.
- `write_openings(qs, nq, ps, np, leaves, lw, h, sibs, [sib_counts, out])` (X0 to X7, then two
  words at SP; rustc dropped `out`'s length, `PHASE_WORDS`; `0 < nq`, `0 < np`: rustc's loops
  run once at least, as `phase_m` always has a query): the phase of the openings `openingAt`.
- `phase_m(r, out, w)` (X0, X1, X2; rustc dropped `out`'s length): `phaseM`, the phase at `out`.
- `decode(bytes, L, dec, len, w)` (X0 to X4): `decodeM`, the decoded proof `DecodedAt` the area.
-/

namespace NativeRustcVmArm

open NativeRustcVm NativeRustcVm.Wire NativeRustcVm.Transcript NativeVm NativeVm.Wire
open NativeRustcArm (Spec StackOk Saved stackBelow)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-! ## Symbols -/


/-! ## Stacks -/

/-- `Reader::le` uses no stack. -/
def readerLeStack : Nat := 0
/-- The stack `Reader::digest` uses: its 48-byte frame. -/
def readerDigestStack : Nat := 48 + readerLeStack
/-- The stack `Reader::words` uses: its 32-byte frame. -/
def readerWordsStack : Nat := 32 + readerLeStack
/-- `ins_d` uses no stack. -/
def insDStack : Nat := 0
/-- `find` uses no stack. -/
def findStack : Nat := 0
/-- The stack `rd_rows` uses: its 112-byte frame and `Reader::words`'s. -/
def rdRowsStack : Nat := 112 + readerWordsStack
/-- The stack `climb_level` uses: its 224-byte frame and `hash_pair`'s (above `Reader::digest`'s). -/
def climbLevelStack : Nat := 224 + hashPairStack
/-- The stack `write_openings` uses: its 176-byte frame. -/
def writeOpeningsStack : Nat := 176 + findStack
/-- The stack `phase_m` uses: its 192-byte frame and `climb_level`'s (the largest of its callees'). -/
def phaseMStack : Nat := 192 + climbLevelStack
/-- The stack `decode` uses: its 96-byte frame and `phase_m`'s. -/
def decodeStack : Nat := 96 + phaseMStack

section
variable [Labels]

/-- The `n` bytes below SP. -/
def stackR (m : MachineData) (n : Nat) : Region := ⟨stackBelow m n, n⟩

/-- The round constants' bytes. -/
def rcR : Region := ⟨rcAddr, 192⟩

/-! ## `Reader::le`, `Reader::digest`, `Reader::words` -/

/-- `Reader::le`'s precondition. -/
def ReaderLePre (m : MachineData) : Prop :=
  StackOk m readerLeStack ∧ (m.regs.X1.toNat = 4 ∨ m.regs.X1.toNat = 8) ∧
    ∃ bp B c, ReaderAt m.dmem m.regs.X0.toBitVec bp B c

/-- `Reader::le`'s postcondition. -/
def ReaderLePost (m m' : MachineData) : Prop :=
  let r := m.regs.X0.toBitVec
  (∀ bp B c, ReaderAt m.dmem r bp B c →
    match rdLe B c m.regs.X1.toNat with
    | some (v, c') => m'.regs.X0 = 1 ∧ m'.regs.X1 = v ∧ ReaderAt m'.dmem r bp B c'
    | none => m'.regs.X0 = 0) ∧
    SameOutside m.dmem m'.dmem (curRegion r).Holds ∧ Saved m m'

/-- `Reader::digest`'s precondition. -/
def ReaderDigestPre (m : MachineData) : Prop :=
  let out := m.regs.X0.toBitVec; let r := m.regs.X1.toBitVec
  StackOk m readerDigestStack ∧ Region.Ok m.dmem ⟨out, 40⟩ ∧
    ∃ bp B c, ReaderAt m.dmem r bp B c ∧
      Disjoint [stackR m readerDigestStack, ⟨r, 24⟩, ⟨bp, B.length⟩, ⟨out, 40⟩]

/-- `Reader::digest`'s postcondition. -/
def ReaderDigestPost (m m' : MachineData) : Prop :=
  let out := m.regs.X0.toBitVec; let r := m.regs.X1.toBitVec
  (∀ bp B c, ReaderAt m.dmem r bp B c →
    match rdDigest B c with
    | some (dg, c') => WordAt m'.dmem out 1 ∧ WordsAt m'.dmem (off out 8) dg.toList ∧
        ReaderAt m'.dmem r bp B c'
    | none => WordAt m'.dmem out 0) ∧
    SameOutside m.dmem m'.dmem (InAny [⟨out, 40⟩, curRegion r, stackR m readerDigestStack]) ∧
    Saved m m'

/-- `Reader::words`'s precondition. -/
def ReaderWordsPre (m : MachineData) : Prop :=
  let r := m.regs.X0.toBitVec; let out := m.regs.X1.toBitVec; let n := m.regs.X2.toNat
  StackOk m readerWordsStack ∧ Region.Ok m.dmem ⟨out, 8 * n⟩ ∧
    ∃ bp B c, ReaderAt m.dmem r bp B c ∧
      Disjoint [stackR m readerWordsStack, ⟨r, 24⟩, ⟨bp, B.length⟩, ⟨out, 8 * n⟩]

/-- `Reader::words`'s postcondition. -/
def ReaderWordsPost (m m' : MachineData) : Prop :=
  let r := m.regs.X0.toBitVec; let out := m.regs.X1.toBitVec; let n := m.regs.X2.toNat
  (∀ bp B c, ReaderAt m.dmem r bp B c →
    match rdWords B n c with
    | some (ws, c') => m'.regs.X0 = 1 ∧ WordsAt m'.dmem out (ws.map K.lane) ∧
        ReaderAt m'.dmem r bp B c'
    | none => m'.regs.X0 = 0) ∧
    SameOutside m.dmem m'.dmem (InAny [⟨out, 8 * n⟩, curRegion r, stackR m readerWordsStack]) ∧
    Saved m m'

/-! ## `ins_d`, `find` -/

/-- `ins_d`'s precondition. -/
def InsDPre (m : MachineData) : Prop :=
  StackOk m insDStack ∧ m.regs.X1.toNat < 256 ∧ Region.Ok m.dmem ⟨m.regs.X0.toBitVec, 2048⟩

/-- `ins_d`'s postcondition. -/
def InsDPost (m m' : MachineData) : Prop :=
  let a := m.regs.X0.toBitVec
  (∀ l : List Nat, l.length = m.regs.X1.toNat → (∀ y ∈ l, y < 2 ^ 64) →
    WordsAt m.dmem a (l.map Nat.toUInt64) →
    m'.regs.X0.toNat = (insD l m.regs.X2.toNat).length ∧
      WordsAt m'.dmem a ((insD l m.regs.X2.toNat).map Nat.toUInt64)) ∧
    SameOutside m.dmem m'.dmem (InRange a 2048) ∧ Saved m m'

/-- `find`'s precondition. -/
def FindPre (m : MachineData) : Prop :=
  StackOk m findStack ∧ Region.Ok m.dmem ⟨m.regs.X0.toBitVec, 40 * m.regs.X1.toNat⟩

/-- `find`'s postcondition. -/
def FindPost (m m' : MachineData) : Prop :=
  let a := m.regs.X0.toBitVec
  (∀ ks : List UInt64, ks.length = m.regs.X1.toNat →
    (∀ i (h : i < ks.length), WordAt m.dmem (off a (40 * i)) ks[i]) →
    match ks.findIdx? (· == m.regs.X2) with
    | some i => m'.regs.X0 = 1 ∧ m'.regs.X1.toNat = i
    | none => m'.regs.X0 = 0) ∧
    m'.dmem = m.dmem ∧ Saved m m'

/-! ## `rd_rows`, `climb_level` -/

/-- `rd_rows`'s precondition. -/
def RdRowsPre (m : MachineData) : Prop :=
  let r := m.regs.X0.toBitVec; let n := m.regs.X1.toNat; let lw := m.regs.X2.toNat
  let rw := m.regs.X3.toNat; let lv := m.regs.X4.toBitVec
  StackOk m rdRowsStack ∧ 0 < n ∧ n ≤ 256 ∧ lw ≤ 64 ∧ rw ≤ lw ∧ Region.Ok m.dmem ⟨lv, 512 * n⟩ ∧
    ∃ bp B c, ReaderAt m.dmem r bp B c ∧
      Disjoint [stackR m rdRowsStack, ⟨r, 24⟩, ⟨bp, B.length⟩, ⟨lv, 512 * n⟩]

/-- `rd_rows`'s postcondition. -/
def RdRowsPost (m m' : MachineData) : Prop :=
  let r := m.regs.X0.toBitVec; let n := m.regs.X1.toNat; let lw := m.regs.X2.toNat
  let rw := m.regs.X3.toNat; let lv := m.regs.X4.toBitVec
  (∀ bp B c, ReaderAt m.dmem r bp B c →
    match rdRows B rw n c with
    | some (rows, c') => m'.regs.X0 = (if ∀ x ∈ rows, x.getD 0 0 = 0 then 1 else 0) ∧
        LeavesAt m'.dmem lv (rows.map fun x ↦ paddedLeaf x lw) ∧
        ReaderAt m'.dmem r bp B c'
    | none => m'.regs.X0 = 2) ∧
    SameOutside m.dmem m'.dmem (InAny [⟨lv, 512 * n⟩, curRegion r, stackR m rdRowsStack]) ∧
    Saved m m'

/-- `climb_level`'s precondition. -/
def ClimbLevelPre (m : MachineData) : Prop :=
  let r := m.regs.X0.toBitVec; let nodes := m.regs.X1.toBitVec; let n := m.regs.X2.toNat
  let sibs := m.regs.X3.toBitVec; let next := m.regs.X4.toBitVec
  StackOk m climbLevelStack ∧ NativeRustcVmArm.RcAt m climbLevelStack ∧ n ≤ 256 ∧
    Region.Ok m.dmem ⟨nodes, 40 * n⟩ ∧ Region.Ok m.dmem ⟨sibs, nodesBytes⟩ ∧
    Region.Ok m.dmem ⟨next, nodesBytes⟩ ∧
    ∃ bp B c, ReaderAt m.dmem r bp B c ∧
      Disjoint [stackR m climbLevelStack, rcR, ⟨r, 24⟩, ⟨bp, B.length⟩, ⟨nodes, 40 * n⟩,
        ⟨sibs, nodesBytes⟩, ⟨next, nodesBytes⟩]

/-- `climb_level`'s postcondition. -/
def ClimbLevelPost (m m' : MachineData) : Prop :=
  let r := m.regs.X0.toBitVec; let nodes := m.regs.X1.toBitVec; let n := m.regs.X2.toNat
  let sibs := m.regs.X3.toBitVec; let next := m.regs.X4.toBitVec
  (∀ bp B c, ReaderAt m.dmem r bp B c → ∀ ns, ns.length = n → NodesAt m.dmem nodes ns →
    match sibsM B ns ns c with
    | some (sl, c') => m'.regs.X0 = 1 ∧ m'.regs.X1.toNat = (parentsOf ns sl).length ∧
        NodesAt m'.dmem sibs (sl.map fun s ↦ (s.1, s.2.1)) ∧
        NodesAt m'.dmem next (parentsOf ns sl) ∧ ReaderAt m'.dmem r bp B c'
    | none => m'.regs.X0 = 0) ∧
    SameOutside m.dmem m'.dmem (InAny [⟨sibs, nodesBytes⟩, ⟨next, nodesBytes⟩, curRegion r,
      stackR m climbLevelStack]) ∧ Saved m m'

/-! ## `write_openings` -/

/-- `write_openings`'s regions: the queries, the positions, the leaves, the siblings, their
counts, and the phase's words. -/
def writeOpeningsRegions (m : MachineData) (cnt out : BitVec 64) : List Region :=
  [⟨m.regs.X0.toBitVec, 8 * m.regs.X1.toNat⟩, ⟨m.regs.X2.toBitVec, 8 * m.regs.X3.toNat⟩,
    ⟨m.regs.X4.toBitVec, 512 * m.regs.X3.toNat⟩, ⟨m.regs.X7.toBitVec, nodesBytes * m.regs.X6.toNat⟩,
    ⟨cnt, 8 * m.regs.X6.toNat⟩, ⟨out, phaseBytes⟩]

/-- `write_openings`'s precondition: its last two arguments, the sibling counts' and the phase's
addresses, at SP. -/
def WriteOpeningsPre (m : MachineData) : Prop :=
  StackOk m writeOpeningsStack ∧ m.regs.X1.toNat ≤ 256 ∧ m.regs.X3.toNat ≤ 256 ∧
    m.regs.X5.toNat ≤ 64 ∧ m.regs.X6.toNat ≤ 32 ∧ 0 < m.regs.X1.toNat ∧ 0 < m.regs.X3.toNat ∧
    ∃ cnt out, WordAt m.dmem m.regs.SP.toBitVec (UInt64.ofBitVec cnt) ∧
      WordAt m.dmem (off m.regs.SP.toBitVec 8) (UInt64.ofBitVec out) ∧
      (∀ R ∈ writeOpeningsRegions m cnt out, R.Ok m.dmem) ∧
      Disjoint (stackR m writeOpeningsStack :: ⟨m.regs.SP.toBitVec, 16⟩ ::
        writeOpeningsRegions m cnt out)

/-- `write_openings`'s postcondition: given the queries `qs` (below `2 ^ 32`, each a position),
the positions `ps`, their leaves of `lw` words and `h` levels of siblings, the phase at `out`. -/
def WriteOpeningsPost (m m' : MachineData) : Prop :=
  let lw := m.regs.X5.toNat; let h := m.regs.X6.toNat
  ∀ cnt out, WordAt m.dmem m.regs.SP.toBitVec (UInt64.ofBitVec cnt) →
    WordAt m.dmem (off m.regs.SP.toBitVec 8) (UInt64.ofBitVec out) →
    (∀ (qs ps : List Nat) (leaves : List (List K)) (sibs : List (List (Nat × Digest))),
      qs.length = m.regs.X1.toNat → (∀ q ∈ qs, q < 2 ^ 32 ∧ q ∈ ps) →
      WordsAt m.dmem m.regs.X0.toBitVec (qs.map Nat.toUInt64) →
      ps.length = m.regs.X3.toNat → (∀ p ∈ ps, p < 2 ^ 64) →
      WordsAt m.dmem m.regs.X2.toBitVec (ps.map Nat.toUInt64) →
      leaves.length = ps.length → (∀ x ∈ leaves, x.length = lw) →
      LeavesAt m.dmem m.regs.X4.toBitVec leaves →
      sibs.length = h → SibsAt m.dmem m.regs.X7.toBitVec cnt sibs →
      m'.regs.X0 = 1 ∧
        PhaseAt m'.dmem out (phaseW ⟨h, lw, qs.map (openingAt ps leaves sibs h)⟩)) ∧
    SameOutside m.dmem m'.dmem (InAny [⟨out, phaseBytes⟩, stackR m writeOpeningsStack]) ∧
    Saved m m'

/-! ## `phase_m`, `decode` -/

/-- `phase_m`'s precondition. -/
def PhaseMPre (m : MachineData) : Prop :=
  let r := m.regs.X0.toBitVec; let out := m.regs.X1.toBitVec; let w := m.regs.X2.toBitVec
  StackOk m phaseMStack ∧ NativeRustcVmArm.RcAt m phaseMStack ∧
    Region.Ok m.dmem ⟨out, phaseBytes⟩ ∧ Region.Ok m.dmem ⟨w, workBytes⟩ ∧
    ∃ bp B c, ReaderAt m.dmem r bp B c ∧
      Disjoint [stackR m phaseMStack, rcR, ⟨r, 24⟩, ⟨bp, B.length⟩, ⟨out, phaseBytes⟩,
        ⟨w, workBytes⟩]

/-- `phase_m`'s postcondition. -/
def PhaseMPost (m m' : MachineData) : Prop :=
  let r := m.regs.X0.toBitVec; let out := m.regs.X1.toBitVec; let w := m.regs.X2.toBitVec
  (∀ bp B c, ReaderAt m.dmem r bp B c →
    match phaseM B c with
    | some (po, c') => m'.regs.X0 = 1 ∧ PhaseAt m'.dmem out (phaseW po) ∧
        ReaderAt m'.dmem r bp B c'
    | none => m'.regs.X0 = 0) ∧
    SameOutside m.dmem m'.dmem (InAny [⟨out, phaseBytes⟩, ⟨w, workBytes⟩, curRegion r,
      stackR m phaseMStack]) ∧ Saved m m'

/-- `decode`'s precondition: the wire's `L < 2 ^ 32` bytes at X0 (any address when `L = 0`), the
decoded area of at least `decodedWords L` words at X2, the working area at X4. -/
def DecodePre (m : MachineData) : Prop :=
  let bp := m.regs.X0.toBitVec; let L := m.regs.X1.toNat; let dec := m.regs.X2.toBitVec
  let len := m.regs.X3.toNat; let w := m.regs.X4.toBitVec
  StackOk m decodeStack ∧ NativeRustcVmArm.RcAt m decodeStack ∧ L < 2 ^ 32 ∧
    decodedWords L ≤ len ∧ Region.Ok m.dmem ⟨bp, L⟩ ∧ Region.Ok m.dmem ⟨dec, 8 * len⟩ ∧
    Region.Ok m.dmem ⟨w, workBytes⟩ ∧
    Disjoint [stackR m decodeStack, rcR, ⟨dec, 8 * len⟩, ⟨w, workBytes⟩] ∧
    (0 < L → Disjoint [stackR m decodeStack, rcR, ⟨bp, L⟩, ⟨dec, 8 * len⟩, ⟨w, workBytes⟩])

/-- `decode`'s postcondition: for the wire bytes `B`, `Some` exactly when `decodeM B` decodes,
the area then holding the decoded proof. -/
def DecodePost (m m' : MachineData) : Prop :=
  let bp := m.regs.X0.toBitVec; let L := m.regs.X1.toNat; let dec := m.regs.X2.toBitVec
  let len := m.regs.X3.toNat; let w := m.regs.X4.toBitVec
  (∀ B : List UInt8, B.length = L → BytesAt m.dmem bp B →
    match decodeM B with
    | some r => m'.regs.X0 = 1 ∧ DecodedAt m'.dmem ⟨dec, len, L⟩ (streamW r.1) (openingsW r.2)
    | none => m'.regs.X0 = 0) ∧
    SameOutside m.dmem m'.dmem (InAny [⟨dec, 8 * len⟩, ⟨w, workBytes⟩, stackR m decodeStack]) ∧
    Saved m m'

end

end

end NativeRustcVmArm
