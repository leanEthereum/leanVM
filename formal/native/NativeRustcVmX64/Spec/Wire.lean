module

public import NativeRustcVmX64.Spec.Keccak
public import NativeRustcVmX64.Basic
public import NativeRustcVm.Wire.Rep
public import NativeRustcVmX64.Code.Vm.ClimbLevel.Names
public import NativeRustcVmX64.Code.Vm.Decode.Names
public import NativeRustcVmX64.Code.Vm.Find.Names
public import NativeRustcVmX64.Code.Vm.InsD.Names
public import NativeRustcVmX64.Code.Vm.PhaseM.Names
public import NativeRustcVmX64.Code.Vm.RdRows.Names
public import NativeRustcVmX64.Code.Vm.ReaderDigest.Names
public import NativeRustcVmX64.Code.Vm.ReaderLe.Names
public import NativeRustcVmX64.Code.Vm.ReaderWords.Names
public import NativeRustcVmX64.Code.Vm.WriteOpenings.Names

/-!
# The contracts of `wire.rs`'s functions on x86-64

The AArch64 contracts (`NativeRustcVmArm.Spec.Wire`) with the System V registers: arguments in
RDI, RSI, RDX, RCX, R8, R9, then on the stack above the return address; a `usize`/`u64` result in
RAX, an `Option<u64>` or `Option<usize>` in RAX (the tag, `1` for `Some`, `0` for `None`) and RDX;
a `bool`, `Option<()>` or `Option<bool>` in AL alone (`boolRet`: rustc sets AL only). Each
function uses the stack below RSP (`<fn>Stack` bytes: its pushes, its frame, its callees' return
addresses and stacks; `StackOk` in its precondition also maps the return address at RSP) and
returns with the callee-saved registers kept (and RSP 8 above, `Spec`), no byte changed outside
its outputs and that stack (`frameR`). Regions are `NativeRustcVm.Region`s, data memory not
wrapping (`Region.Ok`), pairwise apart where listed (`Disjoint`), the stack with the return address
(`stackR`, `n + 8` bytes: unlike AArch64's, x86-64's return address is in memory, so even a leaf's
outputs are apart from it). The reader at `r` is `NativeRustcVm.Wire.ReaderAt`; a read moves only
its cursor word (`curRegion r`). The hashing callers require loader GOT slots for `memcpy` and
`memset`, kept apart from their existing writable areas, stack and round constants. Reader
operations and `write_openings` reach no GOT-reading callee. Results follow the model
`NativeVm.Wire.decodeM`:

- `Reader::le(r, n)` (RDI, RSI; rustc reads at least four bytes: `n` is `4` or `8`): `rdLe B c n`,
  the tag in RAX, the word in RDX.
- `Reader::digest(out, r)` (RDI the `Option<Digest>`, 40 bytes; RSI): `rdDigest`.
- `Reader::words(r, out, n)` (RDI, RSI, RDX): `rdWords`, the words at `out`; AL.
- `ins_d(sorted, n, x)` (RDI, RSI, RDX): `insD` of the first `n < 256` words; the new count in
  RAX.
- `find(nodes, len, key)` (RDI, RSI, RDX): the index of the first node of key `key`, the tag in
  RAX, the index in RDX.
- `rd_rows(r, n, lw, rw, leaves)` (RDI to R8, `0 < n ≤ 256`, `rw ≤ lw ≤ 64`; rustc assumes a row,
  as `phase_m` always has one): `rdRows`, each row `paddedLeaf` at `leaves + 512 i`; AL `1` if
  every row's first word is zero, `0` if not, `2` for `None`.
- `climb_level(r, nodes, len, sibs, next)` (RDI to R8, `len ≤ 256`): `sibsM` and `parentsOf`, the
  tag in RAX, the parents' count in RDX.
- `write_openings(qs, nq, ps, np, leaves, lw, [h, sibs, sib_counts, out])` (RDI to R9, then four
  words above the return address, `stackArg`; `0 < nq`, `0 < np`; rustc dropped `out`'s length,
  `PHASE_WORDS`): the phase of the openings `openingAt`; AL.
- `phase_m(r, out, w)` (RDI, RSI, RDX; rustc dropped `out`'s length): `phaseM`, the phase at
  `out`; AL.
- `decode(bytes, L, dec, len, w)` (RDI to R8): `decodeM`, the decoded proof `DecodedAt` the area;
  AL.
-/

namespace NativeRustcVmX64

open NativeRustcVm NativeRustcVm.Wire NativeRustcVm.Transcript NativeVm NativeVm.Wire
open NativeRustcX64 (Spec StackOk Saved stackBelow rspOf reg)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-! ## Stacks -/

/-- `Reader::le` uses no stack. -/
def readerLeStack : Nat := 0
/-- The stack `Reader::digest` uses: its 5 pushes, then `Reader::le`'s return address. -/
def readerDigestStack : Nat := 40 + 8 + readerLeStack
/-- The stack `Reader::words` uses: its 5 pushes, then `Reader::le`'s return address. -/
def readerWordsStack : Nat := 40 + 8 + readerLeStack
/-- `ins_d` uses no stack. -/
def insDStack : Nat := 0
/-- `find` uses no stack. -/
def findStack : Nat := 0
/-- The stack `rd_rows` uses: its 6 pushes, its 24-byte frame, then `Reader::words`'s return
address and stack. -/
def rdRowsStack : Nat := 48 + 24 + 8 + readerWordsStack
/-- The stack `climb_level` uses: its 6 pushes, its 152-byte frame, then `hash_pair`'s return
address and stack (above `Reader::digest`'s). -/
def climbLevelStack : Nat := 48 + 152 + 8 + hashPairStack
/-- The stack `write_openings` uses: its 6 pushes, its 104-byte frame, then `find`'s return
address. -/
def writeOpeningsStack : Nat := 48 + 104 + 8 + findStack
/-- The stack `phase_m` uses: its 6 pushes, its 104-byte frame, then `climb_level`'s return
address and stack (the largest of its callees', `write_openings`'s with its four argument words
included). -/
def phaseMStack : Nat := 48 + 104 + 8 + climbLevelStack
/-- The stack `decode` uses: its 6 pushes, its 24-byte frame, then `phase_m`'s return address and
stack. -/
def decodeStack : Nat := 48 + 24 + 8 + phaseMStack

section
variable [Labels]

/-- The `n` bytes below RSP and the return address at RSP. -/
def stackR (m : MachineData) (n : Nat) : Region := ⟨stackBelow m n, n + 8⟩

/-- The `n` bytes below RSP: what a function may change of the stack. -/
def frameR (m : MachineData) (n : Nat) : Region := ⟨stackBelow m n, n⟩

/-- The round constants' bytes. -/
def rcR : Region := ⟨rcAddr, 192⟩

/-! ## `Reader::le`, `Reader::digest`, `Reader::words` -/

/-- `Reader::le`'s precondition: the reader apart from the return address it writes beside. -/
def ReaderLePre (m : MachineData) : Prop :=
  let r := reg m .rdi
  StackOk m readerLeStack ∧ ((reg m .rsi).toNat = 4 ∨ (reg m .rsi).toNat = 8) ∧
    ∃ bp B c, ReaderAt m.dmem r bp B c ∧ Disjoint [stackR m readerLeStack, ⟨r, 24⟩]

/-- `Reader::le`'s postcondition. -/
def ReaderLePost (m m' : MachineData) : Prop :=
  let r := reg m .rdi
  (∀ bp B c, ReaderAt m.dmem r bp B c →
    match rdLe B c (reg m .rsi).toNat with
    | some (v, c') => reg m' .rax = 1 ∧ reg m' .rdx = v.toBitVec ∧ ReaderAt m'.dmem r bp B c'
    | none => reg m' .rax = 0) ∧
    SameOutside m.dmem m'.dmem (curRegion r).Holds ∧ Saved m m'

/-- `Reader::digest`'s precondition. -/
def ReaderDigestPre (m : MachineData) : Prop :=
  let out := reg m .rdi; let r := reg m .rsi
  StackOk m readerDigestStack ∧ Region.Ok m.dmem ⟨out, 40⟩ ∧
    ∃ bp B c, ReaderAt m.dmem r bp B c ∧
      Disjoint [stackR m readerDigestStack, ⟨r, 24⟩, ⟨bp, B.length⟩, ⟨out, 40⟩]

/-- `Reader::digest`'s postcondition. -/
def ReaderDigestPost (m m' : MachineData) : Prop :=
  let out := reg m .rdi; let r := reg m .rsi
  (∀ bp B c, ReaderAt m.dmem r bp B c →
    match rdDigest B c with
    | some (dg, c') => WordAt m'.dmem out 1 ∧ WordsAt m'.dmem (off out 8) dg.toList ∧
        ReaderAt m'.dmem r bp B c'
    | none => WordAt m'.dmem out 0) ∧
    SameOutside m.dmem m'.dmem (InAny [⟨out, 40⟩, curRegion r, frameR m readerDigestStack]) ∧
    Saved m m'

/-- `Reader::words`'s precondition. -/
def ReaderWordsPre (m : MachineData) : Prop :=
  let r := reg m .rdi; let out := reg m .rsi; let n := (reg m .rdx).toNat
  StackOk m readerWordsStack ∧ Region.Ok m.dmem ⟨out, 8 * n⟩ ∧
    ∃ bp B c, ReaderAt m.dmem r bp B c ∧
      Disjoint [stackR m readerWordsStack, ⟨r, 24⟩, ⟨bp, B.length⟩, ⟨out, 8 * n⟩]

/-- `Reader::words`'s postcondition. -/
def ReaderWordsPost (m m' : MachineData) : Prop :=
  let r := reg m .rdi; let out := reg m .rsi; let n := (reg m .rdx).toNat
  (∀ bp B c, ReaderAt m.dmem r bp B c →
    match rdWords B n c with
    | some (ws, c') => boolRet m' = 1 ∧ WordsAt m'.dmem out (ws.map K.lane) ∧
        ReaderAt m'.dmem r bp B c'
    | none => boolRet m' = 0) ∧
    SameOutside m.dmem m'.dmem (InAny [⟨out, 8 * n⟩, curRegion r, frameR m readerWordsStack]) ∧
    Saved m m'

/-! ## `ins_d`, `find` -/

/-- `ins_d`'s precondition. -/
def InsDPre (m : MachineData) : Prop :=
  StackOk m insDStack ∧ (reg m .rsi).toNat < 256 ∧ Region.Ok m.dmem ⟨reg m .rdi, 2048⟩ ∧
    Disjoint [stackR m insDStack, ⟨reg m .rdi, 2048⟩]

/-- `ins_d`'s postcondition. -/
def InsDPost (m m' : MachineData) : Prop :=
  let a := reg m .rdi
  (∀ l : List Nat, l.length = (reg m .rsi).toNat → (∀ y ∈ l, y < 2 ^ 64) →
    WordsAt m.dmem a (l.map Nat.toUInt64) →
    (reg m' .rax).toNat = (insD l (reg m .rdx).toNat).length ∧
      WordsAt m'.dmem a ((insD l (reg m .rdx).toNat).map Nat.toUInt64)) ∧
    SameOutside m.dmem m'.dmem (InRange a 2048) ∧ Saved m m'

/-- `find`'s precondition. -/
def FindPre (m : MachineData) : Prop :=
  StackOk m findStack ∧ Region.Ok m.dmem ⟨reg m .rdi, 40 * (reg m .rsi).toNat⟩

/-- `find`'s postcondition. -/
def FindPost (m m' : MachineData) : Prop :=
  let a := reg m .rdi
  (∀ ks : List UInt64, ks.length = (reg m .rsi).toNat →
    (∀ i (h : i < ks.length), WordAt m.dmem (off a (40 * i)) ks[i]) →
    match ks.findIdx? (· == UInt64.ofBitVec (reg m .rdx)) with
    | some i => reg m' .rax = 1 ∧ (reg m' .rdx).toNat = i
    | none => reg m' .rax = 0) ∧
    m'.dmem = m.dmem ∧ Saved m m'

/-! ## `rd_rows`, `climb_level` -/

/-- `rd_rows`'s precondition. -/
def RdRowsPre (m : MachineData) : Prop :=
  let r := reg m .rdi; let n := (reg m .rsi).toNat; let lw := (reg m .rdx).toNat
  let rw := (reg m .rcx).toNat; let lv := reg m .r8
  StackOk m rdRowsStack ∧ 0 < n ∧ n ≤ 256 ∧ lw ≤ 64 ∧ rw ≤ lw ∧ Region.Ok m.dmem ⟨lv, 512 * n⟩ ∧
    ∃ bp B c, ReaderAt m.dmem r bp B c ∧
      Disjoint [stackR m rdRowsStack, ⟨r, 24⟩, ⟨bp, B.length⟩, ⟨lv, 512 * n⟩]

/-- `rd_rows`'s postcondition. -/
def RdRowsPost (m m' : MachineData) : Prop :=
  let r := reg m .rdi; let n := (reg m .rsi).toNat; let lw := (reg m .rdx).toNat
  let rw := (reg m .rcx).toNat; let lv := reg m .r8
  (∀ bp B c, ReaderAt m.dmem r bp B c →
    match rdRows B rw n c with
    | some (rows, c') => boolRet m' = (if ∀ x ∈ rows, x.getD 0 0 = 0 then 1 else 0) ∧
        LeavesAt m'.dmem lv (rows.map fun x ↦ paddedLeaf x lw) ∧
        ReaderAt m'.dmem r bp B c'
    | none => boolRet m' = 2) ∧
    SameOutside m.dmem m'.dmem (InAny [⟨lv, 512 * n⟩, curRegion r, frameR m rdRowsStack]) ∧
    Saved m m'

/-- `climb_level`'s precondition. -/
def ClimbLevelPre (m : MachineData) : Prop :=
  let r := reg m .rdi; let nodes := reg m .rsi; let n := (reg m .rdx).toNat
  let sibs := reg m .rcx; let next := reg m .r8
  StackOk m climbLevelStack ∧ RcAt m climbLevelStack ∧ n ≤ 256 ∧
    Region.Ok m.dmem ⟨nodes, 40 * n⟩ ∧ Region.Ok m.dmem ⟨sibs, nodesBytes⟩ ∧
    Region.Ok m.dmem ⟨next, nodesBytes⟩ ∧
    ∃ bp B c, ReaderAt m.dmem r bp B c ∧
      Disjoint [stackR m climbLevelStack, rcR, ⟨r, 24⟩, ⟨bp, B.length⟩, ⟨nodes, 40 * n⟩,
        ⟨sibs, nodesBytes⟩, ⟨next, nodesBytes⟩] ∧
      NativeRustcX64.GotAt m climbLevelStack
        [(rcAddr, 192), (r, 24), (sibs, nodesBytes), (next, nodesBytes)] ["memcpy", "memset"]

/-- `climb_level`'s postcondition. -/
def ClimbLevelPost (m m' : MachineData) : Prop :=
  let r := reg m .rdi; let nodes := reg m .rsi; let n := (reg m .rdx).toNat
  let sibs := reg m .rcx; let next := reg m .r8
  (∀ bp B c, ReaderAt m.dmem r bp B c → ∀ ns, ns.length = n → NodesAt m.dmem nodes ns →
    match sibsM B ns ns c with
    | some (sl, c') => reg m' .rax = 1 ∧ (reg m' .rdx).toNat = (parentsOf ns sl).length ∧
        NodesAt m'.dmem sibs (sl.map fun s ↦ (s.1, s.2.1)) ∧
        NodesAt m'.dmem next (parentsOf ns sl) ∧ ReaderAt m'.dmem r bp B c'
    | none => reg m' .rax = 0) ∧
    SameOutside m.dmem m'.dmem (InAny [⟨sibs, nodesBytes⟩, ⟨next, nodesBytes⟩, curRegion r,
      frameR m climbLevelStack]) ∧ Saved m m'

/-! ## `write_openings` -/

/-- `write_openings`'s regions: the queries, the positions, the leaves, the siblings (`h` levels
from `stackArg m 1`), their counts (from `stackArg m 2`), and the phase's words (from
`stackArg m 3`). -/
def writeOpeningsRegions (m : MachineData) : List Region :=
  let h := (stackArg m 0).toNat
  [⟨reg m .rdi, 8 * (reg m .rsi).toNat⟩, ⟨reg m .rdx, 8 * (reg m .rcx).toNat⟩,
    ⟨reg m .r8, 512 * (reg m .rcx).toNat⟩, ⟨stackArg m 1, nodesBytes * h⟩,
    ⟨stackArg m 2, 8 * h⟩, ⟨stackArg m 3, phaseBytes⟩]

/-- `write_openings`'s precondition: its last four arguments, the levels' count `h`, the
siblings', the sibling counts' and the phase's addresses, above the return address (`ArgsOk`,
`stackArg`); `0 < nq`, `0 < np`: rustc's loops over the queries and the positions test at their
ends. -/
def WriteOpeningsPre (m : MachineData) : Prop :=
  StackOk m writeOpeningsStack ∧ ArgsOk m 4 ∧ (reg m .rsi).toNat ≤ 256 ∧
    (reg m .rcx).toNat ≤ 256 ∧ (reg m .r9).toNat ≤ 64 ∧ (stackArg m 0).toNat ≤ 32 ∧
    0 < (reg m .rsi).toNat ∧ 0 < (reg m .rcx).toNat ∧
    (∀ R ∈ writeOpeningsRegions m, R.Ok m.dmem) ∧
    Disjoint (stackR m writeOpeningsStack :: ⟨off (rspOf m) 8, 32⟩ :: writeOpeningsRegions m)

/-- `write_openings`'s postcondition: given the queries `qs` (below `2 ^ 32`, each a position),
the positions `ps`, their leaves of `lw` words and `h` levels of siblings, the phase at `out`. -/
def WriteOpeningsPost (m m' : MachineData) : Prop :=
  let lw := (reg m .r9).toNat; let h := (stackArg m 0).toNat
  let out := stackArg m 3
  (∀ (qs ps : List Nat) (leaves : List (List K)) (sibs : List (List (Nat × Digest))),
    qs.length = (reg m .rsi).toNat → (∀ q ∈ qs, q < 2 ^ 32 ∧ q ∈ ps) →
    WordsAt m.dmem (reg m .rdi) (qs.map Nat.toUInt64) →
    ps.length = (reg m .rcx).toNat → (∀ p ∈ ps, p < 2 ^ 64) →
    WordsAt m.dmem (reg m .rdx) (ps.map Nat.toUInt64) →
    leaves.length = ps.length → (∀ x ∈ leaves, x.length = lw) →
    LeavesAt m.dmem (reg m .r8) leaves →
    sibs.length = h → SibsAt m.dmem (stackArg m 1) (stackArg m 2) sibs →
    boolRet m' = 1 ∧ PhaseAt m'.dmem out (phaseW ⟨h, lw, qs.map (openingAt ps leaves sibs h)⟩)) ∧
    SameOutside m.dmem m'.dmem (InAny [⟨out, phaseBytes⟩, frameR m writeOpeningsStack]) ∧
    Saved m m'

/-! ## `phase_m`, `decode` -/

/-- `phase_m`'s precondition. -/
def PhaseMPre (m : MachineData) : Prop :=
  let r := reg m .rdi; let out := reg m .rsi; let w := reg m .rdx
  StackOk m phaseMStack ∧ RcAt m phaseMStack ∧
    Region.Ok m.dmem ⟨out, phaseBytes⟩ ∧ Region.Ok m.dmem ⟨w, workBytes⟩ ∧
    ∃ bp B c, ReaderAt m.dmem r bp B c ∧
      Disjoint [stackR m phaseMStack, rcR, ⟨r, 24⟩, ⟨bp, B.length⟩, ⟨out, phaseBytes⟩,
        ⟨w, workBytes⟩] ∧
      NativeRustcX64.GotAt m phaseMStack
        [(rcAddr, 192), (r, 24), (out, phaseBytes), (w, workBytes)] ["memcpy", "memset"]

/-- `phase_m`'s postcondition. -/
def PhaseMPost (m m' : MachineData) : Prop :=
  let r := reg m .rdi; let out := reg m .rsi; let w := reg m .rdx
  (∀ bp B c, ReaderAt m.dmem r bp B c →
    match phaseM B c with
    | some (po, c') => boolRet m' = 1 ∧ PhaseAt m'.dmem out (phaseW po) ∧
        ReaderAt m'.dmem r bp B c'
    | none => boolRet m' = 0) ∧
    SameOutside m.dmem m'.dmem (InAny [⟨out, phaseBytes⟩, ⟨w, workBytes⟩, curRegion r,
      frameR m phaseMStack]) ∧ Saved m m'

/-- `decode`'s precondition: the wire's `L < 2 ^ 32` bytes at RDI (any address when `L = 0`), the
decoded area of at least `decodedWords L` words at RDX, the working area at R8. -/
def DecodePre (m : MachineData) : Prop :=
  let bp := reg m .rdi; let L := (reg m .rsi).toNat; let dec := reg m .rdx
  let len := (reg m .rcx).toNat; let w := reg m .r8
  StackOk m decodeStack ∧ RcAt m decodeStack ∧ L < 2 ^ 32 ∧
    decodedWords L ≤ len ∧ Region.Ok m.dmem ⟨bp, L⟩ ∧ Region.Ok m.dmem ⟨dec, 8 * len⟩ ∧
    Region.Ok m.dmem ⟨w, workBytes⟩ ∧
    Disjoint [stackR m decodeStack, rcR, ⟨dec, 8 * len⟩, ⟨w, workBytes⟩] ∧
    (0 < L → Disjoint [stackR m decodeStack, rcR, ⟨bp, L⟩, ⟨dec, 8 * len⟩, ⟨w, workBytes⟩]) ∧
    NativeRustcX64.GotAt m decodeStack
      [(rcAddr, 192), (dec, 8 * len), (w, workBytes)] ["memcpy", "memset"]

/-- `decode`'s postcondition: for the wire bytes `B`, `Some` exactly when `decodeM B` decodes,
the area then holding the decoded proof. -/
def DecodePost (m m' : MachineData) : Prop :=
  let bp := reg m .rdi; let L := (reg m .rsi).toNat; let dec := reg m .rdx
  let len := (reg m .rcx).toNat; let w := reg m .r8
  (∀ B : List UInt8, B.length = L → BytesAt m.dmem bp B →
    match decodeM B with
    | some r => boolRet m' = 1 ∧ DecodedAt m'.dmem ⟨dec, len, L⟩ (streamW r.1) (openingsW r.2)
    | none => boolRet m' = 0) ∧
    SameOutside m.dmem m'.dmem (InAny [⟨dec, 8 * len⟩, ⟨w, workBytes⟩, frameR m decodeStack]) ∧
    Saved m m'

end

end

end NativeRustcVmX64
