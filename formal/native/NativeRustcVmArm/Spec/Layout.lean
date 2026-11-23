module

public import NativeRustcVmArm.Code.Vm.BuildLayout.Names
public import NativeRustcVmArm.Code.Vm.ColumnKappas.Names
public import NativeRustcVmArm.Code.Vm.CommitStack.Names
public import NativeRustcVmArm.Code.Vm.ConstraintsW.Names
public import NativeRustcVmArm.Code.Vm.Evaluate.Names
public import NativeRustcVmArm.Code.Vm.FormBufAddScaled.Names
public import NativeRustcVmArm.Code.Vm.FormBufAddTerm.Names
public import NativeRustcVmArm.Code.Vm.FormTerms.Names
public import NativeRustcVmArm.Code.Vm.InsertionSortOfStackOffsets.Names
public import NativeRustcVmArm.Code.Vm.Ladder.Names
public import NativeRustcVmArm.Code.Vm.LayoutWPlacement.Names
public import NativeRustcVmArm.Code.Vm.PlacementsOf.Names
public import NativeRustcVmArm.Code.Vm.PushClaim.Names
public import NativeRustcVmArm.Code.Vm.ReadAnnouncedSizes.Names
public import NativeRustcVmArm.Code.Vm.ReadOod.Names
public import NativeRustcVmArm.Code.Vm.StackOffsets.Names
public import NativeRustcVmArm.Code.Vm.StackPoint.Names
public import NativeRustcVmArm.Spec.Arrays
public import NativeRustcVmArm.Spec.Transcript
public import NativeRustcVmArm.Rodata
public import NativeRustcVm.Layout.Values

/-!
# The contracts of `layout.rs`'s and `stack.rs`'s functions and `whir.rs`'s `ladder` on AArch64

Each function uses the stack below SP (`<fn>Stack` bytes, its callees' included; `StackOk` in its
precondition) and returns with the callee-saved registers and SP kept (`Saved`), no byte changed
outside its outputs and that stack. Arguments and results as `Spec/Arrays.lean` reads them (slices
`slice`, `E` elements `ewArg`/`ewRet`, `Changes`); `usize` slices as numbers (`natsOf`); the
crate's structs as `NativeRustcVm.Layout`'s representations (`LayoutWAt`, `FormBufAt`, `TermsAt`,
`ClaimsWAt`, `OodAt`, `LadderAt`). Those reading `data.rs`'s arrays take them at their labels
(`RodataAt`), their outputs apart from them (`RodataApart`). Results are the model's
(`NativeVm.Model`); rustc's internal ABI returns an `Option<usize>` as tag X0, value X1, an
`Option<()>` as X0 `0`/`1` (`okWord`), a larger value through a pointer in X0.

- `form_terms(form)` (X0): the slice (X0, X1) of `formAt form`'s terms, inside `TERMS` (`InTerms`).
- `evaluate(terms, row)` (X0, X1; X2, X3): `FormW.evaluate` in X0, X1.
- `FormBuf::add_term(self, t, c)` (X0, X1; `c` X2, X3): `FormW.addTerm`, `None` past `formCap`.
- `FormBuf::add_scaled(self, other, weight)` (X0; X1, X2; X3, X4): `FormW.addScaled`, `None` past
  `formCap`.
- `constraints_w(opcode, row, out)` (X0; X1, X2; X3): `constraintsW` at `out`, its count in X0.
- `LayoutW::placement(self, column)` (X0, X1; rustc dropped the bounds check: `column < 158`):
  `LayoutW.placement` in X0, X1.
- `stack_point(p, point, stack_log, out)` (`p` X0, X1; X2, X3; X4; X5, rustc fixed `out`'s length
  to `66`): `stackPoint` at `out`, its length in X1, or `None` when longer than `66`.
- `insertion_sort(order, |i, j| …)` (X0, X1; the closure's `sizes` X2, X3): `insertionSort`.
- `stack_offsets(sizes, offsets)` (X0, X1; X2, X3; rustc dropped `n ≤ 158`): `stackOffsets`, or
  `None` when `offsets` is shorter or the blocks do not fit a `u64` (`OffsetsFit`).
- `column_kappas(out, log_memory, log_bytecode, heights)` (X0 the `[usize; 158]`; X1; X2; X3):
  `columnKappas`.
- `placements_of(kappas, placements)` (X0, X1; every `kappa ≤ 36`, as `build_layout` gives):
  `placementsOf`, always `Some`.
- `build_layout(bytecode_len, log_memory, table_rows, layout)` (X0 to X3): `buildLayout`, the layout
  at X3.
- `read_announced_sizes(t, bytecode_len, layout)` (X0, X1, X2): `readAnnouncedSizes`, the layout
  at X2, the rate exponent in X1.
- `ladder(out, mu, log_inv_rate)` (X0 the result; X1, X2): `Whir.ladder`.
- `commit_stack(t, log_n, log_inv_rate)` (X0, X1, X2; fewer than `8` roots read): `commitStack`.
- `read_ood(t, stack_log, out)` (X0, X1, X2; `stack_log ≤ 30`): `readOod`, the claim at `out`.
- `push_claim(claims, column, point, value)` (X0; X1; X2, X3; X4, X5): the claim appended, `None`
  at `claimCap` claims or past `pointCap` coordinates.
-/

namespace NativeRustcVmArm

open NativeRustcArm NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Layout
open LeanVM.Parameters
open NativeRustcVm (wordsOf EWsAt WordsAt)

@[expose] public section

/-! ## Symbols -/


/-! ## Stacks -/

/-- `form_terms` uses no stack. -/
def formTermsStack : Nat := 0
/-- The stack `evaluate` uses: its 80-byte frame and `EW::mul`'s. -/
def evaluateStack : Nat := 80 + ewMulStack
/-- `FormBuf::add_term` uses no stack. -/
def formBufAddTermStack : Nat := 0
/-- The stack `FormBuf::add_scaled` uses: its 48-byte frame and `EW::mul`'s (`add_term` uses
none). -/
def formBufAddScaledStack : Nat := 48 + ewMulStack
/-- The stack `constraints_w` uses: its 48-byte frame and `EW::mul`'s. -/
def constraintsWStack : Nat := 48 + ewMulStack
/-- `LayoutW::placement` uses no stack. -/
def layoutWPlacementStack : Nat := 0
/-- The stack `stack_point` uses: its 16-byte frame (`selector_point` uses none). -/
def stackPointStack : Nat := 16 + selectorPointStack
/-- `insertion_sort` uses no stack. -/
def insertionSortStack : Nat := 0
/-- The stack `stack_offsets` uses: 64 bytes of saved registers and the 1264-byte `order` array
(`memset`, `insertion_sort` and `bit_length` use none). -/
def stackOffsetsStack : Nat := 64 + 1264 + insertionSortStack + bitLengthStack
/-- `column_kappas` uses no stack. -/
def columnKappasStack : Nat := 0
/-- The stack `placements_of` uses: 80 bytes of saved registers, its four 1264-byte arrays, and
`stack_offsets`'s. -/
def placementsOfStack : Nat := 80 + 4 * 1264 + stackOffsetsStack
/-- The stack `build_layout` uses: 96 bytes of saved registers, the 1264-byte `kappas`, and
`placements_of`'s. -/
def buildLayoutStack : Nat := 96 + 1264 + placementsOfStack
/-- The stack `read_announced_sizes` uses: its 208-byte frame and `read_scalars`' or
`build_layout`'s. -/
def readAnnouncedSizesStack : Nat := 208 + max readScalarsStack buildLayoutStack
/-- `ladder` uses no stack. -/
def ladderStack : Nat := 0
/-- The stack `commit_stack` uses: its 192-byte frame (`ladder` uses none), or `read_commitment`'s,
which it tail-calls from its own entry's SP. -/
def commitStackStack : Nat := max (192 + ladderStack) readCommitmentStack
/-- The stack `read_ood` uses: its 64-byte frame and `grind`'s, `sample_challenges`' or
`read_scalar`'s. -/
def readOodStack : Nat := 64 + max grindStack (max sampleChallengesStack readScalarStack)
/-- The stack `push_claim` uses: its 48-byte frame (`Buf::extend` uses none). -/
def pushClaimStack : Nat := 48 + bufExtendStack

/-! ## Values -/

/-- The `n` numbers (`usize`) from `a`. -/
def natsOf (m : MachineData) (a : UInt64) (n : Nat) : Array Nat :=
  ((wordsOf m.dmem a.toBitVec n).map UInt64.toNat).toArray

/-- Numbers as `usize` words. -/
def natWords (xs : Array Nat) : List UInt64 := xs.toList.map Nat.toUInt64

/-- `stack_point`'s output: `66` elements of `E`. -/
def stackPointOut : Nat := 66

/-- The `[usize; 158]` `column_kappas` returns, `placements_of` reads. -/
def kappasBytes : Nat := 8 * columnCountW

/-- `LayoutW.placements`' bytes. -/
def placementsBytes : Nat := placementBytes * columnCountW

/-- `read_ood`'s and `read_announced_sizes`' `TState` reads `stack_log ≤ 30`. -/
abbrev maxStackLog : Nat := stackCap

section
variable [Labels]

/-- The `n` terms from `a` are inside `TERMS`, or none. -/
def InTerms (a : BitVec 64) (n : Nat) : Prop :=
  n = 0 ∨ ∃ k, k + n ≤ NativeRustcVm.Data.terms.length ∧
    a = rodataAddr .terms + BitVec.ofNat 64 (termBytes * k)

/-! ## Forms -/

/-- `form_terms`'s precondition. -/
def FormTermsPre (m : MachineData) : Prop := RodataAt m formTermsStack

/-- `form_terms`'s postcondition. -/
def FormTermsPost (m m' : MachineData) : Prop :=
  let f := formAt m.regs.X0.toNat
  m'.regs.X1.toNat = f.size ∧ TermsAt m'.dmem m'.regs.X0.toBitVec f ∧
    InTerms m'.regs.X0.toBitVec f.size ∧ SameOutside m.dmem m'.dmem (fun _ ↦ False) ∧ Saved m m'

/-- `evaluate`'s precondition: the terms (X0, X1) represent `f`. -/
def EvaluatePre (f : FormW) (m : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let n := termBytes * m.regs.X1.toNat
  StackOk m evaluateStack ∧ m.regs.X1.toNat = f.size ∧ TermsAt m.dmem t f ∧ Readable m t n ∧
    OffStack m t n evaluateStack ∧ SliceOk m m.regs.X2 m.regs.X3 evaluateStack

/-- `evaluate`'s postcondition. -/
def EvaluatePost (f : FormW) (m m' : MachineData) : Prop :=
  ewRet m' = f.evaluate (slice m m.regs.X2 m.regs.X3) ∧ Changes m m' evaluateStack 0 0 ∧
    Saved m m'

/-- `FormBuf::add_term`'s precondition: the `FormBuf` at X0 represents `f`, the term at X1 `t`. -/
def FormBufAddTermPre (f : FormW) (t : TermW) (m : MachineData) : Prop :=
  let b := m.regs.X0.toBitVec; let p := m.regs.X1.toBitVec
  FormBufAt m.dmem b f ∧ TermWAt m.dmem p t ∧ Readable m b formBufBytes ∧ Readable m p termBytes ∧
    Apart b formBufBytes p termBytes

/-- `FormBuf::add_term`'s postcondition. -/
def FormBufAddTermPost (f : FormW) (t : TermW) (m m' : MachineData) : Prop :=
  let b := m.regs.X0.toBitVec
  let g := f.addTerm t.cols (ewArg m.regs.X2 m.regs.X3)
  (if g.size ≤ formCap then m'.regs.X0 = 1 ∧ FormBufAt m'.dmem b g else m'.regs.X0 = 0) ∧
    Changes m m' formBufAddTermStack b formBufBytes ∧ Saved m m'

/-- `FormBuf::add_scaled`'s precondition: the `FormBuf` at X0 represents `f`, the terms (X1, X2)
`other`. -/
def FormBufAddScaledPre (f other : FormW) (m : MachineData) : Prop :=
  let b := m.regs.X0.toBitVec; let p := m.regs.X1.toBitVec
  let n := termBytes * m.regs.X2.toNat; let s := formBufAddScaledStack
  StackOk m s ∧ m.regs.X2.toNat = other.size ∧ FormBufAt m.dmem b f ∧ TermsAt m.dmem p other ∧
    Readable m b formBufBytes ∧ OffStack m b formBufBytes s ∧ Readable m p n ∧ OffStack m p n s ∧
    Apart b formBufBytes p n

/-- `FormBuf::add_scaled`'s postcondition. -/
def FormBufAddScaledPost (f other : FormW) (m m' : MachineData) : Prop :=
  let b := m.regs.X0.toBitVec
  let g := f.addScaled other (ewArg m.regs.X3 m.regs.X4)
  (if g.size ≤ formCap then m'.regs.X0 = 1 ∧ FormBufAt m'.dmem b g else m'.regs.X0 = 0) ∧
    Changes m m' formBufAddScaledStack b formBufBytes ∧ Saved m m'

/-- `constraints_w`'s precondition: the row (X1, X2), the output's two elements at X3. -/
def ConstraintsWPre (m : MachineData) : Prop :=
  StackOk m constraintsWStack ∧ SliceOk m m.regs.X1 m.regs.X2 constraintsWStack ∧
    Readable m m.regs.X3.toBitVec 32 ∧ OffStack m m.regs.X3.toBitVec 32 constraintsWStack

/-- `constraints_w`'s postcondition. -/
def ConstraintsWPost (m m' : MachineData) : Prop :=
  let r := constraintsW m.regs.X0.toNat (slice m m.regs.X1 m.regs.X2)
  m'.regs.X0.toNat = r.size ∧ EWsAt m'.dmem m.regs.X3.toBitVec r.toList ∧
    Changes m m' constraintsWStack m.regs.X3.toBitVec 32 ∧ Saved m m'

/-! ## Placements -/

/-- `LayoutW::placement`'s precondition: the layout at X0 represents `L`, readable, a column below
`158`. -/
def LayoutWPlacementPre (L : LayoutW) (m : MachineData) : Prop :=
  m.regs.X1.toNat < columnCountW ∧ LayoutWAt m.dmem m.regs.X0.toBitVec L ∧
    Readable m m.regs.X0.toBitVec layoutBytes

/-- `LayoutW::placement`'s postcondition. -/
def LayoutWPlacementPost (L : LayoutW) (m m' : MachineData) : Prop :=
  let p := L.placement m.regs.X1.toNat
  m'.regs.X0 = p.variableCount.toUInt64 ∧ m'.regs.X1 = p.index.toUInt64 ∧
    SameOutside m.dmem m'.dmem (fun _ ↦ False) ∧ Saved m m'

/-- `stack_point`'s precondition: the point (X2, X3), the output's `66` elements at X5, fewer than
`64` coordinates (rustc's copy loop takes `|point| < 64` from its callers: `and x13, x3, #0x3e`). -/
def StackPointPre (m : MachineData) : Prop :=
  let o := m.regs.X5.toBitVec; let n := 16 * stackPointOut
  StackOk m stackPointStack ∧ SliceOk m m.regs.X2 m.regs.X3 stackPointStack ∧ Readable m o n ∧
    OffStack m o n stackPointStack ∧ Apart o n m.regs.X2.toBitVec (16 * m.regs.X3.toNat) ∧
    m.regs.X3.toNat < 64

/-- `stack_point`'s postcondition. -/
def StackPointPost (m m' : MachineData) : Prop :=
  let o := m.regs.X5.toBitVec; let n := m.regs.X3.toNat + (m.regs.X4.toNat - m.regs.X0.toNat)
  (if n ≤ stackPointOut then
      m'.regs.X0 = 1 ∧ m'.regs.X1.toNat = n ∧
        EWsAt m'.dmem o (stackPoint ⟨m.regs.X0.toNat, m.regs.X1.toNat⟩
          (slice m m.regs.X2 m.regs.X3) m.regs.X4.toNat).toList
    else m'.regs.X0 = 0) ∧
    Changes m m' stackPointStack o (16 * stackPointOut) ∧ Saved m m'

/-- `insertion_sort`'s precondition: the order (X0, X1), the sizes (X2, X3) apart from it. -/
def InsertionSortPre (m : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec; let s := m.regs.X2.toBitVec
  Readable m o (8 * m.regs.X1.toNat) ∧ Readable m s (8 * m.regs.X3.toNat) ∧
    Apart o (8 * m.regs.X1.toNat) s (8 * m.regs.X3.toNat)

/-- `insertion_sort`'s postcondition. -/
def InsertionSortPost (m m' : MachineData) : Prop :=
  let sizes := natsOf m m.regs.X2 m.regs.X3.toNat
  let o := m.regs.X0.toBitVec
  WordsAt m'.dmem o (natWords (insertionSort (sortLt (sizes.getD · 0))
      (natsOf m m.regs.X0 m.regs.X1.toNat))) ∧
    Changes m m' insertionSortStack o (8 * m.regs.X1.toNat) ∧ Saved m m'

/-- `stack_offsets`' precondition: at most `158` sizes (X0, X1), the offsets (X2, X3) apart. -/
def StackOffsetsPre (m : MachineData) : Prop :=
  let a := m.regs.X0.toBitVec; let n := 8 * m.regs.X1.toNat
  let o := m.regs.X2.toBitVec; let k := 8 * m.regs.X3.toNat
  StackOk m stackOffsetsStack ∧ m.regs.X1.toNat ≤ columnCountW ∧ Readable m a n ∧
    OffStack m a n stackOffsetsStack ∧ Readable m o k ∧ OffStack m o k stackOffsetsStack ∧
    Apart a n o k

/-- `stack_offsets`' postcondition. -/
def StackOffsetsPost (m m' : MachineData) : Prop :=
  let sizes := natsOf m m.regs.X0 m.regs.X1.toNat
  let o := m.regs.X2.toBitVec
  (if m.regs.X1.toNat ≤ m.regs.X3.toNat ∧ OffsetsFit sizes then
      m'.regs.X0 = 1 ∧ m'.regs.X1.toNat = (stackOffsets sizes).2 ∧
        WordsAt m'.dmem o (natWords (stackOffsets sizes).1)
    else m'.regs.X0 = 0) ∧
    Changes m m' stackOffsetsStack o (8 * m.regs.X3.toNat) ∧ Saved m m'

/-- `column_kappas`' precondition: the output's `158` words at X0, the six heights at X3, the
keccak table's `+ qkeccakSlotBits` not wrapping. -/
def ColumnKappasPre (m : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec; let h := m.regs.X3.toBitVec
  Readable m o kappasBytes ∧ Readable m h (8 * nTables) ∧ Apart o kappasBytes h (8 * nTables) ∧
    (natsOf m m.regs.X3 nTables).getD LeanVM.Protocol.Verifier.opKeccak 0 +
      LeanVM.Protocol.Verifier.qkeccakSlotBits < 2 ^ 64

/-- `column_kappas`' postcondition. -/
def ColumnKappasPost (m m' : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec
  WordsAt m'.dmem o (natWords (columnKappas m.regs.X1.toNat m.regs.X2.toNat
      (natsOf m m.regs.X3 nTables))) ∧
    Changes m m' columnKappasStack o kappasBytes ∧ Saved m m'

/-- `placements_of`'s precondition: the `158` log-sizes at X0, each at most `36`, the placements
at X1. -/
def PlacementsOfPre (m : MachineData) : Prop :=
  let k := m.regs.X0.toBitVec; let p := m.regs.X1.toBitVec; let s := placementsOfStack
  StackOk m s ∧ RodataAt m s ∧ Readable m k kappasBytes ∧ OffStack m k kappasBytes s ∧
    Readable m p placementsBytes ∧ OffStack m p placementsBytes s ∧ RodataApart p placementsBytes ∧
    Apart k kappasBytes p placementsBytes ∧ ∀ κ ∈ natsOf m m.regs.X0 columnCountW, κ ≤ 36

/-- `placements_of`'s postcondition. -/
def PlacementsOfPost (m m' : MachineData) : Prop :=
  let r := placementsOf (natsOf m m.regs.X0 columnCountW)
  let p := m.regs.X1.toBitVec
  m'.regs.X0 = 1 ∧ m'.regs.X1.toNat = r.2 ∧ r.1.size = columnCountW ∧
    (∀ c (h : c < r.1.size), PlacementWAt m'.dmem (off p (placementBytes * c)) r.1[c]) ∧
    Changes m m' placementsOfStack p placementsBytes ∧ Saved m m'

/-! ## Phase 1 -/

/-- `build_layout`'s precondition: X0 the bytecode's length, the six row counts at X2, the layout
at X3. -/
def BuildLayoutPre (bytecode : Array UInt64) (m : MachineData) : Prop :=
  let r := m.regs.X2.toBitVec; let l := m.regs.X3.toBitVec; let s := buildLayoutStack
  StackOk m s ∧ RodataAt m s ∧ m.regs.X0.toNat = bytecode.size ∧ Readable m r (8 * nTables) ∧
    OffStack m r (8 * nTables) s ∧ Readable m l layoutBytes ∧ OffStack m l layoutBytes s ∧
    RodataApart l layoutBytes ∧ Apart r (8 * nTables) l layoutBytes

/-- `build_layout`'s postcondition. -/
def BuildLayoutPost (bytecode : Array UInt64) (m m' : MachineData) : Prop :=
  let r := buildLayout bytecode m.regs.X1.toNat (natsOf m m.regs.X2 nTables)
  let l := m.regs.X3.toBitVec
  m'.regs.X0 = okWord r.isSome ∧ (∀ L, r = some L → LayoutWAt m'.dmem l L) ∧
    Changes m m' buildLayoutStack l layoutBytes ∧ Saved m m'

/-- `read_announced_sizes`' precondition: the `TState` at X0 represents `s`, X1 the bytecode's
length, the layout at X2. -/
def ReadAnnouncedSizesPre (bytecode : Array UInt64) (a : DecArea) (s : TState) (m : MachineData) :
    Prop :=
  let t := m.regs.X0.toBitVec; let l := m.regs.X2.toBitVec; let n := readAnnouncedSizesStack
  StackOk m n ∧ RcAt m n ∧ RodataAt m n ∧ TStateAt m.dmem t a s ∧ TStateOk m t a n ∧
    RodataApart t tstateBytes ∧ m.regs.X1.toNat = bytecode.size ∧ Readable m l layoutBytes ∧
    OffStack m l layoutBytes n ∧ RodataApart l layoutBytes ∧ Apart l layoutBytes rcAddr 192 ∧
    Apart l layoutBytes t tstateBytes ∧ Apart l layoutBytes a.words (8 * a.len)

/-- `read_announced_sizes`' postcondition. -/
def ReadAnnouncedSizesPost (bytecode : Array UInt64) (a : DecArea) (s : TState)
    (m m' : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let l := m.regs.X2.toBitVec
  let r := (readAnnouncedSizes bytecode).run s
  m'.regs.X0 = okWord r.isSome ∧
    (∀ L rate s', r = some ((L, rate), s') →
      m'.regs.X1.toNat = rate ∧ LayoutWAt m'.dmem l L ∧ TStateAt m'.dmem t a s') ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange l layoutBytes q ∨ InRange t tstateBytes q ∨
      InRange (stackBelow m readAnnouncedSizesStack) readAnnouncedSizesStack q) ∧ Saved m m'

/-! ## Phase 2 -/

/-- `ladder`'s precondition: its 160-byte result at X0. -/
def LadderPre (m : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec
  RodataAt m ladderStack ∧ Readable m o ladderBytes ∧ RodataApart o ladderBytes

/-- `ladder`'s postcondition. -/
def LadderPost (m m' : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec
  LadderAt m'.dmem o (Whir.ladder m.regs.X1.toNat m.regs.X2.toNat) ∧
    Changes m m' ladderStack o ladderBytes ∧ Saved m m'

/-- `commit_stack`'s precondition: the `TState` at X0 represents `s`, fewer than `maxRoots` roots
read. -/
def CommitStackPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let n := commitStackStack
  StackOk m n ∧ RcAt m n ∧ RodataAt m n ∧ TStateAt m.dmem t a s ∧ TStateOk m t a n ∧
    s.roots.size < maxRoots

/-- `commit_stack`'s postcondition. -/
def CommitStackPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec
  let r := (commitStack m.regs.X1.toNat m.regs.X2.toNat).run s
  m'.regs.X0 = okWord r.isSome ∧ NextAt m'.dmem t a r ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange t tstateBytes q ∨
      InRange (stackBelow m commitStackStack) commitStackStack q) ∧ Saved m m'

/-- `read_ood`'s precondition: the `TState` at X0 represents `s`, `stack_log ≤ 30`, the
`EqClaimW` at X2. -/
def ReadOodPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let n := readOodStack
  StackOk m n ∧ RcAt m n ∧ TStateAt m.dmem t a s ∧ TStateOk m t a n ∧
    m.regs.X1.toNat ≤ maxStackLog ∧ OutOk m t a m.regs.X2.toBitVec eqClaimBytes n

/-- `read_ood`'s postcondition. -/
def ReadOodPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let o := m.regs.X2.toBitVec
  let r := (readOod m.regs.X1.toNat).run s
  m'.regs.X0 = okWord r.isSome ∧
    (∀ c s', r = some (c, s') → OodAt m'.dmem o c ∧ TStateAt m'.dmem t a s') ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange o eqClaimBytes q ∨ InRange t tstateBytes q ∨
      InRange (stackBelow m readOodStack) readOodStack q) ∧ Saved m m'

/-! ## The claims -/

/-- `push_claim`'s precondition: the claims at X0 represent `cs`, the point (X2, X3) apart. -/
def PushClaimPre (cs : Array ColumnClaimW) (m : MachineData) : Prop :=
  let c := m.regs.X0.toBitVec
  StackOk m pushClaimStack ∧ ClaimsWAt m.dmem c cs ∧ Readable m c claimsBytes ∧
    OffStack m c claimsBytes pushClaimStack ∧ SliceOk m m.regs.X2 m.regs.X3 pushClaimStack ∧
    Apart c claimsBytes m.regs.X2.toBitVec (16 * m.regs.X3.toNat)

/-- `push_claim`'s postcondition. -/
def PushClaimPost (cs : Array ColumnClaimW) (m m' : MachineData) : Prop :=
  let c := m.regs.X0.toBitVec
  (if cs.size < claimCap ∧ m.regs.X3.toNat ≤ pointCap then
      m'.regs.X0 = 1 ∧ ClaimsWAt m'.dmem c
        (cs.push ⟨m.regs.X1.toNat, slice m m.regs.X2 m.regs.X3, ewArg m.regs.X4 m.regs.X5⟩)
    else m'.regs.X0 = 0) ∧
    Changes m m' pushClaimStack c claimsBytes ∧ Saved m m'

end

end

end NativeRustcVmArm
