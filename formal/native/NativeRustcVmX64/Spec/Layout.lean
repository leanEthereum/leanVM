module

public import NativeRustcVmX64.Spec.Ring
public import NativeRustcVmX64.Rodata
public import NativeRustcVm.Layout.Values
public import NativeRustcVmX64.Got
public import NativeRustcVmX64.Code.Vm.BuildLayout.Names
public import NativeRustcVmX64.Code.Vm.ColumnKappas.Names
public import NativeRustcVmX64.Code.Vm.CommitStack.Names
public import NativeRustcVmX64.Code.Vm.ConstraintsW.Names
public import NativeRustcVmX64.Code.Vm.Evaluate.Names
public import NativeRustcVmX64.Code.Vm.FormBufAddScaled.Names
public import NativeRustcVmX64.Code.Vm.FormBufAddTerm.Names
public import NativeRustcVmX64.Code.Vm.FormTerms.Names
public import NativeRustcVmX64.Code.Vm.InsertionSortOfStackOffsets.Names
public import NativeRustcVmX64.Code.Vm.Ladder.Names
public import NativeRustcVmX64.Code.Vm.LayoutWPlacement.Names
public import NativeRustcVmX64.Code.Vm.PlacementsOf.Names
public import NativeRustcVmX64.Code.Vm.PushClaim.Names
public import NativeRustcVmX64.Code.Vm.ReadAnnouncedSizes.Names
public import NativeRustcVmX64.Code.Vm.ReadOod.Names
public import NativeRustcVmX64.Code.Vm.StackOffsets.Names

/-!
# The contracts of `layout.rs`'s and `stack.rs`'s functions and `whir.rs`'s `ladder` on x86-64

The AArch64 contracts (`NativeRustcVmArm.Spec.Layout`) with the System V registers: arguments in
RDI, RSI, RDX, RCX, R8, R9; an `E` result in RAX, RDX; an `Option<usize>` as the tag RAX (the full
word, `okWord`), the value RDX; a `bool`/`Option<()>` in AL alone (`boolRet`, `OkAl`). Each
function uses the stack below RSP (`<fn>Stack` bytes: its pushes, its frame, its callees' return
addresses and stacks; `StackOk` also maps its return address at RSP), its inputs and outputs are
apart from that stack and the return address (`OffStack`), and it returns with the callee-saved
registers kept (and RSP 8 above, `Spec`), no byte changed outside its outputs and that stack.
Functions that read a GOT slot, directly or through a callee, also require `GotAt` for exactly
those symbols, apart from their existing stack and memory arguments. The slots remain ordinary
read-only memory; postconditions and model results are unchanged.
x86-64 pushes callee-saved registers where AArch64's leaves used none (`FormBuf::add_term`,
`insertion_sort`, `column_kappas`, `ladder`): those take `StackOk` and `OffStack` for their
memory arguments, which their callers' stack and arguments satisfy (the callers' own frames
contain the callee's stack). The results are the model's (`NativeVm.Model`):

- `form_terms(form)` (RDI): the slice (RAX, RDX) of `formAt form`'s terms, inside `TERMS`
  (`InTerms`).
- `evaluate(terms, row)` (RDI, RSI; RDX, RCX): `FormW.evaluate` in RAX, RDX.
- `FormBuf::add_term(self, t, c)` (RDI, RSI; `c` RDX, RCX): `FormW.addTerm`, AL = `0` (`None`)
  past `formCap`.
- `FormBuf::add_scaled(self, other, weight)` (RDI; RSI, RDX; RCX, R8): `FormW.addScaled`, AL = `0`
  past `formCap`.
- `constraints_w(opcode, row, out)` (RDI; RSI, RDX; RCX): `constraintsW` at `out`, its count in
  RAX.
- `LayoutW::placement(self, column)` (RDI, RSI; rustc dropped the bounds check: `column < 158`):
  `LayoutW.placement` in RAX, RDX.
- `stack_point`: its contract is `NativeRustcVmX64.Spec.Ring`'s (`StackPointPre`,
  `StackPointPost`).
- `insertion_sort(order, |i, j| …)` (RDI, RSI; the closure's `sizes` RDX, RCX): `insertionSort`.
- `stack_offsets(sizes, offsets)` (RDI, RSI; RDX, RCX; rustc dropped `n ≤ 158`): `stackOffsets`
  (RAX = 1, the bit length RDX), or RAX = 0 when `offsets` is shorter or the blocks do not fit a
  `u64` (`OffsetsFit`).
- `column_kappas(out, log_memory, log_bytecode, heights)` (RDI the `[usize; 158]`; RSI; RDX;
  RCX): `columnKappas`.
- `placements_of(kappas, placements)` (RDI, RSI; every `kappa ≤ 36`, as `build_layout` gives):
  `placementsOf`, always `Some` (RAX = 1, the value RDX).
- `build_layout(bytecode_len, log_memory, table_rows, layout)` (RDI to RCX): `buildLayout`, the
  layout at RCX, AL the `bool`.
- `read_announced_sizes(t, bytecode_len, layout)` (RDI, RSI, RDX): `readAnnouncedSizes`, the
  layout at RDX, the tag RAX, the rate exponent RDX.
- `ladder(out, mu, log_inv_rate)` (RDI the result; RSI, RDX): `Whir.ladder`.
- `commit_stack(t, log_n, log_inv_rate)` (RDI, RSI, RDX; fewer than `8` roots read):
  `commitStack`, AL the `Option<()>`.
- `read_ood(t, stack_log, out)` (RDI, RSI, RDX; `stack_log ≤ 30`): `readOod`, the claim at `out`,
  AL the `Option<()>`.
- `push_claim(claims, column, point, value)` (RDI; RSI; RDX, RCX; R8, R9): the claim appended,
  AL = `0` at `claimCap` claims or past `pointCap` coordinates.
-/

namespace NativeRustcVmX64

open NativeRustcX64 NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Layout
open LeanVM.Parameters
open NativeRustcVm (wordsOf EWsAt WordsAt)

@[expose] public section

/-! ## Stacks -/

/-- `form_terms` uses no stack. -/
def formTermsStack : Nat := 0
/-- The stack `evaluate` uses: 6 pushes, its 40-byte frame, `EW::mul`'s return address and
stack. -/
def evaluateStack : Nat := 96 + ewMulStack
/-- The stack `FormBuf::add_term` uses: 5 pushes. -/
def formBufAddTermStack : Nat := 40
/-- The stack `FormBuf::add_scaled` uses: 5 pushes, the return address and stack of `EW::mul`
(above `add_term`'s). -/
def formBufAddScaledStack : Nat := 48 + max ewMulStack formBufAddTermStack
/-- The stack `constraints_w` uses: 5 pushes, `EW::mul`'s return address and stack. -/
def constraintsWStack : Nat := 48 + ewMulStack
/-- `LayoutW::placement` uses no stack. -/
def layoutWPlacementStack : Nat := 0
/-- The stack `insertion_sort` uses: 2 pushes. -/
def insertionSortStack : Nat := 16
/-- The stack `stack_offsets` uses: 6 pushes, its 1272-byte frame (the `order` array), the return
address and stack of `insertion_sort` or `bit_length` (`memset` uses none). -/
def stackOffsetsStack : Nat := 1328 + max insertionSortStack bitLengthStack
/-- The stack `column_kappas` uses: 1 push. -/
def columnKappasStack : Nat := 8
/-- The stack `placements_of` uses: 6 pushes, its 5064-byte frame (its four 1264-byte arrays),
`stack_offsets`' return address and stack (`memset` uses none). -/
def placementsOfStack : Nat := 5120 + stackOffsetsStack
/-- The stack `build_layout` uses: 6 pushes, its 1304-byte frame (`kappas`), the return address
and stack of `placements_of` (above `bit_length`'s and `column_kappas`'). -/
def buildLayoutStack : Nat := 1360 + max placementsOfStack (max bitLengthStack columnKappasStack)
/-- The stack `read_announced_sizes` uses: 3 pushes, its 176-byte frame, the return address and
stack of `read_scalars` or `build_layout`. -/
def readAnnouncedSizesStack : Nat := 208 + max readScalarsStack buildLayoutStack
/-- The stack `ladder` uses: 6 pushes, its 24-byte frame. -/
def ladderStack : Nat := 72
/-- The stack `commit_stack` uses: 2 pushes, its 168-byte frame, `ladder`'s return address and
stack, or `read_commitment`'s, which it tail-calls from its own entry's RSP. -/
def commitStackStack : Nat := max (192 + ladderStack) readCommitmentStack
/-- The stack `read_ood` uses: 3 pushes, its 32-byte frame, the return address and stack of
`grind`, `sample_challenges` or `read_scalar`. -/
def readOodStack : Nat := 64 + max grindStack (max sampleChallengesStack readScalarStack)
/-- The stack `push_claim` uses: 5 pushes, `Buf::extend`'s return address and stack. -/
def pushClaimStack : Nat := 48 + bufEWExtendStack

/-! ## Values -/

/-- The `n` numbers (`usize`) from `a`. -/
def natsOf (m : MachineData) (a : BitVec 64) (n : Nat) : Array Nat :=
  ((wordsOf m.dmem a n).map UInt64.toNat).toArray

/-- Numbers as `usize` words. -/
def natWords (xs : Array Nat) : List UInt64 := xs.toList.map Nat.toUInt64

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
def FormTermsPre (m : MachineData) : Prop := StackOk m formTermsStack ∧ RodataAt m formTermsStack

/-- `form_terms`'s postcondition. -/
def FormTermsPost (m m' : MachineData) : Prop :=
  let f := formAt (reg m .rdi).toNat
  (reg m' .rdx).toNat = f.size ∧ TermsAt m'.dmem (reg m' .rax) f ∧
    InTerms (reg m' .rax) f.size ∧ SameOutside m.dmem m'.dmem (fun _ ↦ False) ∧ Saved m m'

/-- `evaluate`'s precondition: the terms (RDI, RSI) represent `f`. -/
def EvaluatePre (f : FormW) (m : MachineData) : Prop :=
  let t := reg m .rdi; let n := termBytes * (reg m .rsi).toNat
  StackOk m evaluateStack ∧ (reg m .rsi).toNat = f.size ∧ TermsAt m.dmem t f ∧ Readable m t n ∧
    OffStack m t n evaluateStack ∧ SliceOk m (reg m .rdx) (reg m .rcx) evaluateStack

/-- `evaluate`'s postcondition. -/
def EvaluatePost (f : FormW) (m m' : MachineData) : Prop :=
  ewRet m' = f.evaluate (slice m (reg m .rdx) (reg m .rcx)) ∧ Changes m m' evaluateStack 0 0 ∧
    Saved m m'

/-- `FormBuf::add_term`'s precondition: the `FormBuf` at RDI represents `f`, the term at RSI
`t`, both apart from the stack its pushes use. -/
def FormBufAddTermPre (f : FormW) (t : TermW) (m : MachineData) : Prop :=
  let b := reg m .rdi; let p := reg m .rsi; let s := formBufAddTermStack
  StackOk m s ∧ FormBufAt m.dmem b f ∧ TermWAt m.dmem p t ∧ Readable m b formBufBytes ∧
    OffStack m b formBufBytes s ∧ Readable m p termBytes ∧ OffStack m p termBytes s ∧
    Apart b formBufBytes p termBytes

/-- `FormBuf::add_term`'s postcondition. -/
def FormBufAddTermPost (f : FormW) (t : TermW) (m m' : MachineData) : Prop :=
  let b := reg m .rdi
  let g := f.addTerm t.cols (ewArg (reg m .rdx) (reg m .rcx))
  (if g.size ≤ formCap then boolRet m' = 1 ∧ FormBufAt m'.dmem b g else boolRet m' = 0) ∧
    Changes m m' formBufAddTermStack b formBufBytes ∧ Saved m m'

/-- `FormBuf::add_scaled`'s precondition: the `FormBuf` at RDI represents `f`, the terms (RSI,
RDX) `other`. -/
def FormBufAddScaledPre (f other : FormW) (m : MachineData) : Prop :=
  let b := reg m .rdi; let p := reg m .rsi
  let n := termBytes * (reg m .rdx).toNat; let s := formBufAddScaledStack
  StackOk m s ∧ (reg m .rdx).toNat = other.size ∧ FormBufAt m.dmem b f ∧
    TermsAt m.dmem p other ∧ Readable m b formBufBytes ∧ OffStack m b formBufBytes s ∧
    Readable m p n ∧ OffStack m p n s ∧ Apart b formBufBytes p n

/-- `FormBuf::add_scaled`'s postcondition. -/
def FormBufAddScaledPost (f other : FormW) (m m' : MachineData) : Prop :=
  let b := reg m .rdi
  let g := f.addScaled other (ewArg (reg m .rcx) (reg m .r8))
  (if g.size ≤ formCap then boolRet m' = 1 ∧ FormBufAt m'.dmem b g else boolRet m' = 0) ∧
    Changes m m' formBufAddScaledStack b formBufBytes ∧ Saved m m'

/-- `constraints_w`'s precondition: the row (RSI, RDX), the output's two elements at RCX. -/
def ConstraintsWPre (m : MachineData) : Prop :=
  StackOk m constraintsWStack ∧ SliceOk m (reg m .rsi) (reg m .rdx) constraintsWStack ∧
    Readable m (reg m .rcx) 32 ∧ OffStack m (reg m .rcx) 32 constraintsWStack

/-- `constraints_w`'s postcondition. -/
def ConstraintsWPost (m m' : MachineData) : Prop :=
  let r := constraintsW (reg m .rdi).toNat (slice m (reg m .rsi) (reg m .rdx))
  (reg m' .rax).toNat = r.size ∧ EWsAt m'.dmem (reg m .rcx) r.toList ∧
    Changes m m' constraintsWStack (reg m .rcx) 32 ∧ Saved m m'

/-! ## Placements -/

/-- `LayoutW::placement`'s precondition: the layout at RDI represents `L`, readable, a column
below `158`. -/
def LayoutWPlacementPre (L : LayoutW) (m : MachineData) : Prop :=
  StackOk m layoutWPlacementStack ∧ (reg m .rsi).toNat < columnCountW ∧
    LayoutWAt m.dmem (reg m .rdi) L ∧ Readable m (reg m .rdi) layoutBytes

/-- `LayoutW::placement`'s postcondition. -/
def LayoutWPlacementPost (L : LayoutW) (m m' : MachineData) : Prop :=
  let p := L.placement (reg m .rsi).toNat
  reg m' .rax = p.variableCount.toUInt64.toBitVec ∧ reg m' .rdx = p.index.toUInt64.toBitVec ∧
    SameOutside m.dmem m'.dmem (fun _ ↦ False) ∧ Saved m m'

/-- `insertion_sort`'s precondition: the order (RDI, RSI), the sizes (RDX, RCX) apart from it,
both apart from the stack its pushes use. -/
def InsertionSortPre (m : MachineData) : Prop :=
  let o := reg m .rdi; let s := reg m .rdx
  let no := 8 * (reg m .rsi).toNat; let ns := 8 * (reg m .rcx).toNat
  StackOk m insertionSortStack ∧ Readable m o no ∧ OffStack m o no insertionSortStack ∧
    Readable m s ns ∧ OffStack m s ns insertionSortStack ∧ Apart o no s ns

/-- `insertion_sort`'s postcondition. -/
def InsertionSortPost (m m' : MachineData) : Prop :=
  let sizes := natsOf m (reg m .rdx) (reg m .rcx).toNat
  let o := reg m .rdi
  WordsAt m'.dmem o (natWords (insertionSort (sortLt (sizes.getD · 0))
      (natsOf m (reg m .rdi) (reg m .rsi).toNat))) ∧
    Changes m m' insertionSortStack o (8 * (reg m .rsi).toNat) ∧ Saved m m'

/-- `stack_offsets`' precondition: at most `158` sizes (RDI, RSI), the offsets (RDX, RCX)
apart. -/
def StackOffsetsPre (m : MachineData) : Prop :=
  let a := reg m .rdi; let n := 8 * (reg m .rsi).toNat
  let o := reg m .rdx; let k := 8 * (reg m .rcx).toNat
  StackOk m stackOffsetsStack ∧ (reg m .rsi).toNat ≤ columnCountW ∧ Readable m a n ∧
    OffStack m a n stackOffsetsStack ∧ Readable m o k ∧ OffStack m o k stackOffsetsStack ∧
    Apart a n o k ∧ GotAt m stackOffsetsStack [(a, n), (o, k)] ["memset"]

/-- `stack_offsets`' postcondition. -/
def StackOffsetsPost (m m' : MachineData) : Prop :=
  let sizes := natsOf m (reg m .rdi) (reg m .rsi).toNat
  let o := reg m .rdx
  (if (reg m .rsi).toNat ≤ (reg m .rcx).toNat ∧ OffsetsFit sizes then
      reg m' .rax = 1#64 ∧ (reg m' .rdx).toNat = (stackOffsets sizes).2 ∧
        WordsAt m'.dmem o (natWords (stackOffsets sizes).1)
    else reg m' .rax = 0#64) ∧
    Changes m m' stackOffsetsStack o (8 * (reg m .rcx).toNat) ∧ Saved m m'

/-- `column_kappas`' precondition: the output's `158` words at RDI, the six heights at RCX, the
keccak table's `+ qkeccakSlotBits` not wrapping. -/
def ColumnKappasPre (m : MachineData) : Prop :=
  let o := reg m .rdi; let h := reg m .rcx; let s := columnKappasStack
  StackOk m s ∧ Readable m o kappasBytes ∧ OffStack m o kappasBytes s ∧
    Readable m h (8 * nTables) ∧ OffStack m h (8 * nTables) s ∧
    Apart o kappasBytes h (8 * nTables) ∧
    (natsOf m (reg m .rcx) nTables).getD LeanVM.Protocol.Verifier.opKeccak 0 +
      LeanVM.Protocol.Verifier.qkeccakSlotBits < 2 ^ 64

/-- `column_kappas`' postcondition. -/
def ColumnKappasPost (m m' : MachineData) : Prop :=
  let o := reg m .rdi
  WordsAt m'.dmem o (natWords (columnKappas (reg m .rsi).toNat (reg m .rdx).toNat
      (natsOf m (reg m .rcx) nTables))) ∧
    Changes m m' columnKappasStack o kappasBytes ∧ Saved m m'

/-- `placements_of`'s precondition: the `158` log-sizes at RDI, each at most `36`, the
placements at RSI. -/
def PlacementsOfPre (m : MachineData) : Prop :=
  let k := reg m .rdi; let p := reg m .rsi; let s := placementsOfStack
  StackOk m s ∧ RodataAt m s ∧ Readable m k kappasBytes ∧ OffStack m k kappasBytes s ∧
    Readable m p placementsBytes ∧ OffStack m p placementsBytes s ∧ RodataApart p placementsBytes ∧
    Apart k kappasBytes p placementsBytes ∧
    (∀ κ ∈ natsOf m (reg m .rdi) columnCountW, κ ≤ 36) ∧
    GotAt m s [(k, kappasBytes), (p, placementsBytes)] ["memset"]

/-- `placements_of`'s postcondition. -/
def PlacementsOfPost (m m' : MachineData) : Prop :=
  let r := placementsOf (natsOf m (reg m .rdi) columnCountW)
  let p := reg m .rsi
  reg m' .rax = 1#64 ∧ (reg m' .rdx).toNat = r.2 ∧ r.1.size = columnCountW ∧
    (∀ c (h : c < r.1.size), PlacementWAt m'.dmem (off p (placementBytes * c)) r.1[c]) ∧
    Changes m m' placementsOfStack p placementsBytes ∧ Saved m m'

/-! ## Phase 1 -/

/-- `build_layout`'s precondition: RDI the bytecode's length, the six row counts at RDX, the
layout at RCX. -/
def BuildLayoutPre (bytecode : Array UInt64) (m : MachineData) : Prop :=
  let r := reg m .rdx; let l := reg m .rcx; let s := buildLayoutStack
  StackOk m s ∧ RodataAt m s ∧ (reg m .rdi).toNat = bytecode.size ∧ Readable m r (8 * nTables) ∧
    OffStack m r (8 * nTables) s ∧ Readable m l layoutBytes ∧ OffStack m l layoutBytes s ∧
    RodataApart l layoutBytes ∧ Apart r (8 * nTables) l layoutBytes ∧
    GotAt m s [(r, 8 * nTables), (l, layoutBytes)] ["memset"]

/-- `build_layout`'s postcondition: AL the `bool`. -/
def BuildLayoutPost (bytecode : Array UInt64) (m m' : MachineData) : Prop :=
  let r := buildLayout bytecode (reg m .rsi).toNat (natsOf m (reg m .rdx) nTables)
  let l := reg m .rcx
  OkAl m' r.isSome ∧ (∀ L, r = some L → LayoutWAt m'.dmem l L) ∧
    Changes m m' buildLayoutStack l layoutBytes ∧ Saved m m'

/-- `read_announced_sizes`' precondition: the `TState` at RDI represents `s`, RSI the bytecode's
length, the layout at RDX. -/
def ReadAnnouncedSizesPre (bytecode : Array UInt64) (a : DecArea) (s : TState) (m : MachineData) :
    Prop :=
  let t := reg m .rdi; let l := reg m .rdx; let n := readAnnouncedSizesStack
  StackOk m n ∧ RcAt m n ∧ RodataAt m n ∧ TStateAt m.dmem t a s ∧ TStateOk m t a n ∧
    RodataApart t tstateBytes ∧ (reg m .rsi).toNat = bytecode.size ∧ Readable m l layoutBytes ∧
    OffStack m l layoutBytes n ∧ RodataApart l layoutBytes ∧ Apart l layoutBytes rcAddr 192 ∧
    Apart l layoutBytes t tstateBytes ∧ Apart l layoutBytes a.words (8 * a.len) ∧
    GotAt m n [(t, tstateBytes), (a.words, 8 * a.len), (l, layoutBytes), (rcAddr, 192)]
      ["memcpy", "memset"]

/-- `read_announced_sizes`' postcondition: the tag RAX (the full word), the rate RDX. -/
def ReadAnnouncedSizesPost (bytecode : Array UInt64) (a : DecArea) (s : TState)
    (m m' : MachineData) : Prop :=
  let t := reg m .rdi; let l := reg m .rdx
  let r := (readAnnouncedSizes bytecode).run s
  reg m' .rax = (okWord r.isSome).toBitVec ∧
    (∀ L rate s', r = some ((L, rate), s') →
      (reg m' .rdx).toNat = rate ∧ LayoutWAt m'.dmem l L ∧ TStateAt m'.dmem t a s') ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange l layoutBytes q ∨ InRange t tstateBytes q ∨
      InRange (stackBelow m readAnnouncedSizesStack) readAnnouncedSizesStack q) ∧ Saved m m'

/-! ## Phase 2 -/

/-- `ladder`'s precondition: its 160-byte result at RDI, apart from the stack its pushes and frame
use. -/
def LadderPre (m : MachineData) : Prop :=
  let o := reg m .rdi
  StackOk m ladderStack ∧ RodataAt m ladderStack ∧ Readable m o ladderBytes ∧
    OffStack m o ladderBytes ladderStack ∧ RodataApart o ladderBytes

/-- `ladder`'s postcondition. -/
def LadderPost (m m' : MachineData) : Prop :=
  let o := reg m .rdi
  LadderAt m'.dmem o (Whir.ladder (reg m .rsi).toNat (reg m .rdx).toNat) ∧
    Changes m m' ladderStack o ladderBytes ∧ Saved m m'

/-- `commit_stack`'s precondition: the `TState` at RDI represents `s`, fewer than `maxRoots` roots
read. -/
def CommitStackPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let t := reg m .rdi; let n := commitStackStack
  StackOk m n ∧ RcAt m n ∧ RodataAt m n ∧ TStateAt m.dmem t a s ∧ TStateOk m t a n ∧
    s.roots.size < maxRoots ∧
    GotAt m n [(t, tstateBytes), (a.words, 8 * a.len), (rcAddr, 192)] ["memcpy"]

/-- `commit_stack`'s postcondition: AL the `Option<()>`. -/
def CommitStackPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let t := reg m .rdi
  let r := (commitStack (reg m .rsi).toNat (reg m .rdx).toNat).run s
  OkAl m' r.isSome ∧ NextAt m'.dmem t a r ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange t tstateBytes q ∨
      InRange (stackBelow m commitStackStack) commitStackStack q) ∧ Saved m m'

/-- `read_ood`'s precondition: the `TState` at RDI represents `s`, `stack_log ≤ 30`, the
`EqClaimW` at RDX. -/
def ReadOodPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let t := reg m .rdi; let n := readOodStack
  StackOk m n ∧ RcAt m n ∧ TStateAt m.dmem t a s ∧ TStateOk m t a n ∧
    (reg m .rsi).toNat ≤ maxStackLog ∧ OutOk m t a (reg m .rdx) eqClaimBytes n ∧
    GotAt m n [(t, tstateBytes), (a.words, 8 * a.len), (reg m .rdx, eqClaimBytes), (rcAddr, 192)]
      ["memcpy"]

/-- `read_ood`'s postcondition: AL the `Option<()>`. -/
def ReadOodPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let t := reg m .rdi; let o := reg m .rdx
  let r := (readOod (reg m .rsi).toNat).run s
  OkAl m' r.isSome ∧
    (∀ c s', r = some (c, s') → OodAt m'.dmem o c ∧ TStateAt m'.dmem t a s') ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange o eqClaimBytes q ∨ InRange t tstateBytes q ∨
      InRange (stackBelow m readOodStack) readOodStack q) ∧ Saved m m'

/-! ## The claims -/

/-- `push_claim`'s precondition: the claims at RDI represent `cs`, the point (RDX, RCX) apart. -/
def PushClaimPre (cs : Array ColumnClaimW) (m : MachineData) : Prop :=
  let c := reg m .rdi
  StackOk m pushClaimStack ∧ ClaimsWAt m.dmem c cs ∧ Readable m c claimsBytes ∧
    OffStack m c claimsBytes pushClaimStack ∧ SliceOk m (reg m .rdx) (reg m .rcx) pushClaimStack ∧
    Apart c claimsBytes (reg m .rdx) (16 * (reg m .rcx).toNat)

/-- `push_claim`'s postcondition: AL the `Option<()>`. -/
def PushClaimPost (cs : Array ColumnClaimW) (m m' : MachineData) : Prop :=
  let c := reg m .rdi
  (if cs.size < claimCap ∧ (reg m .rcx).toNat ≤ pointCap then
      boolRet m' = 1 ∧ ClaimsWAt m'.dmem c
        (cs.push ⟨(reg m .rsi).toNat, slice m (reg m .rdx) (reg m .rcx),
          ewArg (reg m .r8) (reg m .r9)⟩)
    else boolRet m' = 0) ∧
    Changes m m' pushClaimStack c claimsBytes ∧ Saved m m'

end

end

end NativeRustcVmX64
