module

public import NativeRustcVmX64.Spec.Sumcheck
public import NativeRustcVmX64.Spec.Layout
public import NativeRustcX64.Spec.Got
public import NativeRustcVm.Bus.Rep
public import NativeRustcVm.Bus.Blocks
public import NativeRustcVm.Bus.FitsModel
public import NativeRustcVmX64.Code.Vm.AccumulateSide.Names
public import NativeRustcVmX64.Code.Vm.BlockForm.Names
public import NativeRustcVmX64.Code.Vm.BusLayout.Names
public import NativeRustcVmX64.Code.Vm.BytecodeShare.Names
public import NativeRustcVmX64.Code.Vm.ComputedBytecodeValue.Names
public import NativeRustcVmX64.Code.Vm.Fingerprints.Names
public import NativeRustcVmX64.Code.Vm.GkrLayers.Names
public import NativeRustcVmX64.Code.Vm.GkrStep.Names
public import NativeRustcVmX64.Code.Vm.VerifyBusBalance.Names
public import NativeRustcVmX64.Code.Vm.VerifyBusBalanceClosure0.Names
public import NativeRustcVmX64.Code.Vm.VerifyGkrGrandProducts.Names

/-!
# The contracts of `bus.rs`'s and `gkr.rs`'s functions on x86-64

The AArch64 contracts (`NativeRustcVmArm.Spec.Bus`) with the System V registers: arguments in
RDI, RSI, RDX, RCX, R8, R9, then on the stack above the return address (`stackArg`, mapped by
`ArgsOk`); an `Option<()>` or `bool` result in AL alone (`OkAl`, `boolRet`); an `Option<…>` result
at the `sret` pointer RDI. Each function uses the stack below RSP (`<fn>Stack` bytes: its pushes,
its frame, the stack arguments it pushes, its callees' return addresses and stacks; `StackOk` also
maps its return address at RSP) and returns with the callee-saved registers kept (and RSP 8
above, `Spec`), no byte changed outside its outputs and that stack. Results are the model's
(`NativeVm.Model`, `Bus.lean`, `Gkr.lean`); a `VM` step's `none` is the Rust's `None` (AL = `0`,
or a tag word `0`), and on it a contract says nothing more than the frame.

- `gkr_step(t, step, last, s)` (RDI, RSI, RDX, RCX; rustc specialised the body to
  `step ∈ {1, 2}`): the `GkrStateW` at `s` (`GkrStateWAt`) becomes `gkrStep step last`'s; the
  point stays within its 63 slots (`|point| + step ≤ 63`, as `verify_bus_balance`'s `depth < 64`
  makes it). AL the `Option<()>`.
- `gkr_layers(t, depth, s)` (RDI, RSI, RDX): `gkrLayers depth` (`depth + |point| ≤ 63`), AL the
  `Option<()>`.
- `verify_gkr_grand_products(out, t, depth, s)` (RDI, RSI, RDX, RCX; `depth ≤ 63`): the count
  root as the `Option<EW>` at `out`, the point and the trees' values at `s`.
- `fingerprints(out, weights, memory, memory_low, bytecode_low, share, pc, memory_count,
  bytecode_count)` (RDI, RSI, RDX, RCX and R8, R9 and stack word `0`, then stack words `1` to `7`;
  rustc dropped `weights`'s length, which is `16`, and `pc`'s limb `1`, which is `0`): the three
  fingerprints at `out`.
- `verify_bus_balance::{closure#0}(out, env, pc, memory_count, bytecode_count)` (RDI, RSI, RDX,
  RCX and R8, R9 and stack word `0`): the `fingerprints` of the slices its environment names.
- `computed_bytecode_value(words, point, value)` (RDI, RSI; RDX, RCX; R8, R9): AL = `1` iff the
  bytecode's multilinear extension at the point is the value.
- `bytecode_share(out, t, weights, bytecode_low, point)` (RDI, RSI, RDX, RCX and R8, R9; `weights`
  its `16` elements, `|bytecode_low| ≤ 63`): `bytecodeShare` as the `Option<(EW, usize, EW)>` at
  `out`, the bytecode point at `point`.
- `bus_layout(out, framework_log_rows, blocks, layout)` (RDI, RSI and RDX, RCX and R8, R9; at most
  3 framework sizes, 1 to 51 blocks, every size at most 30): `busLayout` of the sizes and the
  blocks (`blockW`, at the layout's heights) as the `Option<BusLayoutW>` at `out`, never `None`.
- `block_form(tuple, side_weights, side_beta, form)` (RDI, RSI and RDX, RCX and R8, R9; rustc
  passes the block's tuple alone): `blockForm` of the tuple's forms (`tupleOf`) at `form` if it
  fits a `FormBuf`, AL = `1`; else AL = `0`.
- `accumulate_side(out, forms, side, blocks, layout, side_layout, framework_fingerprints,
  side_weights, side_beta, point, tree_value)` (RDI, RSI, RDX, RCX and R8, R9, then 11 stack
  words: `side_layout`, the fingerprints' pointer and count, the weights' pointer and length,
  `side_beta`, the point's pointer and length, the tree's value): `accumulateSide` of the side's
  blocks (`blockW` at the layout's heights and rows), the forms at `forms` (`FormsAt`), the total
  as the `Option<EW>` at `out`; the forms fit their `FormBuf`s (`SideFits`).
- `verify_bus_balance(t, layout, bytecode, bus, claims)` (RDI, RSI, RDX and RCX, R8, R9):
  `verifyBusBalance` of the layout (`LayoutWAt`) and the bytecode, the result at `bus` (`BusWAt`),
  its claims at `claims` (`ClaimsWAt`), AL the `Option<()>`. The blocks are the data's
  (`busBlocks_eq`).
-/

namespace NativeRustcVmX64

open NativeRustcX64 NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVm (ewsOf wordsOf wordOf ewOf EWsAt EWAt WordAt BufEWAt)

@[expose] public section

/-! ## Stacks -/

/-- The largest of a list. -/
def maxOf (ns : List Nat) : Nat := ns.foldr max 0

/-- The stack `gkr_step` uses: 6 pushes, its 1320-byte frame, then a callee's return address and
stack, the sumcheck's three stack arguments and alignment word (32 bytes) above its. The raw
`bts` sets the sumcheck's term-count bit without touching the stack. -/
def gkrStepStack : Nat :=
  48 + 1320 + max (8 + maxOf [bitLengthStack, grindStack, squeezeStack, polyEvalStack,
    readScalarsStack, prodEStack, sampleChallengesStack, mleStack]) (40 + sumcheckGkrStack)
/-- The stack `gkr_layers` uses: 5 pushes, `gkr_step`'s return address and stack (its last call
a tail call, within). -/
def gkrLayersStack : Nat := 48 + gkrStepStack
/-- The stack `verify_gkr_grand_products` uses: 6 pushes, its 24-byte frame, a callee's return
address and stack. -/
def verifyGkrStack : Nat := 80 + max readScalarStack gkrLayersStack
/-- The stack `fingerprints` uses: 6 pushes, its 200-byte frame, a callee's return address and
stack. -/
def fingerprintsStack : Nat := 256 + maxOf [kpowStack, dotStack, indexMleFromStack]
/-- The stack `verify_bus_balance::{closure#0}` uses: 3 pushes, `fingerprints`'s 8 stack
arguments, its return address and stack. -/
def fpClosureStack : Nat := 96 + fingerprintsStack
/-- The stack `computed_bytecode_value` uses: 3 pushes, `multilinear_eval_by`'s return address
and stack. -/
def computedBytecodeValueStack : Nat := 32 + mleStack
/-- The stack `bytecode_share` uses: 6 pushes, its 376-byte frame (the sumcheck's stack argument
within), a callee's return address and stack. -/
def bytecodeShareStack : Nat :=
  432 + maxOf [readScalarStack, sumcheckPlainStack, eqKernelStack, dotStack, ewMulStack]

section
variable [Labels]

/-! ## The GKR walk -/

/-- The `GkrStateW` at `p` beside the `TState` at `t` for a function using `N` bytes of stack. -/
def GkrOk (m : MachineData) (t : BitVec 64) (a : DecArea) (p : BitVec 64) (N : Nat) : Prop :=
  OutOk m t a p gkrStateBytes N

/-- `gkr_step`'s precondition: `step ∈ {1, 2}` (RSI), `last` (RDX) `0` or `1`, the point's
`step` more coordinates within its capacity. -/
def GkrStepPre (a : DecArea) (s : TState) (g : GkrStateW) (m : MachineData) : Prop :=
  let t := reg m .rdi; let p := reg m .rcx
  StackOk m gkrStepStack ∧ RcAt m gkrStepStack ∧ TStateAt m.dmem t a s ∧
    TStateOk m t a gkrStepStack ∧ ((reg m .rsi).toNat = 1 ∨ (reg m .rsi).toNat = 2) ∧
    (reg m .rdx).toNat ≤ 1 ∧ g.point.size + (reg m .rsi).toNat ≤ busPointCap ∧
    GkrOk m t a p gkrStepStack ∧ GkrStateWAt m.dmem p g ∧
    GotAt m gkrStepStack [(t, tstateBytes), (a.words, 8 * a.len), (p, gkrStateBytes),
      (rcAddr, 192)] ["memcpy"]

/-- `gkr_step`'s postcondition: `gkrStep step last g`. -/
def GkrStepPost (a : DecArea) (s : TState) (g : GkrStateW) (m m' : MachineData) : Prop :=
  let t := reg m .rdi; let p := reg m .rcx
  let r := (gkrStep (reg m .rsi).toNat ((reg m .rdx).toNat = 1) g).run s
  OkAl m' r.isSome ∧
    (∀ g' s', r = some (g', s') → TStateAt m'.dmem t a s' ∧ GkrStateWAt m'.dmem p g') ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange t tstateBytes q ∨ InRange p gkrStateBytes q ∨
      InRange (stackBelow m gkrStepStack) gkrStepStack q) ∧ Saved m m'

/-- `gkr_layers`'s precondition: `depth` (RSI) more coordinates within the point's capacity. -/
def GkrLayersPre (a : DecArea) (s : TState) (g : GkrStateW) (m : MachineData) : Prop :=
  let t := reg m .rdi; let p := reg m .rdx
  StackOk m gkrLayersStack ∧ RcAt m gkrLayersStack ∧ TStateAt m.dmem t a s ∧
    TStateOk m t a gkrLayersStack ∧ g.point.size + (reg m .rsi).toNat ≤ busPointCap ∧
    GkrOk m t a p gkrLayersStack ∧ GkrStateWAt m.dmem p g ∧
    GotAt m gkrLayersStack [(t, tstateBytes), (a.words, 8 * a.len), (p, gkrStateBytes),
      (rcAddr, 192)] ["memcpy"]

/-- `gkr_layers`'s postcondition: `gkrLayers depth g`. -/
def GkrLayersPost (a : DecArea) (s : TState) (g : GkrStateW) (m m' : MachineData) : Prop :=
  let t := reg m .rdi; let p := reg m .rdx
  let r := (gkrLayers (reg m .rsi).toNat g).run s
  OkAl m' r.isSome ∧
    (∀ g' s', r = some (g', s') → TStateAt m'.dmem t a s' ∧ GkrStateWAt m'.dmem p g') ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange t tstateBytes q ∨ InRange p gkrStateBytes q ∨
      InRange (stackBelow m gkrLayersStack) gkrLayersStack q) ∧ Saved m m'

/-- `verify_gkr_grand_products`'s precondition: `depth ≤ 63` (RDX); the `Option<EW>` at `out`
(RDI) and the `GkrStateW` at `s` (RCX) outputs, apart. -/
def VerifyGkrPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let o := reg m .rdi; let t := reg m .rsi; let p := reg m .rcx
  StackOk m verifyGkrStack ∧ RcAt m verifyGkrStack ∧ TStateAt m.dmem t a s ∧
    TStateOk m t a verifyGkrStack ∧ (reg m .rdx).toNat ≤ busPointCap ∧
    OutOk m t a o 24 verifyGkrStack ∧ GkrOk m t a p verifyGkrStack ∧ Apart o 24 p gkrStateBytes ∧
    GotAt m verifyGkrStack [(t, tstateBytes), (a.words, 8 * a.len), (o, 24),
      (p, gkrStateBytes), (rcAddr, 192)] ["memcpy"]

/-- `verify_gkr_grand_products`'s postcondition: `verifyGkrGrandProducts depth`, the count root
at `out`, the point and the values at `s`. -/
def VerifyGkrPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let o := reg m .rdi; let t := reg m .rsi; let p := reg m .rcx
  let r := (verifyGkrGrandProducts (reg m .rdx).toNat).run s
  OptEWAt m'.dmem o (r.map (·.1.1)) ∧
    (∀ c pt vs s', r = some ((c, pt, vs), s') →
      TStateAt m'.dmem t a s' ∧ GkrStateWAt m'.dmem p ⟨vs, pt⟩) ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange o 24 q ∨ InRange t tstateBytes q ∨
      InRange p gkrStateBytes q ∨ InRange (stackBelow m verifyGkrStack) verifyGkrStack q) ∧
    Saved m m'

end

/-! ## Fingerprints -/

/-- `n` readable elements of `E` at `p`, apart from `s` bytes of stack and the return address. -/
def EWsOk (m : MachineData) (p : BitVec 64) (n s : Nat) : Prop :=
  Readable m p (16 * n) ∧ OffStack m p (16 * n) s

/-- `fingerprints`'s arguments: `weights` (5 of them read), `memory`, `memory_low`,
`bytecode_low`, the share, `pc` (limb `0`), the counts. -/
def fpArgs (m : MachineData) : Array EW × Array EW × Array EW × Array EW × EW × EW × EW × EW :=
  ((ewsOf m.dmem (reg m .rsi) 5).toArray, (ewsOf m.dmem (reg m .rdx) 2).toArray,
    slice m (reg m .rcx) (reg m .r8), slice m (reg m .r9) (stackArg m 0),
    ewArg (stackArg m 1) (stackArg m 2), EW.ofK (.ofBitVec (stackArg m 3)),
    ewArg (stackArg m 4) (stackArg m 5), ewArg (stackArg m 6) (stackArg m 7))

/-- `fingerprints`'s precondition: the slices readable, apart from the stack; the eight stack
arguments' words data memory; the 48 bytes at `out` (RDI) data memory, apart from the stack. -/
def FingerprintsPre (m : MachineData) : Prop :=
  let o := reg m .rdi
  StackOk m fingerprintsStack ∧ ArgsOk m 8 ∧ EWsOk m (reg m .rsi) 5 fingerprintsStack ∧
    EWsOk m (reg m .rdx) 2 fingerprintsStack ∧
    SliceOk m (reg m .rcx) (reg m .r8) fingerprintsStack ∧
    SliceOk m (reg m .r9) (stackArg m 0) fingerprintsStack ∧
    Readable m o 48 ∧ OffStack m o 48 fingerprintsStack

/-- `fingerprints`'s postcondition: the three fingerprints at `out`. -/
def FingerprintsPost (m m' : MachineData) : Prop :=
  let (w, mem, ml, bl, share, pc, mc, bc) := fpArgs m
  EWsAt m'.dmem (reg m .rdi) (fingerprints w mem ml bl share pc mc bc).toList ∧
    Changes m m' fingerprintsStack (reg m .rdi) 48 ∧ Saved m m'

/-- The closure's environment at `e` (RSI, 56 bytes): `weights`'s, `memory`'s addresses,
`memory_low`'s and `bytecode_low`'s addresses and lengths, the share's address. -/
def envWord (m : MachineData) (i : Nat) : BitVec 64 :=
  (wordOf m.dmem (reg m .rsi + BitVec.ofNat 64 (8 * i))).toBitVec

/-- The closure's arguments, as `fpArgs`. -/
def fpClosureArgs (m : MachineData) :
    Array EW × Array EW × Array EW × Array EW × EW × EW × EW × EW :=
  ((ewsOf m.dmem (envWord m 0) 5).toArray, (ewsOf m.dmem (envWord m 1) 2).toArray,
    slice m (envWord m 2) (envWord m 3), slice m (envWord m 4) (envWord m 5),
    ewOf m.dmem (envWord m 6), EW.ofK (.ofBitVec (reg m .rdx)), ewArg (reg m .rcx) (reg m .r8),
    ewArg (reg m .r9) (stackArg m 0))

/-- The closure's precondition: its environment (RSI, 56 bytes) and what it names readable, apart
from the stack; the stack argument's word data memory; the 48 bytes at `out` (RDI). -/
def FpClosurePre (m : MachineData) : Prop :=
  let o := reg m .rdi; let e := reg m .rsi
  StackOk m fpClosureStack ∧ ArgsOk m 1 ∧ Readable m e 56 ∧ OffStack m e 56 fpClosureStack ∧
    EWsOk m (envWord m 0) 5 fpClosureStack ∧ EWsOk m (envWord m 1) 2 fpClosureStack ∧
    SliceOk m (envWord m 2) (envWord m 3) fpClosureStack ∧
    SliceOk m (envWord m 4) (envWord m 5) fpClosureStack ∧
    EWsOk m (envWord m 6) 1 fpClosureStack ∧
    Readable m o 48 ∧ OffStack m o 48 fpClosureStack

/-- The closure's postcondition: the three fingerprints at `out`. -/
def FpClosurePost (m m' : MachineData) : Prop :=
  let (w, mem, ml, bl, share, pc, mc, bc) := fpClosureArgs m
  EWsAt m'.dmem (reg m .rdi) (fingerprints w mem ml bl share pc mc bc).toList ∧
    Changes m m' fpClosureStack (reg m .rdi) 48 ∧ Saved m m'

/-! ## The bytecode's value -/

/-- `computed_bytecode_value`'s precondition: the `n` words (RDI, RSI; apart from the stack when
`0 < n`, the empty slice's pointer dangling), the point (RDX, RCX). -/
def ComputedBytecodeValuePre (m : MachineData) : Prop :=
  StackOk m computedBytecodeValueStack ∧ Readable m (reg m .rdi) (8 * (reg m .rsi).toNat) ∧
    (0 < (reg m .rsi).toNat →
      OffStack m (reg m .rdi) (8 * (reg m .rsi).toNat) computedBytecodeValueStack) ∧
    SliceOk m (reg m .rdx) (reg m .rcx) computedBytecodeValueStack

/-- `computed_bytecode_value`'s postcondition: `computedBytecodeValue words point value`
succeeds iff AL = `1`. -/
def ComputedBytecodeValuePost (m m' : MachineData) : Prop :=
  OkAl m' (multilinearEval (wordSliceE m (reg m .rdi) (reg m .rsi))
      (slice m (reg m .rdx) (reg m .rcx)) == ewArg (reg m .r8) (reg m .r9)) ∧
    Changes m m' computedBytecodeValueStack 0 0 ∧ Saved m m'

/-! ## The bytecode share -/

/-- The bytecode point's slots (`[EW; BUS_POINT_CAP + BUS_BITS]`). -/
def sharePointSlots : Nat := busPointCap + 4

/-- `Option<(EW, usize, EW)>` at `o` (48 bytes): tag word `0`; or tag word `1`, the share, the
bytecode point's length, the value. -/
def OptShareAt (d : Mem 64) (o : BitVec 64) : Option (EW × Array EW × EW) → Prop
  | none => WordAt d o 0
  | some (share, p, value) => WordAt d o 1 ∧ EWAt d (off o 8) share ∧
      WordAt d (off o 24) p.size.toUInt64 ∧ EWAt d (off o 32) value

section
variable [Labels]

/-- `bytecode_share`'s precondition: `weights` (RDX) its 16 elements, `bytecode_low` (RCX, R8) at
most 63, the output (RDI, 48 bytes) and the point's 67 slots (R9) outputs, apart. -/
def BytecodeSharePre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let o := reg m .rdi; let t := reg m .rsi; let p := reg m .r9
  let N := bytecodeShareStack
  StackOk m N ∧ RcAt m N ∧ TStateAt m.dmem t a s ∧ TStateOk m t a N ∧
    EWsOk m (reg m .rdx) 16 N ∧ (reg m .r8).toNat ≤ busPointCap ∧
    SliceOk m (reg m .rcx) (reg m .r8) N ∧ OutOk m t a o 48 N ∧
    OutOk m t a p (16 * sharePointSlots) N ∧ Apart o 48 p (16 * sharePointSlots) ∧
    Apart p (16 * sharePointSlots) (reg m .rcx) (16 * (reg m .r8).toNat) ∧
    Apart (reg m .rdx) (16 * 16) t tstateBytes ∧
    Apart (reg m .rcx) (16 * (reg m .r8).toNat) t tstateBytes ∧
    GotAt m N [(t, tstateBytes), (a.words, 8 * a.len), (o, 48), (p, 16 * sharePointSlots),
      (reg m .rdx, 16 * 16), (reg m .rcx, 16 * (reg m .r8).toNat), (rcAddr, 192)] ["memcpy"]

/-- `bytecode_share`'s postcondition: `bytecodeShare weights bytecode_low`, the share, the
point's length and the value at `out`, the bytecode point at `point`. -/
def BytecodeSharePost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let o := reg m .rdi; let t := reg m .rsi; let p := reg m .r9
  let N := bytecodeShareStack
  let r := (bytecodeShare (ewsOf m.dmem (reg m .rdx) 16).toArray
    (slice m (reg m .rcx) (reg m .r8))).run s
  OptShareAt m'.dmem o (r.map (·.1)) ∧
    (∀ x s', r = some (x, s') → EWsAt m'.dmem p x.2.1.toList ∧ TStateAt m'.dmem t a s') ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange o 48 q ∨ InRange p (16 * sharePointSlots) q ∨
      InRange t tstateBytes q ∨ InRange (stackBelow m N) N q) ∧ Saved m m'

end

/-! ## The sides' layouts, forms and totals -/


/-- The stack `bus_layout` uses: 6 pushes, its 1752-byte frame, `stack_offsets`'s return address
and stack (`memset`'s and `memcpy`'s only their return address). -/
def busLayoutStack : Nat := 1808 + stackOffsetsStack
/-- The stack `block_form` uses: 6 pushes, its 24-byte frame, a callee's return address and
stack. -/
def blockFormStack : Nat := 80 + max formTermsStack formBufAddScaledStack
/-- The stack `accumulate_side` uses: 6 pushes, its 11976-byte frame (probed by 4096-byte
steps), a callee's return address and stack (`memcpy`'s only its return address). -/
def accumulateSideStack : Nat :=
  12032 + maxOf [eqEvalFnStack, ewMulStack, formBufAddScaledStack, blockFormStack,
    paddingWeightStack, evaluateStack]
/-- The stack `verify_bus_balance` uses: 6 pushes, its 5368-byte frame, a callee's return address
and stack; the closure's stack argument and alignment word (16 bytes) and `accumulate_side`'s 11
stack arguments and alignment word (96 bytes) above theirs. -/
def verifyBusBalanceStack : Nat :=
  5424 + maxOf [busLayoutStack, bitLengthStack, grindStack, sampleChallengesStack, squeezeStack,
    verifyGkrStack, readScalarsStack, readScalarStack, pushClaimStack, bytecodeShareStack,
    computedBytecodeValueStack, kpowStack, 16 + fpClosureStack, 96 + accumulateSideStack,
    bufEWExtendStack]

/-- An `Option<BusLayoutW>`'s bytes. -/
def optBusLayoutBytes : Nat := 8 + busLayoutBytes

/-- The `n` bytes from `a` readable and apart from the `s` bytes of stack and the return
address. -/
def InOk (m : MachineData) (a : BitVec 64) (n s : Nat) : Prop := Readable m a n ∧ OffStack m a n s

section
variable [Labels]

/-- `bus_layout`'s precondition: at most 3 framework sizes (RSI, RDX), each at most 30; the
blocks `bl` (RCX, R8), 2 to 51 of them, each of a table; the layout at R9 represents `L`; the
output (RDI) apart from them. x86-64 only: at least `2` blocks (AArch64: `1`), as rustc enters
the sizes' pair loop unconditionally (its callers pass `45` or `51` blocks, `PUSH_BLOCKS`,
`PULL_BLOCKS`, `COUNT_BLOCKS`). The loader slots are separate from all caller areas. -/
def BusLayoutPre (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m : MachineData) : Prop :=
  let o := reg m .rdi; let f := reg m .rsi; let b := reg m .rcx
  let lay := reg m .r9; let N := busLayoutStack
  let nf := 8 * (reg m .rdx).toNat; let nb := 16 * bl.length
  StackOk m N ∧ (reg m .rdx).toNat ≤ 3 ∧ (∀ s ∈ natsOf m f (reg m .rdx).toNat, s ≤ 30) ∧
    InOk m f nf N ∧ 2 ≤ bl.length ∧ bl.length ≤ maxBlocks ∧ (reg m .r8).toNat = bl.length ∧
    (∀ x ∈ bl, x.owner < nTables) ∧
    NativeRustcVm.BytesAt m.dmem b (bl.flatMap NativeRustcVm.Data.Block.bytes) ∧ InOk m b nb N ∧
    LayoutWAt m.dmem lay L ∧ InOk m lay layoutBytes N ∧ InOk m o optBusLayoutBytes N ∧
    Apart o optBusLayoutBytes f nf ∧ Apart o optBusLayoutBytes b nb ∧
    Apart o optBusLayoutBytes lay layoutBytes ∧
    GotAt m N ([(o, optBusLayoutBytes), (b, nb), (lay, layoutBytes)] ++
      (if nf = 0 then [] else [(f, nf)])) ["memcpy", "memset"]

/-- `bus_layout`'s postcondition: `busLayout` of the sizes and the blocks at the layout's heights
(whatever their rows) at `out`. -/
def BusLayoutPost (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m m' : MachineData) :
    Prop :=
  let o := reg m .rdi
  (∀ rows, OptBusLayoutWAt m'.dmem o (some (busLayout (natsOf m (reg m .rsi) (reg m .rdx).toNat)
    (bl.map (blockW L.tableLogHeights rows)).toArray))) ∧
    Changes m m' busLayoutStack o optBusLayoutBytes ∧ Saved m m'

/-- `block_form`'s precondition: a tuple of `TUPLES` (RDI), the weights (RSI, RDX), the `FormBuf`
at R9 an output apart from the stack, the data and the weights. -/
def BlockFormPre (m : MachineData) : Prop :=
  let f := reg m .r9; let N := blockFormStack
  StackOk m N ∧ RodataAt m N ∧ (reg m .rdi).toNat < NativeRustcVm.Data.tuples.length ∧
    SliceOk m (reg m .rsi) (reg m .rdx) N ∧ InOk m f formBufBytes N ∧ RodataApart f formBufBytes ∧
    Apart f formBufBytes (reg m .rsi) (16 * (reg m .rdx).toNat)

/-- `block_form`'s postcondition: `blockForm` of the tuple's forms at R9, when it fits. -/
def BlockFormPost (m m' : MachineData) : Prop :=
  let f := reg m .r9
  let g := blockForm ⟨0, 0, tupleOf (reg m .rdi).toNat, 0⟩ (slice m (reg m .rsi) (reg m .rdx))
    (ewArg (reg m .rcx) (reg m .r8))
  (if g.size ≤ formCap then boolRet m' = 1 ∧ FormBufAt m'.dmem f g else boolRet m' = 0) ∧
    Changes m m' blockFormStack f formBufBytes ∧ Saved m m'

/-- `accumulate_side`'s stack arguments past the side layout and the fingerprints' pointer: the
fingerprints' count, the weights, `side_beta`, the point, the tree's value. -/
def accArgs (m : MachineData) : Nat × Array EW × EW × Array EW × EW :=
  ((stackArg m 2).toNat, slice m (stackArg m 3) (stackArg m 4),
    ewArg (stackArg m 5) (stackArg m 6), slice m (stackArg m 7) (stackArg m 8),
    ewArg (stackArg m 9) (stackArg m 10))

/-- `accumulate_side`'s precondition: the forms at RSI represent `F`, the side (RDX) below `3`;
the blocks `bl` (RCX, R8, at least one, each of a table and a tuple of the data) as many as the
side layout's (stack word `0`, `SL`) table blocks; the layout at R9 represents `L`, its rows
`rows`; the fingerprints (stack word `1`, `n` stack word `2`), the weights, the point (fewer than
64 coordinates) readable; the forms fit; the outputs (RDI, 24 bytes, and the forms) apart from
the inputs, the data and the stack; the forms and the side layout apart from the 11 stack
arguments (`accumulate_side` writes the forms and re-reads the arguments in its table loop) and
the fingerprints. -/
def AccumulateSidePre (L : LayoutW) (rows : Array Nat) (bl : List NativeRustcVm.Data.Block)
    (F : Array (Array FormW)) (SL : BusLayoutW) (m : MachineData) : Prop :=
  let o := reg m .rdi; let fs := reg m .rsi; let b := reg m .rcx
  let lay := reg m .r9; let sl := stackArg m 0; let fp := stackArg m 1
  let N := accumulateSideStack; let nb := 16 * bl.length
  let (n, w, beta, point, tree) := accArgs m
  let fps := (ewsOf m.dmem fp n).toArray
  let B := (bl.map (blockW L.tableLogHeights rows)).toArray
  StackOk m N ∧ RodataAt m N ∧ ArgsOk m 11 ∧ (reg m .rdx).toNat < 3 ∧
    FormsAt m.dmem fs F ∧ InOk m fs formsBytes N ∧ RodataApart fs formsBytes ∧
    1 ≤ bl.length ∧ (reg m .r8).toNat = bl.length ∧
    (∀ x ∈ bl, x.owner < nTables ∧ x.tuple < NativeRustcVm.Data.tuples.length) ∧
    NativeRustcVm.BytesAt m.dmem b (bl.flatMap NativeRustcVm.Data.Block.bytes) ∧ InOk m b nb N ∧
    LayoutWAt m.dmem lay L ∧ rows.size = nTables ∧
    NativeRustcVm.WordsAt m.dmem (off lay 72) (rows.toList.map Nat.toUInt64) ∧
    InOk m lay layoutBytes N ∧
    BusLayoutWAt m.dmem sl SL ∧ SL.tables.size = bl.length ∧ InOk m sl busLayoutBytes N ∧
    (0 < n → InOk m fp (16 * n) N) ∧ SliceOk m (stackArg m 3) (stackArg m 4) N ∧
    (stackArg m 8).toNat < 64 ∧ SliceOk m (stackArg m 7) (stackArg m 8) N ∧
    SideFits F (reg m .rdx).toNat B SL fps w beta point tree ∧
    InOk m o 24 N ∧ RodataApart o 24 ∧ Apart o 24 fs formsBytes ∧
    Apart fs formsBytes b nb ∧ Apart fs formsBytes lay layoutBytes ∧
    Apart fs formsBytes sl busLayoutBytes ∧ (0 < n → Apart fs formsBytes fp (16 * n)) ∧
    Apart fs formsBytes (stackArg m 3) (16 * (stackArg m 4).toNat) ∧
    Apart fs formsBytes (stackArg m 7) (16 * (stackArg m 8).toNat) ∧
    Apart fs formsBytes (rspOf m + 8#64) 88 ∧
    Apart sl busLayoutBytes (rspOf m + 8#64) 88 ∧ (0 < n → Apart sl busLayoutBytes fp (16 * n)) ∧
    GotAt m N ([(o, 24), (fs, formsBytes), (b, nb), (lay, layoutBytes),
      (sl, busLayoutBytes), (stackArg m 3, 16 * (stackArg m 4).toNat),
      (stackArg m 7, 16 * (stackArg m 8).toNat), (rspOf m + 8#64, 88)] ++
      (if n = 0 then [] else [(fp, 16 * n)]) ++
      ([.tuples, .tables, .padding, .one] : List NativeRustcVm.Data.Item).map
        (fun i => (rodataAddr i, i.bytes.length))) ["memcpy"]

/-- `accumulate_side`'s postcondition: `accumulateSide`, its forms at RSI, its total at RDI. -/
def AccumulateSidePost (L : LayoutW) (rows : Array Nat) (bl : List NativeRustcVm.Data.Block)
    (F : Array (Array FormW)) (SL : BusLayoutW) (m m' : MachineData) : Prop :=
  let o := reg m .rdi; let fs := reg m .rsi
  let (n, w, beta, point, tree) := accArgs m
  let fps := (ewsOf m.dmem (stackArg m 1) n).toArray
  let B := (bl.map (blockW L.tableLogHeights rows)).toArray
  let r := accumulateSide F (reg m .rdx).toNat B SL fps w beta point tree
  OptEWAt m'.dmem o (some r.2) ∧ FormsAt m'.dmem fs r.1 ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange o 24 q ∨ InRange fs formsBytes q ∨
      InRange (stackBelow m accumulateSideStack) accumulateSideStack q) ∧ Saved m m'

/-! ## Phase 3 -/

/-- `verify_bus_balance`'s precondition: the transcript (RDI) at `s`; the layout at RSI
represents `L`, the `n` bytecode words (RDX, RCX) its bytecode; the bus's result (R8, 107768
bytes) and the claims (R9) outputs apart from the inputs, the transcript, the data and the stack.
A bytecode of no words may sit anywhere (rustc's dangling pointer): its bytes' conditions hold
for `n > 0`. -/
def VerifyBusBalancePre (a : DecArea) (s : TState) (L : LayoutW) (m : MachineData) : Prop :=
  let t := reg m .rdi; let lay := reg m .rsi; let bc := reg m .rdx
  let n := (reg m .rcx).toNat; let bus := reg m .r8; let cl := reg m .r9
  let N := verifyBusBalanceStack
  StackOk m N ∧ RcAt m N ∧ RodataAt m N ∧ TStateAt m.dmem t a s ∧ TStateOk m t a N ∧
    LayoutWAt m.dmem lay L ∧ InOk m lay layoutBytes N ∧ Apart lay layoutBytes t tstateBytes ∧
    L.bytecode.size = n ∧ NativeRustcVm.WordsAt m.dmem bc L.bytecode.toList ∧
    Readable m bc (8 * n) ∧ (0 < n → OffStack m bc (8 * n) N) ∧
    OutOk m t a bus busBytes N ∧ RodataApart bus busBytes ∧ Apart bus busBytes lay layoutBytes ∧
    (0 < n → Apart bus busBytes bc (8 * n)) ∧
    OutOk m t a cl claimsBytes N ∧ RodataApart cl claimsBytes ∧
    Apart cl claimsBytes lay layoutBytes ∧ (0 < n → Apart cl claimsBytes bc (8 * n)) ∧
    Apart bus busBytes cl claimsBytes ∧ RodataApart t tstateBytes ∧
    (0 < n → Apart bc (8 * n) t tstateBytes) ∧
    GotAt m N ([(t, tstateBytes), (a.words, 8 * a.len), (lay, layoutBytes),
      (bus, busBytes), (cl, claimsBytes), (rcAddr, 192)] ++ (if n = 0 then [] else [(bc, 8 * n)]) ++
      ([.tuples, .tables, .padding, .pushBlocks, .pullBlocks, .countBlocks, .one] :
        List NativeRustcVm.Data.Item).map (fun i => (rodataAddr i, i.bytes.length)))
      ["memcpy", "memset"]

/-- `verify_bus_balance`'s postcondition: `verifyBusBalance L`; on `some`, the next transcript,
the result at `bus`, its claims at `claims`; AL the `Option<()>`. -/
def VerifyBusBalancePost (a : DecArea) (s : TState) (L : LayoutW) (m m' : MachineData) : Prop :=
  let t := reg m .rdi; let bus := reg m .r8; let cl := reg m .r9
  let N := verifyBusBalanceStack
  let r := (verifyBusBalance L).run s
  OkAl m' r.isSome ∧
    (∀ res s', r = some (res, s') → TStateAt m'.dmem t a s' ∧ BusWAt m'.dmem bus res ∧
      ClaimsWAt m'.dmem cl res.claims) ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange t tstateBytes q ∨ InRange bus busBytes q ∨
      InRange cl claimsBytes q ∨ InRange (stackBelow m N) N q) ∧ Saved m m'

end

end

end NativeRustcVmX64
