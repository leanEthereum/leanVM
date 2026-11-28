module

public import NativeRustcVmArm.Code.Vm.AccumulateSide.Names
public import NativeRustcVmArm.Code.Vm.BlockForm.Names
public import NativeRustcVmArm.Code.Vm.BusLayout.Names
public import NativeRustcVmArm.Code.Vm.BytecodeShare.Names
public import NativeRustcVmArm.Code.Vm.ComputedBytecodeValue.Names
public import NativeRustcVmArm.Code.Vm.Fingerprints.Names
public import NativeRustcVmArm.Code.Vm.GkrLayers.Names
public import NativeRustcVmArm.Code.Vm.GkrStep.Names
public import NativeRustcVmArm.Code.Vm.VerifyBusBalance.Names
public import NativeRustcVmArm.Code.Vm.VerifyBusBalanceClosure0.Names
public import NativeRustcVmArm.Code.Vm.VerifyGkrGrandProducts.Names
public import NativeRustcVmArm.Spec.Sumcheck
public import NativeRustcVmArm.Spec.Layout
public import NativeRustcVm.Bus.Rep
public import NativeRustcVm.Bus.Blocks
public import NativeRustcVm.Bus.FitsModel

/-!
# The contracts of `bus.rs`'s and `gkr.rs`'s functions on AArch64

Each function uses the stack below SP (`<fn>Stack` bytes, its callees' included; `StackOk` in its
precondition) and returns with the callee-saved registers and SP kept (`Saved`), no byte changed
outside its outputs and that stack. Results are the model's (`NativeVm.Model`, `Bus.lean`,
`Gkr.lean`); a `VM` step's `none` is the Rust's `None` (X0 = `0`, or a tag word `0`), and on it a
contract says nothing more than the frame.

- `gkr_step(t, step, last, s)` (X0 to X3; rustc specialised the body to `step ∈ {1, 2}`): the
  `GkrStateW` at `s` (`GkrStateWAt`) becomes `gkrStep step last`'s; the point stays within its 63
  slots (`|point| + step ≤ 63`, as `verify_bus_balance`'s `depth < 64` makes it).
- `gkr_layers(t, depth, s)` (X0 to X2): `gkrLayers depth` (`depth + |point| ≤ 63`).
- `verify_gkr_grand_products(out, t, depth, s)` (X0 to X3; `depth ≤ 63`): the count root as the
  `Option<EW>` at `out`, the point and the trees' values at `s`.
- `fingerprints(out, weights, memory, memory_low, bytecode_low, share, pc, memory_count,
  bytecode_count)` (X0 to X7, then the stack; rustc dropped `weights`'s length, which is `16`, and
  `pc`'s limb `1`, which is `0`): the three fingerprints at `out`.
- `verify_bus_balance::{closure#0}(out, env, pc, memory_count, bytecode_count)` (X0 to X6): the
  `fingerprints` of the slices its environment names.
- `computed_bytecode_value(words, point, value)` (X0 to X5): X0 = `1` iff the bytecode's
  multilinear extension at the point is the value.
- `bytecode_share(out, t, weights, bytecode_low, point)` (X0 to X5; `weights` its `16` elements,
  `|bytecode_low| ≤ 63`): `bytecodeShare` as the `Option<(EW, usize, EW)>` at `out`, the bytecode
  point at `point`.
- `bus_layout(out, framework_log_rows, blocks, layout)` (X0 to X5; at most 3 framework sizes, 1 to
  51 blocks, every size at most 30): `busLayout` of the sizes and the blocks (`blockW`, at the
  layout's heights) as the `Option<BusLayoutW>` at `out`, never `None`.
- `block_form(tuple, side_weights, side_beta, form)` (X0 to X5; rustc passes the block's tuple
  alone): `blockForm` of the tuple's forms (`tupleOf`) at `form` if it fits a `FormBuf`, X0 = `1`;
  else X0 = `0`.
- `accumulate_side(out, forms, side, blocks, layout, side_layout, framework_fingerprints,
  side_weights, side_beta, point, tree_value)` (X0 to X7, then the stack): `accumulateSide` of the
  side's blocks (`blockW` at the layout's heights and rows), the forms at `forms` (`FormsAt`), the
  total as the `Option<EW>` at `out`; the forms fit their `FormBuf`s (`SideFits`).
- `verify_bus_balance(t, layout, bytecode, bus, claims)` (X0 to X5): `verifyBusBalance` of the
  layout (`LayoutWAt`) and the bytecode, the result at `bus` (`BusWAt`), its claims at `claims`
  (`ClaimsWAt`), X0 the `Option<()>`. The blocks are the data's (`busBlocks_eq`).
-/

namespace NativeRustcVmArm

open NativeRustcArm NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVm (ewsOf wordsOf wordOf ewOf EWsAt EWAt WordAt BufEWAt)

@[expose] public section

/-! ## Symbols -/


/-! ## Stacks -/

/-- The largest of a list. -/
def maxOf (ns : List Nat) : Nat := ns.foldr max 0

/-- The stack `gkr_step` uses: its 1392-byte frame and its callees' largest. -/
def gkrStepStack : Nat :=
  1392 + maxOf [bitLengthStack, grindStack, squeezeStack, polyEvalStack, sumcheckGkrStack,
    readScalarsStack, prodEStack, sampleChallengesStack, mleStack]
/-- The stack `gkr_layers` uses. -/
def gkrLayersStack : Nat := 48 + gkrStepStack
/-- The stack `verify_gkr_grand_products` uses. -/
def verifyGkrStack : Nat := 96 + max readScalarStack gkrLayersStack
/-- The stack `fingerprints` uses. -/
def fingerprintsStack : Nat := 320 + maxOf [kpowStack, dotStack, indexMleFromStack]
/-- The stack `verify_bus_balance::{closure#0}` uses. -/
def fpClosureStack : Nat := 64 + fingerprintsStack
/-- The stack `computed_bytecode_value` uses. -/
def computedBytecodeValueStack : Nat := 32 + mleStack
/-- The stack `bytecode_share` uses. -/
def bytecodeShareStack : Nat :=
  432 + maxOf [readScalarStack, sumcheckPlainStack, eqKernelStack, dotStack, ewMulStack]

section
variable [Labels]

/-! ## The GKR walk -/

/-- The `GkrStateW` at `p` beside the `TState` at `t` for a function using `N` bytes of stack. -/
def GkrOk (m : MachineData) (t : BitVec 64) (a : DecArea) (p : BitVec 64) (N : Nat) : Prop :=
  OutOk m t a p gkrStateBytes N

/-- `gkr_step`'s precondition: `step ∈ {1, 2}` (X1), `last` (X2) `0` or `1`, the point's
`step` more coordinates within its capacity. -/
def GkrStepPre (a : DecArea) (s : TState) (g : GkrStateW) (m : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let p := m.regs.X3.toBitVec
  StackOk m gkrStepStack ∧ RcAt m gkrStepStack ∧ TStateAt m.dmem t a s ∧
    TStateOk m t a gkrStepStack ∧ (m.regs.X1.toNat = 1 ∨ m.regs.X1.toNat = 2) ∧
    m.regs.X2.toNat ≤ 1 ∧ g.point.size + m.regs.X1.toNat ≤ busPointCap ∧
    GkrOk m t a p gkrStepStack ∧ GkrStateWAt m.dmem p g

/-- `gkr_step`'s postcondition: `gkrStep step last g`. -/
def GkrStepPost (a : DecArea) (s : TState) (g : GkrStateW) (m m' : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let p := m.regs.X3.toBitVec
  let r := (gkrStep m.regs.X1.toNat (m.regs.X2.toNat = 1) g).run s
  m'.regs.X0 = okWord r.isSome ∧
    (∀ g' s', r = some (g', s') → TStateAt m'.dmem t a s' ∧ GkrStateWAt m'.dmem p g') ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange t tstateBytes q ∨ InRange p gkrStateBytes q ∨
      InRange (stackBelow m gkrStepStack) gkrStepStack q) ∧ Saved m m'

/-- `gkr_layers`'s precondition: `depth` (X1) more coordinates within the point's capacity. -/
def GkrLayersPre (a : DecArea) (s : TState) (g : GkrStateW) (m : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let p := m.regs.X2.toBitVec
  StackOk m gkrLayersStack ∧ RcAt m gkrLayersStack ∧ TStateAt m.dmem t a s ∧
    TStateOk m t a gkrLayersStack ∧ g.point.size + m.regs.X1.toNat ≤ busPointCap ∧
    GkrOk m t a p gkrLayersStack ∧ GkrStateWAt m.dmem p g

/-- `gkr_layers`'s postcondition: `gkrLayers depth g`. -/
def GkrLayersPost (a : DecArea) (s : TState) (g : GkrStateW) (m m' : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let p := m.regs.X2.toBitVec
  let r := (gkrLayers m.regs.X1.toNat g).run s
  m'.regs.X0 = okWord r.isSome ∧
    (∀ g' s', r = some (g', s') → TStateAt m'.dmem t a s' ∧ GkrStateWAt m'.dmem p g') ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange t tstateBytes q ∨ InRange p gkrStateBytes q ∨
      InRange (stackBelow m gkrLayersStack) gkrLayersStack q) ∧ Saved m m'

/-- `verify_gkr_grand_products`'s precondition: `depth ≤ 63` (X2); the `Option<EW>` at `out`
(X0) and the `GkrStateW` at `s` (X3) outputs, apart. -/
def VerifyGkrPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec; let t := m.regs.X1.toBitVec; let p := m.regs.X3.toBitVec
  StackOk m verifyGkrStack ∧ RcAt m verifyGkrStack ∧ TStateAt m.dmem t a s ∧
    TStateOk m t a verifyGkrStack ∧ m.regs.X2.toNat ≤ busPointCap ∧
    OutOk m t a o 24 verifyGkrStack ∧ GkrOk m t a p verifyGkrStack ∧ Apart o 24 p gkrStateBytes

/-- `verify_gkr_grand_products`'s postcondition: `verifyGkrGrandProducts depth`, the count root at
`out`, the point and the values at `s`. -/
def VerifyGkrPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec; let t := m.regs.X1.toBitVec; let p := m.regs.X3.toBitVec
  let r := (verifyGkrGrandProducts m.regs.X2.toNat).run s
  OptEWAt m'.dmem o (r.map (·.1.1)) ∧
    (∀ c pt vs s', r = some ((c, pt, vs), s') →
      TStateAt m'.dmem t a s' ∧ GkrStateWAt m'.dmem p ⟨vs, pt⟩) ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange o 24 q ∨ InRange t tstateBytes q ∨
      InRange p gkrStateBytes q ∨ InRange (stackBelow m verifyGkrStack) verifyGkrStack q) ∧
    Saved m m'

end

/-! ## Fingerprints -/

/-- `n` readable elements of `E` at `p`, apart from `s` bytes of stack. -/
def EWsOk (m : MachineData) (p : BitVec 64) (n s : Nat) : Prop :=
  Readable m p (16 * n) ∧ OffStack m p (16 * n) s

/-- The word `k` bytes above SP (a stack argument). -/
def stackArg (m : MachineData) (k : Nat) : UInt64 :=
  wordOf m.dmem (m.regs.SP.toBitVec + BitVec.ofNat 64 k)

/-- `fingerprints`'s arguments: `weights` (5 of them read), `memory`, `memory_low`,
`bytecode_low`, the share, `pc` (limb `0`), the counts. -/
def fpArgs (m : MachineData) : Array EW × Array EW × Array EW × Array EW × EW × EW × EW × EW :=
  ((ewsOf m.dmem m.regs.X1.toBitVec 5).toArray, (ewsOf m.dmem m.regs.X2.toBitVec 2).toArray,
    slice m m.regs.X3 m.regs.X4, slice m m.regs.X5 m.regs.X6, ⟨m.regs.X7, stackArg m 0⟩,
    EW.ofK (stackArg m 8), ⟨stackArg m 16, stackArg m 24⟩, ⟨stackArg m 32, stackArg m 40⟩)

/-- `fingerprints`'s precondition: the slices readable, apart from the stack; the six stack
arguments' words data memory; the 48 bytes at `out` (X0) data memory, apart from the stack. -/
def FingerprintsPre (m : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec; let sp := m.regs.SP.toBitVec
  StackOk m fingerprintsStack ∧ EWsOk m m.regs.X1.toBitVec 5 fingerprintsStack ∧
    EWsOk m m.regs.X2.toBitVec 2 fingerprintsStack ∧
    SliceOk m m.regs.X3 m.regs.X4 fingerprintsStack ∧
    SliceOk m m.regs.X5 m.regs.X6 fingerprintsStack ∧ Readable m sp 48 ∧
    Readable m o 48 ∧ OffStack m o 48 fingerprintsStack

/-- `fingerprints`'s postcondition: the three fingerprints at `out`. -/
def FingerprintsPost (m m' : MachineData) : Prop :=
  let (w, mem, ml, bl, share, pc, mc, bc) := fpArgs m
  EWsAt m'.dmem m.regs.X0.toBitVec (fingerprints w mem ml bl share pc mc bc).toList ∧
    Changes m m' fingerprintsStack m.regs.X0.toBitVec 48 ∧ Saved m m'

/-- The closure's environment at `e` (56 bytes): `weights`'s, `memory`'s addresses, `memory_low`'s
and `bytecode_low`'s addresses and lengths, the share's address. -/
def envWord (m : MachineData) (i : Nat) : UInt64 :=
  wordOf m.dmem (m.regs.X1.toBitVec + BitVec.ofNat 64 (8 * i))

/-- The closure's arguments, as `fpArgs`. -/
def fpClosureArgs (m : MachineData) :
    Array EW × Array EW × Array EW × Array EW × EW × EW × EW × EW :=
  ((ewsOf m.dmem (envWord m 0).toBitVec 5).toArray, (ewsOf m.dmem (envWord m 1).toBitVec 2).toArray,
    slice m (envWord m 2) (envWord m 3), slice m (envWord m 4) (envWord m 5),
    ewOf m.dmem (envWord m 6).toBitVec, EW.ofK m.regs.X2, ⟨m.regs.X3, m.regs.X4⟩,
    ⟨m.regs.X5, m.regs.X6⟩)

/-- The closure's precondition: its environment (X1, 56 bytes) and what it names readable, apart
from the stack; the 48 bytes at `out` (X0). -/
def FpClosurePre (m : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec; let e := m.regs.X1.toBitVec
  StackOk m fpClosureStack ∧ Readable m e 56 ∧ OffStack m e 56 fpClosureStack ∧
    EWsOk m (envWord m 0).toBitVec 5 fpClosureStack ∧
    EWsOk m (envWord m 1).toBitVec 2 fpClosureStack ∧
    SliceOk m (envWord m 2) (envWord m 3) fpClosureStack ∧
    SliceOk m (envWord m 4) (envWord m 5) fpClosureStack ∧
    EWsOk m (envWord m 6).toBitVec 1 fpClosureStack ∧
    Readable m o 48 ∧ OffStack m o 48 fpClosureStack

/-- The closure's postcondition: the three fingerprints at `out`. -/
def FpClosurePost (m m' : MachineData) : Prop :=
  let (w, mem, ml, bl, share, pc, mc, bc) := fpClosureArgs m
  EWsAt m'.dmem m.regs.X0.toBitVec (fingerprints w mem ml bl share pc mc bc).toList ∧
    Changes m m' fpClosureStack m.regs.X0.toBitVec 48 ∧ Saved m m'

/-! ## The bytecode's value -/

/-- `computed_bytecode_value`'s precondition: the `n` words (X0, X1; apart from the stack when
`0 < n`, the empty slice's pointer dangling), the point (X2, X3). -/
def ComputedBytecodeValuePre (m : MachineData) : Prop :=
  StackOk m computedBytecodeValueStack ∧ Readable m m.regs.X0.toBitVec (8 * m.regs.X1.toNat) ∧
    (0 < m.regs.X1.toNat →
      OffStack m m.regs.X0.toBitVec (8 * m.regs.X1.toNat) computedBytecodeValueStack) ∧
    SliceOk m m.regs.X2 m.regs.X3 computedBytecodeValueStack

/-- `computed_bytecode_value`'s postcondition: `computedBytecodeValue words point value` succeeds
iff X0 = `1`. -/
def ComputedBytecodeValuePost (m m' : MachineData) : Prop :=
  m'.regs.X0 = okWord (multilinearEval (wordSliceE m m.regs.X0 m.regs.X1)
      (slice m m.regs.X2 m.regs.X3) == ewArg m.regs.X4 m.regs.X5) ∧
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

/-- `bytecode_share`'s precondition: `weights` (X2) its 16 elements, `bytecode_low` (X3, X4) at
most 63, the output (X0, 48 bytes) and the point's 67 slots (X5) outputs, apart. -/
def BytecodeSharePre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec; let t := m.regs.X1.toBitVec; let p := m.regs.X5.toBitVec
  let N := bytecodeShareStack
  StackOk m N ∧ RcAt m N ∧ TStateAt m.dmem t a s ∧ TStateOk m t a N ∧
    EWsOk m m.regs.X2.toBitVec 16 N ∧ m.regs.X4.toNat ≤ busPointCap ∧
    SliceOk m m.regs.X3 m.regs.X4 N ∧ OutOk m t a o 48 N ∧ OutOk m t a p (16 * sharePointSlots) N ∧
    Apart o 48 p (16 * sharePointSlots) ∧
    Apart p (16 * sharePointSlots) m.regs.X3.toBitVec (16 * m.regs.X4.toNat) ∧
    Apart m.regs.X2.toBitVec (16 * 16) t tstateBytes ∧
    Apart m.regs.X3.toBitVec (16 * m.regs.X4.toNat) t tstateBytes

/-- `bytecode_share`'s postcondition: `bytecodeShare weights bytecode_low`, the share, the point's
length and the value at `out`, the bytecode point at `point`. -/
def BytecodeSharePost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec; let t := m.regs.X1.toBitVec; let p := m.regs.X5.toBitVec
  let N := bytecodeShareStack
  let r := (bytecodeShare (ewsOf m.dmem m.regs.X2.toBitVec 16).toArray
    (slice m m.regs.X3 m.regs.X4)).run s
  OptShareAt m'.dmem o (r.map (·.1)) ∧
    (∀ x s', r = some (x, s') → EWsAt m'.dmem p x.2.1.toList ∧ TStateAt m'.dmem t a s') ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange o 48 q ∨ InRange p (16 * sharePointSlots) q ∨
      InRange t tstateBytes q ∨ InRange (stackBelow m N) N q) ∧ Saved m m'

end

/-! ## The sides' layouts, forms and totals -/


/-- The stack `bus_layout` uses: its 1840-byte frame and `stack_offsets`'s (`memset`'s and
`memcpy`'s none). -/
def busLayoutStack : Nat := 1840 + stackOffsetsStack
/-- The stack `block_form` uses. -/
def blockFormStack : Nat := 64 + max formTermsStack formBufAddScaledStack
/-- The stack `accumulate_side` uses: its 12096-byte frame and its callees' largest. -/
def accumulateSideStack : Nat :=
  12096 + maxOf [eqEvalFnStack, ewMulStack, formBufAddScaledStack, blockFormStack,
    paddingWeightStack, evaluateStack]
/-- The stack `verify_bus_balance` uses: its 5488-byte frame and its callees' largest
(`accumulate_side`'s). -/
def verifyBusBalanceStack : Nat :=
  5488 + maxOf [busLayoutStack, bitLengthStack, grindStack, sampleChallengesStack, squeezeStack,
    verifyGkrStack, readScalarsStack, readScalarStack, pushClaimStack, bytecodeShareStack,
    computedBytecodeValueStack, kpowStack, fpClosureStack, accumulateSideStack, bufExtendStack]

/-- An `Option<BusLayoutW>`'s bytes. -/
def optBusLayoutBytes : Nat := 8 + busLayoutBytes

/-- The `n` bytes from `a` readable and apart from the `s` bytes of stack. -/
def InOk (m : MachineData) (a : BitVec 64) (n s : Nat) : Prop := Readable m a n ∧ OffStack m a n s

section
variable [Labels]

/-- `bus_layout`'s precondition: at most 3 framework sizes (X1, X2), each at most 30; the blocks
`bl` (X3, X4), 1 to 51 of them, each of a table; the layout at X5 represents `L`; the output (X0)
apart from them. -/
def BusLayoutPre (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec; let f := m.regs.X1.toBitVec; let b := m.regs.X3.toBitVec
  let lay := m.regs.X5.toBitVec; let N := busLayoutStack
  let nf := 8 * m.regs.X2.toNat; let nb := 16 * bl.length
  StackOk m N ∧ m.regs.X2.toNat ≤ 3 ∧ (∀ s ∈ natsOf m m.regs.X1 m.regs.X2.toNat, s ≤ 30) ∧
    InOk m f nf N ∧ 1 ≤ bl.length ∧ bl.length ≤ maxBlocks ∧ m.regs.X4.toNat = bl.length ∧
    (∀ x ∈ bl, x.owner < nTables) ∧
    NativeRustcVm.BytesAt m.dmem b (bl.flatMap NativeRustcVm.Data.Block.bytes) ∧ InOk m b nb N ∧
    LayoutWAt m.dmem lay L ∧ InOk m lay layoutBytes N ∧ InOk m o optBusLayoutBytes N ∧
    Apart o optBusLayoutBytes f nf ∧ Apart o optBusLayoutBytes b nb ∧
    Apart o optBusLayoutBytes lay layoutBytes

/-- `bus_layout`'s postcondition: `busLayout` of the sizes and the blocks at the layout's heights
(whatever their rows) at `out`. -/
def BusLayoutPost (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m m' : MachineData) :
    Prop :=
  let o := m.regs.X0.toBitVec
  (∀ rows, OptBusLayoutWAt m'.dmem o (some (busLayout (natsOf m m.regs.X1 m.regs.X2.toNat)
    (bl.map (blockW L.tableLogHeights rows)).toArray))) ∧
    Changes m m' busLayoutStack o optBusLayoutBytes ∧ Saved m m'

/-- `block_form`'s precondition: a tuple of `TUPLES` (X0), the weights (X1, X2), the `FormBuf` at
X5 an output apart from the stack, the data and the weights. -/
def BlockFormPre (m : MachineData) : Prop :=
  let f := m.regs.X5.toBitVec; let N := blockFormStack
  StackOk m N ∧ RodataAt m N ∧ m.regs.X0.toNat < NativeRustcVm.Data.tuples.length ∧
    SliceOk m m.regs.X1 m.regs.X2 N ∧ InOk m f formBufBytes N ∧ RodataApart f formBufBytes ∧
    Apart f formBufBytes m.regs.X1.toBitVec (16 * m.regs.X2.toNat)

/-- `block_form`'s postcondition: `blockForm` of the tuple's forms at X5, when it fits. -/
def BlockFormPost (m m' : MachineData) : Prop :=
  let f := m.regs.X5.toBitVec
  let g := blockForm ⟨0, 0, tupleOf m.regs.X0.toNat, 0⟩ (slice m m.regs.X1 m.regs.X2)
    (ewArg m.regs.X3 m.regs.X4)
  (if g.size ≤ formCap then m'.regs.X0 = 1 ∧ FormBufAt m'.dmem f g else m'.regs.X0 = 0) ∧
    Changes m m' blockFormStack f formBufBytes ∧ Saved m m'

/-- `accumulate_side`'s stack arguments: the fingerprints' count, the weights, `side_beta`, the
point, the tree's value. -/
def accArgs (m : MachineData) : Nat × Array EW × EW × Array EW × EW :=
  ((stackArg m 0).toNat, slice m (stackArg m 8) (stackArg m 16), ⟨stackArg m 24, stackArg m 32⟩,
    slice m (stackArg m 40) (stackArg m 48), ⟨stackArg m 56, stackArg m 64⟩)

/-- `accumulate_side`'s precondition: the forms at X1 represent `F`, the side (X2) below `3`; the
blocks `bl` (X3, X4, at least one, each of a table and a tuple of the data) as many as the side
layout's (X6, `SL`) table blocks; the layout at X5 represents `L`, its rows `rows`; the
fingerprints (X7, `n` the first stack argument), the weights, the point (fewer than 64
coordinates) readable; the forms fit; the outputs (X0, 24 bytes, and the forms) apart from the
inputs, the data and the stack; the side layout apart from the stack arguments and the
fingerprints (`accumulate_side` reads them in one block). -/
def AccumulateSidePre (L : LayoutW) (rows : Array Nat) (bl : List NativeRustcVm.Data.Block)
    (F : Array (Array FormW)) (SL : BusLayoutW) (m : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec; let fs := m.regs.X1.toBitVec; let b := m.regs.X3.toBitVec
  let lay := m.regs.X5.toBitVec; let sl := m.regs.X6.toBitVec; let fp := m.regs.X7.toBitVec
  let N := accumulateSideStack; let nb := 16 * bl.length
  let (n, w, beta, point, tree) := accArgs m
  let fps := (ewsOf m.dmem fp n).toArray
  let B := (bl.map (blockW L.tableLogHeights rows)).toArray
  StackOk m N ∧ RodataAt m N ∧ Readable m m.regs.SP.toBitVec 72 ∧ m.regs.X2.toNat < 3 ∧
    FormsAt m.dmem fs F ∧ InOk m fs formsBytes N ∧ RodataApart fs formsBytes ∧
    1 ≤ bl.length ∧ m.regs.X4.toNat = bl.length ∧
    (∀ x ∈ bl, x.owner < nTables ∧ x.tuple < NativeRustcVm.Data.tuples.length) ∧
    NativeRustcVm.BytesAt m.dmem b (bl.flatMap NativeRustcVm.Data.Block.bytes) ∧ InOk m b nb N ∧
    LayoutWAt m.dmem lay L ∧ rows.size = nTables ∧
    NativeRustcVm.WordsAt m.dmem (off lay 72) (rows.toList.map Nat.toUInt64) ∧
    InOk m lay layoutBytes N ∧
    BusLayoutWAt m.dmem sl SL ∧ SL.tables.size = bl.length ∧ InOk m sl busLayoutBytes N ∧
    (0 < n → InOk m fp (16 * n) N) ∧ SliceOk m (stackArg m 8) (stackArg m 16) N ∧
    (stackArg m 48).toNat < 64 ∧ SliceOk m (stackArg m 40) (stackArg m 48) N ∧
    SideFits F m.regs.X2.toNat B SL fps w beta point tree ∧
    InOk m o 24 N ∧ RodataApart o 24 ∧ Apart o 24 fs formsBytes ∧
    Apart fs formsBytes b nb ∧ Apart fs formsBytes lay layoutBytes ∧
    Apart fs formsBytes sl busLayoutBytes ∧ (0 < n → Apart fs formsBytes fp (16 * n)) ∧
    Apart fs formsBytes (stackArg m 8).toBitVec (16 * (stackArg m 16).toNat) ∧
    Apart fs formsBytes (stackArg m 40).toBitVec (16 * (stackArg m 48).toNat) ∧
    Apart fs formsBytes m.regs.SP.toBitVec 72 ∧
    Apart sl busLayoutBytes m.regs.SP.toBitVec 72 ∧ (0 < n → Apart sl busLayoutBytes fp (16 * n))

/-- `accumulate_side`'s postcondition: `accumulateSide`, its forms at X1, its total at X0. -/
def AccumulateSidePost (L : LayoutW) (rows : Array Nat) (bl : List NativeRustcVm.Data.Block)
    (F : Array (Array FormW)) (SL : BusLayoutW) (m m' : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec; let fs := m.regs.X1.toBitVec
  let (n, w, beta, point, tree) := accArgs m
  let fps := (ewsOf m.dmem m.regs.X7.toBitVec n).toArray
  let B := (bl.map (blockW L.tableLogHeights rows)).toArray
  let r := accumulateSide F m.regs.X2.toNat B SL fps w beta point tree
  OptEWAt m'.dmem o (some r.2) ∧ FormsAt m'.dmem fs r.1 ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange o 24 q ∨ InRange fs formsBytes q ∨
      InRange (stackBelow m accumulateSideStack) accumulateSideStack q) ∧ Saved m m'

/-! ## Phase 3 -/

/-- `verify_bus_balance`'s precondition: the transcript (X0) at `s`; the layout at X1 represents
`L`, the `n` bytecode words (X2, X3) its bytecode; the bus's result (X4, 107768 bytes) and the
claims (X5) outputs apart from the inputs, the transcript, the data and the stack. A bytecode of
no words may sit anywhere (rustc's dangling pointer): its bytes' conditions hold for `n > 0`. -/
def VerifyBusBalancePre (a : DecArea) (s : TState) (L : LayoutW) (m : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let lay := m.regs.X1.toBitVec; let bc := m.regs.X2.toBitVec
  let n := m.regs.X3.toNat; let bus := m.regs.X4.toBitVec; let cl := m.regs.X5.toBitVec
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
    (0 < n → Apart bc (8 * n) t tstateBytes)

/-- `verify_bus_balance`'s postcondition: `verifyBusBalance L`; on `some`, the next transcript,
the result at `bus`, its claims at `claims`. -/
def VerifyBusBalancePost (a : DecArea) (s : TState) (L : LayoutW) (m m' : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let bus := m.regs.X4.toBitVec; let cl := m.regs.X5.toBitVec
  let N := verifyBusBalanceStack
  let r := (verifyBusBalance L).run s
  m'.regs.X0 = okWord r.isSome ∧
    (∀ res s', r = some (res, s') → TStateAt m'.dmem t a s' ∧ BusWAt m'.dmem bus res ∧
      ClaimsWAt m'.dmem cl res.claims) ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange t tstateBytes q ∨ InRange bus busBytes q ∨
      InRange cl claimsBytes q ∨ InRange (stackBelow m N) N q) ∧ Saved m m'

end

theorem verifyBusBalanceStack_eq : verifyBusBalanceStack = 18288 := by decide

end

end NativeRustcVmArm
