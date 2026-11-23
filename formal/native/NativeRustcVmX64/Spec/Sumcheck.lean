module

public import NativeRustcVmX64.Spec.Transcript
public import NativeRustcVmX64.Spec.Arrays
public import NativeRustcX64.Spec.Got
public import NativeRustcVm.Sumcheck.Rows
public import NativeRustcVm.Sumcheck.Model
public import NativeRustcVmX64.Code.Vm.Climb.Names
public import NativeRustcVmX64.Code.Vm.OpenPhase.Names
public import NativeRustcVmX64.Code.Vm.RowsRow.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfGkrStep.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfVerifyLayer.Names
public import NativeRustcVmX64.Code.Vm.TStateQueryOpenings.Names
public import NativeRustcVmX64.Code.Vm.TStateSumcheckRoundPoly.Names

/-!
# The contracts of `transcript.rs`'s openings and sumcheck functions on x86-64

The AArch64 contracts (`NativeRustcVmArm.Spec.Sumcheck`) with the System V registers: arguments in
RDI, RSI, RDX, RCX, R8, R9, then on the stack above the return address (`stackArg`, mapped by
`ArgsOk`); a slice result in RAX, RDX; an `Option<()>` in AL (`OkAl`). Each function uses the
stack below RSP (`<fn>Stack` bytes: its pushes, its frame, its callees' return addresses and
stacks; `StackOk` also maps its return address at RSP) and returns with the callee-saved registers
kept (and RSP 8 above, `Spec`), no byte changed outside its outputs and that stack. Those that hash
or touch the transcript read the round constants (`RcAt`) and ordinary-memory GOT slots
(`GotAt`), disjoint from their stack and protected areas. Results are the model's
(`NativeVm.Model`):

- `Rows::row(rows, j)` (RDI, RSI): row `j < count` of the rows at `rows` (`RowsAt`), its address
  in RAX and its word count in RDX.
- `climb(out, node, q, path, height)` (RDI to R8; rustc fixed the path's slice to its
  `4 · wireMaxHeight` words): the 4 words at `out` become `climb node q path`, the path the
  `height ≤ 32` digests at `path`.
- `open_phase(out, root, height, width, positions, n, phase)` (RDI to R9, the phase's address the
  stack argument; its slice fixed to its `phaseWords` words): the `Option<Rows>` at `out` becomes
  `openPhase root height width positions ph` of the phase `ph` at `phase` (`PhaseAt`), its rows
  read at `phase + 24`.
- `TState::query_openings(out, t, i, positions, n)` (RDI to R8): `queryOpenings i positions`, the
  `Option<Rows>` at `out`, the rows read in the decoded area.
- `TState::sumcheck_round_poly(t, count, claim, eq, msg)` (RDI, RSI, `claim` RDX, RCX, `&eq` R8,
  `msg` R9; `2 ≤ count ≤ 5`, rustc dropped the Rust's test for its callers' counts):
  `sumcheckRoundPoly count claim eq`, the round polynomial's `count` coefficients at `msg`; its
  `sum_e` calls take at most `count - 1 ≤ 4` elements (`SumEPre`'s `len ≤ 16`).
- `TState::sumcheck(out, t, claim, count, equality, slots)` with `sumcheck_plain`'s closure
  (RDI, RSI, `claim` RDX, RCX, `count` R8, slots R9 and the stack argument `n`):
  `sumcheckPlain claim count n`, the challenges in the `n` slots, the final claim the
  `Option<EW>` at `out`.
- the same with `gkr_step`'s closure `|i| point.get(i)` (`point` R9 and the stack argument
  `|point|`, then the stack arguments slots, `n`): `sumcheckFn claim count (point[·]?) n`
  (`sumcheck claim count (point.map some)` when `n = |point|`, `sumcheckFn_getElem?`). It reads
  the slots' address and `|point|` from the stack in every round: the `TState` and the slots are
  apart from the arguments.
- the same with `verify_layer`'s closure `|i| old.get(i)` and `count = 3` (rustc dropped the
  argument; `old` R8, R9, then the stack arguments slots, `n`; the slots' address read in every
  round).
-/

namespace NativeRustcVmX64

open NativeRustcX64 NativeVm NativeVm.Model LeanVM.Protocol.Compile NativeRustcVm.Transcript
open NativeRustcVm.Sumcheck

@[expose] public section

/-! ## Stacks -/

/-- `Rows::row` uses no stack. -/
def rowsRowStack : Nat := 0
/-- The stack `climb` uses: 6 pushes, its 104-byte frame, then `hash_pair`'s return address and
stack. -/
def climbStack : Nat := 48 + 104 + 8 + hashPairStack
/-- The stack `open_phase` uses: 6 pushes, its 120-byte frame, then the return address and the
larger stack of `keccak256_words`'s and `climb`'s. -/
def openPhaseStack : Nat := 48 + 120 + 8 + max keccak256WordsStack climbStack
/-- The stack `query_openings` uses: 6 pushes, its 40-byte frame (`open_phase`'s stack argument
and output), then the return address and the larger stack of `Decoded::phase`'s and
`open_phase`'s. -/
def queryOpeningsStack : Nat := 48 + 40 + 8 + max phaseStack openPhaseStack
/-- The stack `sumcheck_round_poly` uses: 6 pushes, its 56-byte frame, then the return address and
the largest stack of its callees'. -/
def roundPolyStack : Nat :=
  48 + 56 + 8 + max (max readScalarStack readScalarsStack)
    (max (max sumEStack bitLengthStack) (max grindStack ewMulStack))
/-- The largest stack of the sumcheck loop's callees. -/
def sumcheckCallStack : Nat := max roundPolyStack (max squeezeStack polyEvalStack)
/-- The stack `sumcheck` with `sumcheck_plain`'s closure uses: 6 pushes, its 120-byte frame,
then a callee's return address and stack. -/
def sumcheckPlainStack : Nat := 48 + 120 + 8 + sumcheckCallStack
/-- The stack `sumcheck` with `gkr_step`'s closure uses: 6 pushes, its 136-byte frame, then a
callee's return address and stack. -/
def sumcheckGkrStack : Nat := 48 + 136 + 8 + sumcheckCallStack
/-- The stack `sumcheck` with `verify_layer`'s closure uses: 6 pushes, its 136-byte frame, then a
callee's return address and stack. -/
def sumcheckLayerStack : Nat := 48 + 136 + 8 + sumcheckCallStack

/-! ## Values -/

/-- A path's digests' words, end to end. -/
def pathWords (path : Array LeanVM.Protocol.Digest) : List UInt64 :=
  path.toList.flatMap (·.toList)

/-- The round polynomial's largest count (`MAX_COUNT`). -/
def maxCount : Nat := 5

section
variable [Labels]

/-! ## `Rows::row` -/

/-- `Rows::row`'s precondition: the `Rows` at RDI, reading the openings at `p`, are `rows`, apart
from the return address at RSP. -/
def RowsRowPre (p : BitVec 64) (rows : Array (Array UInt64)) (m : MachineData) : Prop :=
  StackOk m rowsRowStack ∧ RowsAt m.dmem (reg m .rdi) p rows ∧ NoWrap (reg m .rdi) 32 ∧
    Apart (reg m .rdi) 32 (stackBelow m rowsRowStack) (rowsRowStack + 8)

/-- `Rows::row`'s postcondition: row `j` (RSI) at RAX, word `1 + j · openingWords` of the
openings at `p`, its length in RDX, for `j` below the count. -/
def RowsRowPost (p : BitVec 64) (rows : Array (Array UInt64)) (m m' : MachineData) : Prop :=
  (∀ hj : (reg m .rsi).toNat < rows.size,
      (reg m' .rdx).toNat = rows[(reg m .rsi).toNat].size ∧
        reg m' .rax = off p (8 * (1 + (reg m .rsi).toNat * openingWords)) ∧
        NativeRustcVm.WordsAt m'.dmem (reg m' .rax) rows[(reg m .rsi).toNat].toList) ∧
    m'.dmem = m.dmem ∧ Saved m m'

/-! ## `climb` -/

/-- `climb`'s precondition: `height ≤ 32` (R8); the node `N` (RSI), the `height` digests `P` of
the path (RCX) and the output (RDI) data memory, apart from the stack. -/
def ClimbPre (N : LeanVM.Protocol.Digest) (P : Array LeanVM.Protocol.Digest) (m : MachineData) :
    Prop :=
  let out := reg m .rdi; let node := reg m .rsi; let path := reg m .rcx
  let h := (reg m .r8).toNat
  StackOk m climbStack ∧ RcAt m climbStack ∧ h ≤ wireMaxHeight ∧ P.size = h ∧
    NativeRustcVm.WordsAt m.dmem node N.toList ∧ NativeRustcVm.WordsAt m.dmem path (pathWords P) ∧
    NoWrap node 32 ∧ NoWrap path (32 * h) ∧ Mapped m.dmem out 32 ∧ NoWrap out 32 ∧
    Apart node 32 (stackBelow m climbStack) (climbStack + 8) ∧
    Apart path (32 * h) (stackBelow m climbStack) (climbStack + 8) ∧
    Apart out 32 (stackBelow m climbStack) (climbStack + 8) ∧ Apart out 32 rcAddr 192 ∧
    GotAt m climbStack [(node, 32), (path, 32 * h), (out, 32), (rcAddr, 192)] ["memcpy", "memset"]

/-- `climb`'s postcondition: `climb N q P` at RDI (`q` RDX). -/
def ClimbPost (N : LeanVM.Protocol.Digest) (P : Array LeanVM.Protocol.Digest)
    (m m' : MachineData) : Prop :=
  let out := reg m .rdi
  NativeRustcVm.WordsAt m'.dmem out (climb N (.ofBitVec (reg m .rdx)) P).toList ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange out 32 p ∨
      InRange (stackBelow m climbStack) climbStack p) ∧ Saved m m'

/-! ## `open_phase` -/

/-- `open_phase`'s precondition: the phase `P` at the stack argument (`PhaseAt`), the root `R`
(RSI), the positions `Q` (R8, R9 = `|Q|`); they and the output (RDI) data memory, apart from the
stack; the output apart from the inputs, the positions apart from the phase. -/
def OpenPhasePre (P : Array OpeningW) (R : LeanVM.Protocol.Digest) (Q : Array UInt64)
    (m : MachineData) : Prop :=
  let out := reg m .rdi; let root := reg m .rsi; let pos := reg m .r8
  let n := (reg m .r9).toNat; let ph := stackArg m 0
  StackOk m openPhaseStack ∧ RcAt m openPhaseStack ∧ ArgsOk m 1 ∧ PhaseAt m.dmem ph P ∧
    NativeRustcVm.WordsAt m.dmem root R.toList ∧ Q.size = n ∧
    NativeRustcVm.WordsAt m.dmem pos Q.toList ∧
    Mapped m.dmem ph (8 * phaseWords) ∧ NoWrap ph (8 * phaseWords) ∧ NoWrap root 32 ∧
    NoWrap pos (8 * n) ∧ Mapped m.dmem out 32 ∧ NoWrap out 32 ∧
    Apart ph (8 * phaseWords) (stackBelow m openPhaseStack) (openPhaseStack + 8) ∧
    Apart root 32 (stackBelow m openPhaseStack) (openPhaseStack + 8) ∧
    Apart pos (8 * n) (stackBelow m openPhaseStack) (openPhaseStack + 8) ∧
    Apart out 32 (stackBelow m openPhaseStack) (openPhaseStack + 8) ∧
    Apart out 32 ph (8 * phaseWords) ∧ Apart out 32 root 32 ∧ Apart out 32 pos (8 * n) ∧
    Apart out 32 rcAddr 192 ∧ Apart pos (8 * n) ph (8 * phaseWords) ∧
    GotAt m openPhaseStack
      [(ph, 8 * phaseWords), (root, 32), (pos, 8 * n), (out, 32), (rcAddr, 192)] ["memcpy", "memset"]

/-- `open_phase`'s postcondition: `openPhase R height width Q P` (height RDX, width RCX) at RDI
as an `Option<Rows>` reading the openings at the phase's address + 24. -/
def OpenPhasePost (P : Array OpeningW) (R : LeanVM.Protocol.Digest) (Q : Array UInt64)
    (m m' : MachineData) : Prop :=
  let out := reg m .rdi
  OptRowsAt m'.dmem out (off (stackArg m 0) 24)
      (openPhase R (reg m .rdx).toNat (reg m .rcx).toNat Q P) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange out 32 p ∨
      InRange (stackBelow m openPhaseStack) openPhaseStack p) ∧ Saved m m'

/-! ## `query_openings` -/

/-- `query_openings`'s precondition: the positions `Q` (RCX, R8 = `|Q|`) apart from the stack and
the decoded area, the output (RDI, 32 bytes) apart from them. -/
def QueryOpeningsPre (a : DecArea) (s : TState) (Q : Array UInt64) (m : MachineData) : Prop :=
  let t := reg m .rsi; let out := reg m .rdi; let pos := reg m .rcx
  let n := (reg m .r8).toNat
  StackOk m queryOpeningsStack ∧ RcAt m queryOpeningsStack ∧ TStateAt m.dmem t a s ∧
    TStateOk m t a queryOpeningsStack ∧ Q.size = n ∧ NativeRustcVm.WordsAt m.dmem pos Q.toList ∧
    NoWrap pos (8 * n) ∧
    Apart pos (8 * n) (stackBelow m queryOpeningsStack) (queryOpeningsStack + 8) ∧
    Apart pos (8 * n) a.words (8 * a.len) ∧ OutOk m t a out 32 queryOpeningsStack ∧
    Apart out 32 pos (8 * n) ∧
    GotAt m queryOpeningsStack
      [(t, tstateBytes), (a.words, 8 * a.len), (pos, 8 * n), (out, 32), (rcAddr, 192)] ["memcpy", "memset"]

/-- `query_openings`'s postcondition: `queryOpenings i Q`'s rows (`i` RDX) at RDI, read in the
decoded area's phase `s.phase`. -/
def QueryOpeningsPost (a : DecArea) (s : TState) (Q : Array UInt64) (m m' : MachineData) :
    Prop :=
  let t := reg m .rsi; let out := reg m .rdi
  let r := (queryOpenings (reg m .rdx).toNat Q).run s
  OptRowsAt m'.dmem out (off (a.word (phaseBase a.l s.phase)) 24) (r.map (·.1)) ∧
    NextAt m'.dmem t a r ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange out 32 q ∨ InRange t tstateBytes q ∨
      InRange (stackBelow m queryOpeningsStack) queryOpeningsStack q) ∧ Saved m m'

/-! ## `sumcheck_round_poly` -/

/-- `sumcheck_round_poly`'s precondition: `2 ≤ count ≤ 5` (RSI), the `Option<EW>` `e` at R8
apart from the stack, the message buffer (R9, `maxCount` elements) an output. -/
def RoundPolyPre (a : DecArea) (s : TState) (e : Option EW) (m : MachineData) : Prop :=
  let t := reg m .rdi; let ep := reg m .r8
  StackOk m roundPolyStack ∧ RcAt m roundPolyStack ∧ TStateAt m.dmem t a s ∧
    TStateOk m t a roundPolyStack ∧ 2 ≤ (reg m .rsi).toNat ∧ (reg m .rsi).toNat ≤ maxCount ∧
    OptEWAt m.dmem ep e ∧ NoWrap ep 24 ∧
    Apart ep 24 (stackBelow m roundPolyStack) (roundPolyStack + 8) ∧
    OutOk m t a (reg m .r9) (16 * maxCount) roundPolyStack ∧
    GotAt m roundPolyStack
      [(t, tstateBytes), (a.words, 8 * a.len), (ep, 24), (reg m .r9, 16 * maxCount),
        (rcAddr, 192)] ["memcpy"]

/-- `sumcheck_round_poly`'s postcondition: `sumcheckRoundPoly count claim e` (`claim` RDX, RCX),
AL its `Option<()>`, the polynomial at R9. -/
def RoundPolyPost (a : DecArea) (s : TState) (e : Option EW) (m m' : MachineData) : Prop :=
  let t := reg m .rdi; let msg := reg m .r9
  let r := (sumcheckRoundPoly (reg m .rsi).toNat ⟨.ofBitVec (reg m .rdx), .ofBitVec (reg m .rcx)⟩
    e).run s
  OkAl m' r.isSome ∧
    (∀ xs s', r = some (xs, s') → NativeRustcVm.EWsAt m'.dmem msg xs.toList) ∧
    NextAt m'.dmem t a r ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange msg (16 * maxCount) q ∨ InRange t tstateBytes q ∨
      InRange (stackBelow m roundPolyStack) roundPolyStack q) ∧ Saved m m'

/-! ## `sumcheck` -/

/-- What a sumcheck leaves: the final claim as the `Option<EW>` at `out`, the challenges in the
slots at `slots`, the `TState` at `t` the next state. -/
def SumcheckOut (d : Mem 64) (t : BitVec 64) (a : DecArea) (out slots : BitVec 64)
    (r : Option ((Array EW × EW) × TState)) : Prop :=
  OptEWAt d out (r.map (·.1.2)) ∧
    (∀ xs c s', r = some ((xs, c), s') → NativeRustcVm.EWsAt d slots xs.toList) ∧ NextAt d t a r

/-- A sumcheck's precondition, `N` bytes of stack: `2 ≤ count ≤ 5`, the output (`Option<EW>`,
24 bytes, at `out`) and the `n` slots at `slots` outputs, apart from each other. -/
def SumcheckOk (a : DecArea) (s : TState) (m : MachineData) (t out slots : BitVec 64)
    (count n N : Nat) : Prop :=
  StackOk m N ∧ RcAt m N ∧ TStateAt m.dmem t a s ∧ TStateOk m t a N ∧
    2 ≤ count ∧ count ≤ maxCount ∧ OutOk m t a out 24 N ∧ OutOk m t a slots (16 * n) N ∧
    Apart out 24 slots (16 * n) ∧
    GotAt m N [(t, tstateBytes), (a.words, 8 * a.len), (out, 24), (slots, 16 * n),
      (rcAddr, 192)] ["memcpy"]

/-- The claim a sumcheck starts from: RDX, RCX. -/
def claimArg (m : MachineData) : EW := ⟨.ofBitVec (reg m .rdx), .ofBitVec (reg m .rcx)⟩

/-- `sumcheck::<sumcheck_plain's closure>`'s precondition: the slots' count `n` the stack
argument. -/
def SumcheckPlainPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  ArgsOk m 1 ∧
    SumcheckOk a s m (reg m .rsi) (reg m .rdi) (reg m .r9) (reg m .r8).toNat
      (stackArg m 0).toNat sumcheckPlainStack

/-- `sumcheck::<sumcheck_plain's closure>`'s postcondition: `sumcheckPlain claim count n`. -/
def SumcheckPlainPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let t := reg m .rsi; let out := reg m .rdi; let slots := reg m .r9
  let n := (stackArg m 0).toNat
  SumcheckOut m'.dmem t a out slots ((sumcheckPlain (claimArg m) (reg m .r8).toNat n).run s) ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange out 24 q ∨ InRange slots (16 * n) q ∨
      InRange t tstateBytes q ∨ InRange (stackBelow m sumcheckPlainStack) sumcheckPlainStack q) ∧
    Saved m m'

/-- `sumcheck::<gkr_step's closure>`'s precondition: the point `pt` (R9, `|pt|` the stack argument
`0`) apart from the stack, the `TState` and the slots (the stack argument `1`); the slots' count
`n` the stack argument `2`; the `TState` and the slots apart from the arguments. -/
def SumcheckGkrPre (a : DecArea) (s : TState) (pt : Array EW) (n : Nat) (m : MachineData) :
    Prop :=
  let t := reg m .rsi; let p := reg m .r9; let slots := stackArg m 1
  ArgsOk m 3 ∧
    SumcheckOk a s m t (reg m .rdi) slots (reg m .r8).toNat n sumcheckGkrStack ∧
    pt.size = (stackArg m 0).toNat ∧ NativeRustcVm.EWsAt m.dmem p pt.toList ∧
    NoWrap p (16 * pt.size) ∧
    Apart p (16 * pt.size) (stackBelow m sumcheckGkrStack) (sumcheckGkrStack + 8) ∧
    Apart p (16 * pt.size) t tstateBytes ∧ Apart p (16 * pt.size) slots (16 * n) ∧
    (stackArg m 2).toNat = n ∧ Apart t tstateBytes (rspOf m + 8#64) 24 ∧
    Apart slots (16 * n) (rspOf m + 8#64) 24

/-- `sumcheck::<gkr_step's closure>`'s postcondition: `n` rounds, round `i`'s equality factor
`pt[i]?`. -/
def SumcheckGkrPost (a : DecArea) (s : TState) (pt : Array EW) (n : Nat) (m m' : MachineData) :
    Prop :=
  let t := reg m .rsi; let out := reg m .rdi; let slots := stackArg m 1
  SumcheckOut m'.dmem t a out slots
      ((sumcheckFn (claimArg m) (reg m .r8).toNat (pt[·]?) n).run s) ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange out 24 q ∨ InRange slots (16 * n) q ∨
      InRange t tstateBytes q ∨ InRange (stackBelow m sumcheckGkrStack) sumcheckGkrStack q) ∧
    Saved m m'

/-- `sumcheck::<verify_layer's closure>`'s precondition: count `3`; the point `pt` (R8, R9 =
`|pt|`) apart from the stack, the `TState` and the `n` slots (the stack arguments `0`, `1`); the
`TState` and the slots apart from the arguments. -/
def SumcheckLayerPre (a : DecArea) (s : TState) (pt : Array EW) (m : MachineData) : Prop :=
  let t := reg m .rsi; let p := reg m .r8; let slots := stackArg m 0
  let n := (stackArg m 1).toNat
  ArgsOk m 2 ∧ SumcheckOk a s m t (reg m .rdi) slots 3 n sumcheckLayerStack ∧
    pt.size = (reg m .r9).toNat ∧ NativeRustcVm.EWsAt m.dmem p pt.toList ∧
    NoWrap p (16 * pt.size) ∧
    Apart p (16 * pt.size) (stackBelow m sumcheckLayerStack) (sumcheckLayerStack + 8) ∧
    Apart p (16 * pt.size) t tstateBytes ∧ Apart p (16 * pt.size) slots (16 * n) ∧
    Apart t tstateBytes (rspOf m + 8#64) 16 ∧ Apart slots (16 * n) (rspOf m + 8#64) 16

/-- `sumcheck::<verify_layer's closure>`'s postcondition: `n` rounds of count `3`, round `i`'s
equality factor `pt[i]?`. -/
def SumcheckLayerPost (a : DecArea) (s : TState) (pt : Array EW) (m m' : MachineData) : Prop :=
  let t := reg m .rsi; let out := reg m .rdi; let slots := stackArg m 0
  let n := (stackArg m 1).toNat
  SumcheckOut m'.dmem t a out slots ((sumcheckFn (claimArg m) 3 (pt[·]?) n).run s) ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange out 24 q ∨ InRange slots (16 * n) q ∨
      InRange t tstateBytes q ∨ InRange (stackBelow m sumcheckLayerStack) sumcheckLayerStack q) ∧
    Saved m m'

end

end

end NativeRustcVmX64
