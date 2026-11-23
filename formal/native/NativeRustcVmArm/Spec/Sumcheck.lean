module

public import NativeRustcVmArm.Code.Vm.Climb.Names
public import NativeRustcVmArm.Code.Vm.OpenPhase.Names
public import NativeRustcVmArm.Code.Vm.RowsRow.Names
public import NativeRustcVmArm.Code.Vm.SumcheckOfGkrStep.Names
public import NativeRustcVmArm.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmArm.Code.Vm.SumcheckOfVerifyLayer.Names
public import NativeRustcVmArm.Code.Vm.TStateQueryOpenings.Names
public import NativeRustcVmArm.Code.Vm.TStateSumcheckRoundPoly.Names
public import NativeRustcVmArm.Spec.Transcript
public import NativeRustcVmArm.Spec.Arrays
public import NativeRustcVm.Sumcheck.Rows
public import NativeRustcVm.Sumcheck.Model

/-!
# The contracts of `transcript.rs`'s openings and sumcheck functions on AArch64

Each function uses the stack below SP (`<fn>Stack` bytes, its callees' included; `StackOk` in its
precondition) and returns with the callee-saved registers and SP kept, no byte changed outside its
outputs and that stack (`stackBelow`). Those that hash or touch the transcript read the round
constants (`RcAt`). A digest and a slice of `u64` are their words end to end
(`NativeRustcVm.WordsAt`), a slice of `E` its elements (`NativeRustcVm.EWsAt`). The transcript's
functions take the `TState` at `t` representing the model's `s` with the decoded area `a`
(`TStateAt`) and leave it representing the next state (`NextAt`); on the model's `none` they say
nothing more of it than the frame. Results are the model's (`NativeVm.Model`):

- `Rows::row(rows, j)` (X0, X1): row `j < count` of the rows at `rows` (`RowsAt`), its address in
  X0 and its word count in X1.
- `climb(out, node, q, path, height)` (X0 to X4; rustc fixed the path's slice to its
  `4 · wireMaxHeight` words): the 4 words at `out` become `climb node q path`, the path the
  `height ≤ 32` digests at `path`.
- `open_phase(out, root, height, width, positions, n, phase)` (X0 to X6; the phase's slice fixed
  to its `phaseWords` words): the `Option<Rows>` at `out` becomes `openPhase root height width
  positions ph` of the phase `ph` at `phase` (`PhaseAt`), its rows read at `phase + 24`.
- `TState::query_openings(out, t, i, positions, n)` (X0 to X4): `queryOpenings i positions`, the
  `Option<Rows>` at `out`, the rows read in the decoded area.
- `TState::sumcheck_round_poly(t, count, claim, eq, msg)` (X0, X1, `claim` X2, X3, `&eq` X4,
  `msg` X5; `2 ≤ count ≤ 5`, rustc dropped the Rust's test for its callers' counts):
  `sumcheckRoundPoly count claim eq`, the round polynomial's `count` coefficients at `msg`.
- `TState::sumcheck(out, t, claim, count, equality, slots)` with `sumcheck_plain`'s closure
  (X0, X1, `claim` X2, X3, `count` X4, slots X5, X6): `sumcheckPlain claim count n`, the
  challenges in the `n` slots, the final claim the `Option<EW>` at `out`.
- the same with `gkr_step`'s closure `|i| point.get(i)` (`point` X5, X6, slots X7 and the stack
  argument at SP): `sumcheckFn claim count (point[·]?) n` (`sumcheck claim count (point.map
  some)` when `n = |point|`, `sumcheckFn_getElem?`).
- the same with `verify_layer`'s closure `|i| old.get(i)` and `count = 3` (rustc dropped the
  argument; `old` X4, X5, slots X6, X7).
-/

namespace NativeRustcVmArm

open NativeRustcArm NativeVm NativeVm.Model LeanVM.Protocol.Compile NativeRustcVm.Transcript
open NativeRustcVm.Sumcheck

@[expose] public section

/-! ## Symbols -/


/-! ## Stacks -/

/-- `Rows::row` uses no stack. -/
def rowsRowStack : Nat := 0
/-- The stack `climb` uses: its 144-byte frame and `hash_pair`'s. -/
def climbStack : Nat := 144 + hashPairStack
/-- The stack `open_phase` uses: its 176-byte frame and the larger of `keccak256_words`'s and
`climb`'s. -/
def openPhaseStack : Nat := 176 + max keccak256WordsStack climbStack
/-- The stack `query_openings` uses: its 96-byte frame and the larger of `Decoded::phase`'s and
`open_phase`'s. -/
def queryOpeningsStack : Nat := 96 + max phaseStack openPhaseStack
/-- The stack `sumcheck_round_poly` uses: its 112-byte frame and the largest of its callees'. -/
def roundPolyStack : Nat :=
  112 + max (max readScalarStack readScalarsStack)
    (max (max sumEStack bitLengthStack) (max grindStack ewMulStack))
/-- The largest stack of the sumcheck loop's callees. -/
def sumcheckCallStack : Nat := max roundPolyStack (max squeezeStack polyEvalStack)
/-- The stack `sumcheck` with `sumcheck_plain`'s closure uses: its 160-byte frame and its
callees'. -/
def sumcheckPlainStack : Nat := 160 + sumcheckCallStack
/-- The stack `sumcheck` with `gkr_step`'s closure uses: its 192-byte frame and its callees'. -/
def sumcheckGkrStack : Nat := 192 + sumcheckCallStack
/-- The stack `sumcheck` with `verify_layer`'s closure uses: its 176-byte frame and its
callees'. -/
def sumcheckLayerStack : Nat := 176 + sumcheckCallStack

/-! ## Values -/

/-- A path's digests' words, end to end. -/
def pathWords (path : Array LeanVM.Protocol.Digest) : List UInt64 :=
  path.toList.flatMap (·.toList)

/-- The round polynomial's largest count (`MAX_COUNT`). -/
def maxCount : Nat := 5

section
variable [Labels]

/-! ## `Rows::row` -/

/-- `Rows::row`'s precondition: the `Rows` at X0, reading the openings at `p`, are `rows`. -/
def RowsRowPre (p : BitVec 64) (rows : Array (Array UInt64)) (m : MachineData) : Prop :=
  RowsAt m.dmem m.regs.X0.toBitVec p rows ∧ NoWrap m.regs.X0.toBitVec 32

/-- `Rows::row`'s postcondition: row `j` (X1) at X0, word `1 + j · openingWords` of the openings
at `p`, its length in X1, for `j` below the count. -/
def RowsRowPost (p : BitVec 64) (rows : Array (Array UInt64)) (m m' : MachineData) : Prop :=
  (∀ hj : m.regs.X1.toNat < rows.size,
      m'.regs.X1.toNat = rows[m.regs.X1.toNat].size ∧
        m'.regs.X0.toBitVec = off p (8 * (1 + m.regs.X1.toNat * openingWords)) ∧
        NativeRustcVm.WordsAt m'.dmem m'.regs.X0.toBitVec rows[m.regs.X1.toNat].toList) ∧
    m'.dmem = m.dmem ∧ Saved m m'

/-! ## `climb` -/

/-- `climb`'s precondition: `height ≤ 32`; the node `N` (X1), the `height` digests `P` of the path
(X3) and the output (X0) data memory, apart from the stack. -/
def ClimbPre (N : LeanVM.Protocol.Digest) (P : Array LeanVM.Protocol.Digest) (m : MachineData) :
    Prop :=
  let out := m.regs.X0.toBitVec; let node := m.regs.X1.toBitVec; let path := m.regs.X3.toBitVec
  let h := m.regs.X4.toNat
  StackOk m climbStack ∧ RcAt m climbStack ∧ h ≤ wireMaxHeight ∧ P.size = h ∧
    NativeRustcVm.WordsAt m.dmem node N.toList ∧ NativeRustcVm.WordsAt m.dmem path (pathWords P) ∧
    NoWrap node 32 ∧ NoWrap path (32 * h) ∧ Mapped m.dmem out 32 ∧ NoWrap out 32 ∧
    Apart node 32 (stackBelow m climbStack) climbStack ∧
    Apart path (32 * h) (stackBelow m climbStack) climbStack ∧
    Apart out 32 (stackBelow m climbStack) climbStack ∧ Apart out 32 rcAddr 192

/-- `climb`'s postcondition: `climb N q P` at X0. -/
def ClimbPost (N : LeanVM.Protocol.Digest) (P : Array LeanVM.Protocol.Digest)
    (m m' : MachineData) : Prop :=
  let out := m.regs.X0.toBitVec
  NativeRustcVm.WordsAt m'.dmem out (climb N m.regs.X2 P).toList ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange out 32 p ∨
      InRange (stackBelow m climbStack) climbStack p) ∧ Saved m m'

/-! ## `open_phase` -/

/-- `open_phase`'s precondition: the phase `P` at X6 (`PhaseAt`), the root `R` (X1), the
positions `Q` (X4, X5 = `|Q|`); they and the output (X0) data memory, apart from the stack; the
output apart from the inputs, the positions apart from the phase. -/
def OpenPhasePre (P : Array OpeningW) (R : LeanVM.Protocol.Digest) (Q : Array UInt64)
    (m : MachineData) : Prop :=
  let out := m.regs.X0.toBitVec; let root := m.regs.X1.toBitVec; let pos := m.regs.X4.toBitVec
  let n := m.regs.X5.toNat; let ph := m.regs.X6.toBitVec
  StackOk m openPhaseStack ∧ RcAt m openPhaseStack ∧ PhaseAt m.dmem ph P ∧
    NativeRustcVm.WordsAt m.dmem root R.toList ∧ Q.size = n ∧
    NativeRustcVm.WordsAt m.dmem pos Q.toList ∧
    Mapped m.dmem ph (8 * phaseWords) ∧ NoWrap ph (8 * phaseWords) ∧ NoWrap root 32 ∧
    NoWrap pos (8 * n) ∧ Mapped m.dmem out 32 ∧ NoWrap out 32 ∧
    Apart ph (8 * phaseWords) (stackBelow m openPhaseStack) openPhaseStack ∧
    Apart root 32 (stackBelow m openPhaseStack) openPhaseStack ∧
    Apart pos (8 * n) (stackBelow m openPhaseStack) openPhaseStack ∧
    Apart out 32 (stackBelow m openPhaseStack) openPhaseStack ∧
    Apart out 32 ph (8 * phaseWords) ∧ Apart out 32 root 32 ∧ Apart out 32 pos (8 * n) ∧
    Apart out 32 rcAddr 192 ∧ Apart pos (8 * n) ph (8 * phaseWords)

/-- `open_phase`'s postcondition: `openPhase R height width Q P` at X0 as an `Option<Rows>`
reading the openings at X6 + 24. -/
def OpenPhasePost (P : Array OpeningW) (R : LeanVM.Protocol.Digest) (Q : Array UInt64)
    (m m' : MachineData) : Prop :=
  let out := m.regs.X0.toBitVec
  OptRowsAt m'.dmem out (off m.regs.X6.toBitVec 24)
      (openPhase R m.regs.X2.toNat m.regs.X3.toNat Q P) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange out 32 p ∨
      InRange (stackBelow m openPhaseStack) openPhaseStack p) ∧ Saved m m'

/-! ## `query_openings` -/

/-- `query_openings`'s precondition: the positions `Q` (X3, X4 = `|Q|`) apart from the stack and
the decoded area, the output (X0, 32 bytes) apart from them. -/
def QueryOpeningsPre (a : DecArea) (s : TState) (Q : Array UInt64) (m : MachineData) : Prop :=
  let t := m.regs.X1.toBitVec; let out := m.regs.X0.toBitVec; let pos := m.regs.X3.toBitVec
  let n := m.regs.X4.toNat
  StackOk m queryOpeningsStack ∧ RcAt m queryOpeningsStack ∧ TStateAt m.dmem t a s ∧
    TStateOk m t a queryOpeningsStack ∧ Q.size = n ∧ NativeRustcVm.WordsAt m.dmem pos Q.toList ∧
    NoWrap pos (8 * n) ∧ Apart pos (8 * n) (stackBelow m queryOpeningsStack) queryOpeningsStack ∧
    Apart pos (8 * n) a.words (8 * a.len) ∧ OutOk m t a out 32 queryOpeningsStack ∧
    Apart out 32 pos (8 * n)

/-- `query_openings`'s postcondition: `queryOpenings i Q`'s rows at X0, read in the decoded
area's phase `s.phase`. -/
def QueryOpeningsPost (a : DecArea) (s : TState) (Q : Array UInt64) (m m' : MachineData) :
    Prop :=
  let t := m.regs.X1.toBitVec; let out := m.regs.X0.toBitVec
  let r := (queryOpenings m.regs.X2.toNat Q).run s
  OptRowsAt m'.dmem out (off (a.word (phaseBase a.l s.phase)) 24) (r.map (·.1)) ∧
    NextAt m'.dmem t a r ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange out 32 q ∨ InRange t tstateBytes q ∨
      InRange (stackBelow m queryOpeningsStack) queryOpeningsStack q) ∧ Saved m m'

/-! ## `sumcheck_round_poly` -/

/-- `sumcheck_round_poly`'s precondition: `2 ≤ count ≤ 5` (X1), the `Option<EW>` `e` at X4
apart from the stack, the message buffer (X5, `maxCount` elements) an output. -/
def RoundPolyPre (a : DecArea) (s : TState) (e : Option EW) (m : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let ep := m.regs.X4.toBitVec
  StackOk m roundPolyStack ∧ RcAt m roundPolyStack ∧ TStateAt m.dmem t a s ∧
    TStateOk m t a roundPolyStack ∧ 2 ≤ m.regs.X1.toNat ∧ m.regs.X1.toNat ≤ maxCount ∧
    OptEWAt m.dmem ep e ∧ NoWrap ep 24 ∧ Apart ep 24 (stackBelow m roundPolyStack) roundPolyStack ∧
    OutOk m t a m.regs.X5.toBitVec (16 * maxCount) roundPolyStack

/-- `sumcheck_round_poly`'s postcondition: `sumcheckRoundPoly count claim e`, the polynomial at
X5. -/
def RoundPolyPost (a : DecArea) (s : TState) (e : Option EW) (m m' : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let msg := m.regs.X5.toBitVec
  let r := (sumcheckRoundPoly m.regs.X1.toNat ⟨m.regs.X2, m.regs.X3⟩ e).run s
  m'.regs.X0 = okWord r.isSome ∧
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
    Apart out 24 slots (16 * n)

/-- `sumcheck::<sumcheck_plain's closure>`'s precondition. -/
def SumcheckPlainPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  SumcheckOk a s m m.regs.X1.toBitVec m.regs.X0.toBitVec m.regs.X5.toBitVec m.regs.X4.toNat
    m.regs.X6.toNat sumcheckPlainStack

/-- `sumcheck::<sumcheck_plain's closure>`'s postcondition: `sumcheckPlain claim count n`. -/
def SumcheckPlainPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let t := m.regs.X1.toBitVec; let out := m.regs.X0.toBitVec; let slots := m.regs.X5.toBitVec
  let n := m.regs.X6.toNat
  SumcheckOut m'.dmem t a out slots
      ((sumcheckPlain ⟨m.regs.X2, m.regs.X3⟩ m.regs.X4.toNat n).run s) ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange out 24 q ∨ InRange slots (16 * n) q ∨
      InRange t tstateBytes q ∨ InRange (stackBelow m sumcheckPlainStack) sumcheckPlainStack q) ∧
    Saved m m'

/-- `sumcheck::<gkr_step's closure>`'s precondition: the point `pt` (X5, X6 = `|pt|`) apart from
the stack, the `TState` and the slots; the slots' count `n` the word at SP. -/
def SumcheckGkrPre (a : DecArea) (s : TState) (pt : Array EW) (n : Nat) (m : MachineData) :
    Prop :=
  let t := m.regs.X1.toBitVec; let p := m.regs.X5.toBitVec; let slots := m.regs.X7.toBitVec
  let sp := m.regs.SP.toBitVec
  SumcheckOk a s m t m.regs.X0.toBitVec slots m.regs.X4.toNat n sumcheckGkrStack ∧
    pt.size = m.regs.X6.toNat ∧ NativeRustcVm.EWsAt m.dmem p pt.toList ∧ NoWrap p (16 * pt.size) ∧
    Apart p (16 * pt.size) (stackBelow m sumcheckGkrStack) sumcheckGkrStack ∧
    Apart p (16 * pt.size) t tstateBytes ∧ Apart p (16 * pt.size) slots (16 * n) ∧
    n < 2 ^ 64 ∧ NativeRustcVm.WordAt m.dmem sp n.toUInt64 ∧ NoWrap sp 8

/-- `sumcheck::<gkr_step's closure>`'s postcondition: `n` rounds, round `i`'s equality factor
`pt[i]?`. -/
def SumcheckGkrPost (a : DecArea) (s : TState) (pt : Array EW) (n : Nat) (m m' : MachineData) :
    Prop :=
  let t := m.regs.X1.toBitVec; let out := m.regs.X0.toBitVec; let slots := m.regs.X7.toBitVec
  SumcheckOut m'.dmem t a out slots
      ((sumcheckFn ⟨m.regs.X2, m.regs.X3⟩ m.regs.X4.toNat (pt[·]?) n).run s) ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange out 24 q ∨ InRange slots (16 * n) q ∨
      InRange t tstateBytes q ∨ InRange (stackBelow m sumcheckGkrStack) sumcheckGkrStack q) ∧
    Saved m m'

/-- `sumcheck::<verify_layer's closure>`'s precondition: count `3`; the point `pt` (X4, X5 =
`|pt|`) apart from the stack, the `TState` and the `n` slots (X6, X7). -/
def SumcheckLayerPre (a : DecArea) (s : TState) (pt : Array EW) (m : MachineData) : Prop :=
  let t := m.regs.X1.toBitVec; let p := m.regs.X4.toBitVec; let slots := m.regs.X6.toBitVec
  let n := m.regs.X7.toNat
  SumcheckOk a s m t m.regs.X0.toBitVec slots 3 n sumcheckLayerStack ∧
    pt.size = m.regs.X5.toNat ∧ NativeRustcVm.EWsAt m.dmem p pt.toList ∧ NoWrap p (16 * pt.size) ∧
    Apart p (16 * pt.size) (stackBelow m sumcheckLayerStack) sumcheckLayerStack ∧
    Apart p (16 * pt.size) t tstateBytes ∧ Apart p (16 * pt.size) slots (16 * n)

/-- `sumcheck::<verify_layer's closure>`'s postcondition: `n` rounds of count `3`, round `i`'s
equality factor `pt[i]?`. -/
def SumcheckLayerPost (a : DecArea) (s : TState) (pt : Array EW) (m m' : MachineData) : Prop :=
  let t := m.regs.X1.toBitVec; let out := m.regs.X0.toBitVec; let slots := m.regs.X6.toBitVec
  let n := m.regs.X7.toNat
  SumcheckOut m'.dmem t a out slots ((sumcheckFn ⟨m.regs.X2, m.regs.X3⟩ 3 (pt[·]?) n).run s) ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange out 24 q ∨ InRange slots (16 * n) q ∨
      InRange t tstateBytes q ∨ InRange (stackBelow m sumcheckLayerStack) sumcheckLayerStack q) ∧
    Saved m m'

end

end

end NativeRustcVmArm
