module

public import NativeRustcVmArm.Code.Vm.BasisWEval.Names
public import NativeRustcVmArm.Code.Vm.EachRowOfFinalLevel.Names
public import NativeRustcVmArm.Code.Vm.EachRowOfNextLevel.Names
public import NativeRustcVmArm.Code.Vm.FinalLevel.Names
public import NativeRustcVmArm.Code.Vm.FoldRound.Names
public import NativeRustcVmArm.Code.Vm.FoldRounds.Names
public import NativeRustcVmArm.Code.Vm.FoldRow.Names
public import NativeRustcVmArm.Code.Vm.GlueLevel.Names
public import NativeRustcVmArm.Code.Vm.GluedEval.Names
public import NativeRustcVmArm.Code.Vm.InducedWeight.Names
public import NativeRustcVmArm.Code.Vm.LanesOf.Names
public import NativeRustcVmArm.Code.Vm.NextLevel.Names
public import NativeRustcVmArm.Code.Vm.NovelEval.Names
public import NativeRustcVmArm.Code.Vm.QueryBits.Names
public import NativeRustcVmArm.Code.Vm.SampleQueries.Names
public import NativeRustcVmArm.Code.Vm.SubspaceAtTable.Names
public import NativeRustcVmArm.Code.Vm.SubspaceTable.Names
public import NativeRustcVmArm.Code.Vm.VerifyStackedOpening.Names
public import NativeRustcVmArm.Code.Vm.WhirLevels.Names
public import NativeRustcVmArm.Spec.Arrays
public import NativeRustcVmArm.Spec.Transcript
public import NativeRustcVmArm.Spec.Sumcheck
public import NativeRustcVmArm.Spec.Ring
public import NativeRustcVmArm.Rodata
public import NativeRustcVm.Whir.Model
public import NativeRustcVm.Whir.Basis

/-!
# The contracts of `whir.rs`'s functions on AArch64

Each function uses the stack below SP (`<fn>Stack` bytes, its callees' included; `StackOk` in its
precondition) and returns with the callee-saved registers and SP kept (`Saved`), no byte changed
outside its outputs and that stack. An input area is data memory, not wrapping and apart from that
stack (`WhirIn`); an output also apart from the inputs. Values are the model's
(`NativeVm/Model/Whir.lean`) through the representations of `NativeRustcVm.Whir` (`WhirStateAt`,
`WhirAt`, `GluedAt`, `LevelAt`, `BasisWAt`, …). rustc's `sret` pointer is X0, the arguments after
it. `Option<()>` is X0 (`okWord`), `Option<EW>` at a pointer `OptEWAt`.

- `query_bits(c, shift, depth)` (`c` X0, X1; X2, X3): `queryBits c shift depth` in X0.
- `sample_queries(t, depth, count, out)` (X0 to X3; `count ≤ 230`): `sampleQueries depth count`,
  the positions in the `Buf<u64, 230>` at `out`. Reads `PER_CHALLENGE` (`RodataAt`).
- `lanes_of(index, row, out)` (X0; X1, X2; X3): `Some(n)` (X0 = 1, X1 = `n`) with `lanesOf index
  row`'s `n` lanes at `out` when they fit its 64, else `None` (X0 = 0).
- `subspace_table(out, μ)` (X0, X1): `Some(subspaceTable μ)` (a `Buf<(u64, u64), 31>`) for
  `μ ≤ 30`, else `None`.
- `subspace_at_table(out, table, x)` (X0; X1, X2 (`≤ 31` pairs, rustc's range of its callers);
  X3): `subspaceAtTable table x` in the `Buf<u64, 31>` at `out`.
- `novel_eval(out, coefficients, what)` (X0; X1, X2; X3, X4): `Some(novelEval coefficients what)`
  for at most 64 coefficients, else `None`.
- `fold_row(values, n, x, rounds)` (X0, X1, X2; X3, X4): `foldRow` of the first `min n 64` lanes
  at `values` in X0, X1 (the lanes overwritten).
- `induced_weight(out, μ, queries, weights, point)` (X0, X1; X2, X3; X4, X5; X6, X7):
  `Some(inducedWeight μ queries weights point)` for `μ ≤ 30`, else `None`.
- `glued_eval(out, g, x)` (X0, X1; X2, X3): `Some(g.weight.eval x)`.
- `glue_level(s, λ, μ, oodPoint, oodValue, queries, weights, batched)` (X0; X1, X2; X3; X4, X5;
  X6, X7; the last three, two words each, at SP): the state at `s` becomes `glueLevel …` (room for
  two glued claims, the buffers' caps respected).
- `fold_round(out, t, s)` (X0, X1, X2; fewer than 30 `α`s): `foldRound s`, the
  `Option<FoldRoundW>` at `out`.
- `fold_rounds(t, n, s, rounds)` (X0 to X3; `n ≤ 6`, room for `n` more `α`s): `foldRounds n s`,
  the rounds in the `Buf<FoldRoundW, 6>` at `rounds`.
- `each_row::<final_level's closure>(index, queries, rows, μ, rounds, folded)` (X0; X1, X2; X3;
  X4; X5, X6; the closure's `folded` slice X7 and the word at SP; `μ ≤ 30`, at most 64 folded
  scalars): `finalOk`.
- `each_row::<next_level's closure>(index, queries, rows, μ, rounds, &env)` (X0; X1, X2; X3; X4;
  X5, X6; X7 the closure: `&μ`, `high` (2 words), `&mut batched`, `queryWeights` (2 words);
  `μ ≤ 30`, `batched` `0`): `batched` becomes `batchedOf`.
- `BasisW::eval(out, basis, point)` (X0, X1; X2, X3; at most 64 coordinates): `Some(b.eval
  point)`.
- `final_level(t, index, level, μ, laneFolds, basis, w)` (X0 to X6): `finalLevelM`.
- `next_level(t, index, level, next.fold, next.logInvRate, μ, w)` (X0 to X6; rustc passes `next`
  by its two used fields): `nextLevelM`, the glued state at `w`.
- `whir_levels(t, logN, laneFolds, basis, levels, w)` (X0 to X3; X4, X5; X6; `levels` a ladder,
  the state at `w` fresh): `whirLevels logN laneFolds basis 0 levels`.
-/

namespace NativeRustcVmArm

open NativeRustcArm NativeVm NativeVm.Model LeanVM.Parameters NativeRustcVm.Transcript
open NativeRustcVm.Whir NativeRustcVm.Sumcheck
open NativeRustcVm (ewsOf wordsOf wordOf BufEWAt BufWordsAt EWAt)

@[expose] public section

/-! ## Symbols -/


/-! ## Stacks -/

/-- `query_bits` uses no stack. -/
def queryBitsStack : Nat := 0
/-- The stack `sample_queries` uses: its 112-byte frame and `squeeze`'s. -/
def sampleQueriesStack : Nat := 112 + squeezeStack
/-- `lanes_of` uses no stack. -/
def lanesOfStack : Nat := 0
/-- The stack `subspace_table` uses: its 864-byte frame and `kinv`'s (above `kmul`'s). -/
def subspaceTableStack : Nat := 864 + kinvStack
/-- The stack `subspace_at_table` uses: its 336-byte frame and `kmul`'s. -/
def subspaceAtTableStack : Nat := 336 + kmulStack
/-- The stack `novel_eval` uses: its 1120-byte frame and `kmul`'s. -/
def novelEvalStack : Nat := 1120 + kmulStack
/-- The stack `fold_row` uses: its 128-byte frame and `EW::mul`'s (above `kmul`'s). -/
def foldRowStack : Nat := 128 + ewMulStack
/-- The stack `induced_weight` uses: its 1200-byte frame and the largest of its callees'. -/
def inducedWeightStack : Nat :=
  1200 + max subspaceTableStack (max subspaceAtTableStack ewMulStack)
/-- The stack `glued_eval` uses: a 16-byte frame around `eq_eval`, or `induced_weight`'s
(a tail call). -/
def gluedEvalStack : Nat := max (16 + eqEvalStack) inducedWeightStack
/-- The stack `glue_level` uses: its 112-byte frame and `EW::mul`'s (`extend` uses none). -/
def glueLevelStack : Nat := 112 + ewMulStack
/-- The stack `fold_round` uses: its 208-byte frame and the largest of its callees'. -/
def foldRoundStack : Nat :=
  208 + max readScalarStack (max grindStack (max squeezeStack ewMulStack))
/-- The stack `fold_rounds` uses: its 160-byte frame and `fold_round`'s. -/
def foldRoundsStack : Nat := 160 + foldRoundStack
/-- The stack `each_row` with `final_level`'s closure uses: its 1952-byte frame and the largest of
its callees'. -/
def eachRowFinalStack : Nat :=
  1952 + max subspaceTableStack (max foldRowStack (max subspaceAtTableStack novelEvalStack))
/-- The stack `each_row` with `next_level`'s closure uses: its 2000-byte frame and the largest of
its callees'. -/
def eachRowNextStack : Nat :=
  2000 + max subspaceTableStack (max foldRowStack (max subspaceAtTableStack
    (max novelEvalStack ewMulStack)))
/-- The stack `BasisW::eval` uses: its 144-byte frame and the largest of its callees'
(`LayoutW::placement` uses none). -/
def basisWEvalStack : Nat :=
  144 + max ewMulStack (max ringClaimWeightStack (max columnWeightStack eqEvalStack))
/-- The stack `final_level` uses: its 2672-byte frame and the largest of its callees'. -/
def finalLevelStack : Nat :=
  2672 + max readScalarsStack (max grindStack (max sampleQueriesStack (max queryOpeningsStack
    (max eachRowFinalStack (max sumcheckPlainStack (max basisWEvalStack (max gluedEvalStack
      (max ewMulStack mleStack))))))))
/-- The stack `next_level` uses: its 8192-byte frame and the largest of its callees'. -/
def nextLevelStack : Nat :=
  8192 + max readCommitmentStack (max readScalarsStack (max grindStack
    (max sampleChallengesStack (max readScalarStack (max sampleQueriesStack (max squeezeStack
      (max powersStack (max queryOpeningsStack (max eachRowNextStack glueLevelStack)))))))))
/-- The stack `whir_levels` uses: its 96-byte frame and the largest of its callees'. -/
def whirLevelsStack : Nat := 96 + max foldRoundsStack (max nextLevelStack finalLevelStack)
/-- The stack `verify_stacked_opening` uses: its 512-byte frame and the largest of its callees'
(`ladder` uses none, `ladderStack`). -/
def verifyStackedOpeningStack : Nat :=
  512 + max squeezeStack (max ewMulStack (max powersStack whirLevelsStack))

/-! ## Arguments -/

/-- An input of `n` bytes at `a`: data memory, not wrapping, apart from the `N` bytes below SP. -/
def WhirIn (m : MachineData) (a : BitVec 64) (n N : Nat) : Prop :=
  Readable m a n ∧ OffStack m a n N

/-- Word `i` of the stack arguments: the `i`th word from SP. -/
def whirStackArg (m : MachineData) (i : Nat) : UInt64 :=
  wordOf m.dmem (m.regs.SP.toBitVec + BitVec.ofNat 64 (8 * i))

/-- The `n` words from `a`, as an array. -/
def wordSlice (m : MachineData) (a : BitVec 64) (n : Nat) : Array UInt64 :=
  (wordsOf m.dmem a n).toArray

/-- The `n` elements of `E` from `a`, as an array. -/
def ewSlice (m : MachineData) (a : BitVec 64) (n : Nat) : Array EW := (ewsOf m.dmem a n).toArray

/-- Memory changes only in the `s` bytes below SP and the regions `rs`. -/
def ChangesIn (m m' : MachineData) (s : Nat) (rs : List NativeRustcVm.Region) : Prop :=
  SameOutside m.dmem m'.dmem (fun p ↦ NativeRustcVm.InAny rs p ∨ InRange (stackBelow m s) s p)

/-! ## `query_bits` -/

/-- `query_bits`'s precondition. -/
def QueryBitsPre (_ : MachineData) : Prop := True

/-- `query_bits`'s postcondition. -/
def QueryBitsPost (m m' : MachineData) : Prop :=
  m'.regs.X0 = queryBits ⟨m.regs.X0, m.regs.X1⟩ m.regs.X2.toNat m.regs.X3.toNat ∧
    ChangesIn m m' queryBitsStack [] ∧ Saved m m'

/-! ## `lanes_of` -/

/-- `lanes_of`'s precondition: the row (X1, X2 words) and the 64 lanes at X3, apart. -/
def LanesOfPre (m : MachineData) : Prop :=
  WhirIn m m.regs.X1.toBitVec (8 * m.regs.X2.toNat) 0 ∧ WhirIn m m.regs.X3.toBitVec lanesBytes 0 ∧
    Apart m.regs.X3.toBitVec lanesBytes m.regs.X1.toBitVec (8 * m.regs.X2.toNat)

/-- `lanes_of`'s postcondition. -/
def LanesOfPost (m m' : MachineData) : Prop :=
  let lanes := lanesOf m.regs.X0.toNat (wordSlice m m.regs.X1.toBitVec m.regs.X2.toNat)
  (if lanes.size ≤ laneCap then
      m'.regs.X0 = 1 ∧ m'.regs.X1.toNat = lanes.size ∧
        NativeRustcVm.EWsAt m'.dmem m.regs.X3.toBitVec lanes.toList
    else m'.regs.X0 = 0) ∧
    ChangesIn m m' lanesOfStack [⟨m.regs.X3.toBitVec, lanesBytes⟩] ∧ Saved m m'

/-! ## The subspace polynomials -/

/-- `subspace_table`'s precondition: the `Option<Buf<(u64, u64), 31>>` at X0. -/
def SubspaceTablePre (m : MachineData) : Prop :=
  StackOk m subspaceTableStack ∧ WhirIn m m.regs.X0.toBitVec (8 + tableBytes) subspaceTableStack

/-- `subspace_table`'s postcondition: tag word `1` and the table for `μ ≤ 30`, else `0`. -/
def SubspaceTablePost (m m' : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec
  (if m.regs.X1.toNat ≤ stackCap then
      NativeRustcVm.WordAt m'.dmem o 1 ∧
        BufPairsAt m'.dmem (off o 8) rootCap (subspaceTable m.regs.X1.toNat).toList
    else NativeRustcVm.WordAt m'.dmem o 0) ∧
    ChangesIn m m' subspaceTableStack [⟨o, 8 + tableBytes⟩] ∧ Saved m m'

/-- `subspace_at_table`'s precondition: at most `31` pairs at X1 (X2), the `Buf<u64, 31>` at X0
apart from them. -/
def SubspaceAtTablePre (m : MachineData) : Prop :=
  StackOk m subspaceAtTableStack ∧ m.regs.X2.toNat ≤ rootCap ∧
    WhirIn m m.regs.X1.toBitVec (16 * m.regs.X2.toNat) subspaceAtTableStack ∧
    WhirIn m m.regs.X0.toBitVec whatBytes subspaceAtTableStack ∧
    Apart m.regs.X0.toBitVec whatBytes m.regs.X1.toBitVec (16 * m.regs.X2.toNat)

/-- `subspace_at_table`'s postcondition. -/
def SubspaceAtTablePost (m m' : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec
  BufWordsAt m'.dmem o rootCap (subspaceAtTable
      (pairsOf m.dmem m.regs.X1.toBitVec m.regs.X2.toNat).toArray m.regs.X3).toList ∧
    ChangesIn m m' subspaceAtTableStack [⟨o, whatBytes⟩] ∧ Saved m m'

/-- `novel_eval`'s precondition: the coefficients (X1, X2), the `What`s (X3, X4 words), the
`Option<EW>` at X0. -/
def NovelEvalPre (m : MachineData) : Prop :=
  StackOk m novelEvalStack ∧ SliceOk m m.regs.X1 m.regs.X2 novelEvalStack ∧
    WhirIn m m.regs.X3.toBitVec (8 * m.regs.X4.toNat) novelEvalStack ∧
    WhirIn m m.regs.X0.toBitVec 24 novelEvalStack

/-- `novel_eval`'s postcondition. -/
def NovelEvalPost (m m' : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec
  OptEWAt m'.dmem o (if m.regs.X2.toNat ≤ laneCap then
      some (novelEval (slice m m.regs.X1 m.regs.X2)
        (wordSlice m m.regs.X3.toBitVec m.regs.X4.toNat))
    else none) ∧
    ChangesIn m m' novelEvalStack [⟨o, 24⟩] ∧ Saved m m'

/-! ## Folding -/

/-- `fold_row`'s precondition: the 64 lanes at X0, the rounds (X3, X4, at most 6: rustc unrolled
the rounds' loop for its callers' `Buf<FoldRoundW, 6>`) apart from them. -/
def FoldRowPre (m : MachineData) : Prop :=
  StackOk m foldRowStack ∧ WhirIn m m.regs.X0.toBitVec lanesBytes foldRowStack ∧
    WhirIn m m.regs.X3.toBitVec (roundBytes * m.regs.X4.toNat) foldRowStack ∧
    Apart m.regs.X0.toBitVec lanesBytes m.regs.X3.toBitVec (roundBytes * m.regs.X4.toNat) ∧
    m.regs.X4.toNat ≤ roundCap

/-- `fold_row`'s postcondition. -/
def FoldRowPost (m m' : MachineData) : Prop :=
  ewRet m' = foldRow (ewSlice m m.regs.X0.toBitVec (min m.regs.X1.toNat laneCap)) m.regs.X2
      (roundsOf m.dmem m.regs.X3.toBitVec m.regs.X4.toNat).toArray ∧
    ChangesIn m m' foldRowStack [⟨m.regs.X0.toBitVec, lanesBytes⟩] ∧ Saved m m'

/-! ## Glued claims -/

/-- `induced_weight`'s precondition: the queries (X2, X3 words), their weights (X4, X5), the point
(X6, X7), the `Option<EW>` at X0. -/
def InducedWeightPre (m : MachineData) : Prop :=
  StackOk m inducedWeightStack ∧
    WhirIn m m.regs.X2.toBitVec (8 * m.regs.X3.toNat) inducedWeightStack ∧
    SliceOk m m.regs.X4 m.regs.X5 inducedWeightStack ∧
    SliceOk m m.regs.X6 m.regs.X7 inducedWeightStack ∧
    WhirIn m m.regs.X0.toBitVec 24 inducedWeightStack

/-- `induced_weight`'s postcondition. -/
def InducedWeightPost (m m' : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec
  OptEWAt m'.dmem o (if m.regs.X1.toNat ≤ stackCap then
      some (inducedWeight m.regs.X1.toNat (wordSlice m m.regs.X2.toBitVec m.regs.X3.toNat)
        (slice m m.regs.X4 m.regs.X5) (slice m m.regs.X6 m.regs.X7))
    else none) ∧
    ChangesIn m m' inducedWeightStack [⟨o, 24⟩] ∧ Saved m m'

/-- `glued_eval`'s precondition: the glued claim `g` at X1, the point (X2, X3), the `Option<EW>` at
X0. -/
def GluedEvalPre (g : GluedClaimW) (m : MachineData) : Prop :=
  StackOk m gluedEvalStack ∧ GluedAt m.dmem m.regs.X1.toBitVec g ∧
    WhirIn m m.regs.X1.toBitVec gluedBytes gluedEvalStack ∧
    SliceOk m m.regs.X2 m.regs.X3 gluedEvalStack ∧ WhirIn m m.regs.X0.toBitVec 24 gluedEvalStack

/-- `glued_eval`'s postcondition. -/
def GluedEvalPost (g : GluedClaimW) (m m' : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec
  OptEWAt m'.dmem o (some (g.weight.eval (slice m m.regs.X2 m.regs.X3))) ∧
    ChangesIn m m' gluedEvalStack [⟨o, 24⟩] ∧ Saved m m'

/-- `glue_level`'s stack arguments: the queries, their weights, the batched value. -/
def glueArgs (m : MachineData) : Array UInt64 × Array EW × EW :=
  (wordSlice m (whirStackArg m 0).toBitVec (whirStackArg m 1).toNat,
    slice m (whirStackArg m 2) (whirStackArg m 3), ⟨whirStackArg m 4, whirStackArg m 5⟩)

/-- `glue_level`'s precondition: the state `s` at X0, room for two glued claims; `μ ≤ 30`
(X3), the out-of-domain point (X4, X5) at most 30, the queries and weights (at SP) at most `230`
each, the six argument words above SP; the inputs apart from the state. -/
def GlueLevelPre (s : WhirStateW) (m : MachineData) : Prop :=
  let p := m.regs.X0.toBitVec
  let qa := (whirStackArg m 0).toBitVec; let qn := (whirStackArg m 1).toNat
  let wa := (whirStackArg m 2).toBitVec; let wn := (whirStackArg m 3).toNat
  StackOk m glueLevelStack ∧ WhirStateAt m.dmem p s ∧ s.glued.size + 2 ≤ gluedCap ∧
    m.regs.X3.toNat ≤ stackCap ∧ m.regs.X5.toNat ≤ stackCap ∧ qn ≤ queryCap ∧ wn ≤ queryCap ∧
    Readable m m.regs.SP.toBitVec 48 ∧ WhirIn m p stateBytes glueLevelStack ∧
    SliceOk m m.regs.X4 m.regs.X5 glueLevelStack ∧ WhirIn m qa (8 * qn) glueLevelStack ∧
    WhirIn m wa (16 * wn) glueLevelStack ∧
    Apart p stateBytes m.regs.SP.toBitVec 48 ∧
    Apart p stateBytes m.regs.X4.toBitVec (16 * m.regs.X5.toNat) ∧
    Apart p stateBytes qa (8 * qn) ∧ Apart p stateBytes wa (16 * wn)

/-- `glue_level`'s postcondition. -/
def GlueLevelPost (s : WhirStateW) (m m' : MachineData) : Prop :=
  let p := m.regs.X0.toBitVec
  m'.regs.X0 = 1 ∧
    WhirStateAt m'.dmem p (glueLevel s ⟨m.regs.X1, m.regs.X2⟩ m.regs.X3.toNat
      (slice m m.regs.X4 m.regs.X5) ⟨m.regs.X6, m.regs.X7⟩ (glueArgs m).1 (glueArgs m).2.1
      (glueArgs m).2.2) ∧
    ChangesIn m m' glueLevelStack [⟨p, stateBytes⟩] ∧ Saved m m'

section
variable [Labels]

/-! ## The transcript's areas -/

/-- An area of `n` bytes at `o` the function writes beside the `TState` at `t`: `OutOk`, and apart
from the read-only data. -/
def WhirOut (m : MachineData) (t : BitVec 64) (a : DecArea) (o : BitVec 64) (n N : Nat) : Prop :=
  OutOk m t a o n N ∧ NativeRustcVm.RodataApart rodataAddr o n

/-- The `TState` at `t` reading the area `a`, for a function using `N` bytes of stack: `TStateOk`,
the `TState` apart from the read-only data, the data at their labels. -/
def WhirT (m : MachineData) (t : BitVec 64) (a : DecArea) (N : Nat) : Prop :=
  StackOk m N ∧ RcAt m N ∧ RodataAt m N ∧ TStateOk m t a N ∧
    NativeRustcVm.RodataApart rodataAddr t tstateBytes

/-! ## `sample_queries` -/

/-- `sample_queries`'s precondition: the `TState` at X0, at most `230` queries (X2), the
`Buf<u64, 230>` at X3. -/
def SampleQueriesPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec
  WhirT m t a sampleQueriesStack ∧ TStateAt m.dmem t a s ∧ m.regs.X2.toNat ≤ queryCap ∧
    WhirOut m t a m.regs.X3.toBitVec queryBufBytes sampleQueriesStack

/-- `sample_queries`'s postcondition. -/
def SampleQueriesPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let o := m.regs.X3.toBitVec
  m'.regs.X0 = 1 ∧
    (∃ qs s', (sampleQueries m.regs.X1.toNat m.regs.X2.toNat).run s = some (qs, s') ∧
      BufWordsAt m'.dmem o queryCap qs.toList ∧ TStateAt m'.dmem t a s') ∧
    ChangesIn m m' sampleQueriesStack [⟨o, queryBufBytes⟩, ⟨t, tstateBytes⟩] ∧ Saved m m'

/-! ## Fold rounds -/

/-- `fold_round`'s precondition: the `TState` at X1, the state `w` at X2 (fewer than 30 `α`s), the
`Option<FoldRoundW>` (40 bytes) at X0, apart. -/
def FoldRoundPre (a : DecArea) (s : TState) (w : WhirStateW) (m : MachineData) : Prop :=
  let t := m.regs.X1.toBitVec; let p := m.regs.X2.toBitVec; let o := m.regs.X0.toBitVec
  WhirT m t a foldRoundStack ∧ TStateAt m.dmem t a s ∧ WhirStateAt m.dmem p w ∧
    w.alphas.size < stackCap ∧ WhirOut m t a p stateBytes foldRoundStack ∧
    WhirOut m t a o 40 foldRoundStack ∧ Apart o 40 p stateBytes

/-- `fold_round`'s postcondition: tag word `0`, or `1`, `α` and `β`, the state `foldRound`'s. -/
def FoldRoundPost (a : DecArea) (s : TState) (w : WhirStateW) (m m' : MachineData) : Prop :=
  let t := m.regs.X1.toBitVec; let p := m.regs.X2.toBitVec; let o := m.regs.X0.toBitVec
  (match (foldRound w).run s with
    | none => NativeRustcVm.WordAt m'.dmem o 0
    | some ((w', r), s') => NativeRustcVm.WordAt m'.dmem o 1 ∧
        NativeRustcVm.EWsAt m'.dmem (off o 8) [r.alpha, r.beta] ∧
        WhirStateAt m'.dmem p w' ∧ TStateAt m'.dmem t a s') ∧
    ChangesIn m m' foldRoundStack [⟨o, 40⟩, ⟨p, stateBytes⟩, ⟨t, tstateBytes⟩] ∧ Saved m m'

/-- `fold_rounds`'s precondition: the `TState` at X0, `n ≤ 6` (X1), the state `w` at X2 with room
for `n` more `α`s, the `Buf<FoldRoundW, 6>` at X3, apart. -/
def FoldRoundsPre (a : DecArea) (s : TState) (w : WhirStateW) (m : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let p := m.regs.X2.toBitVec; let r := m.regs.X3.toBitVec
  WhirT m t a foldRoundsStack ∧ TStateAt m.dmem t a s ∧ WhirStateAt m.dmem p w ∧
    m.regs.X1.toNat ≤ roundCap ∧ w.alphas.size + m.regs.X1.toNat ≤ stackCap ∧
    WhirOut m t a p stateBytes foldRoundsStack ∧
    WhirOut m t a r (8 + roundBytes * roundCap) foldRoundsStack ∧
    Apart r (8 + roundBytes * roundCap) p stateBytes

/-- `fold_rounds`'s postcondition. -/
def FoldRoundsPost (a : DecArea) (s : TState) (w : WhirStateW) (m m' : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let p := m.regs.X2.toBitVec; let r := m.regs.X3.toBitVec
  let res := (foldRounds m.regs.X1.toNat w).run s
  m'.regs.X0 = okWord res.isSome ∧
    (∀ w' rs s', res = some ((w', rs), s') →
      WhirStateAt m'.dmem p w' ∧ BufRoundsAt m'.dmem r rs.toList ∧ TStateAt m'.dmem t a s') ∧
    ChangesIn m m' foldRoundsStack
      [⟨r, 8 + roundBytes * roundCap⟩, ⟨p, stateBytes⟩, ⟨t, tstateBytes⟩] ∧ Saved m m'

end

/-! ## `each_row` -/

/-- `each_row`'s common precondition (`N` bytes of stack): the queries (X1, X2 words), the rows
at X3 (`RowsAt`, reading the openings at `op`), `μ ≤ 30` (X4), the rounds (X5, X6, at most 6). -/
def EachRowIn (rows : Array (Array UInt64)) (op : BitVec 64) (N : Nat) (m : MachineData) : Prop :=
  StackOk m N ∧ RowsAt m.dmem m.regs.X3.toBitVec op rows ∧ WhirIn m m.regs.X3.toBitVec 32 N ∧
    WhirIn m op (8 * openingsWords) N ∧
    WhirIn m m.regs.X1.toBitVec (8 * m.regs.X2.toNat) N ∧ m.regs.X4.toNat ≤ stackCap ∧
    m.regs.X6.toNat ≤ roundCap ∧ WhirIn m m.regs.X5.toBitVec (roundBytes * m.regs.X6.toNat) N

/-- The queries, the rounds `each_row` reads. -/
def eachRowArgs (m : MachineData) : Array UInt64 × Array FoldRoundW :=
  (wordSlice m m.regs.X1.toBitVec m.regs.X2.toNat,
    (roundsOf m.dmem m.regs.X5.toBitVec m.regs.X6.toNat).toArray)

/-- `each_row::<final_level's closure>`'s precondition: the folded scalars (X7, the word at SP),
at most 64. -/
def EachRowFinalPre (rows : Array (Array UInt64)) (op : BitVec 64) (m : MachineData) : Prop :=
  EachRowIn rows op eachRowFinalStack m ∧ Readable m m.regs.SP.toBitVec 8 ∧
    (whirStackArg m 0).toNat ≤ laneCap ∧ SliceOk m m.regs.X7 (whirStackArg m 0) eachRowFinalStack

/-- `each_row::<final_level's closure>`'s postcondition: `finalOk`. -/
def EachRowFinalPost (rows : Array (Array UInt64)) (m m' : MachineData) : Prop :=
  m'.regs.X0 = okWord (finalOk m.regs.X0.toNat m.regs.X4.toNat (eachRowArgs m).2
      (slice m m.regs.X7 (whirStackArg m 0)) (eachRowArgs m).1 rows) ∧
    ChangesIn m m' eachRowFinalStack [] ∧ Saved m m'

/-- `next_level`'s closure at X7 (48 bytes): `&μ`, `high` (address, length), `&mut batched`,
the query weights (address, length). -/
def nextEnv (m : MachineData) (i : Nat) : UInt64 :=
  wordOf m.dmem (m.regs.X7.toBitVec + BitVec.ofNat 64 (8 * i))

/-- `each_row::<next_level's closure>`'s precondition: the closure at X7, its `μ` the one in X4,
`high` (at most 64), the query weights, the batched value `0` at `&mut batched`, apart from the
inputs. -/
def EachRowNextPre (rows : Array (Array UInt64)) (op : BitVec 64) (m : MachineData) : Prop :=
  let N := eachRowNextStack; let b := (nextEnv m 3).toBitVec
  EachRowIn rows op N m ∧ WhirIn m m.regs.X7.toBitVec 48 N ∧
    WhirIn m (nextEnv m 0).toBitVec 8 N ∧ wordOf m.dmem (nextEnv m 0).toBitVec = m.regs.X4 ∧
    (nextEnv m 2).toNat ≤ laneCap ∧ SliceOk m (nextEnv m 1) (nextEnv m 2) N ∧
    SliceOk m (nextEnv m 4) (nextEnv m 5) N ∧ WhirIn m b 16 N ∧ EWAt m.dmem b 0 ∧
    Apart b 16 m.regs.X7.toBitVec 48 ∧ Apart b 16 (nextEnv m 0).toBitVec 8 ∧
    Apart b 16 m.regs.X3.toBitVec 32 ∧ Apart b 16 op (8 * openingsWords) ∧
    Apart b 16 m.regs.X1.toBitVec (8 * m.regs.X2.toNat) ∧
    Apart b 16 m.regs.X5.toBitVec (roundBytes * m.regs.X6.toNat) ∧
    Apart b 16 (nextEnv m 1).toBitVec (16 * (nextEnv m 2).toNat) ∧
    Apart b 16 (nextEnv m 4).toBitVec (16 * (nextEnv m 5).toNat)

/-- `each_row::<next_level's closure>`'s postcondition: `batched` becomes `batchedOf`. -/
def EachRowNextPost (rows : Array (Array UInt64)) (m m' : MachineData) : Prop :=
  let b := (nextEnv m 3).toBitVec
  m'.regs.X0 = 1 ∧
    EWAt m'.dmem b (batchedOf m.regs.X0.toNat m.regs.X4.toNat (eachRowArgs m).2
      (slice m (nextEnv m 1) (nextEnv m 2)) (eachRowArgs m).1 rows
      (slice m (nextEnv m 4) (nextEnv m 5))) ∧
    ChangesIn m m' eachRowNextStack [⟨b, 16⟩] ∧ Saved m m'

/-! ## `BasisW::eval` -/

/-- The basis's areas, readable and apart from the `N` bytes of stack, and apart from `o`'s `n`
bytes. -/
def BasisIn (m : MachineData) (p : BitVec 64) (ba : BasisAddrs) (N : Nat) (o : BitVec 64)
    (n : Nat) : Prop :=
  WhirIn m p basisBytes N ∧ Apart p basisBytes o n ∧
    ∀ r ∈ ba.regions, WhirIn m r.addr r.size N ∧ Apart r.addr r.size o n

/-- The `BasisW` at `p` and its areas pairwise apart. -/
def BasisApart (p : BitVec 64) (ba : BasisAddrs) : Prop :=
  (⟨p, basisBytes⟩ :: ba.regions).Pairwise fun r r' ↦ Apart r.addr r.size r'.addr r'.size

/-- `BasisW::eval`'s precondition: the basis `b` at X1 (its areas apart), the point (X2, X3, at
most 64), the `Option<EW>` at X0. -/
def BasisWEvalPre (ba : BasisAddrs) (b : BasisW) (m : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec
  StackOk m basisWEvalStack ∧ BasisWAt m.dmem m.regs.X1.toBitVec ba b ∧
    BasisIn m m.regs.X1.toBitVec ba basisWEvalStack o 24 ∧ m.regs.X3.toNat ≤ 64 ∧
    SliceOk m m.regs.X2 m.regs.X3 basisWEvalStack ∧ WhirIn m o 24 basisWEvalStack ∧
    BasisApart m.regs.X1.toBitVec ba

/-- `BasisW::eval`'s postcondition. -/
def BasisWEvalPost (b : BasisW) (m m' : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec
  OptEWAt m'.dmem o (some (b.eval (slice m m.regs.X2 m.regs.X3))) ∧
    ChangesIn m m' basisWEvalStack [⟨o, 24⟩] ∧ Saved m m'

section
variable [Labels]

/-! ## The levels -/

/-- `final_level`'s precondition: the `TState` at X0, the level at X2, `μ` (X3) with `2^μ` plus
the level's fold at most 64 and room for `μ` more `α`s, at most `230` queries, the basis `b` at
X5, the phase-7 state (`w`, the level's `rounds`) at X6; the inputs apart from the outputs. -/
def FinalLevelPre (a : DecArea) (s : TState) (level : Whir.Level) (ba : BasisAddrs) (b : BasisW)
    (w : WhirStateW) (rounds : Array FoldRoundW) (m : MachineData) : Prop :=
  let N := finalLevelStack; let t := m.regs.X0.toBitVec; let p := m.regs.X6.toBitVec
  let mu := m.regs.X3.toNat
  WhirT m t a N ∧ TStateAt m.dmem t a s ∧ WhirAt m.dmem p w rounds ∧
    LevelAt m.dmem m.regs.X2.toBitVec level ∧ BasisWAt m.dmem m.regs.X5.toBitVec ba b ∧
    mu < 64 ∧ 2 ^ mu + level.fold ≤ laneCap ∧ w.alphas.size + mu ≤ stackCap ∧
    level.logInvRate < 64 ∧ level.queries ≤ queryCap ∧
    WhirOut m t a p whirBytes N ∧ WhirIn m m.regs.X2.toBitVec levelBytes N ∧
    Apart m.regs.X2.toBitVec levelBytes p whirBytes ∧
    Apart m.regs.X2.toBitVec levelBytes t tstateBytes ∧
    BasisIn m m.regs.X5.toBitVec ba N p whirBytes ∧ BasisIn m m.regs.X5.toBitVec ba N t tstateBytes ∧
    BasisApart m.regs.X5.toBitVec ba

/-- `final_level`'s postcondition: `finalLevelM`. -/
def FinalLevelPost (a : DecArea) (s : TState) (level : Whir.Level) (b : BasisW) (w : WhirStateW)
    (rounds : Array FoldRoundW) (m m' : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let p := m.regs.X6.toBitVec
  let r := (finalLevelM m.regs.X1.toNat level m.regs.X3.toNat m.regs.X4.toNat b w rounds).run s
  m'.regs.X0 = okWord r.isSome ∧ NextAt m'.dmem t a r ∧
    ChangesIn m m' finalLevelStack [⟨p, whirBytes⟩, ⟨t, tstateBytes⟩] ∧ Saved m m'

/-- `next_level`'s precondition: the `TState` at X0 (fewer than 8 roots), the level at X2 (at most
6 folds, at most `230` queries), the next level's fold (X3, below 63) and rate exponent (X4, below
64), `μ ≤ 30` (X5), the phase-7 state (`w`, room for two glued claims; the level's `rounds`) at
X6; the level apart from the outputs. -/
def NextLevelPre (a : DecArea) (s : TState) (level : Whir.Level) (w : WhirStateW)
    (rounds : Array FoldRoundW) (m : MachineData) : Prop :=
  let N := nextLevelStack; let t := m.regs.X0.toBitVec; let p := m.regs.X6.toBitVec
  WhirT m t a N ∧ TStateAt m.dmem t a s ∧ s.roots.size < maxRoots ∧ WhirAt m.dmem p w rounds ∧
    LevelAt m.dmem m.regs.X2.toBitVec level ∧ level.fold ≤ roundCap ∧
    level.logInvRate < 64 ∧ level.queries ≤ queryCap ∧ m.regs.X3.toNat < 63 ∧
    m.regs.X4.toNat < 64 ∧ m.regs.X5.toNat ≤ stackCap ∧ w.glued.size + 2 ≤ gluedCap ∧
    WhirOut m t a p whirBytes N ∧ WhirIn m m.regs.X2.toBitVec levelBytes N ∧
    Apart m.regs.X2.toBitVec levelBytes p whirBytes ∧
    Apart m.regs.X2.toBitVec levelBytes t tstateBytes

/-- `next_level`'s postcondition: `nextLevelM` (the next level's query count unused), the glued
state at X6, the rounds kept. -/
def NextLevelPost (a : DecArea) (s : TState) (level : Whir.Level) (w : WhirStateW)
    (rounds : Array FoldRoundW) (m m' : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let p := m.regs.X6.toBitVec
  let r := (nextLevelM m.regs.X1.toNat level ⟨m.regs.X3.toNat, m.regs.X4.toNat, 0⟩
    m.regs.X5.toNat w rounds).run s
  m'.regs.X0 = okWord r.isSome ∧ NextAt m'.dmem t a r ∧
    (∀ w' s', r = some (w', s') → WhirAt m'.dmem p w' rounds) ∧
    ChangesIn m m' nextLevelStack [⟨p, whirBytes⟩, ⟨t, tstateBytes⟩] ∧ Saved m m'

/-- `whir_levels`'s precondition: the `TState` at X0 (room for a root per level), `logN` (X1)
with the levels (X4, X5) its ladder at some rate, the basis `b` at X3, a fresh state of claim
`claim` at X6; the inputs apart from the outputs. -/
def WhirLevelsPre (a : DecArea) (s : TState) (levels : List Whir.Level) (ba : BasisAddrs)
    (b : BasisW) (claim : EW) (m : MachineData) : Prop :=
  let N := whirLevelsStack; let t := m.regs.X0.toBitVec; let p := m.regs.X6.toBitVec
  let lv := m.regs.X4.toBitVec
  WhirT m t a N ∧ TStateAt m.dmem t a s ∧ s.roots.size + levels.length ≤ maxRoots ∧
    (∃ rate, Whir.ladder m.regs.X1.toNat rate = some levels) ∧
    levels.length = m.regs.X5.toNat ∧ LevelsAt m.dmem lv levels ∧
    BasisWAt m.dmem m.regs.X3.toBitVec ba b ∧
    WhirStateAt m.dmem p ⟨claim, #[], #[]⟩ ∧ WhirOut m t a p whirBytes N ∧
    WhirIn m lv (levelBytes * levels.length) N ∧ Apart lv (levelBytes * levels.length) p whirBytes ∧
    Apart lv (levelBytes * levels.length) t tstateBytes ∧
    BasisIn m m.regs.X3.toBitVec ba N p whirBytes ∧ BasisIn m m.regs.X3.toBitVec ba N t tstateBytes ∧
    BasisApart m.regs.X3.toBitVec ba

/-- `whir_levels`'s postcondition: `whirLevels logN laneFolds b 0 levels`. -/
def WhirLevelsPost (a : DecArea) (s : TState) (levels : List Whir.Level) (b : BasisW) (claim : EW)
    (m m' : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let p := m.regs.X6.toBitVec
  let r := (whirLevels m.regs.X1.toNat m.regs.X2.toNat b 0 levels ⟨claim, #[], #[]⟩).run s
  m'.regs.X0 = okWord r.isSome ∧ NextAt m'.dmem t a r ∧
    ChangesIn m m' whirLevelsStack [⟨p, whirBytes⟩, ⟨t, tstateBytes⟩] ∧ Saved m m'

/-! ## `verify_stacked_opening` -/

/-- `verify_stacked_opening`'s inputs (`layout`, `ring`, `keccak`, `claims`, `ood`, X1 and X3 to
X6) as a `BasisAddrs` without scales. -/
def vsoInputs (m : MachineData) : List NativeRustcVm.Region :=
  (BasisAddrs.regions ⟨0, 0, m.regs.X1.toBitVec, m.regs.X3.toBitVec, m.regs.X4.toBitVec,
    m.regs.X5.toBitVec, m.regs.X6.toBitVec⟩).tail

/-- `verify_stacked_opening`'s precondition: the `TState` at X0 (at most two roots read), the
layout at X1, the ring switch's output at X3, the Keccak output at X4, the column claims at X5, the
out-of-domain claim `⟨.eq z, value⟩` at X6, the scales' `Buf<EW, 162>` at X7, the `WhirW` at the
word at SP; the inputs apart from the outputs and from each other, the outputs apart, the word at
SP apart from the `TState` and the scales. -/
def VerifyStackedOpeningPre (a : DecArea) (s : TState) (layout : LayoutW) (target : EW)
    (coefficients point slices : Array EW) (cs : Array ColumnClaimW) (z : Array EW) (value : EW)
    (m : MachineData) : Prop :=
  let N := verifyStackedOpeningStack; let t := m.regs.X0.toBitVec
  let sc := m.regs.X7.toBitVec; let p := (whirStackArg m 0).toBitVec
  WhirT m t a N ∧ TStateAt m.dmem t a s ∧ s.roots.size ≤ 2 ∧
    NativeRustcVm.Layout.LayoutWAt m.dmem m.regs.X1.toBitVec layout ∧
    NativeRustcVm.Ring.RingWAt m.dmem m.regs.X3.toBitVec target coefficients ∧
    NativeRustcVm.KeccakGkr.KeccakOutAt m.dmem m.regs.X4.toBitVec point slices ∧
    NativeRustcVm.Layout.ClaimsWAt m.dmem m.regs.X5.toBitVec cs ∧
    NativeRustcVm.Layout.EqClaimAt m.dmem m.regs.X6.toBitVec z value ∧
    Readable m m.regs.SP.toBitVec 8 ∧ Apart m.regs.SP.toBitVec 8 t tstateBytes ∧
    Apart m.regs.SP.toBitVec 8 sc scalesBytes ∧ WhirOut m t a p whirBytes N ∧
    WhirOut m t a sc scalesBytes N ∧ Apart p whirBytes sc scalesBytes ∧
    (∀ r ∈ vsoInputs m, WhirIn m r.addr r.size N ∧ Apart r.addr r.size t tstateBytes ∧
      Apart r.addr r.size p whirBytes ∧ Apart r.addr r.size sc scalesBytes) ∧
    (vsoInputs m).Pairwise fun r r' ↦ Apart r.addr r.size r'.addr r'.size

/-- `verify_stacked_opening`'s postcondition: `verifyStackedOpening` of the stack's log-size, the
rate exponent (X2) and the stack claims. -/
def VerifyStackedOpeningPost (a : DecArea) (s : TState) (layout : LayoutW) (target : EW)
    (coefficients point : Array EW) (cs : Array ColumnClaimW) (z : Array EW) (value : EW)
    (m m' : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let sc := m.regs.X7.toBitVec; let p := (whirStackArg m 0).toBitVec
  let r := (verifyStackedOpening layout.stackLog m.regs.X2.toNat
    (stackClaims layout target point coefficients cs z value)).run s
  m'.regs.X0 = okWord r.isSome ∧ NextAt m'.dmem t a r ∧
    ChangesIn m m' verifyStackedOpeningStack
      [⟨p, whirBytes⟩, ⟨sc, scalesBytes⟩, ⟨t, tstateBytes⟩] ∧ Saved m m'

end

end

end NativeRustcVmArm
