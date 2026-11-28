module

public import NativeRustcVmX64.Spec.Arrays
public import NativeRustcVmX64.Spec.Transcript
public import NativeRustcVmX64.Spec.Sumcheck
public import NativeRustcVmX64.Spec.Ring
public import NativeRustcVmX64.Rodata
public import NativeRustcVm.Whir.Model
public import NativeRustcVm.Whir.Basis
public import NativeRustcVmX64.Code.Vm.BasisWEval.Names
public import NativeRustcVmX64.Code.Vm.EachRowOfFinalLevel.Names
public import NativeRustcVmX64.Code.Vm.EachRowOfNextLevel.Names
public import NativeRustcVmX64.Code.Vm.FinalLevel.Names
public import NativeRustcVmX64.Code.Vm.FoldRound.Names
public import NativeRustcVmX64.Code.Vm.FoldRounds.Names
public import NativeRustcVmX64.Code.Vm.FoldRow.Names
public import NativeRustcVmX64.Code.Vm.GlueLevel.Names
public import NativeRustcVmX64.Code.Vm.GluedEval.Names
public import NativeRustcVmX64.Code.Vm.InducedWeight.Names
public import NativeRustcVmX64.Code.Vm.LanesOf.Names
public import NativeRustcVmX64.Code.Vm.NextLevel.Names
public import NativeRustcVmX64.Code.Vm.NovelEval.Names
public import NativeRustcVmX64.Code.Vm.QueryBits.Names
public import NativeRustcVmX64.Code.Vm.SampleQueries.Names
public import NativeRustcVmX64.Code.Vm.SubspaceAtTable.Names
public import NativeRustcVmX64.Code.Vm.SubspaceTable.Names
public import NativeRustcVmX64.Code.Vm.VerifyStackedOpening.Names
public import NativeRustcVmX64.Code.Vm.WhirLevels.Names

/-!
# The contracts of `whir.rs`'s functions on x86-64

The AArch64 contracts (`NativeRustcVmArm.Spec.Whir`) with the System V registers: arguments in
RDI, RSI, RDX, RCX, R8, R9, then on the stack above the return address (`stackArg`, mapped by
`ArgsOk`); rustc's `sret` pointer is RDI, the arguments after it; an `E` result in RAX, RDX
(`ewRet`); an `Option<()>` in AL (`OkAl`); an `Option<usize>` in RAX (tag), RDX; an `Option<EW>`
the 24 bytes at a pointer (`OptEWAt`). Each function uses the stack below RSP (`<fn>Stack` bytes:
its pushes, its frame, the argument words it pushes for a callee, its callees' return addresses and
stacks; `StackOk` also maps its return address at RSP) and returns with the callee-saved registers
kept (and RSP 8 above, `Spec`), no byte changed outside its outputs and that stack. An input area
is data memory, not wrapping and apart from that stack and the return address (`WhirIn`); an
output also apart from the inputs. Values are the model's (`NativeVm/Model/Whir.lean`) through the
representations of `NativeRustcVm.Whir` (`WhirStateAt`, `WhirAt`, `GluedAt`, `LevelAt`,
`BasisWAt`, …). A function re-reading a stack argument after writing an output takes the output
apart from the argument words (x86-64 only: AArch64 passes those arguments in registers or below
SP; every caller's arguments are in its own frame, apart from its outputs).

- `query_bits(c, shift, depth)` (`c` RDI, RSI; RDX, RCX): `queryBits c shift depth` in RAX.
- `sample_queries(t, depth, count, out)` (RDI to RCX; `count ≤ 230`): `sampleQueries depth
  count`, the positions in the `Buf<u64, 230>` at `out`. Reads `PER_CHALLENGE` (`RodataAt`).
- `lanes_of(index, row, out)` (RDI; RSI, RDX; RCX): `Some(n)` (RAX = 1, RDX = `n`) with
  `lanesOf index row`'s `n` lanes at `out` when they fit its 64, else `None` (RAX = 0).
- `subspace_table(out, μ)` (RDI, RSI): `Some(subspaceTable μ)` (a `Buf<(u64, u64), 31>`) for
  `μ ≤ 30`, else `None`.
- `subspace_at_table(out, table, x)` (RDI; RSI, RDX (`≤ 31` pairs, rustc's range of its
  callers); RCX): `subspaceAtTable table x` in the `Buf<u64, 31>` at `out`.
- `novel_eval(out, coefficients, what)` (RDI; RSI, RDX; RCX, R8): `Some(novelEval coefficients
  what)` for at most 64 coefficients, else `None`.
- `fold_row(values, n, x, rounds)` (RDI, RSI, RDX; RCX, R8): `foldRow` of the first `min n 64`
  lanes at `values` in RAX, RDX (the lanes overwritten).
- `induced_weight(out, μ, queries, weights, point)` (RDI, RSI; RDX, RCX; R8, R9; the stack
  arguments `0`, `1`): `Some(inducedWeight μ queries weights point)` for `μ ≤ 30`, else `None`.
- `glued_eval(out, g, x)` (RDI, RSI; RDX, RCX): `Some(g.weight.eval x)`.
- `glue_level(s, λ, μ, oodPoint, oodValue, queries, weights, batched)` (RDI; RSI, RDX; RCX; R8,
  R9; the last four, two words each, the stack arguments `0` to `7`): the state at `s` becomes
  `glueLevel …` (room for two glued claims, the buffers' caps respected).
- `fold_round(out, t, s)` (RDI, RSI, RDX; fewer than 30 `α`s): `foldRound s`, the
  `Option<FoldRoundW>` at `out`.
- `fold_rounds(t, n, s, rounds)` (RDI to RCX; `n ≤ 6`, room for `n` more `α`s): `foldRounds n s`,
  the rounds in the `Buf<FoldRoundW, 6>` at `rounds`.
- `each_row::<final_level's closure>(index, queries, rows, μ, rounds, folded)` (RDI; RSI, RDX;
  RCX; R8; R9 and the stack argument `0`; the closure's `folded` slice the stack arguments `1`,
  `2`; `μ ≤ 30`, at most 64 folded scalars): `finalOk`.
- `each_row::<next_level's closure>(index, queries, rows, μ, rounds, &env)` (RDI; RSI, RDX; RCX;
  R8; R9 and the stack argument `0`; the closure's address the stack argument `1`: `&μ`, `high`
  (2 words), `&mut batched`, `queryWeights` (2 words); `μ ≤ 30`, `batched` `0`): `batched`
  becomes `batchedOf`.
- `BasisW::eval(out, basis, point)` (RDI, RSI; RDX, RCX; at most 64 coordinates): `Some(b.eval
  point)`.
- `final_level(t, index, level, μ, laneFolds, basis, w)` (RDI to R9, `w` the stack argument `0`):
  `finalLevelM`.
- `next_level(t, index, level, next.fold, next.logInvRate, μ, w)` (RDI to R9, `w` the stack
  argument `0`; rustc passes `next` by its two used fields): `nextLevelM`, the glued state at `w`.
- `whir_levels(t, logN, laneFolds, basis, levels, w)` (RDI to RCX; R8, R9; `w` the stack argument
  `0`; `levels` a ladder, the state at `w` fresh): `whirLevels logN laneFolds basis 0 levels`.
- `verify_stacked_opening(t, layout, logInvRate, ring, keccak, claims, ood, scales, w)` (RDI to
  R9, then the stack arguments `0` to `2`): `verifyStackedOpening`.
-/

namespace NativeRustcVmX64

open NativeRustcX64 NativeVm NativeVm.Model LeanVM.Parameters NativeRustcVm.Transcript
open NativeRustcVm.Whir NativeRustcVm.Sumcheck
open NativeRustcVm (ewsOf wordsOf wordOf BufEWAt BufWordsAt EWAt)

@[expose] public section

/-! ## Stacks -/

/-- `query_bits` uses no stack. -/
def queryBitsStack : Nat := 0
/-- The stack `sample_queries` uses: 6 pushes, its 72-byte frame, the return address and stack of
`squeeze` (`query_bits` uses none). -/
def sampleQueriesStack : Nat := 128 + squeezeStack
/-- The stack `lanes_of` uses: its push. -/
def lanesOfStack : Nat := 8
/-- The stack `subspace_table` uses: 6 pushes, its 792-byte frame, the return address and stack of
`kinv` (above `kmul`'s, `memcpy`'s, `memset`'s). -/
def subspaceTableStack : Nat := 848 + kinvStack
/-- The stack `subspace_at_table` uses: 6 pushes, its 280-byte frame, the return address and stack
of `kmul` (above `memcpy`'s, `memset`'s). -/
def subspaceAtTableStack : Nat := 336 + kmulStack
/-- The stack `novel_eval` uses: 6 pushes, its 1048-byte frame, the return address and stack of
`kmul` (above `memset`'s). -/
def novelEvalStack : Nat := 1104 + kmulStack
/-- The stack `fold_row` uses: 6 pushes, its 40-byte frame, the return address and stack of
`EW::mul` (above `kmul`'s). -/
def foldRowStack : Nat := 96 + ewMulStack
/-- The stack `induced_weight` uses: 6 pushes, its 1112-byte frame, the return address and the
largest stack of its callees' (`kmul`'s, `memcpy`'s below). -/
def inducedWeightStack : Nat :=
  1168 + max subspaceTableStack (max subspaceAtTableStack ewMulStack)
/-- The stack `glued_eval` uses: its push and `eq_eval`'s return address and stack, or two more
pushes (`induced_weight`'s stack arguments) and `induced_weight`'s return address and stack. -/
def gluedEvalStack : Nat := max (16 + eqEvalStack) (32 + inducedWeightStack)
/-- The stack `glue_level` uses: 6 pushes, its 40-byte frame, the return address and stack of
`EW::mul` (above the `extend`s'). -/
def glueLevelStack : Nat := 96 + ewMulStack
/-- The stack `fold_round` uses: 6 pushes, its 120-byte frame, the return address and the largest
stack of its callees'. -/
def foldRoundStack : Nat :=
  176 + max readScalarStack (max grindStack (max squeezeStack ewMulStack))
/-- The stack `fold_rounds` uses: 6 pushes, its 104-byte frame, `fold_round`'s return address and
stack. -/
def foldRoundsStack : Nat := 160 + foldRoundStack
/-- The stack `each_row` with `final_level`'s closure uses: 6 pushes, its 1880-byte frame, the
return address and the largest stack of its callees' (`Rows::row`'s, `memcpy`'s below). -/
def eachRowFinalStack : Nat :=
  1936 + max subspaceTableStack (max foldRowStack (max subspaceAtTableStack
    (max novelEvalStack lanesOfStack)))
/-- The stack `each_row` with `next_level`'s closure uses: 6 pushes, its 1928-byte frame, the
return address and the largest stack of its callees' (`Rows::row`'s, `memcpy`'s, `kmul`'s
below). -/
def eachRowNextStack : Nat :=
  1984 + max subspaceTableStack (max foldRowStack (max subspaceAtTableStack
    (max novelEvalStack (max lanesOfStack ewMulStack))))
/-- The stack `BasisW::eval` uses: 6 pushes, its 88-byte frame, two pushed argument words, the
return address and the largest stack of its callees' (`LayoutW::placement` uses none). -/
def basisWEvalStack : Nat :=
  160 + max ewMulStack (max ringClaimWeightStack (max columnWeightStack eqEvalStack))
/-- The stack `final_level` uses: 6 pushes, its 2584-byte frame, at most 32 bytes of pushed
arguments (and alignment), the return address and the largest stack of its callees' (the
`extend`s' below). -/
def finalLevelStack : Nat :=
  2672 + max readScalarsStack (max grindStack (max sampleQueriesStack (max queryOpeningsStack
    (max eachRowFinalStack (max sumcheckPlainStack (max basisWEvalStack (max gluedEvalStack
      (max ewMulStack mleStack))))))))
/-- The stack `next_level` uses: 6 pushes, its 8056-byte frame, at most 64 bytes of pushed
arguments, the return address and the largest stack of its callees' (`memcpy`'s below). -/
def nextLevelStack : Nat :=
  8176 + max readCommitmentStack (max readScalarsStack (max grindStack
    (max sampleChallengesStack (max readScalarStack (max sampleQueriesStack (max squeezeStack
      (max powersStack (max queryOpeningsStack (max eachRowNextStack glueLevelStack)))))))))
/-- The stack `whir_levels` uses: 6 pushes, its 56-byte frame, the return address and the largest
stack of its callees' (`final_level` a tail call). -/
def whirLevelsStack : Nat := 112 + max foldRoundsStack (max nextLevelStack finalLevelStack)
/-- The stack `ladder` uses: 6 pushes and its 24-byte frame (a leaf; its contract is the
layout's). -/
def vsoLadderStack : Nat := 72
/-- The stack `verify_stacked_opening` uses: 6 pushes, its 456-byte frame, the return address and
the largest stack of its callees' (`memcpy`'s below). -/
def verifyStackedOpeningStack : Nat :=
  512 + max squeezeStack (max ewMulStack (max powersStack (max whirLevelsStack vsoLadderStack)))

/-! ## Arguments -/

/-- An input of `n` bytes at `a`: data memory, not wrapping, apart from the `N` bytes below RSP
and the return address. -/
def WhirIn (m : MachineData) (a : BitVec 64) (n N : Nat) : Prop :=
  Readable m a n ∧ OffStack m a n N

/-- The `n` words from `a`, as an array. -/
def wordSlice (m : MachineData) (a : BitVec 64) (n : Nat) : Array UInt64 :=
  (wordsOf m.dmem a n).toArray

/-- The `n` elements of `E` from `a`, as an array. -/
def ewSlice (m : MachineData) (a : BitVec 64) (n : Nat) : Array EW := (ewsOf m.dmem a n).toArray

/-- Memory changes only in the `s` bytes below RSP and the regions `rs`. -/
def ChangesIn (m m' : MachineData) (s : Nat) (rs : List NativeRustcVm.Region) : Prop :=
  SameOutside m.dmem m'.dmem (fun p ↦ NativeRustcVm.InAny rs p ∨ InRange (stackBelow m s) s p)

/-! ## `query_bits` -/

/-- `query_bits`'s precondition: its return address mapped. -/
def QueryBitsPre (m : MachineData) : Prop := StackOk m queryBitsStack

/-- `query_bits`'s postcondition. -/
def QueryBitsPost (m m' : MachineData) : Prop :=
  reg m' .rax =
      (queryBits (ewArg (reg m .rdi) (reg m .rsi)) (reg m .rdx).toNat (reg m .rcx).toNat).toBitVec ∧
    ChangesIn m m' queryBitsStack [] ∧ Saved m m'

/-! ## `lanes_of` -/

/-- `lanes_of`'s precondition: the row (RSI, RDX words) and the 64 lanes at RCX, apart. -/
def LanesOfPre (m : MachineData) : Prop :=
  StackOk m lanesOfStack ∧
    WhirIn m (reg m .rsi) (8 * (reg m .rdx).toNat) lanesOfStack ∧
    WhirIn m (reg m .rcx) lanesBytes lanesOfStack ∧
    Apart (reg m .rcx) lanesBytes (reg m .rsi) (8 * (reg m .rdx).toNat)

/-- `lanes_of`'s postcondition. -/
def LanesOfPost (m m' : MachineData) : Prop :=
  let lanes := lanesOf (reg m .rdi).toNat (wordSlice m (reg m .rsi) (reg m .rdx).toNat)
  (if lanes.size ≤ laneCap then
      reg m' .rax = 1#64 ∧ (reg m' .rdx).toNat = lanes.size ∧
        NativeRustcVm.EWsAt m'.dmem (reg m .rcx) lanes.toList
    else reg m' .rax = 0#64) ∧
    ChangesIn m m' lanesOfStack [⟨reg m .rcx, lanesBytes⟩] ∧ Saved m m'

/-! ## The subspace polynomials -/

/-- `subspace_table`'s precondition: the `Option<Buf<(u64, u64), 31>>` at RDI. -/
def SubspaceTablePre [Labels] (m : MachineData) : Prop :=
  StackOk m subspaceTableStack ∧ WhirIn m (reg m .rdi) (8 + tableBytes) subspaceTableStack ∧
    GotAt m subspaceTableStack [(reg m .rdi, 8 + tableBytes)] ["memcpy", "memset"]

/-- `subspace_table`'s postcondition: tag word `1` and the table for `μ ≤ 30` (RSI), else `0`. -/
def SubspaceTablePost (m m' : MachineData) : Prop :=
  let o := reg m .rdi
  (if (reg m .rsi).toNat ≤ stackCap then
      NativeRustcVm.WordAt m'.dmem o 1 ∧
        BufPairsAt m'.dmem (off o 8) rootCap (subspaceTable (reg m .rsi).toNat).toList
    else NativeRustcVm.WordAt m'.dmem o 0) ∧
    ChangesIn m m' subspaceTableStack [⟨o, 8 + tableBytes⟩] ∧ Saved m m'

/-- `subspace_at_table`'s precondition: at most `31` pairs at RSI (RDX), the `Buf<u64, 31>` at
RDI apart from them. -/
def SubspaceAtTablePre [Labels] (m : MachineData) : Prop :=
  StackOk m subspaceAtTableStack ∧ (reg m .rdx).toNat ≤ rootCap ∧
    WhirIn m (reg m .rsi) (16 * (reg m .rdx).toNat) subspaceAtTableStack ∧
    WhirIn m (reg m .rdi) whatBytes subspaceAtTableStack ∧
    Apart (reg m .rdi) whatBytes (reg m .rsi) (16 * (reg m .rdx).toNat) ∧
    GotAt m subspaceAtTableStack
      [(reg m .rsi, 16 * (reg m .rdx).toNat), (reg m .rdi, whatBytes)] ["memcpy", "memset"]

/-- `subspace_at_table`'s postcondition (`x` RCX). -/
def SubspaceAtTablePost (m m' : MachineData) : Prop :=
  let o := reg m .rdi
  BufWordsAt m'.dmem o rootCap (subspaceAtTable
      (pairsOf m.dmem (reg m .rsi) (reg m .rdx).toNat).toArray (.ofBitVec (reg m .rcx))).toList ∧
    ChangesIn m m' subspaceAtTableStack [⟨o, whatBytes⟩] ∧ Saved m m'

/-- `novel_eval`'s precondition: the coefficients (RSI, RDX), the `What`s (RCX, R8 words), the
`Option<EW>` at RDI. -/
def NovelEvalPre [Labels] (m : MachineData) : Prop :=
  StackOk m novelEvalStack ∧ SliceOk m (reg m .rsi) (reg m .rdx) novelEvalStack ∧
    WhirIn m (reg m .rcx) (8 * (reg m .r8).toNat) novelEvalStack ∧
    WhirIn m (reg m .rdi) 24 novelEvalStack ∧
    GotAt m novelEvalStack [(reg m .rsi, 16 * (reg m .rdx).toNat),
      (reg m .rcx, 8 * (reg m .r8).toNat), (reg m .rdi, 24)] ["memset"]

/-- `novel_eval`'s postcondition. -/
def NovelEvalPost (m m' : MachineData) : Prop :=
  let o := reg m .rdi
  OptEWAt m'.dmem o (if (reg m .rdx).toNat ≤ laneCap then
      some (novelEval (slice m (reg m .rsi) (reg m .rdx))
        (wordSlice m (reg m .rcx) (reg m .r8).toNat))
    else none) ∧
    ChangesIn m m' novelEvalStack [⟨o, 24⟩] ∧ Saved m m'

/-! ## Folding -/

/-- `fold_row`'s precondition: the 64 lanes at RDI, the rounds (RCX, R8, at most 6: rustc unrolled
the rounds' loop for its callers' `Buf<FoldRoundW, 6>`) apart from them. -/
def FoldRowPre (m : MachineData) : Prop :=
  StackOk m foldRowStack ∧ WhirIn m (reg m .rdi) lanesBytes foldRowStack ∧
    WhirIn m (reg m .rcx) (roundBytes * (reg m .r8).toNat) foldRowStack ∧
    Apart (reg m .rdi) lanesBytes (reg m .rcx) (roundBytes * (reg m .r8).toNat) ∧
    (reg m .r8).toNat ≤ roundCap

/-- `fold_row`'s postcondition (`n` RSI, `x` RDX). -/
def FoldRowPost (m m' : MachineData) : Prop :=
  ewRet m' = foldRow (ewSlice m (reg m .rdi) (min (reg m .rsi).toNat laneCap))
      (.ofBitVec (reg m .rdx)) (roundsOf m.dmem (reg m .rcx) (reg m .r8).toNat).toArray ∧
    ChangesIn m m' foldRowStack [⟨reg m .rdi, lanesBytes⟩] ∧ Saved m m'

/-! ## Glued claims -/

/-- `induced_weight`'s precondition: the queries (RDX, RCX words), their weights (R8, R9), the
point (the stack arguments `0`, `1`), the `Option<EW>` at RDI apart from the argument words. -/
def InducedWeightPre [Labels] (m : MachineData) : Prop :=
  let N := inducedWeightStack
  StackOk m N ∧ ArgsOk m 2 ∧ WhirIn m (reg m .rdx) (8 * (reg m .rcx).toNat) N ∧
    SliceOk m (reg m .r8) (reg m .r9) N ∧ SliceOk m (stackArg m 0) (stackArg m 1) N ∧
    WhirIn m (reg m .rdi) 24 N ∧ Apart (reg m .rdi) 24 (rspOf m + 8#64) 16 ∧
    GotAt m N ([(reg m .rdx, 8 * (reg m .rcx).toNat),
      (reg m .r8, 16 * (reg m .r9).toNat), (reg m .rdi, 24), (rspOf m + 8#64, 16)] ++
      if 0 < (stackArg m 1).toNat then [(stackArg m 0, 16 * (stackArg m 1).toNat)] else [])
      ["memcpy", "memset"]

/-- `induced_weight`'s postcondition (`μ` RSI). -/
def InducedWeightPost (m m' : MachineData) : Prop :=
  let o := reg m .rdi
  OptEWAt m'.dmem o (if (reg m .rsi).toNat ≤ stackCap then
      some (inducedWeight (reg m .rsi).toNat (wordSlice m (reg m .rdx) (reg m .rcx).toNat)
        (slice m (reg m .r8) (reg m .r9)) (slice m (stackArg m 0) (stackArg m 1)))
    else none) ∧
    ChangesIn m m' inducedWeightStack [⟨o, 24⟩] ∧ Saved m m'

/-- `glued_eval`'s precondition: the glued claim `g` at RSI, the point (RDX, RCX), the
`Option<EW>` at RDI. An empty point has no bytes to protect from the GOT. -/
def GluedEvalPre [Labels] (g : GluedClaimW) (m : MachineData) : Prop :=
  StackOk m gluedEvalStack ∧ GluedAt m.dmem (reg m .rsi) g ∧
    WhirIn m (reg m .rsi) gluedBytes gluedEvalStack ∧
    SliceOk m (reg m .rdx) (reg m .rcx) gluedEvalStack ∧ WhirIn m (reg m .rdi) 24 gluedEvalStack ∧
    GotAt m gluedEvalStack ([(reg m .rsi, gluedBytes), (reg m .rdi, 24)] ++
      if 0 < (reg m .rcx).toNat then [(reg m .rdx, 16 * (reg m .rcx).toNat)] else [])
      ["memcpy", "memset"]

/-- `glued_eval`'s postcondition. -/
def GluedEvalPost (g : GluedClaimW) (m m' : MachineData) : Prop :=
  let o := reg m .rdi
  OptEWAt m'.dmem o (some (g.weight.eval (slice m (reg m .rdx) (reg m .rcx)))) ∧
    ChangesIn m m' gluedEvalStack [⟨o, 24⟩] ∧ Saved m m'

/-- `glue_level`'s stack arguments past the out-of-domain value: the queries, their weights, the
batched value. -/
def glueArgs (m : MachineData) : Array UInt64 × Array EW × EW :=
  (wordSlice m (stackArg m 2) (stackArg m 3).toNat, slice m (stackArg m 4) (stackArg m 5),
    ewArg (stackArg m 6) (stackArg m 7))

/-- `glue_level`'s precondition: the state `s` at RDI, room for two glued claims; `μ ≤ 30` (RCX),
the out-of-domain point (R8, R9) at most 30, the queries and weights (stack arguments `2` to `5`)
at most `230` each, the eight argument words on the stack; the inputs apart from the state. -/
def GlueLevelPre (s : WhirStateW) (m : MachineData) : Prop :=
  let N := glueLevelStack; let p := reg m .rdi
  let qa := stackArg m 2; let qn := (stackArg m 3).toNat
  let wa := stackArg m 4; let wn := (stackArg m 5).toNat
  StackOk m N ∧ ArgsOk m 8 ∧ WhirStateAt m.dmem p s ∧ s.glued.size + 2 ≤ gluedCap ∧
    (reg m .rcx).toNat ≤ stackCap ∧ (reg m .r9).toNat ≤ stackCap ∧ qn ≤ queryCap ∧
    wn ≤ queryCap ∧ WhirIn m p stateBytes N ∧ SliceOk m (reg m .r8) (reg m .r9) N ∧
    WhirIn m qa (8 * qn) N ∧ WhirIn m wa (16 * wn) N ∧
    Apart p stateBytes (rspOf m + 8#64) 64 ∧
    Apart p stateBytes (reg m .r8) (16 * (reg m .r9).toNat) ∧
    Apart p stateBytes qa (8 * qn) ∧ Apart p stateBytes wa (16 * wn)

/-- `glue_level`'s postcondition (`λ` RSI, RDX; the out-of-domain value the stack arguments `0`,
`1`). -/
def GlueLevelPost (s : WhirStateW) (m m' : MachineData) : Prop :=
  let p := reg m .rdi
  OkAl m' true ∧
    WhirStateAt m'.dmem p (glueLevel s (ewArg (reg m .rsi) (reg m .rdx)) (reg m .rcx).toNat
      (slice m (reg m .r8) (reg m .r9)) (ewArg (stackArg m 0) (stackArg m 1)) (glueArgs m).1
      (glueArgs m).2.1 (glueArgs m).2.2) ∧
    ChangesIn m m' glueLevelStack [⟨p, stateBytes⟩] ∧ Saved m m'

section
variable [Labels]

/-! ## The transcript's areas -/

/-- An area of `n` bytes at `o` the function writes beside the `TState` at `t`: `OutOk`, and apart
from the read-only data. -/
def WhirOut (m : MachineData) (t : BitVec 64) (a : DecArea) (o : BitVec 64) (n N : Nat) : Prop :=
  OutOk m t a o n N ∧ RodataApart o n

/-- The `TState` at `t` reading the area `a`, for a function using `N` bytes of stack: `TStateOk`,
the `TState` apart from the read-only data, the data at their labels. -/
def WhirT (m : MachineData) (t : BitVec 64) (a : DecArea) (N : Nat) : Prop :=
  StackOk m N ∧ RcAt m N ∧ RodataAt m N ∧ TStateOk m t a N ∧ RodataApart t tstateBytes

/-! ## `sample_queries` -/

/-- `sample_queries`'s precondition: the `TState` at RDI, at most `230` queries (RDX), the
`Buf<u64, 230>` at RCX. -/
def SampleQueriesPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let t := reg m .rdi
  WhirT m t a sampleQueriesStack ∧ TStateAt m.dmem t a s ∧ (reg m .rdx).toNat ≤ queryCap ∧
    WhirOut m t a (reg m .rcx) queryBufBytes sampleQueriesStack ∧
    GotAt m sampleQueriesStack
      ([(t, tstateBytes), (a.words, 8 * a.len), (reg m .rcx, queryBufBytes)] ++ rodataAreas)
      ["memcpy"]

/-- `sample_queries`'s postcondition (`depth` RSI). -/
def SampleQueriesPost (a : DecArea) (s : TState) (m m' : MachineData) : Prop :=
  let t := reg m .rdi; let o := reg m .rcx
  OkAl m' true ∧
    (∃ qs s', (sampleQueries (reg m .rsi).toNat (reg m .rdx).toNat).run s = some (qs, s') ∧
      BufWordsAt m'.dmem o queryCap qs.toList ∧ TStateAt m'.dmem t a s') ∧
    ChangesIn m m' sampleQueriesStack [⟨o, queryBufBytes⟩, ⟨t, tstateBytes⟩] ∧ Saved m m'

/-! ## Fold rounds -/

/-- `fold_round`'s precondition: the `TState` at RSI, the state `w` at RDX (fewer than 30 `α`s),
the `Option<FoldRoundW>` (40 bytes) at RDI, apart. -/
def FoldRoundPre (a : DecArea) (s : TState) (w : WhirStateW) (m : MachineData) : Prop :=
  let t := reg m .rsi; let p := reg m .rdx; let o := reg m .rdi
  WhirT m t a foldRoundStack ∧ TStateAt m.dmem t a s ∧ WhirStateAt m.dmem p w ∧
    w.alphas.size < stackCap ∧ WhirOut m t a p stateBytes foldRoundStack ∧
    WhirOut m t a o 40 foldRoundStack ∧ Apart o 40 p stateBytes ∧
    GotAt m foldRoundStack
      ([(t, tstateBytes), (a.words, 8 * a.len), (p, stateBytes), (o, 40)] ++ rodataAreas)
      ["memcpy"]

/-- `fold_round`'s postcondition: tag word `0`, or `1`, `α` and `β`, the state `foldRound`'s. -/
def FoldRoundPost (a : DecArea) (s : TState) (w : WhirStateW) (m m' : MachineData) : Prop :=
  let t := reg m .rsi; let p := reg m .rdx; let o := reg m .rdi
  (match (foldRound w).run s with
    | none => NativeRustcVm.WordAt m'.dmem o 0
    | some ((w', r), s') => NativeRustcVm.WordAt m'.dmem o 1 ∧
        NativeRustcVm.EWsAt m'.dmem (off o 8) [r.alpha, r.beta] ∧
        WhirStateAt m'.dmem p w' ∧ TStateAt m'.dmem t a s') ∧
    ChangesIn m m' foldRoundStack [⟨o, 40⟩, ⟨p, stateBytes⟩, ⟨t, tstateBytes⟩] ∧ Saved m m'

/-- `fold_rounds`'s precondition: the `TState` at RDI, `n ≤ 6` (RSI), the state `w` at RDX with
room for `n` more `α`s, the `Buf<FoldRoundW, 6>` at RCX, apart. -/
def FoldRoundsPre (a : DecArea) (s : TState) (w : WhirStateW) (m : MachineData) : Prop :=
  let t := reg m .rdi; let p := reg m .rdx; let r := reg m .rcx
  WhirT m t a foldRoundsStack ∧ TStateAt m.dmem t a s ∧ WhirStateAt m.dmem p w ∧
    (reg m .rsi).toNat ≤ roundCap ∧ w.alphas.size + (reg m .rsi).toNat ≤ stackCap ∧
    WhirOut m t a p stateBytes foldRoundsStack ∧
    WhirOut m t a r (8 + roundBytes * roundCap) foldRoundsStack ∧
    Apart r (8 + roundBytes * roundCap) p stateBytes ∧
    GotAt m foldRoundsStack ([(t, tstateBytes), (a.words, 8 * a.len), (p, stateBytes),
      (r, 8 + roundBytes * roundCap)] ++ rodataAreas) ["memcpy"]

/-- `fold_rounds`'s postcondition. -/
def FoldRoundsPost (a : DecArea) (s : TState) (w : WhirStateW) (m m' : MachineData) : Prop :=
  let t := reg m .rdi; let p := reg m .rdx; let r := reg m .rcx
  let res := (foldRounds (reg m .rsi).toNat w).run s
  OkAl m' res.isSome ∧
    (∀ w' rs s', res = some ((w', rs), s') →
      WhirStateAt m'.dmem p w' ∧ BufRoundsAt m'.dmem r rs.toList ∧ TStateAt m'.dmem t a s') ∧
    ChangesIn m m' foldRoundsStack
      [⟨r, 8 + roundBytes * roundCap⟩, ⟨p, stateBytes⟩, ⟨t, tstateBytes⟩] ∧ Saved m m'

end

/-! ## `each_row` -/

/-- `each_row`'s common precondition (`N` bytes of stack, `k` argument words on the stack): the
queries (RSI, RDX words), the rows at RCX (`RowsAt`, reading the openings at `op`), `μ ≤ 30` (R8),
the rounds (R9, the stack argument `0`, at most 6). -/
def EachRowIn (rows : Array (Array UInt64)) (op : BitVec 64) (N k : Nat) (m : MachineData) :
    Prop :=
  StackOk m N ∧ ArgsOk m k ∧ RowsAt m.dmem (reg m .rcx) op rows ∧ WhirIn m (reg m .rcx) 32 N ∧
    WhirIn m op (8 * openingsWords) N ∧
    WhirIn m (reg m .rsi) (8 * (reg m .rdx).toNat) N ∧ (reg m .r8).toNat ≤ stackCap ∧
    (stackArg m 0).toNat ≤ roundCap ∧ WhirIn m (reg m .r9) (roundBytes * (stackArg m 0).toNat) N

/-- The queries, the rounds `each_row` reads. -/
def eachRowArgs (m : MachineData) : Array UInt64 × Array FoldRoundW :=
  (wordSlice m (reg m .rsi) (reg m .rdx).toNat,
    (roundsOf m.dmem (reg m .r9) (stackArg m 0).toNat).toArray)

/-- `each_row::<final_level's closure>`'s precondition: the folded scalars (the stack arguments
`1`, `2`), at most 64. -/
def EachRowFinalPre [Labels] (rows : Array (Array UInt64)) (op : BitVec 64) (m : MachineData) : Prop :=
  EachRowIn rows op eachRowFinalStack 3 m ∧ (stackArg m 2).toNat ≤ laneCap ∧
    SliceOk m (stackArg m 1) (stackArg m 2) eachRowFinalStack ∧
    GotAt m eachRowFinalStack [(reg m .rcx, 32), (op, 8 * openingsWords),
      (reg m .rsi, 8 * (reg m .rdx).toNat), (reg m .r9, roundBytes * (stackArg m 0).toNat),
      (stackArg m 1, 16 * (stackArg m 2).toNat), (rspOf m + 8#64, 24)] ["memcpy", "memset"]

/-- `each_row::<final_level's closure>`'s postcondition: `finalOk` (`index` RDI, `μ` R8). -/
def EachRowFinalPost (rows : Array (Array UInt64)) (m m' : MachineData) : Prop :=
  OkAl m' (finalOk (reg m .rdi).toNat (reg m .r8).toNat (eachRowArgs m).2
      (slice m (stackArg m 1) (stackArg m 2)) (eachRowArgs m).1 rows) ∧
    ChangesIn m m' eachRowFinalStack [] ∧ Saved m m'

/-- `next_level`'s closure at the stack argument `1` (48 bytes): `&μ`, `high` (address, length),
`&mut batched`, the query weights (address, length). -/
def nextEnv (m : MachineData) (i : Nat) : BitVec 64 :=
  (wordOf m.dmem (stackArg m 1 + BitVec.ofNat 64 (8 * i))).toBitVec

/-- `each_row::<next_level's closure>`'s precondition: the closure at the stack argument `1`, its
`μ` the one in R8, `high` (at most 64), the query weights, the batched value `0` at `&mut batched`,
apart from the inputs and the argument words. -/
def EachRowNextPre [Labels] (rows : Array (Array UInt64)) (op : BitVec 64) (m : MachineData) : Prop :=
  let N := eachRowNextStack; let b := nextEnv m 3; let env := stackArg m 1
  EachRowIn rows op N 2 m ∧ WhirIn m env 48 N ∧
    WhirIn m (nextEnv m 0) 8 N ∧ wordOf m.dmem (nextEnv m 0) = .ofBitVec (reg m .r8) ∧
    (nextEnv m 2).toNat ≤ laneCap ∧ SliceOk m (nextEnv m 1) (nextEnv m 2) N ∧
    SliceOk m (nextEnv m 4) (nextEnv m 5) N ∧ WhirIn m b 16 N ∧ EWAt m.dmem b 0 ∧
    Apart b 16 (rspOf m + 8#64) 16 ∧
    Apart b 16 env 48 ∧ Apart b 16 (nextEnv m 0) 8 ∧
    Apart b 16 (reg m .rcx) 32 ∧ Apart b 16 op (8 * openingsWords) ∧
    Apart b 16 (reg m .rsi) (8 * (reg m .rdx).toNat) ∧
    Apart b 16 (reg m .r9) (roundBytes * (stackArg m 0).toNat) ∧
    Apart b 16 (nextEnv m 1) (16 * (nextEnv m 2).toNat) ∧
    Apart b 16 (nextEnv m 4) (16 * (nextEnv m 5).toNat) ∧
    GotAt m N [(reg m .rcx, 32), (op, 8 * openingsWords),
      (reg m .rsi, 8 * (reg m .rdx).toNat), (reg m .r9, roundBytes * (stackArg m 0).toNat),
      (env, 48), (nextEnv m 0, 8), (nextEnv m 1, 16 * (nextEnv m 2).toNat),
      (nextEnv m 4, 16 * (nextEnv m 5).toNat), (b, 16), (rspOf m + 8#64, 16)]
      ["memcpy", "memset"]

/-- `each_row::<next_level's closure>`'s postcondition: `batched` becomes `batchedOf`. -/
def EachRowNextPost (rows : Array (Array UInt64)) (m m' : MachineData) : Prop :=
  let b := nextEnv m 3
  OkAl m' true ∧
    EWAt m'.dmem b (batchedOf (reg m .rdi).toNat (reg m .r8).toNat (eachRowArgs m).2
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

/-- `BasisW::eval`'s precondition: the basis `b` at RSI (its areas apart), the point (RDX, RCX, at
most 64), the `Option<EW>` at RDI. -/
def BasisWEvalPre (ba : BasisAddrs) (b : BasisW) (m : MachineData) : Prop :=
  let o := reg m .rdi
  StackOk m basisWEvalStack ∧ BasisWAt m.dmem (reg m .rsi) ba b ∧
    BasisIn m (reg m .rsi) ba basisWEvalStack o 24 ∧ (reg m .rcx).toNat ≤ 64 ∧
    SliceOk m (reg m .rdx) (reg m .rcx) basisWEvalStack ∧ WhirIn m o 24 basisWEvalStack ∧
    BasisApart (reg m .rsi) ba

/-- `BasisW::eval`'s postcondition. -/
def BasisWEvalPost (b : BasisW) (m m' : MachineData) : Prop :=
  let o := reg m .rdi
  OptEWAt m'.dmem o (some (b.eval (slice m (reg m .rdx) (reg m .rcx)))) ∧
    ChangesIn m m' basisWEvalStack [⟨o, 24⟩] ∧ Saved m m'

section
variable [Labels]

/-! ## The levels -/

/-- `final_level`'s precondition: the `TState` at RDI, the level at RDX, `μ` (RCX) with `2^μ` plus
the level's fold at most 64 and room for `μ` more `α`s, at most `230` queries, the basis `b` at
R9, the phase-7 state (`w`, the level's `rounds`) at the stack argument `0` (re-read after writes:
the `TState` and the state apart from its word); the inputs apart from the outputs. -/
def FinalLevelPre (a : DecArea) (s : TState) (level : Whir.Level) (ba : BasisAddrs) (b : BasisW)
    (w : WhirStateW) (rounds : Array FoldRoundW) (m : MachineData) : Prop :=
  let N := finalLevelStack; let t := reg m .rdi; let p := stackArg m 0
  let mu := (reg m .rcx).toNat
  WhirT m t a N ∧ ArgsOk m 1 ∧ TStateAt m.dmem t a s ∧ WhirAt m.dmem p w rounds ∧
    LevelAt m.dmem (reg m .rdx) level ∧ BasisWAt m.dmem (reg m .r9) ba b ∧
    mu < 64 ∧ 2 ^ mu + level.fold ≤ laneCap ∧ w.alphas.size + mu ≤ stackCap ∧
    level.logInvRate < 64 ∧ level.queries ≤ queryCap ∧
    WhirOut m t a p whirBytes N ∧ WhirIn m (reg m .rdx) levelBytes N ∧
    Apart (reg m .rdx) levelBytes p whirBytes ∧
    Apart (reg m .rdx) levelBytes t tstateBytes ∧
    BasisIn m (reg m .r9) ba N p whirBytes ∧ BasisIn m (reg m .r9) ba N t tstateBytes ∧
    BasisApart (reg m .r9) ba ∧
    Apart (rspOf m + 8#64) 8 t tstateBytes ∧ Apart (rspOf m + 8#64) 8 p whirBytes ∧
    GotAt m N ([(t, tstateBytes), (a.words, 8 * a.len), (p, whirBytes),
      (reg m .rdx, levelBytes), (rspOf m + 8#64, 8)] ++ rodataAreas) ["memcpy", "memset"]

/-- `final_level`'s postcondition: `finalLevelM` (`index` RSI, `laneFolds` R8). -/
def FinalLevelPost (a : DecArea) (s : TState) (level : Whir.Level) (b : BasisW) (w : WhirStateW)
    (rounds : Array FoldRoundW) (m m' : MachineData) : Prop :=
  let t := reg m .rdi; let p := stackArg m 0
  let r := (finalLevelM (reg m .rsi).toNat level (reg m .rcx).toNat (reg m .r8).toNat b w
    rounds).run s
  OkAl m' r.isSome ∧ NextAt m'.dmem t a r ∧
    ChangesIn m m' finalLevelStack [⟨p, whirBytes⟩, ⟨t, tstateBytes⟩] ∧ Saved m m'

/-- `next_level`'s precondition: the `TState` at RDI (fewer than 8 roots), the level at RDX (at
most 6 folds, at most `230` queries), the next level's fold (RCX, below 63) and rate exponent (R8,
below 64), `μ ≤ 30` (R9), the phase-7 state (`w`, room for two glued claims; the level's `rounds`)
at the stack argument `0` (re-read after writes: the `TState` and the state apart from its word);
the level apart from the outputs. -/
def NextLevelPre (a : DecArea) (s : TState) (level : Whir.Level) (w : WhirStateW)
    (rounds : Array FoldRoundW) (m : MachineData) : Prop :=
  let N := nextLevelStack; let t := reg m .rdi; let p := stackArg m 0
  WhirT m t a N ∧ ArgsOk m 1 ∧ TStateAt m.dmem t a s ∧ s.roots.size < maxRoots ∧
    WhirAt m.dmem p w rounds ∧
    LevelAt m.dmem (reg m .rdx) level ∧ level.fold ≤ roundCap ∧
    level.logInvRate < 64 ∧ level.queries ≤ queryCap ∧ (reg m .rcx).toNat < 63 ∧
    (reg m .r8).toNat < 64 ∧ (reg m .r9).toNat ≤ stackCap ∧ w.glued.size + 2 ≤ gluedCap ∧
    WhirOut m t a p whirBytes N ∧ WhirIn m (reg m .rdx) levelBytes N ∧
    Apart (reg m .rdx) levelBytes p whirBytes ∧
    Apart (reg m .rdx) levelBytes t tstateBytes ∧
    Apart (rspOf m + 8#64) 8 t tstateBytes ∧ Apart (rspOf m + 8#64) 8 p whirBytes ∧
    GotAt m N ([(t, tstateBytes), (a.words, 8 * a.len), (p, whirBytes),
      (reg m .rdx, levelBytes), (rspOf m + 8#64, 8)] ++ rodataAreas) ["memcpy", "memset"]

/-- `next_level`'s postcondition: `nextLevelM` (the next level's query count unused; `index` RSI),
the glued state at the stack argument `0`, the rounds kept. -/
def NextLevelPost (a : DecArea) (s : TState) (level : Whir.Level) (w : WhirStateW)
    (rounds : Array FoldRoundW) (m m' : MachineData) : Prop :=
  let t := reg m .rdi; let p := stackArg m 0
  let r := (nextLevelM (reg m .rsi).toNat level ⟨(reg m .rcx).toNat, (reg m .r8).toNat, 0⟩
    (reg m .r9).toNat w rounds).run s
  OkAl m' r.isSome ∧ NextAt m'.dmem t a r ∧
    (∀ w' s', r = some (w', s') → WhirAt m'.dmem p w' rounds) ∧
    ChangesIn m m' nextLevelStack [⟨p, whirBytes⟩, ⟨t, tstateBytes⟩] ∧ Saved m m'

/-- `whir_levels`'s precondition: the `TState` at RDI (room for a root per level), `logN` (RSI)
with the levels (R8, R9) its ladder at some rate, the basis `b` at RCX, a fresh state of claim
`claim` at the stack argument `0` (`final_level`'s, a tail call: the `TState` and the state apart
from its word); the inputs apart from the outputs. -/
def WhirLevelsPre (a : DecArea) (s : TState) (levels : List Whir.Level) (ba : BasisAddrs)
    (b : BasisW) (claim : EW) (m : MachineData) : Prop :=
  let N := whirLevelsStack; let t := reg m .rdi; let p := stackArg m 0
  let lv := reg m .r8
  WhirT m t a N ∧ ArgsOk m 1 ∧ TStateAt m.dmem t a s ∧ s.roots.size + levels.length ≤ maxRoots ∧
    (∃ rate, Whir.ladder (reg m .rsi).toNat rate = some levels) ∧
    levels.length = (reg m .r9).toNat ∧ LevelsAt m.dmem lv levels ∧
    BasisWAt m.dmem (reg m .rcx) ba b ∧
    WhirStateAt m.dmem p ⟨claim, #[], #[]⟩ ∧ WhirOut m t a p whirBytes N ∧
    WhirIn m lv (levelBytes * levels.length) N ∧ Apart lv (levelBytes * levels.length) p whirBytes ∧
    Apart lv (levelBytes * levels.length) t tstateBytes ∧
    BasisIn m (reg m .rcx) ba N p whirBytes ∧ BasisIn m (reg m .rcx) ba N t tstateBytes ∧
    BasisApart (reg m .rcx) ba ∧
    Apart (rspOf m + 8#64) 8 t tstateBytes ∧ Apart (rspOf m + 8#64) 8 p whirBytes ∧
    GotAt m N ([(t, tstateBytes), (a.words, 8 * a.len), (p, whirBytes),
      (lv, levelBytes * levels.length), (rspOf m + 8#64, 8)] ++ rodataAreas) ["memcpy", "memset"]

/-- `whir_levels`'s postcondition: `whirLevels logN laneFolds b 0 levels` (`laneFolds` RDX). -/
def WhirLevelsPost (a : DecArea) (s : TState) (levels : List Whir.Level) (b : BasisW) (claim : EW)
    (m m' : MachineData) : Prop :=
  let t := reg m .rdi; let p := stackArg m 0
  let r := (whirLevels (reg m .rsi).toNat (reg m .rdx).toNat b 0 levels ⟨claim, #[], #[]⟩).run s
  OkAl m' r.isSome ∧ NextAt m'.dmem t a r ∧
    ChangesIn m m' whirLevelsStack [⟨p, whirBytes⟩, ⟨t, tstateBytes⟩] ∧ Saved m m'

/-! ## `verify_stacked_opening` -/

/-- `verify_stacked_opening`'s inputs (`layout`, `ring`, `keccak`, `claims`, `ood`: RSI, RCX, R8,
R9, the stack argument `0`) as a `BasisAddrs` without scales. -/
def vsoInputs (m : MachineData) : List NativeRustcVm.Region :=
  (BasisAddrs.regions ⟨0, 0, reg m .rsi, reg m .rcx, reg m .r8, reg m .r9, stackArg m 0⟩).tail

/-- `verify_stacked_opening`'s precondition: the `TState` at RDI (at most two roots read), the
layout at RSI, the ring switch's output at RCX, the Keccak output at R8, the column claims at R9,
the out-of-domain claim `⟨.eq z, value⟩` at the stack argument `0`, the scales' `Buf<EW, 162>` at
the stack argument `1`, the `WhirW` at the stack argument `2`; the inputs apart from the outputs
and from each other, the outputs apart, the argument words apart from the `TState`, the scales
and the `WhirW` (re-read after writes). -/
def VerifyStackedOpeningPre (a : DecArea) (s : TState) (layout : LayoutW) (target : EW)
    (coefficients point slices : Array EW) (cs : Array ColumnClaimW) (z : Array EW) (value : EW)
    (m : MachineData) : Prop :=
  let N := verifyStackedOpeningStack; let t := reg m .rdi
  let sc := stackArg m 1; let p := stackArg m 2
  WhirT m t a N ∧ ArgsOk m 3 ∧ TStateAt m.dmem t a s ∧ s.roots.size ≤ 2 ∧
    NativeRustcVm.Layout.LayoutWAt m.dmem (reg m .rsi) layout ∧
    NativeRustcVm.Ring.RingWAt m.dmem (reg m .rcx) target coefficients ∧
    NativeRustcVm.KeccakGkr.KeccakOutAt m.dmem (reg m .r8) point slices ∧
    NativeRustcVm.Layout.ClaimsWAt m.dmem (reg m .r9) cs ∧
    NativeRustcVm.Layout.EqClaimAt m.dmem (stackArg m 0) z value ∧
    Apart (rspOf m + 8#64) 24 t tstateBytes ∧ Apart (rspOf m + 8#64) 24 sc scalesBytes ∧
    Apart (rspOf m + 8#64) 24 p whirBytes ∧ WhirOut m t a p whirBytes N ∧
    WhirOut m t a sc scalesBytes N ∧ Apart p whirBytes sc scalesBytes ∧
    (∀ r ∈ vsoInputs m, WhirIn m r.addr r.size N ∧ Apart r.addr r.size t tstateBytes ∧
      Apart r.addr r.size p whirBytes ∧ Apart r.addr r.size sc scalesBytes) ∧
    ((vsoInputs m).Pairwise fun r r' ↦ Apart r.addr r.size r'.addr r'.size) ∧
    GotAt m N ([(t, tstateBytes), (a.words, 8 * a.len), (sc, scalesBytes), (p, whirBytes)] ++
      (vsoInputs m).map (fun r => (r.addr, r.size)) ++ rodataAreas) ["memcpy", "memset"]

/-- `verify_stacked_opening`'s postcondition: `verifyStackedOpening` of the stack's log-size, the
rate exponent (RDX) and the stack claims. -/
def VerifyStackedOpeningPost (a : DecArea) (s : TState) (layout : LayoutW) (target : EW)
    (coefficients point : Array EW) (cs : Array ColumnClaimW) (z : Array EW) (value : EW)
    (m m' : MachineData) : Prop :=
  let t := reg m .rdi; let sc := stackArg m 1; let p := stackArg m 2
  let r := (verifyStackedOpening layout.stackLog (reg m .rdx).toNat
    (stackClaims layout target point coefficients cs z value)).run s
  OkAl m' r.isSome ∧ NextAt m'.dmem t a r ∧
    ChangesIn m m' verifyStackedOpeningStack
      [⟨p, whirBytes⟩, ⟨sc, scalesBytes⟩, ⟨t, tstateBytes⟩] ∧ Saved m m'

end

end

end NativeRustcVmX64
