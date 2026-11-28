module

public import NativeRustcVmX64.Spec.Sumcheck
public import NativeRustcVmX64.Spec.Layout
public import NativeRustcX64.Spec.Got
public import NativeRustcVmX64.Rodata
public import NativeRustcVm.Tables.Rep
public import NativeVm.Model.PublicInput
public import NativeRustcVmX64.Code.Vm.PublicInputPhase.Names
public import NativeRustcVmX64.Code.Vm.TableColumnClaims.Names
public import NativeRustcVmX64.Code.Vm.TablePhase.Names
public import NativeRustcVmX64.Code.Vm.TableSumcheck.Names
public import NativeRustcVmX64.Code.Vm.TableTerms.Names
public import NativeRustcVmX64.Code.Vm.TableWeights.Names

/-!
# The contracts of `tables.rs`'s functions on x86-64 (phases 4 and 5)

The AArch64 contracts (`NativeRustcVmArm.Spec.Tables`) with the System V registers: arguments in
RDI, RSI, RDX, RCX, R8, R9, then on the stack above the return address (`stackArg`, mapped by
`ArgsOk`); an `Option<()>` in AL (`OkAl`). Each function uses the stack below RSP (`<fn>Stack`
bytes: its pushes, its frame, the argument words it pushes for a callee, its callees' return
addresses and stacks; `StackOk` also maps its return address at RSP) and returns with the
callee-saved registers kept (and RSP 8 above, `Spec`), no byte changed outside its outputs and that
stack. The transcript's functions take the `TState` at `t` representing the model's `s` with the
decoded area `a` (`TStateAt`) and leave it representing the next state (`NextAt`); they read the
round constants (`RcAt`) and, through the transcript permutation, the `memcpy` GOT slot (`GotAt`).
The inputs they only read are readable and apart from what they write (`ReadIn`). rustc fixed the lengths of the arrays of constant length (the six log-heights, the two
constraint powers, the three form powers, the six weights) and passes only their pointers. The
results are the model's (`NativeVm.Model`):

- `table_weights(out, heights, equality_point, point)` (RDI; RSI; RDX, RCX; R8, R9; rustc passes
  the returned `[EW; 6]`'s address in RDI): the six elements at `out` become `tableWeights heights
  equality_point point`, the heights the six words at RSI (`heightsOf`).
- `table_terms(out, t, constraint_powers, form_powers, point, heights, forms, weights, evals)`
  (RDI to RCX, the point R8, R9, then the stack arguments `0` to `3`): `tableTerms` over the rows
  `tablesW`, the heights (`HeightsAt`), the forms (`FormsAt`) and the weights, the final sum the
  `Option<EW>` at `out`, the tables' points and evaluations at `evals` (`TableEvalsAt`). It reads
  `TABLES` (`RodataAt`). `|point| ≤ 30` (its caller's point is the sumcheck's, at most
  `TABLE_POINT_CAP`). It reads the heights and the weights' addresses from the stack in every
  round: its outputs are apart from the arguments.
- `table_sumcheck(t, heights, bus, constraint_powers, form_powers, target, evals)` (RDI to R8;
  `target` R9 and the stack argument `0`; `evals` the stack argument `1`): `tableSumcheck heights
  forms constraint_powers form_powers point target` of the bus's forms and point (`BusWAt`), AL
  the `Option<()>`. It reads `evals` from the stack after its calls: its outputs are apart from
  the arguments.
- `table_phase(t, layout, bus, evals)` (RDI to RCX): `tablePhase layout bus` (`LayoutWAt`,
  `BusWAt`), AL the `Option<()>`, the result at `evals`.
- `table_column_claims(evals, claims)` (RDI, RSI): the claims (`ClaimsWAt`) become theirs followed
  by `tableColumnClaims evals` when they fit `CLAIM_CAP`, AL the `Option<()>`.
- `public_input_phase(t, layout, public_input, claims)` (RDI to RCX): `publicInputPhase layout
  public_input` (the four words at RDX), its two claims appended to the claims when they fit. The
  Rust rejects a memory placement of more than `31` variables (its point's capacity); the layout's
  is at most `30`: `(layout.placement memory0).variableCount ≤ 31`.
-/

namespace NativeRustcVmX64

open NativeRustcX64 NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Layout NativeRustcVm.Bus
open LeanVM.Protocol.Verifier (memory0)
open NativeRustcVm.Tables
open NativeRustcVm (wordsOf wordOf EWsAt)

@[expose] public section

/-! ## Stacks -/

/-- The stack `table_weights` uses: 6 pushes, its 200-byte frame, `EW::mul`'s return address and
stack. -/
def tableWeightsStack : Nat := 256 + ewMulStack
/-- The stack `table_terms` uses: 6 pushes, its 216-byte frame, the return address and stack of
its callees (`read_scalars`, `constraints_w`, `dot`, `evaluate`, `Buf::extend`, `EW::mul`). -/
def tableTermsStack : Nat :=
  272 + max readScalarsStack (max constraintsWStack (max dotStack (max evaluateStack
    (max bufEWExtendStack ewMulStack))))
/-- The stack `table_sumcheck` uses: 6 pushes, its 648-byte frame, the return address and stack
of its callees: `sumcheck` below the two words it pushes (an alignment word and `n`),
`table_weights`, `table_terms` below its four stack arguments. -/
def tableSumcheckStack : Nat :=
  704 + max (16 + sumcheckPlainStack) (max tableWeightsStack (32 + tableTermsStack))
/-- The stack `table_phase` uses: 6 pushes, its 88-byte frame, the return address and stack of its
callees (`bit_length`, `grind`, `squeeze`, `powers`, `dot`; `table_sumcheck` below its two stack
arguments). -/
def tablePhaseStack : Nat :=
  144 + max bitLengthStack (max grindStack (max squeezeStack (max powersStack
    (max dotStack (16 + tableSumcheckStack)))))
/-- The stack `table_column_claims` uses: 7 pushes, `push_claim`'s return address and stack. -/
def tableColumnClaimsStack : Nat := 64 + pushClaimStack
/-- The stack `public_input_phase` uses: 6 pushes, its 552-byte frame, the return address and
stack of its callees (`squeeze`, `LayoutW::placement`, `multilinear_eval_by`, `push_claim`). -/
def publicInputPhaseStack : Nat :=
  608 + max squeezeStack (max layoutWPlacementStack (max mleStack pushClaimStack))

/-! ## Arguments -/

/-- The six words at `a` as numbers: the tables' log-heights `table_weights` reads. -/
def heightsOf (d : Mem 64) (a : BitVec 64) : Array Nat :=
  ((wordsOf d a nTables).map UInt64.toNat).toArray

/-- The `n` elements of `E` from `a` (an array rustc passes by its pointer only). -/
def arrE (m : MachineData) (a : BitVec 64) (n : Nat) : Array EW :=
  (NativeRustcVm.ewsOf m.dmem a n).toArray

/-- An input of `n` bytes at `x`, only read: data memory, not wrapping, apart from the `N` bytes
of stack below RSP and the return address and from each region written (`ws`). -/
def ReadIn (m : MachineData) (x : BitVec 64) (n N : Nat) (ws : List NativeRustcVm.Region) : Prop :=
  Readable m x n ∧ OffStack m x n N ∧ ∀ w ∈ ws, Apart x n w.addr w.size

section
variable [Labels]

/-- `TABLES` at its label, apart from the `N` bytes of stack below RSP and the return address. -/
def TablesAt (m : MachineData) (N : Nat) : Prop := RodataAt m N

/-! ## `table_weights` -/

/-- `table_weights`'s precondition: the six heights at RSI, `equality_point` (RDX, RCX), `point`
(R8, R9) and the 96 bytes at `out` (RDI) apart from the stack. -/
def TableWeightsPre (m : MachineData) : Prop :=
  StackOk m tableWeightsStack ∧ Readable m (reg m .rdi) 96 ∧
    OffStack m (reg m .rdi) 96 tableWeightsStack ∧
    ReadIn m (reg m .rsi) 48 tableWeightsStack [] ∧
    SliceOk m (reg m .rdx) (reg m .rcx) tableWeightsStack ∧
    SliceOk m (reg m .r8) (reg m .r9) tableWeightsStack

/-- `table_weights`'s postcondition. -/
def TableWeightsPost (m m' : MachineData) : Prop :=
  EWsAt m'.dmem (reg m .rdi) (tableWeights (heightsOf m.dmem (reg m .rsi))
      (slice m (reg m .rdx) (reg m .rcx)) (slice m (reg m .r8) (reg m .r9))).toList ∧
    Changes m m' tableWeightsStack (reg m .rdi) 96 ∧ Saved m m'

/-! ## `table_terms` -/

/-- The rows `table_terms` walks: each table, its log-height, its forms, its weight. -/
def tableRows (heights : Array Nat) (forms : Array (Array FormW)) (weights : Array EW) :
    Array (TableW × Nat × Array FormW × EW) :=
  tablesW.zip (heights.zip (forms.zip weights))

/-- `table_terms`'s precondition: the `Option<EW>` at `out` (RDI), the transcript (RSI), the two
constraint powers (RDX), the three form powers (RCX), the point (R8, R9; at most `30`), the heights
(the stack argument `0`), the forms (`1`), the six weights (`2`), the evaluations' entries (`3`);
the outputs and the inputs apart from the four argument words (it reads the heights' and the
weights' addresses from them in the blocks that read the heights and the weights). -/
def TableTermsPre (a : DecArea) (s : TState) (heights : Array Nat) (forms : Array (Array FormW))
    (m : MachineData) : Prop :=
  let N := tableTermsStack
  let o := reg m .rdi; let t := reg m .rsi
  let w := stackArg m 2; let e := stackArg m 3
  let ws : List NativeRustcVm.Region :=
    [⟨o, 24⟩, ⟨t, tstateBytes⟩, ⟨e, tableEvalsBytes⟩, ⟨rspOf m + 8#64, 32⟩]
  StackOk m N ∧ RcAt m N ∧ TablesAt m N ∧ ArgsOk m 4 ∧
    TStateAt m.dmem t a s ∧ TStateOk m t a N ∧ OutOk m t a o 24 N ∧
    OutOk m t a e tableEvalsBytes N ∧ Apart o 24 e tableEvalsBytes ∧
    Apart o 24 (rspOf m + 8#64) 32 ∧ Apart t tstateBytes (rspOf m + 8#64) 32 ∧
    Apart e tableEvalsBytes (rspOf m + 8#64) 32 ∧
    RodataApart t tstateBytes ∧ RodataApart o 24 ∧ RodataApart e tableEvalsBytes ∧
    (reg m .r9).toNat ≤ tablePointCap ∧
    ReadIn m (reg m .rdx) 32 N ws ∧ ReadIn m (reg m .rcx) 48 N ws ∧
    ReadIn m (reg m .r8) (16 * (reg m .r9).toNat) N ws ∧
    ReadIn m (stackArg m 0) 48 N ws ∧ HeightsAt m.dmem (stackArg m 0) heights ∧
    ReadIn m (stackArg m 1) formsBytes N ws ∧ FormsAt m.dmem (stackArg m 1) forms ∧
    ReadIn m w 96 N ws ∧
    GotAt m N [(o, 24), (t, tstateBytes), (a.words, 8 * a.len), (e, tableEvalsBytes),
      (rspOf m + 8#64, 32), (reg m .rdx, 32), (reg m .rcx, 48),
      (reg m .r8, 16 * (reg m .r9).toNat), (stackArg m 0, 48),
      (stackArg m 1, formsBytes), (w, 96), (rcAddr, 192),
      (rodataAddr .tables, NativeRustcVm.Data.Item.tables.bytes.length)] ["memcpy"]

/-- `table_terms`'s postcondition. -/
def TableTermsPost (a : DecArea) (s : TState) (heights : Array Nat) (forms : Array (Array FormW))
    (m m' : MachineData) : Prop :=
  let N := tableTermsStack
  let o := reg m .rdi; let t := reg m .rsi; let e := stackArg m 3
  let weights := (NativeRustcVm.ewsOf m.dmem (stackArg m 2) nTables).toArray
  let r := (tableTerms (arrE m (reg m .rdx) 2) (arrE m (reg m .rcx) 3) (slice m (reg m .r8) (reg m .r9))
    (tableRows heights forms weights)).run s
  OptEWAt m'.dmem o (r.map (·.1.1)) ∧
    (∀ x s', r = some (x, s') → TableEvalsAt m'.dmem e x.2) ∧ NextAt m'.dmem t a r ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange o 24 q ∨ InRange t tstateBytes q ∨
      InRange e tableEvalsBytes q ∨ InRange (stackBelow m N) N q) ∧ Saved m m'

/-! ## `table_sumcheck` -/

/-- `table_sumcheck`'s precondition: the transcript (RDI), the heights (RSI), the bus's result
(RDX), the two constraint powers (RCX), the three form powers (R8), the evaluations' entries (the
stack argument `1`); the outputs apart from the two argument words. -/
def TableSumcheckPre (a : DecArea) (s : TState) (heights : Array Nat) (bus : BusResultW)
    (m : MachineData) : Prop :=
  let N := tableSumcheckStack
  let t := reg m .rdi; let e := stackArg m 1
  let ws : List NativeRustcVm.Region := [⟨t, tstateBytes⟩, ⟨e, tableEvalsBytes⟩]
  StackOk m N ∧ RcAt m N ∧ TablesAt m N ∧ ArgsOk m 2 ∧ TStateAt m.dmem t a s ∧
    TStateOk m t a N ∧ OutOk m t a e tableEvalsBytes N ∧
    Apart t tstateBytes (rspOf m + 8#64) 16 ∧ Apart e tableEvalsBytes (rspOf m + 8#64) 16 ∧
    RodataApart t tstateBytes ∧ RodataApart e tableEvalsBytes ∧
    ReadIn m (reg m .rsi) 48 N ws ∧ HeightsAt m.dmem (reg m .rsi) heights ∧
    ReadIn m (reg m .rdx) busBytes N ws ∧ BusWAt m.dmem (reg m .rdx) bus ∧
    ReadIn m (reg m .rcx) 32 N ws ∧ ReadIn m (reg m .r8) 48 N ws ∧
    GotAt m N [(t, tstateBytes), (a.words, 8 * a.len), (e, tableEvalsBytes),
      (rspOf m + 8#64, 16), (reg m .rsi, 48), (reg m .rdx, busBytes),
      (reg m .rcx, 32), (reg m .r8, 48), (rcAddr, 192),
      (rodataAddr .tables, NativeRustcVm.Data.Item.tables.bytes.length)] ["memcpy"]

/-- `table_sumcheck`'s postcondition. -/
def TableSumcheckPost (a : DecArea) (s : TState) (heights : Array Nat) (bus : BusResultW)
    (m m' : MachineData) : Prop :=
  let N := tableSumcheckStack
  let t := reg m .rdi; let e := stackArg m 1
  let r := (tableSumcheck heights bus.forms (arrE m (reg m .rcx) 2) (arrE m (reg m .r8) 3)
    bus.point (ewArg (reg m .r9) (stackArg m 0))).run s
  OkAl m' r.isSome ∧ (∀ x s', r = some (x, s') → TableEvalsAt m'.dmem e x) ∧
    NextAt m'.dmem t a r ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange t tstateBytes q ∨ InRange e tableEvalsBytes q ∨
      InRange (stackBelow m N) N q) ∧ Saved m m'

/-! ## `table_phase` -/

/-- `table_phase`'s precondition: the transcript (RDI), the layout (RSI), the bus's result (RDX),
the evaluations' entries (RCX). -/
def TablePhasePre (a : DecArea) (s : TState) (layout : LayoutW) (bus : BusResultW)
    (m : MachineData) : Prop :=
  let N := tablePhaseStack
  let t := reg m .rdi; let e := reg m .rcx
  let ws : List NativeRustcVm.Region := [⟨t, tstateBytes⟩, ⟨e, tableEvalsBytes⟩]
  StackOk m N ∧ RcAt m N ∧ TablesAt m N ∧ TStateAt m.dmem t a s ∧ TStateOk m t a N ∧
    OutOk m t a e tableEvalsBytes N ∧ RodataApart t tstateBytes ∧ RodataApart e tableEvalsBytes ∧
    ReadIn m (reg m .rsi) layoutBytes N ws ∧ LayoutWAt m.dmem (reg m .rsi) layout ∧
    ReadIn m (reg m .rdx) busBytes N ws ∧ BusWAt m.dmem (reg m .rdx) bus ∧
    GotAt m N [(t, tstateBytes), (a.words, 8 * a.len), (e, tableEvalsBytes),
      (reg m .rsi, layoutBytes), (reg m .rdx, busBytes), (rcAddr, 192),
      (rodataAddr .tables, NativeRustcVm.Data.Item.tables.bytes.length)] ["memcpy"]

/-- `table_phase`'s postcondition. -/
def TablePhasePost (a : DecArea) (s : TState) (layout : LayoutW) (bus : BusResultW)
    (m m' : MachineData) : Prop :=
  let N := tablePhaseStack
  let t := reg m .rdi; let e := reg m .rcx
  let r := (tablePhase layout bus).run s
  OkAl m' r.isSome ∧ (∀ x s', r = some (x, s') → TableEvalsAt m'.dmem e x) ∧
    NextAt m'.dmem t a r ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange t tstateBytes q ∨ InRange e tableEvalsBytes q ∨
      InRange (stackBelow m N) N q) ∧ Saved m m'

/-! ## `table_column_claims` -/

/-- `table_column_claims`'s precondition: the evaluations' entries (RDI), the claims (RSI). -/
def TableColumnClaimsPre (evals : Array (Array EW × Array EW)) (cs : Array ColumnClaimW)
    (m : MachineData) : Prop :=
  let N := tableColumnClaimsStack
  let e := reg m .rdi; let c := reg m .rsi
  StackOk m N ∧ ReadIn m e tableEvalsBytes N [⟨c, claimsBytes⟩] ∧
    TableEvalsAt m.dmem e evals ∧ Readable m c claimsBytes ∧ OffStack m c claimsBytes N ∧
    ClaimsWAt m.dmem c cs

/-- `table_column_claims`'s postcondition: the claims appended when they fit. -/
def TableColumnClaimsPost (evals : Array (Array EW × Array EW)) (cs : Array ColumnClaimW)
    (m m' : MachineData) : Prop :=
  let c := reg m .rsi
  let fits := cs.size + (tableColumnClaims evals).size ≤ claimCap
  OkAl m' (decide fits) ∧ (fits → ClaimsWAt m'.dmem c (cs ++ tableColumnClaims evals)) ∧
    Changes m m' tableColumnClaimsStack c claimsBytes ∧ Saved m m'

/-! ## `public_input_phase` -/

/-- `public_input_phase`'s precondition: the transcript (RDI), the layout (RSI), its memory
placement of at most `31` variables, the public input's four words (RDX), the claims (RCX). -/
def PublicInputPhasePre (a : DecArea) (s : TState) (layout : LayoutW) (pub : Vector UInt64 4)
    (cs : Array ColumnClaimW) (m : MachineData) : Prop :=
  let N := publicInputPhaseStack
  let t := reg m .rdi; let c := reg m .rcx
  let ws : List NativeRustcVm.Region := [⟨t, tstateBytes⟩, ⟨c, claimsBytes⟩]
  StackOk m N ∧ RcAt m N ∧ TStateAt m.dmem t a s ∧ TStateOk m t a N ∧
    OutOk m t a c claimsBytes N ∧ ClaimsWAt m.dmem c cs ∧
    ReadIn m (reg m .rsi) layoutBytes N ws ∧ LayoutWAt m.dmem (reg m .rsi) layout ∧
    (layout.placement memory0).variableCount ≤ 31 ∧
    ReadIn m (reg m .rdx) 32 N ws ∧ NativeRustcVm.WordsAt m.dmem (reg m .rdx) pub.toList ∧
    GotAt m N [(t, tstateBytes), (a.words, 8 * a.len), (c, claimsBytes),
      (reg m .rsi, layoutBytes), (reg m .rdx, 32), (rcAddr, 192)] ["memcpy"]

/-- `public_input_phase`'s postcondition: the claims appended when they fit. -/
def PublicInputPhasePost (a : DecArea) (s : TState) (layout : LayoutW) (pub : Vector UInt64 4)
    (cs : Array ColumnClaimW) (m m' : MachineData) : Prop :=
  let N := publicInputPhaseStack
  let t := reg m .rdi; let c := reg m .rcx
  let r := (publicInputPhase layout pub).run s
  let fits := cs.size + 2 ≤ claimCap
  OkAl m' (r.isSome && decide fits) ∧
    (∀ x s', r = some (x, s') → fits → ClaimsWAt m'.dmem c (cs ++ x)) ∧ NextAt m'.dmem t a r ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange t tstateBytes q ∨ InRange c claimsBytes q ∨
      InRange (stackBelow m N) N q) ∧ Saved m m'

end

end

end NativeRustcVmX64
