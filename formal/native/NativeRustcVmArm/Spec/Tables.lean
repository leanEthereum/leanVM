module

public import NativeRustcVmArm.Code.Vm.PublicInputPhase.Names
public import NativeRustcVmArm.Code.Vm.TableColumnClaims.Names
public import NativeRustcVmArm.Code.Vm.TablePhase.Names
public import NativeRustcVmArm.Code.Vm.TableSumcheck.Names
public import NativeRustcVmArm.Code.Vm.TableTerms.Names
public import NativeRustcVmArm.Code.Vm.TableWeights.Names
public import NativeRustcVmArm.Spec.Sumcheck
public import NativeRustcVmArm.Spec.Layout
public import NativeRustcVmArm.Rodata
public import NativeRustcVm.Tables.Rep
public import NativeVm.Model.PublicInput

/-!
# The contracts of `tables.rs`'s functions on AArch64 (phases 4 and 5)

Each function uses the stack below SP (`<fn>Stack` bytes, its callees' included; `StackOk` in its
precondition) and returns with the callee-saved registers and SP kept (`Saved`), no byte changed
outside its outputs and that stack. The transcript's functions take the `TState` at `t`
representing the model's `s` with the decoded area `a` (`TStateAt`) and leave it representing the
next state (`NextAt`); they read the round constants (`RcAt`). The inputs they only read are
readable and apart from what they write (`ReadIn`). rustc fixed the lengths of the arrays of
constant length (the six log-heights, the two constraint powers, the three form powers, the six
weights) and passes only their pointers. The results are the model's (`NativeVm.Model`):

- `table_weights(out, heights, equality_point, point)` (X0; X1; X2, X3; X4, X5; rustc passes the
  returned `[EW; 6]`'s address in X0): the six elements at `out` become `tableWeights heights
  equality_point point`, the heights the six words at X1 (`heightsOf`).
- `table_terms(out, t, constraint_powers, form_powers, point, heights, forms, weights, evals)`
  (X0 to X7, then the words at SP and SP + 8): `tableTerms` over the rows `tablesW`, the heights
  (`HeightsAt`), the forms (`FormsAt`) and the weights, the final sum the `Option<EW>` at `out`, the
  tables' points and evaluations at `evals` (`TableEvalsAt`). It reads `TABLES` (`RodataAt`).
  `|point| ≤ 30` (its caller's point is the sumcheck's, at most `TABLE_POINT_CAP`).
- `table_sumcheck(t, heights, bus, constraint_powers, form_powers, target, evals)` (X0, X1, X2,
  X3, X4; `target` X5, X6; X7): `tableSumcheck heights forms constraint_powers form_powers point
  target` of the bus's forms and point (`BusWAt`), X0 the `Option<()>`.
- `table_phase(t, layout, bus, evals)` (X0 to X3): `tablePhase layout bus` (`LayoutWAt`,
  `BusWAt`), X0 the `Option<()>`, the result at `evals`.
- `table_column_claims(evals, claims)` (X0, X1): the claims (`ClaimsWAt`) become theirs followed by
  `tableColumnClaims evals` when they fit `CLAIM_CAP`, X0 the `Option<()>`.
- `public_input_phase(t, layout, public_input, claims)` (X0 to X3): `publicInputPhase layout
  public_input` (the four words at X2), its two claims appended to the claims when they fit. The
  Rust rejects a memory placement of more than `31` variables (its point's capacity); the layout's
  is at most `30`: `(layout.placement memory0).variableCount ≤ 31`.
-/

namespace NativeRustcVmArm

open NativeRustcArm NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Layout NativeRustcVm.Bus
open LeanVM.Protocol.Verifier (memory0)
open NativeRustcVm.Tables
open NativeRustcVm (wordsOf wordOf EWsAt)

@[expose] public section

/-! ## Symbols -/


/-! ## Stacks -/

/-- The stack `table_weights` uses: its 240-byte frame and `EW::mul`'s. -/
def tableWeightsStack : Nat := 240 + ewMulStack
/-- The stack `table_terms` uses: its 288-byte frame and `evaluate`'s (`80 + ewMulStack`), the
largest of its callees' (`read_scalars`, `constraints_w`, `dot`, `Buf::extend`, `EW::mul`). -/
def tableTermsStack : Nat := 288 + evaluateStack
/-- The stack `table_sumcheck` uses: its 720-byte frame and its callees'. -/
def tableSumcheckStack : Nat := 720 + max sumcheckPlainStack (max tableWeightsStack tableTermsStack)
/-- The stack `table_phase` uses: its 128-byte frame and its callees' (`bit_length` uses none). -/
def tablePhaseStack : Nat :=
  128 + max grindStack (max squeezeStack (max powersStack (max dotStack tableSumcheckStack)))
/-- The stack `table_column_claims` uses: its 64-byte frame and `push_claim`'s. -/
def tableColumnClaimsStack : Nat := 64 + pushClaimStack
/-- The stack `public_input_phase` uses: its 608-byte frame and its callees' (`squeeze`,
`multilinear_eval_by`, `push_claim`; `LayoutW::placement` uses none). -/
def publicInputPhaseStack : Nat :=
  608 + max squeezeStack (max layoutWPlacementStack (max mleStack pushClaimStack))

/-! ## Arguments -/

/-- The six words at `a` as numbers: the tables' log-heights `table_weights` reads. -/
def heightsOf (d : Mem 64) (a : BitVec 64) : Array Nat :=
  ((wordsOf d a nTables).map UInt64.toNat).toArray

/-- The `n` elements of `E` from `a` (an array rustc passes by its pointer only). -/
def arrE (m : MachineData) (a : UInt64) (n : Nat) : Array EW :=
  (NativeRustcVm.ewsOf m.dmem a.toBitVec n).toArray

/-- An input of `n` bytes at `x`, only read: data memory, not wrapping, apart from the `N` bytes
of stack below SP and from each region written (`ws`). -/
def ReadIn (m : MachineData) (x : BitVec 64) (n N : Nat) (ws : List NativeRustcVm.Region) : Prop :=
  Readable m x n ∧ OffStack m x n N ∧ ∀ w ∈ ws, Apart x n w.addr w.size

/-- `TABLES` at its label, apart from the `N` bytes of stack below SP. -/
def TablesAt [Labels] (m : MachineData) (N : Nat) : Prop := RodataAt m N

/-- The word at SP + `o` (a stack argument). -/
def stackWord (m : MachineData) (o : Nat) : BitVec 64 :=
  (wordOf m.dmem (m.regs.SP.toBitVec + BitVec.ofNat 64 o)).toBitVec

section
variable [Labels]

/-! ## `table_weights` -/

/-- `table_weights`'s precondition: the six heights at X1, `equality_point` (X2, X3), `point`
(X4, X5) and the 96 bytes at `out` (X0) apart from the stack. -/
def TableWeightsPre (m : MachineData) : Prop :=
  StackOk m tableWeightsStack ∧ Readable m m.regs.X0.toBitVec 96 ∧
    OffStack m m.regs.X0.toBitVec 96 tableWeightsStack ∧
    ReadIn m m.regs.X1.toBitVec 48 tableWeightsStack [] ∧
    SliceOk m m.regs.X2 m.regs.X3 tableWeightsStack ∧ SliceOk m m.regs.X4 m.regs.X5 tableWeightsStack

/-- `table_weights`'s postcondition. -/
def TableWeightsPost (m m' : MachineData) : Prop :=
  EWsAt m'.dmem m.regs.X0.toBitVec (tableWeights (heightsOf m.dmem m.regs.X1.toBitVec)
      (slice m m.regs.X2 m.regs.X3) (slice m m.regs.X4 m.regs.X5)).toList ∧
    Changes m m' tableWeightsStack m.regs.X0.toBitVec 96 ∧ Saved m m'

/-! ## `table_terms` -/

/-- The rows `table_terms` walks: each table, its log-height, its forms, its weight. -/
def tableRows (heights : Array Nat) (forms : Array (Array FormW)) (weights : Array EW) :
    Array (TableW × Nat × Array FormW × EW) :=
  tablesW.zip (heights.zip (forms.zip weights))

/-- `table_terms`'s precondition: the `Option<EW>` at `out` (X0), the transcript (X1), the two
constraint powers (X2), the three form powers (X3), the point (X4, X5; at most `30`), the heights
(X6), the forms (X7), the six weights at the word at SP, the evaluations' entries at the word at
SP + 8. -/
def TableTermsPre (a : DecArea) (s : TState) (heights : Array Nat) (forms : Array (Array FormW))
    (m : MachineData) : Prop :=
  let N := tableTermsStack
  let o := m.regs.X0.toBitVec; let t := m.regs.X1.toBitVec
  let w := stackWord m 0; let e := stackWord m 8
  let ws : List NativeRustcVm.Region := [⟨o, 24⟩, ⟨t, tstateBytes⟩, ⟨e, tableEvalsBytes⟩]
  StackOk m N ∧ RcAt m N ∧ TablesAt m N ∧ Readable m m.regs.SP.toBitVec 16 ∧
    TStateAt m.dmem t a s ∧ TStateOk m t a N ∧ OutOk m t a o 24 N ∧
    OutOk m t a e tableEvalsBytes N ∧ Apart o 24 e tableEvalsBytes ∧
    RodataApart t tstateBytes ∧ RodataApart o 24 ∧ RodataApart e tableEvalsBytes ∧
    m.regs.X5.toNat ≤ tablePointCap ∧
    ReadIn m m.regs.X2.toBitVec 32 N ws ∧ ReadIn m m.regs.X3.toBitVec 48 N ws ∧
    ReadIn m m.regs.X4.toBitVec (16 * m.regs.X5.toNat) N ws ∧
    ReadIn m m.regs.X6.toBitVec 48 N ws ∧ HeightsAt m.dmem m.regs.X6.toBitVec heights ∧
    ReadIn m m.regs.X7.toBitVec formsBytes N ws ∧ FormsAt m.dmem m.regs.X7.toBitVec forms ∧
    ReadIn m w 96 N ws

/-- `table_terms`'s postcondition. -/
def TableTermsPost (a : DecArea) (s : TState) (heights : Array Nat) (forms : Array (Array FormW))
    (m m' : MachineData) : Prop :=
  let N := tableTermsStack
  let o := m.regs.X0.toBitVec; let t := m.regs.X1.toBitVec; let e := stackWord m 8
  let weights := (NativeRustcVm.ewsOf m.dmem (stackWord m 0) nTables).toArray
  let r := (tableTerms (arrE m m.regs.X2 2) (arrE m m.regs.X3 3) (slice m m.regs.X4 m.regs.X5)
    (tableRows heights forms weights)).run s
  OptEWAt m'.dmem o (r.map (·.1.1)) ∧
    (∀ x s', r = some (x, s') → TableEvalsAt m'.dmem e x.2) ∧ NextAt m'.dmem t a r ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange o 24 q ∨ InRange t tstateBytes q ∨
      InRange e tableEvalsBytes q ∨ InRange (stackBelow m N) N q) ∧ Saved m m'

/-! ## `table_sumcheck` -/

/-- `table_sumcheck`'s precondition: the transcript (X0), the heights (X1), the bus's result (X2),
the two constraint powers (X3), the three form powers (X4), the evaluations' entries (X7). -/
def TableSumcheckPre (a : DecArea) (s : TState) (heights : Array Nat) (bus : BusResultW)
    (m : MachineData) : Prop :=
  let N := tableSumcheckStack
  let t := m.regs.X0.toBitVec; let e := m.regs.X7.toBitVec
  let ws : List NativeRustcVm.Region := [⟨t, tstateBytes⟩, ⟨e, tableEvalsBytes⟩]
  StackOk m N ∧ RcAt m N ∧ TablesAt m N ∧ TStateAt m.dmem t a s ∧ TStateOk m t a N ∧
    OutOk m t a e tableEvalsBytes N ∧ RodataApart t tstateBytes ∧ RodataApart e tableEvalsBytes ∧
    ReadIn m m.regs.X1.toBitVec 48 N ws ∧ HeightsAt m.dmem m.regs.X1.toBitVec heights ∧
    ReadIn m m.regs.X2.toBitVec busBytes N ws ∧ BusWAt m.dmem m.regs.X2.toBitVec bus ∧
    ReadIn m m.regs.X3.toBitVec 32 N ws ∧ ReadIn m m.regs.X4.toBitVec 48 N ws

/-- `table_sumcheck`'s postcondition. -/
def TableSumcheckPost (a : DecArea) (s : TState) (heights : Array Nat) (bus : BusResultW)
    (m m' : MachineData) : Prop :=
  let N := tableSumcheckStack
  let t := m.regs.X0.toBitVec; let e := m.regs.X7.toBitVec
  let r := (tableSumcheck heights bus.forms (arrE m m.regs.X3 2) (arrE m m.regs.X4 3) bus.point
    ⟨m.regs.X5, m.regs.X6⟩).run s
  m'.regs.X0 = okWord r.isSome ∧ (∀ x s', r = some (x, s') → TableEvalsAt m'.dmem e x) ∧
    NextAt m'.dmem t a r ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange t tstateBytes q ∨ InRange e tableEvalsBytes q ∨
      InRange (stackBelow m N) N q) ∧ Saved m m'

/-! ## `table_phase` -/

/-- `table_phase`'s precondition: the transcript (X0), the layout (X1), the bus's result (X2), the
evaluations' entries (X3). -/
def TablePhasePre (a : DecArea) (s : TState) (layout : LayoutW) (bus : BusResultW)
    (m : MachineData) : Prop :=
  let N := tablePhaseStack
  let t := m.regs.X0.toBitVec; let e := m.regs.X3.toBitVec
  let ws : List NativeRustcVm.Region := [⟨t, tstateBytes⟩, ⟨e, tableEvalsBytes⟩]
  StackOk m N ∧ RcAt m N ∧ TablesAt m N ∧ TStateAt m.dmem t a s ∧ TStateOk m t a N ∧
    OutOk m t a e tableEvalsBytes N ∧ RodataApart t tstateBytes ∧ RodataApart e tableEvalsBytes ∧
    ReadIn m m.regs.X1.toBitVec layoutBytes N ws ∧ LayoutWAt m.dmem m.regs.X1.toBitVec layout ∧
    ReadIn m m.regs.X2.toBitVec busBytes N ws ∧ BusWAt m.dmem m.regs.X2.toBitVec bus

/-- `table_phase`'s postcondition. -/
def TablePhasePost (a : DecArea) (s : TState) (layout : LayoutW) (bus : BusResultW)
    (m m' : MachineData) : Prop :=
  let N := tablePhaseStack
  let t := m.regs.X0.toBitVec; let e := m.regs.X3.toBitVec
  let r := (tablePhase layout bus).run s
  m'.regs.X0 = okWord r.isSome ∧ (∀ x s', r = some (x, s') → TableEvalsAt m'.dmem e x) ∧
    NextAt m'.dmem t a r ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange t tstateBytes q ∨ InRange e tableEvalsBytes q ∨
      InRange (stackBelow m N) N q) ∧ Saved m m'

/-! ## `table_column_claims` -/

/-- `table_column_claims`'s precondition: the evaluations' entries (X0), the claims (X1). -/
def TableColumnClaimsPre (evals : Array (Array EW × Array EW)) (cs : Array ColumnClaimW)
    (m : MachineData) : Prop :=
  let N := tableColumnClaimsStack
  let e := m.regs.X0.toBitVec; let c := m.regs.X1.toBitVec
  StackOk m N ∧ ReadIn m e tableEvalsBytes N [⟨c, claimsBytes⟩] ∧
    TableEvalsAt m.dmem e evals ∧ Readable m c claimsBytes ∧ OffStack m c claimsBytes N ∧
    ClaimsWAt m.dmem c cs

/-- `table_column_claims`'s postcondition: the claims appended when they fit. -/
def TableColumnClaimsPost (evals : Array (Array EW × Array EW)) (cs : Array ColumnClaimW)
    (m m' : MachineData) : Prop :=
  let c := m.regs.X1.toBitVec
  let fits := cs.size + (tableColumnClaims evals).size ≤ claimCap
  m'.regs.X0 = okWord (decide fits) ∧ (fits → ClaimsWAt m'.dmem c (cs ++ tableColumnClaims evals)) ∧
    Changes m m' tableColumnClaimsStack c claimsBytes ∧ Saved m m'

/-! ## `public_input_phase` -/

/-- `public_input_phase`'s precondition: the transcript (X0), the layout (X1), its memory
placement of at most `31` variables, the public input's four words (X2), the claims (X3). -/
def PublicInputPhasePre (a : DecArea) (s : TState) (layout : LayoutW) (pub : Vector UInt64 4)
    (cs : Array ColumnClaimW) (m : MachineData) : Prop :=
  let N := publicInputPhaseStack
  let t := m.regs.X0.toBitVec; let c := m.regs.X3.toBitVec
  let ws : List NativeRustcVm.Region := [⟨t, tstateBytes⟩, ⟨c, claimsBytes⟩]
  StackOk m N ∧ RcAt m N ∧ TStateAt m.dmem t a s ∧ TStateOk m t a N ∧
    OutOk m t a c claimsBytes N ∧ ClaimsWAt m.dmem c cs ∧
    ReadIn m m.regs.X1.toBitVec layoutBytes N ws ∧ LayoutWAt m.dmem m.regs.X1.toBitVec layout ∧
    (layout.placement memory0).variableCount ≤ 31 ∧
    ReadIn m m.regs.X2.toBitVec 32 N ws ∧ NativeRustcVm.WordsAt m.dmem m.regs.X2.toBitVec pub.toList

/-- `public_input_phase`'s postcondition: the claims appended when they fit. -/
def PublicInputPhasePost (a : DecArea) (s : TState) (layout : LayoutW) (pub : Vector UInt64 4)
    (cs : Array ColumnClaimW) (m m' : MachineData) : Prop :=
  let N := publicInputPhaseStack
  let t := m.regs.X0.toBitVec; let c := m.regs.X3.toBitVec
  let r := (publicInputPhase layout pub).run s
  let fits := cs.size + 2 ≤ claimCap
  m'.regs.X0 = okWord (r.isSome && decide fits) ∧
    (∀ x s', r = some (x, s') → fits → ClaimsWAt m'.dmem c (cs ++ x)) ∧ NextAt m'.dmem t a r ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange t tstateBytes q ∨ InRange c claimsBytes q ∨
      InRange (stackBelow m N) N q) ∧ Saved m m'

end

end

end NativeRustcVmArm
