module

public import NativeRustcVmArm.Code.Vm.PushClaim.Names
public import NativeRustcVmArm.Tables.ColumnClaims.Exec
public import NativeRustcVmArm.Tables.Frame
public import NativeRustcVmArm.Tables.Common
public import NativeRustcVm.Tables.Columns
public import NativeRustcVm.Tables.EvalReads

/-!
# `table_column_claims`: one table's loop

rustc unrolled the outer loop: each table has its own head (`cbz` on `16 ×` the values left), body
(the value at the address register, `bl push_claim`) and the block after the call (the next
value's address back, `tbnz` on the result), in registers `Regs`. `LB` collects one table's
blocks with what the executor says of them; `LoopAt`: at a table's head with `j` values pushed.
The loop itself is `loop`, in `ColumnClaims/Iter.lean`.
-/

namespace NativeRustcVmArm.Tables.ColumnClaims

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVm.Tables
open NativeRustcVm.Layout (claimsBytes ClaimsWAt claimCap pointCap)

@[expose] public section

/-- The frame's saved registers. -/
abbrev slots : List (Nat × XReg) :=
  [(0, .X30), (8, .X25), (16, .X24), (24, .X23), (32, .X22), (40, .X21), (48, .X20), (56, .X19)]

/-- The callee-saved registers the prologue does not save. -/
abbrev keep : List XReg := [.X26, .X27, .X28, .X29]

/-- A table's loop registers: the value's address, the column (one before the next), `16 ×` the
values left, the point's address and length, the next value's address across the call. -/
structure Regs where
  a : XReg
  c : XReg
  n : XReg
  p : XReg
  l : XReg
  s : XReg

/-- Tables `0` to `4`'s. -/
def R04 : Regs := ⟨.X8, .X23, .X24, .X21, .X22, .X25⟩
/-- Table `5`'s. -/
def R5 : Regs := ⟨.X9, .X22, .X23, .X20, .X21, .X24⟩

/-- In the frame, the value at `r`. -/
def bodyOf (r : XReg) : SState := init [(64, true), (16, false)] (.ptr 0 0) [(r, .ptr 1 0)]

/-- The output: the claims (X1). -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop := InRange m0.regs.X1.toBitVec claimsBytes q

/-- **At a table's loop head**, `j` of table `i`'s values pushed. -/
structure LoopAt [Labels] (R : Regs) (ev : Array (Array EW × Array EW)) (cs : Array ColumnClaimW)
    (m0 : MachineData) (i j : Nat) (m : MachineData) : Prop where
  fr : Fr m0 64 tableColumnClaimsStack slots keep (outs m0) m
  x19 : m.regs.getXReg .X19 = m0.regs.X1
  x20 : i < 5 → m.regs.getXReg .X20 = m0.regs.X0
  a : (m.regs.getXReg R.a).toBitVec =
    m0.regs.X0.toBitVec + BitVec.ofNat 64 (1968 * i + 496 + 16 * j)
  c : (m.regs.getXReg R.c).toNat + 1 = globalColumnBasesW.getD i 0 + j
  n : (m.regs.getXReg R.n).toNat = 16 * ((valsOf ev i).size - j)
  p : (m.regs.getXReg R.p).toBitVec = m0.regs.X0.toBitVec + BitVec.ofNat 64 (1968 * i + 8)
  l : (m.regs.getXReg R.l).toNat = (ptOf ev i).size
  j_le : j ≤ (valsOf ev i).size
  claims : ClaimsWAt m.dmem m0.regs.X1.toBitVec (cs ++ (pre ev i j).toArray)

/-- **One table's loop blocks** at their places, with what the executor says of them. -/
structure LB [Host] (k : Nat) (R : Regs) where
  H : List Directive
  B : List Directive
  A : List Directive
  jH : Nat
  jN : Nat
  jF : Nat
  lN : Label
  lH : Label
  cA : SBool
  inH : H.IsInfixAt Host.prog (k + jH)
  inB : B.IsInfixAt Host.prog (k + jH + H.length)
  inA : A.IsInfixAt Host.prog (k + jH + H.length + B.length)
  fA : k + jH + H.length + B.length + A.length = k + jF
  runH : exec H sF = some (Bus.after H sF, .cond (.cmp .eq .W64 (.reg R.n) (.lit 0)) lN)
  runB : exec B (bodyOf R.a) = some (Bus.after B (bodyOf R.a), .call NativeRustcVmArm.Vm.PushClaim.entryLabel)
  runA : exec A sF = some (Bus.after A sF, .cond cA lH)
  lblN : Labels.label lN = Host.addrOf (k + jN)
  lblH : Labels.label lH = Host.addrOf (k + jH)
  okH : (Bus.after H sF).mem = [] ∧ (Bus.after H sF).sp = .ptr 0 0 ∧
    allXRegs.all (fun r ↦ (Bus.after H sF).reg r == some (.reg r)) = true
  okB : (Bus.after B (bodyOf R.a)).mem = [] ∧ (Bus.after B (bodyOf R.a)).sp = .ptr 0 0 ∧
    [XReg.X19, .X20, R.p, R.l, .X26, .X27, .X28, .X29].all
      (fun r ↦ (Bus.after B (bodyOf R.a)).reg r == some (.reg r)) = true ∧
    (Bus.after B (bodyOf R.a)).reg .X0 = some (.reg .X19) ∧
    (Bus.after B (bodyOf R.a)).reg .X1 = some (.bin .add .W64 (.reg R.c) (.lit 1)) ∧
    (Bus.after B (bodyOf R.a)).reg .X2 = some (.reg R.p) ∧
    (Bus.after B (bodyOf R.a)).reg .X3 = some (.reg R.l) ∧
    (Bus.after B (bodyOf R.a)).reg .X4 = some (.load 1 0 8) ∧
    (Bus.after B (bodyOf R.a)).reg .X5 = some (.load 1 8 8) ∧
    (Bus.after B (bodyOf R.a)).reg R.c = some (.bin .add .W64 (.reg R.c) (.lit 1)) ∧
    (Bus.after B (bodyOf R.a)).reg R.n = some (.bin .sub .W64 (.reg R.n) (.lit 16)) ∧
    (Bus.after B (bodyOf R.a)).reg R.s = some (.ptr 1 16)
  okA : (Bus.after A sF).mem = [] ∧ (Bus.after A sF).sp = .ptr 0 0 ∧
    [XReg.X19, .X20, R.c, R.n, R.p, R.l, .X26, .X27, .X28, .X29].all
      (fun r ↦ (Bus.after A sF).reg r == some (.reg r)) = true ∧
    (Bus.after A sF).reg R.a = some (.reg R.s) ∧
    ((Bus.after A sF).reg .X0 = some (.reg .X0) ∨ (Bus.after A sF).reg .X0 = some (.lit 0))
  kB : keep.all (fun r ↦ (bodyOf R.a).reg r == some (.reg r)) = true
  saved : [XReg.X19, .X20, R.c, R.n, R.p, R.l, R.s].all calleeSaved = true
  evalA : ∀ env : Env, cA.eval env = (low .W32 (env.regs .X0)).getLsbD 0

end

public section

theorem keep_callee : ∀ r ∈ keep, calleeSaved r = true := by decide
theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 64 := by decide
theorem F_le : 64 ≤ tableColumnClaimsStack := by decide

/-- A register a block kept, from a list of them. -/
theorem reg_all {S : SState} {L : List XReg} (h : L.all (fun r ↦ S.reg r == some (.reg r)) = true)
    {r : XReg} (hr : r ∈ L) : S.reg r = some (.reg r) :=
  beq_iff_eq.mp (List.all_eq_true.mp h r hr)

theorem all_sub {S : SState} {L L' : List XReg}
    (h : L.all (fun r ↦ S.reg r == some (.reg r)) = true) (hs : ∀ r ∈ L', r ∈ L) :
    L'.all (fun r ↦ S.reg r == some (.reg r)) = true :=
  List.all_eq_true.mpr fun r hr ↦ beq_iff_eq.mpr (reg_all h (hs r hr))

theorem saved_of {L : List XReg} (h : L.all calleeSaved = true) {r : XReg}
    (hr : r ∈ L) : calleeSaved r = true :=
  List.all_eq_true.mp h r hr

end

end NativeRustcVmArm.Tables.ColumnClaims
