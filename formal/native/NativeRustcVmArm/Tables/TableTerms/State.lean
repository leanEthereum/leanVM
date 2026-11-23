module

public import NativeRustcVmArm.Tables.TableTerms.Exec
public import NativeRustcVmArm.Tables.TableTerms.Model
public import NativeRustcVmArm.Tables.Frame
public import NativeRustcVmArm.Tables.Common

/-!
# `table_terms`: the states its proof walks through

From the entry state `m0`: the 288-byte frame at `base m0 288` with the saved registers (`slots`),
the outputs (`outs`: `out`, the `TState`, the evaluations' entries), the frame's words
(`fw`; `cws`: what `b0` stores, `lws i`: the weight's and the height's addresses before table
`i`), the model's rows and its fold over the first `i` (`preRun`), the loop head before table
`i` (`Head`). The precondition's parts by name (`Pre.*`).
-/

namespace NativeRustcVmArm.Tables.TableTerms

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVm (wordOf ewsOf)

@[expose] public section

/-- The function's stack. -/
abbrev N : Nat := tableTermsStack

/-- The frame's saved registers. -/
abbrev slots : List (Nat × XReg) :=
  [(192, .X29), (200, .X30), (208, .X28), (216, .X27), (224, .X26), (232, .X25), (240, .X24),
    (248, .X23), (256, .X22), (264, .X21), (272, .X20), (280, .X19)]

/-- A register's value. -/
abbrev rg (m : MachineData) (r : XReg) : BitVec 64 := (m.regs.getXReg r).toBitVec

/-- The evaluations' entries: the word at SP + 8. -/
def ev (m0 : MachineData) : BitVec 64 := stackWord m0 8

/-- The weights: the word at SP. -/
def wp (m0 : MachineData) : BitVec 64 := stackWord m0 0

/-- Table `i`'s evaluations' entry. -/
def evi (m0 : MachineData) (i : Nat) : BitVec 64 := ev m0 + BitVec.ofNat 64 (1968 * i)

/-- The outputs: `out`, the `TState`, the evaluations' entries. -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange m0.regs.X0.toBitVec 24 q ∨ InRange m0.regs.X1.toBitVec tstateBytes q ∨
    InRange (ev m0) tableEvalsBytes q

/-- The frame's word at offset `o`. -/
def fw (m0 m : MachineData) (o : Nat) : BitVec 64 :=
  (wordOf m.dmem (base m0 288 + BitVec.ofNat 64 o)).toBitVec

/-- The frame's words `L` (offset, value). -/
def FW (m0 m : MachineData) (L : List (Nat × BitVec 64)) : Prop := ∀ p ∈ L, fw m0 m p.1 = p.2

/-- The words `b0` stores: `out`, the two powers, the point, the `TState`. -/
def cws (m0 : MachineData) : List (Nat × BitVec 64) :=
  [(16, rg m0 .X0), (24, rg m0 .X2), (32, rg m0 .X3), (40, rg m0 .X4), (48, rg m0 .X5),
    (56, rg m0 .X1)]

/-- The words for table `i`: the next weight's address plus `8`, the next height's. -/
def lws (m0 : MachineData) (i : Nat) : List (Nat × BitVec 64) :=
  [(96, wp m0 + BitVec.ofNat 64 (8 + 16 * i)), (104, rg m0 .X6 + BitVec.ofNat 64 (8 * i))]

/-! ## The model's side -/

/-- The six weights. -/
def wts (m0 : MachineData) : Array EW := (ewsOf m0.dmem (wp m0) nTables).toArray
/-- The constraint powers. -/
def cpw (m0 : MachineData) : Array EW := arrE m0 m0.regs.X2 2
/-- The form powers. -/
def fpw (m0 : MachineData) : Array EW := arrE m0 m0.regs.X3 3
/-- The point. -/
def ptw (m0 : MachineData) : Array EW := slice m0 m0.regs.X4 m0.regs.X5

/-- The rows. -/
def rowsL (heights : Array Nat) (forms : Array (Array FormW)) (m0 : MachineData) :
    List (TableW × Nat × Array FormW × EW) :=
  (tableRows heights forms (wts m0)).toList

/-- One table. -/
def stp (m0 : MachineData) :
    Nat × EW × Array (Array EW × Array EW) → TableW × Nat × Array FormW × EW →
      VM (Nat × EW × Array (Array EW × Array EW)) :=
  tableTermsStep (cpw m0) (fpw m0) (ptw m0)

/-- The fold over the first `i` rows. -/
def preRun (heights : Array Nat) (forms : Array (Array FormW)) (m0 : MachineData) (i : Nat)
    (s : TState) : Option ((Nat × EW × Array (Array EW × Array EW)) × TState) :=
  (((rowsL heights forms m0).take i).foldlM (stp m0) (0, 0, #[])).run s

/-- The accumulator. -/
abbrev Acc : Type := Nat × EW × Array (Array EW × Array EW)

section
variable [Labels]

/-- `TABLES`' address. -/
def T : BitVec 64 := rodataAddr .tables

/-- **The loop head** before table `i` (`.LTableTerms_1`): the frame, the frame's words, the
registers walking the tables, the evaluations, the forms, the running sum (X22, X23) and the
cursor (X26); the model's fold over the first `i` rows at `acc`, `si`; the `TState` at `si`; the
first `i` entries hold their tables' points and evaluations. -/
structure Head (a : DecArea) (s : TState) (heights : Array Nat) (forms : Array (Array FormW))
    (m0 : MachineData) (i : Nat) (acc : Acc) (si : TState) (m : MachineData) : Prop where
  fr : Fr m0 288 N slots [] (outs m0) m
  fw : FW m0 m (cws m0 ++ lws m0 i)
  x19 : rg m .X19 = T + BitVec.ofNat 64 (8 + 40 * i)
  x21 : rg m .X21 = T + BitVec.ofNat 64 (8 + 40 * i)
  x20 : rg m .X20 = rg m0 .X7 + BitVec.ofNat 64 (17784 * i)
  x27 : rg m .X27 = evi m0 i
  x29 : rg m .X29 = BitVec.ofNat 64 (240 - 40 * i)
  x26 : rg m .X26 = BitVec.ofNat 64 (cursorAt i)
  x22 : m.regs.X22 = acc.2.1.c0
  x23 : m.regs.X23 = acc.2.1.c1
  run : preRun heights forms m0 i s = some (acc, si)
  cur : acc.1 = cursorAt i
  osz : acc.2.2.size = i
  ts : TStateAt m.dmem m0.regs.X1.toBitVec a si
  evs : ∀ j (h : j < acc.2.2.size), TableEvalAt m.dmem (evi m0 j) acc.2.2[j]

end

end

/-! ## The precondition's parts -/

namespace Pre

public section

variable [Labels] {a : DecArea} {s : TState} {heights : Array Nat} {forms : Array (Array FormW)}
  {m0 : MachineData} (h : TableTermsPre a s heights forms m0)
include h

theorem stack : StackOk m0 N := h.1
theorem rc : RcAt m0 N := h.2.1
theorem tables : TablesAt m0 N := h.2.2.1
theorem args : Readable m0 m0.regs.SP.toBitVec 16 := h.2.2.2.1
theorem ts : TStateAt m0.dmem m0.regs.X1.toBitVec a s := h.2.2.2.2.1
theorem tok : TStateOk m0 m0.regs.X1.toBitVec a N := h.2.2.2.2.2.1
theorem out : OutOk m0 m0.regs.X1.toBitVec a m0.regs.X0.toBitVec 24 N := h.2.2.2.2.2.2.1
theorem evs : OutOk m0 m0.regs.X1.toBitVec a (ev m0) tableEvalsBytes N := h.2.2.2.2.2.2.2.1
theorem out_ev : Apart m0.regs.X0.toBitVec 24 (ev m0) tableEvalsBytes := h.2.2.2.2.2.2.2.2.1
theorem rt : RodataApart m0.regs.X1.toBitVec tstateBytes := h.2.2.2.2.2.2.2.2.2.1
theorem ro : RodataApart m0.regs.X0.toBitVec 24 := h.2.2.2.2.2.2.2.2.2.2.1
theorem re : RodataApart (ev m0) tableEvalsBytes := h.2.2.2.2.2.2.2.2.2.2.2.1
theorem x5 : m0.regs.X5.toNat ≤ tablePointCap := h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem cp : ReadIn m0 m0.regs.X2.toBitVec 32 N
    [⟨m0.regs.X0.toBitVec, 24⟩, ⟨m0.regs.X1.toBitVec, tstateBytes⟩, ⟨ev m0, tableEvalsBytes⟩] :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem fp : ReadIn m0 m0.regs.X3.toBitVec 48 N
    [⟨m0.regs.X0.toBitVec, 24⟩, ⟨m0.regs.X1.toBitVec, tstateBytes⟩, ⟨ev m0, tableEvalsBytes⟩] :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pt : ReadIn m0 m0.regs.X4.toBitVec (16 * m0.regs.X5.toNat) N
    [⟨m0.regs.X0.toBitVec, 24⟩, ⟨m0.regs.X1.toBitVec, tstateBytes⟩, ⟨ev m0, tableEvalsBytes⟩] :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem hs : ReadIn m0 m0.regs.X6.toBitVec 48 N
    [⟨m0.regs.X0.toBitVec, 24⟩, ⟨m0.regs.X1.toBitVec, tstateBytes⟩, ⟨ev m0, tableEvalsBytes⟩] :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem hts : HeightsAt m0.dmem m0.regs.X6.toBitVec heights :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem fs : ReadIn m0 m0.regs.X7.toBitVec formsBytes N
    [⟨m0.regs.X0.toBitVec, 24⟩, ⟨m0.regs.X1.toBitVec, tstateBytes⟩, ⟨ev m0, tableEvalsBytes⟩] :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem fms : FormsAt m0.dmem m0.regs.X7.toBitVec forms :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ws : ReadIn m0 (wp m0) 96 N
    [⟨m0.regs.X0.toBitVec, 24⟩, ⟨m0.regs.X1.toBitVec, tstateBytes⟩, ⟨ev m0, tableEvalsBytes⟩] :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end

end Pre

end NativeRustcVmArm.Tables.TableTerms
