module

public import NativeRustcVmX64.Tables.TableTerms.Exec
public import NativeRustcVmX64.Tables.TableTerms.Model
public import NativeRustcVmX64.Spec.Tables

/-!
# `table_terms`: the states its proof walks through (x86-64)

From the entry state `m0`: the 272-byte frame at `fb m0` with the pushed registers (`slots`), the
outputs (`outs`: `out`, the `TState`, the evaluations' entries), the four stack arguments at
`argA m0`, the frame's words (`FW`), the model's rows and its fold over the first `i`
(`preRun`), the loop head before table `i` (`Head`), the iteration's outputs (`It`). The
precondition's parts by name (`Pre.*`).
-/

namespace NativeRustcVmX64.Tables.TableTerms

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body
open NativeRustcVm (wordOf ewsOf)

@[expose] public section

/-- The function's stack. -/
abbrev N : Nat := tableTermsStack

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 272

/-- The stack arguments' address. -/
abbrev argA (m0 : MachineData) : BitVec 64 := rspOf m0 + 8#64

/-- `out`, the `TState`, the constraint powers, the form powers, the point and its length. -/
abbrev oA (m0 : MachineData) : BitVec 64 := reg m0 .rdi
abbrev tA (m0 : MachineData) : BitVec 64 := reg m0 .rsi

/-- The heights, the forms, the weights, the evaluations' entries: the stack arguments. -/
abbrev hA (m0 : MachineData) : BitVec 64 := stackArg m0 0
abbrev fA (m0 : MachineData) : BitVec 64 := stackArg m0 1
abbrev wA (m0 : MachineData) : BitVec 64 := stackArg m0 2
abbrev ev (m0 : MachineData) : BitVec 64 := stackArg m0 3

/-- Table `i`'s evaluations' entry. -/
def evi (m0 : MachineData) (i : Nat) : BitVec 64 := ev m0 + BitVec.ofNat 64 (1968 * i)

/-- The outputs: `out`, the `TState`, the evaluations' entries. -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (oA m0) 24 q ∨ NativeRustcVm.InRange (tA m0) tstateBytes q ∨
    NativeRustcVm.InRange (ev m0) tableEvalsBytes q

/-- The regions the function writes, as `ReadIn` lists them. -/
def wsL (m0 : MachineData) : List NativeRustcVm.Region :=
  [⟨oA m0, 24⟩, ⟨tA m0, tstateBytes⟩, ⟨ev m0, tableEvalsBytes⟩, ⟨argA m0, 32⟩]

/-- The frame's words `L` (offset, value). -/
def FW (m0 d : MachineData) (L : List (Nat × UInt64)) : Prop :=
  ∀ p ∈ L, NativeRustcVm.WordAt d.dmem (off (fb m0) p.1) p.2

/-- The words `b0` stores but table `i`'s entry: `out`, the powers, the point, the `TState`. -/
def cws (m0 : MachineData) : List (Nat × UInt64) :=
  [(8, .ofBitVec (oA m0)), (24, .ofBitVec (reg m0 .rdx)), (32, .ofBitVec (reg m0 .rcx)),
    (40, .ofBitVec (reg m0 .r8)), (48, .ofBitVec (reg m0 .r9)), (56, .ofBitVec (tA m0))]

/-! ## The model's side -/

/-- The six weights. -/
def wts (m0 : MachineData) : Array EW := (ewsOf m0.dmem (wA m0) nTables).toArray
/-- The constraint powers. -/
def cpw (m0 : MachineData) : Array EW := arrE m0 (reg m0 .rdx) 2
/-- The form powers. -/
def fpw (m0 : MachineData) : Array EW := arrE m0 (reg m0 .rcx) 3
/-- The point. -/
def ptw (m0 : MachineData) : Array EW := slice m0 (reg m0 .r8) (reg m0 .r9)

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

/-- The model's result. -/
def R (heights : Array Nat) (forms : Array (Array FormW)) (m0 : MachineData) (s : TState) :
    Option ((EW × Array (Array EW × Array EW)) × TState) :=
  (tableTerms (cpw m0) (fpw m0) (ptw m0) (tableRows heights forms (wts m0))).run s

section
variable [Labels]

/-- `TABLES`' address. -/
def T : BitVec 64 := rodataAddr .tables

/-- What `table_terms` reaches. -/
abbrev Goal (a : DecArea) (s : TState) (heights : Array Nat) (forms : Array (Array FormW))
    (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
    TableTermsPost a s heights forms m0 st.data

/-- **The iteration's outputs** after table `i`'s evaluations `xs` were read, the `TState` at `s'`,
the entries before it `o`. -/
structure It (a : DecArea) (m0 : MachineData) (i : Nat) (o : Array (Array EW × Array EW))
    (xs : Array EW) (s' : TState) (d : MachineData) : Prop where
  ts : TStateAt d.dmem (tA m0) a s'
  vals : NativeRustcVm.BufEWAt d.dmem (evi m0 i + BitVec.ofNat 64 488) 92 xs.toList
  evs : ∀ j (h : j < o.size), TableEvalAt d.dmem (evi m0 j) o[j]
  osz : o.size = i

/-- **The loop head** before table `i` (`NativeRustcVmX64.Vm.TableTerms.label_1`): the body, the frame's words, the
registers walking the tables, the forms, the heights, the running sum (RDX, RCX) and the cursor
(R15); the model's fold over the first `i` rows at `acc`, `si`; the `TState` at `si`; the first
`i` entries hold their tables' points and evaluations. -/
structure Head (a : DecArea) (s : TState) (heights : Array Nat) (forms : Array (Array FormW))
    (m0 : MachineData) (i : Nat) (acc : Acc) (si : TState) (d : MachineData) : Prop where
  bd : Bd m0 272 N slots (outs m0) 8 d
  fw : FW m0 d (cws m0)
  w16 : NativeRustcVm.WordAt d.dmem (off (fb m0) 16) (.ofBitVec (evi m0 i))
  r14 : reg d .r14 = BitVec.ofNat 64 (16 + 40 * i)
  rbp : reg d .rbp = (Labels.label tablesL).toBitVec
  r13 : reg d .r13 = fA m0 + BitVec.ofNat 64 (11864 + 17784 * i)
  rax : reg d .rax = BitVec.ofNat 64 (8 * i)
  r15 : reg d .r15 = BitVec.ofNat 64 (cursorAt i)
  rdx : reg d .rdx = acc.2.1.c0.toBitVec
  rcx : reg d .rcx = acc.2.1.c1.toBitVec
  run : preRun heights forms m0 i s = some (acc, si)
  cur : acc.1 = cursorAt i
  osz : acc.2.2.size = i
  ts : TStateAt d.dmem (tA m0) a si
  evs : ∀ j (h : j < acc.2.2.size), TableEvalAt d.dmem (evi m0 j) acc.2.2[j]

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
theorem args : ArgsOk m0 4 := h.2.2.2.1
theorem ts : TStateAt m0.dmem (tA m0) a s := h.2.2.2.2.1
theorem tok : TStateOk m0 (tA m0) a N := h.2.2.2.2.2.1
theorem out : OutOk m0 (tA m0) a (oA m0) 24 N := h.2.2.2.2.2.2.1
theorem evs : OutOk m0 (tA m0) a (ev m0) tableEvalsBytes N := h.2.2.2.2.2.2.2.1
theorem out_ev : NativeRustcVm.Apart (oA m0) 24 (ev m0) tableEvalsBytes := h.2.2.2.2.2.2.2.2.1
theorem out_arg : NativeRustcVm.Apart (oA m0) 24 (argA m0) 32 := h.2.2.2.2.2.2.2.2.2.1
theorem t_arg : NativeRustcVm.Apart (tA m0) tstateBytes (argA m0) 32 := h.2.2.2.2.2.2.2.2.2.2.1
theorem ev_arg : NativeRustcVm.Apart (ev m0) tableEvalsBytes (argA m0) 32 :=
  h.2.2.2.2.2.2.2.2.2.2.2.1
theorem rt : RodataApart (tA m0) tstateBytes := h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ro : RodataApart (oA m0) 24 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem re : RodataApart (ev m0) tableEvalsBytes := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem r9 : (reg m0 .r9).toNat ≤ tablePointCap := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem cp : ReadIn m0 (reg m0 .rdx) 32 N (wsL m0) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem fp : ReadIn m0 (reg m0 .rcx) 48 N (wsL m0) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pt : ReadIn m0 (reg m0 .r8) (16 * (reg m0 .r9).toNat) N (wsL m0) :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem hs : ReadIn m0 (hA m0) 48 N (wsL m0) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem hts : HeightsAt m0.dmem (hA m0) heights := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem fs : ReadIn m0 (fA m0) formsBytes N (wsL m0) :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem fms : FormsAt m0.dmem (fA m0) forms := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ws : ReadIn m0 (wA m0) 96 N (wsL m0) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem got : GotAt m0 N [(oA m0, 24), (tA m0, tstateBytes), (a.words, 8 * a.len),
    (ev m0, tableEvalsBytes), (argA m0, 32), (reg m0 .rdx, 32), (reg m0 .rcx, 48),
    (reg m0 .r8, 16 * (reg m0 .r9).toNat), (hA m0, 48), (fA m0, formsBytes),
    (wA m0, 96), (rcAddr, 192),
    (rodataAddr .tables, NativeRustcVm.Data.Item.tables.bytes.length)] ["memcpy"] :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end

end Pre

end NativeRustcVmX64.Tables.TableTerms
