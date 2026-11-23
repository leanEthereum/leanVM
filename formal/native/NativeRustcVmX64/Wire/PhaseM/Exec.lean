module

public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVmX64.Code.Vm.PhaseM
public import NativeRustcVmX64.Code.Vm.ClimbLevel.Names
public import NativeRustcVmX64.Code.Vm.InsD.Names
public import NativeRustcVmX64.Code.Vm.Keccak256WordsOfHashWords.Names
public import NativeRustcVmX64.Code.Vm.PhaseM.Names
public import NativeRustcVmX64.Code.Vm.RdRows.Names
public import NativeRustcVmX64.Code.Vm.ReaderLe.Names
public import NativeRustcVmX64.Code.Vm.WriteOpenings.Names
public meta import NativeRustcVmX64.Code.Vm.PhaseM
public meta import NativeRustcVmX64.Sumcheck.Common

/-!
# `phase_m`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 160-byte frame below the entry's RSP and the return address (`Frame`, `F = 160`):
the six pushed registers from `112`, the locals at `8` to `112` (RSP at offset `8` in the body, a
callee's return address at `0`). Region 1, where a block reaches into the working area, is the
part it touches, at an alias: query `i` (`qS`, R14 plus R15), the last position (`lastS`, RDI plus
`8` RBP), position `i` (`posS`, R14 plus `8` R15, the area from query `i` on), node `i` (`nodeS`,
R14 plus `8` R13), level `l`'s count (`cntS`, R11 plus `8` R13). `write_openings`' call pushes its
four stack arguments below the frame: there region 0 is the 192 bytes below the entry's RSP
(`woS`, `woS'`).
-/

namespace NativeRustcVmX64.Wire.PhaseM

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.PhaseM
open NativeRustcVmX64.Transcript (Slots after after_eq ProOk MidOk EpiOk)
open NativeRustcVmX64.Sumcheck (WordW WordsW)

@[expose] public section

/-- The frame's slots: the pushed registers. -/
def slots : Slots := [(152, .rbp), (144, .r15), (136, .r14), (128, .r13), (120, .r12), (112, .rbx)]

/-- The slots in the 192 bytes below the entry's RSP. -/
def slotsW : Slots := slots.map fun p ↦ (p.1 + 32, p.2)

/-- At the entry: the frame, RSP at its end. -/
def entryS : SState := init [168] [(.rsp, .ptr 0 160)]

/-- In the frame, RSP at its offset `8`. -/
def frS : SState := init [168] [(.rsp, .ptr 0 8)]

/-- At the epilogue's pops, RSP at the slots. -/
def epiS : SState := init [168] [(.rsp, .ptr 0 112)]

/-- Query `i`'s address: R14 plus R15. -/
def qAddr : Sym := .bin .add .W64 (.reg .r14) (.reg .r15)

/-- Query `i` (region 1, 8 bytes). -/
def qS : SState := init [168, 8] [(.rsp, .ptr 0 8)] (aliases := [(qAddr, 1, 0)])

/-- Past the last position: RDI plus `8` RBP. -/
def lastAddr : Sym := .bin .add .W64 (.reg .rdi) (.bin .mul .W64 (.reg .rbp) (.lit 8))

/-- The last position (region 1, 8 bytes). -/
def lastS : SState := init [168, 8] [(.rsp, .ptr 0 8)] (aliases := [(lastAddr, 1, 8)])

/-- Query `i`'s address, scaled: R14 plus `8` R15. -/
def posAddr : Sym := .bin .add .W64 (.reg .r14) (.bin .mul .W64 (.reg .r15) (.lit 8))

/-- From query `i` to position `i` (region 1, 2056 bytes). -/
def posS : SState := init [168, 2056] [(.rsp, .ptr 0 8)] (aliases := [(posAddr, 1, 0)])

/-- Node `i`'s address plus 8: R14 plus `8` R13. -/
def nodeAddr : Sym := .bin .add .W64 (.reg .r14) (.bin .mul .W64 (.reg .r13) (.lit 8))

/-- Node `i` (region 1, 40 bytes). -/
def nodeS : SState := init [168, 40] [(.rsp, .ptr 0 8)] (aliases := [(nodeAddr, 1, 8)])

/-- Level `l`'s siblings: R11 plus `8` R13. -/
def cntAddr : Sym := .bin .add .W64 (.reg .r11) (.bin .mul .W64 (.reg .r13) (.lit 8))

/-- Level `l`'s count (region 1, 8 bytes). -/
def cntS : SState := init [168, 8] [(.rsp, .ptr 0 8)] (aliases := [(cntAddr, 1, 256)])

/-- Before `write_openings`' arguments: the 192 bytes below the entry's RSP, RSP at `40`. -/
def woS : SState := init [200] [(.rsp, .ptr 0 40)]

/-- After `write_openings`: RSP at `8` of the 192 bytes. -/
def woS' : SState := init [200] [(.rsp, .ptr 0 8)]

/-- A block from `frS` keeping memory and the callee-saved registers, RSP at `8`. -/
def FrOk (S : SState) : Bool := MidOk 160 8 slots S && S.mem.isEmpty

/-- `b1`'s test: the count read and below `257`. -/
def c1 : SBool :=
  let cl := Sym.bin .merge .W8 (.reg .rcx)
    (.ite (.cmp .ult .W64 (.reg .rdx) (.lit 257)) (.lit 1) (.lit 0))
  (SBool.cmp .eq .W8 (.bin .merge .W8 cl (.bin .and .W8 cl (.reg .rax))) (.lit 1)).not

/-- `b12`'s test: the row width read and a query. -/
def c12 : SBool :=
  let a := Sym.bin .merge .W8 (.reg .rax) (.un .not .W8 (.reg .rax))
  (SBool.cmp .eq .W8 (.bin .and .W8 (.bin .merge .W8 a (.bin .or .W8 a (.reg .rbp))) (.lit 1))
    (.lit 0)).not

/-- `b24`'s test: the rows read, and not all zero where there are words. -/
def c24 : SBool :=
  let d := Sym.bin .merge .W8 (.reg .rdx)
    (.ite (SBool.cmp .eq .W64 (.bin .and .W64 (.reg .r15) (.reg .r15)) (.lit 0)).not (.lit 1) (.lit 0))
  (SBool.cmp .eq .W8 (.bin .or .W8 (.bin .merge .W8 d (.bin .and .W8 d (.reg .rax)))
    (.bin .merge .W8 (.reg .rcx) (.ite (.cmp .eq .W8 (.reg .rax) (.lit 2)) (.lit 1) (.lit 0))))
    (.lit 0)).not

/-- `x > y`, as the blocks test it (`ja`). -/
def gtC (x y : Sym) : SBool := (SBool.cmp .ult .W64 x y).not.and (SBool.cmp .eq .W64 x y).not

/-- `8 count`, as `b2` computes it. -/
def eightC : Sym := .bin .mul .W64 (.load 0 40 8) (.lit 8)

/-- A block from `frS` calling `Reader::le` for four bytes. -/
def LeOk (S : SState) : Prop :=
  MidOk 160 0 slots S = true ∧ (∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    S.reg .rsi = some (.lit 4) ∧ S.reg .rdi = some (.reg .r12) ∧
    (∀ x ∈ [Reg64.r12, .r13, .r14, .r15], S.reg x = some (.reg x))

instance (S : SState) : Decidable (LeOk S) := by unfold LeOk; infer_instance

/-- `climb_level`'s nodes, by the level's parity. -/
def evenSel (a b : Sym) : Sym :=
  .ite (.cmp .eq .W8 (.bin .and .W8 (.reg .r13) (.lit 1)) (.lit 0)) a b

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 frS
sym_block run_b2 := exec b2 frS
sym_block run_b3 := exec b3 frS
sym_block run_b4 := exec b4 frS
sym_block run_b5 := exec b5 frS
sym_block run_b6 := exec b6 qS
sym_block run_b7 := exec b7 frS
sym_block run_b8 := exec b8 frS
sym_block run_b9 := exec b9 frS
sym_block run_b10 := exec b10 frS
sym_block run_b11 := exec b11 frS
sym_block run_b12 := exec b12 frS
sym_block run_b13 := exec b13 frS
sym_block run_b14 := exec b14 qS
sym_block run_b15 := exec b15 frS
sym_block run_b16 := exec b16 frS
sym_block run_b17 := exec b17 frS
sym_block run_b18 := exec b18 epiS
sym_block run_b19 := exec b19 lastS
sym_block run_b20 := exec b20 frS
sym_block run_b21 := exec b21 frS
sym_block run_b22 := exec b22 frS
sym_block run_b23 := exec b23 frS
sym_block run_b24 := exec b24 frS
sym_block run_b25 := exec b25 frS
sym_block run_b26 := exec b26 posS
sym_block run_b27 := exec b27 nodeS
sym_block run_b28 := exec b28 frS
sym_block run_b29 := exec b29 frS
sym_block run_b30 := exec b30 frS
sym_block run_b31 := exec b31 frS
sym_block run_b32 := exec b32 frS
sym_block run_b33 := exec b33 cntS
sym_block run_b34 := exec b34 frS
sym_block run_b35 := exec b35 frS
sym_block run_b36 := exec b36 woS
sym_block run_b37 := exec b37 woS'


public theorem exit_b0 : exec b0 entryS = some (after b0 entryS, .call NativeRustcVmX64.Vm.ReaderLe.entryLabel) :=
  run_b0.trans (by rw [after_eq run_b0])
public theorem ok_b0 : ProOk 160 0 slots (after b0 entryS) = true ∧
    WordW 0 48 (.reg .rsi) (after b0 entryS) ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ 48 ≤ w.off ∧ w.off + w.n ≤ 56 ∨
      112 ≤ w.off ∧ w.off + w.n ≤ 160)) ∧
    (after b0 entryS).reg .rsi = some (.lit 4) ∧ (after b0 entryS).reg .rdi = some (.reg .rdi) ∧
    (after b0 entryS).reg .r12 = some (.reg .rdi) ∧ (after b0 entryS).reg .r14 = some (.reg .rdx) := by
  decide +kernel

public theorem exit_b1 : exec b1 frS = some (after b1 frS, .cond c1 NativeRustcVmX64.Vm.PhaseM.label_23) :=
  run_b1.trans (by rw [after_eq run_b1]; rfl)
public theorem ok_b1 : MidOk 160 8 slots (after b1 frS) = true ∧
    (after b1 frS).mem = [⟨0, 40, 8, .reg .rdx⟩] ∧ WordW 0 40 (.reg .rdx) (after b1 frS) ∧
    (∀ x ∈ [Reg64.r12, .r14], (after b1 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b2 : exec b2 frS = some (after b2 frS,
    .cond (SBool.cmp .eq .W64 (.bin .and .W64 (.load 0 40 8) (.load 0 40 8)) (.lit 0))
      NativeRustcVmX64.Vm.PhaseM.label_5) :=
  run_b2.trans (by rw [after_eq run_b2])
public theorem ok_b2 : FrOk (after b2 frS) = true ∧ (after b2 frS).reg .r13 = some eightC ∧
    (∀ x ∈ [Reg64.r12, .r14], (after b2 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b3 : exec b3 frS = some (after b3 frS, .fall) :=
  run_b3.trans (by rw [after_eq run_b3])
public theorem ok_b3 : FrOk (after b3 frS) = true ∧ (after b3 frS).reg .r15 = some (.lit 0) ∧
    (∀ x ∈ [Reg64.r12, .r13, .r14], (after b3 frS).reg x = some (.reg x)) := by
  decide +kernel


public theorem exit_b4 : exec b4 frS = some (after b4 frS, .call NativeRustcVmX64.Vm.ReaderLe.entryLabel) :=
  run_b4.trans (by rw [after_eq run_b4])
public theorem ok_b4 : LeOk (after b4 frS) := by decide +kernel

public theorem exit_b5 : exec b5 frS = some (after b5 frS,
    .cond (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.lit 1)) (.lit 0)) NativeRustcVmX64.Vm.PhaseM.label_23) :=
  run_b5.trans (by rw [after_eq run_b5])
public theorem ok_b5 : FrOk (after b5 frS) = true ∧
    (∀ x ∈ [Reg64.rdx, .r12, .r13, .r14, .r15], (after b5 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b6 : exec b6 qS = some (after b6 qS,
    .cond (SBool.cmp .eq .W64 (.reg .r13) (.bin .add .W64 (.lit 8) (.reg .r15))).not
      NativeRustcVmX64.Vm.PhaseM.label_3) :=
  run_b6.trans (by rw [after_eq run_b6])
public theorem ok_b6 : MidOk 160 8 slots (after b6 qS) = true ∧
    (after b6 qS).mem = [⟨1, 0, 8, .reg .rdx⟩] ∧ WordW 1 0 (.reg .rdx) (after b6 qS) ∧
    (after b6 qS).reg .r15 = some (.bin .add .W64 (.lit 8) (.reg .r15)) ∧
    (∀ x ∈ [Reg64.r12, .r13, .r14], (after b6 qS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b7 : exec b7 frS = some (after b7 frS, .call NativeRustcVmX64.Vm.ReaderLe.entryLabel) :=
  run_b7.trans (by rw [after_eq run_b7])
public theorem ok_b7 : LeOk (after b7 frS) := by decide +kernel

public theorem exit_b8 : exec b8 frS = some (after b8 frS,
    .cond (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.lit 1)) (.lit 0)) NativeRustcVmX64.Vm.PhaseM.label_23) :=
  run_b8.trans (by rw [after_eq run_b8])
public theorem ok_b8 : MidOk 160 8 slots (after b8 frS) = true ∧
    (after b8 frS).mem = [⟨0, 32, 8, .reg .rdx⟩] ∧ WordW 0 32 (.reg .rdx) (after b8 frS) ∧
    (∀ x ∈ [Reg64.r12, .r13, .r14], (after b8 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b9 : exec b9 frS = some (after b9 frS, .call NativeRustcVmX64.Vm.ReaderLe.entryLabel) :=
  run_b9.trans (by rw [after_eq run_b9])
public theorem ok_b9 : LeOk (after b9 frS) := by decide +kernel

public theorem exit_b10 : exec b10 frS = some (after b10 frS,
    .cond (SBool.cmp .eq .W64 (.reg .rax) (.lit 1)).not NativeRustcVmX64.Vm.PhaseM.label_23) :=
  run_b10.trans (by rw [after_eq run_b10])
public theorem ok_b10 : MidOk 160 8 slots (after b10 frS) = true ∧
    (after b10 frS).mem = [⟨0, 16, 8, .reg .rdx⟩] ∧ WordW 0 16 (.reg .rdx) (after b10 frS) ∧
    (∀ x ∈ [Reg64.r12, .r13, .r14], (after b10 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b11 : exec b11 frS = some (after b11 frS, .call NativeRustcVmX64.Vm.ReaderLe.entryLabel) :=
  run_b11.trans (by rw [after_eq run_b11])
public theorem ok_b11 : MidOk 160 0 slots (after b11 frS) = true ∧
    (∀ w ∈ (after b11 frS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b11 frS).reg .rsi = some (.lit 4) ∧ (after b11 frS).reg .rdi = some (.reg .r12) ∧
    (after b11 frS).reg .rbp = some (.bin .merge .W8 (.reg .rbp)
      (.ite (.cmp .eq .W64 (.load 0 40 8) (.lit 0)) (.lit 1) (.lit 0))) ∧
    (∀ x ∈ [Reg64.r12, .r13, .r14], (after b11 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b12 : exec b12 frS = some (after b12 frS, .cond c12 NativeRustcVmX64.Vm.PhaseM.label_23) :=
  run_b12.trans (by rw [after_eq run_b12]; rfl)
public theorem ok_b12 : FrOk (after b12 frS) = true ∧
    (∀ x ∈ [Reg64.rdx, .r12, .r13, .r14], (after b12 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b13 : exec b13 frS = some (after b13 frS, .fall) :=
  run_b13.trans (by rw [after_eq run_b13])
public theorem ok_b13 : MidOk 160 8 slots (after b13 frS) = true ∧
    (after b13 frS).mem = [⟨0, 24, 8, .reg .rdx⟩] ∧ WordW 0 24 (.reg .rdx) (after b13 frS) ∧
    (after b13 frS).reg .rdi = some (.bin .add .W64 (.reg .r14) (.lit 2048)) ∧
    (after b13 frS).reg .rbp = some (.lit 0) ∧ (after b13 frS).reg .r15 = some (.lit 0) ∧
    (∀ x ∈ [Reg64.r12, .r13, .r14], (after b13 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b14 : exec b14 qS = some (after b14 qS,
    .call NativeRustcVmX64.Vm.InsD.entryLabel) :=
  run_b14.trans (by rw [after_eq run_b14])
public theorem ok_b14 : MidOk 160 0 slots (after b14 qS) = true ∧
    (∀ w ∈ (after b14 qS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b14 qS).reg .rbx = some (.reg .rdi) ∧ (after b14 qS).reg .rdx = some (.load 1 0 8) ∧
    (after b14 qS).reg .rsi = some (.reg .rbp) ∧ (after b14 qS).reg .rdi = some (.reg .rdi) ∧
    (∀ x ∈ [Reg64.r12, .r13, .r14, .r15], (after b14 qS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b15 : exec b15 frS = some (after b15 frS,
    .cond (SBool.cmp .eq .W64 (.reg .r13) (.bin .add .W64 (.lit 8) (.reg .r15))).not
      NativeRustcVmX64.Vm.PhaseM.label_9) :=
  run_b15.trans (by rw [after_eq run_b15])
public theorem ok_b15 : FrOk (after b15 frS) = true ∧
    (after b15 frS).reg .rdi = some (.reg .rbx) ∧ (after b15 frS).reg .rbp = some (.reg .rax) ∧
    (after b15 frS).reg .r15 = some (.bin .add .W64 (.lit 8) (.reg .r15)) ∧
    (∀ x ∈ [Reg64.r12, .r13, .r14], (after b15 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b16 : exec b16 frS = some (after b16 frS,
    .cond (SBool.cmp .ult .W64 (.bin .add .W64 (.reg .rbp) (.lit 18446744073709551359))
      (.lit 18446744073709551360)).not NativeRustcVmX64.Vm.PhaseM.label_11) :=
  run_b16.trans (by rw [after_eq run_b16])
public theorem ok_b16 : FrOk (after b16 frS) = true ∧
    (after b16 frS).reg .r15 = some (.load 0 24 8) ∧
    (∀ x ∈ [Reg64.rdi, .rbp, .r12, .r14], (after b16 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b17 : exec b17 frS = some (after b17 frS, .fall) :=
  run_b17.trans (by rw [after_eq run_b17])
public theorem ok_b17 : MidOk 160 112 slots (after b17 frS) = true ∧ (after b17 frS).mem = [] ∧
    (after b17 frS).reg .rax = some (.lit 0) := by
  decide +kernel

public theorem exit_b18 : exec b18 epiS = some (after b18 epiS, .ret (.load 0 160 8)) :=
  run_b18.trans (by rw [after_eq run_b18])
public theorem ok_b18 : EpiOk 160 slots (after b18 epiS) = true ∧ (after b18 epiS).mem = [] ∧
    (after b18 epiS).reg .rax = some (.reg .rax) := by
  decide +kernel

public theorem exit_b19 : exec b19 lastS = some (after b19 lastS,
    .cond (gtC (.load 0 32 8) (.lit 32)) NativeRustcVmX64.Vm.PhaseM.label_23) :=
  run_b19.trans (by rw [after_eq run_b19]; rfl)
public theorem ok_b19 : MidOk 160 8 slots (after b19 lastS) = true ∧ (after b19 lastS).mem = [] ∧
    (after b19 lastS).reg .rax = some (.bin .shr .W64 (.load 1 0 8) (.load 0 32 8)) ∧
    (∀ x ∈ [Reg64.rdi, .rbp, .r12, .r14, .r15], (after b19 lastS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b20 : exec b20 frS = some (after b20 frS,
    .cond (gtC (.load 0 16 8) (.lit 64)) NativeRustcVmX64.Vm.PhaseM.label_23) :=
  run_b20.trans (by rw [after_eq run_b20]; rfl)
public theorem ok_b20 : FrOk (after b20 frS) = true ∧
    (∀ x ∈ [Reg64.rax, .rdi, .rbp, .r12, .r14, .r15], (after b20 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b21 : exec b21 frS = some (after b21 frS,
    .cond (gtC (.reg .r15) (.load 0 16 8)) NativeRustcVmX64.Vm.PhaseM.label_23) :=
  run_b21.trans (by rw [after_eq run_b21]; rfl)
public theorem ok_b21 : FrOk (after b21 frS) = true ∧
    (∀ x ∈ [Reg64.rax, .rdi, .rbp, .r12, .r14, .r15], (after b21 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b22 : exec b22 frS = some (after b22 frS,
    .cond (SBool.cmp .eq .W64 (.bin .and .W64 (.reg .rax) (.reg .rax)) (.lit 0)).not
      NativeRustcVmX64.Vm.PhaseM.label_23) :=
  run_b22.trans (by rw [after_eq run_b22])
public theorem ok_b22 : FrOk (after b22 frS) = true ∧
    (∀ x ∈ [Reg64.rdi, .rbp, .r12, .r14, .r15], (after b22 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b23 : exec b23 frS = some (after b23 frS,
    .call NativeRustcVmX64.Vm.RdRows.entryLabel) :=
  run_b23.trans (by rw [after_eq run_b23])
public theorem ok_b23 : MidOk 160 0 slots (after b23 frS) = true ∧
    (∀ w ∈ (after b23 frS).mem, w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ 56 ≤ w.off ∧ w.off + w.n ≤ 64)) ∧
    WordW 0 56 (.bin .add .W64 (.reg .r14) (.lit 352512)) (after b23 frS) ∧
    (after b23 frS).reg .rdi = some (.reg .r12) ∧ (after b23 frS).reg .rsi = some (.reg .rbp) ∧
    (after b23 frS).reg .rdx = some (.load 0 16 8) ∧ (after b23 frS).reg .rcx = some (.reg .r15) ∧
    (after b23 frS).reg .r8 = some (.bin .add .W64 (.reg .r14) (.lit 352512)) ∧
    (∀ x ∈ [Reg64.rdi, .rbp, .r12, .r14, .r15], (after b23 frS).reg x = some (.reg x) ∨ x = .rdi) := by
  decide +kernel

public theorem exit_b24 : exec b24 frS = some (after b24 frS, .cond c24 NativeRustcVmX64.Vm.PhaseM.label_23) :=
  run_b24.trans (by rw [after_eq run_b24]; rfl)
public theorem ok_b24 : FrOk (after b24 frS) = true ∧
    (∀ x ∈ [Reg64.rbp, .r12, .r14, .r15], (after b24 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b25 : exec b25 frS = some (after b25 frS, .fall) :=
  run_b25.trans (by rw [after_eq run_b25])
public theorem ok_b25 : MidOk 160 8 slots (after b25 frS) = true ∧
    (after b25 frS).mem = [⟨0, 64, 8, .bin .shl .W64 (.load 0 16 8) (.lit 3)⟩] ∧
    WordW 0 64 (.bin .shl .W64 (.load 0 16 8) (.lit 3)) (after b25 frS) ∧
    (after b25 frS).reg .rcx = some (.bin .add .W64 (.reg .r14) (.lit 352512)) ∧
    (after b25 frS).reg .r9 = some (.load 0 16 8) ∧ (after b25 frS).reg .r13 = some (.lit 513) ∧
    (after b25 frS).reg .r15 = some (.lit 0) ∧
    (∀ x ∈ [Reg64.rbp, .r12, .r14], (after b25 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b26 : exec b26 posS = some (after b26 posS,
    .call NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.entryLabel) :=
  run_b26.trans (by rw [after_eq run_b26])
public theorem ok_b26 : MidOk 160 0 slots (after b26 posS) = true ∧
    (∀ w ∈ (after b26 posS).mem, w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ 24 ≤ w.off ∧ w.off + w.n ≤ 32 ∨
      72 ≤ w.off ∧ w.off + w.n ≤ 80)) ∧
    WordW 0 72 (.load 1 2048 8) (after b26 posS) ∧ WordW 0 24 (.reg .rcx) (after b26 posS) ∧
    (after b26 posS).reg .rdi = some (.ptr 0 80) ∧ (after b26 posS).reg .rsi = some (.reg .r9) ∧
    (after b26 posS).reg .rdx = some (.load 0 64 8) ∧ (after b26 posS).reg .rcx = some (.reg .rcx) ∧
    (after b26 posS).reg .r8 = some (.reg .r9) ∧
    (after b26 posS).reg .r15 = some (.bin .add .W64 (.reg .r15) (.lit 1)) ∧
    (∀ x ∈ [Reg64.rbp, .r12, .r13, .r14], (after b26 posS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b27 : exec b27 nodeS = some (after b27 nodeS,
    .cond (SBool.cmp .eq .W64 (.reg .rbp) (.reg .r15)).not NativeRustcVmX64.Vm.PhaseM.label_17) :=
  run_b27.trans (by rw [after_eq run_b27])
public theorem ok_b27 : MidOk 160 8 slots (after b27 nodeS) = true ∧
    (∀ w ∈ (after b27 nodeS).mem, w.r = 1 ∧ w.off + w.n ≤ 40) ∧
    WordW 1 0 (.load 0 72 8) (after b27 nodeS) ∧
    WordsW 1 8 (fun i ↦ .load 0 (80 + 8 * i) 8) (after b27 nodeS) ∧
    (after b27 nodeS).reg .rcx = some (.bin .add .W64 (.lit 512) (.load 0 24 8)) ∧
    (after b27 nodeS).reg .r9 = some (.load 0 16 8) ∧
    (after b27 nodeS).reg .r13 = some (.bin .add .W64 (.lit 5) (.reg .r13)) ∧
    (∀ x ∈ [Reg64.rbp, .r12, .r14, .r15], (after b27 nodeS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b28 : exec b28 frS = some (after b28 frS,
    .cond (SBool.cmp .eq .W64 (.load 0 32 8) (.lit 0)) NativeRustcVmX64.Vm.PhaseM.label_19) :=
  run_b28.trans (by rw [after_eq run_b28])
public theorem ok_b28 : FrOk (after b28 frS) = true ∧
    (after b28 frS).reg .r11 = some (.bin .add .W64 (.reg .r14) (.lit 24832)) ∧
    (∀ x ∈ [Reg64.rbx, .rbp, .r12, .r14], (after b28 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b29 : exec b29 frS = some (after b29 frS, .fall) :=
  run_b29.trans (by rw [after_eq run_b29])
public theorem ok_b29 : FrOk (after b29 frS) = true ∧ (after b29 frS).reg .rdx = some (.reg .rbp) ∧
    (after b29 frS).reg .rdi = some (.lit 0) ∧ (after b29 frS).reg .r13 = some (.lit 0) ∧
    (∀ x ∈ [Reg64.rbx, .rbp, .r11, .r12, .r14], (after b29 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b30 : exec b30 frS = some (after b30 frS,
    .cond (SBool.cmp .ult .W64 (.reg .rdx) (.lit 257)).not NativeRustcVmX64.Vm.PhaseM.label_23) :=
  run_b30.trans (by rw [after_eq run_b30])
public theorem ok_b30 : FrOk (after b30 frS) = true ∧
    (∀ x ∈ [Reg64.rbx, .rbp, .rdx, .rdi, .r11, .r12, .r13, .r14], (after b30 frS).reg x =
      some (.reg x)) := by
  decide +kernel

public theorem exit_b31 : exec b31 frS = some (after b31 frS,
    .call NativeRustcVmX64.Vm.ClimbLevel.entryLabel) :=
  run_b31.trans (by rw [after_eq run_b31])
public theorem ok_b31 : MidOk 160 0 slots (after b31 frS) = true ∧
    (∀ w ∈ (after b31 frS).mem, w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ 24 ≤ w.off ∧ w.off + w.n ≤ 32)) ∧
    WordW 0 24 (.reg .rdi) (after b31 frS) ∧
    (after b31 frS).reg .rdi = some (.reg .r12) ∧
    (after b31 frS).reg .rsi = some (evenSel (.bin .add .W64 (.reg .r14) (.lit 4096))
      (.bin .add .W64 (.reg .r14) (.lit 14336))) ∧
    (after b31 frS).reg .r8 = some (evenSel (.bin .add .W64 (.reg .r14) (.lit 14336))
      (.bin .add .W64 (.reg .r14) (.lit 4096))) ∧
    (after b31 frS).reg .rcx = some (.bin .add .W64 (.reg .r11) (.reg .rdi)) ∧
    (after b31 frS).reg .r15 = some (.reg .rdx) ∧
    (∀ x ∈ [Reg64.rbx, .rbp, .rdx, .r12, .r13, .r14], (after b31 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b32 : exec b32 frS = some (after b32 frS,
    .cond (SBool.cmp .eq .W64 (.reg .rax) (.lit 1)).not NativeRustcVmX64.Vm.PhaseM.label_23) :=
  run_b32.trans (by rw [after_eq run_b32])
public theorem ok_b32 : FrOk (after b32 frS) = true ∧ (after b32 frS).reg .rdi = some (.load 0 24 8) ∧
    (after b32 frS).reg .r11 = some (.bin .add .W64 (.reg .r14) (.lit 24832)) ∧
    (∀ x ∈ [Reg64.rbx, .rbp, .rdx, .r12, .r13, .r14, .r15], (after b32 frS).reg x =
      some (.reg x)) := by
  decide +kernel

public theorem exit_b33 : exec b33 cntS = some (after b33 cntS,
    .cond (SBool.cmp .eq .W64 (.load 0 32 8) (.bin .add .W64 (.reg .r13) (.lit 1))).not
      NativeRustcVmX64.Vm.PhaseM.label_22) :=
  run_b33.trans (by rw [after_eq run_b33])
public theorem ok_b33 : MidOk 160 8 slots (after b33 cntS) = true ∧
    (after b33 cntS).mem = [⟨1, 0, 8, .reg .r15⟩] ∧ WordW 1 0 (.reg .r15) (after b33 cntS) ∧
    (after b33 cntS).reg .rdi = some (.bin .add .W64 (.lit 10240) (.reg .rdi)) ∧
    (after b33 cntS).reg .r10 = some (.load 0 32 8) ∧
    (after b33 cntS).reg .r13 = some (.bin .add .W64 (.reg .r13) (.lit 1)) ∧
    (∀ x ∈ [Reg64.rbx, .rbp, .rdx, .r11, .r12, .r14], (after b33 cntS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b34 : exec b34 frS = some (after b34 frS, .jump NativeRustcVmX64.Vm.PhaseM.label_20) :=
  run_b34.trans (by rw [after_eq run_b34])
public theorem ok_b34 : FrOk (after b34 frS) = true ∧ (after b34 frS).reg .rcx = some (.reg .rbx) ∧
    (after b34 frS).reg .r9 = some (.load 0 16 8) ∧ (after b34 frS).reg .r15 = some (.load 0 48 8) ∧
    (∀ x ∈ [Reg64.rbp, .r10, .r11, .r12, .r14], (after b34 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b35 : exec b35 frS = some (after b35 frS, .fall) :=
  run_b35.trans (by rw [after_eq run_b35])
public theorem ok_b35 : FrOk (after b35 frS) = true ∧ (after b35 frS).reg .rcx = some (.reg .rbx) ∧
    (after b35 frS).reg .r10 = some (.lit 0) ∧ (after b35 frS).reg .r15 = some (.load 0 48 8) ∧
    (∀ x ∈ [Reg64.r9, .rbp, .r11, .r12, .r14], (after b35 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b36 : exec b36 woS = some (after b36 woS,
    .call NativeRustcVmX64.Vm.WriteOpenings.entryLabel) :=
  run_b36.trans (by rw [after_eq run_b36])
public theorem ok_b36 : MidOk 192 0 slotsW (after b36 woS) = true ∧
    (∀ w ∈ (after b36 woS).mem, w.r = 0 ∧ w.off + w.n ≤ 40) ∧
    WordW 0 8 (.reg .r10) (after b36 woS) ∧ WordW 0 16 (.reg .r11) (after b36 woS) ∧
    WordW 0 24 (.bin .add .W64 (.reg .r14) (.lit 24576)) (after b36 woS) ∧
    WordW 0 32 (.reg .r15) (after b36 woS) ∧
    (after b36 woS).reg .rdi = some (.reg .r14) ∧ (after b36 woS).reg .rsi = some (.load 0 72 8) ∧
    (after b36 woS).reg .rdx = some (.reg .rcx) ∧ (after b36 woS).reg .rcx = some (.reg .rbp) ∧
    (after b36 woS).reg .r8 = some (.load 0 88 8) ∧ (after b36 woS).reg .r9 = some (.reg .r9) := by
  decide +kernel

public theorem exit_b37 : exec b37 woS' = some (after b37 woS', .jump NativeRustcVmX64.Vm.PhaseM.label_24) :=
  run_b37.trans (by rw [after_eq run_b37])
public theorem ok_b37 : MidOk 192 144 slotsW (after b37 woS') = true ∧ (after b37 woS').mem = [] ∧
    (after b37 woS').reg .rax = some (.reg .rax) := by
  decide +kernel

end NativeRustcVmX64.Wire.PhaseM
