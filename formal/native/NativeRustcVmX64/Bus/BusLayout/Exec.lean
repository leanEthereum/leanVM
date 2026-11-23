module

public import NativeRustcVmX64.Bus.Facts
public import NativeRustcVmX64.Code.Vm.BusLayout
public import NativeRustcVmX64.Code.Vm.BusLayout.Names
public meta import NativeRustcVmX64.Code.Vm.BusLayout
public meta import NativeRustcVmX64.Transcript.Frame

namespace NativeRustcVmX64.Bus.BusLayout

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.BusLayout
open NativeRustcVmX64.Transcript NativeRustcVmX64.Bus

@[expose] public section

def slots : Slots :=
  [(1800, .rbp), (1792, .r15), (1784, .r14), (1776, .r13), (1768, .r12), (1760, .rbx)]

def gotS (o : Nat) (l : Label) : SState :=
  (init [1816, 8] [(.rsp, .ptr 0 o)] [] [] [(.gotSlot l, 1, 0)]).withKnownBytes
    1 0 8 (.label l)

def entryS : SState := gotS 1808 "memset"
def midS : SState := init [1816] [(.rsp, .ptr 0 8)]
def fwS (k : Nat) : SState := init [1816, 8 * k] [(.rsp, .ptr 0 8), (.r15, .ptr 1 0)]

def keyP : Sym := .bin .add .W64 (.reg .rax) (.bin .mul .W64 (.reg .rcx) (.lit 8))
def keyO : Sym := .bin .add .W64 (.reg .r13) (.bin .shl .W64 (.reg .rcx) (.lit 4))
def plS : SState := init [1816] [(.rsp, .ptr 0 8), (.rax, .ptr 0 24)] [] [(.reg .rcx, 54)]

def keyF : Sym := .bin .add .W64 (.reg .rax) (.bin .shl .W64 (.reg .rdx) (.lit 4))
def fS : SState := init [16] [] [] [] [(keyF, 0, 0)]

def keyT : Sym := .bin .add .W64 (.reg .rax) (.bin .shl .W64 (.reg .r8) (.lit 4))
def tS : SState := init [72] [] [] [] [(keyT, 0, 0)]

def sB : SState := init [32] [(.rsi, .ptr 0 16)]
def sH : SState := init [16, 72] [(.r12, .ptr 1 0), (.rdi, .var 0)] [] [(.var 0, 6)] [(keyP, 0, 0)]
def sH7 : SState := init [72] [(.r12, .ptr 0 0), (.rdi, .var 0)] [] [(.var 0, 6)]
def sT : SState := init [16] [] [] [] [(keyP, 0, 0)]
def sO : SState := init [16] [] [] [] [(keyO, 0, 0)]
def sH17 : SState := init [72] [(.r12, .ptr 0 0), (.rdx, .var 0)] [] [(.var 0, 6)]

def outS : SState := init [1816, 8] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 midS
sym_block run_b2 := exec b2 (fwS 1)
sym_block run_b3 := exec b3 (fwS 2)
sym_block run_b4 := exec b4 (fwS 3)
sym_block run_b5 := exec b5 midS
sym_block run_b15 := exec b15 midS
sym_block run_b9 := exec b9 sB
sym_block run_b10a := exec (b10.take 2) sH
sym_block run_b10b := exec (b10.drop 2) sB
sym_block run_b7 := exec b7 sH7
sym_block run_b8 := exec b8 sT
sym_block run_b16 := exec b16 sO
sym_block run_b17 := exec b17 sH17
sym_block run_b19 := exec b19 sT
sym_block run_b20 := exec b20 (gotS 8 "memset")
sym_block run_b21 := exec b21 midS
sym_block run_b22 := exec b22 midS
sym_block run_b23 := exec b23 midS
sym_block run_b25 := exec b25 plS
sym_block run_b26 := exec b26 plS
sym_block run_b27 := exec b27 plS
sym_block run_b28 := exec b28 fS
sym_block run_b30 := exec b30 midS
sym_block run_b31a := exec (b31.take 4) tS
sym_block run_b31b := exec (b31.drop 4) midS
sym_block run_b33 := exec b33 (gotS 8 "memcpy")
sym_block run_b34 := exec b34 outS
sym_block run_b35 := exec b35 (after b34 outS)

public theorem ok_b0 : ProOk 1808 0 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0) ∧
    (after b0 entryS).reg .rdi = some (.ptr 0 896) ∧ (after b0 entryS).reg .rdx = some (.lit 432) ∧
    (after b0 entryS).reg .rsi = some (.lit 0) ∧ (after b0 entryS).reg .rbx = some (.reg .rdi) ∧
    (after b0 entryS).reg .rbp = some (.reg .r8) ∧ (after b0 entryS).reg .r12 = some (.reg .r9) ∧
    (after b0 entryS).reg .r13 = some (.reg .rcx) ∧ (after b0 entryS).reg .r14 = some (.reg .rdx) ∧
    (after b0 entryS).reg .r15 = some (.reg .rsi) := by
  decide +kernel

public theorem ok_b1 : MidOk 1808 8 slots (after b1 midS) = true ∧ (after b1 midS).mem = [] ∧
    Keeps [.rbx, .rbp, .r12, .r13, .r14, .r15] (after b1 midS) := by
  decide +kernel

public theorem ok_b234 : MidOk 1808 8 slots (after b2 (fwS 1)) = true ∧
    (∀ w ∈ (after b2 (fwS 1)).mem, w.r = 0) ∧
    Wrote 0 [(896, .load 1 0 8)] (after b2 (fwS 1)) ∧
    Keeps [.rbx, .rbp, .r12, .r13, .r14] (after b2 (fwS 1)) ∧
    Keeps [.rbx, .rbp, .r12, .r13, .r14] (after b3 (fwS 2)) ∧
    Keeps [.rbx, .rbp, .r12, .r13, .r14] (after b4 (fwS 3)) ∧
    (∀ w ∈ (after b2 (fwS 1)).mem, 896 ≤ w.off ∧ w.off + w.n ≤ 904) ∧
    MidOk 1808 8 slots (after b3 (fwS 2)) = true ∧ (∀ w ∈ (after b3 (fwS 2)).mem, w.r = 0) ∧
    Wrote 0 [(904, .load 1 8 8)] (after b3 (fwS 2)) ∧
    (∀ w ∈ (after b3 (fwS 2)).mem, 904 ≤ w.off ∧ w.off + w.n ≤ 912) ∧
    MidOk 1808 8 slots (after b4 (fwS 3)) = true ∧ (∀ w ∈ (after b4 (fwS 3)).mem, w.r = 0) ∧
    Wrote 0 [(912, .load 1 16 8)] (after b4 (fwS 3)) ∧
    (∀ w ∈ (after b4 (fwS 3)).mem, 912 ≤ w.off ∧ w.off + w.n ≤ 920) := by
  decide +kernel

public theorem ok_b5 : MidOk 1808 8 slots (after b5 midS) = true ∧ (after b5 midS).mem = [] ∧
    (after b5 midS).reg .rax = some (.bin .add .W64 (.lit 888)
      (.bin .add .W64 (.ptr 0 8) (.bin .mul .W64 (.reg .r14) (.lit 8)))) ∧
    (after b5 midS).reg .rcx = some (.lit 0) ∧
    (after b5 midS).reg .rdx = some (.bin .and .W32 (.un .trunc .W32 (.reg .rbp)) (.lit 62)) ∧
    (after b5 midS).reg .rsi = some (.bin .add .W64 (.reg .r13) (.lit 16)) ∧
    (after b5 midS).reg .r15 = some (.bin .add .W64 (.reg .r14) (.reg .rbp)) ∧
    Keeps [.rbx, .rbp, .r12, .r13, .r14] (after b5 midS) := by
  decide +kernel

/-- The heights' load at the owner `var 0`, in region `r`. -/
public abbrev hX (r : Nat) : Sym := .loadx r 24 (.bin .mul .W64 (.var 0) (.lit 8)) 8

public theorem ok_b9 : (after b9 sB).mem = [] ∧ (after b9 sB).reg .rdi = some (.load 0 0 8) ∧
    (after b9 sB).reg .rsi = some (.ptr 0 16) ∧
    Keeps [.rax, .rcx, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15, .rsp] (after b9 sB) := by
  decide +kernel

public theorem ok_b10a : (∀ w ∈ (after (b10.take 2) sH).mem, w.r = 0 ∧ w.off + w.n ≤ 16) ∧
    Wrote 0 [(0, hX 1)] (after (b10.take 2) sH) ∧ (after (b10.take 2) sH).reg .rdi = some (hX 1) ∧
    (after (b10.take 2) sH).reg .r12 = some (.ptr 1 0) ∧
    Keeps [.rax, .rcx, .rdx, .rbx, .rbp, .r13, .r14, .r15, .rsp, .rsi] (after (b10.take 2) sH) := by
  decide +kernel

public theorem ok_b10b : (after (b10.drop 2) sB).mem = [] ∧
    (after (b10.drop 2) sB).reg .rdi = some (.load 0 16 8) ∧
    (after (b10.drop 2) sB).reg .rsi = some (.ptr 0 16) ∧
    Keeps [.rax, .rcx, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15, .rsp] (after (b10.drop 2) sB) := by
  decide +kernel

public theorem ok_b7 : (after b7 sH7).mem = [] ∧ (after b7 sH7).reg .rdi = some (hX 0) ∧
    (after b7 sH7).reg .r12 = some (.ptr 0 0) ∧
    Keeps [.rax, .rcx, .rdx, .rbx, .rbp, .r13, .r14, .r15, .rsp, .rsi] (after b7 sH7) := by
  decide +kernel

public theorem ok_b8 : (∀ w ∈ (after b8 sT).mem, w.r = 0 ∧ 8 ≤ w.off ∧ w.off + w.n ≤ 16) ∧
    Wrote 0 [(8, .reg .rdi)] (after b8 sT) ∧
    (after b8 sT).reg .rcx = some (.bin .add .W64 (.lit 2) (.reg .rcx)) ∧
    (after b8 sT).reg .rsi = some (.bin .add .W64 (.lit 32) (.reg .rsi)) ∧
    Keeps [.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15, .rsp] (after b8 sT) := by
  decide +kernel

public theorem exit_b15 : (exec b15 midS).map (·.2) = some (.cond (.cmp .eq .W8
    (.bin .and .W8 (.reg .rbp) (.lit 1)) (.lit 0)) NativeRustcVmX64.Vm.BusLayout.label_16) := by
  rw [run_b15]; rfl

public theorem exit_b16 : (exec b16 sO).map (·.2) = some (.cond
    ((SBool.cmp .ult .W64 (.load 0 0 8) (.lit 5)).not.and
      (SBool.cmp .eq .W64 (.load 0 0 8) (.lit 5)).not) NativeRustcVmX64.Vm.BusLayout.label_14) := by
  rw [run_b16]; rfl

public theorem exit_b17 : (exec b17 sH17).map (·.2) = some (.jump NativeRustcVmX64.Vm.BusLayout.label_15) := by
  rw [run_b17]; rfl

public theorem ok_b16 : (after b16 sO).mem = [] ∧ (after b16 sO).reg .rdx = some (.load 0 0 8) ∧
    Keeps [.rax, .rcx, .rbx, .rbp, .r12, .r13, .r14, .r15, .rsp] (after b16 sO) := by
  decide +kernel

public theorem ok_b17 : (after b17 sH17).mem = [] ∧ (after b17 sH17).reg .rdx = some (hX 0) ∧
    (after b17 sH17).reg .r12 = some (.ptr 0 0) ∧
    Keeps [.rax, .rcx, .rbx, .rbp, .r13, .r14, .r15, .rsp] (after b17 sH17) := by
  decide +kernel

public theorem ok_b19 : (∀ w ∈ (after b19 sT).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    Wrote 0 [(0, .reg .rdx)] (after b19 sT) ∧
    Keeps [.rax, .rcx, .rbx, .rbp, .r12, .r13, .r14, .r15, .rsp] (after b19 sT) := by
  decide +kernel

public theorem ok_b15 : MidOk 1808 8 slots (after b15 midS) = true ∧ (after b15 midS).mem = [] ∧
    Keeps [.rax, .rcx, .rbx, .rbp, .r12, .r13, .r14, .r15] (after b15 midS) := by
  decide +kernel

public theorem ok_b20 : MidOk 1808 0 slots (after b20 (gotS 8 "memset")) = true ∧
    (∀ w ∈ (after b20 (gotS 8 "memset")).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b20 (gotS 8 "memset")).reg .rdi = some (.ptr 0 1328) ∧ (after b20 (gotS 8 "memset")).reg .rdx = some (.lit 432) ∧
    (after b20 (gotS 8 "memset")).reg .rsi = some (.lit 0) ∧ (after b20 (gotS 8 "memset")).reg .r12 = some (.ptr 0 1328) ∧
    Keeps [.rbx, .rbp, .r13, .r14, .r15] (after b20 (gotS 8 "memset")) := by
  decide +kernel

public theorem ok_b21 : MidOk 1808 0 slots (after b21 midS) = true ∧
    (∀ w ∈ (after b21 midS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b21 midS).reg .rdi = some (.ptr 0 896) ∧ (after b21 midS).reg .rcx = some (.lit 54) ∧
    (after b21 midS).reg .rsi = some (.reg .r15) ∧ (after b21 midS).reg .rdx = some (.reg .r12) ∧
    Keeps [.rbx, .rbp, .r12, .r13, .r14, .r15] (after b21 midS) := by
  decide +kernel

public theorem ok_b22 : MidOk 1808 8 slots (after b22 midS) = true ∧ (after b22 midS).mem = [] ∧
    Keeps [.rdx, .rbx, .rbp, .r12, .r13, .r14, .r15] (after b22 midS) := by
  decide +kernel

public theorem ok_b23 : MidOk 1808 8 slots (after b23 midS) = true ∧
    (∀ w ∈ (after b23 midS).mem, w.r = 0) ∧
    Wrote 0 [(8, .reg .rdx), (72, .lit 0)] (after b23 midS) ∧
    (∀ w ∈ (after b23 midS).mem, 8 ≤ w.off ∧ w.off + w.n ≤ 896) ∧
    (after b23 midS).reg .rax = some (.ptr 0 24) ∧ (after b23 midS).reg .rcx = some (.lit 0) ∧
    (after b23 midS).reg .rdx = some (.lit 0) ∧
    Keeps [.rbx, .rbp, .r12, .r13, .r14, .r15] (after b23 midS) := by
  decide +kernel

public theorem ok_b25 : MidOk 1808 8 slots (after b25 plS) = true ∧ (after b25 plS).mem = [] ∧
    (after b25 plS).reg .rcx = some (.bin .add .W64 (.reg .rcx) (.lit 1)) ∧
    Keeps [.rdx, .rbx, .r14, .r15] (after b25 plS) ∧ (after b25 plS).reg .rax = some (.ptr 0 24) := by
  decide +kernel

public theorem ok_b26 : MidOk 1808 8 slots (after b26 plS) = true ∧ (after b26 plS).mem = [] ∧
    (after b26 plS).reg .rdi = some (.loadx 0 896 (.bin .mul .W64 (.reg .rcx) (.lit 8)) 8) ∧
    (after b26 plS).reg .rsi = some (.loadx 0 1328 (.bin .mul .W64 (.reg .rcx) (.lit 8)) 8) ∧
    Keeps [.rcx, .rdx, .rbx, .r14, .r15] (after b26 plS) ∧ (after b26 plS).reg .rax = some (.ptr 0 24) := by
  decide +kernel

public theorem ok_b27 : MidOk 1808 8 slots (after b27 plS) = true ∧ (after b27 plS).mem = [] ∧
    Keeps [.rcx, .rdx, .rdi, .rsi, .rbx, .r14, .r15] (after b27 plS) ∧
    (after b27 plS).reg .rax = some (.ptr 0 24) := by
  decide +kernel

public theorem ok_b28 : (∀ w ∈ (after b28 fS).mem, w.r = 0 ∧ w.off + w.n ≤ 16) ∧
    Wrote 0 [(0, .reg .rdi), (8, .reg .rsi)] (after b28 fS) ∧
    Keeps [.rax, .rcx, .rbx, .rbp, .r12, .r13, .r14, .r15, .rsp] (after b28 fS) ∧
    (after b28 fS).reg .rdx = some (.bin .add .W64 (.reg .rdx) (.lit 1)) := by
  decide +kernel

public theorem ok_b30 : MidOk 1808 8 slots (after b30 midS) = true ∧ (after b30 midS).mem = [] ∧
    (after b30 midS).reg .r8 = some (.load 0 72 8) ∧
    Keeps [.rax, .rcx, .rdx, .rdi, .rsi, .rbx, .r14, .r15] (after b30 midS) := by
  decide +kernel

public theorem ok_b31a : (∀ w ∈ (after (b31.take 4) tS).mem, w.r = 0 ∧ 56 ≤ w.off ∧
      w.off + w.n ≤ 72) ∧
    Wrote 0 [(56, .reg .rdi), (64, .reg .rsi)] (after (b31.take 4) tS) ∧
    Keeps [.rax, .rcx, .rdx, .r8, .rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]
      (after (b31.take 4) tS) := by
  decide +kernel

public theorem ok_b31b : MidOk 1808 8 slots (after (b31.drop 4) midS) = true ∧
    (∀ w ∈ (after (b31.drop 4) midS).mem, w.r = 0) ∧
    Wrote 0 [(72, .bin .add .W64 (.reg .r8) (.lit 1))] (after (b31.drop 4) midS) ∧
    (∀ w ∈ (after (b31.drop 4) midS).mem, 72 ≤ w.off ∧ w.off + w.n ≤ 80) ∧
    Keeps [.rax, .rcx, .rdx, .rbx, .r14, .r15] (after (b31.drop 4) midS) := by
  decide +kernel

public theorem ok_b33 : MidOk 1808 0 slots (after b33 (gotS 8 "memcpy")) = true ∧
    (∀ w ∈ (after b33 (gotS 8 "memcpy")).mem, w.r = 0) ∧ Wrote 0 [(16, .reg .rdx)] (after b33 (gotS 8 "memcpy")) ∧
    (∀ w ∈ (after b33 (gotS 8 "memcpy")).mem, w.off + w.n ≤ 8 ∨ 16 ≤ w.off ∧ w.off + w.n ≤ 24) ∧
    (after b33 (gotS 8 "memcpy")).reg .rdi = some (.bin .add .W64 (.reg .rbx) (.lit 8)) ∧
    (after b33 (gotS 8 "memcpy")).reg .rsi = some (.ptr 0 8) ∧ (after b33 (gotS 8 "memcpy")).reg .rdx = some (.lit 888) ∧
    Keeps [.rbx] (after b33 (gotS 8 "memcpy")) := by
  decide +kernel

/-- After the tag and the epilogue. -/
public abbrev eT : SState := after b35 (after b34 outS)

public theorem ok_end : EpiOk 1808 slots eT = true ∧ (∀ w ∈ eT.mem, w.r = 1 ∧ w.off + w.n ≤ 8) ∧
    Wrote 1 [(0, .lit 1)] eT := by
  decide +kernel

end NativeRustcVmX64.Bus.BusLayout
