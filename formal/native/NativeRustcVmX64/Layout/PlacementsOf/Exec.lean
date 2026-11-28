module

public import NativeRustcVmX64.Layout.BuildFrame
public import NativeRustcVmX64.Code.Vm.PlacementsOf
public import NativeRustcVmX64.Code.Vm.Memset.Names
public import NativeRustcVmX64.Code.Vm.Names
public import NativeRustcVmX64.Code.Vm.PlacementsOf.Names
public import NativeRustcVmX64.Code.Vm.StackOffsets.Names
public meta import NativeRustcVmX64.Code.Vm.PlacementsOf
public meta import NativeRustcVmX64.Layout.BuildFrame

/-!
# `placements_of`'s blocks, run by the symbolic executor (x86-64)

Region 0 of `entryS`/`bodyS` is the 5120-byte frame below the entry's RSP and the return address
(RSP at offset `8` in the body, a callee's return address at `0`): the stack's log-size at `8`,
`offsets` at `16`, `block_cols` at `1280`, `block_sizes` at `2544`, `block_offsets` at `3808`, the
six pushed registers from `5072`. The other states keep RSP an atom and name one or two words by
aliases: `tabS r` a byte of the read-only array at R (index RAX), `colS` (`b8`: the column and its
size stored, `kappas[c]` read), `rdS o` a word of the frame at `RSP + 8 RAX`, `st17` (`b17`: a
block's offset copied into `offsets`), `kapS` (`kappas[c]`), `plS` (`b21`: a placement stored).
-/

namespace NativeRustcVmX64.Layout.PlacementsOf

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.PlacementsOf NativeRustcVmX64.Transcript
open NativeRustcVmX64.Layout.BuildFrame (Keeps AOk)

@[expose] public section

/-- The frame's slots: the pushed registers. -/
def slots : Slots :=
  [(5112, .rbp), (5104, .r15), (5096, .r14), (5088, .r13), (5080, .r12), (5072, .rbx)]

/-- The callee-saved registers. -/
def cs : List Reg64 := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- `p + 8 i`. -/
def idx (p i : Reg64) : Sym := .bin .add .W64 (.reg p) (.bin .mul .W64 (.reg i) (.lit 8))

def entryS : SState :=
  (init [5128, 8] [(.rsp, .ptr 0 5120)] [] [] [(.gotSlot "memset", 1, 0)]).withKnownBytes
    1 0 8 (.label "memset")
def bodyS : SState := init [5128] [(.rsp, .ptr 0 8)]
/-- The cached `memset` address, preserved in R12 across the first call. -/
def cachedS : SState := init [5128] [(.rsp, .ptr 0 8), (.r12, .label "memset")]
/-- The frame and the ordinary-memory GOT slot read by a call. -/
def gotS : SState :=
  (init [5128, 8] [(.rsp, .ptr 0 8)] [] [] [(.gotSlot "memset", 1, 0)]).withKnownBytes
    1 0 8 (.label "memset")
def tabS (r : Reg64) : SState :=
  init [158] (aliases := [(.reg r, (0, 0))]) (bounds := [(.reg .rax, 158)])
def colS : SState :=
  init [1272, 8] (aliases := [(idx .rsp .r13, (0, -1272)), (idx .r14 .rax, (1, 0))])
def rdS (o : Int) : SState := init [8] (aliases := [(idx .rsp .rax, (0, o))])
def st17 : SState :=
  init [8, 8] (aliases := [(idx .rsp .rax, (0, -3800)), (idx .rsp .rcx, (1, -8))])
def kapS : SState := init [8] (aliases := [(idx .r14 .rax, (0, 0))])
def plS : SState := init [24] [(.rbx, .ptr 0 16)]

def b22a : List Directive := b22.take 2
def b22b : List Directive := b22.drop 2
/-- `b31` from `NativeRustcVmX64.Vm.PlacementsOf.label_26`. -/
def b31b : List Directive := b31.drop 1

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 cachedS
sym_block run_b2 := exec b2 bodyS
sym_block run_b4 := exec b4 bodyS
sym_block run_b5 := exec b5 (tabS .rbp)
sym_block run_b6 := exec b6 (tabS .r12)
sym_block run_b7 := exec b7 bodyS
sym_block run_b8 := exec b8 colS
sym_block run_b9 := exec b9 gotS
sym_block run_b10 := exec b10 bodyS
sym_block run_b11 := exec b11 bodyS
sym_block run_b12 := exec b12 bodyS
sym_block run_b13 := exec b13 gotS
sym_block run_b14 := exec b14 bodyS
sym_block run_b15 := exec b15 bodyS
sym_block run_b16 := exec b16 (rdS (-1272))
sym_block run_b17 := exec b17 st17
sym_block run_b18 := exec b18 bodyS
sym_block run_b19 := exec b19 bodyS
sym_block run_b20 := exec b20 (rdS (-8))
sym_block run_b21 := exec b21 plS
sym_block run_b22a := exec b22a kapS
sym_block run_b22b := exec b22b (tabS .rbp)
sym_block run_b23 := exec b23 bodyS
sym_block run_b24 := exec b24 bodyS
sym_block run_b27 := exec b27 (tabS .r12)
sym_block run_b28 := exec b28 bodyS
sym_block run_b31 := exec b31b bodyS
sym_block run_b32 := exec b32 bodyS

public theorem exit_b0 : exec b0 entryS = some (after b0 entryS, .call NativeRustcVmX64.Vm.Memset.entryLabel) :=
  run_b0.trans (by rw [after_eq run_b0])
public theorem ok_b0 : ProOk 5120 0 slots (after b0 entryS) = true ∧
    (after b0 entryS).reg .rdi = some (.ptr 0 1280) ∧ (after b0 entryS).reg .rsi = some (.lit 0) ∧
    (after b0 entryS).reg .rdx = some (.lit 1264) ∧ (after b0 entryS).reg .rbx = some (.reg .rsi) ∧
    (after b0 entryS).reg .r14 = some (.reg .rdi) ∧ (after b0 entryS).reg .r15 = some (.lit 1264) := by
  decide +kernel

public theorem b0_mem : ∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 5120 := by
  decide +kernel

public theorem b0_target : (after b0 entryS).reg .r12 = some (.label "memset") := by
  decide +kernel

public theorem exit_b1 : exec b1 cachedS = some (after b1 cachedS, .call "memset") :=
  run_b1.trans (by rw [after_eq run_b1])
public theorem ok_b1 : MidOk 5120 0 slots (after b1 cachedS) = true ∧
    (after b1 cachedS).reg .rdi = some (.ptr 0 2544) ∧ (after b1 cachedS).reg .rsi = some (.lit 0) ∧
    (after b1 cachedS).reg .rdx = some (.lit 1264) ∧
    (∀ w ∈ (after b1 cachedS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    Keeps (after b1 cachedS) [.rbx, .rbp, .r13, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b2 : exec b2 bodyS = some (after b2 bodyS, .jump NativeRustcVmX64.Vm.PlacementsOf.label_2) :=
  run_b2.trans (by rw [after_eq run_b2])
public theorem ok_b2 : MidOk 5120 8 slots (after b2 bodyS) = true ∧ (after b2 bodyS).mem = [] ∧
    (after b2 bodyS).reg .rax = some (.lit 0) ∧ (after b2 bodyS).reg .r13 = some (.lit 0) ∧
    (after b2 bodyS).reg .rbp = some (.label NativeRustcVmX64.Vm.Symbols.rodata15Label) ∧
    (after b2 bodyS).reg .r12 = some (.label NativeRustcVmX64.Vm.Symbols.rodata16Label) ∧
    Keeps (after b2 bodyS) [.rbx, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b4 : exec b4 bodyS = some (after b4 bodyS,
    .cond (SBool.cmp .eq .W64 (.bin .add .W64 (.lit 18446744073709551608) (.reg .r15)) (.lit 0))
      NativeRustcVmX64.Vm.PlacementsOf.label_6) :=
  run_b4.trans (by rw [after_eq run_b4])
public theorem ok_b4 : MidOk 5120 8 slots (after b4 bodyS) = true ∧ (after b4 bodyS).mem = [] ∧
    (after b4 bodyS).reg .rax = some (.bin .add .W64 (.reg .rax) (.lit 1)) ∧
    (after b4 bodyS).reg .r15 = some (.bin .add .W64 (.lit 18446744073709551608) (.reg .r15)) ∧
    Keeps (after b4 bodyS) [.rbx, .rbp, .r12, .r13, .r14] = true := by
  decide +kernel

public theorem exit_b5 : exec b5 (tabS .rbp) = some (after b5 (tabS .rbp),
    .cond (SBool.cmp .eq .W8 (.loadx 0 0 (.reg .rax) 1) (.lit 18446744073709551615)).not
      NativeRustcVmX64.Vm.PlacementsOf.label_1) :=
  run_b5.trans (by rw [after_eq run_b5])
public theorem ok_b5 : AOk slots (after b5 (tabS .rbp)) = true ∧ (after b5 (tabS .rbp)).mem = [] ∧
    Keeps (after b5 (tabS .rbp)) (.rax :: cs) = true := by
  decide +kernel

public theorem exit_b6 : exec b6 (tabS .r12) = some (after b6 (tabS .r12),
    .cond (SBool.cmp .eq .W8 (.loadx 0 0 (.reg .rax) 1) (.lit 1)) NativeRustcVmX64.Vm.PlacementsOf.label_1) :=
  run_b6.trans (by rw [after_eq run_b6])
public theorem ok_b6 : AOk slots (after b6 (tabS .r12)) = true ∧ (after b6 (tabS .r12)).mem = [] ∧
    Keeps (after b6 (tabS .r12)) (.rax :: cs) = true := by
  decide +kernel

public theorem exit_b7 : exec b7 bodyS = some (after b7 bodyS,
    .cond (SBool.cmp .ult .W64 (.reg .r13) (.lit 158)).not NativeRustcVmX64.Vm.PlacementsOf.label_22) :=
  run_b7.trans (by rw [after_eq run_b7])
public theorem ok_b7 : MidOk 5120 8 slots (after b7 bodyS) = true ∧ (after b7 bodyS).mem = [] ∧
    Keeps (after b7 bodyS) (.rax :: cs) = true := by
  decide +kernel

public theorem exit_b8 : exec b8 colS = some (after b8 colS, .jump NativeRustcVmX64.Vm.PlacementsOf.label_1) :=
  run_b8.trans (by rw [after_eq run_b8])
public theorem ok_b8 : AOk slots (after b8 colS) = true ∧
    (∀ w ∈ (after b8 colS).mem, w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ 1264 ≤ w.off ∧ w.off + w.n ≤ 1272)) ∧
    (∀ t < 8, findWrite 0 t (after b8 colS).mem = some (.reg .rax, t)) ∧
    (∀ t < 8, findWrite 0 (1264 + t) (after b8 colS).mem = some (.load 1 0 8, t)) ∧
    (after b8 colS).reg .r13 = some (.bin .add .W64 (.reg .r13) (.lit 1)) ∧
    Keeps (after b8 colS) [.rax, .rbx, .rbp, .r12, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b9 : exec b9 gotS = some (after b9 gotS, .call "memset") :=
  run_b9.trans (by rw [after_eq run_b9])
public theorem ok_b9 : MidOk 5120 0 slots (after b9 gotS) = true ∧
    (after b9 gotS).reg .rdi = some (.ptr 0 3808) ∧ (after b9 gotS).reg .rsi = some (.lit 0) ∧
    (after b9 gotS).reg .rdx = some (.lit 1264) ∧
    (∀ w ∈ (after b9 gotS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    Keeps (after b9 gotS) [.rbx, .rbp, .r12, .r13, .r14] = true := by
  decide +kernel

public theorem exit_b10 : exec b10 bodyS = some (after b10 bodyS,
    .cond (SBool.cmp .ult .W64 (.reg .r13) (.lit 159)).not NativeRustcVmX64.Vm.PlacementsOf.label_25) :=
  run_b10.trans (by rw [after_eq run_b10])
public theorem ok_b10 : MidOk 5120 8 slots (after b10 bodyS) = true ∧ (after b10 bodyS).mem = [] ∧
    Keeps (after b10 bodyS) cs = true := by
  decide +kernel

public theorem exit_b11 : exec b11 bodyS = some (after b11 bodyS,
    .call NativeRustcVmX64.Vm.StackOffsets.entryLabel) :=
  run_b11.trans (by rw [after_eq run_b11])
public theorem ok_b11 : MidOk 5120 0 slots (after b11 bodyS) = true ∧
    (after b11 bodyS).reg .rdi = some (.ptr 0 2544) ∧
    (after b11 bodyS).reg .rsi = some (.reg .r13) ∧
    (after b11 bodyS).reg .rdx = some (.ptr 0 3808) ∧ (after b11 bodyS).reg .rcx = some (.lit 158) ∧
    (∀ w ∈ (after b11 bodyS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    Keeps (after b11 bodyS) cs = true := by
  decide +kernel

public theorem exit_b12 : exec b12 bodyS = some (after b12 bodyS,
    .cond (SBool.cmp .eq .W64 (.reg .rax) (.lit 1)).not NativeRustcVmX64.Vm.PlacementsOf.label_23) :=
  run_b12.trans (by rw [after_eq run_b12])
public theorem ok_b12 : MidOk 5120 8 slots (after b12 bodyS) = true ∧ (after b12 bodyS).mem = [] ∧
    Keeps (after b12 bodyS) (.rdx :: cs) = true := by
  decide +kernel

public theorem exit_b13 : exec b13 gotS = some (after b13 gotS, .call "memset") :=
  run_b13.trans (by rw [after_eq run_b13])
public theorem ok_b13 : MidOk 5120 0 slots (after b13 gotS) = true ∧
    (after b13 gotS).reg .rdi = some (.ptr 0 16) ∧ (after b13 gotS).reg .rsi = some (.lit 0) ∧
    (after b13 gotS).reg .rdx = some (.lit 1264) ∧
    (∀ w ∈ (after b13 gotS).mem, w.r = 0 ∧ w.off + w.n ≤ 16) ∧
    (∀ t < 8, findWrite 0 (8 + t) (after b13 gotS).mem = some (.reg .rdx, t)) ∧
    Keeps (after b13 gotS) [.rbx, .rbp, .r12, .r13, .r14] = true := by
  decide +kernel

public theorem exit_b14 : exec b14 bodyS = some (after b14 bodyS,
    .cond (SBool.cmp .eq .W64 (.bin .and .W64 (.reg .r13) (.reg .r13)) (.lit 0))
      NativeRustcVmX64.Vm.PlacementsOf.label_13) :=
  run_b14.trans (by rw [after_eq run_b14])
public theorem ok_b14 : MidOk 5120 8 slots (after b14 bodyS) = true ∧ (after b14 bodyS).mem = [] ∧
    Keeps (after b14 bodyS) cs = true := by
  decide +kernel

public theorem exit_b15 : exec b15 bodyS = some (after b15 bodyS, .fall) :=
  run_b15.trans (by rw [after_eq run_b15])
public theorem ok_b15 : MidOk 5120 8 slots (after b15 bodyS) = true ∧ (after b15 bodyS).mem = [] ∧
    (after b15 bodyS).reg .rax = some (.lit 0) ∧
    Keeps (after b15 bodyS) [.rbx, .rbp, .r12, .r13, .r14] = true := by
  decide +kernel

public theorem exit_b16 : exec b16 (rdS (-1272)) = some (after b16 (rdS (-1272)),
    .cond (SBool.cmp .ult .W64 (.load 0 0 8) (.lit 158)).not NativeRustcVmX64.Vm.PlacementsOf.label_25) :=
  run_b16.trans (by rw [after_eq run_b16])
public theorem ok_b16 : AOk slots (after b16 (rdS (-1272))) = true ∧
    (after b16 (rdS (-1272))).mem = [] ∧ (after b16 (rdS (-1272))).reg .rcx = some (.load 0 0 8) ∧
    Keeps (after b16 (rdS (-1272))) (.rax :: cs) = true := by
  decide +kernel

public theorem exit_b17 : exec b17 st17 = some (after b17 st17,
    .cond (SBool.cmp .eq .W64 (.reg .r13) (.bin .add .W64 (.reg .rax) (.lit 1))).not
      NativeRustcVmX64.Vm.PlacementsOf.label_10) :=
  run_b17.trans (by rw [after_eq run_b17])
public theorem ok_b17 : AOk slots (after b17 st17) = true ∧
    (∀ w ∈ (after b17 st17).mem, w.r = 1) ∧
    (∀ t < 8, findWrite 1 t (after b17 st17).mem = some (.load 0 0 8, t)) ∧
    (after b17 st17).reg .rax = some (.bin .add .W64 (.reg .rax) (.lit 1)) ∧
    Keeps (after b17 st17) cs = true := by
  decide +kernel

public theorem exit_b18 : exec b18 bodyS = some (after b18 bodyS, .fall) :=
  run_b18.trans (by rw [after_eq run_b18])
public theorem ok_b18 : MidOk 5120 8 slots (after b18 bodyS) = true ∧ (after b18 bodyS).mem = [] ∧
    (after b18 bodyS).reg .r15 = some (.load 0 48 8) ∧
    Keeps (after b18 bodyS) [.rbx, .rbp, .r12, .r13, .r14] = true := by
  decide +kernel

public theorem exit_b19 : exec b19 bodyS = some (after b19 bodyS, .jump NativeRustcVmX64.Vm.PlacementsOf.label_16) :=
  run_b19.trans (by rw [after_eq run_b19])
public theorem ok_b19 : MidOk 5120 8 slots (after b19 bodyS) = true ∧ (after b19 bodyS).mem = [] ∧
    (after b19 bodyS).reg .rax = some (.lit 0) ∧
    (after b19 bodyS).reg .rbx = some (.bin .add .W64 (.lit 16) (.reg .rbx)) ∧
    Keeps (after b19 bodyS) [.rbp, .r12, .r13, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b20 : exec b20 (rdS (-8)) = some (after b20 (rdS (-8)), .fall) :=
  run_b20.trans (by rw [after_eq run_b20])
public theorem ok_b20 : AOk slots (after b20 (rdS (-8))) = true ∧ (after b20 (rdS (-8))).mem = [] ∧
    (after b20 (rdS (-8))).reg .rdx = some (.load 0 0 8) ∧
    (after b20 (rdS (-8))).reg .rsi = some (.lit 1) ∧
    Keeps (after b20 (rdS (-8))) (.rax :: .rcx :: cs) = true := by
  decide +kernel

public theorem exit_b21 : exec b21 plS = some (after b21 plS,
    .cond (SBool.cmp .eq .W64 (.bin .add .W64 (.reg .rax) (.lit 1)) (.lit 158))
      NativeRustcVmX64.Vm.PlacementsOf.label_24) :=
  run_b21.trans (by rw [after_eq run_b21])
public theorem ok_b21 : AOk slots (after b21 plS) = true ∧
    (∀ w ∈ (after b21 plS).mem, w.r = 0) ∧
    (∀ t < 8, findWrite 0 t (after b21 plS).mem = some (.reg .rsi, t)) ∧
    (∀ t < 8, findWrite 0 (8 + t) (after b21 plS).mem = some (.reg .rcx, t)) ∧
    (∀ t < 8, findWrite 0 (16 + t) (after b21 plS).mem = some (.reg .rdx, t)) ∧
    (after b21 plS).reg .rax = some (.bin .add .W64 (.reg .rax) (.lit 1)) ∧
    (after b21 plS).reg .rbx = some (.ptr 0 40) ∧
    Keeps (after b21 plS) [.rbp, .r12, .r13, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b22a : exec b22a kapS = some (after b22a kapS, .fall) :=
  run_b22a.trans (by rw [after_eq run_b22a])
public theorem ok_b22a : AOk slots (after b22a kapS) = true ∧ (after b22a kapS).mem = [] ∧
    (after b22a kapS).reg .rcx = some (.load 0 0 8) ∧
    Keeps (after b22a kapS) (.rax :: cs) = true := by
  decide +kernel

public theorem exit_b22b : exec b22b (tabS .rbp) = some (after b22b (tabS .rbp),
    .cond (SBool.cmp .eq .W64 (.un (.zext .W8) .W32 (.loadx 0 0 (.reg .rax) 1)) (.lit 255))
      NativeRustcVmX64.Vm.PlacementsOf.label_19) :=
  run_b22b.trans (by rw [after_eq run_b22b])
public theorem ok_b22b : AOk slots (after b22b (tabS .rbp)) = true ∧
    (after b22b (tabS .rbp)).mem = [] ∧
    (after b22b (tabS .rbp)).reg .rdx = some (.un (.zext .W8) .W32 (.loadx 0 0 (.reg .rax) 1)) ∧
    Keeps (after b22b (tabS .rbp)) (.rax :: .rcx :: cs) = true := by
  decide +kernel

public theorem exit_b23 : exec b23 bodyS = some (after b23 bodyS,
    .cond (SBool.cmp .ult .W64 (.reg .rcx) (.lit 64)).not NativeRustcVmX64.Vm.PlacementsOf.label_22) :=
  run_b23.trans (by rw [after_eq run_b23])
public theorem ok_b23 : MidOk 5120 8 slots (after b23 bodyS) = true ∧ (after b23 bodyS).mem = [] ∧
    Keeps (after b23 bodyS) (.rax :: .rcx :: .rdx :: cs) = true := by
  decide +kernel

public theorem exit_b24 : exec b24 bodyS = some (after b24 bodyS,
    .cond (SBool.cmp .addC .W64 (.reg .r15) (.bin .shl .W64 (.reg .rdx) (.reg .rcx))).not
      NativeRustcVmX64.Vm.PlacementsOf.label_15) :=
  run_b24.trans (by rw [after_eq run_b24])
public theorem ok_b24 : MidOk 5120 8 slots (after b24 bodyS) = true ∧ (after b24 bodyS).mem = [] ∧
    (after b24 bodyS).reg .rdx =
      some (.bin .add .W64 (.reg .r15) (.bin .shl .W64 (.reg .rdx) (.reg .rcx))) ∧
    (after b24 bodyS).reg .rsi = some (.lit 1) ∧
    Keeps (after b24 bodyS) (.rax :: .rcx :: cs) = true := by
  decide +kernel

public theorem exit_b27 : exec b27 (tabS .r12) = some (after b27 (tabS .r12),
    .cond (SBool.cmp .eq .W8 (.loadx 0 0 (.reg .rax) 1) (.lit 0)) NativeRustcVmX64.Vm.PlacementsOf.label_14) :=
  run_b27.trans (by rw [after_eq run_b27])
public theorem ok_b27 : AOk slots (after b27 (tabS .r12)) = true ∧
    (after b27 (tabS .r12)).mem = [] ∧ Keeps (after b27 (tabS .r12)) (.rax :: .rcx :: cs) = true := by
  decide +kernel

public theorem exit_b28 : exec b28 bodyS = some (after b28 bodyS, .jump NativeRustcVmX64.Vm.PlacementsOf.label_15) :=
  run_b28.trans (by rw [after_eq run_b28])
public theorem ok_b28 : MidOk 5120 8 slots (after b28 bodyS) = true ∧ (after b28 bodyS).mem = [] ∧
    (after b28 bodyS).reg .rsi = some (.lit 0) ∧ (after b28 bodyS).reg .rcx = some (.lit 0) ∧
    (after b28 bodyS).reg .rdx = some (.lit 0) ∧ Keeps (after b28 bodyS) (.rax :: cs) = true := by
  decide +kernel

public theorem exit_b31 : exec b31b bodyS = some (after b31b bodyS, .ret (.load 0 5120 8)) :=
  run_b31.trans (by rw [after_eq run_b31])
public theorem ok_b31 : EpiOk 5120 slots (after b31b bodyS) = true ∧ (after b31b bodyS).mem = [] ∧
    (after b31b bodyS).reg .rax = some (.reg .r15) ∧ Keeps (after b31b bodyS) [.rdx] = true := by
  decide +kernel

public theorem exit_b32 : exec b32 bodyS = some (after b32 bodyS, .jump NativeRustcVmX64.Vm.PlacementsOf.label_26) :=
  run_b32.trans (by rw [after_eq run_b32])
public theorem ok_b32 : MidOk 5120 8 slots (after b32 bodyS) = true ∧ (after b32 bodyS).mem = [] ∧
    (after b32 bodyS).reg .r15 = some (.lit 1) ∧
    (after b32 bodyS).reg .rdx =
      some (.ite (SBool.cmp .ult .W64 (.load 0 8 8) (.lit 17)).not (.load 0 8 8) (.lit 16)) := by
  decide +kernel

end NativeRustcVmX64.Layout.PlacementsOf
