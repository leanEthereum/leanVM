module

public import NativeRustcVmX64.Whir.MathFrame
public import NativeRustcVmX64.Code.Vm.SubspaceTable
public meta import NativeRustcVmX64.Code.Vm.SubspaceTable
public meta import NativeRustcVmX64.Whir.MathFrame

/-!
# `subspace_table`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 848-byte frame (`Field.frameS 848`, `Field.midS 848`: the pushes, the 792 bytes of
locals, the calls' return-address slot) and the return address. From RSP (offset `8`): the output
pointer at `(%rsp)`, `μ` at `8(%rsp)`, `8μ` at `16(%rsp)`, the table's length and the turn
spilled at `24(%rsp)`, `32(%rsp)`, the table (`len` at `40(%rsp)`, the pairs from `48(%rsp)`), the
layer (31 words) from `544(%rsp)`.
- `entryS` (`b0`: the prologue, `memset` of the layer); `midS` at the frame's stores and loads
  (`b2`, `b11` to `b14`, `b21`) and the epilogue `b24`; `regsS` (registers only) at the counters'
  blocks;
- `outS` (`b5`, `b22`): region 0 the output's tag RBX points to;
- `vecS` (`b7`): region 0 the eight layer words R15 points to; `tailS` (`b10`): region 0 the
  layer word at `r15 + 8·rsi`;
- `wordS` (`b15`, the layer's loop head): region 0 the call slot, region 1 the layer word at
  `rbx + r14`; `kmul`; `callS` (`b16`): the call slot; `stS` (`b17`): region 0 the layer word;
- `rootS` (`b18`): region 0 the frame's first 48 bytes, region 1 the new root at
  `552 + rsp + 8·r13`; `kinv`;
- `pushS` (`b20`): region 0 the frame's first 48 bytes, region 1 the table's pair at
  `56 + rsp + 16·len`;
- `noneS` (`b23`): region 0 the frame's first 16 bytes, region 1 the output's tag.
-/

namespace NativeRustcVmX64.Whir.SubspaceTable

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SubspaceTable NativeRustcVmX64.Field
open NativeRustcVmX64.Arrays (keepsRegs keepsAll freeRegs restores)

@[expose] public section

/-- The layer word's address in `b10`. -/
def tAddr : Sym := .bin .add .W64 (.reg .r15) (.bin .mul .W64 (.reg .rsi) (.lit 8))
/-- The layer word's address in `b15`, `b17`. -/
def eAddr : Sym := .bin .add .W64 (.reg .rbx) (.reg .r14)
/-- The new root's address in `b18`. -/
def rAddr : Sym :=
  .bin .add .W64 (.bin .add .W64 (.ptr 0 8) (.bin .mul .W64 (.load 0 40 8) (.lit 8))) (.lit 544)
/-- The pushed pair's address in `b20`. -/
def pAddr : Sym := .bin .add .W64 (.ptr 0 56) (.bin .shl .W64 (.load 0 32 8) (.lit 4))
/-- `8μ` in `b13`: the base-less scaled-index `lea`. -/
def mu8S : Sym := .bin .mul .W64 (.reg .r14) (.lit 8)

/-- At the entry. -/
abbrev entryS : SState := frameS 848
/-- Registers only. -/
def regsS : SState := init []
/-- The output's tag RBX points to. -/
def outS : SState := init [8] [(.rbx, .ptr 0 0)]
/-- Eight layer words from R15. -/
def vecS : SState := init [64] [(.r15, .ptr 0 0)]
/-- The layer word at `r15 + 8·rsi`. -/
def tailS : SState := init [8] [] [] [] [(tAddr, 0, 0)]
/-- The layer word at `rbx + r14`. -/
def stS : SState := init [8] [] [] [] [(eAddr, 0, 0)]
/-- The frame's first 48 bytes, the new root. -/
def rootS : SState := init [48, 8] [(.rsp, .ptr 0 8)] [] [] [(rAddr, 1, 0)]
/-- The frame's first 48 bytes, the pushed pair. -/
def pushS : SState := init [48, 16] [(.rsp, .ptr 0 8)] [] [] [(pAddr, 1, 0)]
/-- The frame's first 16 bytes, the output's tag the spilled pointer points to. -/
def noneS : SState := init [16, 8] [(.rsp, .ptr 0 8)] [] [] [(.load 0 8 8, 1, 0)]

/-- The prologue. -/
def b0a : List Directive := b0.take 8
/-- The arguments, `memset`. -/
def b0b : List Directive := b0.drop 8
/-- The layer word's load. -/
def b15a : List Directive := b15.take 2
/-- `kmul(v, v)`. -/
def b15b : List Directive := b15.drop 2
/-- The turn's and the root's loads. -/
def b18a : List Directive := b18.take 2
/-- `kinv(root)`. -/
def b18b : List Directive := b18.drop 2

/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) :=
  [(840, .rbp), (832, .r15), (824, .r14), (816, .r13), (808, .r12), (800, .rbx)]

/-- A block that calls, writing the frame below `L`. -/
abbrev CallsBelow (S₀ S₁ : SState) (L : Nat) : Prop :=
  keepsRegs S₀ S₁ (freeRegs slots) = true ∧ S₁.reg .rsp = some (.ptr 0 0) ∧
    ∀ w ∈ S₁.mem, w.r = 0 ∧ w.off + w.n ≤ L

/-- A block that writes region `r` below `L`, keeping RSP and the free registers. -/
abbrev WritesBelow (S₀ S₁ : SState) (r L : Nat) : Prop :=
  keepsRegs S₀ S₁ (.rsp :: freeRegs slots) = true ∧ ∀ w ∈ S₁.mem, w.r = r ∧ w.off + w.n ≤ L


end

set_option Elab.async false

sym_block run_b0a := exec b0a entryS
sym_block run_b0b := exec b0b (gotMidS 848 "memset")
sym_block run_b1 := exec b1 regsS
sym_block run_b2 := exec b2 (midS 848)
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 regsS
sym_block run_b5 := exec b5 outS
sym_block run_b6 := exec b6 (midS 848)
sym_block run_b7 := exec b7 vecS
sym_block run_b8 := exec b8 regsS
sym_block run_b9 := exec b9 regsS
sym_block run_b10 := exec b10 tailS
sym_block run_b11 := exec b11 (midS 848)
sym_block run_b12 := exec b12 (midS 848)
sym_block run_b13 := exec b13 (midS 848)
sym_block run_b14 := exec b14 (midS 848)
sym_block run_b15a := exec b15a stS
sym_block run_b15b := exec b15b (midS 848)
sym_block run_b16 := exec b16 (midS 848)
sym_block run_b17 := exec b17 stS
sym_block run_b18a := exec b18a rootS
sym_block run_b18b := exec b18b (midS 848)
sym_block run_b19 := exec b19 regsS
sym_block run_b20 := exec b20 pushS
sym_block run_b21 := exec b21 (gotMidS 848 "memcpy")
sym_block run_b22 := exec b22 outS
sym_block run_b23 := exec b23 noneS
sym_block run_b24 := exec b24 (midS 848)

public theorem b0a_entry : (∀ p ∈ slots, p.1 + 8 ≤ 848 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b0a entryS).mem = some (.reg p.2, i)) ∧
    (∀ r ∈ freeRegs slots, (after b0a entryS).reg r = some (.reg r)) ∧
    (∀ w ∈ (after b0a entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 848) ∧
    (after b0a entryS).reg .rsp = some (.ptr 0 8) ∧
    (∀ r ∈ [Reg64.rdi, .rsi], (after b0a entryS).reg r = some (.reg r)) := by
  decide +kernel

public theorem b0b_call : CallsBelow (gotMidS 848 "memset") (after b0b (gotMidS 848 "memset")) 8 := by decide +kernel
public theorem b1_keeps : keepsAll regsS (after b1 regsS) (freeRegs slots) = true := by
  decide +kernel
public theorem b2_write : WritesBelow (midS 848) (after b2 (midS 848)) 0 16 ∧
    (∀ w ∈ (after b2 (midS 848)).mem, 8 ≤ w.off) ∧
    (∀ i < 8, findWrite 0 (8 + i) (after b2 (midS 848)).mem = some (.reg .rbx, i)) := by
  decide +kernel
public theorem b3_keeps : keepsAll regsS (after b3 regsS) (freeRegs slots) = true := by
  decide +kernel
public theorem b4_keeps : keepsAll regsS (after b4 regsS) (freeRegs slots) = true := by
  decide +kernel
public theorem b5_write : WritesBelow outS (after b5 outS) 0 8 ∧
    (∀ i < 8, findWrite 0 (0 + i) (after b5 outS).mem = some (.lit 0, i)) := by
  decide +kernel
public theorem b6_keeps : keepsAll (midS 848) (after b6 (midS 848)) (freeRegs slots) = true := by
  decide +kernel
public theorem b7_write : WritesBelow vecS (after b7 vecS) 0 64 ∧
    (∀ k < 8, ∀ i < 8, findWrite 0 (8 * k + i) (after b7 vecS).mem =
      some (.bin .shl .W64 (.lit (2 ^ (k + 1))) (.un .trunc .W32 (.reg .rdx)), i)) := by
  decide +kernel
public theorem b8_keeps : keepsAll regsS (after b8 regsS) (freeRegs slots) = true := by
  decide +kernel
public theorem b9_keeps : keepsAll regsS (after b9 regsS) (freeRegs slots) = true := by
  decide +kernel
public theorem b10_write : WritesBelow tailS (after b10 tailS) 0 8 ∧
    (∀ i < 8, findWrite 0 (0 + i) (after b10 tailS).mem = some (.bin .shl .W64 (.lit 2)
      (.un .trunc .W32 (.bin .add .W64 (.reg .rdx) (.reg .rsi))), i)) := by
  decide +kernel
public theorem b11_call : CallsBelow (midS 848) (after b11 (midS 848)) 552 ∧
    (∀ w ∈ (after b11 (midS 848)).mem, w.off + w.n ≤ 8 ∨ (48 ≤ w.off ∧ w.off + w.n ≤ 56) ∨
      72 ≤ w.off) := by
  decide +kernel
public theorem b12_write : WritesBelow (midS 848) (after b12 (midS 848)) 0 72 ∧
    (∀ w ∈ (after b12 (midS 848)).mem, 56 ≤ w.off) ∧
    (∀ i < 8, findWrite 0 (56 + i) (after b12 (midS 848)).mem = some (.lit 1, i)) ∧
    (∀ i < 8, findWrite 0 (64 + i) (after b12 (midS 848)).mem = some (.reg .rax, i)) := by
  decide +kernel
public theorem b13_write : WritesBelow (midS 848) (after b13 (midS 848)) 0 32 ∧
    (∀ w ∈ (after b13 (midS 848)).mem, 16 ≤ w.off) ∧
    (∀ i < 8, findWrite 0 (16 + i) (after b13 (midS 848)).mem = some (.reg .r14, i)) ∧
    (∀ i < 8, findWrite 0 (24 + i) (after b13 (midS 848)).mem = some (mu8S, i)) := by
  decide +kernel
public theorem b14_write : WritesBelow (midS 848) (after b14 (midS 848)) 0 48 ∧
    (∀ w ∈ (after b14 (midS 848)).mem, 32 ≤ w.off) ∧
    (∀ i < 8, findWrite 0 (40 + i) (after b14 (midS 848)).mem = some (.reg .r13, i)) ∧
    (∀ i < 8, findWrite 0 (32 + i) (after b14 (midS 848)).mem = some (.reg .r12, i)) := by
  decide +kernel
public theorem b15a_keeps : keepsAll stS (after b15a stS) (freeRegs slots) = true := by
  decide +kernel
public theorem b15b_call : CallsBelow (midS 848) (after b15b (midS 848)) 8 := by decide +kernel
public theorem b16_call : CallsBelow (midS 848) (after b16 (midS 848)) 8 := by decide +kernel
public theorem b17_write : WritesBelow stS (after b17 stS) 0 8 ∧
    (∀ i < 8, findWrite 0 (0 + i) (after b17 stS).mem =
      some (.bin .xor .W64 (.reg .rax) (.reg .r13), i)) := by
  decide +kernel
public theorem b18a_keeps : keepsAll rootS (after b18a rootS) (freeRegs slots) = true := by
  decide +kernel
public theorem b18b_call : CallsBelow (midS 848) (after b18b (midS 848)) 8 := by decide +kernel
public theorem b19_keeps : keepsAll regsS (after b19 regsS) (freeRegs slots) = true := by
  decide +kernel
public theorem b20_write : WritesBelow pushS (after b20 pushS) 1 16 ∧
    (∀ i < 8, findWrite 1 (0 + i) (after b20 pushS).mem = some (.reg .r15, i)) ∧
    (∀ i < 8, findWrite 1 (8 + i) (after b20 pushS).mem = some (.reg .rax, i)) := by
  decide +kernel
public theorem b21_call : CallsBelow (gotMidS 848 "memcpy") (after b21 (gotMidS 848 "memcpy")) 56 ∧
    (∀ w ∈ (after b21 (gotMidS 848 "memcpy")).mem, w.off + w.n ≤ 8 ∨ 48 ≤ w.off) ∧
    (∀ i < 8, findWrite 0 (48 + i) (after b21 (gotMidS 848 "memcpy")).mem = some (.reg .r12, i)) := by
  decide +kernel
public theorem b22_write : WritesBelow outS (after b22 outS) 0 8 ∧
    (∀ i < 8, findWrite 0 (0 + i) (after b22 outS).mem = some (.lit 1, i)) := by
  decide +kernel
public theorem b23_write : WritesBelow noneS (after b23 noneS) 1 8 ∧
    (∀ i < 8, findWrite 1 (0 + i) (after b23 noneS).mem = some (.lit 0, i)) := by
  decide +kernel
public theorem b24_restores : restores slots 848 (after b24 (midS 848)) = true ∧
    (after b24 (midS 848)).mem = [] := by
  decide +kernel

public theorem slots_ok : ∀ p ∈ slots, 800 ≤ p.1 ∧ p.1 + 8 ≤ 848 := by decide

end NativeRustcVmX64.Whir.SubspaceTable
