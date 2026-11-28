module

public import NativeRustcVmX64.Whir.MathFrame
public import NativeRustcVmX64.Code.Vm.InducedWeight
public meta import NativeRustcVmX64.Code.Vm.InducedWeight
public meta import NativeRustcVmX64.Whir.MathFrame

/-!
# `induced_weight`'s blocks, run by the symbolic executor (x86-64)

Region 0 of the frame's environment is the 1168-byte frame (`Field.frameS 1168`,
`Field.midS 1168`: the pushes from offset 1120, the 1112 bytes of locals, the calls' return-address
slot at 0) and the return address. From RSP (offset `8`): the products' byte count at 16, the
output pointer at 24, the table's pointer and count at 32, 40, the queries' count at 48, the
queries' and the weights' pointers at 56, 64, the query's index at 72, the sum at 80, 88, the
product's high word at 96, `subspace_table`'s `Option` (later `subspace_at_table`'s `Buf`) from 104,
the table's copy (count at 616, pairs from 624).
- `entryS`: `b0a` (the prologue); `midS`: `b0b`, `b1`, `b3`, `b6`, `b9`, `b10a`, `b10c`,
  `b11`, `b12`, `b13`, `b18b`; `b2` additionally reads the `memcpy` GOT slot;
- `a4S`, `a8S` (region 1 the stack arguments): `b4`, `b8`;
- `wS` (region 1 weight `j`), `qS` (region 1 query `j`): `b7`'s halves;
- `pS` (region 0 the point's element `i`, region 1 `What_i`): `b10b`;
- `regsS`: `b14`, `b15`, `b16`;
- `outS` (region 1 the output the spilled pointer points to): `b17`; `tagS` (region 0 the output's
  tag R14 points to): `b18a`.
-/

namespace NativeRustcVmX64.Whir.InducedWeight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.InducedWeight NativeRustcVmX64.Field
open NativeRustcVmX64.Arrays (keepsRegs keepsAll freeRegs restores)

@[expose] public section

/-- Weight `j`'s address in `b7a`. -/
def wAddr : Sym := .bin .add .W64 (.load 0 64 8) (.bin .shl .W64 (.reg .rsi) (.lit 4))
/-- Query `j`'s address in `b7b`. -/
def qAddr : Sym := .bin .add .W64 (.load 0 56 8) (.bin .mul .W64 (.reg .rsi) (.lit 8))
/-- The point's element's address in `b10b`. -/
def pAddr : Sym := .bin .add .W64 (.reg .r14) (.bin .mul .W64 (.reg .r15) (.lit 2))
/-- `What_i`'s address in `b10b`. -/
def vAddr : Sym := .bin .add .W64 (.bin .add .W64 (.reg .rsp) (.reg .r15)) (.lit 104)

/-- At the entry. -/
abbrev entryS : SState := frameS 1168
/-- Registers only. -/
def regsS : SState := init []
/-- At `b4`: the stack arguments. -/
def a4S : SState := init [1176, 16] [(.rsp, .ptr 0 8)] [] [] [(.ptr 0 1176, 1, 0)]
/-- At `b8`: the stack arguments. -/
def a8S : SState := init [1176, 16] [(.rsp, .ptr 0 8)] [] [] [(.ptr 0 1184, 1, 8)]
/-- At `b7a`: weight `j`. -/
def wS : SState := init [1176, 16] [(.rsp, .ptr 0 8)] [] [] [(wAddr, 1, 0)]
/-- At `b7b`: query `j`. -/
def qS : SState := init [1176, 8] [(.rsp, .ptr 0 8)] [] [] [(qAddr, 1, 0)]
/-- At `b10b`: the point's element, `What_i`. -/
def pS : SState := init [16, 8] [] [] [] [(pAddr, 0, 0), (vAddr, 1, 0)]
/-- At `b17`: the frame, the output the spilled pointer points to. -/
def outS : SState := init [1176, 24] [(.rsp, .ptr 0 8)] [] [] [(.load 0 24 8, 1, 0)]
/-- At `b18a`: the output's tag R14 points to. -/
def tagS : SState := init [8] [(.r14, .ptr 0 0)]

/-- The prologue. -/
def b0a : List Directive := b0.take 8
/-- The spills, `subspace_table`. -/
def b0b : List Directive := b0.drop 8
/-- The spills, weight `j`. -/
def b7a : List Directive := b7.take 8
/-- Query `j`, `subspace_at_table`. -/
def b7b : List Directive := b7.drop 8
/-- The product's spill. -/
def b10a : List Directive := b10.take 2
/-- The point's element, `What_i`. -/
def b10b : List Directive := (b10.drop 2).take 6
/-- `kmul`. -/
def b10c : List Directive := (b10.drop 2).drop 6
/-- The tag's store. -/
def b18a : List Directive := b18.take 2
/-- The epilogue. -/
def b18b : List Directive := b18.drop 2

/-- A write's region, offset and size. -/
def wsig (w : Write) : Nat × Nat × Nat := (w.r, w.off, w.n)
/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) :=
  [(1160, .rbp), (1152, .r15), (1144, .r14), (1136, .r13), (1128, .r12), (1120, .rbx)]

end

set_option Elab.async false

sym_block run_b0a := exec b0a entryS
sym_block run_b0b := exec b0b (midS 1168)
sym_block run_b1 := exec b1 (midS 1168)
sym_block run_b2 := exec b2 (gotMidS 1168 "memcpy")
sym_block run_b3 := exec b3 (midS 1168)
sym_block run_b4 := exec b4 a4S
sym_block run_b6 := exec b6 (midS 1168)
sym_block run_b7a := exec b7a wS
sym_block run_b7b := exec b7b qS
sym_block run_b8 := exec b8 a8S
sym_block run_b9 := exec b9 (midS 1168)
sym_block run_b10a := exec b10a (midS 1168)
sym_block run_b10b := exec b10b pS
sym_block run_b10c := exec b10c (midS 1168)
sym_block run_b11 := exec b11 (midS 1168)
sym_block run_b12 := exec b12 (midS 1168)
sym_block run_b13 := exec b13 (midS 1168)
sym_block run_b14 := exec b14 regsS
sym_block run_b15 := exec b15 regsS
sym_block run_b16 := exec b16 regsS
sym_block run_b17 := exec b17 outS
sym_block run_b18a := exec b18a tagS
sym_block run_b18b := exec b18b (midS 1168)

public theorem b0a_entry : (∀ p ∈ slots, p.1 + 8 ≤ 1168 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b0a entryS).mem = some (.reg p.2, i)) ∧
    (∀ r ∈ freeRegs slots, (after b0a entryS).reg r = some (.reg r)) ∧
    (∀ w ∈ (after b0a entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 1168) ∧
    (after b0a entryS).reg .rsp = some (.ptr 0 8) ∧
    (∀ r ∈ [Reg64.rdi, .rsi, .rdx, .rcx, .r8, .r9], (after b0a entryS).reg r = some (.reg r)) := by
  decide +kernel

public theorem b0b_call : keepsRegs (midS 1168) (after b0b (midS 1168)) (freeRegs slots) = true ∧
    (after b0b (midS 1168)).mem.map wsig = [(0, 0, 8), (0, 56, 8), (0, 64, 8)] ∧
    (∀ i < 8, findWrite 0 (56 + i) (after b0b (midS 1168)).mem = some (.reg .rdx, i)) ∧
    (∀ i < 8, findWrite 0 (64 + i) (after b0b (midS 1168)).mem = some (.reg .r8, i)) := by
  decide +kernel

public theorem b1_keeps : keepsAll (midS 1168) (after b1 (midS 1168)) (freeRegs slots) = true := by
  decide +kernel

public theorem b2_call : keepsRegs (gotMidS 1168 "memcpy") (after b2 (gotMidS 1168 "memcpy")) (freeRegs slots) = true ∧
    (after b2 (gotMidS 1168 "memcpy")).mem.map wsig = [(0, 0, 8), (0, 24, 8)] ∧
    (∀ i < 8, findWrite 0 (24 + i) (after b2 (gotMidS 1168 "memcpy")).mem = some (.reg .r14, i)) := by
  decide +kernel

public theorem b3_write : keepsRegs (midS 1168) (after b3 (midS 1168)) (.rsp :: freeRegs slots) = true ∧
    (after b3 (midS 1168)).mem.map wsig = [(0, 616, 8)] ∧
    (∀ i < 8, findWrite 0 (616 + i) (after b3 (midS 1168)).mem = some (.reg .r14, i)) := by
  decide +kernel

public theorem b4_write : keepsRegs a4S (after b4 a4S) (.rsp :: freeRegs slots) = true ∧
    (after b4 a4S).mem.map wsig = [(0, 40, 8), (0, 48, 8), (0, 32, 8)] ∧
    (∀ i < 8, findWrite 0 (40 + i) (after b4 a4S).mem =
      some (.ite (.not (.cmp .ult .W64 (.reg .r14) (.lit 32))) (.lit 0) (.reg .r14), i)) ∧
    (∀ i < 8, findWrite 0 (48 + i) (after b4 a4S).mem = some (.reg .r15, i)) ∧
    (∀ i < 8, findWrite 0 (32 + i) (after b4 a4S).mem =
      some (.ite (.cmp .ult .W64 (.reg .r14) (.lit 32)) (.reg .r12) (.lit 8), i)) := by
  decide +kernel

public theorem b6_keeps : keepsAll (midS 1168) (after b6 (midS 1168)) (freeRegs slots) = true := by
  decide +kernel

public theorem b7a_write : keepsRegs wS (after b7a wS) (.rsp :: freeRegs slots) = true ∧
    (after b7a wS).mem.map wsig = [(0, 88, 8), (0, 80, 8)] ∧
    (∀ i < 8, findWrite 0 (88 + i) (after b7a wS).mem = some (.reg .rax, i)) ∧
    (∀ i < 8, findWrite 0 (80 + i) (after b7a wS).mem = some (.reg .rcx, i)) := by
  decide +kernel

public theorem b7b_call : keepsRegs qS (after b7b qS) (freeRegs slots) = true ∧
    (after b7b qS).mem.map wsig = [(0, 0, 8), (0, 72, 8)] ∧
    (∀ i < 8, findWrite 0 (72 + i) (after b7b qS).mem = some (.reg .rsi, i)) := by
  decide +kernel

public theorem b8_write : keepsRegs a8S (after b8 a8S) (.rsp :: freeRegs slots) = true ∧
    (after b8 a8S).mem.map wsig = [(0, 16, 8)] ∧
    (∀ i < 8, findWrite 0 (16 + i) (after b8 a8S).mem =
      some (.ite (.not (.cmp .ult .W64 (.load 0 104 8) (.load 1 8 8))) (.load 1 8 8)
        (.load 0 104 8), i)) := by
  decide +kernel

public theorem b9_write : keepsRegs (midS 1168) (after b9 (midS 1168)) (.rsp :: freeRegs slots) = true ∧
    (after b9 (midS 1168)).mem.map wsig = [(0, 16, 8)] ∧
    (∀ i < 8, findWrite 0 (16 + i) (after b9 (midS 1168)).mem =
      some (.bin .shl .W64 (.load 0 16 8) (.lit 3), i)) := by
  decide +kernel

public theorem b10a_write : keepsRegs (midS 1168) (after b10a (midS 1168)) (.rsp :: freeRegs slots) = true ∧
    (after b10a (midS 1168)).mem.map wsig = [(0, 96, 8)] ∧
    (∀ i < 8, findWrite 0 (96 + i) (after b10a (midS 1168)).mem = some (.reg .r12, i)) := by
  decide +kernel

public theorem b10b_keeps : keepsAll pS (after b10b pS) (freeRegs slots) = true := by
  decide +kernel

public theorem b10c_call : keepsRegs (midS 1168) (after b10c (midS 1168)) (freeRegs slots) = true ∧
    (after b10c (midS 1168)).mem.map wsig = [(0, 0, 8)] := by
  decide +kernel

public theorem b11_call : keepsRegs (midS 1168) (after b11 (midS 1168)) (freeRegs slots) = true ∧
    (after b11 (midS 1168)).mem.map wsig = [(0, 0, 8)] := by
  decide +kernel

public theorem b12_call : keepsRegs (midS 1168) (after b12 (midS 1168)) (freeRegs slots) = true ∧
    (after b12 (midS 1168)).mem.map wsig = [(0, 0, 8)] := by
  decide +kernel

public theorem b13_keeps : keepsAll (midS 1168) (after b13 (midS 1168)) (freeRegs slots) = true := by
  decide +kernel
public theorem b14_keeps : keepsAll regsS (after b14 regsS) (freeRegs slots) = true := by
  decide +kernel
public theorem b15_keeps : keepsAll regsS (after b15 regsS) (freeRegs slots) = true := by
  decide +kernel
public theorem b16_keeps : keepsAll regsS (after b16 regsS) (freeRegs slots) = true := by
  decide +kernel

public theorem b17_write : keepsRegs outS (after b17 outS) (.rsp :: freeRegs slots) = true ∧
    (∀ w ∈ (after b17 outS).mem, w.r = 1 ∧ w.off + w.n ≤ 24) ∧
    (∀ i < 8, findWrite 1 (8 + i) (after b17 outS).mem = some (.reg .rcx, i)) ∧
    (∀ i < 8, findWrite 1 (8 + 8 + i) (after b17 outS).mem = some (.reg .rax, i)) := by
  decide +kernel

public theorem b18a_write : keepsRegs tagS (after b18a tagS) (.rsp :: freeRegs slots) = true ∧
    (∀ w ∈ (after b18a tagS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (∀ i < 8, findWrite 0 (0 + i) (after b18a tagS).mem = some (.reg .rax, i)) := by
  decide +kernel

public theorem b18b_restores : restores slots 1168 (after b18b (midS 1168)) = true ∧
    (after b18b (midS 1168)).mem = [] := by
  decide +kernel

public theorem slots_ok : ∀ p ∈ slots, 1120 ≤ p.1 ∧ p.1 + 8 ≤ 1168 := by decide

public theorem freeRegs_nil : freeRegs slots = [] := by decide

end NativeRustcVmX64.Whir.InducedWeight
