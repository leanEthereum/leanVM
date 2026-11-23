module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.LinearTranspose
public import NativeRustcVmX64.Code.Vm.KeccakPi.Names
public import NativeRustcVmX64.Code.Vm.LinearTranspose.Names
public import NativeRustcVmX64.Code.Vm.Names
public meta import NativeRustcVmX64.Code.Vm.LinearTranspose
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `linear_transpose`'s blocks, run by the symbolic executor (x86-64)

Region 0 of the prologue's and the calls' states is the 64-byte frame (RBP to RBX pushed at
offsets `56` to `16`, RAX's push at `8`, a call's return address at `0`) and the return address.
The blocks without memory accesses run from `regsS`. `KECCAK_RHO`'s load (`b2`) from `rhoS`
(region 1 the 100 bytes at its label, the lane R13 below 25). The copy loop (`b3`) from `copyS`:
region 0 the source lane (RAX), region 1 the two elements of `g` at `RBP + RDX - 24`, the two
positions' byte offsets below 1009. A column loop (`b6`, `b8`, …, `b14`, column `x`) from
`colS x`: region 0 `g` from `R15 + RAX`, region 1 the column's element at `R14 + RAX + 1024 x`. The
output loop (`b17`) from `outS`: region 0 `g`'s element at `R15 + R11 - 8`, region 1 the column
`(x + 1) % 5`'s at `RAX + R11 - 8`, region 2 the column `(x + 4) % 5` (RDX), region 3 the output's
element at `RBX + R11 - 8`, the next position's byte offset below 1009.
-/

namespace NativeRustcVmX64.KeccakGkr.LinearTranspose

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.LinearTranspose NativeRustcVmX64.Transcript

@[expose] public section

/-- The frame's slots. -/
def slots : Slots :=
  [(56, .rbp), (48, .r15), (40, .r14), (32, .r13), (24, .r12), (16, .rbx)]

/-- `KECCAK_RHO`'s label. -/
abbrev rhoL : Label := NativeRustcVmX64.Vm.Symbols.rodata2Label

/-- A position's byte offset in a lane: `16 ((x as u32) & 63)`. -/
def posS (x : Sym) : Sym := .bin .shl .W32 (.bin .and .W32 (.un .trunc .W32 x) (.lit 63)) (.lit 4)

/-- The copy loop's first position. -/
def i1S : Sym := posS (.reg .rcx)
/-- The copy loop's second position. -/
def i2S : Sym := posS (.bin .add .W64 (.reg .rcx) (.lit 1))
/-- The output loop's next position. -/
def i3S : Sym := posS (.reg .r10)

def entryS : SState := init [72] [(.rsp, .ptr 0 64)]
def callS : SState := init [72] [(.rsp, .ptr 0 8)]
def regsS : SState := init []
def rhoS : SState := init [72, 100] [(.rsp, .ptr 0 8)] [(rhoL, 1)] [(.reg .r13, 25)]
def copyS : SState :=
  init [1024, 32] [(.rax, .ptr 0 0)] [] [(i1S, 1009), (i2S, 1009)]
    [(.bin .add .W64 (.reg .rbp) (.reg .rdx), 1, 24)]
def colS (x : Nat) : SState :=
  init [20496 + 1024 * x, 16] [] [] []
    [(.bin .add .W64 (.reg .r15) (.reg .rax), 0, 0),
      (.bin .add .W64 (.reg .r14) (.reg .rax), 1, -((1024 * x : Nat) : Int))]
/-- `b16`'s start at lane `l`: its constants and the lane known. -/
def s16 (l : Nat) : SState :=
  init [] [(.rcx, .lit l), (.r8, .lit 14757395258967641293), (.r9, .lit 4096), (.rdi, .lit 0)]

/-- The sum of a column's word `d`, as rustc's `xor` chain. -/
def treeS (x d : Nat) : Sym :=
  .bin .xor .W64 (.bin .xor .W64 (.bin .xor .W64 (.bin .xor .W64
    (.load 0 (1024 * x + 5120 + d) 8) (.load 0 (1024 * x + d) 8)) (.load 0 (1024 * x + 10240 + d) 8))
    (.load 0 (1024 * x + 15360 + d) 8)) (.load 0 (1024 * x + 20480 + d) 8)

/-- The output element's word `d`. -/
def outW (d : Nat) : Sym :=
  .bin .xor .W64 (.bin .xor .W64 (.load 1 d 8) (.load 0 d 8)) (.loadx 2 d i3S 8)

/-- A register holding `r`'s atom plus `c`, as the executor writes it. -/
def isAddLit (v : Option Sym) (r : Reg64) (c : Nat) : Bool :=
  v == some (.bin .add .W64 (.reg r) (.lit c)) || v == some (.bin .add .W64 (.lit c) (.reg r)) ||
    (c == 0 && v == some (.reg r))

/-- Registers holding their atoms. -/
def atoms (S : SState) (rs : List Reg64) : Bool := rs.all fun r ↦ S.reg r == some (.reg r)

/-- A block without memory accesses: no write, RSP kept. -/
def regOk (S : SState) : Bool := S.mem.isEmpty && S.reg .rsp == some (.reg .rsp)

/-- A column loop's block, column `x`: the column's element the two `xor` chains, RAX counted. -/
def colOk (x : Nat) (S : SState) : Bool :=
  S.reg .rsp == some (.reg .rsp) && atoms S [.r12, .r14, .r15, .rbx] &&
    S.reg .rax == some (.bin .add .W64 (.lit 16) (.reg .rax)) &&
    S.mem.all (fun w ↦ w.r == 1 && decide (w.off + w.n ≤ 16)) &&
    (List.range 8).all (fun t ↦ findWrite 1 t S.mem == some (treeS x 0, t) &&
      findWrite 1 (8 + t) S.mem == some (treeS x 8, t))

def outS : SState :=
  init [16, 16, 1024, 16] [(.rdx, .ptr 2 0)] [] [(i3S, 1009)]
    [(.bin .add .W64 (.reg .r15) (.reg .r11), 0, 8), (.bin .add .W64 (.reg .rax) (.reg .r11), 1, 8),
      (.bin .add .W64 (.reg .rbx) (.reg .r11), 3, 8)]

end

set_option Elab.async false

sym_block e0 := exec b0 entryS
sym_block e1 := exec b1 callS
sym_block e2 := exec b2 rhoS
sym_block e3 := exec b3 copyS
sym_block e4 := exec b4 regsS
sym_block e5 := exec b5 regsS
sym_block e6 := exec b6 (colS 0)
sym_block e7 := exec b7 regsS
sym_block e8 := exec b8 (colS 1)
sym_block e9 := exec b9 regsS
sym_block e10 := exec b10 (colS 2)
sym_block e11 := exec b11 regsS
sym_block e12 := exec b12 (colS 3)
sym_block e13 := exec b13 regsS
sym_block e14 := exec b14 (colS 4)
sym_block e15 := exec b15 regsS
sym_block e17 := exec b17 outS
sym_block e18 := exec b18 regsS
sym_block e19 := exec b19 callS

public section

theorem ok_b0 : ProOk 64 8 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 64) ∧
    (after b0 entryS).reg .rbx = some (.reg .rcx) ∧ (after b0 entryS).reg .r14 = some (.reg .rdx) ∧
    (after b0 entryS).reg .r15 = some (.reg .rsi) ∧ (after b0 entryS).reg .r12 = some (.reg .rdi) ∧
    (after b0 entryS).reg .rbp = some (.bin .add .W64 (.reg .rsi) (.lit 24)) ∧
    (after b0 entryS).reg .r13 = some (.lit 0) := by
  rw [after_eq e0]; decide +kernel

theorem exit_b0 : exec b0 entryS = some (after b0 entryS, .fall) := e0.trans (by rw [after_eq e0])

theorem ok_b1 : MidOk 64 0 slots (after b1 callS) = true ∧
    (∀ w ∈ (after b1 callS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b1 callS).reg .rdi = some (.reg .r13) ∧
    atoms (after b1 callS) [.r12, .r13, .r14, .r15, .rbx, .rbp] = true := by
  rw [after_eq e1]; decide +kernel

theorem exit_b1 : exec b1 callS = some (after b1 callS,
    .call NativeRustcVmX64.Vm.KeccakPi.entryLabel) := e1.trans (by rw [after_eq e1])

theorem ok_b2 : MidOk 64 8 slots (after b2 rhoS) = true ∧ (after b2 rhoS).mem = [] ∧
    (after b2 rhoS).reg .rcx = some (.loadx 1 0 (.bin .mul .W64 (.reg .r13) (.lit 4)) 4) ∧
    (after b2 rhoS).reg .rax =
      some (.bin .add .W64 (.reg .r12) (.bin .shl .W32 (.reg .rax) (.lit 10))) ∧
    (after b2 rhoS).reg .rdx = some (.lit 0) ∧
    atoms (after b2 rhoS) [.r12, .r13, .r14, .r15, .rbx, .rbp] = true := by
  rw [after_eq e2]; decide +kernel

theorem exit_b2 : exec b2 rhoS = some (after b2 rhoS, .fall) := e2.trans (by rw [after_eq e2])

theorem ok_b3 : (after b3 copyS).reg .rsp = some (.reg .rsp) ∧
    atoms (after b3 copyS) [.r12, .r13, .r14, .r15, .rbx, .rbp] = true ∧
    (after b3 copyS).reg .rdx = some (.bin .add .W64 (.lit 32) (.reg .rdx)) ∧
    (after b3 copyS).reg .rcx = some (.bin .add .W64 (.lit 2) (.reg .rcx)) ∧
    (after b3 copyS).reg .rax = some (.ptr 0 0) ∧
    (∀ w ∈ (after b3 copyS).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 32) ∧
    (∀ t < 8, findWrite 1 t (after b3 copyS).mem = some (.loadx 0 0 i1S 8, t) ∧
      findWrite 1 (8 + t) (after b3 copyS).mem = some (.loadx 0 8 i1S 8, t) ∧
      findWrite 1 (16 + t) (after b3 copyS).mem = some (.loadx 0 0 i2S 8, t) ∧
      findWrite 1 (24 + t) (after b3 copyS).mem = some (.loadx 0 8 i2S 8, t)) := by
  rw [after_eq e3]; decide +kernel

theorem exit_b3 : exec b3 copyS = some (after b3 copyS,
    .cond (SBool.cmp .eq .W64 (.bin .add .W64 (.lit 32) (.reg .rdx)) (.lit 1024)).not
      NativeRustcVmX64.Vm.LinearTranspose.label_2) := e3.trans (by rw [after_eq e3])

theorem ok_b4 : regOk (after b4 regsS) = true ∧
    atoms (after b4 regsS) [.r12, .r14, .r15, .rbx] = true ∧
    (after b4 regsS).reg .r13 = some (.bin .add .W64 (.reg .r13) (.lit 1)) ∧
    (after b4 regsS).reg .rbp = some (.bin .add .W64 (.lit 1024) (.reg .rbp)) := by
  rw [after_eq e4]; decide +kernel

theorem exit_b4 : exec b4 regsS = some (after b4 regsS,
    .cond (SBool.cmp .eq .W64 (.bin .add .W64 (.reg .r13) (.lit 1)) (.lit 25)).not
      NativeRustcVmX64.Vm.LinearTranspose.label_1) := e4.trans (by rw [after_eq e4])

/-- `b5`, `b7`, `b9`, `b11`, `b13`: RAX zeroed. -/
theorem ok_zero : ∀ b ∈ [b5, b7, b9, b11, b13], (exec b regsS).map (fun p ↦ (p.2,
    regOk p.1 && atoms p.1 [.r12, .r14, .r15, .rbx] && p.1.reg .rax == some (.lit 0))) =
    some (.fall, true) := by
  rw [show [b5, b7, b9, b11, b13] = _ from rfl]
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · rw [e5]; decide +kernel
  · rw [e7]; decide +kernel
  · rw [e9]; decide +kernel
  · rw [e11]; decide +kernel
  · rw [e13]; decide +kernel

theorem ok_cols : (exec b6 (colS 0)).map (fun p ↦ (colOk 0 p.1, p.2)) = some (true, .cond
      (SBool.cmp .eq .W64 (.bin .add .W64 (.lit 16) (.reg .rax)) (.lit 1024)).not
      NativeRustcVmX64.Vm.LinearTranspose.label_5) ∧
    (exec b8 (colS 1)).map (fun p ↦ (colOk 1 p.1, p.2)) = some (true, .cond
      (SBool.cmp .eq .W64 (.bin .add .W64 (.lit 16) (.reg .rax)) (.lit 1024)).not
      NativeRustcVmX64.Vm.LinearTranspose.label_7) ∧
    (exec b10 (colS 2)).map (fun p ↦ (colOk 2 p.1, p.2)) = some (true, .cond
      (SBool.cmp .eq .W64 (.bin .add .W64 (.lit 16) (.reg .rax)) (.lit 1024)).not
      NativeRustcVmX64.Vm.LinearTranspose.label_9) ∧
    (exec b12 (colS 3)).map (fun p ↦ (colOk 3 p.1, p.2)) = some (true, .cond
      (SBool.cmp .eq .W64 (.bin .add .W64 (.lit 16) (.reg .rax)) (.lit 1024)).not
      NativeRustcVmX64.Vm.LinearTranspose.label_11) ∧
    (exec b14 (colS 4)).map (fun p ↦ (colOk 4 p.1, p.2)) = some (true, .cond
      (SBool.cmp .eq .W64 (.bin .add .W64 (.lit 16) (.reg .rax)) (.lit 1024)).not
      NativeRustcVmX64.Vm.LinearTranspose.label_13) := by
  rw [e6, e8, e10, e12, e14]; decide +kernel

theorem ok_b15 : regOk (after b15 regsS) = true ∧ atoms (after b15 regsS) [.r14] = true ∧
    (after b15 regsS).reg .rsi = some (.bin .add .W64 (.reg .r14) (.lit 8)) ∧
    (after b15 regsS).reg .rbx = some (.bin .add .W64 (.lit 8) (.reg .rbx)) ∧
    (after b15 regsS).reg .r15 = some (.bin .add .W64 (.lit 8) (.reg .r15)) ∧
    (after b15 regsS).reg .rdi = some (.lit 0) ∧
    (after b15 regsS).reg .r8 = some (.lit 14757395258967641293) ∧
    (after b15 regsS).reg .r9 = some (.lit 4096) ∧ (after b15 regsS).reg .rcx = some (.lit 0) := by
  rw [after_eq e15]; decide +kernel

theorem exit_b15 : exec b15 regsS = some (after b15 regsS, .fall) := e15.trans (by rw [after_eq e15])

/-- `b16` at lane `l`: the two columns' addresses. -/
theorem ok_b16 : ∀ l, l < 25 → (exec b16 (s16 l)).map (fun p ↦ (p.2, regOk p.1 &&
    atoms p.1 [.rsi, .r14, .r15, .rbx] && p.1.reg .rcx == some (.lit l) &&
    p.1.reg .r8 == some (.lit 14757395258967641293) && p.1.reg .r9 == some (.lit 4096) &&
    p.1.reg .rdi == some (.lit 0) && p.1.reg .r10 == some (.lit 1) && p.1.reg .r11 == some (.lit 0) &&
    isAddLit (p.1.reg .rax) .rsi (1024 * ((l % 5 + 1) % 5)) &&
    isAddLit (p.1.reg .rdx) .r14 (1024 * ((l % 5 + 4) % 5)))) = some (.fall, true) := by
  decide +kernel

theorem ok_b17 : (after b17 outS).reg .rsp = some (.reg .rsp) ∧
    atoms (after b17 outS) [.rax, .rsi, .rdi, .rcx, .r8, .r9, .r14, .r15, .rbx] = true ∧
    (after b17 outS).reg .rdx = some (.ptr 2 0) ∧
    (after b17 outS).reg .r11 = some (.bin .add .W64 (.lit 16) (.reg .r11)) ∧
    (after b17 outS).reg .r10 = some (.bin .add .W64 (.reg .r10) (.lit 1)) ∧
    (∀ w ∈ (after b17 outS).mem, w.r = 3 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 16) ∧
    (∀ t < 8, findWrite 3 t (after b17 outS).mem = some (outW 0, t) ∧
      findWrite 3 (8 + t) (after b17 outS).mem = some (outW 8, t)) := by
  rw [after_eq e17]; decide +kernel

theorem exit_b17 : exec b17 outS = some (after b17 outS,
    .cond (SBool.cmp .eq .W64 (.bin .add .W64 (.lit 16) (.reg .r11)) (.lit 1024)).not
      NativeRustcVmX64.Vm.LinearTranspose.label_17) := e17.trans (by rw [after_eq e17])

theorem ok_b18 : regOk (after b18 regsS) = true ∧
    atoms (after b18 regsS) [.rsi, .rdi, .r8, .r9, .r14] = true ∧
    (after b18 regsS).reg .rcx = some (.bin .add .W64 (.reg .rcx) (.lit 1)) ∧
    (after b18 regsS).reg .rbx = some (.bin .add .W64 (.lit 1024) (.reg .rbx)) ∧
    (after b18 regsS).reg .r15 = some (.bin .add .W64 (.lit 1024) (.reg .r15)) := by
  rw [after_eq e18]; decide +kernel

theorem exit_b18 : exec b18 regsS = some (after b18 regsS,
    .cond (SBool.cmp .eq .W64 (.bin .add .W64 (.reg .rcx) (.lit 1)) (.lit 25)).not
      NativeRustcVmX64.Vm.LinearTranspose.label_16) := e18.trans (by rw [after_eq e18])

theorem ok_b19 : EpiOk 64 slots (after b19 callS) = true ∧ (after b19 callS).mem = [] := by
  rw [after_eq e19]; decide +kernel

theorem exit_b19 : exec b19 callS = some (after b19 callS, .ret (.load 0 64 8)) :=
  e19.trans (by rw [after_eq e19])

end

end NativeRustcVmX64.KeccakGkr.LinearTranspose
