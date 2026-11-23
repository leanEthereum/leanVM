module

public import NativeRustcVmX64.Sumcheck.OpenPhase.Common
public import NativeRustcVmX64.Code.Vm.OpenPhase
public import NativeRustcVmX64.Code.Vm.Climb.Names
public import NativeRustcVmX64.Code.Vm.Keccak256WordsOfHashWords.Names
public import NativeRustcVmX64.Code.Vm.OpenPhase.Names
public meta import NativeRustcVmX64.Code.Vm.OpenPhase
public meta import NativeRustcVmX64.Sumcheck.OpenPhase.Common

/-!
# `open_phase`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 176-byte frame below the entry's RSP and the return address (`Frame`, `F = 176`:
RSP at offset `8` in the body, a callee's return address at `0`): the output's address at `16`,
the root's words at `48`, `40`, `32`, `24` (word `i` at `48 - 8 i`), the height at `56`,
`climb`'s output at `64`, `hash_words`' at `96`, the six pushed registers from `128`.

- `entryS` at the entry (`b0a`, `b0`'s first nine directives: the prologue, the phase's address
  loaded from the stack argument): region 1 the stack argument (at RSP + 8, `.ptr 0 184`);
- `phS` for the rest of `b0` (`b0b`: the phase's three counts, R15 region 1);
- `frS` in the frame: the tests, the loops' heads, `b5`, `b10`, `b14`, `b16` to `b20`;
- `posS` at `b7`: region 1 position `j` (R8), region 2 opening `j`'s leaf index (`RBP + RCX`);
- `fail8S` at `b8` (`None` through RDI, then `b9`): region 1 the output;
- `rootS` at `b12`: region 1 the root (RSI);
- `hashS` at `b15`: region 1 opening `j`'s leaf index (`R15 - 520`);
- `outS` at `b21`, `b22` (then `b9`): region 1 the output, its address the word at `16`.
-/

namespace NativeRustcVmX64.Sumcheck.OpenPhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.OpenPhase
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck

@[expose] public section

/-- The frame's slots: the pushed registers. -/
def slots : Slots :=
  [(168, .rbp), (160, .r15), (152, .r14), (144, .r13), (136, .r12), (128, .rbx)]

/-- `b0`'s prologue and stack-argument load. -/
abbrev b0a : List Directive := b0.take 9
/-- `b0`'s loads of the phase's counts and test. -/
abbrev b0b : List Directive := b0.drop 9

def entryS : SState := init [184, 8] [(.rsp, .ptr 0 176)] (aliases := [(.ptr 0 184, (1, 0))])
def phS : SState := init [184, 24] [(.rsp, .ptr 0 8), (.r15, .ptr 1 0)]
def frS : SState := init [184] [(.rsp, .ptr 0 8)]
def posS : SState := init [184, 8, 8] [(.rsp, .ptr 0 8), (.r8, .ptr 1 0)]
  (aliases := [(.bin .add .W64 (.reg .rbp) (.reg .rcx), (2, 0))])
def fail8S : SState := init [184, 32] [(.rsp, .ptr 0 8), (.rdi, .ptr 1 0)]
def rootS : SState := init [184, 32] [(.rsp, .ptr 0 8), (.rsi, .ptr 1 0)]
def hashS : SState := init [184, 8] [(.rsp, .ptr 0 8)] (aliases := [(.reg .r15, (1, 520))])
def outS : SState := init [184, 32] [(.rsp, .ptr 0 8)] (aliases := [(.load 0 16 8, (1, 0))])

/-- `x == 0` as `test x, x`. -/
abbrev isZero (x : Sym) : SBool := .cmp .eq .W64 (.bin .and .W64 x x) (.lit 0)

def c1 : SBool := (SBool.cmp .eq .W64 (.reg .r14) (.reg .rcx)).not
def c2 : SBool := .cmp .eq .W64
  (.bin .or .W64 (.bin .xor .W64 (.reg .r13) (.reg .r9)) (.bin .xor .W64 (.reg .rdx) (.reg .r10)))
  (.lit 0)
def c6 : SBool := .cmp .eq .W64 (.reg .rax) (.reg .rcx)
def c7 : SBool := .cmp .eq .W64 (.load 2 0 8) (.load 1 0 8)
def c11 : SBool :=
  .and (.not (.cmp .ult .W64 (.reg .r14) (.lit 192))) (.not (.cmp .eq .W64 (.reg .r14) (.lit 192)))
def c13 : SBool := .cmp .eq .W64 (.reg .r12) (.lit 256)
/-- `b16` to `b19`: the climbed digest's word `i` against the root's. -/
def cw (i : Nat) : SBool :=
  (SBool.cmp .eq .W64 (.load 0 (64 + 8 * i) 8) (.load 0 (48 - 8 * i) 8)).not
def c20 : SBool := (SBool.cmp .eq .W64 (.reg .r13) (.bin .add .W64 (.reg .r12) (.lit 1))).not

/-- `8 w` as `b14` computes it. -/
def eightW : Sym := .bin .mul .W64 (.reg .r14) (.lit 8)

end

set_option Elab.async false

sym_block run_b0a := exec b0a entryS
sym_block run_b0b := exec b0b phS
sym_block run_b1 := exec b1 frS
sym_block run_b2 := exec b2 frS
sym_block run_b3 := exec b3 frS
sym_block run_b4 := exec b4 frS
sym_block run_b5 := exec b5 frS
sym_block run_b6 := exec b6 frS
sym_block run_b7 := exec b7 posS
sym_block run_b8 := exec b8 fail8S
sym_block run_b9f := exec b9 (after b8 fail8S)
sym_block run_b10 := exec b10 frS
sym_block run_b11 := exec b11 frS
sym_block run_b12 := exec b12 rootS
sym_block run_b13 := exec b13 frS
sym_block run_b14 := exec b14 frS
sym_block run_b15 := exec b15 hashS
sym_block run_b16 := exec b16 frS
sym_block run_b17 := exec b17 frS
sym_block run_b18 := exec b18 frS
sym_block run_b19 := exec b19 frS
sym_block run_b20 := exec b20 frS
sym_block run_b21 := exec b21 outS
sym_block run_b9r := exec b9 (after b21 outS)
sym_block run_b22 := exec b22 outS
sym_block run_b9n := exec b9 (after b22 outS)

public theorem b0a_in_code : b0a.IsInfixAt code (NativeRustcVmX64.Vm.OpenPhase.b0Offset) :=
  (infix_take b0 9).trans b0_in_code (fun h ↦ absurd (congrArg List.length h) (by decide))
public theorem b0b_in_code : b0b.IsInfixAt code (NativeRustcVmX64.Vm.OpenPhase.b0Offset + b0a.length) :=
  (infix_drop b0 9).trans b0_in_code (fun h ↦ absurd (congrArg List.length h) (by decide))
public theorem b0a_ne : b0a ≠ [] := fun h ↦ absurd (congrArg List.length h) (by decide)
public theorem b0b_ne : b0b ≠ [] := fun h ↦ absurd (congrArg List.length h) (by decide)

public theorem exit_b0a : exec b0a entryS = some (after b0a entryS, .fall) :=
  run_b0a.trans (by rw [after_eq run_b0a])
public theorem ok_b0a : ProOk 176 8 slots (after b0a entryS) = true ∧
    (∀ w ∈ (after b0a entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 176) ∧
    (after b0a entryS).reg .r15 = some (.load 1 0 8) ∧
    KeepBut [.r15] (after b0a entryS) = true := by
  decide +kernel
public theorem exit_b0b :
    exec b0b phS = some (after b0b phS, .cond (isZero (.load 1 0 8)) NativeRustcVmX64.Vm.OpenPhase.label_1) :=
  run_b0b.trans (by rw [after_eq run_b0b])
public theorem ok_b0b : MidOk 176 8 slots (after b0b phS) = true ∧ (after b0b phS).mem = [] ∧
    (after b0b phS).reg .r13 = some (.load 1 0 8) ∧
    (after b0b phS).reg .r10 = some (.load 1 8 8) ∧
    (after b0b phS).reg .r14 = some (.load 1 16 8) ∧
    (after b0b phS).reg .r15 = some (.ptr 1 0) ∧
    KeepBut [.r10, .r13, .r14, .r15] (after b0b phS) = true := by
  decide +kernel

/-- A test block of the frame: no write, every register kept. -/
public abbrev TestOk (S : SState) : Prop :=
  MidOk 176 8 slots S = true ∧ S.mem = [] ∧ KeepBut [] S = true

public theorem exit_b1 : exec b1 frS = some (after b1 frS, .cond c1 NativeRustcVmX64.Vm.OpenPhase.label_16) :=
  run_b1.trans (by rw [after_eq run_b1]; rfl)
public theorem ok_b1 : TestOk (after b1 frS) := by decide +kernel
public theorem exit_b2 : exec b2 frS = some (after b2 frS, .cond c2 NativeRustcVmX64.Vm.OpenPhase.label_2) :=
  run_b2.trans (by rw [after_eq run_b2]; rfl)
public theorem ok_b2 : MidOk 176 8 slots (after b2 frS) = true ∧ (after b2 frS).mem = [] ∧
    KeepBut [.rax, .rdx] (after b2 frS) = true := by
  decide +kernel
public theorem exit_b3 : exec b3 frS = some (after b3 frS, .jump NativeRustcVmX64.Vm.OpenPhase.label_16) :=
  run_b3.trans (by rw [after_eq run_b3])
public theorem ok_b3 : TestOk (after b3 frS) := by decide +kernel
public theorem exit_b4 :
    exec b4 frS = some (after b4 frS, .cond (isZero (.reg .r9)).not NativeRustcVmX64.Vm.OpenPhase.label_16) :=
  run_b4.trans (by rw [after_eq run_b4])
public theorem ok_b4 : TestOk (after b4 frS) := by decide +kernel
public theorem exit_b5 : exec b5 frS = some (after b5 frS, .fall) :=
  run_b5.trans (by rw [after_eq run_b5])
public theorem ok_b5 : MidOk 176 8 slots (after b5 frS) = true ∧ (after b5 frS).mem = [] ∧
    (after b5 frS).reg .rbp = some (.bin .add .W64 (.reg .r15) (.lit 24)) ∧
    (after b5 frS).reg .rax = some (.bin .mul .W64 (.reg .r9) (.lit 1544)) ∧
    (after b5 frS).reg .rcx = some (.lit 0) ∧
    KeepBut [.rax, .rbp, .rcx] (after b5 frS) = true := by
  decide +kernel
public theorem exit_b6 : exec b6 frS = some (after b6 frS, .cond c6 NativeRustcVmX64.Vm.OpenPhase.label_4) :=
  run_b6.trans (by rw [after_eq run_b6]; rfl)
public theorem ok_b6 : TestOk (after b6 frS) := by decide +kernel
public theorem exit_b7 : exec b7 posS = some (after b7 posS, .cond c7 NativeRustcVmX64.Vm.OpenPhase.label_3) :=
  run_b7.trans (by rw [after_eq run_b7]; rfl)
public theorem ok_b7 : MidOk 176 8 slots (after b7 posS) = true ∧ (after b7 posS).mem = [] ∧
    (after b7 posS).reg .rcx = some (.bin .add .W64 (.lit 1544) (.reg .rcx)) ∧
    (after b7 posS).reg .r8 = some (.ptr 1 8) ∧
    KeepBut [.rcx, .rdx, .r8] (after b7 posS) = true := by
  decide +kernel
public theorem exit_b8 : exec b8 fail8S = some (after b8 fail8S, .fall) :=
  run_b8.trans (by rw [after_eq run_b8])
public theorem exit_b9f : exec b9 (after b8 fail8S) =
    some (after b9 (after b8 fail8S), .ret (.load 0 176 8)) :=
  run_b9f.trans (by rw [after_eq run_b9f])
public theorem ok_b9f : EpiOk 176 slots (after b9 (after b8 fail8S)) = true ∧
    WordW 1 0 (.lit 0) (after b9 (after b8 fail8S)) ∧
    (∀ w ∈ (after b9 (after b8 fail8S)).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 32) := by
  decide +kernel
public theorem exit_b10 :
    exec b10 frS = some (after b10 frS, .cond (isZero (.reg .r13)) NativeRustcVmX64.Vm.OpenPhase.label_13) :=
  run_b10.trans (by rw [after_eq run_b10])
public theorem ok_b10 : MidOk 176 8 slots (after b10 frS) = true ∧
    (∀ w ∈ (after b10 frS).mem, w.r = 0 ∧ w.off + w.n ≤ 176) ∧
    WordW 0 16 (.reg .rdi) (after b10 frS) ∧ WordW 0 56 (.reg .r10) (after b10 frS) ∧
    KeepBut [] (after b10 frS) = true := by
  decide +kernel
public theorem exit_b11 : exec b11 frS = some (after b11 frS, .cond c11 NativeRustcVmX64.Vm.OpenPhase.label_19) :=
  run_b11.trans (by rw [after_eq run_b11]; rfl)
public theorem ok_b11 : TestOk (after b11 frS) := by decide +kernel
public theorem exit_b12 : exec b12 rootS = some (after b12 rootS, .fall) :=
  run_b12.trans (by rw [after_eq run_b12])
public theorem ok_b12 : MidOk 176 8 slots (after b12 rootS) = true ∧
    (∀ w ∈ (after b12 rootS).mem, w.r = 0 ∧ 24 ≤ w.off ∧ w.off + w.n ≤ 56) ∧
    WordW 0 48 (.load 1 0 8) (after b12 rootS) ∧ WordW 0 40 (.load 1 8 8) (after b12 rootS) ∧
    WordW 0 32 (.load 1 16 8) (after b12 rootS) ∧ WordW 0 24 (.load 1 24 8) (after b12 rootS) ∧
    (after b12 rootS).reg .r12 = some (.lit 0) ∧
    (after b12 rootS).reg .r15 = some (.bin .add .W64 (.lit 544) (.reg .r15)) ∧
    KeepBut [.rax, .rsi, .r12, .r15] (after b12 rootS) = true := by
  decide +kernel
public theorem exit_b13 : exec b13 frS = some (after b13 frS, .cond c13 NativeRustcVmX64.Vm.OpenPhase.label_19) :=
  run_b13.trans (by rw [after_eq run_b13]; rfl)
public theorem ok_b13 : TestOk (after b13 frS) := by decide +kernel
public theorem exit_b14 : exec b14 frS = some (after b14 frS,
    .call NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.entryLabel) :=
  run_b14.trans (by rw [after_eq run_b14])
public theorem ok_b14 : MidOk 176 0 slots (after b14 frS) = true ∧
    (∀ w ∈ (after b14 frS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b14 frS).reg .rdi = some (.ptr 0 96) ∧ (after b14 frS).reg .rbx = some (.ptr 0 96) ∧
    (after b14 frS).reg .rsi = some (.reg .r14) ∧ (after b14 frS).reg .rdx = some eightW ∧
    (after b14 frS).reg .rcx = some (.bin .add .W64 (.reg .r15) (.lit 18446744073709551104)) ∧
    (after b14 frS).reg .r8 = some (.reg .r14) ∧
    KeepBut [.rbx, .rcx, .rdx, .rsi, .rdi, .r8] (after b14 frS) = true := by
  decide +kernel
public theorem exit_b15 : exec b15 hashS = some (after b15 hashS,
    .call NativeRustcVmX64.Vm.Climb.entryLabel) :=
  run_b15.trans (by rw [after_eq run_b15])
public theorem ok_b15 : MidOk 176 0 slots (after b15 hashS) = true ∧
    (∀ w ∈ (after b15 hashS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b15 hashS).reg .rdi = some (.ptr 0 64) ∧ (after b15 hashS).reg .rsi = some (.reg .rbx) ∧
    (after b15 hashS).reg .rdx = some (.load 1 0 8) ∧
    (after b15 hashS).reg .rcx = some (.reg .r15) ∧
    (after b15 hashS).reg .r8 = some (.load 0 56 8) ∧
    KeepBut [.rcx, .rdx, .rsi, .rdi, .r8] (after b15 hashS) = true := by
  decide +kernel
public theorem exit_b16 : exec b16 frS = some (after b16 frS, .cond (cw 0) NativeRustcVmX64.Vm.OpenPhase.label_19) :=
  run_b16.trans (by rw [after_eq run_b16]; rfl)
public theorem exit_b17 : exec b17 frS = some (after b17 frS, .cond (cw 1) NativeRustcVmX64.Vm.OpenPhase.label_19) :=
  run_b17.trans (by rw [after_eq run_b17]; rfl)
public theorem exit_b18 : exec b18 frS = some (after b18 frS, .cond (cw 2) NativeRustcVmX64.Vm.OpenPhase.label_19) :=
  run_b18.trans (by rw [after_eq run_b18]; rfl)
public theorem exit_b19 : exec b19 frS = some (after b19 frS, .cond (cw 3) NativeRustcVmX64.Vm.OpenPhase.label_19) :=
  run_b19.trans (by rw [after_eq run_b19]; rfl)
/-- A word test of `b16` to `b19`: no write, every register but RAX kept. -/
public abbrev WTestOk (S : SState) : Prop :=
  MidOk 176 8 slots S = true ∧ S.mem = [] ∧ KeepBut [.rax] S = true
public theorem ok_b16 : WTestOk (after b16 frS) := by decide +kernel
public theorem ok_b17 : WTestOk (after b17 frS) := by decide +kernel
public theorem ok_b18 : WTestOk (after b18 frS) := by decide +kernel
public theorem ok_b19 : WTestOk (after b19 frS) := by decide +kernel
public theorem exit_b20 : exec b20 frS = some (after b20 frS, .cond c20 NativeRustcVmX64.Vm.OpenPhase.label_7) :=
  run_b20.trans (by rw [after_eq run_b20]; rfl)
public theorem ok_b20 : MidOk 176 8 slots (after b20 frS) = true ∧ (after b20 frS).mem = [] ∧
    (after b20 frS).reg .r12 = some (.bin .add .W64 (.reg .r12) (.lit 1)) ∧
    (after b20 frS).reg .r15 = some (.bin .add .W64 (.lit 1544) (.reg .r15)) ∧
    KeepBut [.r12, .r15] (after b20 frS) = true := by
  decide +kernel
public theorem exit_b21 : exec b21 outS = some (after b21 outS, .jump NativeRustcVmX64.Vm.OpenPhase.label_17) :=
  run_b21.trans (by rw [after_eq run_b21])
public theorem exit_b9r : exec b9 (after b21 outS) =
    some (after b9 (after b21 outS), .ret (.load 0 176 8)) :=
  run_b9r.trans (by rw [after_eq run_b9r])
public theorem ok_b9r : EpiOk 176 slots (after b9 (after b21 outS)) = true ∧
    WordW 1 0 (.reg .rbp) (after b9 (after b21 outS)) ∧
    WordW 1 8 (.lit 49408) (after b9 (after b21 outS)) ∧
    WordW 1 16 (.reg .r13) (after b9 (after b21 outS)) ∧
    WordW 1 24 (.reg .r14) (after b9 (after b21 outS)) ∧
    (∀ w ∈ (after b9 (after b21 outS)).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 32) := by
  decide +kernel
public theorem exit_b22 : exec b22 outS = some (after b22 outS, .jump NativeRustcVmX64.Vm.OpenPhase.label_17) :=
  run_b22.trans (by rw [after_eq run_b22])
public theorem exit_b9n : exec b9 (after b22 outS) =
    some (after b9 (after b22 outS), .ret (.load 0 176 8)) :=
  run_b9n.trans (by rw [after_eq run_b9n])
public theorem ok_b9n : EpiOk 176 slots (after b9 (after b22 outS)) = true ∧
    WordW 1 0 (.lit 0) (after b9 (after b22 outS)) ∧
    (∀ w ∈ (after b9 (after b22 outS)).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 32) := by
  decide +kernel

end NativeRustcVmX64.Sumcheck.OpenPhase
