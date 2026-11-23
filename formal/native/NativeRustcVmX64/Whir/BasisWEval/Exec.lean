module

public import NativeRustcVmX64.Whir.BasisWEval.Frame
public import NativeRustcVmX64.Code.Vm.BasisWEval
public import NativeRustcVmX64.Code.Vm.BasisWEval.Names
public import NativeRustcVmX64.Code.Vm.ColumnWeight.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqEval.Names
public import NativeRustcVmX64.Code.Vm.LayoutWPlacement.Names
public import NativeRustcVmX64.Code.Vm.RingClaimWeight.Names
public meta import NativeRustcVmX64.Code.Vm.BasisWEval
public meta import NativeRustcVmX64.Whir.BasisWEval.Frame

/-!
# `BasisW::eval`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 160-byte frame below the entry's RSP and the return address (`Fr`, `F = 160`):
the six pushes at `152` down to `112`, the 88-byte locals from `24` (RSP at offset `24` in the
body), `ring_claim_weight`'s and `column_weight`'s two pushed argument words at `8`, `16` and
their return address at `0` (RSP at `0` at their calls), the other callees' return address at
`16`. The locals: the sum's limb `0` (`24`), the output's address (`32`), the point (`40`, `48`),
the `BasisW`'s address (`56`), the sum's limb `1` (`64`), the layout's address (`72`), the
callees' `Option<EW>` (`80` to `103`), the placements' address (`104`).

- `entryS` (`b0`): the frame, the `BasisW` (RSI).
- `bodyS o` (`b1`, `b3`, `b6`, `b8`, `b10`, `b15`, `b18`, `b19`, `b21`, `b23`, `b25`): the frame,
  RSP at `o`; `b5`, `b17` at `8`, after a call with two argument words.
- `scaleS r` (`b2` RBP, `b14`, `b22` R13): a scale.
- `ringS` (`b4`): the `BasisW` (RBX), the Keccak output's point count (loaded from it).
- `claimsS` (`b7`): the `BasisW` (RBX), the claims' count (loaded from it).
- `colS` (`b11`): a column claim, R12 16 bytes into it.
- `placeS` (`b12`), `pentS` (`b13`): the placement entry, at the address the blocks compute from
  the placements' address (RCX) and three times the column (RAX).
- `cwS` (`b16`): a column claim (R12), the layout's head (its address loaded from the frame).
- `oodS` (`b24`): the `BasisW` (its address loaded from the frame), the out-of-domain point's
  count (loaded from it).
- `outS` (`b26`, `b27` after it): the `Option<EW>` output (its address loaded from the frame).
-/

namespace NativeRustcVmX64.Whir.BasisWEval

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.BasisWEval NativeRustcVmX64.Transcript

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(152, .rbp), (144, .r15), (136, .r14), (128, .r13), (120, .r12), (112, .rbx)]

/-- At the entry. -/
def entryS : SState := init [168, 56] [(.rsp, .ptr 0 160), (.rsi, .ptr 1 0)]
/-- The frame, RSP at offset `o`. -/
def bodyS (o : Nat) : SState := init [168] [(.rsp, .ptr 0 (o : Int))]
/-- A scale at the register `r`. -/
def scaleS (r : Reg64) : SState := init [168, 16] [(.rsp, .ptr 0 24), (r, .ptr 1 0)]
/-- The ring claim's call. -/
def ringS : SState :=
  init [168, 56, 8] [(.rsp, .ptr 0 24), (.rbx, .ptr 1 0)] [] [] [(.load 1 32 8, 2, 0)]
/-- The claims' count. -/
def claimsS : SState :=
  init [168, 56, 8] [(.rsp, .ptr 0 24), (.rbx, .ptr 1 0)] [] [] [(.load 1 40 8, 2, 0)]
/-- A column claim. -/
def colS : SState := init [168, 608] [(.rsp, .ptr 0 24), (.r12, .ptr 1 16)]
/-- Three times the column, as `b12` computes it from RAX. -/
def col3 : Sym := .bin .add .W64 (.reg .rax) (.bin .mul .W64 (.reg .rax) (.lit 2))
/-- The placement entry's address `b12` computes. -/
def placeSym : Sym := .bin .add .W64 (.reg .rcx) (.bin .mul .W64 col3 (.lit 8))
/-- The placement entry, `b12`. -/
def placeS : SState := init [168, 24] [(.rsp, .ptr 0 24)] [] [] [(placeSym, 1, 0)]
/-- The placement entry's address `b13` computes. -/
def pentSym : Sym := .bin .add .W64 (.reg .rcx) (.bin .mul .W64 (.reg .rax) (.lit 8))
/-- The placement entry, `b13`. -/
def pentS : SState := init [168, 24] [(.rsp, .ptr 0 24)] [] [] [(pentSym, 1, 0)]
/-- A column claim's call. -/
def cwS : SState :=
  init [168, 608, 24] [(.rsp, .ptr 0 24), (.r12, .ptr 1 16)] [] [] [(.load 0 72 8, 2, 0)]
/-- The out-of-domain claim's call. -/
def oodS : SState :=
  init [168, 56, 8] [(.rsp, .ptr 0 24)] [] [] [(.load 0 56 8, 1, 0), (.load 1 48 8, 2, 0)]
/-- The result. -/
def outS : SState := init [168, 24] [(.rsp, .ptr 0 24)] [] [] [(.load 0 32 8, 1, 0)]

/-! The branch conditions and the values the blocks compute. -/

/-- `testq %r15, %r15; je`: no scales. -/
def c1 : SBool := .cmp .eq .W64 (.bin .and .W64 (.reg .r15) (.reg .r15)) (.lit 0)
/-- `cmpl $1, 56(%rsp); jne`: a callee's `None`. -/
def cTag : SBool := .not (.cmp .eq .W32 (.load 0 80 4) (.lit 1))
/-- The claims' bytes, `0` past the cap. -/
def rbx7 : Sym :=
  .ite (.cmp .ult .W64 (.load 2 0 8) (.lit 161)) (.bin .mul .W64 (.load 2 0 8) (.lit 608)) (.lit 0)
/-- The first claim's address, R12 past the cap. -/
def r127 : Sym :=
  .ite (.cmp .ult .W64 (.load 2 0 8) (.lit 161)) (.bin .add .W64 (.lit 8) (.load 1 40 8))
    (.reg .r12)
/-- `testq %rbx, %rbx; je`: no claims. -/
def c7 : SBool := .cmp .eq .W64 (.bin .and .W64 rbx7 rbx7) (.lit 0)
/-- `addq $-608, %rbx; je`: the last claim. -/
def c10 : SBool := .cmp .eq .W64 (.bin .add .W64 (.lit 18446744073709551008) (.reg .rbx)) (.lit 0)
/-- `cmpq $158, %rax; jae`: no such column. -/
def c11 : SBool := .not (.cmp .ult .W64 (.load 1 0 8) (.lit 158))
/-- `cmpq $0, (%rcx,%rax,8); je`: no placement. -/
def c12 : SBool := .cmp .eq .W64 (.load 1 0 8) (.lit 0)
/-- `cmpq %rbp, %r13; je`: the scales run out. -/
def cScale : SBool := .cmp .eq .W64 (.reg .r13) (.reg .rbp)
/-- The Keccak point's address, `8` past its cap. -/
def rcx4 : Sym :=
  .ite (.not (.cmp .ult .W64 (.load 2 0 8) (.lit 37))) (.lit 8)
    (.bin .add .W64 (.lit 8) (.load 1 32 8))
/-- The Keccak point's count, `0` past its cap. -/
def r84 : Sym := .ite (.cmp .ult .W64 (.load 2 0 8) (.lit 37)) (.load 2 0 8) (.lit 0)
/-- A column claim's point's address, `8` past its cap. -/
def rcx16 : Sym := .ite (.cmp .ult .W64 (.load 1 8 8) (.lit 37)) (.ptr 1 16) (.lit 8)
/-- A column claim's point's count, `0` past its cap. -/
def r816 : Sym := .ite (.not (.cmp .ult .W64 (.load 1 8 8) (.lit 37))) (.lit 0) (.load 1 8 8)
/-- The out-of-domain point's address, `8` past its cap. -/
def rdi24 : Sym :=
  .ite (.cmp .ult .W64 (.load 2 0 8) (.lit 31)) (.bin .add .W64 (.lit 8) (.load 1 48 8)) (.lit 8)
/-- The out-of-domain point's count, `0` past its cap. -/
def rsi24 : Sym := .ite (.cmp .ult .W64 (.load 2 0 8) (.lit 31)) (.load 2 0 8) (.lit 0)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (bodyS 24)
sym_block run_b2 := exec b2 (scaleS .rbp)
sym_block run_b3 := exec b3 (bodyS 24)
sym_block run_b4 := exec b4 ringS
sym_block run_b5 := exec b5 (bodyS 8)
sym_block run_b6 := exec b6 (bodyS 24)
sym_block run_b7 := exec b7 claimsS
sym_block run_b8 := exec b8 (bodyS 24)
sym_block run_b10 := exec b10 (bodyS 24)
sym_block run_b11 := exec b11 colS
sym_block run_b12 := exec b12 placeS
sym_block run_b13 := exec b13 pentS
sym_block run_b14 := exec b14 (scaleS .r13)
sym_block run_b15 := exec b15 (bodyS 24)
sym_block run_b16 := exec b16 cwS
sym_block run_b17 := exec b17 (bodyS 8)
sym_block run_b18 := exec b18 (bodyS 24)
sym_block run_b19 := exec b19 (bodyS 24)
sym_block run_b21 := exec b21 (bodyS 24)
sym_block run_b22 := exec b22 (scaleS .r13)
sym_block run_b23 := exec b23 (bodyS 24)
sym_block run_b24 := exec b24 oodS
sym_block run_b25 := exec b25 (bodyS 24)
sym_block run_b26 := exec b26 outS
sym_block run_b27 := exec b27 (after b26 outS)

/-! ## The blocks' exits -/

public section

theorem exit_b0 : exec b0 entryS = some (after b0 entryS,
    .call NativeRustcVmX64.Vm.LayoutWPlacement.entryLabel) := by
  rw [after_eq run_b0]; exact run_b0
theorem exit_b1 : exec b1 (bodyS 24) = some (after b1 (bodyS 24), .cond c1 NativeRustcVmX64.Vm.BasisWEval.label_1) := by
  rw [after_eq run_b1]; exact run_b1
theorem exit_b2 : exec b2 (scaleS .rbp) = some (after b2 (scaleS .rbp), .jump NativeRustcVmX64.Vm.BasisWEval.label_3) := by
  rw [after_eq run_b2]; exact run_b2
theorem exit_b3 : exec b3 (bodyS 24) = some (after b3 (bodyS 24), .fall) := by
  rw [after_eq run_b3]; exact run_b3
theorem exit_b4 : exec b4 ringS = some (after b4 ringS,
    .call NativeRustcVmX64.Vm.RingClaimWeight.entryLabel) := by
  rw [after_eq run_b4]; exact run_b4
theorem exit_b5 : exec b5 (bodyS 8) = some (after b5 (bodyS 8), .cond cTag NativeRustcVmX64.Vm.BasisWEval.label_16) := by
  rw [after_eq run_b5]; exact run_b5
theorem exit_b6 : exec b6 (bodyS 24) = some (after b6 (bodyS 24),
    .call NativeRustcVmX64.Vm.EWMul.entryLabel) := by
  rw [after_eq run_b6]; exact run_b6
theorem exit_b7 : exec b7 claimsS = some (after b7 claimsS, .cond c7 NativeRustcVmX64.Vm.BasisWEval.label_10) := by
  rw [after_eq run_b7]; exact run_b7
theorem exit_b8 : exec b8 (bodyS 24) = some (after b8 (bodyS 24), .jump NativeRustcVmX64.Vm.BasisWEval.label_6) := by
  rw [after_eq run_b8]; exact run_b8
theorem exit_b10 : exec b10 (bodyS 24) =
    some (after b10 (bodyS 24), .cond c10 NativeRustcVmX64.Vm.BasisWEval.label_10) := by
  rw [after_eq run_b10]; exact run_b10
theorem exit_b11 : exec b11 colS = some (after b11 colS, .cond c11 NativeRustcVmX64.Vm.BasisWEval.label_15) := by
  rw [after_eq run_b11]; exact run_b11
theorem exit_b12 : exec b12 placeS = some (after b12 placeS, .cond c12 NativeRustcVmX64.Vm.BasisWEval.label_15) := by
  rw [after_eq run_b12]; exact run_b12
theorem exit_b13 : exec b13 pentS = some (after b13 pentS, .cond cScale NativeRustcVmX64.Vm.BasisWEval.label_9) := by
  rw [after_eq run_b13]; exact run_b13
theorem exit_b14 : exec b14 (scaleS .r13) =
    some (after b14 (scaleS .r13), .jump NativeRustcVmX64.Vm.BasisWEval.label_13) := by
  rw [after_eq run_b14]; exact run_b14
theorem exit_b15 : exec b15 (bodyS 24) = some (after b15 (bodyS 24), .fall) := by
  rw [after_eq run_b15]; exact run_b15
theorem exit_b16 : exec b16 cwS = some (after b16 cwS,
    .call NativeRustcVmX64.Vm.ColumnWeight.entryLabel) := by
  rw [after_eq run_b16]; exact run_b16
theorem exit_b17 : exec b17 (bodyS 8) =
    some (after b17 (bodyS 8), .cond cTag NativeRustcVmX64.Vm.BasisWEval.label_16) := by
  rw [after_eq run_b17]; exact run_b17
theorem exit_b18 : exec b18 (bodyS 24) = some (after b18 (bodyS 24),
    .call NativeRustcVmX64.Vm.EWMul.entryLabel) := by
  rw [after_eq run_b18]; exact run_b18
theorem exit_b19 : exec b19 (bodyS 24) = some (after b19 (bodyS 24), .jump NativeRustcVmX64.Vm.BasisWEval.label_15) := by
  rw [after_eq run_b19]; exact run_b19
theorem exit_b21 : exec b21 (bodyS 24) =
    some (after b21 (bodyS 24), .cond cScale NativeRustcVmX64.Vm.BasisWEval.label_11) := by
  rw [after_eq run_b21]; exact run_b21
theorem exit_b22 : exec b22 (scaleS .r13) =
    some (after b22 (scaleS .r13), .jump NativeRustcVmX64.Vm.BasisWEval.label_19) := by
  rw [after_eq run_b22]; exact run_b22
theorem exit_b23 : exec b23 (bodyS 24) = some (after b23 (bodyS 24), .fall) := by
  rw [after_eq run_b23]; exact run_b23
theorem exit_b24 : exec b24 oodS = some (after b24 oodS,
    .call NativeRustcVmX64.Vm.EqEval.entryLabel) := by
  rw [after_eq run_b24]; exact run_b24
theorem exit_b25 : exec b25 (bodyS 24) = some (after b25 (bodyS 24),
    .call NativeRustcVmX64.Vm.EWMul.entryLabel) := by
  rw [after_eq run_b25]; exact run_b25
theorem exit_b26 : exec b26 outS = some (after b26 outS, .fall) := by
  rw [after_eq run_b26]; exact run_b26
theorem exit_b27 : exec b27 (after b26 outS) =
    some (after b27 (after b26 outS), .ret (.load 0 160 8)) := by
  rw [after_eq run_b27]; exact run_b27

/-! ## What the blocks leave -/

theorem ok_b0 : ProOk 160 16 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0) ∧
    (after b0 entryS).reg .rbx = some (.ptr 1 0) ∧ (after b0 entryS).reg .rsi = some (.lit 4) ∧
    (after b0 entryS).reg .rdi = some (.load 1 16 8) ∧
    (after b0 entryS).reg .rbp = some (.load 1 0 8) ∧
    (after b0 entryS).reg .r15 = some (.load 1 8 8) ∧
    wrote (after b0 entryS) 0 72 (.load 1 16 8) = true ∧
    wrote (after b0 entryS) 0 32 (.reg .rdi) = true ∧
    wrote (after b0 entryS) 0 40 (.reg .rdx) = true ∧
    wrote (after b0 entryS) 0 48 (.reg .rcx) = true := by
  decide +kernel

theorem ok_b1 : MidOk 160 24 slots (after b1 (bodyS 24)) = true ∧ (after b1 (bodyS 24)).mem = [] ∧
    Keeps (after b1 (bodyS 24)) [.rax, .rdx, .rbx, .rbp, .r15] = true := by
  decide +kernel

theorem ok_b2 : MidOk 160 24 slots (after b2 (scaleS .rbp)) = true ∧
    (∀ w ∈ (after b2 (scaleS .rbp)).mem, w.r = 0) ∧
    wrote (after b2 (scaleS .rbp)) 0 24 (.load 1 8 8) = true ∧
    missWs [32, 40, 48, 72] (after b2 (scaleS .rbp)) = true ∧
    (after b2 (scaleS .rbp)).reg .r13 = some (.ptr 1 16) ∧
    (after b2 (scaleS .rbp)).reg .r14 = some (.load 1 0 8) ∧
    (after b2 (scaleS .rbp)).reg .rbp = some (.ptr 1 0) ∧
    Keeps (after b2 (scaleS .rbp)) [.rax, .rdx, .rbx, .r15] = true := by
  decide +kernel

theorem ok_b3 : MidOk 160 24 slots (after b3 (bodyS 24)) = true ∧
    (∀ w ∈ (after b3 (bodyS 24)).mem, w.r = 0) ∧
    wrote (after b3 (bodyS 24)) 0 24 (.lit 0) = true ∧
    missWs [32, 40, 48, 72] (after b3 (bodyS 24)) = true ∧
    (after b3 (bodyS 24)).reg .r13 = some (.reg .rbp) ∧
    (after b3 (bodyS 24)).reg .r14 = some (.lit 0) ∧
    Keeps (after b3 (bodyS 24)) [.rax, .rdx, .rbx, .rbp, .r15] = true := by
  decide +kernel

theorem ok_b4 : MidOk 160 0 slots (after b4 ringS) = true ∧
    (∀ w ∈ (after b4 ringS).mem, w.r = 0) ∧
    missWs [24, 32, 40, 48, 72] (after b4 ringS) = true ∧
    wrote (after b4 ringS) 0 8 (.load 0 40 8) = true ∧
    wrote (after b4 ringS) 0 16 (.load 0 48 8) = true ∧
    (after b4 ringS).reg .rcx = some rcx4 ∧ (after b4 ringS).reg .r8 = some r84 ∧
    (after b4 ringS).reg .rsi = some (.reg .rax) ∧ (after b4 ringS).reg .rdi = some (.ptr 0 80) ∧
    (after b4 ringS).reg .r9 = some (.bin .add .W64 (.lit 16) (.load 1 24 8)) ∧
    (after b4 ringS).reg .r12 = some (.lit 8) ∧ (after b4 ringS).reg .rbx = some (.ptr 1 0) ∧
    Keeps (after b4 ringS) [.rdx, .rbp, .r13, .r14, .r15] = true := by
  decide +kernel

theorem ok_b5 : MidOk 160 24 slots (after b5 (bodyS 8)) = true ∧ (after b5 (bodyS 8)).mem = [] ∧
    Keeps (after b5 (bodyS 8)) [.rbx, .rbp, .r12, .r13, .r14, .r15] = true := by
  decide +kernel

theorem ok_b6 : MidOk 160 16 slots (after b6 (bodyS 24)) = true ∧
    (∀ w ∈ (after b6 (bodyS 24)).mem, w.r = 0) ∧
    missWs [24, 32, 40, 48, 56, 64, 72, 104] (after b6 (bodyS 24)) = true ∧
    (after b6 (bodyS 24)).reg .rcx = some (.load 0 96 8) ∧
    (after b6 (bodyS 24)).reg .rdx = some (.load 0 88 8) ∧
    (after b6 (bodyS 24)).reg .rsi = some (.load 0 24 8) ∧
    (after b6 (bodyS 24)).reg .rdi = some (.reg .r14) ∧
    (after b6 (bodyS 24)).reg .rbp =
      some (.bin .add .W64 (.bin .shl .W64 (.reg .r15) (.lit 4)) (.reg .rbp)) ∧
    Keeps (after b6 (bodyS 24)) [.rbx, .r12, .r13, .r14] = true := by
  decide +kernel

theorem ok_b7 : MidOk 160 24 slots (after b7 claimsS) = true ∧
    (∀ w ∈ (after b7 claimsS).mem, w.r = 0) ∧
    wrote (after b7 claimsS) 0 64 (.reg .rdx) = true ∧
    wrote (after b7 claimsS) 0 56 (.ptr 1 0) = true ∧
    wrote (after b7 claimsS) 0 24 (.reg .rax) = true ∧
    missWs [32, 40, 48, 72] (after b7 claimsS) = true ∧
    (after b7 claimsS).reg .rbx = some rbx7 ∧ (after b7 claimsS).reg .r12 = some r127 ∧
    Keeps (after b7 claimsS) [.rbp, .r13] = true := by
  decide +kernel

theorem ok_b8 : MidOk 160 24 slots (after b8 (bodyS 24)) = true ∧
    (∀ w ∈ (after b8 (bodyS 24)).mem, w.r = 0) ∧
    wrote (after b8 (bodyS 24)) 0 104 (.bin .add .W64 (.load 0 72 8) (.lit 120)) = true ∧
    missWs [24, 32, 40, 48, 56, 64, 72] (after b8 (bodyS 24)) = true ∧
    (after b8 (bodyS 24)).reg .rcx = some (.bin .add .W64 (.load 0 72 8) (.lit 120)) ∧
    (after b8 (bodyS 24)).reg .r12 = some (.bin .add .W64 (.lit 16) (.reg .r12)) ∧
    Keeps (after b8 (bodyS 24)) [.rbx, .rbp, .r13] = true := by
  decide +kernel

theorem ok_b10 : MidOk 160 24 slots (after b10 (bodyS 24)) = true ∧
    (after b10 (bodyS 24)).mem = [] ∧
    (after b10 (bodyS 24)).reg .rbx =
      some (.bin .add .W64 (.lit 18446744073709551008) (.reg .rbx)) ∧
    (after b10 (bodyS 24)).reg .r12 = some (.bin .add .W64 (.lit 608) (.reg .r12)) ∧
    Keeps (after b10 (bodyS 24)) [.rcx, .rbp, .r13] = true := by
  decide +kernel

theorem ok_b11 : MidOk 160 24 slots (after b11 colS) = true ∧ (after b11 colS).mem = [] ∧
    (after b11 colS).reg .rax = some (.load 1 0 8) ∧ (after b11 colS).reg .r12 = some (.ptr 1 16) ∧
    Keeps (after b11 colS) [.rcx, .rbx, .rbp, .r13] = true := by
  decide +kernel

theorem ok_b12 : MidOk 160 24 slots (after b12 placeS) = true ∧ (after b12 placeS).mem = [] ∧
    (after b12 placeS).reg .rax = some col3 ∧
    Keeps (after b12 placeS) [.rcx, .rbx, .rbp, .r12, .r13] = true := by
  decide +kernel

theorem ok_b13 : MidOk 160 24 slots (after b13 pentS) = true ∧ (after b13 pentS).mem = [] ∧
    (after b13 pentS).reg .rsi = some (.load 1 8 8) ∧
    (after b13 pentS).reg .rdx = some (.load 1 16 8) ∧
    Keeps (after b13 pentS) [.rbx, .rbp, .r12, .r13] = true := by
  decide +kernel

theorem ok_b14 : MidOk 160 24 slots (after b14 (scaleS .r13)) = true ∧
    (after b14 (scaleS .r13)).mem = [] ∧
    (after b14 (scaleS .r13)).reg .r13 = some (.ptr 1 16) ∧
    (after b14 (scaleS .r13)).reg .r14 = some (.load 1 0 8) ∧
    (after b14 (scaleS .r13)).reg .r15 = some (.load 1 8 8) ∧
    Keeps (after b14 (scaleS .r13)) [.rsi, .rdx, .rbx, .rbp, .r12] = true := by
  decide +kernel

theorem ok_b15 : MidOk 160 24 slots (after b15 (bodyS 24)) = true ∧
    (after b15 (bodyS 24)).mem = [] ∧
    (after b15 (bodyS 24)).reg .r13 = some (.reg .rbp) ∧
    (after b15 (bodyS 24)).reg .r14 = some (.lit 0) ∧
    (after b15 (bodyS 24)).reg .r15 = some (.lit 0) ∧
    Keeps (after b15 (bodyS 24)) [.rsi, .rdx, .rbx, .rbp, .r12] = true := by
  decide +kernel

theorem ok_b16 : MidOk 160 0 slots (after b16 cwS) = true ∧ (∀ w ∈ (after b16 cwS).mem, w.r = 0) ∧
    missWs [24, 32, 40, 48, 56, 64, 72, 104] (after b16 cwS) = true ∧
    wrote (after b16 cwS) 0 8 (.load 0 40 8) = true ∧
    wrote (after b16 cwS) 0 16 (.load 0 48 8) = true ∧
    (after b16 cwS).reg .rcx = some rcx16 ∧ (after b16 cwS).reg .r8 = some r816 ∧
    (after b16 cwS).reg .rdi = some (.ptr 0 80) ∧ (after b16 cwS).reg .r9 = some (.load 2 16 8) ∧
    (after b16 cwS).reg .r12 = some (.ptr 1 16) ∧
    Keeps (after b16 cwS) [.rsi, .rdx, .rbx, .rbp, .r13, .r14, .r15] = true := by
  decide +kernel

theorem ok_b17 : MidOk 160 24 slots (after b17 (bodyS 8)) = true ∧ (after b17 (bodyS 8)).mem = [] ∧
    Keeps (after b17 (bodyS 8)) [.rbx, .rbp, .r12, .r13, .r14, .r15] = true := by
  decide +kernel

theorem ok_b18 : MidOk 160 16 slots (after b18 (bodyS 24)) = true ∧
    (∀ w ∈ (after b18 (bodyS 24)).mem, w.r = 0) ∧
    missWs [24, 32, 40, 48, 56, 64, 72, 104] (after b18 (bodyS 24)) = true ∧
    (after b18 (bodyS 24)).reg .rcx = some (.load 0 96 8) ∧
    (after b18 (bodyS 24)).reg .rdx = some (.load 0 88 8) ∧
    (after b18 (bodyS 24)).reg .rsi = some (.reg .r15) ∧
    (after b18 (bodyS 24)).reg .rdi = some (.reg .r14) ∧
    Keeps (after b18 (bodyS 24)) [.rbx, .rbp, .r12, .r13] = true := by
  decide +kernel

theorem ok_b19 : MidOk 160 24 slots (after b19 (bodyS 24)) = true ∧
    (∀ w ∈ (after b19 (bodyS 24)).mem, w.r = 0) ∧
    wrote (after b19 (bodyS 24)) 0 64 (.bin .xor .W64 (.load 0 64 8) (.reg .rdx)) = true ∧
    wrote (after b19 (bodyS 24)) 0 24 (.bin .xor .W64 (.load 0 24 8) (.reg .rax)) = true ∧
    missWs [32, 40, 48, 56, 72, 104] (after b19 (bodyS 24)) = true ∧
    (after b19 (bodyS 24)).reg .rcx = some (.load 0 104 8) ∧
    Keeps (after b19 (bodyS 24)) [.rbx, .rbp, .r12, .r13] = true := by
  decide +kernel

theorem ok_b21 : MidOk 160 24 slots (after b21 (bodyS 24)) = true ∧
    (after b21 (bodyS 24)).mem = [] ∧ Keeps (after b21 (bodyS 24)) [.rbp, .r13] = true := by
  decide +kernel

theorem ok_b22 : MidOk 160 24 slots (after b22 (scaleS .r13)) = true ∧
    (after b22 (scaleS .r13)).mem = [] ∧
    (after b22 (scaleS .r13)).reg .r14 = some (.load 1 0 8) ∧
    (after b22 (scaleS .r13)).reg .r15 = some (.load 1 8 8) := by
  decide +kernel

theorem ok_b23 : MidOk 160 24 slots (after b23 (bodyS 24)) = true ∧
    (after b23 (bodyS 24)).mem = [] ∧
    (after b23 (bodyS 24)).reg .r14 = some (.lit 0) ∧
    (after b23 (bodyS 24)).reg .r15 = some (.lit 0) := by
  decide +kernel

theorem ok_b24 : MidOk 160 16 slots (after b24 oodS) = true ∧
    (∀ w ∈ (after b24 oodS).mem, w.r = 0) ∧
    missWs [24, 32, 64] (after b24 oodS) = true ∧
    (after b24 oodS).reg .rdi = some rdi24 ∧ (after b24 oodS).reg .rsi = some rsi24 ∧
    (after b24 oodS).reg .rdx = some (.load 0 40 8) ∧
    (after b24 oodS).reg .rcx = some (.load 0 48 8) ∧
    Keeps (after b24 oodS) [.r14, .r15] = true := by
  decide +kernel

theorem ok_b25 : MidOk 160 16 slots (after b25 (bodyS 24)) = true ∧
    (∀ w ∈ (after b25 (bodyS 24)).mem, w.r = 0) ∧
    missWs [24, 32, 64] (after b25 (bodyS 24)) = true ∧
    (after b25 (bodyS 24)).reg .rcx = some (.reg .rdx) ∧
    (after b25 (bodyS 24)).reg .rdx = some (.reg .rax) ∧
    (after b25 (bodyS 24)).reg .rsi = some (.reg .r15) ∧
    (after b25 (bodyS 24)).reg .rdi = some (.reg .r14) := by
  decide +kernel

theorem ok_b27 : EpiOk 160 slots (after b27 (after b26 outS)) = true ∧
    (∀ w ∈ (after b27 (after b26 outS)).mem, w.r = 1 ∧ w.off + w.n ≤ 24) ∧
    wrote (after b27 (after b26 outS)) 1 0 (.lit 1) = true ∧
    wrote (after b27 (after b26 outS)) 1 8 (.bin .xor .W64 (.reg .rax) (.load 0 24 8)) = true ∧
    wrote (after b27 (after b26 outS)) 1 16 (.bin .xor .W64 (.reg .rdx) (.load 0 64 8)) = true := by
  decide +kernel

end

end NativeRustcVmX64.Whir.BasisWEval
