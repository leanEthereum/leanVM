module

public import NativeRustcVmX64.Arrays.Common
public import NativeRustcVmX64.Code.Vm.TableWeights
public meta import NativeRustcVmX64.Code.Vm.TableWeights
public meta import NativeRustcVmX64.Arrays.Common

/-!
# `table_weights`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the frame (`Field.frameS 256`, `Field.midS 256`): the 248 bytes of pushes and locals,
the call's return-address slot at offset `0`, the return address at `256`. A local at `o(%rsp)`
is at offset `o + 8`.
- `entryS` at the entry (`b0`); `htS` for `b1`, the heights at RSI (region 1);
- `ptS` at the loop head `NativeRustcVmX64.Vm.TableWeights.label_3` (`b10`) and at `NativeRustcVmX64.Vm.TableWeights.label_5` (`b3`): the point's
  element at `r8 + rbp` (region 1);
- `eqS` for `b11`: the equality point's element at `[104] + rbp` (region 1);
- `midS 256` for the other blocks of the loop (`b4` to `b9`) and for `b12`;
- `outS` for the stores into `out` (`b13a`, region 1 at `[96]`), `midS 256` for the epilogue
  (`b13b`).
-/

namespace NativeRustcVmX64.Tables.TableWeights

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TableWeights NativeRustcVmX64.Field
open NativeRustcVmX64.Arrays

@[expose] public section

/-- At the entry. -/
abbrev entryS : SState := frameS 256
/-- Between the prologue and the epilogue. -/
abbrev mS : SState := midS 256
/-- `b1`: the heights at RSI. -/
def htS : SState := init [264, 48] [(.rsp, .ptr 0 8)] [] [] [(.reg .rsi, 1, 0)]
/-- The point's element at `r8 + rbp`. -/
def ptS : SState := init [264, 16] [(.rsp, .ptr 0 8)] [] []
  [(.bin .add .W64 (.reg .r8) (.reg .rbp), 1, 0)]
/-- The equality point's element at the frame's word `104` plus `rbp`. -/
def eqS : SState := init [264, 16] [(.rsp, .ptr 0 8)] [] []
  [(.bin .add .W64 (.load 0 104 8) (.reg .rbp), 1, 0)]
/-- `out`'s 96 bytes at the frame's word `96`. -/
def outS : SState := init [264, 96] [(.rsp, .ptr 0 8)] [] [] [(.load 0 96 8, 1, 0)]

/-- `b13`'s stores into `out`. -/
def b13a : List Directive := b13.take 24
/-- The epilogue. -/
def b13b : List Directive := b13.drop 24

/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) :=
  [(248, .rbp), (240, .r15), (232, .r14), (224, .r13), (216, .r12), (208, .rbx)]

/-! ## What a block's result says -/

/-- The words of region `r` at `p.1` written as `p.2`. -/
def WrW (r : Nat) (S : SState) (l : List (Nat × Sym)) : Prop :=
  ∀ p ∈ l, ∀ t < 8, findWrite r (p.1 + t) S.mem = some (p.2, t)

instance (r : Nat) (S : SState) (l : List (Nat × Sym)) : Decidable (WrW r S l) := by
  unfold WrW; infer_instance

/-- No write over the frame's words at `os`. -/
def KeepW (S : SState) (os : List Nat) : Prop := ∀ o ∈ os, firstOverlap 0 o 8 S.mem = none

instance (S : SState) (os : List Nat) : Decidable (KeepW S os) := by
  unfold KeepW; infer_instance

/-- The registers' symbolic values. -/
def RegsAre (S : SState) (l : List (Reg64 × Sym)) : Prop := ∀ p ∈ l, S.reg p.1 = some p.2

instance (S : SState) (l : List (Reg64 × Sym)) : Decidable (RegsAre S l) := by
  unfold RegsAre; infer_instance

/-- Every write in region 0 below `L`. -/
def InFrame (S : SState) (L : Nat) : Prop := ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ L

instance (S : SState) (L : Nat) : Decidable (InFrame S L) := by
  unfold InFrame; infer_instance

/-- The callee-saved registers, each its atom. -/
def atoms : List (Reg64 × Sym) :=
  [(.rbx, .reg .rbx), (.rbp, .reg .rbp), (.r12, .reg .r12), (.r13, .reg .r13), (.r14, .reg .r14),
    (.r15, .reg .r15)]

/-- The frame's words the loop keeps: `out`, the equality point, its length, the six heights, the
point's end, the point. -/
def kfo : List Nat := [96, 104, 176, 152, 144, 136, 128, 120, 112, 168, 160]

/-- Weight `i`'s low limb's word (`i < 5`). -/
def wlo : Nat → Nat
  | 0 => 16 | 1 => 32 | 2 => 48 | 3 => 64 | _ => 88
/-- Weight `i`'s high limb's word (`i < 5`). -/
def whi : Nat → Nat
  | 0 => 24 | 1 => 40 | 2 => 56 | 3 => 72 | _ => 80
/-- Height `j`'s word. -/
def hoff (j : Nat) : Nat := 152 - 8 * j

/-- The words of the weights `0` to `4` but `i`. -/
def wOthers (i : Nat) : List Nat :=
  ((List.range 5).filter (· ≠ i)).flatMap fun j ↦ [wlo j, whi j]

/-- The words of the weights `0` to `4`. -/
def wAll : List Nat := (List.range 5).flatMap fun j ↦ [wlo j, whi j]

/-- `rbx < [h]`. -/
def ltH (h : Nat) : SBool := .cmp .ult .W64 (.reg .rbx) (.load 0 h 8)
/-- The factor's low limb a block passes. -/
def facLo (h : Nat) (p : Sym) : Sym := .bin .xor .W64 (.ite (ltH h) (.reg .r15) (.lit 0)) p
/-- The factor's high limb a block passes. -/
def facHi (h : Nat) : Sym := .ite (ltH h) (.reg .r13) (.reg .r14)

/-- What a multiplying block `b<3 + j>` (`1 ≤ j ≤ 4`) leaves: the previous product stored as weight
`j - 1`, weight `j` and its factor passed. -/
def MidOk (j : Nat) (S : SState) : Prop :=
  RegsAre S ([(.rdi, .load 0 (wlo j) 8), (.rsi, .load 0 (whi j) 8),
    (.rdx, facLo (hoff j) (.reg .r12)), (.rcx, facHi (hoff j)), (.rsp, .ptr 0 0)] ++ atoms) ∧
  InFrame S 208 ∧ WrW 0 S [(wlo (j - 1), .reg .rax), (whi (j - 1), .reg .rdx)] ∧
  KeepW S (kfo ++ [184, 200, 192] ++ wOthers (j - 1))

instance (j : Nat) (S : SState) : Decidable (MidOk j S) := by
  unfold MidOk; infer_instance

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 htS
sym_block run_b3 := exec b3 ptS
sym_block run_b4 := exec b4 mS
sym_block run_b5 := exec b5 mS
sym_block run_b6 := exec b6 mS
sym_block run_b7 := exec b7 mS
sym_block run_b8 := exec b8 mS
sym_block run_b9 := exec b9 mS
sym_block run_b10 := exec b10 ptS
sym_block run_b11 := exec b11 eqS
sym_block run_b12 := exec b12 mS
sym_block run_b13a := exec b13a outS
sym_block run_b13b := exec b13b mS

public theorem b0_ok : (∀ p ∈ slots, p.1 + 8 ≤ 256 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b0 entryS).mem = some (.reg p.2, i)) ∧
    (∀ r ∈ freeRegs slots, (after b0 entryS).reg r = some (.reg r)) ∧
    InFrame (after b0 entryS) 256 ∧ (after b0 entryS).reg .rsp = some (.ptr 0 8) ∧
    WrW 0 (after b0 entryS) [(96, .reg .rdi), (104, .reg .rdx), (176, .reg .rcx)] ∧
    RegsAre (after b0 entryS) [(.rsi, .reg .rsi), (.r8, .reg .r8), (.r9, .reg .r9)] := by
  decide +kernel

public theorem b1_ok : RegsAre (after b1 htS) [(.rax, .lit 1), (.rdx, .lit 0), (.rbx, .lit 0),
      (.rbp, .lit 0), (.r8, .reg .r8), (.rsp, .ptr 0 8)] ∧
    InFrame (after b1 htS) 208 ∧
    WrW 0 (after b1 htS) [(152, .load 1 0 8), (144, .load 1 8 8), (136, .load 1 16 8),
      (128, .load 1 24 8), (120, .load 1 32 8), (112, .load 1 40 8),
      (16, .lit 1), (24, .lit 0), (32, .lit 1), (40, .lit 0), (48, .lit 1), (56, .lit 0),
      (64, .lit 1), (72, .lit 0), (88, .lit 1), (80, .lit 0),
      (168, .bin .add .W64 (.reg .r8) (.bin .shl .W64 (.reg .r9) (.lit 4))), (160, .reg .r8)] ∧
    KeepW (after b1 htS) [96, 104, 176] ∧
    keepsRegs htS (after b1 htS) (.rsp :: freeRegs slots) = true := by
  decide +kernel

public theorem b3_ok : RegsAre (after b3 ptS) ([(.rdi, .load 0 16 8), (.rsi, .load 0 24 8),
      (.rdx, facLo 152 (.load 1 0 8)), (.rcx, facHi 152), (.rsp, .ptr 0 0)] ++
      [(.rbx, .reg .rbx), (.rbp, .reg .rbp), (.r12, .load 1 0 8), (.r13, .reg .r13),
        (.r14, .reg .r14), (.r15, .reg .r15)]) ∧
    InFrame (after b3 ptS) 208 ∧
    WrW 0 (after b3 ptS) [(184, .bin .add .W64 (.reg .r8) (.reg .rbp))] ∧
    KeepW (after b3 ptS) (kfo ++ [200, 192] ++ wAll) := by
  decide +kernel

public theorem b4_ok : MidOk 1 (after b4 mS) := by decide +kernel
public theorem b5_ok : MidOk 2 (after b5 mS) := by decide +kernel
public theorem b6_ok : MidOk 3 (after b6 mS) := by decide +kernel
public theorem b7_ok : MidOk 4 (after b7 mS) := by decide +kernel

public theorem b8_ok : RegsAre (after b8 mS) [(.rdi, .load 0 200 8), (.rsi, .load 0 192 8),
      (.rdx, .bin .xor .W64 (.ite (.not (ltH 112)) (.lit 0) (.reg .r15)) (.reg .r12)),
      (.rcx, facHi 112), (.rsp, .ptr 0 0), (.rbx, .reg .rbx), (.rbp, .reg .rbp)] ∧
    InFrame (after b8 mS) 208 ∧ WrW 0 (after b8 mS) [(88, .reg .rax), (80, .reg .rdx)] ∧
    KeepW (after b8 mS) (kfo ++ [184] ++ wOthers 4) := by
  decide +kernel

public theorem b9_ok : RegsAre (after b9 mS) [(.rax, .reg .rax), (.rdx, .reg .rdx),
      (.rbx, .bin .add .W64 (.reg .rbx) (.lit 1)), (.rbp, .bin .add .W64 (.lit 16) (.reg .rbp)),
      (.r8, .load 0 160 8), (.rsp, .ptr 0 8)] ∧ (after b9 mS).mem = [] ∧
    keepsAll mS (after b9 mS) (freeRegs slots) = true := by
  decide +kernel

public theorem b10_ok : RegsAre (after b10 ptS) [(.r14, .load 1 8 8), (.r13, .load 1 8 8),
      (.r15, .lit 1), (.rsp, .ptr 0 8), (.rbx, .reg .rbx), (.rbp, .reg .rbp), (.r8, .reg .r8)] ∧
    InFrame (after b10 ptS) 208 ∧ WrW 0 (after b10 ptS) [(200, .reg .rax), (192, .reg .rdx)] ∧
    KeepW (after b10 ptS) (kfo ++ wAll) ∧
    keepsRegs ptS (after b10 ptS) (.rsp :: freeRegs slots) = true := by
  decide +kernel

public theorem b11_ok : RegsAre (after b11 eqS) [(.r15, .bin .xor .W64 (.load 1 0 8) (.lit 1)),
      (.r13, .bin .xor .W64 (.load 1 8 8) (.reg .r14)), (.r14, .reg .r14), (.rsp, .ptr 0 8),
      (.rbx, .reg .rbx), (.rbp, .reg .rbp), (.r8, .reg .r8)] ∧ (after b11 eqS).mem = [] ∧
    keepsAll eqS (after b11 eqS) (freeRegs slots) = true := by
  decide +kernel

public theorem b12_ok : RegsAre (after b12 mS) [(.rax, .lit 1), (.rdx, .lit 0), (.rsp, .ptr 0 8)] ∧
    InFrame (after b12 mS) 208 ∧
    WrW 0 (after b12 mS) [(16, .lit 1), (24, .lit 0), (32, .lit 1), (40, .lit 0), (48, .lit 1),
      (56, .lit 0), (64, .lit 1), (72, .lit 0), (88, .lit 1), (80, .lit 0)] ∧
    KeepW (after b12 mS) [96] ∧ keepsRegs mS (after b12 mS) (.rsp :: freeRegs slots) = true := by
  decide +kernel

public theorem b13a_ok : RegsAre (after b13a outS) [(.rsp, .ptr 0 8)] ∧
    (∀ w ∈ (after b13a outS).mem, w.r = 1 ∧ w.off + w.n ≤ 96) ∧
    WrW 1 (after b13a outS) [(0, .load 0 16 8), (8, .load 0 24 8), (16, .load 0 32 8),
      (24, .load 0 40 8), (32, .load 0 48 8), (40, .load 0 56 8), (48, .load 0 64 8),
      (56, .load 0 72 8), (64, .load 0 88 8), (72, .load 0 80 8), (80, .reg .rax),
      (88, .reg .rdx)] ∧ keepsRegs outS (after b13a outS) (.rsp :: freeRegs slots) = true := by
  decide +kernel

public theorem b13b_ok : restores slots 256 (after b13b mS) = true ∧ (after b13b mS).mem = [] := by
  decide +kernel

public theorem slots_ok : ∀ p ∈ slots, 208 ≤ p.1 ∧ p.1 + 8 ≤ 256 := by decide

public theorem freeRegs_slots : freeRegs slots = [] := by decide

end NativeRustcVmX64.Tables.TableWeights
