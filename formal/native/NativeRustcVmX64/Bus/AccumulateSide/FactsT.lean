module

public import NativeRustcVmX64.Bus.AccumulateSide.FactsZ
public import NativeRustcVmX64.Code.Vm.AccumulateSide.Names
public import NativeRustcVmX64.Code.Vm.BlockForm.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqEvalFnOfEqAbove.Names
public import NativeRustcVmX64.Code.Vm.Evaluate.Names
public import NativeRustcVmX64.Code.Vm.FormBufAddScaled.Names
public import NativeRustcVmX64.Code.Vm.Names
public import NativeRustcVmX64.Code.Vm.PaddingWeight.Names
public meta import NativeRustcVmX64.Bus.AccumulateSide.Exec

/-!
# `accumulate_side`: the table loop's blocks (x86-64)

What the executor's summaries say of `b17` to `b32`, checked by the kernel. The loop's values
are `Vt`'s indices from `32` (`lpT`): `32` the offset, `33`, `34` the padding rows, `35`, `36` the
ones, `37`, `38` the selector, `39` the owner, `40` the tuple, `41` the block's form's size, `42`
the frame's terms' address, `43`, `44` the padding span, `45`, `46` the next ones, `47` the
padding's address, `48`, `49` the padding weight, `50`, `51` the selector times it, `52`, `53`
the form's value, `54`, `55` the padding row, `56`, `57` the next padding rows.
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.AccumulateSide NativeRustcVmX64.Transcript

@[expose] public section

/-- A block's writes: frame bytes below `6056`. -/
def lowW' (S : SState) : Prop := S.mem.all (fun w ↦ w.r == 0 && decide (w.off + w.n ≤ 6056)) = true

instance (S : SState) : Decidable (lowW' S) := by unfold lowW'; infer_instance

/-- The frame words the turn keeps throughout, with the padding rows. -/
def FTp : List (Sym × Nat) := FT ++ [(Lw 56, 33), (Lw 128, 34)]
/-- After `b17`'s call. -/
def D17 : List (Sym × Nat) := [(Rg .r12, 32), (Rg .r14, 35), (Rg .r15, 36)] ++ FTp
/-- After `b18a`. -/
def D18 : List (Sym × Nat) := D17 ++ [(Rg .r13, 37), (Rg .rbp, 38), (Rg .rdi, 40)]
/-- After `block_form`'s call. -/
def D18c : List (Sym × Nat) := D17 ++ [(Rg .r13, 37), (Rg .rbp, 38)]
/-- After `b20`. -/
def D20 : List (Sym × Nat) := D18c ++ [(Rg .rsi, 39)]
/-- After `b21`'s call. -/
def D21c : List (Sym × Nat) :=
  [(Rg .r14, 35), (Rg .r15, 36), (Rg .rbx, 37)] ++ FTp ++
    [(Lw 120, 32), (Lw 48, 39), (Lw 16, 38)]
/-- … and what `b21` computes. -/
def E21 : List (Sym × Nat) := [(Rg .r13, 41), (Rg .rbp, 42), (Rg .r12, 43), (Lw 24, 44)]
/-- After `b23a`, the values kept. -/
def D23 : List (Sym × Nat) :=
  [(Rg .r13, 41), (Rg .rbp, 42)] ++ FTp ++ [(Lw 120, 32), (Lw 16, 38), (Lw 112, 37)]
/-- … and what it computes. -/
def E23 : List (Sym × Nat) := [(Rg .r14, 45), (Rg .r15, 46), (Rg .r12, 47), (Lw 24, 44)]
/-- After `b23b`'s call (`padding_weight`). -/
def D23c : List (Sym × Nat) := D23 ++ [(Rg .r14, 45), (Rg .r15, 46), (Rg .r12, 47), (Lw 24, 44),
  (Rg .rbx, 14)]
/-- After `b24`'s call (`EW::mul`). -/
def D24c : List (Sym × Nat) := D23c
/-- After `b25`'s call (`evaluate`). -/
def D25c : List (Sym × Nat) :=
  [(Rg .r14, 45), (Rg .r15, 46), (Rg .rbp, 14)] ++ FTp ++ [(Lw 120, 32), (Lw 16, 50), (Lw 48, 51)]
/-- After `b26`'s call (`EW::mul`). -/
def D26c : List (Sym × Nat) := [(Rg .r14, 45), (Rg .r15, 46), (Rg .rbp, 14)] ++ FTp ++
  [(Lw 120, 32)]
/-- After `b27`. -/
def D27 : List (Sym × Nat) :=
  [(Rg .rdi, 13), (Rg .rbp, 14), (Rg .r8, 27), (Rg .r9, 26), (Rg .r14, 45), (Rg .r15, 46)] ++ FT

/-- `eq_above`'s arguments in `b17`. -/
def satT : Sym := .ite (.cmp .ult .W64 (.reg .rbp) (.load 2 72 8)) (.reg .r8)
  (.bin .sub .W64 (.reg .rbp) (.load 2 72 8))
def shrT : Sym := .ite (.not (.cmp .ult .W64 (.load 2 72 8) (.lit 64))) (.reg .r8)
  (.bin .shr .W64 (.load 2 80 8) (.load 2 72 8))
def aboveT : Sym := .ite (.cmp .ult .W64 (.reg .rbp) (.load 2 72 8)) (.reg .r9)
  (.bin .add .W64 (.reg .rdi) (.bin .shl .W64 (.load 2 72 8) (.lit 4)))

/-- `b19`'s, `b22`'s exit: AL `0`. -/
def cAl : SBool := .cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)
/-- `b20`'s exit: the owner past `5`. -/
def c20 : SBool := .and (.not (.cmp .ult .W64 (.load 1 0 8) (.lit 5)))
  (.not (.cmp .eq .W64 (.load 1 0 8) (.lit 5)))

/-- The owner times five, in `b21`. -/
def five8 : Sym := .bin .mul .W64 five (.lit 8)
/-- `b21`'s values. -/
def r13T : Sym := .ite (.not (.cmp .ult .W64 (.load 0 6056 8) (.lit 149))) (.lit 0) (.load 0 6056 8)
def rbpT : Sym := .ite (.cmp .ult .W64 (.load 0 6056 8) (.lit 149)) (.ptr 0 6064) (.lit 8)
def slotT : Sym := .bin .add .W64 (.load 0 88 8) (.bin .mul .W64 (.reg .rsi) (.lit 17784))

/-- `b23a`'s values. -/
def sumP : Sym := .bin .add .W64 (.load 0 24 8) (.reg .r12)
def okP : SBool := .cmp .eq .W8
  (.bin .and .W8 (.bin .merge .W8 (.reg .rcx)
      (.ite (.not (.cmp .ult .W64 sumP (.reg .r12))) (.lit 1) (.lit 0)))
    (.bin .merge .W8 sumP (.ite (.cmp .ult .W64 sumP (.lit 154)) (.lit 1) (.lit 0)))) (.lit 0)
def r12P : Sym := .ite okP (.lit 8)
  (.bin .add .W64 (.label NativeRustcVmX64.Vm.Symbols.rodata5Label)
    (.bin .shl .W64 (.reg .r12) (.lit 4)))
def lenP : Sym := .ite okP (.lit 0) (.load 0 24 8)

/-- `b27`'s exit: more table blocks. -/
def c27 : SBool := .not (.cmp .eq .W64 (.load 0 40 8) (.bin .add .W64 (.lit 16) (.load 0 120 8)))

end

public theorem low_T : lowW' (after b17 pS) ∧ lowW' (after b18a bS) ∧ lowW' (after b18b aS) ∧
    lowW' (after b19 fS) ∧ lowW' (after b20 bS) ∧ lowW' (after b21 tS) ∧ lowW' (after b22 fS) ∧
    lowW' (after b23a hS) ∧ lowW' (after b23b aS) ∧ lowW' (after b24 fS) ∧
    lowW' (after b25 fS) ∧ lowW' (after b26 fS) := by
  rw [after_eq run_b17, after_eq run_b18a, after_eq run_b18b, after_eq run_b19, after_eq run_b20,
    after_eq run_b21, after_eq run_b22, after_eq run_b23a, after_eq run_b23b, after_eq run_b24,
    after_eq run_b25, after_eq run_b26]
  decide +kernel

public theorem exit_b17 : exec b17 pS = some (after b17 pS,
    .call NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.entryLabel) :=
  run_b17.trans (by rw [after_eq run_b17])
public theorem ok_b17 : MidOk F 0 slots (after b17 pS) = true ∧
    (after b17 pS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040, 88, 88] (after b17 pS) (DT ++ DA) D17 = true ∧
    (after b17 pS).reg .rdi = some satT ∧ (after b17 pS).reg .rcx = some satT ∧
    (after b17 pS).reg .rsi = some shrT ∧ (after b17 pS).reg .rdx = some aboveT := by
  rw [after_eq run_b17]; decide +kernel

public theorem exit_b18a : exec b18a bS = some (after b18a bS, .fall) :=
  run_b18a.trans (by rw [after_eq run_b18a])
public theorem ok_b18a : MidOk F 8 slots (after b18a bS) = true ∧
    (after b18a bS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040, 16] (after b18a bS) (D17 ++ [(Rg .rax, 37), (Rg .rdx, 38)])
      (D18c ++ [(Rg .rax, 3)]) = true ∧
    (after b18a bS).reg .rdi = some (.load 1 8 8) := by
  rw [after_eq run_b18a]; decide +kernel

public theorem exit_b18b : exec b18b aS = some (after b18b aS,
    .call NativeRustcVmX64.Vm.BlockForm.entryLabel) :=
  run_b18b.trans (by rw [after_eq run_b18b])
public theorem ok_b18b : MidOk F 0 slots (after b18b aS) = true ∧
    (after b18b aS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040, 88] (after b18b aS) (D18 ++ DA)
      (D18c ++ [(Rg .rdi, 40), (Rg .rsi, 9), (Rg .rdx, 10), (Rg .rcx, 11), (Rg .r8, 12)]) = true ∧
    (after b18b aS).reg .r9 = some (.ptr 0 6056) := by
  rw [after_eq run_b18b]; decide +kernel

public theorem exit_b19 : exec b19 fS = some (after b19 fS, .cond cAl NativeRustcVmX64.Vm.AccumulateSide.label_13) :=
  run_b19.trans (by rw [after_eq run_b19]; rfl)
public theorem exit_b22 : exec b22 fS = some (after b22 fS, .cond cAl NativeRustcVmX64.Vm.AccumulateSide.label_13) :=
  run_b22.trans (by rw [after_eq run_b22]; rfl)
public theorem ok_b19 : MidOk F 8 slots (after b19 fS) = true ∧
    (after b19 fS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040] (after b19 fS) D18c D18c = true ∧
    MidOk F 8 slots (after b22 fS) = true ∧
    (after b22 fS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040] (after b22 fS) (D21c ++ E21) (D21c ++ E21) = true := by
  rw [after_eq run_b19, after_eq run_b22]; decide +kernel

public theorem exit_b20 : exec b20 bS = some (after b20 bS, .cond c20 NativeRustcVmX64.Vm.AccumulateSide.label_17) :=
  run_b20.trans (by rw [after_eq run_b20]; rfl)
public theorem ok_b20 : MidOk F 8 slots (after b20 bS) = true ∧
    (after b20 bS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040, 16] (after b20 bS) D18c D18c = true ∧
    (after b20 bS).reg .rsi = some (.load 1 0 8) := by
  rw [after_eq run_b20]; decide +kernel

public theorem exit_b21 : exec b21 tS = some (after b21 tS,
    .call NativeRustcVmX64.Vm.FormBufAddScaled.entryLabel) :=
  run_b21.trans (by rw [after_eq run_b21])
public theorem ok_b21 : MidOk F 0 slots (after b21 tS) = true ∧
    (after b21 tS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040, 240] (after b21 tS) D20 (D21c ++ [(Rg .rcx, 37), (Rg .r8, 38)]) = true ∧
    (after b21 tS).reg .r13 = some r13T ∧ (after b21 tS).reg .rbp = some rbpT ∧
    (after b21 tS).reg .rsi = some rbpT ∧ (after b21 tS).reg .rdx = some r13T ∧
    (after b21 tS).reg .rdi = some slotT ∧
    (after b21 tS).reg .r12 = some (.loadx 1 24 five8 8) ∧
    content [12040, 240] (after b21 tS) (Lw 24) = some (.loadx 1 32 five8 8) := by
  rw [after_eq run_b21]; decide +kernel

public theorem exit_b23a : exec b23a hS = some (after b23a hS, .fall) :=
  run_b23a.trans (by rw [after_eq run_b23a])
public theorem ok_b23a : MidOk F 8 slots (after b23a hS) = true ∧
    (after b23a hS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040, 120] (after b23a hS) (D21c ++ E21) D23 = true ∧
    (after b23a hS).reg .r14 = some (.bin .xor .W64 (.reg .r14) (.reg .rbx)) ∧
    (after b23a hS).reg .r15 = some (.bin .xor .W64 (.reg .r15) (.load 0 16 8)) ∧
    (after b23a hS).reg .r12 = some r12P ∧
    content [12040, 120] (after b23a hS) (Lw 24) = some lenP ∧
    (after b23a hS).reg .rsi = some (.loadx 1 24 (.bin .mul .W64 (.load 0 48 8) (.lit 8)) 8) ∧
    (after b23a hS).reg .rdx = some (.loadx 1 72 (.bin .mul .W64 (.load 0 48 8) (.lit 8)) 8) := by
  rw [after_eq run_b23a]; decide +kernel

public theorem exit_b23b : exec b23b aS = some (after b23b aS,
    .call NativeRustcVmX64.Vm.PaddingWeight.entryLabel) :=
  run_b23b.trans (by rw [after_eq run_b23b])
public theorem ok_b23b : MidOk F 0 slots (after b23b aS) = true ∧
    (after b23b aS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040, 88] (after b23b aS) (D23 ++ E23 ++ DA) D23c = true ∧
    (after b23b aS).reg .rdi = some (.load 1 56 8) ∧
    (after b23b aS).reg .rsi = some (.ite (.not (.cmp .ult .W64 (.reg .rsi) (.load 1 64 8)))
      (.load 1 64 8) (.reg .rsi)) ∧
    (after b23b aS).reg .rdx = some (.reg .rdx) := by
  rw [after_eq run_b23b]; decide +kernel

public theorem exit_b24 : exec b24 fS = some (after b24 fS,
    .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  run_b24.trans (by rw [after_eq run_b24])
public theorem ok_b24 : MidOk F 0 slots (after b24 fS) = true ∧
    (after b24 fS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040] (after b24 fS) (D23c ++ [(Rg .rax, 48), (Rg .rdx, 49)])
      (D23c ++ [(Rg .rdi, 37), (Rg .rsi, 38), (Rg .rdx, 48), (Rg .rcx, 49)]) = true := by
  rw [after_eq run_b24]; decide +kernel

public theorem exit_b25 : exec b25 fS = some (after b25 fS,
    .call NativeRustcVmX64.Vm.Evaluate.entryLabel) :=
  run_b25.trans (by rw [after_eq run_b25])
public theorem ok_b25 : MidOk F 0 slots (after b25 fS) = true ∧
    (after b25 fS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040] (after b25 fS) (D23c ++ [(Rg .rax, 50), (Rg .rdx, 51)])
      (D25c ++ [(Rg .rdi, 42), (Rg .rsi, 41), (Rg .rdx, 47), (Rg .rcx, 44)]) = true := by
  rw [after_eq run_b25]; decide +kernel

public theorem exit_b26 : exec b26 fS = some (after b26 fS,
    .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  run_b26.trans (by rw [after_eq run_b26])
public theorem ok_b26 : MidOk F 0 slots (after b26 fS) = true ∧
    (after b26 fS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040] (after b26 fS) (D25c ++ [(Rg .rdx, 53)])
      (D26c ++ [(Rg .rdi, 50), (Rg .rsi, 51), (Rg .rcx, 53)]) = true ∧
    (after b26 fS).reg .rdx = some (.bin .xor .W64 (.reg .rax) (.lit 1)) := by
  rw [after_eq run_b26]; decide +kernel

public theorem exit_b27 : exec b27 aS = some (after b27 aS, .cond c27 NativeRustcVmX64.Vm.AccumulateSide.label_15) :=
  run_b27.trans (by rw [after_eq run_b27]; rfl)
public theorem ok_b27 : MidOk F 8 slots (after b27 aS) = true ∧
    (after b27 aS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040, 88] (after b27 aS) (D26c ++ DA ++ Dl) D27 = true ∧
    (after b27 aS).reg .rsi = some (.bin .xor .W64 (.load 0 56 8) (.reg .rax)) ∧
    (after b27 aS).reg .rdx = some (.bin .xor .W64 (.load 0 128 8) (.reg .rdx)) ∧
    (after b27 aS).reg .r12 = some (.bin .add .W64 (.lit 16) (.load 0 120 8)) := by
  rw [after_eq run_b27]; decide +kernel

public theorem exit_b28 : exec b28 fS = some (after b28 fS, .jump NativeRustcVmX64.Vm.AccumulateSide.label_12) :=
  run_b28.trans (by rw [after_eq run_b28])
public theorem exit_b29 : exec b29 fS = some (after b29 fS, .fall) :=
  run_b29.trans (by rw [after_eq run_b29])
public theorem exit_b30 : exec b30 outS = some (after b30 outS, .fall) :=
  run_b30.trans (by rw [after_eq run_b30])
public theorem exit_b31 : exec b31 outS = some (after b31 outS, .ret (.load 0 12032 8)) :=
  run_b31.trans (by rw [after_eq run_b31])
public theorem ok_b28 : MidOk F 8 slots (after b28 fS) = true ∧ (after b28 fS).mem = [] ∧
    trackOk [12040] (after b28 fS) D27 D27 = true := by
  rw [after_eq run_b28]; decide +kernel
public theorem ok_b30 : MidOk F 8 slots (after b30 outS) = true ∧
    (after b30 outS).mem.all (fun w ↦ (w.r == 0 && decide (w.off = 32 ∧ w.n = 8)) ||
      (w.r == 1 && decide (w.off + w.n ≤ 24))) = true ∧
    trackOk [12040, 24] (after b30 outS) D27 D27 = true ∧
    content [12040, 24] (after b30 outS) (Lw 32) = some (.lit 1) ∧
    (∀ i < 8, findWrite 1 (8 + i) (after b30 outS).mem =
      some (.bin .xor .W64 (.bin .xor .W64 (.load 0 64 8) (.reg .r14)) (.reg .rsi), i)) ∧
    (∀ i < 8, findWrite 1 (16 + i) (after b30 outS).mem =
      some (.bin .xor .W64 (.bin .xor .W64 (.load 0 72 8) (.reg .r15)) (.reg .rdx), i)) := by
  rw [after_eq run_b30]; decide +kernel
public theorem ok_b31 : EpiOk F slots (after b31 outS) = true ∧
    (∀ i < 8, findWrite 1 i (after b31 outS).mem = some (.load 0 32 8, i)) ∧
    (after b31 outS).mem.all (fun w ↦ w.r == 1 && decide (w.off + w.n ≤ 8)) = true := by
  rw [after_eq run_b31]; decide +kernel

end NativeRustcVmX64.Bus.AccumulateSide
