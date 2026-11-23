module

public import NativeRustcVmX64.Tables.Common
public import NativeRustcVmX64.Code.Vm.TableColumnClaims
public meta import NativeRustcVmX64.Code.Vm.TableColumnClaims
public meta import NativeRustcVmX64.Tables.Common

/-!
# `table_column_claims`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the frame (`Field.frameS 64`, RSP at offset `8` in the body): the seven pushes at
`8` to `56` (the evaluations' address stored over RAX's at `8`), the call's return-address slot at
`0`, the return address at `64`. rustc unrolled the loop over the six tables; each table's loop
keeps its registers in `R04` (tables `0` to `4`) or `R5` (table `5`): the next value's address
`a`, `16 ×` the values left `n`, the point's address `p` and length `l`, the last column `c`.
- the prologue `b0a` (`entryS`), table `0`'s setup `b0b` (`evS`, the evaluations region 1 at
  RDI); the other tables' setups `b5`, `b10`, `b15`, `b20`, `b26` (`setS`, region 1 at the frame's
  word `8`);
- each loop's test (`b1`, `b6`, `b11`, `b16`, `b21`, `b27`), push block (`b2` … `b22`, `b28`;
  `pushS`, the value region 1 at `a`), after-call block (`b3` … `b23`, `b29`), from `regsS`;
- the exits: the failure jumps (`b4` … `b19`, `b30`), `b24` (AL zero), `b31` (AL one), the
  epilogue `b25` (`midS 64`).
-/

namespace NativeRustcVmX64.Tables.ColumnClaims

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TableColumnClaims NativeRustcVmX64.Field
open NativeRustcVmX64.Arrays

@[expose] public section

/-- A table loop's registers. -/
structure Regs where
  a : Reg64
  n : Reg64
  p : Reg64
  l : Reg64
  c : Reg64

/-- Tables `0` to `4`. -/
def R04 : Regs := ⟨.rcx, .rbp, .r12, .r15, .r13⟩
/-- Table `5`. -/
def R5 : Regs := ⟨.rdx, .r13, .rbp, .r15, .r12⟩

/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) :=
  [(56, .rbp), (48, .r15), (40, .r14), (32, .r13), (24, .r12), (16, .rbx)]

/-- The evaluations' bytes. -/
abbrev evB : Nat := 11808

/-- At the entry. -/
abbrev entryS : SState := frameS 64
/-- Table `0`'s setup: the evaluations at RDI. -/
def evS : SState := init [72, evB] [(.rsp, .ptr 0 8)] [] [] [(.reg .rdi, 1, 0)]
/-- A later table's setup: the evaluations at the frame's word `8`. -/
def setS : SState := init [72, evB] [(.rsp, .ptr 0 8)] [] [] [(.load 0 8 8, 1, 0)]
/-- Registers only. -/
abbrev regsS : SState := init []
/-- A push block: the value at `a`. -/
abbrev pushS (R : Regs) : SState := elemS 64 (.reg R.a) 0

/-- The prologue's pushes. -/
def b0a : List Directive := b0.take 9
/-- Table `0`'s setup. -/
def b0b : List Directive := b0.drop 9

/-! ## What a block's result says -/

/-- The registers' symbolic values. -/
def RegsAre (S : SState) (l : List (Reg64 × Sym)) : Prop := ∀ p ∈ l, S.reg p.1 = some p.2

instance (S : SState) (l : List (Reg64 × Sym)) : Decidable (RegsAre S l) := by
  unfold RegsAre; infer_instance

/-- Every write in region 0 below `L`. -/
def InFrame (S : SState) (L : Nat) : Prop := ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ L

instance (S : SState) (L : Nat) : Decidable (InFrame S L) := by
  unfold InFrame; infer_instance

/-- Every register its atom but those of `rs`. -/
def KeptBut (S : SState) (rs : List Reg64) : Prop :=
  (allRegs.all fun r ↦ rs.any (· == r) || S.reg r == some (.reg r)) = true

instance (S : SState) (rs : List Reg64) : Decidable (KeptBut S rs) := by
  unfold KeptBut; infer_instance

/-- `x + o`, or `o + x` (rustc's operand order varies). -/
def addE (x : Sym) (o : Nat) (sw : Bool) : Sym :=
  if sw then .bin .add .W64 (.lit o) x else .bin .add .W64 x (.lit o)

/-- `count < bound` for the word at `o` of region 1. -/
def ltW (o b : Nat) : SBool := .cmp .ult .W64 (.load 1 o 8) (.lit b)

/-- **The loop registers a table's setup sets**: table `t`'s entry at `1968 t` of the evaluations
(`x` their address), the column before its first `c`. -/
def Shapes (R : Regs) (t c : Nat) (x : Sym) (sw : Bool) (S : SState) : Prop :=
  RegsAre S [(R.a, .ite (.not (ltW (1968 * t + 488) 93)) (.lit 8) (addE x (1968 * t + 496) false)),
    (R.n, .bin .shl .W64 (.ite (.not (ltW (1968 * t + 488) 93)) (.lit 0) (.load 1 (1968 * t + 488) 8))
      (.lit 4)),
    (R.p, .ite (.not (ltW (1968 * t) 31)) (.lit 8) (addE x (1968 * t + 8) sw)),
    (R.l, .ite (ltW (1968 * t) 31) (.load 1 (1968 * t) 8) (.lit 0)),
    (R.c, .lit c), (.rsp, .ptr 0 8)]

instance (R : Regs) (t c : Nat) (x : Sym) (sw : Bool) (S : SState) :
    Decidable (Shapes R t c x sw S) := by
  unfold Shapes; infer_instance

/-- What a push block leaves. -/
def PushOk (R : Regs) (S : SState) : Prop :=
  RegsAre S [(.rdi, .reg .rbx), (.rsi, .bin .add .W64 (.reg R.c) (.lit 1)), (.rdx, .reg R.p),
    (.rcx, .reg R.l), (.r8, .load 1 0 8), (.r9, .load 1 8 8),
    (R.c, .bin .add .W64 (.reg R.c) (.lit 1)),
    (R.n, .bin .add .W64 (.lit 18446744073709551600) (.reg R.n)),
    (.r14, .bin .add .W64 (.reg R.a) (.lit 16)), (.rsp, .ptr 0 0), (.rbx, .reg .rbx),
    (R.p, .reg R.p), (R.l, .reg R.l)] ∧ InFrame S 8

instance (R : Regs) (S : SState) : Decidable (PushOk R S) := by
  unfold PushOk; infer_instance

/-- A loop's test of `n`. -/
def testN (R : Regs) : SBool := .cmp .eq .W64 (.bin .and .W64 (.reg R.n) (.reg R.n)) (.lit 0)

/-- `testb %al, %al`'s `jne`. -/
def alNZ (x : Sym) : SBool := .not (.cmp .eq .W8 (.bin .and .W8 x x) (.lit 0))

end

set_option Elab.async false

sym_block run_b0a := exec b0a entryS
sym_block run_b0b := exec b0b evS
sym_block run_b1 := exec b1 regsS
sym_block run_b2 := exec b2 (pushS R04)
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 regsS
sym_block run_b5 := exec b5 setS
sym_block run_b6 := exec b6 regsS
sym_block run_b7 := exec b7 (pushS R04)
sym_block run_b8 := exec b8 regsS
sym_block run_b9 := exec b9 regsS
sym_block run_b10 := exec b10 setS
sym_block run_b11 := exec b11 regsS
sym_block run_b12 := exec b12 (pushS R04)
sym_block run_b13 := exec b13 regsS
sym_block run_b14 := exec b14 regsS
sym_block run_b15 := exec b15 setS
sym_block run_b16 := exec b16 regsS
sym_block run_b17 := exec b17 (pushS R04)
sym_block run_b18 := exec b18 regsS
sym_block run_b19 := exec b19 regsS
sym_block run_b20 := exec b20 setS
sym_block run_b21 := exec b21 regsS
sym_block run_b22 := exec b22 (pushS R04)
sym_block run_b23 := exec b23 regsS
sym_block run_b24 := exec b24 regsS
sym_block run_b25 := exec b25 (midS 64)
sym_block run_b26 := exec b26 setS
sym_block run_b27 := exec b27 regsS
sym_block run_b28 := exec b28 (pushS R5)
sym_block run_b29 := exec b29 regsS
sym_block run_b30 := exec b30 regsS
sym_block run_b31 := exec b31 regsS

public theorem ok_b0a : (∀ p ∈ slots, p.1 + 8 ≤ 64 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b0a entryS).mem = some (.reg p.2, i)) ∧
    InFrame (after b0a entryS) 64 ∧ (after b0a entryS).reg .rsp = some (.ptr 0 8) ∧
    RegsAre (after b0a entryS) [(.rbx, .reg .rsi), (.rdi, .reg .rdi)] := by
  decide +kernel

public theorem ok_b0b : Shapes R04 0 4 (.reg .rdi) false (after b0b evS) ∧ InFrame (after b0b evS) 16 ∧
    (∀ t < 8, findWrite 0 (8 + t) (after b0b evS).mem = some (.reg .rdi, t)) ∧
    RegsAre (after b0b evS) [(.rbx, .reg .rbx)] := by
  decide +kernel

public theorem ok_set : Shapes R04 1 17 (.load 0 8 8) false (after b5 setS) ∧
    Shapes R04 2 30 (.load 0 8 8) false (after b10 setS) ∧
    Shapes R04 3 37 (.load 0 8 8) false (after b15 setS) ∧
    Shapes R04 4 51 (.load 0 8 8) false (after b20 setS) ∧
    Shapes R5 5 65 (.load 0 8 8) true (after b26 setS) ∧
    (after b5 setS).mem = [] ∧ (after b10 setS).mem = [] ∧ (after b15 setS).mem = [] ∧
    (after b20 setS).mem = [] ∧ (after b26 setS).mem = [] ∧
    RegsAre (after b5 setS) [(.rbx, .reg .rbx)] ∧ RegsAre (after b10 setS) [(.rbx, .reg .rbx)] ∧
    RegsAre (after b15 setS) [(.rbx, .reg .rbx)] ∧ RegsAre (after b20 setS) [(.rbx, .reg .rbx)] ∧
    RegsAre (after b26 setS) [(.rbx, .reg .rbx)] := by
  decide +kernel

public theorem ok_push : PushOk R04 (after b2 (pushS R04)) ∧ PushOk R04 (after b7 (pushS R04)) ∧
    PushOk R04 (after b12 (pushS R04)) ∧ PushOk R04 (after b17 (pushS R04)) ∧
    PushOk R04 (after b22 (pushS R04)) ∧ PushOk R5 (after b28 (pushS R5)) := by
  decide +kernel

public theorem ok_test : (after b1 regsS).mem = [] ∧ (after b6 regsS).mem = [] ∧
    (after b11 regsS).mem = [] ∧ (after b16 regsS).mem = [] ∧ (after b21 regsS).mem = [] ∧
    (after b27 regsS).mem = [] ∧
    KeptBut (after b1 regsS) [] ∧ KeptBut (after b6 regsS) [] ∧ KeptBut (after b11 regsS) [] ∧
    KeptBut (after b16 regsS) [] ∧ KeptBut (after b21 regsS) [] ∧ KeptBut (after b27 regsS) [] := by
  decide +kernel

public theorem ok_after : RegsAre (after b3 regsS) [(R04.a, .reg .r14), (.rax, .reg .rax)] ∧
    RegsAre (after b8 regsS) [(R04.a, .reg .r14), (.rax, .reg .rax)] ∧
    RegsAre (after b13 regsS) [(R04.a, .reg .r14), (.rax, .reg .rax)] ∧
    RegsAre (after b18 regsS) [(R04.a, .reg .r14), (.rax, .reg .rax)] ∧
    RegsAre (after b23 regsS) [(R04.a, .reg .r14), (.rax, .reg .rax)] ∧
    RegsAre (after b29 regsS) [(R5.a, .reg .r14), (.rax, .lit 0)] ∧
    (after b3 regsS).mem = [] ∧ (after b8 regsS).mem = [] ∧ (after b13 regsS).mem = [] ∧
    (after b18 regsS).mem = [] ∧ (after b23 regsS).mem = [] ∧ (after b29 regsS).mem = [] ∧
    KeptBut (after b3 regsS) [R04.a, .rax, .rcx] ∧ KeptBut (after b8 regsS) [R04.a, .rax, .rcx] ∧
    KeptBut (after b13 regsS) [R04.a, .rax, .rcx] ∧ KeptBut (after b18 regsS) [R04.a, .rax, .rcx] ∧
    KeptBut (after b23 regsS) [R04.a, .rax, .rcx] ∧ KeptBut (after b29 regsS) [R5.a, .rax, .rcx] := by
  decide +kernel

public theorem ok_exit : (after b4 regsS).mem = [] ∧ (after b9 regsS).mem = [] ∧
    (after b14 regsS).mem = [] ∧ (after b19 regsS).mem = [] ∧ (after b30 regsS).mem = [] ∧
    (after b24 regsS).mem = [] ∧ (after b31 regsS).mem = [] ∧
    KeptBut (after b4 regsS) [] ∧ KeptBut (after b9 regsS) [] ∧ KeptBut (after b14 regsS) [] ∧
    KeptBut (after b19 regsS) [] ∧ KeptBut (after b30 regsS) [] ∧
    KeptBut (after b24 regsS) [.rax] ∧ KeptBut (after b31 regsS) [.rax] ∧
    RegsAre (after b24 regsS) [(.rax, .lit 0)] ∧
    RegsAre (after b31 regsS) [(.rax, .bin .merge .W8 (.reg .rax) (.lit 1))] := by
  decide +kernel

public theorem ok_b25 : restores slots 64 (after b25 (midS 64)) = true ∧
    (after b25 (midS 64)).mem = [] ∧ RegsAre (after b25 (midS 64)) [(.rax, .reg .rax)] := by
  decide +kernel

public theorem keeps_set : keepsRegs evS (after b0b evS) (.rsp :: freeRegs slots) = true ∧
    keepsAll setS (after b5 setS) (freeRegs slots) = true ∧
    keepsAll setS (after b10 setS) (freeRegs slots) = true ∧
    keepsAll setS (after b15 setS) (freeRegs slots) = true ∧
    keepsAll setS (after b20 setS) (freeRegs slots) = true ∧
    keepsAll setS (after b26 setS) (freeRegs slots) = true := by
  decide +kernel

public theorem slots_ok : ∀ p ∈ slots, 16 ≤ p.1 ∧ p.1 + 8 ≤ 64 := by decide

public theorem freeRegs_slots : freeRegs slots = [] := by decide

end NativeRustcVmX64.Tables.ColumnClaims
