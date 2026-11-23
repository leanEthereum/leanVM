module

public import NativeRustcVmX64.Tables.ColumnClaims.Exec
public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.PublicInputPhase
public meta import NativeRustcVmX64.Code.Vm.PublicInputPhase
public meta import NativeRustcVmX64.Tables.ColumnClaims.Exec
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `public_input_phase`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the frame (`Transcript.Frame`, `F = 608`): the six pushes at `560` to `608`, RSP after
the prologue at `8` (`stO 8`), the calls' return addresses at `0`; the locals: the challenge (the
point of the `multilinear_eval_by` calls) at `16`, the two values at `32`, the claims' point (`31`
elements) at `64`. The public input is region 1 (`pubS`, at R14) for `b3` and `b6`.
-/

namespace NativeRustcVmX64.Tables.PublicInputPhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.PublicInputPhase NativeRustcVmX64.Transcript
open NativeRustcVmX64.Tables.ColumnClaims (RegsAre)

@[expose] public section

/-- RSP at the frame's offset `o`. -/
def stO (o : Nat) : SState := init [616] [(.rsp, .ptr 0 (o : Int))]
/-- The public input's four words at R14. -/
def pubS : SState := init [616, 32] [(.rsp, .ptr 0 8)] [] [] [(.reg .r14, 1, 0)]

/-- Every write in region 0. -/
def In0 (S : SState) : Prop := ∀ w ∈ S.mem, w.r = 0

instance (S : SState) : Decidable (In0 S) := by unfold In0; infer_instance

/-- Every write in region 0 below `L`. -/
def InFrame (S : SState) (L : Nat) : Prop := ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ L

instance (S : SState) (L : Nat) : Decidable (InFrame S L) := by unfold InFrame; infer_instance

/-- The words of region `r` at `p.1` written as `p.2`. -/
def WrW (r : Nat) (S : SState) (l : List (Nat × Sym)) : Prop :=
  ∀ p ∈ l, ∀ t < 8, findWrite r (p.1 + t) S.mem = some (p.2, t)

instance (r : Nat) (S : SState) (l : List (Nat × Sym)) : Decidable (WrW r S l) := by
  unfold WrW; infer_instance

/-- The pushed registers' slots. -/
def slots : Slots := [(600, .rbp), (592, .r15), (584, .r14), (576, .r13), (568, .r12), (560, .rbx)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 (stO 608)
sym_block run_b1 := exec b1 (stO 8)
sym_block run_b2 := exec b2 (stO 8)
sym_block run_b3 := exec b3 pubS
sym_block run_b4 := exec b4 (stO 8)
sym_block run_b5 := exec b5 (stO 8)
sym_block run_b6 := exec b6 pubS
sym_block run_b7 := exec b7 (stO 8)
sym_block run_b8 := exec b8 (stO 8)
sym_block run_b9 := exec b9 (stO 8)

public theorem ok_b0 : ProOk 608 0 slots (after b0 (stO 608)) = true ∧ In0 (after b0 (stO 608)) ∧
    RegsAre (after b0 (stO 608)) [(.rbx, .reg .rcx), (.r14, .reg .rdx), (.r13, .reg .rsi),
      (.rdi, .reg .rdi)] := by
  decide +kernel

public theorem ok_b1 : MidOk 608 0 slots (after b1 (stO 8)) = true ∧ In0 (after b1 (stO 8)) ∧
    InFrame (after b1 (stO 8)) 560 ∧
    RegsAre (after b1 (stO 8)) [(.rsi, .lit 0), (.rdi, .reg .r13), (.rbp, .lit 0), (.r12, .reg .rdx),
      (.r15, .reg .rax), (.rbx, .reg .rbx), (.r14, .reg .r14)] ∧
    (∀ j < 62, ∀ t < 8, findWrite 0 (64 + 8 * j + t) (after b1 (stO 8)).mem = some (.lit 0, t)) := by
  decide +kernel

public theorem ok_b2 : MidOk 608 8 slots (after b2 (stO 8)) = true ∧ (after b2 (stO 8)).mem = [] ∧
    RegsAre (after b2 (stO 8)) [(.r13, .bin .add .W64 (.reg .rax)
      (.ite (.cmp .ult .W64 (.reg .rax) (.lit 1)) (.lit 1) (.lit 0))), (.rbp, .reg .rbp),
      (.rbx, .reg .rbx), (.r12, .reg .r12), (.r14, .reg .r14), (.r15, .reg .r15)] := by
  decide +kernel

public theorem ok_b3 : MidOk 608 0 slots (after b3 pubS) = true ∧ In0 (after b3 pubS) ∧
    InFrame (after b3 pubS) 80 ∧
    RegsAre (after b3 pubS) [(.rcx, .ptr 0 16), (.rdx, .lit 2), (.rsi, .ptr 0 32), (.rdi, .lit 2),
      (.r8, .lit 1), (.rbp, .reg .rbp), (.rbx, .reg .rbx), (.r12, .reg .r12), (.r13, .reg .r13), (.r14, .reg .r14), (.r15, .reg .r15)] ∧
    WrW 0 (after b3 pubS) [(16, .reg .r15), (24, .reg .r12), (32, .load 1 0 8), (40, .lit 0),
      (48, .load 1 16 8), (56, .lit 0), (64, .reg .r15), (72, .reg .r12)] := by
  decide +kernel

public theorem ok_b6 : MidOk 608 0 slots (after b6 pubS) = true ∧ In0 (after b6 pubS) ∧
    InFrame (after b6 pubS) 64 ∧
    RegsAre (after b6 pubS) [(.rcx, .ptr 0 16), (.rdx, .lit 2), (.rsi, .ptr 0 32), (.rdi, .lit 2),
      (.r8, .lit 1), (.rbp, .reg .rbp), (.rbx, .reg .rbx), (.r12, .reg .r12), (.r13, .reg .r13), (.r14, .reg .r14), (.r15, .reg .r15)] ∧
    WrW 0 (after b6 pubS) [(16, .reg .r15), (24, .reg .r12), (32, .load 1 8 8), (40, .lit 0),
      (48, .load 1 24 8), (56, .lit 0)] := by
  decide +kernel

public theorem ok_b4 : MidOk 608 0 slots (after b4 (stO 8)) = true ∧ In0 (after b4 (stO 8)) ∧
    InFrame (after b4 (stO 8)) 8 ∧
    RegsAre (after b4 (stO 8)) [(.rcx, .reg .r13), (.rdx, .ptr 0 64), (.rsi, .lit 0),
      (.rdi, .reg .rbx), (.rbp, .lit 0), (.r8, .reg .rax), (.r9, .reg .rdx), (.rbx, .reg .rbx), (.r12, .reg .r12), (.r13, .reg .r13), (.r14, .reg .r14), (.r15, .reg .r15)] := by
  decide +kernel

public theorem ok_b7 : MidOk 608 0 slots (after b7 (stO 8)) = true ∧ In0 (after b7 (stO 8)) ∧
    InFrame (after b7 (stO 8)) 8 ∧
    RegsAre (after b7 (stO 8)) [(.rcx, .reg .r13), (.rdx, .ptr 0 64), (.rsi, .lit 1),
      (.rdi, .reg .rbx), (.rbp, .reg .rbp), (.r8, .reg .rax), (.r9, .reg .rdx), (.rbx, .reg .rbx), (.r12, .reg .r12), (.r13, .reg .r13), (.r14, .reg .r14), (.r15, .reg .r15)] := by
  decide +kernel

public theorem ok_b5 : MidOk 608 8 slots (after b5 (stO 8)) = true ∧ (after b5 (stO 8)).mem = [] ∧
    RegsAre (after b5 (stO 8)) [(.rbp, .reg .rbp), (.rbx, .reg .rbx), (.r12, .reg .r12), (.r13, .reg .r13), (.r14, .reg .r14), (.r15, .reg .r15)] := by
  decide +kernel

public theorem ok_b8 : MidOk 608 8 slots (after b8 (stO 8)) = true ∧ (after b8 (stO 8)).mem = [] ∧
    RegsAre (after b8 (stO 8)) [(.rbp, .un .trunc .W32 (.reg .rax))] := by
  decide +kernel

public theorem ok_b9 : EpiOk 608 slots (after b9 (stO 8)) = true ∧ (after b9 (stO 8)).mem = [] ∧
    RegsAre (after b9 (stO 8)) [(.rax, .un .trunc .W32 (.reg .rbp))] := by
  decide +kernel

end NativeRustcVmX64.Tables.PublicInputPhase
