module

public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVmX64.Code.Vm.VerifyBusBalanceClosure0
public import NativeRustcVmX64.Code.Vm.Fingerprints.Names
public meta import NativeRustcVmX64.Code.Vm.VerifyBusBalanceClosure0
public meta import NativeRustcVmX64.Sumcheck.Common

/-!
# `verify_bus_balance::{closure#0}`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 96-byte frame below the entry's RSP and the return address (`F = 96`): R15, R14,
RBX pushed at `88`, `80`, `72`, then `fingerprints`' eight stack arguments at `8` to `64`, its
return address at `0`. `b0` runs in four parts, each in an environment of its own:

- `b0a` (`sA`): the prologue, the environment's words read (region 1 the environment, RSI);
- `b0b` (`sB`): the closure's own stack argument (`32(%rsp)`, above the return address: region 0
  the frame and the 8 bytes above, `112` bytes) and the four registers pushed;
- `b0c` (`sC`): the share's two words pushed (region 1 the share, R15);
- `b0d` (`sD`): `bytecode_low`'s length pushed (region 1 the environment, R14), the call.

`b1` (`sE`) pops the frame and returns.
-/

namespace NativeRustcVmX64.Bus.FpClosure

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalanceClosure0
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(88, .r15), (80, .r14), (72, .rbx)]

/-- `b0`'s parts. -/
def b0a : List Directive := b0.take 15
def b0b : List Directive := (b0.drop 15).take 5
def b0c : List Directive := ((b0.drop 15).drop 5).take 2
def b0d : List Directive := ((b0.drop 15).drop 5).drop 2

def sA : SState := init [104, 56] [(.rsp, .ptr 0 96), (.rsi, .ptr 1 0)]
def sB : SState := init [112] [(.rsp, .ptr 0 72)]
def sC : SState := init [104, 16] [(.rsp, .ptr 0 32), (.r15, .ptr 1 0)]
def sD : SState := init [104, 56] [(.rsp, .ptr 0 16), (.r14, .ptr 1 0)]
def sE : SState := init [104] [(.rsp, .ptr 0 8)]

/-- What `b0a` leaves: the frame set up, the arguments moved, the environment's words read. -/
def AOk (S : SState) : Prop :=
  ProOk 96 72 slots S = true ∧ (∀ w ∈ S.mem, w.r = 0 ∧ 72 ≤ w.off ∧ w.off + w.n ≤ 96) ∧
    S.reg .rax = some (.reg .r9) ∧ S.reg .r10 = some (.reg .r8) ∧
    S.reg .r11 = some (.reg .rcx) ∧ S.reg .rbx = some (.reg .rdx) ∧
    S.reg .r14 = some (.ptr 1 0) ∧ S.reg .rsi = some (.load 1 0 8) ∧
    S.reg .rdx = some (.load 1 8 8) ∧ S.reg .rcx = some (.load 1 16 8) ∧
    S.reg .r8 = some (.load 1 24 8) ∧ S.reg .r9 = some (.load 1 32 8) ∧
    S.reg .r15 = some (.load 1 48 8) ∧ S.reg .rdi = some (.reg .rdi)

instance (S : SState) : Decidable (AOk S) := by unfold AOk; infer_instance

/-- What `b0b` leaves: the stack argument and four registers pushed, nothing else changed. -/
def BOk (S : SState) : Prop :=
  S.reg .rsp = some (.ptr 0 32) ∧ (∀ w ∈ S.mem, w.r = 0 ∧ 32 ≤ w.off ∧ w.off + w.n ≤ 72) ∧
    WordW 0 64 (.load 0 104 8) S ∧ WordW 0 56 (.reg .rax) S ∧ WordW 0 48 (.reg .r10) S ∧
    WordW 0 40 (.reg .r11) S ∧ WordW 0 32 (.reg .rbx) S ∧
    allRegs.all (fun r ↦ r == .rsp || S.reg r == some (.reg r)) = true

instance (S : SState) : Decidable (BOk S) := by unfold BOk; infer_instance

/-- What `b0c` leaves: the share's words pushed. -/
def COk (S : SState) : Prop :=
  MidOk 96 16 slots S = true ∧ (∀ w ∈ S.mem, w.r = 0 ∧ 16 ≤ w.off ∧ w.off + w.n ≤ 32) ∧
    WordW 0 24 (.load 1 8 8) S ∧ WordW 0 16 (.load 1 0 8) S ∧
    allRegs.all (fun r ↦ (r == .rsp || r == .r15) || S.reg r == some (.reg r)) = true

instance (S : SState) : Decidable (COk S) := by unfold COk; infer_instance

/-- What `b0d` leaves at the call: `bytecode_low`'s length pushed, the return address. -/
def DOk (S : SState) : Prop :=
  MidOk 96 0 slots S = true ∧ (∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 16) ∧
    WordW 0 8 (.load 1 40 8) S ∧
    allRegs.all (fun r ↦ (r == .rsp || r == .r14) || S.reg r == some (.reg r)) = true

instance (S : SState) : Decidable (DOk S) := by unfold DOk; infer_instance

end

set_option Elab.async false

sym_block run_b0a := exec b0a sA
sym_block run_b0b := exec b0b sB
sym_block run_b0c := exec b0c sC
sym_block run_b0d := exec b0d sD
sym_block run_b1 := exec b1 sE

end NativeRustcVmX64.Bus.FpClosure

namespace NativeRustcVmX64.Bus.FpClosure

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalanceClosure0
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck

public theorem exit_b0a : exec b0a sA = some (after b0a sA, .fall) :=
  run_b0a.trans (by rw [after_eq run_b0a])
public theorem ok_b0a : AOk (after b0a sA) := by decide +kernel

public theorem exit_b0b : exec b0b sB = some (after b0b sB, .fall) :=
  run_b0b.trans (by rw [after_eq run_b0b])
public theorem ok_b0b : BOk (after b0b sB) := by decide +kernel

public theorem exit_b0c : exec b0c sC = some (after b0c sC, .fall) :=
  run_b0c.trans (by rw [after_eq run_b0c])
public theorem ok_b0c : COk (after b0c sC) := by decide +kernel

public theorem exit_b0d : exec b0d sD =
    some (after b0d sD, .call NativeRustcVmX64.Vm.Fingerprints.entryLabel) :=
  run_b0d.trans (by rw [after_eq run_b0d])
public theorem ok_b0d : DOk (after b0d sD) := by decide +kernel

public theorem exit_b1 : exec b1 sE = some (after b1 sE, .ret (.load 0 96 8)) :=
  run_b1.trans (by rw [after_eq run_b1])
public theorem ok_b1 : EpiOk 96 slots (after b1 sE) = true ∧ (after b1 sE).mem = [] := by
  decide +kernel

public theorem len_b0a : b0a.length = 15 := by decide
public theorem len_b0b : b0b.length = 5 := by decide
public theorem len_b0c : b0c.length = 2 := by decide
public theorem len_b0d : b0d.length = 2 := by decide

public theorem b0_split : b0 = b0a ++ (b0b ++ (b0c ++ b0d)) := by
  simp only [b0a, b0b, b0c, b0d, List.take_append_drop]

end NativeRustcVmX64.Bus.FpClosure
