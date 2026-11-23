module

public import NativeRustcVmX64.Field.Parts
public meta import NativeRustcVmX64.Field.Parts
public import NativeRustcVmX64.Field.RustSym
public import NativeRustcVmX64.Field.Frame
public meta import NativeRustcVmX64.Field.Frame
public import NativeRustcVmX64.Code.Vm.Kmul
public meta import NativeRustcVmX64.Code.Vm.Kmul

/-!
# `kmul`'s block, run by the symbolic executor in parts (x86-64)

`kmul` is one straight-line block (`b0`), run from `frameS 48` (its 6 pushes below RSP) in five
parts: the first pushes, computes the low word of the carry-less product and bit-reverses the
first factor (R15, variable `0`); the second bit-reverses the second factor (RCX, variable `1`);
the third multiplies the reversed factors (RSI, variable `2`); the fourth bit-reverses that
product (RCX, variable `3`); the fifth reduces and returns, retaining rustc's base-less scaled
`lea`. Each variable is checked against its definition (`c1` to `c4`), the result against the
transcription's reduction (`c5`).
-/

namespace NativeRustcVmX64.Field.Kmul

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Field NativeRustcVmX64.Vm.Kmul

set_option Elab.async false

sym_part r1 := exec (slice b0 0 100) (frameS 48)
sym_part r2 := exec (slice b0 100 16) (r1.out.setReg .r15 (some (.var 0)))
sym_part r3 := exec (slice b0 116 66) (r2.out.setReg .rcx (some (.var 1)))
sym_part r4 := exec (slice b0 182 19) (r3.out.setReg .rsi (some (.var 2)))
sym_part r5 := exec (slice b0 201 22) (r4.out.setReg .rcx (some (.var 3)))

public theorem c1 : (r1.out.reg .r15).map (fun v ↦ Lin.checkRev 64 v (.reg .rdi)) = some true := by
  decide +kernel

public theorem c2 : (r2.out.reg .rcx).map (fun v ↦ Lin.checkRev 64 v (.reg .rsi)) = some true := by
  decide +kernel

public theorem c3 : (r3.out.reg .rsi).map
    (fun v ↦ Lin.check 64 v (clmulLowS (.var 0) (.var 1))) = some true := by
  decide +kernel

public theorem c4 : (r4.out.reg .rcx).map (fun v ↦ Lin.checkRev 64 v (.var 2)) = some true := by
  decide +kernel

public theorem c5 : (r5.out.reg .rax).map (fun v ↦ Lin.check 64 v
    (reduceS (clmulLowS (.reg .rdi) (.reg .rsi)) (shrS (.var 3) 1))) = some true := by
  decide +kernel

public theorem r1_exit : r1.exit = .fall := by decide +kernel
public theorem r2_exit : r2.exit = .fall := by decide +kernel
public theorem r3_exit : r3.exit = .fall := by decide +kernel
public theorem r4_exit : r4.exit = .fall := by decide +kernel
public theorem r5_exit : r5.exit = .ret (.load 0 48 8) := by decide +kernel

public theorem lens : (slice b0 0 100).length = 100 ∧ (slice b0 100 16).length = 16 ∧
    (slice b0 116 66).length = 66 ∧ (slice b0 182 19).length = 19 ∧ 201 ≤ b0.length := by
  decide +kernel

public theorem r5_rsp : r5.out.reg .rsp = some (.ptr 0 ((48 + 8 : Nat) : Int)) := by
  decide +kernel

public theorem r5_keeps : keeps (frameS 48) r5.out = true := by decide +kernel

public theorem r5_mem : ∀ w ∈ r5.out.mem, w.r = 0 ∧ w.off + w.n ≤ 48 := by decide +kernel

end NativeRustcVmX64.Field.Kmul
