module

public import NativeRustcVmX64.Field.Parts
public meta import NativeRustcVmX64.Field.Parts
public import NativeRustcVmX64.Field.Frame
public meta import NativeRustcVmX64.Field.Frame
public import NativeRustcVmX64.Code.Vm.BitLength
public meta import NativeRustcVmX64.Code.Vm.BitLength

/-!
# `bit_length`'s block, run by the symbolic executor (x86-64)

`bit_length` is one straight-line block (`b0`), run from `frameS 0` (its return address at RSP).
rustc unrolls the halving loop into `cmov`s and assembles the count from `setne`s by shifts, `or`s
and `lea`s: its result is `blS` (`rax_eq`).
-/

namespace NativeRustcVmX64.Field.BitLength

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Field NativeRustcVmX64.Vm.BitLength

@[expose] public section

/-- `v >>> s`. -/
def shrS (s : Nat) (v : Sym) : Sym := .bin .shr .W64 v (.lit s)

/-- The halving step at `s`: `v >>> s` if nonzero, else `v`. -/
def stepS (s : Nat) (v : Sym) : Sym := .ite (.cmp .eq .W64 (shrS s v) (.lit 0)) v (shrS s v)

/-- `setne` of `v >>> s`, into a zeroed register's low byte. -/
def bitS (s : Nat) (v : Sym) : Sym :=
  .bin .merge .W8 (.lit 0) (.ite (.not (.cmp .eq .W64 (shrS s v) (.lit 0))) (.lit 1) (.lit 0))

/-- RAX at the return. -/
def blS : Sym :=
  let v1 := stepS 32 (.reg .rdi)
  let v2 := stepS 16 v1
  let v3 := stepS 8 v2
  let v4 := stepS 4 v3
  let v5 := stepS 2 v4
  let n1 := Sym.bin .or .W32 (.bin .shl .W32 (bitS 16 v1) (.lit 4))
    (.bin .shl .W32 (bitS 32 (.reg .rdi)) (.lit 5))
  let n2 := Sym.un .trunc .W32 (.bin .add .W64 n1 (.bin .mul .W64 (bitS 8 v2) (.lit 8)))
  let n3 := Sym.un .trunc .W32 (.bin .add .W64 n2 (.bin .mul .W64 (bitS 4 v3) (.lit 4)))
  let n4 := Sym.un .trunc .W32 (.bin .add .W64 n3 (.bin .mul .W64 (bitS 2 v4) (.lit 2)))
  let r := Sym.bin .or .W64
    (.bin .merge .W8 (.lit 0) (.ite (.not (.cmp .ult .W64 v5 (.lit 2))) (.lit 1) (.lit 0))) n4
  .bin .sub .W64 (.bin .sub .W64 r (.lit 18446744073709551615))
    (.ite (.cmp .ult .W64 v5 (.lit 1)) (.lit 1) (.lit 0))

end

set_option Elab.async false

sym_part r := exec b0 (frameS 0)

public theorem rax_eq : r.out.reg .rax = some blS := by decide +kernel

public theorem exit_eq : r.exit = .ret (.load 0 0 8) := by decide +kernel

public theorem rsp_eq : r.out.reg .rsp = some (.ptr 0 ((0 + 8 : Nat) : Int)) := by decide +kernel

public theorem keeps_eq : keeps (frameS 0) r.out = true := by decide +kernel

public theorem mem_eq : ∀ w ∈ r.out.mem, w.r = 0 ∧ w.off + w.n ≤ 0 := by decide +kernel

end NativeRustcVmX64.Field.BitLength
