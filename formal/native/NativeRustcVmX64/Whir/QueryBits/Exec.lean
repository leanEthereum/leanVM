module

public import NativeRustcVmX64.Whir.Common
public import NativeRustcVmX64.Field.Frame
public import NativeRustcVmX64.Code.Vm.QueryBits
public meta import NativeRustcVmX64.Code.Vm.QueryBits
public meta import NativeRustcVmX64.Whir.Common
public meta import NativeRustcVmX64.Field.Frame

/-!
# `query_bits`'s blocks, run by the symbolic executor (x86-64)

Region 0 the return address at RSP (`Field.frameS 0`); every block from the entry's registers,
along the four paths: `shift = 0` (`b0`, `b6`), `0 < shift < 64` (`b0`, `b1`, `b2`, `b6`),
`64 ≤ shift < 128` (`b0`, `b1`, `b3`, `b4`, `b6`), `128 ≤ shift` (`b0`, `b1`, `b3`, `b5`, `b6`).
-/

namespace NativeRustcVmX64.Whir.QueryBits

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.QueryBits NativeRustcVmX64.Field

@[expose] public section

/-- At the entry. -/
abbrev entryS : SState := frameS 0

/-- After `b0`'s test. -/
def s1 : SState := after b0 entryS
/-- After `b1`'s test. -/
def s2 : SState := after b1 s1
/-- After `b3`'s test. -/
def s3 : SState := after b3 s2

/-- The mask: all ones for a depth (RCX) of `64` or more, else `!(-1 << depth)`. -/
def maskS : Sym :=
  .ite (.not (.cmp .ult .W64 (.reg .rcx) (.lit 64))) (.lit 18446744073709551615)
    (.un .not .W64 (.bin .shl .W64 (.lit 18446744073709551615) (.un .trunc .W32 (.reg .rcx))))

/-- RAX at the return: the mask and the value `v`. -/
def retS (v : Sym) : Sym := .bin .and .W64 maskS v

/-- The shift count, ECX = EDX. -/
def shS : Sym := .un .trunc .W32 (.reg .rdx)

/-- A path's end: RAX `retS v`, the callee-saved registers kept, no write, RSP above the return
address. -/
def finOk (S : SState) (v : Sym) : Bool :=
  S.reg .rax == some (retS v) && keeps entryS S && S.mem.isEmpty &&
    S.reg .rsp == some (.ptr 0 ((0 + 8 : Nat) : Int))

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 s1
sym_block run_b2 := exec b2 s2
sym_block run_b3 := exec b3 s2
sym_block run_b4 := exec b4 s3
sym_block run_b5 := exec b5 s3
sym_block run_b6z := exec b6 s1
sym_block run_b6a := exec b6 (after b2 s2)
sym_block run_b6b := exec b6 (after b4 s3)
sym_block run_b6c := exec b6 (after b5 s3)

public theorem fin_z : finOk (after b6 s1) (.reg .rdi) = true := by decide +kernel
public theorem fin_a : finOk (after b6 (after b2 s2)) (.tern .shrd .W64 (.reg .rdi) (.reg .rsi) shS) =
    true := by decide +kernel
public theorem fin_b : finOk (after b6 (after b4 s3)) (.bin .shr .W64 (.reg .rsi) shS) = true := by
  decide +kernel
public theorem fin_c : finOk (after b6 (after b5 s3)) (.lit 0) = true := by decide +kernel

end NativeRustcVmX64.Whir.QueryBits
