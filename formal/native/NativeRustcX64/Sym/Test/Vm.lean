module

public import NativeRustcX64.Sym
public meta import NativeRustcVmX64.Code.Vm.KeccakPi
public meta import NativeRustcVmX64.Code.Vm.BitLength
public meta import NativeRustcVmX64.Code.Vm.PublicInputPhase

/-!
# The x86-64 symbolic executor on blocks of the leanVM verifier

Blocks of `leanvm_verify` using the instructions the signature verifiers do not: one-operand
`mulq` (`keccak_pi`), `sbbq` (`bit_length`) and `adcq` (`public_input_phase`).
-/

namespace NativeRustcX64.Sym.Test.Vm

set_option Elab.async false

open NativeRustcVmX64.Vm

/-- RSP at the return address, the 8-byte region 0. -/
def retS : SState := init [8] [(.rsp, .ptr 0 0)]

sym_block keccak_pi_exec := exec KeccakPi.b0 retS

/-- `keccak_pi` runs to its `retq`; `mulq %rdx` leaves CF and OF known, the high half in RDX. -/
example : (exec KeccakPi.b0 retS).map (fun r => (r.1.flags.cf.isSome, r.2)) =
    some (true, .ret (.load 0 0 8)) := by
  rw [keccak_pi_exec]
  rfl

sym_block bit_length_exec := exec BitLength.b0 retS

/-- `bit_length` runs to its `retq` through `sbbq $-1, %rax`. -/
example : (exec BitLength.b0 retS).map (·.2) = some (.ret (.load 0 0 8)) := by
  rw [bit_length_exec]
  rfl

sym_block public_input_b2_exec := exec PublicInputPhase.b2 (init [])

/-- `cmpq $1, %rax; movq %rax, %r13; adcq $0, %r13`: R13 is RAX plus the borrow of `rax - 1`. -/
example : (exec PublicInputPhase.b2 (init [])).map (·.1.reg .r13) =
    some (some (.bin .add .W64 (.reg .rax)
      (.ite (.cmp .ult .W64 (.reg .rax) (.lit 1)) (.lit 1) (.lit 0)))) := by
  rw [public_input_b2_exec]
  rfl

end NativeRustcX64.Sym.Test.Vm
