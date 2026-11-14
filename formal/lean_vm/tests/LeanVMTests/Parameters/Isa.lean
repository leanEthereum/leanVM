module

public import LeanVM.Parameters.Isa

/-!
# Tests: opcode codes and instance caps

Kernel checks that the six codes are the words `1, 2, 4, 8, 16, 32`, bits `0` to `5` since `g = x`,
in the order of `crates/leanvm_core/src/tables.rs`, and that the caps carry the values of
`cpu/mod.rs`, `crates/verifier/src/layout.rs` and `crates/flock/src/hash.rs`. The
caps are checked against each other so that an announcement at the floor is admissible.
-/

namespace LeanVMTests.Parameters

open LeanVM.Parameters

public section

/-! ## Codes -/

/-- `OP_XOR = 1, OP_MUL = 2, OP_SET = 4, OP_DEREF = 8, OP_JUMP = 16, OP_KECCAK = 32`. -/
example : Opcode.xor.busCode = 0x01 ∧ Opcode.mulNative.busCode = K.ofBits 0x02 ∧ Opcode.setConstant.busCode = K.ofBits 0x04 ∧
    Opcode.deref.busCode = K.ofBits 0x08 ∧ Opcode.jump.busCode = K.ofBits 0x10 ∧ Opcode.keccak.busCode = K.ofBits 0x20 := by
  decide +kernel

/-- The codes are the six lowest addresses, in order. -/
example : ∀ o : Opcode, o.busCode = addressOfIndex (Opcode.ctorIdx o) := by
  intro o; cases o <;> rfl

/-- Mutation: two codes never coincide; `code_injective` on the pair closest in the table. -/
example : Opcode.deref.busCode ≠ Opcode.jump.busCode :=
  fun h ↦ Opcode.noConfusion (Opcode.code_injective h)

/-! ## Caps -/

example : minLogMem = 1 ∧ maxLogMem = 30 ∧ maxLogRows = 30 ∧ maxLogBytecode = 30 := by
  decide

/-- The floor is below the cap: the smallest announcement is admissible. -/
example : minLogMem ≤ maxLogMem := by decide

/-- Every cap keeps its address space inside the order of `g`, which `gLog?_spec` needs. -/
example : maxLogMem < 64 ∧ maxLogBytecode < 64 := by decide

end
end LeanVMTests.Parameters
