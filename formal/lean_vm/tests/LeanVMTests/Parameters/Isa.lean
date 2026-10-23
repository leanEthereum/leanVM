module

public import LeanVM.Parameters.Isa

/-!
# Tests: opcode codes and instance caps

Kernel checks that the six codes are the words `1, 2, 4, 8, 16, 32`, bits `0` to `5` since `g = x`,
in the order of `crates/leanvm_core/src/tables.rs:99-104`, and that the caps carry the values of
`cpu/mod.rs:51-60`, `crates/verifier/src/layout.rs:393` and `crates/flock/src/hash.rs:281-284`. The
caps are checked against each other so that an announcement at the floor is admissible.
-/

namespace LeanVMTests.Parameters

open LeanVM.Parameters

public section

/-! ## Codes -/

/-- `OP_XOR = 1, OP_MUL = 2, OP_SET = 4, OP_DEREF = 8, OP_JUMP = 16, OP_BLAKE2S = 32`. -/
example : Opcode.xor.code = 0x01 ∧ Opcode.mulNative.code = K.ofBits 0x02 ∧ Opcode.setConstant.code = K.ofBits 0x04 ∧
    Opcode.deref.code = K.ofBits 0x08 ∧ Opcode.jump.code = K.ofBits 0x10 ∧ Opcode.blake2s.code = K.ofBits 0x20 := by
  decide +kernel

/-- The codes are the six lowest addresses, in order. -/
example : ∀ o : Opcode, o.code = gpow (Opcode.ctorIdx o) := by
  intro o; cases o <;> rfl

/-- Mutation: two codes never coincide; `code_injective` on the pair closest in the table. -/
example : Opcode.deref.code ≠ Opcode.jump.code :=
  fun h ↦ Opcode.noConfusion (Opcode.code_injective h)

/-! ## Caps -/

example : minLogMem = 16 ∧ maxLogMem = 32 ∧ maxLogRows = 32 ∧ maxLogBytecode = 32 := by
  decide

/-- The floor is below the cap: the smallest announcement is admissible. -/
example : minLogMem ≤ maxLogMem := by decide

/-- Every cap keeps its address space inside the order of `g`, which `gLog?_spec` needs. -/
example : maxLogMem < 64 ∧ maxLogBytecode < 64 := by decide

end
end LeanVMTests.Parameters
