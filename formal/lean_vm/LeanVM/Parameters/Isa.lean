/-
  LeanVM.Parameters.Isa

  The opcode codes are distinct, and the two table-height caps the verifier checks announced
  sizes against.
-/

module

public import LeanVM.Parameters.Generator
public import Statement.LeanIsa
public import Statement.Fast.QuadExt
public import Statement.Fast.FieldWords

/-!
# Opcodes and instance caps

The opcodes, their codes and the
memory and bytecode caps are defined in `Statement.LeanIsa`; the two table-height caps are here.
Transcribed at leanVM
pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d`, the opcodes checked again at `4af2cddd`:

* the opcode codes `g^0, …, g^5` in the order XOR, MUL_NATIVE, SET_CONSTANT, DEREF, JUMP,
  KECCAK: `crates/leanvm_core/src/tables.rs:99-104` at `4af2cddd` (`OP_XOR`, …, `OP_KECCAK`; the
  sixth was `OP_BLAKE2S` at `127510d1`);
* the memory bounds `1 ≤ κ_mem ≤ 30`, the floor the public input's two cells: specification §2
  (`02-vm-specification.tex:49`) and §6.3 (`06-bus-interactions.tex:84`) at `aca3ea6a`;
  `crates/leanvm_core/src/cpu/mod.rs:38-39`, `crates/verifier/src/layout.rs:88`
  (`MIN_LOG_MEMORY`);
* at most `2^30` rows per table and `2^30` bytecode instructions: specification §6.2, "Instance
  caps", and §6.4; `cpu/mod.rs` (`MAX_LOG_ROWS`) and `crates/verifier/src/layout.rs`
  (`MAX_TABLE_LOG`, `MAX_LOG_BYTECODE`);

The verifier rejects an announcement outside these caps before any reduction runs
(`crates/verifier/src/layout.rs:387-395`); they are what keeps the total read count below
`2^64 - 1`, the bound the bus argument needs (specification §6.2). Each cap is a log-2 size, as
announced, so that `LeanIsaProgram.logSize_le`, `HoldsPublicInput` and `Caps` state the verifier's
checks by name. The codes are symbolic powers of `g`; the value of `g`
appears only in `LeanVM.Parameters.Generator`.
-/

namespace LeanVM.Parameters

@[expose] public section

/-- Distinct opcodes have distinct codes. -/
theorem Opcode.code_injective : Function.Injective Opcode.busCode := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide +kernel)

/-! ## Instance caps -/

/-- The greatest log-height of an opcode table (`cpu/mod.rs`, `MAX_LOG_ROWS`, which is
`MAX_TABLE_LOG` of `crates/verifier/src/layout.rs`). -/
def maxLogRows : ℕ := 30

end
end LeanVM.Parameters
