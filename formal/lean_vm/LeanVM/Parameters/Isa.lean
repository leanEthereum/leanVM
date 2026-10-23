/-
  LeanVM.Parameters.Isa

  The opcode codes are distinct, and the two table-height caps the verifier checks announced
  sizes against.
-/

module

public import LeanVM.Parameters.Generator
public import LeanVM.Spec.Isa

/-!
# Opcodes and instance caps

The opcodes, their codes and the
memory and bytecode caps are defined in `LeanVM.Spec.Isa`; the two table-height caps are here.
Transcribed at leanVM
pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d`:

* the opcode codes `g^0, …, g^5` in the order XOR, MUL_NATIVE, SET_CONSTANT, DEREF, JUMP,
  BLAKE2S: specification §6.4 (`doc/leanvm/body/06-bus-interactions.tex:95`) and
  `crates/leanvm_core/src/tables.rs:99-104` (`OP_XOR`, …, `OP_BLAKE2S`);
* the memory bounds `16 ≤ κ_mem ≤ 32`: specification §2 (`02-vm-specification.tex:49`) and
  §6.3 (`06-bus-interactions.tex:86`); `crates/leanvm_core/src/cpu/mod.rs:51-52`;
* at most `2^32` rows per table and `2^32` bytecode instructions: specification §6.2, "Instance
  caps" (`06-bus-interactions.tex:80`) and §6.4 (`:93`); `cpu/mod.rs:60` (`MAX_LOG_ROWS`) and
  `crates/verifier/src/layout.rs:84`, `:393` (`MAX_TABLE_LOG`, the bytecode bound);

The verifier rejects an announcement outside these caps before any reduction runs
(`crates/verifier/src/layout.rs:387-395`); they are what keeps the total read count below
`2^64 - 1`, the bound the bus argument needs (specification §6.2). Each cap is a log-2 size, as
announced, so that `Program.logSize_le`, `HasPublicBoundary` and `Caps` state the verifier's
checks by name. The codes are symbolic powers of `g`; the value of `g`
appears only in `LeanVM.Parameters.Generator`.
-/

namespace LeanVM.Parameters

@[expose] public section

/-- Distinct opcodes have distinct codes. -/
theorem Opcode.code_injective : Function.Injective Opcode.code := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide +kernel)

/-! ## Instance caps -/

/-- The greatest log-height of an opcode table (`cpu/mod.rs:60`, `MAX_LOG_ROWS`). -/
def maxLogRows : ℕ := 32

end
end LeanVM.Parameters
