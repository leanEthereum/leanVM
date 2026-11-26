/-
  LeanVM.Arithmetization.Completeness.Basics

  What the completeness witness and the hand-built `SatisfiedBy` witness share: a typed row as a
  raw row, a table's interactions read through its row circuit, and the constraints of the
  components that have none.
-/

module

public import LeanVM.Arithmetization.Statement

@[expose] public section

/-!
# Shared vocabulary of the completeness witness

These are the row-generic facts that the hand-built `SatisfiedBy` witness proves in
`tests/LeanVMTests/Arithmetization/Statement.lean`, moved here so that the construction of the
witness for an arbitrary trace and the hand-built one use the same proofs; the test file imports
them back and its proofs are unchanged.

* `rawRow` writes a typed row as the raw row Clean's tables hold (`toElements`).
* `table_interactions_eq` reads a table's interactions through its row circuit
  (`Component.rowOperations`): the form the kernel evaluates and the form this layer rewrites.
  `Component.operations` reaches them through `instantiate` and `toSubcircuit`, which the kernel
  does not unfold. `rowMessagesOn_eq` is the same for one row.
* `xor_constraints` and its six siblings: the components with no constraint satisfy their
  constraints on every row, in every environment, since only the `JUMP` table asserts anything
  (`tables.rs`).

## Wrong readings excluded

* A raw row is the typed row's elements and nothing more: the `JUMP` table's two local
  witnesses are not part of it and are appended by the witness (`Completeness.Messages`).
* The constraints here hold in every environment: a wrong count never breaks them, it breaks
  the bus.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics
open Air.Flat (Component EnsembleWitness)

/-! ## Raw rows -/

/-- A typed row as a raw row: its elements, in column order. -/
def rawRow {Row : TypeMap} [ProvableType Row] (r : Row K) : Array K := (toElements r).toArray

/-- A raw row has the row type's width. -/
theorem rawRow_size {Row : TypeMap} [ProvableType Row] (r : Row K) :
    (rawRow r).size = size Row :=
  Vector.size_toArray _

/-- The raw rows of a list of typed rows all have the row type's width. -/
theorem rawRows_size {Row : TypeMap} [ProvableType Row] (rs : List (Row K)) :
    ∀ r ∈ rs.map rawRow, r.size = size Row := by
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨_, -, rfl⟩ := hr
  exact rawRow_size _

/-! ## A table's interactions through its row circuit -/

/-- A table's interactions through the row circuit (Clean's `Component.interactions_eq`): the
form the kernel evaluates, `Component.operations` reaching them through `instantiate` and
`toSubcircuit`, which it does not unfold. -/
theorem table_interactions_eq (t : Air.Flat.Table K) :
    t.interactions = t.table.flatMap fun row ↦
      t.component.rowOperations.interactions.map (·.eval (t.environment row)) := by
  simp only [Air.Flat.Table.interactions, Operations.interactionValues, Component.interactions_eq]

/-- A row's messages on a channel, through the row circuit. -/
theorem rowMessagesOn_eq (t : Air.Flat.Table K) (r : Array K) (c : RawChannel K) :
    rowMessagesOn t r c =
      ((t.component.rowOperations.interactions.map (·.eval (t.environment r))).filter
        (·.channel.name = c.name)).map (·.msg) := by
  rw [rowMessagesOn, Operations.interactionValues, Component.interactions_eq]

/-! ## The components with no constraint -/

/-- The `XOR` table asserts nothing: its constraints hold in every environment. -/
theorem xor_constraints (env : Environment K) :
    (opcodeComponent xorTable).operations.ConstraintsHold env := by
  rw [Component.constraintsHold_iff]
  simp only [circuit_norm, opcodeComponent, xorTable, memRead, bytecodeRead, -BitVec.reduceNeg]

/-- The `MUL_NATIVE` table asserts nothing. -/
theorem mul_constraints (env : Environment K) :
    (opcodeComponent mulTable).operations.ConstraintsHold env := by
  rw [Component.constraintsHold_iff]
  simp only [circuit_norm, opcodeComponent, mulTable, memRead, bytecodeRead, -BitVec.reduceNeg]

/-- The `SET_CONSTANT` table asserts nothing. -/
theorem set_constraints (env : Environment K) :
    (opcodeComponent setTable).operations.ConstraintsHold env := by
  rw [Component.constraintsHold_iff]
  simp only [circuit_norm, opcodeComponent, setTable, memRead, bytecodeRead, -BitVec.reduceNeg]

/-- The `DEREF` table asserts nothing. -/
theorem deref_constraints (env : Environment K) :
    (opcodeComponent derefTable).operations.ConstraintsHold env := by
  rw [Component.constraintsHold_iff]
  simp only [circuit_norm, opcodeComponent, derefTable, memRead, bytecodeRead, -BitVec.reduceNeg]

/-- The `KECCAK` table asserts nothing: the permutation is the Keccak reduction's
(`KeccakRowsValid`). -/
theorem keccak_constraints (env : Environment K) :
    (opcodeComponent keccakTable).operations.ConstraintsHold env := by
  rw [Component.constraintsHold_iff]
  simp only [circuit_norm, opcodeComponent, keccakTable, memRead, memReadIf, bytecodeRead, -BitVec.reduceNeg]

/-- The memory block asserts nothing. -/
theorem mem_constraints (κ : ℕ) (env : Environment K) :
    (memComponent κ).operations.ConstraintsHold env := by
  rw [Component.constraintsHold_iff]
  simp only [circuit_norm, memComponent, memTable, -BitVec.reduceNeg]

/-- The bytecode block asserts nothing. -/
theorem bytecode_constraints (prog : LeanIsaProgram) (env : Environment K) :
    (bytecodeComponent prog).operations.ConstraintsHold env := by
  rw [Component.constraintsHold_iff]
  simp only [circuit_norm, bytecodeComponent, bytecodeTable, -BitVec.reduceNeg]

end LeanVM.Arithmetization
