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
* `filter_eq_nil_of_rowOps`, `memTable_rowOps` and `bytecodeTable_rowOps`: a table whose row
  circuit has no interaction on a channel sends nothing on it, and the two blocks' interactions
  are their seed push and finalize pull on the row's variables.
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

/-- The memory block's two interactions, on a row's variables (the limbs in cells `0`-`1`, the
address in `2`, the finalize count in `3`): the seed push at count `1` and the finalize pull. -/
theorem memTable_rowOps (κ : ℕ) :
    (memComponent κ).rowOperations.interactions =
      [⟨MemPush.toRaw, .push, 1, toElements (⟨var ⟨2⟩, 1, #v[var ⟨0⟩, var ⟨1⟩]⟩ :
          MemMsg (Expression K))⟩,
       ⟨MemPull.toRaw, .pull, 1, toElements (⟨var ⟨2⟩, var ⟨3⟩, #v[var ⟨0⟩, var ⟨1⟩]⟩ :
          MemMsg (Expression K))⟩] := by
  with_unfolding_all rfl

/-- The bytecode block's two interactions, on a row's variables. -/
theorem bytecodeTable_rowOps (prog : LeanIsaProgram) :
    (bytecodeComponent prog).rowOperations.interactions =
      [⟨BytecodePush.toRaw, .push, 1, toElements (⟨var ⟨0⟩, 1, var ⟨2⟩,
          #v[var ⟨3⟩, var ⟨4⟩, var ⟨5⟩, var ⟨6⟩, var ⟨7⟩, var ⟨8⟩, var ⟨9⟩, var ⟨10⟩,
            var ⟨11⟩, var ⟨12⟩, var ⟨13⟩, var ⟨14⟩]⟩ :
          BytecodeMsg (Expression K))⟩,
       ⟨BytecodePull.toRaw, .pull, 1, toElements (⟨var ⟨0⟩, var ⟨1⟩, var ⟨2⟩,
          #v[var ⟨3⟩, var ⟨4⟩, var ⟨5⟩, var ⟨6⟩, var ⟨7⟩, var ⟨8⟩, var ⟨9⟩, var ⟨10⟩,
            var ⟨11⟩, var ⟨12⟩, var ⟨13⟩, var ⟨14⟩]⟩ :
          BytecodeMsg (Expression K))⟩] := by
  have hv : (varFromOffset BytecodeRow 0 : Var BytecodeRow K) = ⟨var ⟨0⟩, var ⟨1⟩, var ⟨2⟩,
      #v[var ⟨3⟩, var ⟨4⟩, var ⟨5⟩, var ⟨6⟩, var ⟨7⟩, var ⟨8⟩, var ⟨9⟩, var ⟨10⟩,
        var ⟨11⟩, var ⟨12⟩, var ⟨13⟩, var ⟨14⟩]⟩ := by
    with_unfolding_all rfl
  simp only [Component.rowOperations, bytecodeComponent, bytecodeTable, circuit_norm]
  simp only [ChannelInteraction.toRaw, pushed, pulled]
  erw [hv]

/-- A table whose row circuit interacts on no channel named `c` sends nothing on `c`, whatever
its rows. -/
theorem filter_eq_nil_of_rowOps (t : Air.Flat.Table K) (c : RawChannel K)
    (h : ∀ i ∈ t.component.rowOperations.interactions, i.channel.name ≠ c.name) :
    t.interactions.filter (·.channel.name = c.name) = [] := by
  rw [List.filter_eq_nil_iff, table_interactions_eq]
  intro i hi
  rw [List.mem_flatMap] at hi
  obtain ⟨r, -, hi⟩ := hi
  rw [List.mem_map] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  exact fun h' ↦ h j hj (of_decide_eq_true h')

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
