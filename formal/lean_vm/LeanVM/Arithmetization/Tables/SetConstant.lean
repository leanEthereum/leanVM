/-
  LeanVM.Arithmetization.Tables.SetConstant

  The `SET_CONSTANT` table: one Clean component per row, sound and complete for the relation
  the row refines, `execute` of the instruction it names.
-/

module

public import LeanVM.Arithmetization.Tables.Basic
public import Clean.Circuit.Formal
public import Clean.Utils.Tactics.CircuitProofStart

@[expose] public section

/-!
# The `SET_CONSTANT` table

At leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d` and Clean pin `42fe4b26`. The columns
are `crates/leanvm_core/src/tables.rs:532-543` (`mod set`, in that order) and the flushes
`tables.rs:553-566` (`SetTable::flushes`), matching specification §7.3
(`doc/leanvm/body/07-instruction-tables.tex:52-64`). There is no constraint.

**The row** `SetRow` is the column list: `pc, fp`; the operand `o`; the immediate `k` as three
limbs (`K_LO, K_HI, K_TOP`, the bytecode's spare slots); the memory count `r`; the bytecode
count `r_bc`.

**The relation.** `SetRefines mem r next` is one fact, `exec_eq`: from the row's registers the
machine executes the instruction the row names, `SET_CONSTANT o k` with the row's immediate
`E.ofLimbs k[0] k[1] k[2]`, all three limbs, to `next`. There is no separate binding: the only
cell read is the one `execute` checks against the immediate, and the immediate is the row's
own, so a `SetBindings` would be empty (the other tables bind their input words). The table is
program-free, as leanVM's is (`Arithmetization.Channels`). `set_refines_iff` expands it: the
cell `fp·o` holds the immediate and the successor is `(g·pc, fp)` (see
`LeanVM.Arithmetization.Tables.Xor` for the template). `SetSpec r next data` adapts the
relation to Clean's prover data and is the table's `Spec`; `ProverAssumptions r data _ :=
∃ next, SetSpec r next data` is the honest prover's row, proved of the row of any valid
execution by `setRowOf_refines` (`set_exec_complete`); completeness discharges the two pulls
from it through `set_refines_iff`, the tuple `main` emits decoding to the instruction the row
names (`decode_entry`).

**The component** `setTable` pulls the state `(pc, fp)`, pushes and returns the fall-through
successor `(g·pc, fp)`, reads the bytecode entry `(SET, o, k₀, k₁, k₂, 0, 0, 0)` at `pc`, and
reads the cell `fp·o` carrying the immediate. `Spec` is `SetSpec`.

**Rows from executions.** `setRowOf pc fp o k r rbc` is the row of an execution of
`SET_CONSTANT o k`: the immediate's limbs are the instruction's, so the builder reads nothing
back and is computable; `setRowOf_refines` and `set_exec_complete` are the `XOR` statements.

## Wrong readings excluded

* The immediate's three lanes are bytecode coordinates `4, 5, 6` of the entry, the slots
  `DEREF` uses for `o₃, f_pc, f_fp` (`entry`).
* The word read at `fp·o` is the immediate itself, all three limbs: a row whose cell holds any
  other word fails `SetRefines` (the mutated row in the tests). A row whose immediate is not the
  program's at its counter is the bus's to reject (`Soundness.BytecodeChannel`), as it is for
  leanVM's `SET` AIR, never this table's.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics

/-! ## The row -/

/-- The `SET_CONSTANT` columns, in the order of `tables.rs:532-543`. -/
structure SetRow (F : Type) where
  /-- The program counter. -/
  pc : F
  /-- The frame pointer. -/
  fp : F
  /-- The operand `o`. -/
  o : F
  /-- The immediate `k = k₀ + k₁·y + k₂·y²`, as limbs. -/
  k : Vector F 3
  /-- The read count of the cell `fp · o`. -/
  r : F
  /-- The read count of the bytecode entry at `pc`. -/
  rbc : F
  deriving ProvableStruct

/-! ## The relation -/

/-- The relation a `SET_CONSTANT` row refines: from its registers the machine executes the
instruction it names, `SET_CONSTANT o k` with the row's immediate, to `next` (`execute`).
-/
structure SetRefines {κ : ℕ} (mem : MemImage κ) (r : SetRow K) (next : Regs K) : Prop where
  /-- From the row's registers the machine executes `SET_CONSTANT o k` to `next`. -/
  exec_eq :
    execute mem ⟨r.pc, r.fp⟩ (.setConstant r.o (E.ofLimbs r.k[0] r.k[1] r.k[2])) = some next

/-- `SetRefines`, expanded: the cell `fp·o` holds the immediate, and the successor is the
fall-through `(g·pc, fp)`. -/
theorem set_refines_iff {κ : ℕ} (mem : MemImage κ) (r : SetRow K) (next : Regs K) :
    SetRefines mem r next ↔
      mem.read (r.fp * r.o) = some (E.ofLimbs r.k[0] r.k[1] r.k[2]) ∧
        next = Regs.next ⟨r.pc, r.fp⟩ := by
  constructor
  · rintro ⟨hexec⟩
    simp only [execute, executeWith, Option.bind_eq_bind] at hexec
    cases hc : mem.read (r.fp * r.o) with
    | none => rw [hc] at hexec; exact absurd hexec (by simp)
    | some c =>
      rw [hc, Option.bind_some, guard_bind_eq_some_iff] at hexec
      obtain ⟨rfl, h⟩ := hexec
      simp only [Option.pure_def, Option.some.injEq] at h
      exact ⟨rfl, h.symm⟩
  · rintro ⟨hk, rfl⟩
    refine ⟨?_⟩
    simp only [execute, executeWith, hk, Option.bind_eq_bind, Option.bind_some, guard_bind_eq_some_iff,
      Option.pure_def, true_and]

/-! ## The adapter to the prover data -/

/-- The table's `Spec`: the row refines `SetRefines` over the image the prover data names. No
program: the table is program-free (the module docstring). -/
def SetSpec (r : SetRow K) (next : Regs K) (data : ProverData K) : Prop :=
  SetRefines (imageOf data).2 r next

/-! ## The table -/

/-- The `SET_CONSTANT` table (specification §7.3; `tables.rs:532-585`): state step, bytecode
read of `(SET, o, k₀, k₁, k₂, 0, 0, 0)`, and the read of `fp·o` carrying the immediate. Returns
the pushed successor `(g·pc, fp)`. -/
def setTable : GeneralFormalCircuit K SetRow Regs where
  main r := do
    let next : Var Regs K := ⟨Expression.const g * r.pc, r.fp⟩
    StatePull.pull ⟨r.pc, r.fp⟩
    StatePush.push next
    bytecodeRead r.pc r.rbc (Expression.const Opcode.setConstant.code)
      #v[r.o, r.k[0], r.k[1], r.k[2], 0, 0, 0]
    memRead (r.fp * r.o) r.r r.k
    pure next
  -- The push channels: their requirements are vacuous, the obligation is `Spec`.
  channelsWithRequirements := [StatePush.toRaw, MemPush.toRaw, BytecodePush.toRaw]
  requirementsChannelsLawful input offset := by
    -- Without core's `BitVec.reduceNeg` simproc, which misreads `-1 : K` (the field's `-1` is `1`).
    simp only [circuit_norm, memRead, bytecodeRead, -BitVec.reduceNeg]
    tauto
  -- The row refines the relation over the data's image, to the pushed successor.
  Spec := SetSpec
  -- The honest prover's row: written from a valid step, it executes its instruction. Proved of
  -- the row built from any valid execution by `setRowOf_refines`; see `set_exec_complete`.
  ProverAssumptions r data _ := ∃ next, SetSpec r next data
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    -- The bytecode guarantee, that the tuple decodes, is unused (see `XOR`).
    obtain ⟨-, hk⟩ := h_holds
    obtain ⟨_, _, _, hvk, _, _⟩ := h_input
    subst hvk
    refine (set_refines_iff _ _ _).mpr ⟨?_, rfl⟩
    simpa only [Vector.getElem_map] using hk
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    -- The two pull guarantees, from the semantic premise: the tuple `main` emits decodes
    -- (`decode_entry`).
    obtain ⟨next, h⟩ := h_assumptions
    obtain ⟨hk, -⟩ := (set_refines_iff _ _ _).mp h
    obtain ⟨_, _, _, hvk, _, _⟩ := h_input
    subst hvk
    simp only [Vector.getElem_map] at hk ⊢
    exact ⟨⟨_, decode_entry (.setConstant _ (E.ofLimbs _ _ _))⟩, hk⟩

/-! ## Rows from executions -/

/-- The row of an execution of `SET_CONSTANT o k` from `(pc, fp)`: the registers, the operand,
the immediate's limbs, and the counts as parameters. -/
def setRowOf (pc fp o : K) (k : E) (rc rbc : K) : SetRow K :=
  ⟨pc, fp, o, #v[k.limb 0, k.limb 1, k.limb 2], rc, rbc⟩

/-- A valid execution of `SET_CONSTANT o k` is represented by `setRowOf`, with any counts: the
honest prover's row refines the relation, which is `ProverAssumptions` over the data. -/
theorem setRowOf_refines {κ : ℕ} {mem : MemImage κ} {pc fp o : K} {k : E} {next : Regs K}
    (hexec : execute mem ⟨pc, fp⟩ (.setConstant o k) = some next) (rc rbc : K) :
    SetRefines mem (setRowOf pc fp o k rc rbc) next :=
  ⟨by
    show execute mem ⟨pc, fp⟩ (.setConstant o (E.ofLimbs (k.limb 0) (k.limb 1) (k.limb 2))) =
      some next
    rw [ofLimbs_limb]; exact hexec⟩

/-- Every valid `SET_CONSTANT` execution has a satisfying row, from the execution alone: the
constraints of `main` hold of `setRowOf` in the row environment over the data. -/
theorem set_exec_complete {data : ProverData K} {pc fp o : K} {k : E} {next : Regs K}
    (hexec : execute (imageOf data).2 ⟨pc, fp⟩ (.setConstant o k) = some next) (rc rbc : K) :
    ConstraintsHold.Completeness (rowEnv data)
      ((setTable.main (const (setRowOf pc fp o k rc rbc))).operations 0) :=
  (setTable.completeness 0 (rowEnv data) (const _)
    -- No witness slot: the row environment uses the local witnesses vacuously.
    (by simp only [circuit_norm, setTable, memRead, bytecodeRead, -BitVec.reduceNeg]) _
    ProvableType.eval_const_prover ⟨_, setRowOf_refines hexec rc rbc⟩).1

end LeanVM.Arithmetization
