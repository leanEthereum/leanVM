/-
  LeanVM.Arithmetization.Tables.Xor

  The `XOR` table: one Clean component per row, sound and complete for the relation the row
  refines, its bindings to an image together with `execute` of the instruction it
  names.
-/

module

public import LeanVM.Arithmetization.Tables.Basic
public import Clean.Circuit.Formal
public import Clean.Utils.Tactics.CircuitProofStart

@[expose] public section

/-!
# The `XOR` table

At leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d` and Clean pin `42fe4b26`. The columns
are `crates/leanvm_core/src/tables.rs:441-461` (`mod arith`, in that order), the flushes
`tables.rs:488-500` (`Arith::flushes` with `is_xor`), the result coordinates `tables.rs:466-478`
(`arith_result`, the lane-wise sum), all matching specification §7.1
(`doc/leanvm/body/07-instruction-tables.tex:9-26`). There is no constraint: the bus balance is
the assertion `[o_C] = [o_A] + [o_B]` (§5, "M3").

**The row** `XorRow` is the column list: `pc, fp`; the operands `o_A, o_B, o_C`; the two read
words `v_A, v_B` as three limbs each; the memory counts `r_A, r_B, r_C`; the bytecode count
`r_bc`. The result word is never a column: its limbs ride the third memory read as the sums
`v_{A,i} + v_{B,i}`. A three-limb column `v` is the word `E.ofLimbs v[0] v[1] v[2]`, as
`MemPull.Guarantees` spells it.

**The relation.** `XorBindings mem r` binds the row to an image, as named facts: `readA_eq`,
`readB_eq`, the operand cells `fp·o_A`, `fp·o_B` hold the row's words. `XorRefines mem r next`
is the bindings together with `exec_eq : execute mem ⟨pc, fp⟩ (.xor o_A o_B o_C) = some next`,
`execute` of the instruction the row names, `XOR o_A o_B o_C`, from the row's
registers to `next`: the relation an `XOR` row refines, stated over the image itself, so that
execution and witness proofs state their obligations over theirs. The program is not in it:
the table is program-free, as leanVM's `XOR` AIR is (its bytecode flush is the constant opcode
and its own operand columns, `tables.rs:147-156`), and which instruction the program holds at
the row's counter is the bus's to bind (`Arithmetization.Channels`, `Soundness.BytecodeChannel`).
`xor_refines_iff` expands it into the opcode's equation, the word at `fp·o_C` is the sum of the
two words in `E` (addition in `E`, whose limbs are bitwise `XOR` in `K`, never integer
addition), and the successor `next = (g·pc, fp)`. Access counts are outside the relation: their
allocation is the bus's (`SatisfiedBy`, `Arithmetization.Soundness`), and a wrong count does
not falsify the opcode's specification.

**The adapter.** `XorSpec r next data := XorRefines (imageOf data).2 r next` reads the image
off Clean's prover data (`imageOf`) and is the table's `Spec`; constructing and relating
`ProverData` is this one explicit step. The row's pull guarantees have no name of their own:
they are what Clean's `circuit_proof_start` hands soundness as hypotheses and asks of
completeness as goals, and `xor_refines_iff` with `add_limbs` is their semantic
reading (the result read carries the sum's limbs).

**The component** `xorTable` pulls the state `(pc, fp)`, pushes and returns the fall-through
successor `(g·pc, fp)`, reads the bytecode entry `(XOR, o_A, o_B, o_C, 0, 0, 0, 0)` at `pc`,
and reads the three cells `fp·o_A`, `fp·o_B`, `fp·o_C` with the third carrying the sum. `Spec`
is `XorSpec`.

**Soundness** assumes the guarantees of the four pulls (memory reads are the image's words, the
bytecode entry decodes to an instruction, which for the tuple `main` emits is `XOR o_A o_B o_C`
by `decode_entry`) and concludes `XorSpec`: the bindings are exactly what the memory
pulls guarantee, and the execution follows by the arm of `execute`; the requirements of the
three pushes are vacuous, since the push channels guarantee nothing (what a push must
satisfy is this `Spec`).

**Completeness** takes `ProverAssumptions r data _ := ∃ next, XorSpec r next data`: the row is
an honest row, one an honest prover wrote from a valid step of the execution it proves, so it
is bound to the image and the machine executes its instruction from its registers. That is the
honest-prover precondition Clean's completeness is relative to, and nothing above this file
assumes it: `xorRowOf_refines` proves it of the row built from any valid `XOR` execution, so
`xor_exec_complete` states completeness from the execution alone. What completeness then
proves is the encoding: the tuple `main` emits decodes (`decode_entry`), and the
coordinates it emits for the result read are the limbs of the word a valid execution reads
(`add_limbs`, through `xor_refines_iff`); a mistranscribed lane would fail here. For a table
without constraints the constraints are the pull guarantees and nothing else, which is why the
proof is a substitution once `xor_refines_iff` and `add_limbs` have done theirs.

**Rows from executions.** `xorRowOf mem pc fp oA oB oC rA rB rC rbc` is the row of an
execution over the image `mem`: the registers and the operands, the two operand words read back
from the image (`MemImage.limbsAt`), and the counts as parameters. `xorRowOf_refines`
says it refines `XorRefines mem` whenever `XOR oA oB oC` executes from `(pc, fp)`, and
`xor_exec_complete` pushes it through `completeness` over the prover data: every valid `XOR`
execution has a satisfying row, its constraints holding in the row environment `rowEnv data`.
A step of a program that fetches `XOR oA oB oC` is such an execution
(`execute_of_step`). The builder is noncomputable, since `MemImage.read` is; an executable,
data-aware generator would be proved against these theorems.

This is all a table file states. Facts about its bytecode tuple are
`Arithmetization.Bytecode`'s (`decode_entry`), the successor `main` returns is fixed by
`xor_refines_iff` under `soundness`, and one-line corollaries of `soundness` and
`completeness` are left to their consumers.

## Wrong readings excluded

* The result is `v_A + v_B` limb by limb, in `E` (`add_limbs`): a row whose result read
  carries any other word fails `XorRefines`, since `step` compares the word read at `fp·o_C`
  with the sum (the mutated row in the tests).
* `XorRefines` names the row's operands and words, not only its registers: an `XOR` row with an
  operand word that is not the image's fails its bindings even where `execute` succeeds (a
  counterexample in the tests). Which instruction the program holds at the row's
  counter is not the table's to check, as it is not leanVM's `XOR` AIR's: a row naming an
  instruction the program does not hold there is rejected by the bytecode pair's balance
  (`Soundness.BytecodeChannel`), never locally (the tests state that rejection at the block).
* The successor is `(g·pc, fp)`, never `(pc + 1, fp)`.
* Every bytecode coordinate is explicit, the four spare slots as literal zeros
  (`decode` rejects a nonzero spare slot).
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics

/-! ## The row -/

/-- The `XOR` columns, in the order of `tables.rs:441-461`. -/
structure XorRow (F : Type) where
  /-- The program counter. -/
  pc : F
  /-- The frame pointer. -/
  fp : F
  /-- The operand `o_A`. -/
  oA : F
  /-- The operand `o_B`. -/
  oB : F
  /-- The operand `o_C`. -/
  oC : F
  /-- The word read at `fp · o_A`, as limbs. -/
  vA : Vector F 3
  /-- The word read at `fp · o_B`, as limbs. -/
  vB : Vector F 3
  /-- The read count of the cell `fp · o_A`. -/
  rA : F
  /-- The read count of the cell `fp · o_B`. -/
  rB : F
  /-- The read count of the cell `fp · o_C`. -/
  rC : F
  /-- The read count of the bytecode entry at `pc`. -/
  rbc : F
  deriving ProvableStruct

/-! ## The relation -/

/-- The row's bindings to an image: the operand cells hold the row's words. -/
structure XorBindings {κ : ℕ} (mem : MemImage κ) (r : XorRow K) : Prop where
  /-- The cell `fp · o_A` holds the row's word `v_A`. -/
  readA_eq : mem.read (r.fp * r.oA) = some (E.ofLimbs r.vA[0] r.vA[1] r.vA[2])
  /-- The cell `fp · o_B` holds the row's word `v_B`. -/
  readB_eq : mem.read (r.fp * r.oB) = some (E.ofLimbs r.vB[0] r.vB[1] r.vB[2])

/-- The relation an `XOR` row refines: it is bound to the image, and from its registers the
machine executes the instruction it names, `XOR o_A o_B o_C`, to `next` (`execute`).
-/
structure XorRefines {κ : ℕ} (mem : MemImage κ) (r : XorRow K) (next : Regs K) : Prop where
  /-- The row is bound to the image. -/
  bindings : XorBindings mem r
  /-- From the row's registers the machine executes `XOR o_A o_B o_C` to `next`. -/
  exec_eq : execute mem ⟨r.pc, r.fp⟩ (.xor r.oA r.oB r.oC) = some next

/-- `XorRefines`, expanded: the bindings, the result cell holds the sum in `E`, and the
successor is the fall-through `(g·pc, fp)`. -/
theorem xor_refines_iff {κ : ℕ} (mem : MemImage κ) (r : XorRow K) (next : Regs K) :
    XorRefines mem r next ↔
      XorBindings mem r ∧
        mem.read (r.fp * r.oC) =
          some (E.ofLimbs r.vA[0] r.vA[1] r.vA[2] + E.ofLimbs r.vB[0] r.vB[1] r.vB[2]) ∧
        next = Regs.next ⟨r.pc, r.fp⟩ := by
  constructor
  · rintro ⟨⟨hA, hB⟩, hexec⟩
    refine ⟨⟨hA, hB⟩, ?_⟩
    simp only [execute, executeWith, hA, hB, Option.bind_eq_bind, Option.bind_some] at hexec
    cases hc : mem.read (r.fp * r.oC) with
    | none => rw [hc] at hexec; exact absurd hexec (by simp)
    | some c =>
      rw [hc, Option.bind_some, guard_bind_eq_some_iff] at hexec
      obtain ⟨rfl, h⟩ := hexec
      simp only [Option.pure_def, Option.some.injEq] at h
      exact ⟨rfl, h.symm⟩
  · rintro ⟨⟨hA, hB⟩, hC, rfl⟩
    refine ⟨⟨hA, hB⟩, ?_⟩
    simp only [execute, executeWith, hA, hB, hC, Option.bind_eq_bind, Option.bind_some,
      guard_bind_eq_some_iff, Option.pure_def, true_and]

/-! ## The adapter to the prover data -/

/-- The table's `Spec`: the row refines `XorRefines` over the image the prover data names
(`imageOf`). No program: the table is program-free (the module docstring). -/
def XorSpec (r : XorRow K) (next : Regs K) (data : ProverData K) : Prop :=
  XorRefines (imageOf data).2 r next

/-! ## The table -/

/-- The `XOR` table (specification §7.1; `tables.rs:441-526`): state step, bytecode read of
`(XOR, o_A, o_B, o_C, 0, 0, 0, 0)`, the two operand reads, and the result read carrying the
limb-wise sum. Returns the pushed successor `(g·pc, fp)`. -/
def xorTable : GeneralFormalCircuit K XorRow Regs where
  main r := do
    let next : Var Regs K := ⟨Expression.const g * r.pc, r.fp⟩
    StatePull.pull ⟨r.pc, r.fp⟩
    StatePush.push next
    bytecodeRead r.pc r.rbc (Expression.const Opcode.xor.code) #v[r.oA, r.oB, r.oC, 0, 0, 0, 0]
    memRead (r.fp * r.oA) r.rA r.vA
    memRead (r.fp * r.oB) r.rB r.vB
    memRead (r.fp * r.oC) r.rC #v[r.vA[0] + r.vB[0], r.vA[1] + r.vB[1], r.vA[2] + r.vB[2]]
    pure next
  -- The push channels: their requirements are vacuous, the obligation is `Spec`.
  channelsWithRequirements := [StatePush.toRaw, MemPush.toRaw, BytecodePush.toRaw]
  requirementsChannelsLawful input offset := by
    -- Clean's default tactic decides channel equalities through `Channel.toRaw_ext_iff`, whose
    -- `-1 : K` core's `BitVec.reduceNeg` simproc then rewrites as the two's-complement word,
    -- which the kernel rejects (the field's `-1` is `1`); neither is needed here.
    simp only [circuit_norm, memRead, bytecodeRead, -BitVec.reduceNeg]
    tauto
  -- The row refines the relation over the data's image, to the pushed successor.
  Spec := XorSpec
  -- The honest prover's row: written from a valid step, it is bound and executes its
  -- instruction. Proved of the row built from any valid execution by `xorRowOf_refines`; see
  -- `xor_exec_complete`.
  ProverAssumptions r data _ := ∃ next, XorSpec r next data
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    -- The bytecode guarantee, that the tuple decodes, is unused: the tuple `main` emits is
    -- `XOR`'s entry by construction, and the program is the bus's (`Soundness.BytecodeChannel`).
    obtain ⟨-, hA, hB, hC⟩ := h_holds
    obtain ⟨_, _, _, _, _, hvA, hvB, _, _, _, _⟩ := h_input
    subst hvA hvB
    refine (xor_refines_iff _ _ _).mpr ⟨⟨?_, ?_⟩, ?_, rfl⟩
    · simpa only [Vector.getElem_map] using hA
    · simpa only [Vector.getElem_map] using hB
    · simpa only [add_limbs, Vector.getElem_map] using hC
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    -- The four pull guarantees, from the semantic premise: the tuple `main` emits decodes
    -- (`decode_entry`), and the result read carries the limbs of the sum a valid execution reads
    -- (`add_limbs`).
    obtain ⟨next, h⟩ := h_assumptions
    obtain ⟨⟨hA, hB⟩, hC, -⟩ := (xor_refines_iff _ _ _).mp h
    rw [add_limbs] at hC
    obtain ⟨_, _, _, _, _, hvA, hvB, _, _, _, _⟩ := h_input
    subst hvA hvB
    simp only [Vector.getElem_map] at hA hB hC ⊢
    exact ⟨⟨_, decode_entry (.xor _ _ _)⟩, hA, hB, hC⟩

/-! ## Rows from executions -/

/-- The row of an execution of `XOR oA oB oC` from `(pc, fp)` over the image `mem`: the
registers, the operands, the two operand words read back from the image, and the counts as
parameters. Noncomputable: it reads the image. -/
noncomputable def xorRowOf {κ : ℕ} (mem : MemImage κ) (pc fp oA oB oC rA rB rC rbc : K) :
    XorRow K :=
  ⟨pc, fp, oA, oB, oC, mem.limbsAt (fp * oA), mem.limbsAt (fp * oB), rA, rB, rC, rbc⟩

/-- A valid execution of `XOR oA oB oC` is represented by `xorRowOf`, with any counts: the
honest prover's row refines the relation, which is `ProverAssumptions` over the data. -/
theorem xorRowOf_refines {κ : ℕ} {mem : MemImage κ} {pc fp oA oB oC : K} {next : Regs K}
    (hexec : execute mem ⟨pc, fp⟩ (.xor oA oB oC) = some next) (rA rB rC rbc : K) :
    XorRefines mem (xorRowOf mem pc fp oA oB oC rA rB rC rbc) next := by
  have h := hexec
  simp only [execute, executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, -⟩ := h
  refine ⟨⟨?_, ?_⟩, hexec⟩
  · show mem.read (fp * oA) = some (E.ofLimbs (mem.limbsAt (fp * oA))[0]
      (mem.limbsAt (fp * oA))[1] (mem.limbsAt (fp * oA))[2])
    rw [MemImage.ofLimbs_limbsAt ha]; exact ha
  · show mem.read (fp * oB) = some (E.ofLimbs (mem.limbsAt (fp * oB))[0]
      (mem.limbsAt (fp * oB))[1] (mem.limbsAt (fp * oB))[2])
    rw [MemImage.ofLimbs_limbsAt hb]; exact hb

/-- Every valid `XOR` execution has a satisfying row, from the execution alone: the constraints
of `main` hold of `xorRowOf` in the row environment over the data. A step of a program that
fetches `XOR oA oB oC` is such an execution (`execute_of_step`). -/
theorem xor_exec_complete {data : ProverData K} {pc fp oA oB oC : K} {next : Regs K}
    (hexec : execute (imageOf data).2 ⟨pc, fp⟩ (.xor oA oB oC) = some next) (rA rB rC rbc : K) :
    ConstraintsHold.Completeness (rowEnv data)
      ((xorTable.main (const (xorRowOf (imageOf data).2 pc fp oA oB oC rA rB rC rbc))).operations
        0) :=
  (xorTable.completeness 0 (rowEnv data) (const _)
    -- No witness slot: the row environment uses the local witnesses vacuously.
    (by simp only [circuit_norm, xorTable, memRead, bytecodeRead, -BitVec.reduceNeg]) _
    ProvableType.eval_const_prover ⟨_, xorRowOf_refines hexec rA rB rC rbc⟩).1

end LeanVM.Arithmetization
