/-
  LeanVM.Arithmetization.Tables.MulNative

  The `MUL_NATIVE` table: one Clean component per row, sound and complete for the relation the
  row refines, its bindings to an image together with `execute` of the instruction
  it names.
-/

module

public import LeanVM.Arithmetization.Tables.Basic
public import Clean.Circuit.Formal
public import Clean.Utils.Tactics.CircuitProofStart

@[expose] public section

/-!
# The `MUL_NATIVE` table

At Clean pin `b41c196b`. The columns
are `crates/leanvm_core/src/tables.rs` (`mod arith`, shared with `XOR`, in that order), the
flushes `tables.rs` (`Arith::flushes` with `is_xor = false`), the result coordinates
`tables.rs` (`TOWER_LANES`, `arith_result`; the verifier's
`crates/verifier/src/layout.rs`), all matching specification §7.2
(`doc/leanvm/body/07-instruction-tables.tex`). There is no constraint: the bus
balance is the assertion `[o_C] = [o_A] · [o_B]` (§5, "M3").

**The row** `MulRow` is the column list: `pc, fp`; the operands `o_A, o_B, o_C`; the two read
words `v_A, v_B` as two limbs each; the memory counts `r_A, r_B, r_C`; the bytecode count
`r_bc`. The product is never a column: its limbs ride the third memory read as the four
products over the four limb pairs, `a₁b₁·y²` folded by `y^2 = x·y + 1` into both lanes,

```text
c0 = a0·b0 + a1·b1
c1 = a0·b1 + a1·b0 + g·(a1·b1)
```

(`TOWER_LANES`, each term `g^e·a_j·b_k` for `(j, k, e)`; §7.2's `p_0 + p_2, p_1 + g·p_2`). `mul_limbs` is the
statement that these are the limbs of the product in `E`, and licenses the proofs to read the
result coordinates as `v_A · v_B`.

**The relation** is the `XOR` table's with the product for the sum (see
`LeanVM.Arithmetization.Tables.Xor` for the template): `MulBindings mem r` binds the two
operand words (`readA_eq`, `readB_eq`) to an image; `MulRefines mem r next` is the bindings and
the execution of the instruction the row names, `MUL_NATIVE o_A o_B o_C` (`exec_eq`);
`mul_refines_iff` expands it to the word at `fp·o_C` being the product of the two words in `E`,
and the successor `(g·pc, fp)`. The public description of the operation is the product in `E`;
the circuit's expanded polynomial is `main`'s coordinates alone, tied to it by `mul_limbs`.
`MulSpec r next data` adapts the relation to Clean's prover data and is the table's `Spec`;
`ProverAssumptions r data _ := ∃ next, MulSpec r next data` is the honest prover's row, proved
of the row of any valid execution by `mulRowOf_refines` (`mul_exec_complete`); completeness
discharges the pulls from it through `mul_refines_iff` and `mul_limbs`, the four products
`main` emits being the product's limbs. The table is program-free, as leanVM's is
(`Arithmetization.Channels`).

**The component** `mulTable` pulls the state `(pc, fp)`, pushes and returns the fall-through
successor `(g·pc, fp)`, reads the bytecode entry `(MUL, o_A, o_B, o_C, 0, 0, 0, 0)` at `pc`,
and reads the three cells `fp·o_A`, `fp·o_B`, `fp·o_C` with the third carrying the product.
`Spec` is `MulSpec`; soundness and completeness are as for `XOR`.

**Rows from executions.** `mulRowOf`, `mulRowOf_refines` and `mul_exec_complete` are the `XOR`
statements for this table.

## Wrong readings excluded

* A three-lane or unfolded product is not the tower product: `y · y = x·y + 1`, so the
  `y^2` partial sum folds back into lane `0` and, times `g`, lane `1` (`mul_limbs`, whose proof
  is exactly the fold by `y_sq`); a product without the `g` is that of `y^2 + y + 1`.
* `MulRefines` names the operands and the operand words: a wrong input limb fails the bindings
  even where the result cell happens to hold the product of the image's words.
* The successor is `(g·pc, fp)`; the spare bytecode slots are literal zeros (`decode` rejects
  a nonzero spare slot).
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics

/-! ## The row -/

/-- The `MUL_NATIVE` columns, in the order of `tables.rs`. -/
structure MulRow (F : Type) where
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
  vA : Vector F 2
  /-- The word read at `fp · o_B`, as limbs. -/
  vB : Vector F 2
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
structure MulBindings {κ : ℕ} (mem : MemoryImage κ) (r : MulRow K) : Prop where
  /-- The cell `fp · o_A` holds the row's word `v_A`. -/
  readA_eq : mem.read (r.fp * r.oA) = some (E.ofLimbs r.vA[0] r.vA[1])
  /-- The cell `fp · o_B` holds the row's word `v_B`. -/
  readB_eq : mem.read (r.fp * r.oB) = some (E.ofLimbs r.vB[0] r.vB[1])

/-- The relation a `MUL_NATIVE` row refines: it is bound to the image, and from its registers
the machine executes the instruction it names, `MUL_NATIVE o_A o_B o_C`, to `next`. -/
structure MulRefines {κ : ℕ} (mem : MemoryImage κ) (r : MulRow K) (next : Registers K) : Prop where
  /-- The row is bound to the image. -/
  bindings : MulBindings mem r
  /-- From the row's registers the machine executes `MUL_NATIVE o_A o_B o_C` to `next`. -/
  exec_eq : execute mem ⟨r.pc, r.fp⟩ (.mulNative r.oA r.oB r.oC) = some next

/-- `MulRefines`, expanded: the bindings, the result cell holds the product in `E`, and the
successor is the fall-through `(g·pc, fp)`. -/
theorem mul_refines_iff {κ : ℕ} (mem : MemoryImage κ) (r : MulRow K) (next : Registers K) :
    MulRefines mem r next ↔
      MulBindings mem r ∧
        mem.read (r.fp * r.oC) =
          some (E.ofLimbs r.vA[0] r.vA[1] * E.ofLimbs r.vB[0] r.vB[1]) ∧
        next = Registers.next ⟨r.pc, r.fp⟩ := by
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

/-- The table's `Spec`: the row refines `MulRefines` over the image the prover data names. No
program: the table is program-free (the module docstring). -/
def MulSpec (r : MulRow K) (next : Registers K) (data : ProverData K) : Prop :=
  MulRefines (imageOf data).2 r next

/-- The bytecode tuple of a row is `entry` of the instruction it names, by definition; spelled
once, so that the unifier need not see it through `decode`. -/
private theorem mulNative_entry (a b c : K) :
    #v[Opcode.mulNative.busCode] ++ #v[a, b, c, 0, 0, 0, 0, 0, 0, 0, 0, 0] = busEntry (.mulNative a b
        c) := rfl

/-! ## The table -/

/-- The `MUL_NATIVE` table (specification §7.2; `tables.rs`): state step, bytecode read
of `(MUL, o_A, o_B, o_C, 0, 0, 0, 0)`, the two operand reads, and the result read carrying the
tower product's two lanes. Returns the pushed successor `(g·pc, fp)`. -/
def mulTable : GeneralFormalCircuit K MulRow Registers where
  -- The table's name in leanVM (`TABLES`, `cpu/mod.rs`), unique in the ensemble (Clean keys
  -- the prover data by it).
  name := "MUL"
  main r := do
    let next : Var Registers K := ⟨Expression.const g * r.pc, r.fp⟩
    StatePull.pull ⟨r.pc, r.fp⟩
    StatePush.push next
    bytecodeRead r.pc r.rbc (Expression.const Opcode.mulNative.busCode)
      #v[r.oA, r.oB, r.oC, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    memRead (r.fp * r.oA) r.rA r.vA
    memRead (r.fp * r.oB) r.rB r.vB
    -- `TOWER_LANES` (`tables.rs`), lane by lane, term by term, `(j, k, e)` as
    -- `g^e · v_{A,j} · v_{B,k}`.
    memRead (r.fp * r.oC) r.rC
      #v[r.vA[0] * r.vB[0] + r.vA[1] * r.vB[1],
         r.vA[0] * r.vB[1] + r.vA[1] * r.vB[0] + Expression.const g * (r.vA[1] * r.vB[1])]
    pure next
  -- The push channels: their requirements are vacuous, the obligation is `Spec`.
  channelsWithRequirements := [StatePush.toRaw, MemPush.toRaw, BytecodePush.toRaw]
  requirementsChannelsLawful input offset := by
    -- Without core's `BitVec.reduceNeg` simproc, which misreads `-1 : K` (the field's `-1` is `1`).
    simp only [circuit_norm, memRead, bytecodeRead, -BitVec.reduceNeg]
    tauto
  -- The row refines the relation over the data's image, to the pushed successor.
  Spec := MulSpec
  -- The honest prover's row: written from a valid step, it is bound and executes its
  -- instruction. Proved of the row built from any valid execution by `mulRowOf_refines`; see
  -- `mul_exec_complete`.
  ProverAssumptions r data _ := ∃ next, MulSpec r next data
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    -- The bytecode guarantee, that the tuple decodes, is unused (see `XOR`).
    obtain ⟨-, hA, hB, hC⟩ := h_holds
    obtain ⟨_, _, _, _, _, hvA, hvB, _, _, _, _⟩ := h_input
    subst hvA hvB
    refine (mul_refines_iff _ _ _).mpr ⟨⟨?_, ?_⟩, ?_, rfl⟩
    · simpa only [Vector.getElem_map] using hA
    · simpa only [Vector.getElem_map] using hB
    · simpa only [mul_limbs, Vector.getElem_map] using hC
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    -- The four pull guarantees, from the semantic premise: the tuple `main` emits decodes
    -- (`decode_entry`), and the result read carries the limbs of the product a valid execution
    -- reads (`mul_limbs`).
    obtain ⟨next, h⟩ := h_assumptions
    obtain ⟨⟨hA, hB⟩, hC, -⟩ := (mul_refines_iff _ _ _).mp h
    rw [mul_limbs] at hC
    obtain ⟨_, _, _, _, _, hvA, hvB, _, _, _, _⟩ := h_input
    subst hvA hvB
    simp only [Vector.getElem_map] at hA hB hC ⊢
    exact ⟨⟨_, by rw [mulNative_entry]; exact decode_entry _⟩, hA, hB, hC⟩

/-! ## Rows from executions -/

/-- The row of an execution of `MUL_NATIVE oA oB oC` from `(pc, fp)` over the image `mem`: the
registers, the operands, the two operand words read back from the image, and the counts as
parameters. Noncomputable: it reads the image. -/
noncomputable def mulRowOf {κ : ℕ} (mem : MemoryImage κ) (pc fp oA oB oC rA rB rC rbc : K) :
    MulRow K :=
  ⟨pc, fp, oA, oB, oC, mem.limbsAt (fp * oA), mem.limbsAt (fp * oB), rA, rB, rC, rbc⟩

/-- A valid execution of `MUL_NATIVE oA oB oC` is represented by `mulRowOf`, with any counts:
the honest prover's row refines the relation, which is `ProverAssumptions` over the data. -/
theorem mulRowOf_refines {κ : ℕ} {mem : MemoryImage κ} {pc fp oA oB oC : K} {next : Registers K}
    (hexec : execute mem ⟨pc, fp⟩ (.mulNative oA oB oC) = some next) (rA rB rC rbc : K) :
    MulRefines mem (mulRowOf mem pc fp oA oB oC rA rB rC rbc) next := by
  have h := hexec
  simp only [execute, executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, -⟩ := h
  refine ⟨⟨?_, ?_⟩, hexec⟩
  · show mem.read (fp * oA) = some (E.ofLimbs (mem.limbsAt (fp * oA))[0]
      (mem.limbsAt (fp * oA))[1])
    rw [MemoryImage.ofLimbs_limbsAt ha]; exact ha
  · show mem.read (fp * oB) = some (E.ofLimbs (mem.limbsAt (fp * oB))[0]
      (mem.limbsAt (fp * oB))[1])
    rw [MemoryImage.ofLimbs_limbsAt hb]; exact hb

/-- Every valid `MUL_NATIVE` execution has a satisfying row, from the execution alone: the
constraints of `main` hold of `mulRowOf` in the row environment over the data. -/
theorem mul_exec_complete {data : ProverData K} {pc fp oA oB oC : K} {next : Registers K}
    (hexec : execute (imageOf data).2 ⟨pc, fp⟩ (.mulNative oA oB oC) = some next)
    (rA rB rC rbc : K) :
    ConstraintsHold.Completeness (rowEnv data)
      ((mulTable.main (const (mulRowOf (imageOf data).2 pc fp oA oB oC rA rB rC rbc))).operations
        0) :=
  (mulTable.completeness 0 (rowEnv data) (const _)
    -- No witness slot: the row environment uses the local witnesses vacuously.
    (by simp only [circuit_norm, mulTable, memRead, bytecodeRead, -BitVec.reduceNeg]) _
    ProvableType.eval_const_prover ⟨_, mulRowOf_refines hexec rA rB rC rbc⟩).1

end LeanVM.Arithmetization
