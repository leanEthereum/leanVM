/-
  LeanVM.Arithmetization.Tables.Deref

  The `DEREF` table: one Clean component per row, sound and complete for the relation the row
  refines, its bindings to an image together with `execute` of the instruction it
  names.
-/

module

public import LeanVM.Arithmetization.Tables.Basic
public import Clean.Circuit.Formal
public import Clean.Utils.Tactics.CircuitProofStart
public import Mathlib.Algebra.CharP.Two

@[expose] public section

/-!
# The `DEREF` table

At leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d` and Clean pin `42fe4b26`. The columns
are `crates/leanvm_core/src/tables.rs:591-614` (`mod deref`, in that order), the store coordinates
`tables.rs:621-628` (`deref_store`), the flushes `tables.rs:638-648` (`DerefTable::flushes`),
matching specification §7.4 (`doc/leanvm/body/07-instruction-tables.tex:66-92`). There is no
constraint enforcing Boolean flags. Local soundness instead requires the bytecode pull's
canonical-entry guarantee, whose decoder (`decode`) admits only the three flag pairs. The typed
public program stores `Instr` values; this does not supply a raw-program parser or its
correspondence theorem.

**The row** `DerefRow` is the column list: `pc, fp`; the operands `o₁, o₂, o₃`; the flags
`f_pc, f_fp`; the pointer `p`, a single `K` limb; the local word `v₃` as three limbs; the memory
counts `r₁, r₂, r₃`; the bytecode count `r_bc`. The target word is never a column: its limbs
ride the target read as `(f̄·v₃₀ + f_pc·(g²·pc) + f_fp·fp, f̄·v₃₁, f̄·v₃₂)` with
`f̄ = 1 + f_pc + f_fp`, the flag-selected source of §7.4, which `storeCoords_eval` identifies
with `derefSource` at each of the three flag settings.

**The relation.** `DerefBindings mem r mode` binds the row to an image for a store mode: the
row's flags are the mode's (`flags_eq`, `derefFlags`), the pointer cell `fp·o₁` holds `p` in
`K` (`ptr_eq`), and the local cell `fp·o₃` holds the row's word (`local_eq`). `DerefRefines
mem r next` is, for some mode, the bindings and the execution of the instruction the row names
in that mode, `DEREF o₁ o₂ o₃ mode` (`execute`), the one mode shared by both, which
the flags determine; `deref_refines_iff` expands it, with the same mode: the target cell `p·o₂`
holds `derefSource mode (pc, fp)` of the local word, the return address `g²·pc`, or `fp`, and
the successor is `(g·pc, fp)`. The local cell is read in every mode. `DerefSpec r next data`
adapts the relation to Clean's prover data and is the table's `Spec`; `ProverAssumptions r
data _ := ∃ next, DerefSpec r next data` is the honest prover's row (see
`LeanVM.Arithmetization.Tables.Xor` for the template), proved of the row of any valid
execution by `derefRowOf_refines`. The table is program-free, as leanVM's is
(`Arithmetization.Channels`).

**The component** `derefTable` pulls the state `(pc, fp)`, pushes and returns `(g·pc, fp)`,
reads the bytecode entry `(DRF, o₁, o₂, o₃, f_pc, f_fp, 0, 0)` at `pc`, reads the pointer cell
`fp·o₁` as `(p, 0, 0)`, the local cell `fp·o₃`, and the target cell `p·o₂`, in the order of
§7.4; `Spec` is `DerefSpec`. Soundness reads the instruction the pulled tuple decodes to
through `decode_deref_eq_some_iff`, the one use a table makes of the bytecode
guarantee: the pulled tuple *is* an instruction, so its flag pair is a store mode's (a pair that
is no mode's decodes to nothing, so such a row cannot satisfy the lookup guarantee), and the
target read's coordinates are that mode's source (`storeCoords_eval`). Completeness discharges the four pulls
from the semantic premise through `deref_refines_iff`: the tuple `main` emits decodes
(`decode_entry`), and the target coordinates it emits are the mode's source.

**Rows from executions.** `derefRowOf mem pc fp o₁ o₂ o₃ mode r₁ r₂ r₃ rbc` is the row of an
execution of `DEREF o₁ o₂ o₃ mode` over the image `mem`: the mode's flags, the pointer's low
limb and the local word read back from the image (`MemImage.limbsAt`); `derefRowOf_refines`
proves it refines the relation, and `deref_exec_complete` its acceptance by `main` over the
prover data, from the execution alone.

## Wrong readings excluded

* The pointer read carries literal zeros above its low limb (`memory_k`, `tables.rs:179-181`),
  so a pointer word outside `K` cannot balance the bus; `step` asserts `IsInK p` the same way.
* The local cell is read in every mode, `pc` and `fp` modes included:
  `memRead (fp·o₃)` is unconditional, as is the third read of `execute`, and `DerefBindings`
  binds it in every mode.
* The return address is `g²·pc`, a free `×g²` on the product coordinate (`Prod(FPC, PC, 2)`),
  never `pc + 2`.
* `DerefRefines` names the mode: the flag pair `(1, 1)` is no `derefFlags mode`, so a row
  carrying it fails its bindings at every counter, where the old step-only reading accepted it
  (a counterexample in the tests).
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics

/-! ## The row -/

/-- The `DEREF` columns, in the order of `tables.rs:591-614`. -/
structure DerefRow (F : Type) where
  /-- The program counter. -/
  pc : F
  /-- The frame pointer. -/
  fp : F
  /-- The operand `o₁`, naming the pointer cell. -/
  o1 : F
  /-- The operand `o₂`, the pointer-relative offset of the target. -/
  o2 : F
  /-- The operand `o₃`, naming the local cell. -/
  o3 : F
  /-- The flag `f_pc`. -/
  fpc : F
  /-- The flag `f_fp`. -/
  ffp : F
  /-- The pointer `p`, the low limb of the word at `fp · o₁`. -/
  p : F
  /-- The local word at `fp · o₃`, as limbs. -/
  v3 : Vector F 3
  /-- The read count of the pointer cell. -/
  r1 : F
  /-- The read count of the target cell. -/
  r2 : F
  /-- The read count of the local cell. -/
  r3 : F
  /-- The read count of the bytecode entry at `pc`. -/
  rbc : F
  deriving ProvableStruct

/-! ## The store coordinates -/

/-- The store coordinates evaluate to `derefSource` at each flag setting
(specification §7.4; `tables.rs:621-628`): the local word in `cell` mode, `g²·pc` in `pc` mode,
`fp` in `fp` mode. -/
theorem storeCoords_eval (mode : DerefMode) (pc fp v30 v31 v32 : K) :
    E.ofLimbs
        ((1 + (derefFlags mode).1 + (derefFlags mode).2) * v30 +
          (derefFlags mode).1 * (g ^ 2 * pc) + (derefFlags mode).2 * fp)
        ((1 + (derefFlags mode).1 + (derefFlags mode).2) * v31)
        ((1 + (derefFlags mode).1 + (derefFlags mode).2) * v32) =
      derefSource mode ⟨pc, fp⟩ (E.ofLimbs v30 v31 v32) := by
  cases mode <;>
    simp only [derefFlags, derefSource, ofK_eq_ofLimbs, add_zero, zero_add, one_mul, zero_mul,
      CharTwo.add_self_eq_zero]

/-! ## The relation -/

/-- The row's bindings to an image for a store mode: the flags are the mode's, the pointer cell
holds `p` in `K`, and the local cell holds the row's word. -/
structure DerefBindings {κ : ℕ} (mem : MemImage κ) (r : DerefRow K) (mode : DerefMode) :
    Prop where
  /-- The row's flags are the mode's. -/
  flags_eq : derefFlags mode = (r.fpc, r.ffp)
  /-- The pointer cell `fp · o₁` holds `p`, a word in `K`. -/
  ptr_eq : mem.read (r.fp * r.o1) = some (E.ofLimbs r.p 0 0)
  /-- The local cell `fp · o₃` holds the row's word `v₃`. -/
  local_eq : mem.read (r.fp * r.o3) = some (E.ofLimbs r.v3[0] r.v3[1] r.v3[2])

/-- The relation a `DEREF` row refines: for some store mode, the row is bound to the image and
from its registers the machine executes the instruction it names in that mode,
`DEREF o₁ o₂ o₃ mode`, to `next` (`execute`). One mode for both: the flags determine
it (`flags_eq`), and nothing outside the row fixes it. -/
def DerefRefines {κ : ℕ} (mem : MemImage κ) (r : DerefRow K) (next : Regs K) : Prop :=
  ∃ mode, DerefBindings mem r mode ∧
    execute mem ⟨r.pc, r.fp⟩ (.deref r.o1 r.o2 r.o3 mode) = some next

/-- `DerefRefines`, expanded with the same mode: the bindings, the target cell `p·o₂` holds the
source the mode selects, and the successor is the fall-through `(g·pc, fp)`. -/
theorem deref_refines_iff {κ : ℕ} (mem : MemImage κ) (r : DerefRow K) (next : Regs K) :
    DerefRefines mem r next ↔
      ∃ mode, DerefBindings mem r mode ∧
        mem.read (r.p * r.o2) =
          some (derefSource mode ⟨r.pc, r.fp⟩ (E.ofLimbs r.v3[0] r.v3[1] r.v3[2])) ∧
        next = Regs.next ⟨r.pc, r.fp⟩ := by
  constructor
  · rintro ⟨mode, ⟨hflags, h1, h3⟩, hexec⟩
    refine ⟨mode, ⟨hflags, h1, h3⟩, ?_⟩
    simp only [execute, executeWith, h1, h3, Option.bind_eq_bind, Option.bind_some, guard_bind_eq_some_iff,
      isInK_ofLimbs, true_and, limb_ofLimbs, Matrix.cons_val_zero] at hexec
    cases hc : mem.read (r.p * r.o2) with
    | none => rw [hc] at hexec; exact absurd hexec (by simp)
    | some c =>
      rw [hc, Option.bind_some, guard_bind_eq_some_iff] at hexec
      obtain ⟨rfl, h⟩ := hexec
      simp only [Option.pure_def, Option.some.injEq] at h
      exact ⟨rfl, h.symm⟩
  · rintro ⟨mode, ⟨hflags, h1, h3⟩, h2, rfl⟩
    refine ⟨mode, ⟨hflags, h1, h3⟩, ?_⟩
    simp only [execute, executeWith, h1, h3, h2, Option.bind_eq_bind, Option.bind_some,
      guard_bind_eq_some_iff, isInK_ofLimbs, true_and, limb_ofLimbs, Matrix.cons_val_zero,
      Option.pure_def]

/-! ## The adapter to the prover data -/

/-- The table's `Spec`: the row refines `DerefRefines` over the image the prover data names. No
program: the table is program-free (the module docstring). -/
def DerefSpec (r : DerefRow K) (next : Regs K) (data : ProverData K) : Prop :=
  DerefRefines (imageOf data).2 r next

/-! ## The table -/

/-- The `DEREF` table (specification §7.4; `tables.rs:591-687`): state step, bytecode read of
`(DRF, o₁, o₂, o₃, f_pc, f_fp, 0, 0)`, the pointer read `(p, 0, 0)` at `fp·o₁`, the target read
at `p·o₂` carrying the flag-selected source, and the local read at `fp·o₃`, in the order of
`tables.rs:642-647` and of the Python verifier's `_flushes_deref`, which fixes the order of the
bus blocks. Returns the pushed successor `(g·pc, fp)`. -/
def derefTable : GeneralFormalCircuit K DerefRow Regs where
  main r := do
    let next : Var Regs K := ⟨Expression.const g * r.pc, r.fp⟩
    -- `f̄ = 1 + f_pc + f_fp`: `1` at the three store modes' flags in `cell` mode, `0` otherwise.
    let fbar : Expression K := 1 + r.fpc + r.ffp
    StatePull.pull ⟨r.pc, r.fp⟩
    StatePush.push next
    bytecodeRead r.pc r.rbc (Expression.const Opcode.deref.code)
      #v[r.o1, r.o2, r.o3, r.fpc, r.ffp, 0, 0]
    memRead (r.fp * r.o1) r.r1 #v[r.p, 0, 0]
    memRead (r.p * r.o2) r.r2
      #v[fbar * r.v3[0] + r.fpc * (Expression.const (g ^ 2) * r.pc) + r.ffp * r.fp,
         fbar * r.v3[1], fbar * r.v3[2]]
    memRead (r.fp * r.o3) r.r3 r.v3
    pure next
  -- The push channels: their requirements are vacuous, the obligation is `Spec`.
  channelsWithRequirements := [StatePush.toRaw, MemPush.toRaw, BytecodePush.toRaw]
  requirementsChannelsLawful input offset := by
    -- Without core's `BitVec.reduceNeg` simproc, which misreads `-1 : K` (the field's `-1` is `1`).
    simp only [circuit_norm, memRead, bytecodeRead, -BitVec.reduceNeg]
    tauto
  -- The row refines the relation over the data's image, to the pushed successor.
  Spec := DerefSpec
  -- The honest prover's row: written from a valid step, it is bound and executes its
  -- instruction. Proved of the row built from any valid execution by `derefRowOf_refines`.
  ProverAssumptions r data _ := ∃ next, DerefSpec r next data
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨⟨ins, hdec⟩, h1, h2, h3⟩ := h_holds
    obtain ⟨_, _, _, _, _, _, _, _, hv3, _, _, _, _⟩ := h_input
    subst hv3
    -- The pulled tuple is an instruction (`decode`): `DEREF` with the row's operands, the flags
    -- a store mode's. The one use a table makes of the bytecode guarantee.
    obtain ⟨mode, rfl, hflags⟩ := decode_deref_eq_some_iff.mp hdec
    obtain ⟨h4, h5⟩ := Prod.ext_iff.mp hflags
    subst h4 h5
    simp only [Vector.getElem_map] at h3 h2
    rw [storeCoords_eval] at h2
    refine (deref_refines_iff _ _ _).mpr ⟨mode, ⟨rfl, h1, ?_⟩, ?_, rfl⟩
    · simpa only [Vector.getElem_map] using h3
    · simpa only [Vector.getElem_map] using h2
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    -- The four pull guarantees, from the semantic premise: the tuple `main` emits decodes
    -- (`decode_entry`), and the target read carries the coordinates of the mode's source
    -- (`storeCoords_eval`).
    obtain ⟨next, h⟩ := h_assumptions
    obtain ⟨mode, ⟨hflags, h1, h3⟩, h2, -⟩ := (deref_refines_iff _ _ _).mp h
    obtain ⟨_, _, _, _, _, _, _, _, hv3, _, _, _, _⟩ := h_input
    subst hv3
    obtain ⟨h4, h5⟩ := Prod.ext_iff.mp hflags
    subst h4 h5
    rw [← storeCoords_eval] at h2
    simp only [Vector.getElem_map] at h3 h2 ⊢
    exact ⟨⟨_, decode_entry (.deref _ _ _ mode)⟩, h1, h2, h3⟩

/-! ## Rows from executions -/

/-- The row of an execution of `DEREF o₁ o₂ o₃ mode` from `(pc, fp)` over the image `mem`: the
registers, the operands, the mode's flags, the pointer's low limb and the local word read back
from the image, and the counts as parameters. Noncomputable: it reads the image. -/
noncomputable def derefRowOf {κ : ℕ} (mem : MemImage κ) (pc fp o1 o2 o3 : K) (mode : DerefMode)
    (r1 r2 r3 rbc : K) : DerefRow K :=
  ⟨pc, fp, o1, o2, o3, (derefFlags mode).1, (derefFlags mode).2,
    (mem.limbsAt (fp * o1))[0], mem.limbsAt (fp * o3), r1, r2, r3, rbc⟩

/-- A valid execution of `DEREF o₁ o₂ o₃ mode` is represented by `derefRowOf`, with any counts:
the honest prover's row refines the relation, which is `ProverAssumptions` over the data. -/
theorem derefRowOf_refines {κ : ℕ} {mem : MemImage κ} {pc fp o1 o2 o3 : K} {mode : DerefMode}
    {next : Regs K} (hexec : execute mem ⟨pc, fp⟩ (.deref o1 o2 o3 mode) = some next)
    (r1 r2 r3 rbc : K) :
    DerefRefines mem (derefRowOf mem pc fp o1 o2 o3 mode r1 r2 r3 rbc) next := by
  have h := hexec
  simp only [execute, executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨p, hp, u, hu, v3, hv3, -⟩ := h
  have hin := guard_eq_some hu
  refine ⟨mode, ⟨rfl, ?_, ?_⟩, hexec⟩
  · show mem.read (fp * o1) = some (E.ofLimbs (mem.limbsAt (fp * o1))[0] 0 0)
    rw [MemImage.limbsAt_getElem_zero hp, ofLimbs_of_isInK hin]; exact hp
  · show mem.read (fp * o3) = some (E.ofLimbs (mem.limbsAt (fp * o3))[0]
      (mem.limbsAt (fp * o3))[1] (mem.limbsAt (fp * o3))[2])
    rw [MemImage.ofLimbs_limbsAt hv3]; exact hv3

/-- Every valid `DEREF` execution has a satisfying row, from the execution alone: the
constraints of `main` hold of `derefRowOf` in the row environment over the data. -/
theorem deref_exec_complete {data : ProverData K} {pc fp o1 o2 o3 : K} {mode : DerefMode}
    {next : Regs K} (hexec : execute (imageOf data).2 ⟨pc, fp⟩ (.deref o1 o2 o3 mode) = some next)
    (r1 r2 r3 rbc : K) :
    ConstraintsHold.Completeness (rowEnv data)
      ((derefTable.main
        (const (derefRowOf (imageOf data).2 pc fp o1 o2 o3 mode r1 r2 r3 rbc))).operations 0) :=
  (derefTable.completeness 0 (rowEnv data) (const _)
    -- No witness slot: the row environment uses the local witnesses vacuously.
    (by simp only [circuit_norm, derefTable, memRead, bytecodeRead, -BitVec.reduceNeg]) _
    ProvableType.eval_const_prover ⟨_, derefRowOf_refines hexec r1 r2 r3 rbc⟩).1

end LeanVM.Arithmetization
