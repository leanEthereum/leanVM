/-
  LeanVM.Arithmetization.Tables.Jump

  The `JUMP` table: one Clean component per row, sound and complete for the relation the row
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
# The `JUMP` table

At leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d` and Clean pin `42fe4b26`. The columns are
`crates/leanvm_core/src/tables.rs:693-717` (`mod jump`, in that order), the two identities
`tables.rs:70-78` (`jump_identity` with `quadratic = false`; `true` selects their degree-2 parts),
the flushes `tables.rs:736-756` (`JumpTable::flushes`), matching specification §7.5
(`doc/leanvm/body/07-instruction-tables.tex:94-112`).

**The row** `JumpRow` is the column list: `pc, fp`; the operands `o_c, o_d, o_f`; the condition
`v_cond`, the destination `v_pc` and the frame `v_fp`, each a single `K` limb; the memory counts
`r_c, r_d, r_f`; the bytecode count `r_bc`. The inverse `w` and the taken indicator `b` are
local witnesses of the component (`tables.rs:711-715`, "local witness columns"): the honest
prover sets `w = v_cond⁻¹` when `v_cond ≠ 0` and `0` otherwise, and `b = [v_cond ≠ 0]`.

**The constraints** are the two residuals `b + v_cond·w = 0` and `v_cond·(b + 1) = 0`. Together
they force `b = [v_cond ≠ 0]` (`flags_sound`): with `v_cond = 0` the first gives `b = 0`; with
`v_cond ≠ 0` the second gives `b = 1`. Booleanity of `b` alone would accept `b = 1` with
`v_cond = 0` and a wrong successor. The honest witnesses satisfy
both (`flags_complete`).

**The relation.** `JumpBindings mem r` binds the row to an image: the three cells hold the `K`
words `v_cond`, `v_pc`, `v_fp` (`cond_eq`, `dest_eq`, `frame_eq`), taken or not. `JumpRefines
mem r next` is the bindings and the execution of the instruction the row names, `JUMP o_c o_d
o_f` (`exec_eq`, `execute`); `jump_refines_iff` expands it: the successor is
`(v_pc, v_fp)` when `v_cond ≠ 0` and `(g·pc, fp)` otherwise, so the bindings alone make a
successor exist. `JumpSpec r next data` adapts the relation to Clean's prover data and is the
table's `Spec`; `ProverAssumptions r data _ := ∃ next, JumpSpec r next data` is the honest
prover's row (see `LeanVM.Arithmetization.Tables.Xor` for the template), proved of the row
of any valid execution by `jumpRowOf_refines` (`jump_exec_complete`); completeness discharges
the four pulls from its bindings and the two residuals from the honest witnesses
(`flags_complete`). The relation does not mention `w`: with `v_cond = 0` the residuals accept
every `w`, and the honest generator's `0` is one satisfying assignment among all of them. The
table is program-free, as leanVM's is (`Arithmetization.Channels`).

**The component** `jumpTable` pulls the state `(pc, fp)`, pushes and returns the derived
successor `(b·v_pc + b·(g·pc) + g·pc, b·v_fp + b·fp + fp)`, in characteristic two the selection
of `(v_pc, v_fp)` when `b = 1` and of `(g·pc, fp)` when `b = 0`; reads the bytecode entry
`(JMP, o_c, o_d, o_f, 0, 0, 0, 0)` at `pc`; and reads the three cells `fp·o_c`, `fp·o_d`,
`fp·o_f` as single-limb words `(v, 0, 0)`. `Spec` is `JumpSpec`: the successor is a function of
the witness `b`, which is why the table returns it rather than naming it in `Spec` from the
row; soundness reads `b` off the residuals (`flags_sound`), and leaves the bytecode pull's
guarantee unused, the tuple `main` emits being `JUMP o_c o_d o_f`'s entry by construction
(`decode_entry`, in completeness).

**The witness discipline.** `jump_env_iff` says exactly which prover environments use the two
local witnesses: slot `offset` is the honest inverse and slot `offset + 1` the honest
indicator of the row's condition. `jumpEnv data r` is that environment for a row over its
data, in which `jump_exec_complete` pushes the row of any valid execution through
`completeness`. Clean's array generator `Circuit.witgen` computes the same two values (the
tests run it), but its environment carries no data, so the data-carrying environment is
`jumpEnv`, whose witness discipline is the theorem.

**Rows from executions.** `jumpRowOf mem pc fp o_c o_d o_f r_c r_d r_f r_bc` reads the three
low limbs back from the image (`MemImage.limbsAt`); `jumpRowOf_refines` proves it refines the
relation, and `jump_exec_complete` its acceptance by `main` in `jumpEnv`, witnesses included,
from the execution alone.

## Wrong readings excluded

* The three memory reads carry literal zeros above the low limb, so the condition, destination
  and frame words are in `K` whether or not the branch is taken, as `step` asserts.
* `b·(b + 1) = 0` is not the constraint: `flags_sound` needs both
  residuals, and `b = 1` at `v_cond = 0` fails the first (`flags_sound`, in the tests).
* The successor is a degree-two coordinate of the state push, not a column: there is no
  `next_pc` column to constrain.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics

/-! ## The row -/

/-- The `JUMP` columns, in the order of `tables.rs:693-717`; the witnesses `w` and `b` are
local to the component. -/
structure JumpRow (F : Type) where
  /-- The program counter. -/
  pc : F
  /-- The frame pointer. -/
  fp : F
  /-- The operand `o_c`, naming the condition cell. -/
  oc : F
  /-- The operand `o_d`, naming the destination cell. -/
  od : F
  /-- The operand `o_f`, naming the frame cell. -/
  of : F
  /-- The condition `v_cond`, the low limb of the word at `fp · o_c`. -/
  vcond : F
  /-- The destination `v_pc`, the low limb of the word at `fp · o_d`. -/
  vpc : F
  /-- The frame `v_fp`, the low limb of the word at `fp · o_f`. -/
  vfp : F
  /-- The read count of the condition cell. -/
  rc : F
  /-- The read count of the destination cell. -/
  rd : F
  /-- The read count of the frame cell. -/
  rf : F
  /-- The read count of the bytecode entry at `pc`. -/
  rbc : F
  deriving ProvableStruct

/-! ## The residuals -/

/-- The two residuals force the indicator: `b = [c ≠ 0]` (specification §7.5). -/
theorem flags_sound {c w b : K} (h1 : b + c * w = 0) (h2 : c * (b + 1) = 0) :
    b = if c = 0 then 0 else 1 := by
  split_ifs with hc
  · subst hc
    rwa [zero_mul, add_zero] at h1
  · exact CharTwo.add_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hc)

/-- The honest witnesses satisfy the two residuals: `w = c⁻¹` (or `0`) and `b = [c ≠ 0]`. -/
theorem flags_complete (c : K) :
    (if c = 0 then 0 else 1) + c * (if c = 0 then 0 else c⁻¹) = 0 ∧
      c * ((if c = 0 then 0 else 1) + 1) = 0 := by
  split_ifs with hc
  · subst hc
    exact ⟨by rw [zero_mul, add_zero], by rw [zero_mul]⟩
  · exact ⟨by rw [mul_inv_cancel₀ hc, CharTwo.add_self_eq_zero],
      by rw [CharTwo.add_self_eq_zero, mul_zero]⟩

/-! ## The relation -/

/-- The row's bindings to an image: the three cells hold the row's `K` words. -/
structure JumpBindings {κ : ℕ} (mem : MemImage κ) (r : JumpRow K) : Prop where
  /-- The condition cell `fp · o_c` holds `v_cond`, a word in `K`. -/
  cond_eq : mem.read (r.fp * r.oc) = some (E.ofLimbs r.vcond 0 0)
  /-- The destination cell `fp · o_d` holds `v_pc`, a word in `K`. -/
  dest_eq : mem.read (r.fp * r.od) = some (E.ofLimbs r.vpc 0 0)
  /-- The frame cell `fp · o_f` holds `v_fp`, a word in `K`. -/
  frame_eq : mem.read (r.fp * r.of) = some (E.ofLimbs r.vfp 0 0)

/-- The relation a `JUMP` row refines: it is bound to the image, and from its registers the
machine executes the instruction it names, `JUMP o_c o_d o_f`, to `next` (`execute`).
-/
structure JumpRefines {κ : ℕ} (mem : MemImage κ) (r : JumpRow K) (next : Regs K) : Prop where
  /-- The row is bound to the image. -/
  bindings : JumpBindings mem r
  /-- From the row's registers the machine executes `JUMP o_c o_d o_f` to `next`. -/
  exec_eq : execute mem ⟨r.pc, r.fp⟩ (.jump r.oc r.od r.of) = some next

/-- `JumpRefines`, expanded: the bindings, and the successor is `(v_pc, v_fp)` when the
condition is nonzero and the fall-through `(g·pc, fp)` otherwise. -/
theorem jump_refines_iff {κ : ℕ} (mem : MemImage κ) (r : JumpRow K) (next : Regs K) :
    JumpRefines mem r next ↔
      JumpBindings mem r ∧
        next = if r.vcond = 0 then Regs.next ⟨r.pc, r.fp⟩ else ⟨r.vpc, r.vfp⟩ := by
  constructor
  · rintro ⟨⟨hc, hd, hf⟩, hexec⟩
    refine ⟨⟨hc, hd, hf⟩, ?_⟩
    simp only [execute, executeWith, hc, hd, hf, Option.bind_eq_bind, Option.bind_some,
      guard_bind_eq_some_iff, isInK_ofLimbs, and_self, true_and, Option.pure_def,
      Option.some.injEq, ofLimbs_eq_zero_iff, limb_ofLimbs, Matrix.cons_val_zero] at hexec
    exact hexec.symm
  · rintro ⟨⟨hc, hd, hf⟩, rfl⟩
    refine ⟨⟨hc, hd, hf⟩, ?_⟩
    simp only [execute, executeWith, hc, hd, hf, Option.bind_eq_bind, Option.bind_some,
      guard_bind_eq_some_iff, isInK_ofLimbs, and_self, Option.pure_def, ofLimbs_eq_zero_iff,
      limb_ofLimbs, Matrix.cons_val_zero]

/-! ## The adapter to the prover data -/

/-- The table's `Spec`: the row refines `JumpRefines` over the image the prover data names. No
program: the table is program-free (the module docstring). -/
def JumpSpec (r : JumpRow K) (next : Regs K) (data : ProverData K) : Prop :=
  JumpRefines (imageOf data).2 r next

/-! ## The table -/

/-- The `JUMP` table (specification §7.5; `tables.rs:693-815`): the witnesses `w`, `b`, the two
residual constraints, the state pull and the push of the derived successor, the bytecode read
of `(JMP, o_c, o_d, o_f, 0, 0, 0, 0)`, and the three single-limb reads. Returns the pushed
successor. -/
def jumpTable : GeneralFormalCircuit K JumpRow Regs where
  main r := do
    -- The honest inverse `w = v_cond⁻¹` (`0` when `v_cond = 0`) and the indicator `b`.
    let w ← witness (.ite (r.vcond =? 0) 0 r.vcond⁻¹)
    let b ← witness (.ite (r.vcond =? 0) 0 1)
    assertZero (b + r.vcond * w)
    assertZero (r.vcond * (b + 1))
    let next : Var Regs K :=
      ⟨b * r.vpc + b * (Expression.const g * r.pc) + Expression.const g * r.pc,
        b * r.vfp + b * r.fp + r.fp⟩
    StatePull.pull ⟨r.pc, r.fp⟩
    StatePush.push next
    bytecodeRead r.pc r.rbc (Expression.const Opcode.jump.code) #v[r.oc, r.od, r.of, 0, 0, 0, 0]
    memRead (r.fp * r.oc) r.rc #v[r.vcond, 0, 0]
    memRead (r.fp * r.od) r.rd #v[r.vpc, 0, 0]
    memRead (r.fp * r.of) r.rf #v[r.vfp, 0, 0]
    pure next
  -- The push channels: their requirements are vacuous, the obligation is `Spec`.
  channelsWithRequirements := [StatePush.toRaw, MemPush.toRaw, BytecodePush.toRaw]
  requirementsChannelsLawful input offset := by
    -- Without core's `BitVec.reduceNeg` simproc, which misreads `-1 : K` (the field's `-1` is `1`).
    simp only [circuit_norm, memRead, bytecodeRead, -BitVec.reduceNeg]
    tauto
  -- The row refines the relation over the data's image, to the pushed successor.
  Spec := JumpSpec
  -- The honest prover's row: written from a valid step, it is bound and executes its
  -- instruction (the bindings alone, by `jump_refines_iff`). Proved of the row built from any
  -- valid execution by `jumpRowOf_refines`; see `jump_exec_complete`.
  ProverAssumptions r data _ := ∃ next, JumpSpec r next data
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    -- The bytecode guarantee, that the tuple decodes, is unused (see `XOR`).
    obtain ⟨hw, hb, -, hc, hd, hf⟩ := h_holds
    have hind := flags_sound hw hb
    refine (jump_refines_iff _ _ _).mpr ⟨⟨hc, hd, hf⟩, ?_⟩
    split_ifs at hind ⊢ with hc0
    · -- Not taken: `b = 0`, the successor is `(g·pc, fp)`.
      simp only [hind, zero_mul, zero_add, Regs.next]
    · -- Taken: `b = 1`, the successor is `(v_pc, v_fp)` since `x + x = 0`.
      simp only [hind, one_mul, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    -- The four pull guarantees are the bindings of the semantic premise, the tuple `main`
    -- emits decodes (`decode_entry`), and the two residuals hold of the honest witnesses.
    obtain ⟨next, h⟩ := h_assumptions
    obtain ⟨hc, hd, hf⟩ := h.bindings
    obtain ⟨hw, hb⟩ := h_env
    rw [hw, hb]
    exact ⟨(flags_complete _).1, (flags_complete _).2, ⟨_, decode_entry (.jump _ _ _)⟩,
      hc, hd, hf⟩

/-! ## The witness discipline -/

/-- A witness program's conditional on a decided field equality is the conditional on the
equality of the evaluations. Applied before `circuit_norm` descends into the `decide` (the `↓`
below): rewriting underneath a `decide` leaves its `Decidable` instance behind, an ill-typed
term no later rewrite can touch. -/
private theorem ite_feq {α : Type} (ctx : Witgen.Ctx K) (x y : Witgen.FExpr K) (a b : α) :
    (if (Witgen.BExpr.feq x y).eval ctx = true then a else b) =
      if x.eval ctx = y.eval ctx then a else b := by
  simp only [Witgen.BExpr.eval_feq_iff]

/-- A prover environment uses the two local witnesses of a `JUMP` row exactly when slot
`offset` is the honest inverse and slot `offset + 1` the honest indicator of the condition. -/
theorem jump_env_iff (env : ProverEnvironment K) (offset : ℕ) (r : Var JumpRow K) :
    env.UsesLocalWitnessesCompleteness offset ((jumpTable.main r).operations offset) ↔
      env.get offset = (if (eval env r).vcond = 0 then 0 else (eval env r).vcond⁻¹) ∧
        env.get (offset + 1) = (if (eval env r).vcond = 0 then 0 else 1) := by
  -- As `circuit_proof_start` does: the row destructured into its columns, the table unfolded
  -- by `dsimp` (unfolding it by `simp` exhausts the recursion depth), then `circuit_norm`,
  -- with `ite_feq` reading the witness programs' `Bool` conditions back as propositions before
  -- the descent.
  obtain ⟨pc, fp, oc, od, of, vcond, vpc, vfp, rc, rd, rf, rbc⟩ := r
  dsimp only [jumpTable]
  simp only [↓ite_feq, circuit_norm, memRead, bytecodeRead, -BitVec.reduceNeg]
  -- The two sides differ only in the instance paths of `K`'s field structure.
  exact Iff.rfl

/-- The honest prover environment of a `JUMP` row over `data`: slot `0` the inverse `w`, slot
`1` the indicator `b`, as the two witness programs compute them; the data; no hints. -/
def jumpEnv (data : ProverData K) (r : JumpRow K) : ProverEnvironment K :=
  ⟨⟨fun j ↦ if j = 0 then (if r.vcond = 0 then 0 else r.vcond⁻¹)
      else if j = 1 then (if r.vcond = 0 then 0 else 1) else 0, data⟩, default⟩

/-! ## Rows from executions -/

/-- The row of an execution of `JUMP o_c o_d o_f` from `(pc, fp)` over the image `mem`: the
registers, the operands, the three low limbs read back from the image, and the counts as
parameters. Noncomputable: it reads the image. -/
noncomputable def jumpRowOf {κ : ℕ} (mem : MemImage κ) (pc fp oc od of rc rd rf rbc : K) :
    JumpRow K :=
  ⟨pc, fp, oc, od, of, (mem.limbsAt (fp * oc))[0], (mem.limbsAt (fp * od))[0],
    (mem.limbsAt (fp * of))[0], rc, rd, rf, rbc⟩

/-- A valid execution of `JUMP o_c o_d o_f` is represented by `jumpRowOf`, with any counts: the
honest prover's row refines the relation, which is `ProverAssumptions` over the data. -/
theorem jumpRowOf_refines {κ : ℕ} {mem : MemImage κ} {pc fp oc od of : K} {next : Regs K}
    (hexec : execute mem ⟨pc, fp⟩ (.jump oc od of) = some next) (rc rd rf rbc : K) :
    JumpRefines mem (jumpRowOf mem pc fp oc od of rc rd rf rbc) next := by
  have h := hexec
  simp only [execute, executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨c, hc, d, hd, f, hf, u, hu, -⟩ := h
  obtain ⟨hcK, hdK, hfK⟩ := guard_eq_some hu
  refine ⟨⟨?_, ?_, ?_⟩, hexec⟩
  · show mem.read (fp * oc) = some (E.ofLimbs (mem.limbsAt (fp * oc))[0] 0 0)
    rw [MemImage.limbsAt_getElem_zero hc, ofLimbs_of_isInK hcK]; exact hc
  · show mem.read (fp * od) = some (E.ofLimbs (mem.limbsAt (fp * od))[0] 0 0)
    rw [MemImage.limbsAt_getElem_zero hd, ofLimbs_of_isInK hdK]; exact hd
  · show mem.read (fp * of) = some (E.ofLimbs (mem.limbsAt (fp * of))[0] 0 0)
    rw [MemImage.limbsAt_getElem_zero hf, ofLimbs_of_isInK hfK]; exact hf

/-- Every valid `JUMP` execution has a satisfying row, witnesses included, from the execution
alone: the constraints of `main` hold of `jumpRowOf` in its honest environment over the data. -/
theorem jump_exec_complete {data : ProverData K} {pc fp oc od of : K} {next : Regs K}
    (hexec : execute (imageOf data).2 ⟨pc, fp⟩ (.jump oc od of) = some next) (rc rd rf rbc : K) :
    ConstraintsHold.Completeness
      (jumpEnv data (jumpRowOf (imageOf data).2 pc fp oc od of rc rd rf rbc))
      ((jumpTable.main
        (const (jumpRowOf (imageOf data).2 pc fp oc od of rc rd rf rbc))).operations 0) :=
  (jumpTable.completeness 0 (jumpEnv data _) (const _)
    -- `jumpEnv` holds the honest inverse and indicator of the row's condition (`jump_env_iff`).
    (by rw [jump_env_iff, ProvableType.eval_const_prover]; exact ⟨rfl, rfl⟩) _
    ProvableType.eval_const_prover ⟨_, jumpRowOf_refines hexec rc rd rf rbc⟩).1

end LeanVM.Arithmetization
