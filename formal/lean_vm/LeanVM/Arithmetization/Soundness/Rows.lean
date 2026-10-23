/-
  LeanVM.Arithmetization.Soundness.Rows

  What an arbitrary row of each of the six opcode tables sends, in the shape every table shares,
  and what the table's soundness makes of it: under the guarantees of its pulls, the row is a step
  of the machine from its pulled state to its pushed state.
-/

module

public import LeanVM.Arithmetization.Completeness.Rows

@[expose] public section

/-!
# The rows of a satisfying witness

At leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d` and Clean pin `42fe4b26`. Specification
§7 (the six AIRs, `doc/leanvm/body/07-*`) and §6 (their bus interactions): the per-row soundness
of the six opcode tables, from the tables of `Arithmetization.Tables` and their Clean soundness
theorems; the bus is `Soundness.Bus`'s.

**The shape of a row** (`OpRow`). A raw row of a witness is an arbitrary array, read by its
component as the typed row `rowInput` (the first cells, a missing cell `0`). Whatever its cells,
the row circuit of each opcode table sends the messages `sendsOf pc fp next rbc e reads` of
`Completeness.Rows`: the state pull `(pc, fp)` and push `next`, the bytecode pull and push of the
eight coordinates `e` at `pc`, and per memory read a pull of `(addr, count, v)` and a push of
`(addr, g·count, v)`, at most nine reads (`BLAKE2S`). The memory and bytecode pairs need nothing
more of the rows than this shape (`Soundness.MemChannel`, `Soundness.BytecodeChannel`).

**The step** (also `OpRow`). Under the table's `Assumptions` (the compression, for `BLAKE2S`), its
constraints (the `JUMP` residuals), and the guarantees of its pulls (that the memory reads are the
image's words and the bytecode entry decodes, which `Soundness.MemChannel` and
`Soundness.BytecodeChannel` derive from the bus), Clean's instantiated soundness theorem
(`Component.weakSoundness`) gives the table's `Spec`: the row refines the table's relation, so some
instruction `ins` with `entry ins = e` executes from `(pc, fp)` to `next` (`execute`), and
to the fall-through `(g·pc, fp)` unless it is a `JUMP`. The pushed successor is the table's output,
which for `JUMP` reads the indicator, the row's second local witness (`jump_output_gen`).

**The guarantees** (`ChannelOk`). Of the six channels only the memory pull and the bytecode pull
carry a guarantee; every interaction a table emits is on one of the six (`*_channelOk`), so the
guarantees of a row are those of its memory and bytecode pulls.

## Wrong readings excluded

* A row is not assumed to be a typed row written by an honest prover: the shape holds for every
  array, the step only under the guarantees, which the bus supplies.
* The table does not know which instruction the program holds at `pc`: `e = entry ins` names the
  instruction the row's own columns encode, and that it is the program's is the bytecode pair's
  (`Soundness.BytecodeChannel`).
* The `JUMP` successor is not read from the row's columns alone: it is the output, a function of
  the indicator, forced by the residuals (`flags_sound`) inside the table's soundness.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics
open Air.Flat (Component)

/-! ## The shape of a row -/

/-- The parameters of what an opcode-table row sends (`sendsOf`): the pulled state, the pushed
successor, the bytecode count and coordinates, and the memory reads. -/
structure RowRec where
  /-- The pulled program counter. -/
  pc : K
  /-- The pulled frame pointer. -/
  fp : K
  /-- The pushed successor. -/
  next : Regs K
  /-- The bytecode read count. -/
  rbc : K
  /-- The bytecode coordinates `(opcode, op₁, …, op₇)`. -/
  e : Vector K 8
  /-- The memory reads `(addr, count, limbs)`. -/
  reads : List (K × K × Vector K 3)

/-- A record exists. -/
instance : Inhabited RowRec := ⟨⟨0, 0, ⟨0, 0⟩, 0, 0, []⟩⟩

/-- What a row with these parameters sends. -/
def RowRec.sends (x : RowRec) : List (String × Array K) :=
  sendsOf x.pc x.fp x.next x.rbc x.e x.reads

/-- The pulled state of a record. -/
def RowRec.src (x : RowRec) : Regs K := ⟨x.pc, x.fp⟩

/-- A component's row in the environment `env` has the shape of an opcode-table row, with at
most nine memory reads, and under the table's assumptions, constraints and pull guarantees it is
a step: an instruction encoded by its bytecode coordinates executes from its pulled state to its
pushed state over the image the data names, to the fall-through unless it is a `JUMP`. -/
def OpRow (c : Component K) (env : Environment K) : Prop :=
  ∃ x : RowRec, rowSends c env = x.sends ∧ x.reads.length ≤ 9 ∧
    (c.Assumptions env → c.operations.ConstraintsHold env → c.operations.FullGuarantees env →
      ∃ ins, x.e = entry ins ∧ execute (imageOf env.data).2 x.src ins = some x.next ∧
        (ins.opcode ≠ .jump → x.next = ⟨g * x.pc, x.fp⟩))

/-! ## The six tables -/

/-- An `XOR` row has the shape and, under the guarantees, steps. -/
theorem xor_opRow (env : Environment K) : OpRow ⟨xorTable⟩ env := by
  set r := (⟨xorTable⟩ : Component K).rowInput env with hr
  have hx : eval env (varFromOffset XorRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine ⟨⟨r.pc, r.fp, ⟨g * r.pc, r.fp⟩, r.rbc, entry (.xor r.oA r.oB r.oC),
    [(r.fp * r.oA, r.rA, r.vA), (r.fp * r.oB, r.rB, r.vB),
     (r.fp * r.oC, r.rC, #v[r.vA[0] + r.vB[0], r.vA[1] + r.vB[1], r.vA[2] + r.vB[2]])]⟩,
    ?_, by simp, ?_⟩
  · rw [rowSends_mk, xor_sends_gen _ _ _ _ hx]
    simp [RowRec.sends, sendsOf, memMsgOf, bcMsgOf, entry]
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : XorRefines (imageOf env.data).2 r ((⟨xorTable⟩ : Component K).rowOutput env) := hs
    obtain ⟨-, -, hnext⟩ := (xor_refines_iff _ _ _).mp hs'
    refine ⟨.xor r.oA r.oB r.oC, rfl, ?_, fun _ ↦ rfl⟩
    rw [← show ((⟨xorTable⟩ : Component K).rowOutput env) = ⟨g * r.pc, r.fp⟩ from hnext]
    exact hs'.exec_eq

/-- A `SET_CONSTANT` row has the shape and, under the guarantees, steps. -/
theorem set_opRow (env : Environment K) : OpRow ⟨setTable⟩ env := by
  set r := (⟨setTable⟩ : Component K).rowInput env with hr
  have hx : eval env (varFromOffset SetRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine ⟨⟨r.pc, r.fp, ⟨g * r.pc, r.fp⟩, r.rbc,
    #v[Opcode.setConstant.code, r.o, r.k[0], r.k[1], r.k[2], 0, 0, 0],
    [(r.fp * r.o, r.r, r.k)]⟩, ?_, by simp, ?_⟩
  · rw [rowSends_mk, set_sends_gen _ _ _ _ hx]
    simp [RowRec.sends, sendsOf, memMsgOf, bcMsgOf]
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : SetRefines (imageOf env.data).2 r ((⟨setTable⟩ : Component K).rowOutput env) := hs
    obtain ⟨-, hnext⟩ := (set_refines_iff _ _ _).mp hs'
    refine ⟨.setConstant r.o (E.ofLimbs r.k[0] r.k[1] r.k[2]), by simp [entry, limb_ofLimbs],
      ?_, fun _ ↦ rfl⟩
    rw [← show ((⟨setTable⟩ : Component K).rowOutput env) = ⟨g * r.pc, r.fp⟩ from hnext]
    exact hs'.exec_eq

/-- A `MUL_NATIVE` row has the shape and, under the guarantees, steps. -/
theorem mul_opRow (env : Environment K) : OpRow ⟨mulTable⟩ env := by
  set r := (⟨mulTable⟩ : Component K).rowInput env with hr
  have hx : eval env (varFromOffset MulRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine ⟨⟨r.pc, r.fp, ⟨g * r.pc, r.fp⟩, r.rbc, entry (.mulNative r.oA r.oB r.oC),
    [(r.fp * r.oA, r.rA, r.vA), (r.fp * r.oB, r.rB, r.vB),
     (r.fp * r.oC, r.rC, #v[r.vA[0] * r.vB[0] + r.vA[1] * r.vB[2] + r.vA[2] * r.vB[1],
          r.vA[0] * r.vB[1] + r.vA[1] * r.vB[0] + r.vA[1] * r.vB[2] + r.vA[2] * r.vB[1] +
            r.vA[2] * r.vB[2],
          r.vA[0] * r.vB[2] + r.vA[1] * r.vB[1] + r.vA[2] * r.vB[0] + r.vA[2] * r.vB[2]])]⟩,
    ?_, by simp, ?_⟩
  · rw [rowSends_mk, mul_sends_gen _ _ _ _ hx]
    simp [RowRec.sends, sendsOf, memMsgOf, bcMsgOf, entry]
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : MulRefines (imageOf env.data).2 r ((⟨mulTable⟩ : Component K).rowOutput env) := hs
    obtain ⟨-, -, hnext⟩ := (mul_refines_iff _ _ _).mp hs'
    refine ⟨.mulNative r.oA r.oB r.oC, rfl, ?_, fun _ ↦ rfl⟩
    rw [← show ((⟨mulTable⟩ : Component K).rowOutput env) = ⟨g * r.pc, r.fp⟩ from hnext]
    exact hs'.exec_eq

/-- A `DEREF` row has the shape and, under the guarantees, steps: the mode is the one its flags
name. -/
theorem deref_opRow (env : Environment K) : OpRow ⟨derefTable⟩ env := by
  set r := (⟨derefTable⟩ : Component K).rowInput env with hr
  have hx : eval env (varFromOffset DerefRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine ⟨⟨r.pc, r.fp, ⟨g * r.pc, r.fp⟩, r.rbc,
    #v[Opcode.deref.code, r.o1, r.o2, r.o3, r.fpc, r.ffp, 0, 0],
    [(r.fp * r.o1, r.r1, #v[r.p, 0, 0]),
     (r.p * r.o2, r.r2, #v[(1 + r.fpc + r.ffp) * r.v3[0] + r.fpc * (g ^ 2 * r.pc) + r.ffp * r.fp,
          (1 + r.fpc + r.ffp) * r.v3[1], (1 + r.fpc + r.ffp) * r.v3[2]]),
     (r.fp * r.o3, r.r3, r.v3)]⟩,
    ?_, by simp, ?_⟩
  · rw [rowSends_mk, deref_sends_gen _ _ _ _ hx]
    simp [RowRec.sends, sendsOf, memMsgOf, bcMsgOf]
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : DerefRefines (imageOf env.data).2 r
      ((⟨derefTable⟩ : Component K).rowOutput env) := hs
    obtain ⟨mode, hb, -, hnext⟩ := (deref_refines_iff _ _ _).mp hs'
    obtain ⟨mode', hb', hexec⟩ := hs'
    have hflags := hb.flags_eq
    have hm : mode' = mode := by
      have h1 := derefMode?_flags mode
      have h2 := derefMode?_flags mode'
      rw [hflags] at h1
      rw [hb'.flags_eq] at h2
      exact Option.some.inj (h2.symm.trans h1)
    subst hm
    refine ⟨.deref r.o1 r.o2 r.o3 mode', ?_, ?_, fun _ ↦ rfl⟩
    · simp [entry, hflags]
    · rw [← show ((⟨derefTable⟩ : Component K).rowOutput env) = ⟨g * r.pc, r.fp⟩ from hnext]
      exact hexec

/-- A `BLAKE2S` row has the shape and, under the compression and the guarantees, steps. -/
theorem blake2s_opRow (env : Environment K) : OpRow ⟨blake2sTable⟩ env := by
  set r := (⟨blake2sTable⟩ : Component K).rowInput env with hr
  have hx : eval env (varFromOffset Blake2sRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine ⟨⟨r.pc, r.fp, ⟨g * r.pc, r.fp⟩, r.rbc,
    entry (.blake2s ![r.om0, r.om1, r.om2, r.om3] r.ocv r.oout r.omd),
    [(r.fp * r.om0, r.rm0, #v[r.m0[0], r.m0[1], 0]), (r.fp * r.om1, r.rm1, #v[r.m1[0], r.m1[1], 0]),
     (r.fp * r.om2, r.rm2, #v[r.m2[0], r.m2[1], 0]), (r.fp * r.om3, r.rm3, #v[r.m3[0], r.m3[1], 0]),
     (r.fp * r.ocv, r.rcv0, #v[r.cv0[0], r.cv0[1], 0]),
     (r.fp * (g * r.ocv), r.rcv1, #v[r.cv1[0], r.cv1[1], 0]),
     (r.fp * r.oout, r.rout0, #v[r.out0[0], r.out0[1], 0]),
     (r.fp * (g * r.oout), r.rout1, #v[r.out1[0], r.out1[1], 0]),
     (r.fp * r.omd, r.rmd, #v[r.md[0], r.md[1], 0])]⟩, ?_, by simp, ?_⟩
  · rw [rowSends_mk, blake2s_sends_gen _ _ _ _ hx]
    simp [RowRec.sends, sendsOf, memMsgOf, bcMsgOf, entry]
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : Blake2sRefines (imageOf env.data).2 r
      ((⟨blake2sTable⟩ : Component K).rowOutput env) := hs
    obtain ⟨-, -, hnext⟩ := (blake2s_refines_iff _ _ _).mp hs'
    refine ⟨.blake2s ![r.om0, r.om1, r.om2, r.om3] r.ocv r.oout r.omd, rfl, ?_, fun _ ↦ rfl⟩
    rw [← show ((⟨blake2sTable⟩ : Component K).rowOutput env) = ⟨g * r.pc, r.fp⟩ from hnext]
    exact hs'.exec_eq

/-- The output of the `JUMP` row circuit at a row variable that evaluates to `r`: the successor
selected by the indicator `b`, the local witness at slot `n + 1`. -/
theorem jump_output_gen (x : Var JumpRow K) (env : Environment K) (n : ℕ) (r : JumpRow K)
    (hx : eval env x = r) (b : K) (hb : env.get (n + 1) = b) :
    eval env ((jumpTable.main x).output n) =
      (⟨b * r.vpc + b * (g * r.pc) + g * r.pc, b * r.vfp + b * r.fp + r.fp⟩ : Regs K) := by
  subst hx
  obtain ⟨pc, fp, oc, od, of, vcond, vpc, vfp, rc, rd, rf, rbc⟩ := x
  dsimp only [jumpTable]
  simp only [circuit_norm, memRead, bytecodeRead, hb, -BitVec.reduceNeg]

/-- A `JUMP` row has the shape, its pushed successor the table's output, and under the residuals
and the guarantees steps. -/
theorem jump_opRow (env : Environment K) : OpRow ⟨jumpTable⟩ env := by
  set r := (⟨jumpTable⟩ : Component K).rowInput env with hr
  have hx : eval env (varFromOffset JumpRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine ⟨⟨r.pc, r.fp, (⟨jumpTable⟩ : Component K).rowOutput env, r.rbc,
    entry (.jump r.oc r.od r.of),
    [(r.fp * r.oc, r.rc, #v[r.vcond, 0, 0]), (r.fp * r.od, r.rd, #v[r.vpc, 0, 0]),
     (r.fp * r.of, r.rf, #v[r.vfp, 0, 0])]⟩, ?_, by simp, ?_⟩
  · have ho : (⟨jumpTable⟩ : Component K).rowOutput env = _ :=
      jump_output_gen _ env (size JumpRow) r hx _ rfl
    rw [rowSends_mk, jump_sends_gen _ _ _ _ hx _ rfl, ho]
    simp [RowRec.sends, sendsOf, memMsgOf, bcMsgOf, entry]
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : JumpRefines (imageOf env.data).2 r
      ((⟨jumpTable⟩ : Component K).rowOutput env) := hs
    exact ⟨_, rfl, hs'.exec_eq, fun h ↦ absurd rfl h⟩

/-! ## The guarantees of a row -/

/-- A channel whose guarantee a row may need: the memory pull, the bytecode pull, or a channel
guaranteeing nothing. -/
def ChannelOk (ch : RawChannel K) : Prop :=
  ch = MemPull.toRaw ∨ ch = BytecodePull.toRaw ∨ ∀ mult msg data, ch.Guarantees mult msg data

-- Each of the six channels is `ChannelOk`: the two lookup pulls by name, the others since their
-- guarantee is `True` at every multiplicity.
private theorem channelOk_memPull : ChannelOk MemPull.toRaw := Or.inl rfl
private theorem channelOk_bytecodePull : ChannelOk BytecodePull.toRaw := Or.inr (Or.inl rfl)
private theorem channelOk_statePull : ChannelOk StatePull.toRaw :=
  Or.inr (Or.inr fun _ _ _ _ ↦ trivial)
private theorem channelOk_statePush : ChannelOk StatePush.toRaw :=
  Or.inr (Or.inr fun _ _ _ _ ↦ trivial)
private theorem channelOk_memPush : ChannelOk MemPush.toRaw :=
  Or.inr (Or.inr fun _ _ _ _ ↦ trivial)
private theorem channelOk_bytecodePush : ChannelOk BytecodePush.toRaw :=
  Or.inr (Or.inr fun _ _ _ _ ↦ trivial)

/-- Every interaction of the `XOR` table is on one of the six channels. -/
theorem xor_channelOk : ∀ a ∈ (⟨xorTable⟩ : Component K).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  simp only [Component.rowOperations_mk, circuit_norm, xorTable, memRead, bytecodeRead,
    -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

/-- Every interaction of the `MUL_NATIVE` table is on one of the six channels. -/
theorem mul_channelOk : ∀ a ∈ (⟨mulTable⟩ : Component K).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  simp only [Component.rowOperations_mk, circuit_norm, mulTable, memRead, bytecodeRead,
    -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

/-- Every interaction of the `SET_CONSTANT` table is on one of the six channels. -/
theorem set_channelOk : ∀ a ∈ (⟨setTable⟩ : Component K).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  simp only [Component.rowOperations_mk, circuit_norm, setTable, memRead, bytecodeRead,
    -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

/-- Every interaction of the `DEREF` table is on one of the six channels. -/
theorem deref_channelOk : ∀ a ∈ (⟨derefTable⟩ : Component K).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  simp only [Component.rowOperations_mk, circuit_norm, derefTable, memRead, bytecodeRead,
    -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

/-- Every interaction of the `JUMP` table is on one of the six channels. -/
theorem jump_channelOk : ∀ a ∈ (⟨jumpTable⟩ : Component K).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  dsimp only [Component.rowOperations_mk, jumpTable]
  simp only [circuit_norm, memRead, bytecodeRead, -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

/-- Every interaction of the `BLAKE2S` table is on one of the six channels. -/
theorem blake2s_channelOk : ∀ a ∈ (⟨blake2sTable⟩ : Component K).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  simp only [Component.rowOperations_mk, circuit_norm, blake2sTable, memRead, bytecodeRead,
    -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

/-! ## The opcode tables of a witness -/

variable {prog : Program}

/-- Each of the first six tables of a witness has rows of the opcode-table shape, and every
interaction it emits is on one of the six channels. -/
theorem tableAt_opRow (w : Air.Flat.EnsembleWitness (leanIsaEnsemble prog)) (j : Fin 8)
    (hj : (j : ℕ) < 6) :
    (∀ env, OpRow (tableAt w j).component env) ∧
      ∀ a ∈ (tableAt w j).component.operations.interactions, ChannelOk a.channel := by
  rw [tableAt_component]
  fin_cases j
  · exact ⟨xor_opRow, xor_channelOk⟩
  · exact ⟨mul_opRow, mul_channelOk⟩
  · exact ⟨set_opRow, set_channelOk⟩
  · exact ⟨deref_opRow, deref_channelOk⟩
  · exact ⟨jump_opRow, jump_channelOk⟩
  · exact ⟨blake2s_opRow, blake2s_channelOk⟩
  · exact absurd hj (by decide)
  · exact absurd hj (by decide)

end LeanVM.Arithmetization
