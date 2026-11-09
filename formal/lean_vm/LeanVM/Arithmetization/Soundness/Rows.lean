/-
  LeanVM.Arithmetization.Soundness.Rows

  What an arbitrary row of each of the six opcode tables sends, in the shape every table shares,
  and what the table's soundness makes of it: under the guarantees of its pulls, the row is a step
  of the machine from its pulled state to its pushed state.
-/

module

public import LeanVM.Arithmetization.Completeness.Bus
public import Statement.LeanIsa
public import LeanVM.Facts.IsaWith
public import Statement.Fast.QuadExt
public import Statement.Fast.FieldWords

@[expose] public section

/-!
# The rows of a satisfying witness

At leanVM pin `4af2cdddd7cd41b9df2cc7e123e314a91b0b4462` and Clean pin `b41c196b`. Specification
§7 (the six AIRs, `doc/leanvm/body/07-*`) and §6 (their bus interactions): the per-row soundness
of the six opcode tables, from the tables of `Arithmetization.Tables` and their Clean soundness
theorems; the bus is `Soundness.Bus`'s.

**The shape of a row** (`OpRow`). A raw row of a witness is an arbitrary array, read by its
component as the typed row `rowInput` (the first cells, a missing cell `0`). Whatever its cells,
the row circuit of each opcode table sends the messages `sendsOf pc fp next rbc e reads` of
`Completeness.Rows`: the state pull `(pc, fp)` and push `next`, the bytecode pull and push of the
thirteen coordinates `e` at `pc`, and per memory read a pull of `(addr, count, v)` and a push of
`(addr, g·count, v)`; then, for `KECCAK`'s output cells `1..13` (leanVM main `40f877dc`),
per gated read `(flag, addr, count, v)` a pull of `(addr, count, v)` and a push of
`(addr, count + g·(flag·count) + flag·count, v)` (`gatedSends`): at most twenty-six reads, plain
or gated. A gated read at flag `1` is a read (`RowRec.real`); at flag `0` a cancelled pair
(`RowRec.skips`). A memory pull of multiplicity `1`, the one whose guarantee a soundness proof
assumes, is a read the row makes (the gated pull's multiplicity is `flag`), and when the row's
bytecode coordinates are an instruction's every gate is `0` or `1` (`decode` of the output flags).
The memory and bytecode pairs need nothing more of the rows than this shape
(`Soundness.MemChannel`, `Soundness.BytecodeChannel`).

**The step** (also `OpRow`). Under the table's `Assumptions` (the permutation, for `KECCAK`), its
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

**Without the permutation** (`OpRow`'s last clause). Under its constraints and the guarantees
alone a row is a step of the reduction-blind semantics `keccakFree` (`Statement.LeanIsa`), whose
`KECCAK` asks only the written cells' free limb zero: a `KECCAK` row is bound
to the image by the table's circuit without its assumption (`keccakTableFree`), and its cells are
cells of lanes (`keccak_free_exec`); every other table assumes nothing, and a deployed step is a
reduction-blind one (`executeWithB_free_of_executeWith`).

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

/-- The row operations of an opcode table: its circuit's, at the row variable. -/
theorem rowOperations_opcodeComponent {Row : TypeMap} [ProvableType Row]
    (c : GeneralFormalCircuit K Row Registers) :
    (opcodeComponent c).rowOperations = (c.main (varFromOffset Row 0)).operations (size Row) :=
  rfl

/-! ## The shape of a row -/

/-- The parameters of what an opcode-table row sends (`sendsOf`): the pulled state, the pushed
successor, the bytecode count and coordinates, and the memory reads. -/
structure RowRec where
  /-- The pulled program counter. -/
  pc : K
  /-- The pulled frame pointer. -/
  fp : K
  /-- The pushed successor. -/
  next : Registers K
  /-- The bytecode read count. -/
  rbc : K
  /-- The bytecode coordinates `(opcode, op₁, …, op₁₂)`. -/
  e : Vector K 13
  /-- The memory reads `(addr, count, limbs)`. -/
  reads : List (K × K × Vector K 2)
  /-- The gated memory reads `(flag, addr, count, limbs)` (`memReadIf`): a `KECCAK` row's output
  cells past the first, after the reads. -/
  gated : List (K × K × K × Vector K 2)

/-- A record exists. -/
instance : Inhabited RowRec := ⟨⟨0, 0, ⟨0, 0⟩, 0, 0, [], []⟩⟩

/-- What a row with these parameters sends: its reads, then its gated reads. -/
def RowRec.sends (x : RowRec) : List (String × Array K) :=
  sendsOf x.pc x.fp x.next x.rbc x.e x.reads ++ gatedSends x.gated

/-- The reads a row makes: its reads and its gated reads at flag `1`. A gated read at flag `0` is a
cancelled pair, and makes none. -/
def RowRec.real (x : RowRec) : List (K × K × Vector K 2) :=
  x.reads ++ (x.gated.filter fun y ↦ y.1 = 1).map (·.2)

/-- The cancelled pairs of a row: its gated reads at flag `0`. -/
def RowRec.skips (x : RowRec) : List (K × K × Vector K 2) :=
  (x.gated.filter fun y ↦ y.1 = 0).map (·.2)

/-- The pulled state of a record. -/
def RowRec.src (x : RowRec) : Registers K := ⟨x.pc, x.fp⟩

/-- A component's row in the environment `env` has the shape of an opcode-table row, with at
most twenty-six memory reads, plain or gated; a memory pull of multiplicity `1` is a read the row
makes; its gates are `0` or `1` when its bytecode coordinates are an instruction's; and under the
table's assumptions, constraints and pull guarantees it is
a step: an instruction encoded by its bytecode coordinates executes from its pulled state to its
pushed state over the image the data names, to the fall-through unless it is a `JUMP`. Without
the assumptions (the permutation, for `KECCAK`) it is a step under the reduction-blind semantics
`keccakFree` (`Statement.LeanIsa`). -/
def OpRow (c : Component K) (env : Environment K) : Prop :=
  ∃ x : RowRec, rowSends c env = x.sends ∧ x.reads.length + x.gated.length ≤ 26 ∧
    -- A memory pull of multiplicity `1`, the one whose guarantee a soundness proof assumes, is a
    -- read the row makes: a read or a gated read at flag `1`.
    (∀ i ∈ c.rowOperations.interactions.map (AbstractInteraction.eval env),
      i.channel.name = MemPull.name → i.mult = 1 →
        i.msg ∈ x.real.map fun y ↦ memMsgOf y.1 y.2.1 y.2.2) ∧
    -- When its bytecode coordinates are an instruction's, every gate is `0` or `1`.
    ((∃ ins, x.e = busEntry ins) → ∀ y ∈ x.gated, y.1 = 0 ∨ y.1 = 1) ∧
    (c.CircuitAssumptions env → c.operations.ConstraintsHold env → c.operations.FullGuarantees env →
      ∃ ins, x.e = busEntry ins ∧ execute (imageOf env.data).2 x.src ins = some x.next ∧
        (ins.opcode ≠ .jump → x.next = ⟨g * x.pc, x.fp⟩)) ∧
    (c.operations.ConstraintsHold env → c.operations.FullGuarantees env →
      ∃ ins, x.e = busEntry ins ∧
        executeWithB keccakFree (imageOf env.data).2.read x.src ins = some x.next ∧
        (ins.opcode ≠ .jump → x.next = ⟨g * x.pc, x.fp⟩))

/-- **A deployed step is a reduction-blind step**: the cells Keccak-f writes have their free limb
zero. -/
theorem executeWithB_free_of_executeWith {read : K → Option E} {r next : Registers K} {ins :
    LeanIsaInstruction}
    (h : executeWith read r ins = some next) : executeWithB keccakFree read r ins = some next := by
  cases ins with
  | keccak om otail ob8 ocap oout inOdd outOdd =>
    simp only [executeWith, executeWithB, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨input, hin, output, hout, u, hu, hnext⟩ := h
    refine ⟨input, hin, output, hout, (), ?_, hnext⟩
    have hc := freeLimbZero_of_keccakCells (guard_eq_some hu)
    unfold guard
    simp only [keccakFree, hc, ↓reduceIte]
    rfl
  | _ => exact h

/-- A row with no gated read: its memory pulls are its reads. -/
theorem guarded_of_sends {c : Component K} {env : Environment K} {x : RowRec}
    (hs : rowSends c env = x.sends) (hg : x.gated = []) :
    ∀ i ∈ c.rowOperations.interactions.map (AbstractInteraction.eval env),
      i.channel.name = MemPull.name → i.mult = 1 →
        i.msg ∈ x.real.map fun y ↦ memMsgOf y.1 y.2.1 y.2.2 := by
  intro i hi hn _
  have hm : (i.channel.name, i.msg) ∈ rowSends c env :=
    List.mem_map.mpr ⟨i, hi, rfl⟩
  rw [hs, RowRec.sends, hg, gatedSends, List.flatMap_nil, List.append_nil] at hm
  have hm' : i.msg ∈ ((sendsOf x.pc x.fp x.next x.rbc x.e x.reads).filter
      (·.1 = MemPull.name)).map (·.2) :=
    List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hm, by simp [hn]⟩, rfl⟩
  rw [sendsOf_memPull] at hm'
  simpa [RowRec.real, hg] using hm'

/-- A row of a table whose assumptions hold, with no gated read, is a reduction-blind step where it
is a step. -/
theorem opRow_of_assumptions {c : Component K} {env : Environment K} (hA : c.CircuitAssumptions env)
    (h : ∃ x : RowRec, rowSends c env = x.sends ∧ x.gated = [] ∧ x.reads.length ≤ 26 ∧
      (c.CircuitAssumptions env → c.operations.ConstraintsHold env → c.operations.FullGuarantees env →
        ∃ ins, x.e = busEntry ins ∧ execute (imageOf env.data).2 x.src ins = some x.next ∧
          (ins.opcode ≠ .jump → x.next = ⟨g * x.pc, x.fp⟩))) :
    OpRow c env := by
  obtain ⟨x, hs, hg, hl, hd⟩ := h
  refine ⟨x, hs, by simpa [hg] using hl, guarded_of_sends hs hg, fun _ ↦ by simp [hg], hd,
    fun hc hg ↦ (hd hA hc hg).imp fun _ h ↦
      ⟨h.1, executeWithB_free_of_executeWith h.2.1, h.2.2⟩⟩

/-! ## The six tables -/

/-- An `XOR` row has the shape and, under the guarantees, steps. -/
theorem xor_opRow (env : Environment K) : OpRow (opcodeComponent xorTable) env := by
  set r := (opcodeComponent xorTable).rowInput env with hr
  have hx : eval env (varFromOffset XorRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine opRow_of_assumptions trivial
    ⟨⟨r.pc, r.fp, ⟨g * r.pc, r.fp⟩, r.rbc, busEntry (.xor r.oA r.oB r.oC),
    [(r.fp * r.oA, r.rA, r.vA), (r.fp * r.oB, r.rB, r.vB),
     (r.fp * r.oC, r.rC, #v[r.vA[0] + r.vB[0], r.vA[1] + r.vB[1]])], []⟩,
    ?_, rfl, by simp, ?_⟩
  · rw [rowSends_mk, xor_sends_gen _ _ _ _ hx]
    simp [RowRec.sends, sendsOf, gatedSends, memMsgOf, bcMsgOf, busEntry]
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : XorRefines (imageOf env.data).2 r ((opcodeComponent xorTable).rowOutput env) := hs
    obtain ⟨-, -, hnext⟩ := (xor_refines_iff _ _ _).mp hs'
    refine ⟨.xor r.oA r.oB r.oC, rfl, ?_, fun _ ↦ rfl⟩
    rw [← show ((opcodeComponent xorTable).rowOutput env) = ⟨g * r.pc, r.fp⟩ from hnext]
    exact hs'.exec_eq

/-- A `SET_CONSTANT` row has the shape and, under the guarantees, steps. -/
theorem set_opRow (env : Environment K) : OpRow (opcodeComponent setTable) env := by
  set r := (opcodeComponent setTable).rowInput env with hr
  have hx : eval env (varFromOffset SetRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine opRow_of_assumptions trivial ⟨⟨r.pc, r.fp, ⟨g * r.pc, r.fp⟩, r.rbc,
    #v[Opcode.setConstant.busCode, r.o, r.k[0], r.k[1], 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [(r.fp * r.o, r.r, r.k)], []⟩, ?_, rfl, by simp, ?_⟩
  · rw [rowSends_mk, set_sends_gen _ _ _ _ hx]
    simp [RowRec.sends, sendsOf, gatedSends, memMsgOf, bcMsgOf]
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : SetRefines (imageOf env.data).2 r ((opcodeComponent setTable).rowOutput env) := hs
    obtain ⟨-, hnext⟩ := (set_refines_iff _ _ _).mp hs'
    refine ⟨.setConstant r.o (E.ofLimbs r.k[0] r.k[1]), by simp [busEntry, limb_ofLimbs],
      ?_, fun _ ↦ rfl⟩
    rw [← show ((opcodeComponent setTable).rowOutput env) = ⟨g * r.pc, r.fp⟩ from hnext]
    exact hs'.exec_eq

/-- A `MUL_NATIVE` row has the shape and, under the guarantees, steps. -/
theorem mul_opRow (env : Environment K) : OpRow (opcodeComponent mulTable) env := by
  set r := (opcodeComponent mulTable).rowInput env with hr
  have hx : eval env (varFromOffset MulRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine opRow_of_assumptions trivial
    ⟨⟨r.pc, r.fp, ⟨g * r.pc, r.fp⟩, r.rbc, busEntry (.mulNative r.oA r.oB r.oC),
    [(r.fp * r.oA, r.rA, r.vA), (r.fp * r.oB, r.rB, r.vB),
     (r.fp * r.oC, r.rC, #v[r.vA[0] * r.vB[0] + r.vA[1] * r.vB[1],
          r.vA[0] * r.vB[1] + r.vA[1] * r.vB[0] + g * (r.vA[1] * r.vB[1])])], []⟩,
    ?_, rfl, by simp, ?_⟩
  · rw [rowSends_mk, mul_sends_gen _ _ _ _ hx]
    simp [RowRec.sends, sendsOf, gatedSends, memMsgOf, bcMsgOf, busEntry]
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : MulRefines (imageOf env.data).2 r ((opcodeComponent mulTable).rowOutput env) := hs
    obtain ⟨-, -, hnext⟩ := (mul_refines_iff _ _ _).mp hs'
    refine ⟨.mulNative r.oA r.oB r.oC, rfl, ?_, fun _ ↦ rfl⟩
    rw [← show ((opcodeComponent mulTable).rowOutput env) = ⟨g * r.pc, r.fp⟩ from hnext]
    exact hs'.exec_eq

/-- A `DEREF` row has the shape and, under the guarantees, steps: the mode is the one its flags
name. -/
theorem deref_opRow (env : Environment K) : OpRow (opcodeComponent derefTable) env := by
  set r := (opcodeComponent derefTable).rowInput env with hr
  have hx : eval env (varFromOffset DerefRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine opRow_of_assumptions trivial ⟨⟨r.pc, r.fp, ⟨g * r.pc, r.fp⟩, r.rbc,
    #v[Opcode.deref.busCode, r.o1, r.o2, r.o3, r.fpc, r.ffp, 0, 0, 0, 0, 0, 0, 0],
    [(r.fp * r.o1, r.r1, #v[r.p, 0]),
     (r.p * r.o2, r.r2, #v[(1 + r.fpc + r.ffp) * r.v3[0] + r.fpc * (g ^ 2 * r.pc) + r.ffp * r.fp,
          (1 + r.fpc + r.ffp) * r.v3[1]]),
     (r.fp * r.o3, r.r3, r.v3)], []⟩,
    ?_, rfl, by simp, ?_⟩
  · rw [rowSends_mk, deref_sends_gen _ _ _ _ hx]
    simp [RowRec.sends, sendsOf, gatedSends, memMsgOf, bcMsgOf]
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : DerefRefines (imageOf env.data).2 r
      ((opcodeComponent derefTable).rowOutput env) := hs
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
    · simp [busEntry, hflags]
    · rw [← show ((opcodeComponent derefTable).rowOutput env) = ⟨g * r.pc, r.fp⟩ from hnext]
      exact hexec

/-- **The `KECCAK` table without its assumption**: the same row circuit, sound for the flags, the
bindings and the fall-through alone, whatever the output lanes hold (the reduction-blind reading
of a row). -/
def keccakTableFree : GeneralFormalCircuit K KeccakRow Registers :=
  { keccakTable with
    Assumptions := fun _ _ ↦ True
    Spec := fun r next data ↦ (∃ inOdd outOdd outCells, KeccakFlags r inOdd outOdd outCells ∧
      KeccakBindings (imageOf data).2 r inOdd outOdd outCells) ∧
      next = Registers.next ⟨r.pc, r.fp⟩
    soundness := by
      circuit_proof_start [keccakTable, StatePull, StatePush, MemPull, MemPush, BytecodePull,
        BytecodePush, memRead, memReadIf, bytecodeRead]
      obtain ⟨⟨ins, hdec⟩, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩ := h_holds
      obtain ⟨_, _, hom, _, _, _, _, hoi, hoo, hot, hoa, _, hlin, hlout, _, _⟩ := h_input
      subst hom hlin hlout
      rw [keccak_tuple] at hdec
      obtain ⟨inOdd, outOdd, oc, hfi, hfo, hft, hfa⟩ := keccak_flags_of_decode rfl hdec
      simp only [hfi] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
      simp only [hfo] at h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
      simp only [hft] at h14
      simp only [hfa] at h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
      refine ⟨?_, ?_⟩
      swap
      · -- The gated pulls' requirements: the flags are `0` or `1`, so the multiplicity is `0` or `1`.
        obtain ⟨b1, b2⟩ := keccakOutputFlags_bits oc
        rw [hft, hfa]
        rcases b1 with b1 | b1 <;> rcases b2 with b2 | b2 <;> simp [b1, b2]
      refine ⟨⟨inOdd, outOdd, oc, ⟨hfi, hfo, hft, hfa⟩, ⟨fun c ↦ ?_, fun c hc ↦ ?_⟩⟩, rfl⟩
      · fin_cases c
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, KeccakRow.oms, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h0 ⊢ <;> exact h0
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, KeccakRow.oms, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h1 ⊢ <;> exact h1
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, KeccakRow.oms, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h2 ⊢ <;> exact h2
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, KeccakRow.oms, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h3 ⊢ <;> exact h3
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, pow_zero, one_mul] at h4 ⊢ <;> exact h4
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul, pow_one] at h5 ⊢ <;> exact h5
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h6 ⊢ <;> exact h6
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h7 ⊢ <;> exact h7
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h8 ⊢ <;> exact h8
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, Vector.getElem_map, pow_zero, one_mul] at h9 ⊢ <;> exact h9
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, Vector.getElem_map, pow_one] at h10 ⊢ <;> exact h10
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, Vector.getElem_map] at h11 ⊢ <;> exact h11
        · cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, Vector.getElem_map] at h12 ⊢ <;> exact h12
      · fin_cases c
        · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, pow_zero, one_mul] at h13 ⊢ <;> exact h13
        · have h14 := h14 (by rw [gate_two (by simpa using hc)])
          · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul, pow_one] at h14 ⊢ <;> exact h14
        · have h15 := h15 (by rw [gate_all (by simp at hc; omega)])
          · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h15 ⊢ <;> exact h15
        · have h16 := h16 (by rw [gate_all (by simp at hc; omega)])
          · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h16 ⊢ <;> exact h16
        · have h17 := h17 (by rw [gate_all (by simp at hc; omega)])
          · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h17 ⊢ <;> exact h17
        · have h18 := h18 (by rw [gate_all (by simp at hc; omega)])
          · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h18 ⊢ <;> exact h18
        · have h19 := h19 (by rw [gate_all (by simp at hc; omega)])
          · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h19 ⊢ <;> exact h19
        · have h20 := h20 (by rw [gate_all (by simp at hc; omega)])
          · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h20 ⊢ <;> exact h20
        · have h21 := h21 (by rw [gate_all (by simp at hc; omega)])
          · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h21 ⊢ <;> exact h21
        · have h22 := h22 (by rw [gate_all (by simp at hc; omega)])
          · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, Vector.getElem_map] at h22 ⊢ <;> exact h22
        · have h23 := h23 (by rw [gate_all (by simp at hc; omega)])
          · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, Vector.getElem_map] at h23 ⊢ <;> exact h23
        · have h24 := h24 (by rw [gate_all (by simp at hc; omega)])
          · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, Vector.getElem_map] at h24 ⊢ <;> exact h24
        · have h25 := h25 (by rw [gate_all (by simp at hc; omega)])
          · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, Vector.getElem_map] at h25 ⊢ <;> exact h25 }

/-- The cells of lanes in a layout satisfy the reduction-blind check: the written cells' free limb
is zero; the cells past those written are not read and are `0`. -/
theorem freeLimbZero_laneCells (L' : Fin 25 → K) (outOdd : Bool) (outCells : KeccakOutputCells) :
    FreeLimbZero (fun c ↦ if c.val < outCells.cellCount then laneCells L' outOdd 0 c else 0) outOdd
      outCells := by
  have h0 : 0 < outCells.cellCount := by cases outCells <;> decide
  cases outOdd
  · intro h8
    simp [h8, laneCells, cellLanes, laneLimb, limb_ofLimbs]
  · simp [FreeLimbZero, h0, laneCells, cellLanes, laneLimb, limb_ofLimbs]

/-- A bound `KECCAK` row executes under the reduction-blind semantics. -/
theorem keccak_free_exec {κ : ℕ} {mem : MemoryImage κ} {r : KeccakRow K} {inOdd outOdd : Bool}
    {outCells : KeccakOutputCells} (h : KeccakBindings mem r inOdd outOdd outCells) :
    executeWithB keccakFree mem.read ⟨r.pc, r.fp⟩
      (.keccak r.oms r.otail r.ob8 r.ocap r.oout inOdd outOdd outCells) =
        some (Registers.next ⟨r.pc, r.fp⟩) := by
  have hin := (readCells_eq_some_iff mem.read r.fp (keccakInputCellOffset r.oms r.otail r.ob8
      r.ocap)
    (laneCells r.inLanes inOdd r.free)).mpr h.in_eq
  have hout := (readFirstCells_eq_some_iff mem.read r.fp (fun c ↦ g ^ c.val * r.oout)
    outCells.cellCount
    (fun c ↦ if c.val < outCells.cellCount then laneCells r.outLanes outOdd 0 c else 0)).mpr
      ⟨fun c hc ↦ by simp only [hc, ↓reduceIte]; exact h.out_eq c hc,
        fun c hc ↦ by split_ifs <;> first | omega | rfl⟩
  simp only [executeWithB, keccakFree, hin, hout, Option.bind_eq_bind, Option.bind_some]
  unfold guard
  simp only [freeLimbZero_laneCells, ↓reduceIte]
  rfl

/-- The record of a `KECCAK` row: the state step, the bytecode read of its thirteen coordinates,
the thirteen cells read and output cell `0` as reads, and output cells `1` (gate `out_two`) and
`2..13` (gate `out_all`) as gated reads. -/
def keccakRecOf (r : KeccakRow K) : RowRec :=
  ⟨r.pc, r.fp, ⟨g * r.pc, r.fp⟩, r.rbc,
    #v[Opcode.keccak.busCode, r.om[0], r.om[1], r.om[2], r.om[3], r.otail, r.ob8, r.ocap, r.oout,
      r.oddIn, r.oddOut, r.outTwo, r.outAll],
    [(r.fp * r.om[0], r.cnt[0], #v[r.lin[0] + r.oddIn * r.lin[0] + r.oddIn * r.free, r.lin[1] + r.oddIn * r.lin[1] + r.oddIn * r.lin[0]]),
     (r.fp * r.om[1], r.cnt[1], #v[r.lin[2] + r.oddIn * r.lin[2] + r.oddIn * r.lin[1], r.lin[3] + r.oddIn * r.lin[3] + r.oddIn * r.lin[2]]),
     (r.fp * r.om[2], r.cnt[2], #v[r.lin[4] + r.oddIn * r.lin[4] + r.oddIn * r.lin[3], r.lin[5] + r.oddIn * r.lin[5] + r.oddIn * r.lin[4]]),
     (r.fp * r.om[3], r.cnt[3], #v[r.lin[6] + r.oddIn * r.lin[6] + r.oddIn * r.lin[5], r.lin[7] + r.oddIn * r.lin[7] + r.oddIn * r.lin[6]]),
     (r.fp * (g ^ 0 * r.otail), r.cnt[4], #v[r.lin[8] + r.oddIn * r.lin[8] + r.oddIn * r.lin[7], r.lin[9] + r.oddIn * r.lin[9] + r.oddIn * r.lin[8]]),
     (r.fp * (g ^ 1 * r.otail), r.cnt[5], #v[r.lin[10] + r.oddIn * r.lin[10] + r.oddIn * r.lin[9], r.lin[11] + r.oddIn * r.lin[11] + r.oddIn * r.lin[10]]),
     (r.fp * (g ^ 2 * r.otail), r.cnt[6], #v[r.lin[12] + r.oddIn * r.lin[12] + r.oddIn * r.lin[11], r.lin[13] + r.oddIn * r.lin[13] + r.oddIn * r.lin[12]]),
     (r.fp * (g ^ 3 * r.otail), r.cnt[7], #v[r.lin[14] + r.oddIn * r.lin[14] + r.oddIn * r.lin[13], r.lin[15] + r.oddIn * r.lin[15] + r.oddIn * r.lin[14]]),
     (r.fp * r.ob8, r.cnt[8], #v[r.lin[16] + r.oddIn * r.lin[16] + r.oddIn * r.lin[15], r.free + r.oddIn * r.free + r.oddIn * r.lin[16]]),
     (r.fp * (g ^ 0 * r.ocap), r.cnt[9], #v[r.lin[17], r.lin[18]]),
     (r.fp * (g ^ 1 * r.ocap), r.cnt[10], #v[r.lin[19], r.lin[20]]),
     (r.fp * (g ^ 2 * r.ocap), r.cnt[11], #v[r.lin[21], r.lin[22]]),
     (r.fp * (g ^ 3 * r.ocap), r.cnt[12], #v[r.lin[23], r.lin[24]]),
     (r.fp * (g ^ 0 * r.oout), r.cnt[13], #v[r.lout[0] + r.oddOut * r.lout[0], r.lout[1] + r.oddOut * r.lout[1] + r.oddOut * r.lout[0]])],
    [(r.outTwo, r.fp * (g ^ 1 * r.oout), r.cnt[14], #v[r.lout[2] + r.oddOut * r.lout[2] + r.oddOut * r.lout[1], r.lout[3] + r.oddOut * r.lout[3] + r.oddOut * r.lout[2]]),
     (r.outAll, r.fp * (g ^ 2 * r.oout), r.cnt[15], #v[r.lout[4] + r.oddOut * r.lout[4] + r.oddOut * r.lout[3], r.lout[5] + r.oddOut * r.lout[5] + r.oddOut * r.lout[4]]),
     (r.outAll, r.fp * (g ^ 3 * r.oout), r.cnt[16], #v[r.lout[6] + r.oddOut * r.lout[6] + r.oddOut * r.lout[5], r.lout[7] + r.oddOut * r.lout[7] + r.oddOut * r.lout[6]]),
     (r.outAll, r.fp * (g ^ 4 * r.oout), r.cnt[17], #v[r.lout[8] + r.oddOut * r.lout[8] + r.oddOut * r.lout[7], r.lout[9] + r.oddOut * r.lout[9] + r.oddOut * r.lout[8]]),
     (r.outAll, r.fp * (g ^ 5 * r.oout), r.cnt[18], #v[r.lout[10] + r.oddOut * r.lout[10] + r.oddOut * r.lout[9], r.lout[11] + r.oddOut * r.lout[11] + r.oddOut * r.lout[10]]),
     (r.outAll, r.fp * (g ^ 6 * r.oout), r.cnt[19], #v[r.lout[12] + r.oddOut * r.lout[12] + r.oddOut * r.lout[11], r.lout[13] + r.oddOut * r.lout[13] + r.oddOut * r.lout[12]]),
     (r.outAll, r.fp * (g ^ 7 * r.oout), r.cnt[20], #v[r.lout[14] + r.oddOut * r.lout[14] + r.oddOut * r.lout[13], r.lout[15] + r.oddOut * r.lout[15] + r.oddOut * r.lout[14]]),
     (r.outAll, r.fp * (g ^ 8 * r.oout), r.cnt[21], #v[r.lout[16] + r.oddOut * r.lout[16] + r.oddOut * r.lout[15], r.oddOut * r.lout[16]]),
     (r.outAll, r.fp * (g ^ 9 * r.oout), r.cnt[22], #v[r.lout[17], r.lout[18]]),
     (r.outAll, r.fp * (g ^ 10 * r.oout), r.cnt[23], #v[r.lout[19], r.lout[20]]),
     (r.outAll, r.fp * (g ^ 11 * r.oout), r.cnt[24], #v[r.lout[21], r.lout[22]]),
     (r.outAll, r.fp * (g ^ 12 * r.oout), r.cnt[25], #v[r.lout[23], r.lout[24]])]⟩

/-- A read is a read the row makes. -/
theorem RowRec.mem_real_of_read {x : RowRec} {y : K × K × Vector K 2} (h : y ∈ x.reads) :
    memMsgOf y.1 y.2.1 y.2.2 ∈ x.real.map fun y ↦ memMsgOf y.1 y.2.1 y.2.2 :=
  List.mem_map_of_mem (List.mem_append_left _ h)

/-- A gated read at flag `1` is a read the row makes. -/
theorem RowRec.mem_real_of_gated {x : RowRec} {y : K × K × K × Vector K 2} (h : y ∈ x.gated)
    (h1 : y.1 = 1) :
    memMsgOf y.2.1 y.2.2.1 y.2.2.2 ∈ x.real.map fun y ↦ memMsgOf y.1 y.2.1 y.2.2 :=
  List.mem_map_of_mem (List.mem_append_right _
    (List.mem_map_of_mem (List.mem_filter.mpr ⟨h, by simp [h1]⟩)))

set_option maxHeartbeats 16000000 in
/-- The interactions of the `KECCAK` row circuit, as `((channel name, message), multiplicity)`, in
closed form: a memory pull's multiplicity is `1`, or `out_two`, `out_all` for a gated output
cell. -/
theorem keccak_mults_gen (x : Var KeccakRow K) (env : Environment K) (n : ℕ) (r : KeccakRow K)
    (hx : eval env x = r) :
    (((keccakTable.main x).operations n).interactionValues env).map
      (fun i ↦ ((i.channel.name, i.msg), i.mult)) =
      [((StatePull.name, #[r.pc, r.fp]), (1 : K)),
       ((StatePush.name, #[g * r.pc, r.fp]), (1 : K)),
       ((BytecodePull.name, #[r.pc, r.rbc, Opcode.keccak.busCode, r.om[0], r.om[1], r.om[2], r.om[3], r.otail, r.ob8,
          r.ocap, r.oout, r.oddIn, r.oddOut, r.outTwo, r.outAll]), (1 : K)),
       ((BytecodePush.name, #[r.pc, g * r.rbc, Opcode.keccak.busCode, r.om[0], r.om[1], r.om[2], r.om[3],
            r.otail, r.ob8,
          r.ocap, r.oout, r.oddIn, r.oddOut, r.outTwo, r.outAll]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * r.om[0]) (r.cnt[0]) #v[r.lin[0] + r.oddIn * r.lin[0] + r.oddIn * r.free, r.lin[1] + r.oddIn * r.lin[1] + r.oddIn * r.lin[0]]), (1 : K)),
       ((MemPush.name, memMsgOf (r.fp * r.om[0]) (g * r.cnt[0]) #v[r.lin[0] + r.oddIn * r.lin[0] + r.oddIn * r.free, r.lin[1] + r.oddIn * r.lin[1] + r.oddIn * r.lin[0]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * r.om[1]) (r.cnt[1]) #v[r.lin[2] + r.oddIn * r.lin[2] + r.oddIn * r.lin[1], r.lin[3] + r.oddIn * r.lin[3] + r.oddIn * r.lin[2]]), (1 : K)),
       ((MemPush.name, memMsgOf (r.fp * r.om[1]) (g * r.cnt[1]) #v[r.lin[2] + r.oddIn * r.lin[2] + r.oddIn * r.lin[1], r.lin[3] + r.oddIn * r.lin[3] + r.oddIn * r.lin[2]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * r.om[2]) (r.cnt[2]) #v[r.lin[4] + r.oddIn * r.lin[4] + r.oddIn * r.lin[3], r.lin[5] + r.oddIn * r.lin[5] + r.oddIn * r.lin[4]]), (1 : K)),
       ((MemPush.name, memMsgOf (r.fp * r.om[2]) (g * r.cnt[2]) #v[r.lin[4] + r.oddIn * r.lin[4] + r.oddIn * r.lin[3], r.lin[5] + r.oddIn * r.lin[5] + r.oddIn * r.lin[4]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * r.om[3]) (r.cnt[3]) #v[r.lin[6] + r.oddIn * r.lin[6] + r.oddIn * r.lin[5], r.lin[7] + r.oddIn * r.lin[7] + r.oddIn * r.lin[6]]), (1 : K)),
       ((MemPush.name, memMsgOf (r.fp * r.om[3]) (g * r.cnt[3]) #v[r.lin[6] + r.oddIn * r.lin[6] + r.oddIn * r.lin[5], r.lin[7] + r.oddIn * r.lin[7] + r.oddIn * r.lin[6]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * (g ^ 0 * r.otail)) (r.cnt[4]) #v[r.lin[8] + r.oddIn * r.lin[8] + r.oddIn * r.lin[7], r.lin[9] + r.oddIn * r.lin[9] + r.oddIn * r.lin[8]]), (1 : K)),
       ((MemPush.name, memMsgOf (r.fp * (g ^ 0 * r.otail)) (g * r.cnt[4]) #v[r.lin[8] + r.oddIn * r.lin[8] + r.oddIn * r.lin[7], r.lin[9] + r.oddIn * r.lin[9] + r.oddIn * r.lin[8]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * (g ^ 1 * r.otail)) (r.cnt[5]) #v[r.lin[10] + r.oddIn * r.lin[10] + r.oddIn * r.lin[9], r.lin[11] + r.oddIn * r.lin[11] + r.oddIn * r.lin[10]]), (1 : K)),
       ((MemPush.name, memMsgOf (r.fp * (g ^ 1 * r.otail)) (g * r.cnt[5]) #v[r.lin[10] + r.oddIn * r.lin[10] + r.oddIn * r.lin[9], r.lin[11] + r.oddIn * r.lin[11] + r.oddIn * r.lin[10]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * (g ^ 2 * r.otail)) (r.cnt[6]) #v[r.lin[12] + r.oddIn * r.lin[12] + r.oddIn * r.lin[11], r.lin[13] + r.oddIn * r.lin[13] + r.oddIn * r.lin[12]]), (1 : K)),
       ((MemPush.name, memMsgOf (r.fp * (g ^ 2 * r.otail)) (g * r.cnt[6]) #v[r.lin[12] + r.oddIn * r.lin[12] + r.oddIn * r.lin[11], r.lin[13] + r.oddIn * r.lin[13] + r.oddIn * r.lin[12]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * (g ^ 3 * r.otail)) (r.cnt[7]) #v[r.lin[14] + r.oddIn * r.lin[14] + r.oddIn * r.lin[13], r.lin[15] + r.oddIn * r.lin[15] + r.oddIn * r.lin[14]]), (1 : K)),
       ((MemPush.name, memMsgOf (r.fp * (g ^ 3 * r.otail)) (g * r.cnt[7]) #v[r.lin[14] + r.oddIn * r.lin[14] + r.oddIn * r.lin[13], r.lin[15] + r.oddIn * r.lin[15] + r.oddIn * r.lin[14]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * r.ob8) (r.cnt[8]) #v[r.lin[16] + r.oddIn * r.lin[16] + r.oddIn * r.lin[15], r.free + r.oddIn * r.free + r.oddIn * r.lin[16]]), (1 : K)),
       ((MemPush.name, memMsgOf (r.fp * r.ob8) (g * r.cnt[8]) #v[r.lin[16] + r.oddIn * r.lin[16] + r.oddIn * r.lin[15], r.free + r.oddIn * r.free + r.oddIn * r.lin[16]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * (g ^ 0 * r.ocap)) (r.cnt[9]) #v[r.lin[17], r.lin[18]]), (1 : K)),
       ((MemPush.name, memMsgOf (r.fp * (g ^ 0 * r.ocap)) (g * r.cnt[9]) #v[r.lin[17], r.lin[18]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * (g ^ 1 * r.ocap)) (r.cnt[10]) #v[r.lin[19], r.lin[20]]), (1 : K)),
       ((MemPush.name, memMsgOf (r.fp * (g ^ 1 * r.ocap)) (g * r.cnt[10]) #v[r.lin[19], r.lin[20]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * (g ^ 2 * r.ocap)) (r.cnt[11]) #v[r.lin[21], r.lin[22]]), (1 : K)),
       ((MemPush.name, memMsgOf (r.fp * (g ^ 2 * r.ocap)) (g * r.cnt[11]) #v[r.lin[21], r.lin[22]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * (g ^ 3 * r.ocap)) (r.cnt[12]) #v[r.lin[23], r.lin[24]]), (1 : K)),
       ((MemPush.name, memMsgOf (r.fp * (g ^ 3 * r.ocap)) (g * r.cnt[12]) #v[r.lin[23], r.lin[24]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * (g ^ 0 * r.oout)) (r.cnt[13]) #v[r.lout[0] + r.oddOut * r.lout[0], r.lout[1] + r.oddOut * r.lout[1] + r.oddOut * r.lout[0]]), (1 : K)),
       ((MemPush.name, memMsgOf (r.fp * (g ^ 0 * r.oout)) (g * r.cnt[13]) #v[r.lout[0] + r.oddOut * r.lout[0], r.lout[1] + r.oddOut * r.lout[1] + r.oddOut * r.lout[0]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * (g ^ 1 * r.oout)) (r.cnt[14]) #v[r.lout[2] + r.oddOut * r.lout[2] + r.oddOut * r.lout[1], r.lout[3] + r.oddOut * r.lout[3] + r.oddOut * r.lout[2]]), r.outTwo),
       ((MemPush.name, memMsgOf (r.fp * (g ^ 1 * r.oout)) (r.cnt[14] + g * (r.outTwo * r.cnt[14]) + r.outTwo * r.cnt[14]) #v[r.lout[2] + r.oddOut * r.lout[2] + r.oddOut * r.lout[1], r.lout[3] + r.oddOut * r.lout[3] + r.oddOut * r.lout[2]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * (g ^ 2 * r.oout)) (r.cnt[15]) #v[r.lout[4] + r.oddOut * r.lout[4] + r.oddOut * r.lout[3], r.lout[5] + r.oddOut * r.lout[5] + r.oddOut * r.lout[4]]), r.outAll),
       ((MemPush.name, memMsgOf (r.fp * (g ^ 2 * r.oout)) (r.cnt[15] + g * (r.outAll * r.cnt[15]) + r.outAll * r.cnt[15]) #v[r.lout[4] + r.oddOut * r.lout[4] + r.oddOut * r.lout[3], r.lout[5] + r.oddOut * r.lout[5] + r.oddOut * r.lout[4]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * (g ^ 3 * r.oout)) (r.cnt[16]) #v[r.lout[6] + r.oddOut * r.lout[6] + r.oddOut * r.lout[5], r.lout[7] + r.oddOut * r.lout[7] + r.oddOut * r.lout[6]]), r.outAll),
       ((MemPush.name, memMsgOf (r.fp * (g ^ 3 * r.oout)) (r.cnt[16] + g * (r.outAll * r.cnt[16]) + r.outAll * r.cnt[16]) #v[r.lout[6] + r.oddOut * r.lout[6] + r.oddOut * r.lout[5], r.lout[7] + r.oddOut * r.lout[7] + r.oddOut * r.lout[6]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * (g ^ 4 * r.oout)) (r.cnt[17]) #v[r.lout[8] + r.oddOut * r.lout[8] + r.oddOut * r.lout[7], r.lout[9] + r.oddOut * r.lout[9] + r.oddOut * r.lout[8]]), r.outAll),
       ((MemPush.name, memMsgOf (r.fp * (g ^ 4 * r.oout)) (r.cnt[17] + g * (r.outAll * r.cnt[17]) + r.outAll * r.cnt[17]) #v[r.lout[8] + r.oddOut * r.lout[8] + r.oddOut * r.lout[7], r.lout[9] + r.oddOut * r.lout[9] + r.oddOut * r.lout[8]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * (g ^ 5 * r.oout)) (r.cnt[18]) #v[r.lout[10] + r.oddOut * r.lout[10] + r.oddOut * r.lout[9], r.lout[11] + r.oddOut * r.lout[11] + r.oddOut * r.lout[10]]), r.outAll),
       ((MemPush.name, memMsgOf (r.fp * (g ^ 5 * r.oout)) (r.cnt[18] + g * (r.outAll * r.cnt[18]) + r.outAll * r.cnt[18]) #v[r.lout[10] + r.oddOut * r.lout[10] + r.oddOut * r.lout[9], r.lout[11] + r.oddOut * r.lout[11] + r.oddOut * r.lout[10]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * (g ^ 6 * r.oout)) (r.cnt[19]) #v[r.lout[12] + r.oddOut * r.lout[12] + r.oddOut * r.lout[11], r.lout[13] + r.oddOut * r.lout[13] + r.oddOut * r.lout[12]]), r.outAll),
       ((MemPush.name, memMsgOf (r.fp * (g ^ 6 * r.oout)) (r.cnt[19] + g * (r.outAll * r.cnt[19]) + r.outAll * r.cnt[19]) #v[r.lout[12] + r.oddOut * r.lout[12] + r.oddOut * r.lout[11], r.lout[13] + r.oddOut * r.lout[13] + r.oddOut * r.lout[12]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * (g ^ 7 * r.oout)) (r.cnt[20]) #v[r.lout[14] + r.oddOut * r.lout[14] + r.oddOut * r.lout[13], r.lout[15] + r.oddOut * r.lout[15] + r.oddOut * r.lout[14]]), r.outAll),
       ((MemPush.name, memMsgOf (r.fp * (g ^ 7 * r.oout)) (r.cnt[20] + g * (r.outAll * r.cnt[20]) + r.outAll * r.cnt[20]) #v[r.lout[14] + r.oddOut * r.lout[14] + r.oddOut * r.lout[13], r.lout[15] + r.oddOut * r.lout[15] + r.oddOut * r.lout[14]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * (g ^ 8 * r.oout)) (r.cnt[21]) #v[r.lout[16] + r.oddOut * r.lout[16] + r.oddOut * r.lout[15], r.oddOut * r.lout[16]]), r.outAll),
       ((MemPush.name, memMsgOf (r.fp * (g ^ 8 * r.oout)) (r.cnt[21] + g * (r.outAll * r.cnt[21]) + r.outAll * r.cnt[21]) #v[r.lout[16] + r.oddOut * r.lout[16] + r.oddOut * r.lout[15], r.oddOut * r.lout[16]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * (g ^ 9 * r.oout)) (r.cnt[22]) #v[r.lout[17], r.lout[18]]), r.outAll),
       ((MemPush.name, memMsgOf (r.fp * (g ^ 9 * r.oout)) (r.cnt[22] + g * (r.outAll * r.cnt[22]) + r.outAll * r.cnt[22]) #v[r.lout[17], r.lout[18]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * (g ^ 10 * r.oout)) (r.cnt[23]) #v[r.lout[19], r.lout[20]]), r.outAll),
       ((MemPush.name, memMsgOf (r.fp * (g ^ 10 * r.oout)) (r.cnt[23] + g * (r.outAll * r.cnt[23]) + r.outAll * r.cnt[23]) #v[r.lout[19], r.lout[20]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * (g ^ 11 * r.oout)) (r.cnt[24]) #v[r.lout[21], r.lout[22]]), r.outAll),
       ((MemPush.name, memMsgOf (r.fp * (g ^ 11 * r.oout)) (r.cnt[24] + g * (r.outAll * r.cnt[24]) + r.outAll * r.cnt[24]) #v[r.lout[21], r.lout[22]]), (1 : K)),
       ((MemPull.name, memMsgOf (r.fp * (g ^ 12 * r.oout)) (r.cnt[25]) #v[r.lout[23], r.lout[24]]), r.outAll),
       ((MemPush.name, memMsgOf (r.fp * (g ^ 12 * r.oout)) (r.cnt[25] + g * (r.outAll * r.cnt[25]) + r.outAll * r.cnt[25]) #v[r.lout[23], r.lout[24]]), (1 : K))] := by
  subst hx
  obtain ⟨pc, fp, om, otail, ob8, ocap, oout, oddIn, oddOut, outTwo, outAll, free, lin, lout, cnt,
    rbc⟩ := x
  simp only [Operations.interactionValues, circuit_norm, keccakTable, memRead, memReadIf,
    bytecodeRead, AbstractInteraction.eval, Vector.toArray_map, regs_toArray, memMsg_toArray,
    bytecodeMsg_toArray, Vector.getElem_map, memMsgOf, -BitVec.reduceNeg]

set_option maxHeartbeats 16000000 in
/-- A `KECCAK` memory pull of multiplicity `1` is a read the row makes: the thirteen cells read and
output cell `0` always, output cell `c ≥ 1` when its gate, which is the pull's multiplicity,
is `1`. -/
theorem keccak_guarded_gen (x : Var KeccakRow K) (env : Environment K) (n : ℕ) (r : KeccakRow K)
    (hx : eval env x = r) :
    ∀ i ∈ ((keccakTable.main x).operations n).interactionValues env,
      i.channel.name = MemPull.name → i.mult = 1 →
        i.msg ∈ (keccakRecOf r).real.map fun y ↦ memMsgOf y.1 y.2.1 y.2.2 := by
  intro i hi hn hm
  have := List.mem_map_of_mem (f := fun i : Interaction K ↦ ((i.channel.name, i.msg), i.mult)) hi
  rw [keccak_mults_gen x env n r hx] at this
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at this
  rcases this with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h2]
    exact List.mem_map_of_mem (f := fun y ↦ memMsgOf y.1 y.2.1 y.2.2) (a := ((r.fp * r.om[0]), (r.cnt[0]), #v[r.lin[0] + r.oddIn * r.lin[0] + r.oddIn * r.free, r.lin[1] + r.oddIn * r.lin[1] + r.oddIn * r.lin[0]]))
      (List.mem_append_left _ (by simp only [keccakRecOf, List.mem_cons, true_or]))
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h2]
    exact List.mem_map_of_mem (f := fun y ↦ memMsgOf y.1 y.2.1 y.2.2) (a := ((r.fp * r.om[1]), (r.cnt[1]), #v[r.lin[2] + r.oddIn * r.lin[2] + r.oddIn * r.lin[1], r.lin[3] + r.oddIn * r.lin[3] + r.oddIn * r.lin[2]]))
      (List.mem_append_left _ (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]))
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h2]
    exact List.mem_map_of_mem (f := fun y ↦ memMsgOf y.1 y.2.1 y.2.2) (a := ((r.fp * r.om[2]), (r.cnt[2]), #v[r.lin[4] + r.oddIn * r.lin[4] + r.oddIn * r.lin[3], r.lin[5] + r.oddIn * r.lin[5] + r.oddIn * r.lin[4]]))
      (List.mem_append_left _ (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]))
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h2]
    exact List.mem_map_of_mem (f := fun y ↦ memMsgOf y.1 y.2.1 y.2.2) (a := ((r.fp * r.om[3]), (r.cnt[3]), #v[r.lin[6] + r.oddIn * r.lin[6] + r.oddIn * r.lin[5], r.lin[7] + r.oddIn * r.lin[7] + r.oddIn * r.lin[6]]))
      (List.mem_append_left _ (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]))
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h2]
    exact List.mem_map_of_mem (f := fun y ↦ memMsgOf y.1 y.2.1 y.2.2) (a := ((r.fp * (g ^ 0 * r.otail)), (r.cnt[4]), #v[r.lin[8] + r.oddIn * r.lin[8] + r.oddIn * r.lin[7], r.lin[9] + r.oddIn * r.lin[9] + r.oddIn * r.lin[8]]))
      (List.mem_append_left _ (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]))
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h2]
    exact List.mem_map_of_mem (f := fun y ↦ memMsgOf y.1 y.2.1 y.2.2) (a := ((r.fp * (g ^ 1 * r.otail)), (r.cnt[5]), #v[r.lin[10] + r.oddIn * r.lin[10] + r.oddIn * r.lin[9], r.lin[11] + r.oddIn * r.lin[11] + r.oddIn * r.lin[10]]))
      (List.mem_append_left _ (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]))
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h2]
    exact List.mem_map_of_mem (f := fun y ↦ memMsgOf y.1 y.2.1 y.2.2) (a := ((r.fp * (g ^ 2 * r.otail)), (r.cnt[6]), #v[r.lin[12] + r.oddIn * r.lin[12] + r.oddIn * r.lin[11], r.lin[13] + r.oddIn * r.lin[13] + r.oddIn * r.lin[12]]))
      (List.mem_append_left _ (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]))
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h2]
    exact List.mem_map_of_mem (f := fun y ↦ memMsgOf y.1 y.2.1 y.2.2) (a := ((r.fp * (g ^ 3 * r.otail)), (r.cnt[7]), #v[r.lin[14] + r.oddIn * r.lin[14] + r.oddIn * r.lin[13], r.lin[15] + r.oddIn * r.lin[15] + r.oddIn * r.lin[14]]))
      (List.mem_append_left _ (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]))
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h2]
    exact List.mem_map_of_mem (f := fun y ↦ memMsgOf y.1 y.2.1 y.2.2) (a := ((r.fp * r.ob8), (r.cnt[8]), #v[r.lin[16] + r.oddIn * r.lin[16] + r.oddIn * r.lin[15], r.free + r.oddIn * r.free + r.oddIn * r.lin[16]]))
      (List.mem_append_left _ (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]))
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h2]
    exact List.mem_map_of_mem (f := fun y ↦ memMsgOf y.1 y.2.1 y.2.2) (a := ((r.fp * (g ^ 0 * r.ocap)), (r.cnt[9]), #v[r.lin[17], r.lin[18]]))
      (List.mem_append_left _ (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]))
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h2]
    exact List.mem_map_of_mem (f := fun y ↦ memMsgOf y.1 y.2.1 y.2.2) (a := ((r.fp * (g ^ 1 * r.ocap)), (r.cnt[10]), #v[r.lin[19], r.lin[20]]))
      (List.mem_append_left _ (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]))
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h2]
    exact List.mem_map_of_mem (f := fun y ↦ memMsgOf y.1 y.2.1 y.2.2) (a := ((r.fp * (g ^ 2 * r.ocap)), (r.cnt[11]), #v[r.lin[21], r.lin[22]]))
      (List.mem_append_left _ (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]))
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h2]
    exact List.mem_map_of_mem (f := fun y ↦ memMsgOf y.1 y.2.1 y.2.2) (a := ((r.fp * (g ^ 3 * r.ocap)), (r.cnt[12]), #v[r.lin[23], r.lin[24]]))
      (List.mem_append_left _ (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]))
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h2]
    exact List.mem_map_of_mem (f := fun y ↦ memMsgOf y.1 y.2.1 y.2.2) (a := ((r.fp * (g ^ 0 * r.oout)), (r.cnt[13]), #v[r.lout[0] + r.oddOut * r.lout[0], r.lout[1] + r.oddOut * r.lout[1] + r.oddOut * r.lout[0]]))
      (List.mem_append_left _ (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]))
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h3] at hm
    rw [h2]
    exact RowRec.mem_real_of_gated (x := keccakRecOf r) (y := (r.outTwo, (r.fp * (g ^ 1 * r.oout)), (r.cnt[14]), #v[r.lout[2] + r.oddOut * r.lout[2] + r.oddOut * r.lout[1], r.lout[3] + r.oddOut * r.lout[3] + r.oddOut * r.lout[2]]))
      (by simp only [keccakRecOf, List.mem_cons, true_or]) hm
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h3] at hm
    rw [h2]
    exact RowRec.mem_real_of_gated (x := keccakRecOf r) (y := (r.outAll, (r.fp * (g ^ 2 * r.oout)), (r.cnt[15]), #v[r.lout[4] + r.oddOut * r.lout[4] + r.oddOut * r.lout[3], r.lout[5] + r.oddOut * r.lout[5] + r.oddOut * r.lout[4]]))
      (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]) hm
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h3] at hm
    rw [h2]
    exact RowRec.mem_real_of_gated (x := keccakRecOf r) (y := (r.outAll, (r.fp * (g ^ 3 * r.oout)), (r.cnt[16]), #v[r.lout[6] + r.oddOut * r.lout[6] + r.oddOut * r.lout[5], r.lout[7] + r.oddOut * r.lout[7] + r.oddOut * r.lout[6]]))
      (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]) hm
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h3] at hm
    rw [h2]
    exact RowRec.mem_real_of_gated (x := keccakRecOf r) (y := (r.outAll, (r.fp * (g ^ 4 * r.oout)), (r.cnt[17]), #v[r.lout[8] + r.oddOut * r.lout[8] + r.oddOut * r.lout[7], r.lout[9] + r.oddOut * r.lout[9] + r.oddOut * r.lout[8]]))
      (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]) hm
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h3] at hm
    rw [h2]
    exact RowRec.mem_real_of_gated (x := keccakRecOf r) (y := (r.outAll, (r.fp * (g ^ 5 * r.oout)), (r.cnt[18]), #v[r.lout[10] + r.oddOut * r.lout[10] + r.oddOut * r.lout[9], r.lout[11] + r.oddOut * r.lout[11] + r.oddOut * r.lout[10]]))
      (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]) hm
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h3] at hm
    rw [h2]
    exact RowRec.mem_real_of_gated (x := keccakRecOf r) (y := (r.outAll, (r.fp * (g ^ 6 * r.oout)), (r.cnt[19]), #v[r.lout[12] + r.oddOut * r.lout[12] + r.oddOut * r.lout[11], r.lout[13] + r.oddOut * r.lout[13] + r.oddOut * r.lout[12]]))
      (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]) hm
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h3] at hm
    rw [h2]
    exact RowRec.mem_real_of_gated (x := keccakRecOf r) (y := (r.outAll, (r.fp * (g ^ 7 * r.oout)), (r.cnt[20]), #v[r.lout[14] + r.oddOut * r.lout[14] + r.oddOut * r.lout[13], r.lout[15] + r.oddOut * r.lout[15] + r.oddOut * r.lout[14]]))
      (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]) hm
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h3] at hm
    rw [h2]
    exact RowRec.mem_real_of_gated (x := keccakRecOf r) (y := (r.outAll, (r.fp * (g ^ 8 * r.oout)), (r.cnt[21]), #v[r.lout[16] + r.oddOut * r.lout[16] + r.oddOut * r.lout[15], r.oddOut * r.lout[16]]))
      (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]) hm
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h3] at hm
    rw [h2]
    exact RowRec.mem_real_of_gated (x := keccakRecOf r) (y := (r.outAll, (r.fp * (g ^ 9 * r.oout)), (r.cnt[22]), #v[r.lout[17], r.lout[18]]))
      (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]) hm
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h3] at hm
    rw [h2]
    exact RowRec.mem_real_of_gated (x := keccakRecOf r) (y := (r.outAll, (r.fp * (g ^ 10 * r.oout)), (r.cnt[23]), #v[r.lout[19], r.lout[20]]))
      (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]) hm
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h3] at hm
    rw [h2]
    exact RowRec.mem_real_of_gated (x := keccakRecOf r) (y := (r.outAll, (r.fp * (g ^ 11 * r.oout)), (r.cnt[24]), #v[r.lout[21], r.lout[22]]))
      (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]) hm
  · rw [h1] at hn; exact absurd hn (by decide)
  · rw [h3] at hm
    rw [h2]
    exact RowRec.mem_real_of_gated (x := keccakRecOf r) (y := (r.outAll, (r.fp * (g ^ 12 * r.oout)), (r.cnt[25]), #v[r.lout[23], r.lout[24]]))
      (by simp only [keccakRecOf, List.mem_cons, true_or, or_true]) hm
  · rw [h1] at hn; exact absurd hn (by decide)


/-- The interactions of the `KECCAK` table's row circuit, at the row variable, are the closed
form's. -/
theorem keccak_rowInteractions (env : Environment K) :
    (opcodeComponent keccakTable).rowOperations.interactions.map (AbstractInteraction.eval env) =
      ((keccakTable.main (varFromOffset KeccakRow 0)).operations (size KeccakRow)).interactionValues
        env := rfl

/-- A `KECCAK` row has the shape and, under the permutation and the guarantees, steps; without the
permutation it is a reduction-blind step. Its gates are the bytecode's output flags, so `0` or `1`
when its bytecode coordinates are an instruction's. -/
theorem keccak_opRow (env : Environment K) : OpRow (opcodeComponent keccakTable) env := by
  set r := (opcodeComponent keccakTable).rowInput env with hr
  have hx : eval env (varFromOffset KeccakRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine ⟨keccakRecOf r, ?_, by simp [keccakRecOf], ?_, ?_, ?_, ?_⟩
  · rw [rowSends_mk, keccak_sends_gen _ _ _ _ hx]
    simp [keccakRecOf, RowRec.sends, sendsOf, gatedSends, gatedCount, memMsgOf, bcMsgOf]
  · rw [keccak_rowInteractions]
    exact keccak_guarded_gen _ env _ r hx
  · rintro ⟨ins, he⟩ y hy
    have hd : decode (keccakRecOf r).e = some ins := by rw [he]; exact decode_entry ins
    obtain ⟨_, _, oc, -, -, h3, h4⟩ := keccak_flags_of_decode rfl hd
    obtain ⟨b1, b2⟩ := keccakOutputFlags_bits oc
    simp only [keccakRecOf, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h3]; exact b1
    all_goals rw [h4]; exact b2
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : KeccakRefines (imageOf env.data).2 r
      ((opcodeComponent keccakTable).rowOutput env) := hs
    have hnext := hs'.bindings.2
    obtain ⟨i, o, oc, ⟨h1, h2, h3, h4⟩, -, hexec⟩ := hs'
    refine ⟨.keccak r.oms r.otail r.ob8 r.ocap r.oout i o oc, ?_, ?_, fun _ ↦ rfl⟩
    · simp [keccakRecOf, busEntry, h1, h2, h3, h4, KeccakRow.oms]
    · show execute (imageOf env.data).2 ⟨r.pc, r.fp⟩ _ = some ⟨g * r.pc, r.fp⟩
      rw [← show ((opcodeComponent keccakTable).rowOutput env) = ⟨g * r.pc, r.fp⟩ from hnext]
      exact hexec
  · intro hc hg
    obtain ⟨⟨⟨i, o, oc, hf, hb⟩, -⟩, -⟩ :=
      Component.weakSoundness (component := (opcodeComponent keccakTableFree)) trivial hc hg
    have hf' : KeccakFlags r i o oc := hf
    have hb' : KeccakBindings (imageOf env.data).2 r i o oc := hb
    obtain ⟨h1, h2, h3, h4⟩ := hf'
    exact ⟨.keccak r.oms r.otail r.ob8 r.ocap r.oout i o oc,
      by simp [keccakRecOf, busEntry, h1, h2, h3, h4, KeccakRow.oms], keccak_free_exec hb',
      fun _ ↦ rfl⟩

/-- The output of the `JUMP` row circuit at a row variable that evaluates to `r`: the successor
selected by the indicator `b`, the local witness at slot `n + 1`. -/
theorem jump_output_gen (x : Var JumpRow K) (env : Environment K) (n : ℕ) (r : JumpRow K)
    (hx : eval env x = r) (b : K) (hb : env.get (n + 1) = b) :
    eval env ((jumpTable.main x).output n) =
      (⟨b * r.vpc + b * (g * r.pc) + g * r.pc, b * r.vfp + b * r.fp + r.fp⟩ : Registers K) := by
  subst hx
  obtain ⟨pc, fp, oc, od, of, vcond, vpc, vfp, rc, rd, rf, rbc⟩ := x
  dsimp only [jumpTable]
  simp only [circuit_norm, memRead, bytecodeRead, hb, -BitVec.reduceNeg]

/-- A `JUMP` row has the shape, its pushed successor the table's output, and under the residuals
and the guarantees steps. -/
theorem jump_opRow (env : Environment K) : OpRow (opcodeComponent jumpTable) env := by
  set r := (opcodeComponent jumpTable).rowInput env with hr
  have hx : eval env (varFromOffset JumpRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine opRow_of_assumptions trivial
    ⟨⟨r.pc, r.fp, (opcodeComponent jumpTable).rowOutput env, r.rbc,
    busEntry (.jump r.oc r.od r.of),
    [(r.fp * r.oc, r.rc, #v[r.vcond, 0]), (r.fp * r.od, r.rd, #v[r.vpc, 0]),
     (r.fp * r.of, r.rf, #v[r.vfp, 0])], []⟩, ?_, rfl, by simp, ?_⟩
  · have ho : (opcodeComponent jumpTable).rowOutput env = _ :=
      jump_output_gen _ env (size JumpRow) r hx _ rfl
    rw [rowSends_mk, jump_sends_gen _ _ _ _ hx _ rfl, ho]
    simp [RowRec.sends, sendsOf, gatedSends, memMsgOf, bcMsgOf, busEntry]
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : JumpRefines (imageOf env.data).2 r
      ((opcodeComponent jumpTable).rowOutput env) := hs
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
theorem xor_channelOk : ∀ a ∈ (opcodeComponent xorTable).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  simp only [opcodeComponent, circuit_norm, xorTable, memRead, bytecodeRead,
    -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

/-- Every interaction of the `MUL_NATIVE` table is on one of the six channels. -/
theorem mul_channelOk : ∀ a ∈ (opcodeComponent mulTable).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  simp only [opcodeComponent, circuit_norm, mulTable, memRead, bytecodeRead,
    -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

/-- Every interaction of the `SET_CONSTANT` table is on one of the six channels. -/
theorem set_channelOk : ∀ a ∈ (opcodeComponent setTable).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  simp only [opcodeComponent, circuit_norm, setTable, memRead, bytecodeRead,
    -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

/-- Every interaction of the `DEREF` table is on one of the six channels. -/
theorem deref_channelOk : ∀ a ∈ (opcodeComponent derefTable).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  simp only [opcodeComponent, circuit_norm, derefTable, memRead, bytecodeRead,
    -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

/-- Every interaction of the `JUMP` table is on one of the six channels. -/
theorem jump_channelOk : ∀ a ∈ (opcodeComponent jumpTable).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  dsimp only [rowOperations_opcodeComponent, opcodeComponent, jumpTable]
  simp only [circuit_norm, memRead, bytecodeRead, -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

/-- Every interaction of the `KECCAK` table is on one of the six channels. -/
theorem keccak_channelOk : ∀ a ∈ (opcodeComponent keccakTable).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  simp only [opcodeComponent, circuit_norm, keccakTable, memRead, memReadIf, bytecodeRead,
    -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

/-! ## The opcode tables of a witness -/

variable {prog : LeanIsaProgram} {κ : ℕ}

/-- Each of the first six tables of a witness has rows of the opcode-table shape, and every
interaction it emits is on one of the six channels. -/
theorem tableAt_opRow (w : Air.Flat.EnsembleWitness (leanIsaEnsemble prog κ)) (j : Fin 8)
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
  · exact ⟨keccak_opRow, keccak_channelOk⟩
  · exact absurd hj (by decide)
  · exact absurd hj (by decide)

end LeanVM.Arithmetization
