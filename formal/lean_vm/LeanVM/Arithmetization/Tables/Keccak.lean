/-
  LeanVM.Arithmetization.Tables.Keccak

  The `KECCAK` table: one Clean component per row, sound and complete for the relation the row
  refines, its bindings to an image together with `execute` of the instruction it names, under
  the named assumption that the Keccak reduction proves the permutation on the row's lanes.
-/

module

public import LeanVM.Arithmetization.Tables.Basic
public import LeanVM.Semantics.KeccakCells
public import Clean.Circuit.Formal
public import Clean.Utils.Tactics.CircuitProofStart
public import Mathlib.Algebra.CharP.Two

@[expose] public section

/-!
# The `KECCAK` table

At leanVM main `40f877dc2c858f013c5974ab71ca594b31a7aec9` and Clean pin `b41c196b`. The
columns are `keccak_columns` (`crates/verifier/src/layout.rs:388-397, 434-443`;
`crates/leanvm_core/src/tables.rs:880-889`, `keccakt`) and the flushes `flushes_keccak`
(`layout.rs:329-371`; `tables.rs:937-961`),
matching specification §7.6 (`doc/leanvm/body/07-instruction-tables.tex`). There is no table constraint: the permutation is
proved by the Keccak reduction (`verify_keccak`) on the input lanes committed to `q_keccak` and
the output lanes the table's claims hand it.

**The row** `KeccakRow` is the column list: `pc, fp`; the operands `o_m₀, …, o_m₃` (`om`),
`o_tail, o_b8, o_cap, o_out`; the two layout flags `odd_in, odd_out`; the two output flags
`out_two, out_all`; the read limb holding no lane (`free`); the 25 input lanes (`lin`) and the 25 output lanes (`lout`); one memory count per
cell, the thirteen read then the thirteen written or cancelled (`cnt`); the bytecode count
`r_bc`. A cell's
limb holding lane `a` in the even layout and `b` in the odd one is `a + flag·a + flag·b`
(`layout_limb`, `layout.rs:311-327`): `a` at `flag = 0`, `b` at `flag = 1`; every cell's top
limb is a literal zero.

**The output cells.** Output cell `0` is a read (`memRead`); cell `1` is a read gated by
`out_two` and cells `2..13` reads gated by `out_all` (`memReadIf`, the Rust's `memory_coords_if`):
the push's counter is `count + flag·count·g + flag·count`, which is `g·count` at `flag = 1`, a
read, and the pull's own `count` at `flag = 0`, where the push and the pull are one tuple and the
pair cancels, touching no cell. The flags reach the row only through the bytecode read, as the
public program's (`decode` of the pulled entry gives `keccakOutputFlags outCells`, each `0` or
`1`), so the prover cannot choose them; a gated pull carries its guarantee at `flag = 1` only.

**The relation.** `KeccakBindings mem r inOdd outOdd outCells` binds the row to an image: the
thirteen cells read hold the input lanes in the layout `inOdd` (`laneCells`, the free limb the
column `free`), the first `outCells.cellCount` cells written hold the output lanes in the layout
`outOdd` (the free limb zero); nothing binds a cell past them. `KeccakRefines mem r next` says the
row's flags are the bits `inOdd`, `outOdd` and the output flags of `outCells`, the row is bound,
and the machine executes `KECCAK` with the row's operands, these layouts and `outCells` to
`next`; `KeccakRefines.bindings` reads the flags, the bindings and the successor `(g·pc, fp)` off
it, and `keccak_refines_of` is its converse given `KeccakRelation r` (the output lanes are
Keccak-f[1600] of the input lanes). A row writing one or two cells binds no more lanes, so the
relation is never read off `KeccakRefines`: it is the reduction's.

**The boundary.** `KeccakRelation r` is the table's `Assumptions` field: the component proves the
memory binding, and the Keccak reduction discharges the permutation for the composed system.
The layout and output flags are read from the bytecode guarantee (the pulled entry decodes, so
they are `0` or `1`, and the output pair one of `(0, 0)`, `(1, 0)`, `(1, 1)`): the one use the
table makes of it.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics

/-! ## The row -/

/-- The `KECCAK` columns, in the order of `keccak_columns` (`layout.rs:434-443`). -/
structure KeccakRow (F : Type) where
  /-- The program counter. -/
  pc : F
  /-- The frame pointer. -/
  fp : F
  /-- The operands `o_m₀, …, o_m₃` of the four addressed cells. -/
  om : Vector F 4
  /-- The operand `o_tail`: four consecutive cells. -/
  otail : F
  /-- The operand `o_b8`. -/
  ob8 : F
  /-- The operand `o_cap`: the four capacity cells. -/
  ocap : F
  /-- The operand `o_out`: the output cells, of which the first one, two or thirteen are
  written. -/
  oout : F
  /-- The layout flag of the cells read. -/
  oddIn : F
  /-- The layout flag of the cells written. -/
  oddOut : F
  /-- Whether output cell `1` is written (`out_two`). -/
  outTwo : F
  /-- Whether output cells `2..13` are written (`out_all`). -/
  outAll : F
  /-- The read limb that holds no lane. -/
  free : F
  /-- The input state's lanes. -/
  lin : Vector F 25
  /-- The output state's lanes. -/
  lout : Vector F 25
  /-- The read counts: the thirteen cells read, then the thirteen output cells. -/
  cnt : Vector F 26
  /-- The read count of the bytecode entry at `pc`. -/
  rbc : F
  deriving ProvableStruct

/-- The input lanes of a row. -/
def KeccakRow.inLanes (r : KeccakRow K) : Fin 25 → K := fun l ↦ r.lin[l]

/-- The output lanes of a row. -/
def KeccakRow.outLanes (r : KeccakRow K) : Fin 25 → K := fun l ↦ r.lout[l]

/-- The four addressed operands of a row. -/
def KeccakRow.oms (r : KeccakRow K) : Fin 4 → K := fun i ↦ r.om[i]

/-- The permutation on a row's lanes, as the Keccak reduction proves it: the output lanes are
Keccak-f[1600] of the input lanes. The named assumption of the table. -/
def KeccakRelation (r : KeccakRow K) : Prop :=
  r.outLanes = stateLanes (keccakF1600 (laneState r.inLanes))

/-! ## The relation -/

/-- The row's bindings to an image, in the layouts `inOdd`, `outOdd`, writing the output cells
`outCells`: the cells read hold the input lanes, the first `outCells.cellCount` cells written the
output lanes. -/
structure KeccakBindings {κ : ℕ} (mem : MemoryImage κ) (r : KeccakRow K) (inOdd outOdd : Bool)
    (outCells : KeccakOutputCells) : Prop where
  /-- Cell `c` read holds the input lanes' cell `c` in the layout `inOdd`. -/
  in_eq : ∀ c : Fin 13, mem.read (r.fp * keccakInputCellOffset r.oms r.otail r.ob8 r.ocap c) =
    some (laneCells r.inLanes inOdd r.free c)
  /-- Cell `c` written, `c < outCells.cellCount`, holds the output lanes' cell `c` in the layout
  `outOdd`. -/
  out_eq : ∀ c : Fin 13, c.val < outCells.cellCount → mem.read (r.fp * (g ^ c.val * r.oout)) =
    some (laneCells r.outLanes outOdd 0 c)

/-- The row's flags are the layouts `inOdd`, `outOdd` and the output flags of `outCells`. -/
def KeccakFlags (r : KeccakRow K) (inOdd outOdd : Bool) (outCells : KeccakOutputCells) : Prop :=
  r.oddIn = layoutFlagWord inOdd ∧ r.oddOut = layoutFlagWord outOdd ∧
    r.outTwo = (keccakOutputFlags outCells).1 ∧ r.outAll = (keccakOutputFlags outCells).2

/-- The relation a `KECCAK` row refines: its flags are the layouts `inOdd`, `outOdd` and the output
cells `outCells`, it is bound to the image, and from its registers the machine executes the
instruction it names to `next`. -/
def KeccakRefines {κ : ℕ} (mem : MemoryImage κ) (r : KeccakRow K) (next : Registers K) : Prop :=
  ∃ inOdd outOdd outCells, KeccakFlags r inOdd outOdd outCells ∧
    KeccakBindings mem r inOdd outOdd outCells ∧
    execute mem ⟨r.pc, r.fp⟩ (.keccak r.oms r.otail r.ob8 r.ocap r.oout inOdd outOdd outCells) =
      some next

/-- `KeccakRefines` gives the flags, the bindings and the successor `(g·pc, fp)`. Not the
permutation on the lanes: a row writing one or two cells binds only those, and the permutation is
the Keccak reduction's (`KeccakRelation`, the table's assumption). -/
theorem KeccakRefines.bindings {κ : ℕ} {mem : MemoryImage κ} {r : KeccakRow K}
    {next : Registers K} (h : KeccakRefines mem r next) :
    (∃ inOdd outOdd outCells, KeccakFlags r inOdd outOdd outCells ∧
      KeccakBindings mem r inOdd outOdd outCells) ∧ next = Registers.next ⟨r.pc, r.fp⟩ := by
  obtain ⟨inOdd, outOdd, outCells, hf, hb, hexec⟩ := h
  obtain ⟨-, -, -, -, -, hnext⟩ :=
    (execute_keccak_eq_some_iff _ _ _ _ _ _ _ _ _ _ _).mp hexec
  exact ⟨⟨inOdd, outOdd, outCells, hf, hb⟩, hnext⟩

/-- A row writing all thirteen output cells (`out_all = 1`) binds every output lane, so
`KeccakRefines` gives the permutation on its lanes; a row writing one or two cells does not, and
there the permutation is the Keccak reduction's alone. -/
theorem KeccakRefines.relation_of_all {κ : ℕ} {mem : MemoryImage κ} {r : KeccakRow K}
    {next : Registers K} (h : KeccakRefines mem r next) (hall : r.outAll = 1) :
    KeccakRelation r := by
  obtain ⟨inOdd, outOdd, oc, ⟨-, -, -, ha⟩, hb, hexec⟩ := h
  have hoc : oc = .all := by
    cases oc
    · exact absurd (ha.symm.trans hall) (by simp [keccakOutputFlags, layoutFlagWord])
    · exact absurd (ha.symm.trans hall) (by simp [keccakOutputFlags, layoutFlagWord])
    · rfl
  subst hoc
  obtain ⟨input, output, hin, hout, hcells, -⟩ :=
    (execute_keccak_eq_some_iff _ _ _ _ _ _ _ _ _ _ _).mp hexec
  have hinput : input = laneCells r.inLanes inOdd r.free := by
    funext c; exact Option.some.inj ((hin c).symm.trans (hb.in_eq c))
  have houtput : output = laneCells r.outLanes outOdd 0 := by
    funext c; exact Option.some.inj ((hout c c.isLt).symm.trans (hb.out_eq c c.isLt))
  have h2 := hcells.2
  rw [hinput, houtput, stateOfCells_laneCells] at h2
  have h3 : laneCells r.outLanes outOdd 0 =
      laneCells (stateLanes (keccakF1600 (laneState r.inLanes))) outOdd 0 := by
    funext c; rw [h2 c c.isLt, cellsOfState_eq_laneCells]
  exact laneCells_eq_iff.mp h3

/-- **A bound row whose lanes permute refines `KECCAK`**, to the successor `(g·pc, fp)`. -/
theorem keccak_refines_of {κ : ℕ} {mem : MemoryImage κ} {r : KeccakRow K}
    (hb : ∃ inOdd outOdd outCells, KeccakFlags r inOdd outOdd outCells ∧
      KeccakBindings mem r inOdd outOdd outCells) (hrel : KeccakRelation r) :
    KeccakRefines mem r (Registers.next ⟨r.pc, r.fp⟩) := by
  obtain ⟨inOdd, outOdd, outCells, hf, hb⟩ := hb
  refine ⟨inOdd, outOdd, outCells, hf, hb, ?_⟩
  refine (execute_keccak_eq_some_iff _ _ _ _ _ _ _ _ _ _ _).mpr
    ⟨laneCells r.inLanes inOdd r.free, laneCells r.outLanes outOdd 0, hb.in_eq, hb.out_eq,
      ⟨fun c ↦ ?_, fun c _ ↦ ?_⟩, rfl⟩
  · show (E.ofLimbs _ _ 0).limb 2 = 0
    rw [limb_ofLimbs]; rfl
  · rw [stateOfCells_laneCells, cellsOfState_eq_laneCells, ← hrel]

/-! ## The adapter to the prover data -/

/-- The table's `Spec`: the row refines `KeccakRefines` over the image the prover data names. -/
def KeccakSpec (r : KeccakRow K) (next : Registers K) (data : ProverData K) : Prop :=
  KeccakRefines (imageOf data).2 r next

/-! ## Proof helpers -/

/-- A cell limb holding the same lane in both layouts, and the others, in the layout a flag
selects (the forms `layout_limb` takes with a missing lane). -/
theorem layoutLimb_flag' (a : K) (odd : Bool) :
    a + layoutFlagWord odd * a = if odd then 0 else a := by
  cases odd <;> simp [layoutFlagWord, CharTwo.add_self_eq_zero]

/-- The tuple of a `KECCAK` bytecode read, flat. -/
theorem keccak_tuple (c o0 o1 o2 o3 o4 o5 o6 o7 f1 f2 f3 f4 : K) :
    #v[c] ++ #v[o0, o1, o2, o3, o4, o5, o6, o7, f1, f2, f3, f4] =
      #v[c, o0, o1, o2, o3, o4, o5, o6, o7, f1, f2, f3, f4] := rfl

/-- The bytecode tuple of a row, its operands spelled out, is `entry` of the instruction it names. -/
private theorem keccak_entry' (a0 a1 a2 a3 otail ob8 ocap oout : K) (inOdd outOdd : Bool)
    (outCells : KeccakOutputCells) :
    #v[Opcode.keccak.busCode] ++ #v[a0, a1, a2, a3, otail, ob8, ocap, oout, layoutFlagWord inOdd,
      layoutFlagWord outOdd, (keccakOutputFlags outCells).1, (keccakOutputFlags outCells).2] =
        busEntry (.keccak ![a0, a1, a2, a3] otail ob8 ocap oout inOdd outOdd outCells) := rfl

/-- A decoding `KECCAK` tuple has `0/1` layout flags and the output flags of an output-cell
choice. -/
theorem keccak_flags_of_decode {c o0 o1 o2 o3 o4 o5 o6 o7 f1 f2 f3 f4 : K}
    {ins : LeanIsaInstruction} (hc : c = Opcode.keccak.busCode)
    (h : decode #v[c, o0, o1, o2, o3, o4, o5, o6, o7, f1, f2, f3, f4] = some ins) :
    ∃ b1 b2 oc, f1 = layoutFlagWord b1 ∧ f2 = layoutFlagWord b2 ∧
      f3 = (keccakOutputFlags oc).1 ∧ f4 = (keccakOutputFlags oc).2 := by
  subst hc
  simp only [decode, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, opcode?_code] at h
  rcases h1 : flag? f1 with _ | b1 <;> rcases h2 : flag? f2 with _ | b2 <;>
    rcases h3 : outCells? f3 f4 with _ | oc <;>
    simp only [h1, h2, h3, reduceCtorEq] at h
  obtain ⟨h3, h4⟩ := Prod.mk.inj (outCells?_eq_some_iff.mp h3)
  exact ⟨b1, b2, oc, flag?_eq_some_iff.mp h1, flag?_eq_some_iff.mp h2, h3, h4⟩

/-- A choice writing cell `1` has `out_two = 1`. -/
theorem gate_two {oc : KeccakOutputCells} (h : 1 < oc.cellCount) : (keccakOutputFlags oc).1 = 1 := by
  cases oc <;> simp_all [KeccakOutputCells.cellCount, keccakOutputFlags, layoutFlagWord]

/-- A choice writing a cell from `2` on has `out_all = 1`. -/
theorem gate_all {oc : KeccakOutputCells} (h : 2 < oc.cellCount) : (keccakOutputFlags oc).2 = 1 := by
  cases oc <;> simp_all [KeccakOutputCells.cellCount, keccakOutputFlags, layoutFlagWord]

/-- `out_two = 1` writes cell `1`. -/
theorem of_gate_two {oc : KeccakOutputCells} (h : (keccakOutputFlags oc).1 = 1) : 1 < oc.cellCount := by
  cases oc <;> simp_all [KeccakOutputCells.cellCount, keccakOutputFlags, layoutFlagWord]

/-- `out_all = 1` writes every cell. -/
theorem of_gate_all {oc : KeccakOutputCells} (h : (keccakOutputFlags oc).2 = 1) {c : ℕ} (hc : c < 13) :
    c < oc.cellCount := by
  cases oc <;> simp_all [KeccakOutputCells.cellCount, keccakOutputFlags, layoutFlagWord]

/-! ## The table -/

set_option maxHeartbeats 16000000 in
/-- The `KECCAK` table (`flushes_keccak`, `layout.rs:329-371`): state step, bytecode read of
`(KECCAK, o_m₀, …, o_m₃, o_tail, o_b8, o_cap, o_out, odd_in, odd_out, out_two, out_all)`, the
thirteen cells read, output cell `0` written, cell `1` written as `out_two` says and cells `2..13`
as `out_all` says (`memReadIf`), each as `(lo, hi, 0)` in its layout. Returns the pushed successor
`(g·pc, fp)`; sound under `KeccakRelation`. -/
def keccakTable : GeneralFormalCircuit K KeccakRow Registers where
  -- The table's name in leanVM (`TABLES`, `cpu/mod.rs:391`), unique in the ensemble (Clean keys
  -- the prover data by it).
  name := "KECCAK"
  main r := do
    let next : Var Registers K := ⟨Expression.const g * r.pc, r.fp⟩
    StatePull.pull ⟨r.pc, r.fp⟩
    StatePush.push next
    bytecodeRead r.pc r.rbc (Expression.const Opcode.keccak.busCode)
      #v[r.om[0], r.om[1], r.om[2], r.om[3], r.otail, r.ob8, r.ocap, r.oout, r.oddIn, r.oddOut,
        r.outTwo, r.outAll]
    memRead (r.fp * r.om[0]) r.cnt[0] #v[r.lin[0] + r.oddIn * r.lin[0] + r.oddIn * r.free, r.lin[1] + r.oddIn * r.lin[1] + r.oddIn * r.lin[0], 0]
    memRead (r.fp * r.om[1]) r.cnt[1] #v[r.lin[2] + r.oddIn * r.lin[2] + r.oddIn * r.lin[1], r.lin[3] + r.oddIn * r.lin[3] + r.oddIn * r.lin[2], 0]
    memRead (r.fp * r.om[2]) r.cnt[2] #v[r.lin[4] + r.oddIn * r.lin[4] + r.oddIn * r.lin[3], r.lin[5] + r.oddIn * r.lin[5] + r.oddIn * r.lin[4], 0]
    memRead (r.fp * r.om[3]) r.cnt[3] #v[r.lin[6] + r.oddIn * r.lin[6] + r.oddIn * r.lin[5], r.lin[7] + r.oddIn * r.lin[7] + r.oddIn * r.lin[6], 0]
    memRead (r.fp * (Expression.const (g ^ 0) * r.otail)) r.cnt[4] #v[r.lin[8] + r.oddIn * r.lin[8] + r.oddIn * r.lin[7], r.lin[9] + r.oddIn * r.lin[9] + r.oddIn * r.lin[8], 0]
    memRead (r.fp * (Expression.const (g ^ 1) * r.otail)) r.cnt[5] #v[r.lin[10] + r.oddIn * r.lin[10] + r.oddIn * r.lin[9], r.lin[11] + r.oddIn * r.lin[11] + r.oddIn * r.lin[10], 0]
    memRead (r.fp * (Expression.const (g ^ 2) * r.otail)) r.cnt[6] #v[r.lin[12] + r.oddIn * r.lin[12] + r.oddIn * r.lin[11], r.lin[13] + r.oddIn * r.lin[13] + r.oddIn * r.lin[12], 0]
    memRead (r.fp * (Expression.const (g ^ 3) * r.otail)) r.cnt[7] #v[r.lin[14] + r.oddIn * r.lin[14] + r.oddIn * r.lin[13], r.lin[15] + r.oddIn * r.lin[15] + r.oddIn * r.lin[14], 0]
    memRead (r.fp * r.ob8) r.cnt[8] #v[r.lin[16] + r.oddIn * r.lin[16] + r.oddIn * r.lin[15], r.free + r.oddIn * r.free + r.oddIn * r.lin[16], 0]
    memRead (r.fp * (Expression.const (g ^ 0) * r.ocap)) r.cnt[9] #v[r.lin[17], r.lin[18], 0]
    memRead (r.fp * (Expression.const (g ^ 1) * r.ocap)) r.cnt[10] #v[r.lin[19], r.lin[20], 0]
    memRead (r.fp * (Expression.const (g ^ 2) * r.ocap)) r.cnt[11] #v[r.lin[21], r.lin[22], 0]
    memRead (r.fp * (Expression.const (g ^ 3) * r.ocap)) r.cnt[12] #v[r.lin[23], r.lin[24], 0]
    memRead (r.fp * (Expression.const (g ^ 0) * r.oout)) r.cnt[13] #v[r.lout[0] + r.oddOut * r.lout[0], r.lout[1] + r.oddOut * r.lout[1] + r.oddOut * r.lout[0], 0]
    memReadIf r.outTwo (r.fp * (Expression.const (g ^ 1) * r.oout)) r.cnt[14] #v[r.lout[2] + r.oddOut * r.lout[2] + r.oddOut * r.lout[1], r.lout[3] + r.oddOut * r.lout[3] + r.oddOut * r.lout[2], 0]
    memReadIf r.outAll (r.fp * (Expression.const (g ^ 2) * r.oout)) r.cnt[15] #v[r.lout[4] + r.oddOut * r.lout[4] + r.oddOut * r.lout[3], r.lout[5] + r.oddOut * r.lout[5] + r.oddOut * r.lout[4], 0]
    memReadIf r.outAll (r.fp * (Expression.const (g ^ 3) * r.oout)) r.cnt[16] #v[r.lout[6] + r.oddOut * r.lout[6] + r.oddOut * r.lout[5], r.lout[7] + r.oddOut * r.lout[7] + r.oddOut * r.lout[6], 0]
    memReadIf r.outAll (r.fp * (Expression.const (g ^ 4) * r.oout)) r.cnt[17] #v[r.lout[8] + r.oddOut * r.lout[8] + r.oddOut * r.lout[7], r.lout[9] + r.oddOut * r.lout[9] + r.oddOut * r.lout[8], 0]
    memReadIf r.outAll (r.fp * (Expression.const (g ^ 5) * r.oout)) r.cnt[18] #v[r.lout[10] + r.oddOut * r.lout[10] + r.oddOut * r.lout[9], r.lout[11] + r.oddOut * r.lout[11] + r.oddOut * r.lout[10], 0]
    memReadIf r.outAll (r.fp * (Expression.const (g ^ 6) * r.oout)) r.cnt[19] #v[r.lout[12] + r.oddOut * r.lout[12] + r.oddOut * r.lout[11], r.lout[13] + r.oddOut * r.lout[13] + r.oddOut * r.lout[12], 0]
    memReadIf r.outAll (r.fp * (Expression.const (g ^ 7) * r.oout)) r.cnt[20] #v[r.lout[14] + r.oddOut * r.lout[14] + r.oddOut * r.lout[13], r.lout[15] + r.oddOut * r.lout[15] + r.oddOut * r.lout[14], 0]
    memReadIf r.outAll (r.fp * (Expression.const (g ^ 8) * r.oout)) r.cnt[21] #v[r.lout[16] + r.oddOut * r.lout[16] + r.oddOut * r.lout[15], r.oddOut * r.lout[16], 0]
    memReadIf r.outAll (r.fp * (Expression.const (g ^ 9) * r.oout)) r.cnt[22] #v[r.lout[17], r.lout[18], 0]
    memReadIf r.outAll (r.fp * (Expression.const (g ^ 10) * r.oout)) r.cnt[23] #v[r.lout[19], r.lout[20], 0]
    memReadIf r.outAll (r.fp * (Expression.const (g ^ 11) * r.oout)) r.cnt[24] #v[r.lout[21], r.lout[22], 0]
    memReadIf r.outAll (r.fp * (Expression.const (g ^ 12) * r.oout)) r.cnt[25] #v[r.lout[23], r.lout[24], 0]
    pure next
  -- The push channels: their requirements are vacuous, the obligation is `Spec`. And the memory
  -- pull: a gated pull of multiplicity `flag` requires the flag to be `0` or `1`, which the
  -- soundness proof gives, the flags being an entry's (`decode`).
  channelsWithRequirements := [StatePush.toRaw, MemPush.toRaw, BytecodePush.toRaw, MemPull.toRaw]
  requirementsChannelsLawful input offset := by
    simp only [circuit_norm, memRead, memReadIf, bytecodeRead, -BitVec.reduceNeg]
    tauto
  -- The named assumption: the Keccak reduction's proof of the permutation on the row's lanes.
  Assumptions r _ := KeccakRelation r
  Spec := KeccakSpec
  -- The local premise: the flags are layouts and output cells, and the cells read and written are
  -- bound.
  ProverAssumptions r data _ := ∃ inOdd outOdd outCells, KeccakFlags r inOdd outOdd outCells ∧
    KeccakBindings (imageOf data).2 r inOdd outOdd outCells
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, memReadIf, bytecodeRead]
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
    · -- The gated pulls' requirements: the flags, the multiplicities, are `0` or `1`.
      obtain ⟨b1, b2⟩ := keccakOutputFlags_bits oc
      rw [hft, hfa]
      rcases b1 with b1 | b1 <;> rcases b2 with b2 | b2 <;> simp [b1, b2]
    refine keccak_refines_of ⟨inOdd, outOdd, oc, ⟨hfi, hfo, hft, hfa⟩, ⟨fun c ↦ ?_, fun c hc ↦ ?_⟩⟩
      h_assumptions
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
        · cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, Vector.getElem_map] at h25 ⊢ <;> exact h25
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, memReadIf, bytecodeRead]
    obtain ⟨inOdd, outOdd, oc, ⟨hfi, hfo, hft, hfa⟩, hb⟩ := h_assumptions
    obtain ⟨_, _, hom, _, _, _, _, hoi, hoo, hot, hoa, _, hlin, hlout, _, _⟩ := h_input
    subst hom hlin hlout hfi hfo hft hfa
    refine ⟨⟨_, by rw [keccak_entry']; exact decode_entry _⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h := hb.in_eq 0
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, KeccakRow.oms, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.in_eq 1
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, KeccakRow.oms, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.in_eq 2
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, KeccakRow.oms, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.in_eq 3
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, KeccakRow.oms, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.in_eq 4
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, pow_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.in_eq 5
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul, pow_one] at h ⊢ <;> exact h
    · have h := hb.in_eq 6
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.in_eq 7
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.in_eq 8
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.in_eq 9
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, Vector.getElem_map, pow_zero, one_mul] at h ⊢ <;> exact h
    · have h := hb.in_eq 10
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, Vector.getElem_map, pow_one] at h ⊢ <;> exact h
    · have h := hb.in_eq 11
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, Vector.getElem_map] at h ⊢ <;> exact h
    · have h := hb.in_eq 12
      cases inOdd <;> simp [laneCells, cellLanes, laneLimb, keccakInputCellOffset, KeccakRow.inLanes, Vector.getElem_map] at h ⊢ <;> exact h
    · have h := hb.out_eq 0 (by cases oc <;> decide)
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, pow_zero, one_mul] at h ⊢ <;> exact h
    · intro hg
      have h := hb.out_eq 1 (of_gate_two (by simpa using hg))
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul, pow_one] at h ⊢ <;> exact h
    · intro hg
      have h := hb.out_eq 2 (of_gate_all (by simpa using hg) (by decide))
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · intro hg
      have h := hb.out_eq 3 (of_gate_all (by simpa using hg) (by decide))
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · intro hg
      have h := hb.out_eq 4 (of_gate_all (by simpa using hg) (by decide))
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · intro hg
      have h := hb.out_eq 5 (of_gate_all (by simpa using hg) (by decide))
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · intro hg
      have h := hb.out_eq 6 (of_gate_all (by simpa using hg) (by decide))
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · intro hg
      have h := hb.out_eq 7 (of_gate_all (by simpa using hg) (by decide))
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · intro hg
      have h := hb.out_eq 8 (of_gate_all (by simpa using hg) (by decide))
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, layoutFlagWord, Vector.getElem_map, CharTwo.add_self_eq_zero, one_mul] at h ⊢ <;> exact h
    · intro hg
      have h := hb.out_eq 9 (of_gate_all (by simpa using hg) (by decide))
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, Vector.getElem_map] at h ⊢ <;> exact h
    · intro hg
      have h := hb.out_eq 10 (of_gate_all (by simpa using hg) (by decide))
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, Vector.getElem_map] at h ⊢ <;> exact h
    · intro hg
      have h := hb.out_eq 11 (of_gate_all (by simpa using hg) (by decide))
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, Vector.getElem_map] at h ⊢ <;> exact h
    · intro hg
      have h := hb.out_eq 12 (of_gate_all (by simpa using hg) (by decide))
      cases outOdd <;> simp [laneCells, cellLanes, laneLimb, KeccakRow.outLanes, Vector.getElem_map] at h ⊢ <;> exact h

/-! ## Rows from executions -/

/-- The cells a `KECCAK` with these operands reads at `fp` over the image, the zero word where a
read fails. -/
noncomputable def keccakInputCells {κ : ℕ} (mem : MemoryImage κ) (fp : K) (om : Fin 4 → K)
    (otail ob8 ocap : K) (c : Fin 13) : E :=
  (mem.read (fp * keccakInputCellOffset om otail ob8 ocap c)).getD 0

/-- The row of an execution of `KECCAK om o_tail o_b8 o_cap o_out inOdd outOdd outCells` from
`(pc, fp)` over the image `mem`: the registers, the operands, the layout and output flags, the
input lanes the cells read hold and their free limb, the output lanes Keccak-f[1600] of them (all
twenty-five, as the Rust fills `V_OUT` with the input permuted again, `tables.rs:996-1000`, whatever
`outCells`), and the counts as parameters. Noncomputable: it reads the image. -/
noncomputable def keccakRowOf {κ : ℕ} (mem : MemoryImage κ) (pc fp : K) (om : Fin 4 → K)
    (otail ob8 ocap oout : K) (inOdd outOdd : Bool) (outCells : KeccakOutputCells)
    (cnt : Vector K 26) (rbc : K) : KeccakRow K :=
  let input := keccakInputCells mem fp om otail ob8 ocap
  let S := stateOfCells input inOdd
  ⟨pc, fp, #v[om 0, om 1, om 2, om 3], otail, ob8, ocap, oout, layoutFlagWord inOdd,
    layoutFlagWord outOdd, (keccakOutputFlags outCells).1, (keccakOutputFlags outCells).2,
    freeLimb input inOdd, Vector.ofFn (stateLanes S), Vector.ofFn (stateLanes (keccakF1600 S)), cnt,
    rbc⟩

/-- The operands of `keccakRowOf` are the instruction's. -/
theorem keccakRowOf_oms {κ : ℕ} (mem : MemoryImage κ) (pc fp : K) (om : Fin 4 → K)
    (otail ob8 ocap oout : K) (inOdd outOdd : Bool) (outCells : KeccakOutputCells)
    (cnt : Vector K 26) (rbc : K) :
    (keccakRowOf mem pc fp om otail ob8 ocap oout inOdd outOdd outCells cnt rbc).oms = om := by
  funext i; fin_cases i <;> rfl

/-- The lanes of `keccakRowOf` permute: its output lanes are Keccak-f[1600] of its input lanes. -/
theorem keccakRowOf_relation {κ : ℕ} (mem : MemoryImage κ) (pc fp : K) (om : Fin 4 → K)
    (otail ob8 ocap oout : K) (inOdd outOdd : Bool) (outCells : KeccakOutputCells)
    (cnt : Vector K 26) (rbc : K) :
    KeccakRelation (keccakRowOf mem pc fp om otail ob8 ocap oout inOdd outOdd outCells cnt rbc) := by
  have hin : (keccakRowOf mem pc fp om otail ob8 ocap oout inOdd outOdd outCells cnt rbc).inLanes =
      stateLanes (stateOfCells (keccakInputCells mem fp om otail ob8 ocap) inOdd) := by
    funext l; simp [keccakRowOf, KeccakRow.inLanes]
  unfold KeccakRelation
  rw [hin, laneState_stateLanes]
  funext l; simp [keccakRowOf, KeccakRow.outLanes]

/-- A valid execution of `KECCAK` binds `keccakRowOf`, with any counts: its input cells are
canonical, so they are the cells of the lanes they hold, and its written output cells are the cells
of Keccak-f[1600] of those lanes. -/
theorem keccakRowOf_bindings {κ : ℕ} {mem : MemoryImage κ} {pc fp : K} {om : Fin 4 → K}
    {otail ob8 ocap oout : K} {inOdd outOdd : Bool} {outCells : KeccakOutputCells}
    {next : Registers K}
    (hexec : execute mem ⟨pc, fp⟩ (.keccak om otail ob8 ocap oout inOdd outOdd outCells) =
      some next)
    (cnt : Vector K 26) (rbc : K) :
    KeccakBindings mem (keccakRowOf mem pc fp om otail ob8 ocap oout inOdd outOdd outCells cnt rbc)
      inOdd outOdd outCells := by
  obtain ⟨input, output, hin, hout, hcells, -⟩ :=
    (execute_keccak_eq_some_iff _ _ _ _ _ _ _ _ _ _ _).mp hexec
  have hinput : keccakInputCells mem fp om otail ob8 ocap = input := by
    funext c; simp [keccakInputCells, hin c]
  set R := keccakRowOf mem pc fp om otail ob8 ocap oout inOdd outOdd outCells cnt rbc with hR
  have hlanes : R.inLanes = stateLanes (stateOfCells input inOdd) := by
    funext l; simp [hR, keccakRowOf, KeccakRow.inLanes, hinput]
  have hlout : R.outLanes = stateLanes (keccakF1600 (stateOfCells input inOdd)) := by
    funext l; simp [hR, keccakRowOf, KeccakRow.outLanes, hinput]
  have hfree : R.free = freeLimb input inOdd := by
    simp [hR, keccakRowOf, hinput]
  refine ⟨fun c ↦ ?_, fun c hc ↦ ?_⟩
  · rw [hlanes, hfree, laneCells_stateOfCells hcells.1, hR, keccakRowOf_oms]
    exact hin c
  · rw [hlout, ← cellsOfState_eq_laneCells, ← hcells.2 c hc]
    exact hout c hc

/-- A valid execution of `KECCAK` is represented by `keccakRowOf`, with any counts
(`keccakRowOf_bindings`); its flags are the instruction's. -/
theorem keccakRowOf_refines {κ : ℕ} {mem : MemoryImage κ} {pc fp : K} {om : Fin 4 → K}
    {otail ob8 ocap oout : K} {inOdd outOdd : Bool} {outCells : KeccakOutputCells}
    {next : Registers K}
    (hexec : execute mem ⟨pc, fp⟩ (.keccak om otail ob8 ocap oout inOdd outOdd outCells) =
      some next)
    (cnt : Vector K 26) (rbc : K) :
    KeccakRefines mem (keccakRowOf mem pc fp om otail ob8 ocap oout inOdd outOdd outCells cnt rbc)
      next :=
  ⟨inOdd, outOdd, outCells, ⟨rfl, rfl, rfl, rfl⟩, keccakRowOf_bindings hexec cnt rbc, by
    rw [keccakRowOf_oms]; exact hexec⟩

/-- Every valid `KECCAK` execution has a satisfying row, from the execution alone. -/
theorem keccak_exec_complete {data : ProverData K} {pc fp : K} {om : Fin 4 → K}
    {otail ob8 ocap oout : K} {inOdd outOdd : Bool} {outCells : KeccakOutputCells}
    {next : Registers K}
    (hexec : execute (imageOf data).2 ⟨pc, fp⟩
      (.keccak om otail ob8 ocap oout inOdd outOdd outCells) = some next)
    (cnt : Vector K 26) (rbc : K) :
    ConstraintsHold.Completeness (rowEnv data)
      ((keccakTable.main (const (keccakRowOf (imageOf data).2 pc fp om otail ob8 ocap oout inOdd
        outOdd outCells cnt rbc))).operations 0) := by
  obtain ⟨i, o, oc, hf, hb, -⟩ := keccakRowOf_refines hexec cnt rbc
  exact (keccakTable.completeness 0 (rowEnv data) (const _)
    (by simp only [circuit_norm, keccakTable, memRead, memReadIf, bytecodeRead, -BitVec.reduceNeg])
    _ ProvableType.eval_const_prover ⟨i, o, oc, hf, hb⟩).1

end LeanVM.Arithmetization
