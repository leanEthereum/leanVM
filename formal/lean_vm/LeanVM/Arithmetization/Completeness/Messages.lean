/-
  LeanVM.Arithmetization.Completeness.Messages

  What the row of each of the six tables sends on the bus: the state step, the bytecode read, and
  the memory reads, as the explicit messages the row circuit emits.
-/

module

public import LeanVM.Arithmetization.Completeness.Basics

@[expose] public section

/-!
# The messages of a row

The balance of the three channel pairs is a statement about the messages the rows send, so the
witness of `constraintCompleteness` needs them in closed form. Every table's row circuit has the
same shape: pull the state `(pc, fp)`, push the successor, read the bytecode entry at `pc`
(`bytecodeRead`: a pull with count `r` and a push with count `g·r`), then read its memory cells
(`memRead`, likewise). `rowSends c env` lists the `(channel name, message)` pairs a component's
row circuit sends in the row environment `env`, in the circuit's order.

`xor_sends` and its five siblings state, for a typed row `r` written as the raw row `rawRow r`,
exactly the list the circuit sends, as arrays of the row's fields. The proof is one `simp` with
the circuit lemmas over a row variable `x` with `eval env x = r` (`xor_sends_gen`), the general
form the raw-row lemmas instantiate at Clean's `varFromOffset`; no column index is ever
computed. The `JUMP` row's pushed successor depends on its local witness `b`, which is the slot
after the row's twelve columns.

## Wrong readings excluded

* The sends of a row are not its columns: the third read of an `XOR` row carries the sums
  `v_A + v_B`, the `MUL_NATIVE` row's the twelve products folded by `y^3 = y + 1`, the `DEREF`
  row's the store coordinates of its mode; none of these is a column.
* The pull of a bus read carries the count `r`, the push `g·r` (specification §6.2): a message
  is `(addr, count, v)`, never `(addr, v, count)`.
* The local witnesses of a `JUMP` row are in the raw row, after the columns: reading the
  successor at a row without them would read `0` and push the fall-through for a taken jump.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics
open Air.Flat (Component)

/-! ## Messages as arrays -/

/-- A vector of three is the list of its entries. -/
theorem vec3_toList {F : Type} (v : Vector F 3) : v.toList = [v[0], v[1], v[2]] := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have : i < 3 := by simpa using h1
  interval_cases i <;> simp

/-- A vector of twelve is the list of its entries. -/
theorem vec12_toList {F : Type} (v : Vector F 12) :
    v.toList = [v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9], v[10], v[11]] := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have : i < 12 := by simpa using h1
  interval_cases i <;> simp

/-- A state message flattens to the array `[pc, fp]`, over any type of coordinates. -/
theorem regs_toArray {F : Type} (s : Registers F) : (toElements s).toArray = #[s.pc, s.fp] := by
  obtain ⟨pc, fp⟩ := s
  simp [circuit_norm, explicit_provable_type, ProvableStruct.toComponents]

/-- A memory message flattens to the array `[addr, count, v₀, v₁, v₂]`. -/
theorem memMsg_toArray {F : Type} (m : MemMsg F) :
    (toElements m).toArray = #[m.addr, m.count, m.v[0], m.v[1], m.v[2]] := by
  obtain ⟨addr, count, v⟩ := m
  simp [circuit_norm, explicit_provable_type, ProvableStruct.toComponents]
  apply Array.toList_inj.mp
  rw [Vector.toList_toArray, Vector.toList_append, Vector.toList_append, vec3_toList]
  rfl

/-- A bytecode message flattens to the array `[pc, count, opcode, op₀, …, op₁₁]`. -/
theorem bytecodeMsg_toArray {F : Type} (b : BytecodeMsg F) :
    (toElements b).toArray =
      #[b.pc, b.count, b.opcode, b.op[0], b.op[1], b.op[2], b.op[3], b.op[4], b.op[5], b.op[6],
        b.op[7], b.op[8], b.op[9], b.op[10], b.op[11]] := by
  obtain ⟨pc, count, opcode, op⟩ := b
  simp [circuit_norm, explicit_provable_type, ProvableStruct.toComponents]
  apply Array.toList_inj.mp
  rw [Vector.toList_toArray, Vector.toList_append, Vector.toList_append, Vector.toList_append,
    vec12_toList]
  rfl

/-! ## A row's sends -/

/-- The `(channel name, message)` pairs a component's row circuit sends in the row environment
`env`, in the circuit's order. -/
def rowSends (c : Component K) (env : Environment K) : List (String × Array K) :=
  (c.rowOperations.interactions.map (AbstractInteraction.eval env)).map
    fun i ↦ (i.channel.name, i.msg)

/-- A row's messages on a channel are the sends with that channel's name. -/
theorem rowMessagesOn_eq_rowSends (t : Air.Flat.Table K) (row : Array K) (c : RawChannel K) :
    rowMessagesOn t row c =
      ((rowSends t.component (t.environment row)).filter (·.1 = c.name)).map (·.2) := by
  rw [rowMessagesOn_eq]
  unfold rowSends
  generalize t.component.rowOperations.interactions.map
    (AbstractInteraction.eval (t.environment row)) = l
  induction l with
  | nil => rfl
  | cons i l ih => by_cases h : i.channel.name = c.name <;> simp [h, ih]

/-- The raw row of a `JUMP` row: its twelve columns, then the local witnesses `w` (the inverse of
the condition) and `b` (its indicator). -/
def jumpRaw (r : JumpRow K) (w b : K) : Array K := rawRow r ++ #[w, b]

/-- Reading the row's variable at any environment whose first cells are the row, and whatever
follows, gives back the row. -/
theorem eval_rowVar_append {Row : TypeMap} [ProvableType Row] (r : Row K) (extra : Array K)
    (data : ProverData K) :
    eval (Environment.fromArray (rawRow r ++ extra) data) (varFromOffset Row 0 : Var Row K) =
      r := by
  rw [eval_varFromOffset_valueFromOffset]
  unfold valueFromOffset
  convert ProvableType.fromElements_toElements r
  refine Vector.ext fun i hi ↦ ?_
  rw [Vector.getElem_mapRange]
  show (((rawRow r ++ extra)[0 + i]?).getD 0) = _
  rw [Nat.zero_add, Array.getElem?_append_left (by rw [rawRow_size]; simpa using hi)]
  show ((toElements r).toArray[i]?).getD 0 = _
  rw [Array.getElem?_eq_getElem (by simpa using hi), Option.getD_some, Vector.getElem_toArray]

/-- The row variable of a raw row evaluates to the row. -/
theorem eval_rowVar {Row : TypeMap} [ProvableType Row] (r : Row K) (data : ProverData K) :
    eval (Environment.fromArray (rawRow r) data) (varFromOffset Row 0 : Var Row K) = r := by
  simpa only [Array.append_empty] using eval_rowVar_append r #[] data

/-! ## The six tables -/

/-- The sends of a row circuit at a row variable that evaluates to `r`: the circuit's interactions
as the arrays of `r`'s fields. -/
theorem xor_sends_gen (x : Var XorRow K) (env : Environment K) (n : ℕ) (r : XorRow K)
    (hx : eval env x = r) :
    (((xorTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) =
      [(StatePull.name, #[r.pc, r.fp]), (StatePush.name, #[g * r.pc, r.fp]),
       (BytecodePull.name, #[r.pc, r.rbc, Opcode.xor.busCode, r.oA, r.oB, r.oC, 0, 0, 0, 0, 0,
           0, 0, 0, 0]),
       (BytecodePush.name, #[r.pc, g * r.rbc, Opcode.xor.busCode, r.oA, r.oB, r.oC, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
       (MemPull.name, #[r.fp * r.oA, r.rA, r.vA[0], r.vA[1], r.vA[2]]),
       (MemPush.name, #[r.fp * r.oA, g * r.rA, r.vA[0], r.vA[1], r.vA[2]]),
       (MemPull.name, #[r.fp * r.oB, r.rB, r.vB[0], r.vB[1], r.vB[2]]),
       (MemPush.name, #[r.fp * r.oB, g * r.rB, r.vB[0], r.vB[1], r.vB[2]]),
       (MemPull.name,
        #[r.fp * r.oC, r.rC, r.vA[0] + r.vB[0], r.vA[1] + r.vB[1], r.vA[2] + r.vB[2]]),
       (MemPush.name,
        #[r.fp * r.oC, g * r.rC, r.vA[0] + r.vB[0], r.vA[1] + r.vB[1], r.vA[2] + r.vB[2]])] := by
  subst hx
  obtain ⟨pc, fp, oA, oB, oC, vA, vB, rA, rB, rC, rbc⟩ := x
  simp only [Operations.interactionValues, circuit_norm, xorTable, memRead, bytecodeRead,
    AbstractInteraction.eval, Vector.toArray_map, regs_toArray, memMsg_toArray,
    bytecodeMsg_toArray, -BitVec.reduceNeg]

/-- The sends of the `MUL_NATIVE` row circuit, in closed form. -/
theorem mul_sends_gen (x : Var MulRow K) (env : Environment K) (n : ℕ) (r : MulRow K)
    (hx : eval env x = r) :
    (((mulTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) =
      [(StatePull.name, #[r.pc, r.fp]), (StatePush.name, #[g * r.pc, r.fp]),
       (BytecodePull.name,
        #[r.pc, r.rbc, Opcode.mulNative.busCode, r.oA, r.oB, r.oC, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
       (BytecodePush.name,
        #[r.pc, g * r.rbc, Opcode.mulNative.busCode, r.oA, r.oB, r.oC, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
       (MemPull.name, #[r.fp * r.oA, r.rA, r.vA[0], r.vA[1], r.vA[2]]),
       (MemPush.name, #[r.fp * r.oA, g * r.rA, r.vA[0], r.vA[1], r.vA[2]]),
       (MemPull.name, #[r.fp * r.oB, r.rB, r.vB[0], r.vB[1], r.vB[2]]),
       (MemPush.name, #[r.fp * r.oB, g * r.rB, r.vB[0], r.vB[1], r.vB[2]]),
       (MemPull.name, #[r.fp * r.oC, r.rC,
          r.vA[0] * r.vB[0] + r.vA[1] * r.vB[2] + r.vA[2] * r.vB[1],
          r.vA[0] * r.vB[1] + r.vA[1] * r.vB[0] + r.vA[1] * r.vB[2] + r.vA[2] * r.vB[1] +
            r.vA[2] * r.vB[2],
          r.vA[0] * r.vB[2] + r.vA[1] * r.vB[1] + r.vA[2] * r.vB[0] + r.vA[2] * r.vB[2]]),
       (MemPush.name, #[r.fp * r.oC, g * r.rC,
          r.vA[0] * r.vB[0] + r.vA[1] * r.vB[2] + r.vA[2] * r.vB[1],
          r.vA[0] * r.vB[1] + r.vA[1] * r.vB[0] + r.vA[1] * r.vB[2] + r.vA[2] * r.vB[1] +
            r.vA[2] * r.vB[2],
          r.vA[0] * r.vB[2] + r.vA[1] * r.vB[1] + r.vA[2] * r.vB[0] + r.vA[2] * r.vB[2]])] := by
  subst hx
  obtain ⟨pc, fp, oA, oB, oC, vA, vB, rA, rB, rC, rbc⟩ := x
  simp only [Operations.interactionValues, circuit_norm, mulTable, memRead, bytecodeRead,
    AbstractInteraction.eval, Vector.toArray_map, regs_toArray, memMsg_toArray,
    bytecodeMsg_toArray, -BitVec.reduceNeg]

/-- The sends of the `SET_CONSTANT` row circuit, in closed form. -/
theorem set_sends_gen (x : Var SetRow K) (env : Environment K) (n : ℕ) (r : SetRow K)
    (hx : eval env x = r) :
    (((setTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) =
      [(StatePull.name, #[r.pc, r.fp]), (StatePush.name, #[g * r.pc, r.fp]),
       (BytecodePull.name,
        #[r.pc, r.rbc, Opcode.setConstant.busCode, r.o, r.k[0], r.k[1], r.k[2], 0, 0, 0, 0, 0, 0, 0, 0]),
       (BytecodePush.name,
        #[r.pc, g * r.rbc, Opcode.setConstant.busCode, r.o, r.k[0], r.k[1], r.k[2], 0, 0, 0, 0,
            0, 0, 0, 0]),
       (MemPull.name, #[r.fp * r.o, r.r, r.k[0], r.k[1], r.k[2]]),
       (MemPush.name, #[r.fp * r.o, g * r.r, r.k[0], r.k[1], r.k[2]])] := by
  subst hx
  obtain ⟨pc, fp, o, k, r, rbc⟩ := x
  simp only [Operations.interactionValues, circuit_norm, setTable, memRead, bytecodeRead,
    AbstractInteraction.eval, Vector.toArray_map, regs_toArray, memMsg_toArray,
    bytecodeMsg_toArray, -BitVec.reduceNeg]

/-- The sends of the `DEREF` row circuit, in closed form. -/
theorem deref_sends_gen (x : Var DerefRow K) (env : Environment K) (n : ℕ) (r : DerefRow K)
    (hx : eval env x = r) :
    (((derefTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) =
      [(StatePull.name, #[r.pc, r.fp]), (StatePush.name, #[g * r.pc, r.fp]),
       (BytecodePull.name,
        #[r.pc, r.rbc, Opcode.deref.busCode, r.o1, r.o2, r.o3, r.fpc, r.ffp, 0, 0, 0, 0, 0, 0, 0]),
       (BytecodePush.name,
        #[r.pc, g * r.rbc, Opcode.deref.busCode, r.o1, r.o2, r.o3, r.fpc, r.ffp, 0, 0, 0, 0, 0, 0, 0]),
       (MemPull.name, #[r.fp * r.o1, r.r1, r.p, 0, 0]),
       (MemPush.name, #[r.fp * r.o1, g * r.r1, r.p, 0, 0]),
       (MemPull.name, #[r.p * r.o2, r.r2,
          (1 + r.fpc + r.ffp) * r.v3[0] + r.fpc * (g ^ 2 * r.pc) + r.ffp * r.fp,
          (1 + r.fpc + r.ffp) * r.v3[1], (1 + r.fpc + r.ffp) * r.v3[2]]),
       (MemPush.name, #[r.p * r.o2, g * r.r2,
          (1 + r.fpc + r.ffp) * r.v3[0] + r.fpc * (g ^ 2 * r.pc) + r.ffp * r.fp,
          (1 + r.fpc + r.ffp) * r.v3[1], (1 + r.fpc + r.ffp) * r.v3[2]]),
       (MemPull.name, #[r.fp * r.o3, r.r3, r.v3[0], r.v3[1], r.v3[2]]),
       (MemPush.name, #[r.fp * r.o3, g * r.r3, r.v3[0], r.v3[1], r.v3[2]])] := by
  subst hx
  obtain ⟨pc, fp, o1, o2, o3, fpc, ffp, p, v3, r1, r2, r3, rbc⟩ := x
  simp only [Operations.interactionValues, circuit_norm, derefTable, memRead, bytecodeRead,
    AbstractInteraction.eval, Vector.toArray_map, regs_toArray, memMsg_toArray,
    bytecodeMsg_toArray, -BitVec.reduceNeg]

/-- The sends of the `JUMP` row circuit, in closed form: the pushed successor reads the indicator
`b`, the local witness at slot `n + 1`. -/
theorem jump_sends_gen (x : Var JumpRow K) (env : Environment K) (n : ℕ) (r : JumpRow K)
    (hx : eval env x = r) (b : K) (hb : env.get (n + 1) = b) :
    (((jumpTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) =
      [(StatePull.name, #[r.pc, r.fp]),
       (StatePush.name, #[b * r.vpc + b * (g * r.pc) + g * r.pc, b * r.vfp + b * r.fp + r.fp]),
       (BytecodePull.name, #[r.pc, r.rbc, Opcode.jump.busCode, r.oc, r.od, r.of, 0, 0, 0, 0, 0,
           0, 0, 0, 0]),
       (BytecodePush.name, #[r.pc, g * r.rbc, Opcode.jump.busCode, r.oc, r.od, r.of, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
       (MemPull.name, #[r.fp * r.oc, r.rc, r.vcond, 0, 0]),
       (MemPush.name, #[r.fp * r.oc, g * r.rc, r.vcond, 0, 0]),
       (MemPull.name, #[r.fp * r.od, r.rd, r.vpc, 0, 0]),
       (MemPush.name, #[r.fp * r.od, g * r.rd, r.vpc, 0, 0]),
       (MemPull.name, #[r.fp * r.of, r.rf, r.vfp, 0, 0]),
       (MemPush.name, #[r.fp * r.of, g * r.rf, r.vfp, 0, 0])] := by
  subst hx
  obtain ⟨pc, fp, oc, od, of, vcond, vpc, vfp, rc, rd, rf, rbc⟩ := x
  dsimp only [jumpTable]
  simp only [Operations.interactionValues, circuit_norm, memRead, bytecodeRead,
    AbstractInteraction.eval, Vector.toArray_map, regs_toArray, memMsg_toArray,
    bytecodeMsg_toArray, hb, -BitVec.reduceNeg]

set_option maxHeartbeats 16000000 in
/-- The sends of the `KECCAK` row circuit, in closed form: the state step, the bytecode read, and
twenty-six cells of two limbs in their layouts, the third limb of each message `0`; the push of
output cell `c ≥ 1` carries the gated counter `count + g·(flag·count) + flag·count`, its flag
`out_two` for `c = 1` and `out_all` past it. -/
theorem keccak_sends_gen (x : Var KeccakRow K) (env : Environment K) (n : ℕ)
    (r : KeccakRow K) (hx : eval env x = r) :
    (((keccakTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) =
      [(StatePull.name, #[r.pc, r.fp]), (StatePush.name, #[g * r.pc, r.fp]),
       (BytecodePull.name,
        #[r.pc, r.rbc, Opcode.keccak.busCode, r.om[0], r.om[1], r.om[2], r.om[3], r.otail, r.ob8,
          r.ocap, r.oout, r.oddIn, r.oddOut, r.outTwo, r.outAll]),
       (BytecodePush.name,
        #[r.pc, g * r.rbc, Opcode.keccak.busCode, r.om[0], r.om[1], r.om[2], r.om[3],
            r.otail, r.ob8,
          r.ocap, r.oout, r.oddIn, r.oddOut, r.outTwo, r.outAll]),
       (MemPull.name, #[r.fp * r.om[0], r.cnt[0], r.lin[0] + r.oddIn * r.lin[0] + r.oddIn * r.free, r.lin[1] + r.oddIn * r.lin[1] + r.oddIn * r.lin[0], 0]),
       (MemPush.name, #[r.fp * r.om[0], g * r.cnt[0], r.lin[0] + r.oddIn * r.lin[0] + r.oddIn * r.free, r.lin[1] + r.oddIn * r.lin[1] + r.oddIn * r.lin[0], 0]),
       (MemPull.name, #[r.fp * r.om[1], r.cnt[1], r.lin[2] + r.oddIn * r.lin[2] + r.oddIn * r.lin[1], r.lin[3] + r.oddIn * r.lin[3] + r.oddIn * r.lin[2], 0]),
       (MemPush.name, #[r.fp * r.om[1], g * r.cnt[1], r.lin[2] + r.oddIn * r.lin[2] + r.oddIn * r.lin[1], r.lin[3] + r.oddIn * r.lin[3] + r.oddIn * r.lin[2], 0]),
       (MemPull.name, #[r.fp * r.om[2], r.cnt[2], r.lin[4] + r.oddIn * r.lin[4] + r.oddIn * r.lin[3], r.lin[5] + r.oddIn * r.lin[5] + r.oddIn * r.lin[4], 0]),
       (MemPush.name, #[r.fp * r.om[2], g * r.cnt[2], r.lin[4] + r.oddIn * r.lin[4] + r.oddIn * r.lin[3], r.lin[5] + r.oddIn * r.lin[5] + r.oddIn * r.lin[4], 0]),
       (MemPull.name, #[r.fp * r.om[3], r.cnt[3], r.lin[6] + r.oddIn * r.lin[6] + r.oddIn * r.lin[5], r.lin[7] + r.oddIn * r.lin[7] + r.oddIn * r.lin[6], 0]),
       (MemPush.name, #[r.fp * r.om[3], g * r.cnt[3], r.lin[6] + r.oddIn * r.lin[6] + r.oddIn * r.lin[5], r.lin[7] + r.oddIn * r.lin[7] + r.oddIn * r.lin[6], 0]),
       (MemPull.name, #[r.fp * (g ^ 0 * r.otail), r.cnt[4], r.lin[8] + r.oddIn * r.lin[8] + r.oddIn * r.lin[7], r.lin[9] + r.oddIn * r.lin[9] + r.oddIn * r.lin[8], 0]),
       (MemPush.name, #[r.fp * (g ^ 0 * r.otail), g * r.cnt[4], r.lin[8] + r.oddIn * r.lin[8] + r.oddIn * r.lin[7], r.lin[9] + r.oddIn * r.lin[9] + r.oddIn * r.lin[8], 0]),
       (MemPull.name, #[r.fp * (g ^ 1 * r.otail), r.cnt[5], r.lin[10] + r.oddIn * r.lin[10] + r.oddIn * r.lin[9], r.lin[11] + r.oddIn * r.lin[11] + r.oddIn * r.lin[10], 0]),
       (MemPush.name, #[r.fp * (g ^ 1 * r.otail), g * r.cnt[5], r.lin[10] + r.oddIn * r.lin[10] + r.oddIn * r.lin[9], r.lin[11] + r.oddIn * r.lin[11] + r.oddIn * r.lin[10], 0]),
       (MemPull.name, #[r.fp * (g ^ 2 * r.otail), r.cnt[6], r.lin[12] + r.oddIn * r.lin[12] + r.oddIn * r.lin[11], r.lin[13] + r.oddIn * r.lin[13] + r.oddIn * r.lin[12], 0]),
       (MemPush.name, #[r.fp * (g ^ 2 * r.otail), g * r.cnt[6], r.lin[12] + r.oddIn * r.lin[12] + r.oddIn * r.lin[11], r.lin[13] + r.oddIn * r.lin[13] + r.oddIn * r.lin[12], 0]),
       (MemPull.name, #[r.fp * (g ^ 3 * r.otail), r.cnt[7], r.lin[14] + r.oddIn * r.lin[14] + r.oddIn * r.lin[13], r.lin[15] + r.oddIn * r.lin[15] + r.oddIn * r.lin[14], 0]),
       (MemPush.name, #[r.fp * (g ^ 3 * r.otail), g * r.cnt[7], r.lin[14] + r.oddIn * r.lin[14] + r.oddIn * r.lin[13], r.lin[15] + r.oddIn * r.lin[15] + r.oddIn * r.lin[14], 0]),
       (MemPull.name, #[r.fp * r.ob8, r.cnt[8], r.lin[16] + r.oddIn * r.lin[16] + r.oddIn * r.lin[15], r.free + r.oddIn * r.free + r.oddIn * r.lin[16], 0]),
       (MemPush.name, #[r.fp * r.ob8, g * r.cnt[8], r.lin[16] + r.oddIn * r.lin[16] + r.oddIn * r.lin[15], r.free + r.oddIn * r.free + r.oddIn * r.lin[16], 0]),
       (MemPull.name, #[r.fp * (g ^ 0 * r.ocap), r.cnt[9], r.lin[17], r.lin[18], 0]),
       (MemPush.name, #[r.fp * (g ^ 0 * r.ocap), g * r.cnt[9], r.lin[17], r.lin[18], 0]),
       (MemPull.name, #[r.fp * (g ^ 1 * r.ocap), r.cnt[10], r.lin[19], r.lin[20], 0]),
       (MemPush.name, #[r.fp * (g ^ 1 * r.ocap), g * r.cnt[10], r.lin[19], r.lin[20], 0]),
       (MemPull.name, #[r.fp * (g ^ 2 * r.ocap), r.cnt[11], r.lin[21], r.lin[22], 0]),
       (MemPush.name, #[r.fp * (g ^ 2 * r.ocap), g * r.cnt[11], r.lin[21], r.lin[22], 0]),
       (MemPull.name, #[r.fp * (g ^ 3 * r.ocap), r.cnt[12], r.lin[23], r.lin[24], 0]),
       (MemPush.name, #[r.fp * (g ^ 3 * r.ocap), g * r.cnt[12], r.lin[23], r.lin[24], 0]),
       (MemPull.name, #[r.fp * (g ^ 0 * r.oout), r.cnt[13], r.lout[0] + r.oddOut * r.lout[0], r.lout[1] + r.oddOut * r.lout[1] + r.oddOut * r.lout[0], 0]),
       (MemPush.name, #[r.fp * (g ^ 0 * r.oout), g * r.cnt[13], r.lout[0] + r.oddOut * r.lout[0], r.lout[1] + r.oddOut * r.lout[1] + r.oddOut * r.lout[0], 0]),
       (MemPull.name, #[r.fp * (g ^ 1 * r.oout), r.cnt[14], r.lout[2] + r.oddOut * r.lout[2] + r.oddOut * r.lout[1], r.lout[3] + r.oddOut * r.lout[3] + r.oddOut * r.lout[2], 0]),
       (MemPush.name, #[r.fp * (g ^ 1 * r.oout), r.cnt[14] + g * (r.outTwo * r.cnt[14]) + r.outTwo * r.cnt[14], r.lout[2] + r.oddOut * r.lout[2] + r.oddOut * r.lout[1], r.lout[3] + r.oddOut * r.lout[3] + r.oddOut * r.lout[2], 0]),
       (MemPull.name, #[r.fp * (g ^ 2 * r.oout), r.cnt[15], r.lout[4] + r.oddOut * r.lout[4] + r.oddOut * r.lout[3], r.lout[5] + r.oddOut * r.lout[5] + r.oddOut * r.lout[4], 0]),
       (MemPush.name, #[r.fp * (g ^ 2 * r.oout), r.cnt[15] + g * (r.outAll * r.cnt[15]) + r.outAll * r.cnt[15], r.lout[4] + r.oddOut * r.lout[4] + r.oddOut * r.lout[3], r.lout[5] + r.oddOut * r.lout[5] + r.oddOut * r.lout[4], 0]),
       (MemPull.name, #[r.fp * (g ^ 3 * r.oout), r.cnt[16], r.lout[6] + r.oddOut * r.lout[6] + r.oddOut * r.lout[5], r.lout[7] + r.oddOut * r.lout[7] + r.oddOut * r.lout[6], 0]),
       (MemPush.name, #[r.fp * (g ^ 3 * r.oout), r.cnt[16] + g * (r.outAll * r.cnt[16]) + r.outAll * r.cnt[16], r.lout[6] + r.oddOut * r.lout[6] + r.oddOut * r.lout[5], r.lout[7] + r.oddOut * r.lout[7] + r.oddOut * r.lout[6], 0]),
       (MemPull.name, #[r.fp * (g ^ 4 * r.oout), r.cnt[17], r.lout[8] + r.oddOut * r.lout[8] + r.oddOut * r.lout[7], r.lout[9] + r.oddOut * r.lout[9] + r.oddOut * r.lout[8], 0]),
       (MemPush.name, #[r.fp * (g ^ 4 * r.oout), r.cnt[17] + g * (r.outAll * r.cnt[17]) + r.outAll * r.cnt[17], r.lout[8] + r.oddOut * r.lout[8] + r.oddOut * r.lout[7], r.lout[9] + r.oddOut * r.lout[9] + r.oddOut * r.lout[8], 0]),
       (MemPull.name, #[r.fp * (g ^ 5 * r.oout), r.cnt[18], r.lout[10] + r.oddOut * r.lout[10] + r.oddOut * r.lout[9], r.lout[11] + r.oddOut * r.lout[11] + r.oddOut * r.lout[10], 0]),
       (MemPush.name, #[r.fp * (g ^ 5 * r.oout), r.cnt[18] + g * (r.outAll * r.cnt[18]) + r.outAll * r.cnt[18], r.lout[10] + r.oddOut * r.lout[10] + r.oddOut * r.lout[9], r.lout[11] + r.oddOut * r.lout[11] + r.oddOut * r.lout[10], 0]),
       (MemPull.name, #[r.fp * (g ^ 6 * r.oout), r.cnt[19], r.lout[12] + r.oddOut * r.lout[12] + r.oddOut * r.lout[11], r.lout[13] + r.oddOut * r.lout[13] + r.oddOut * r.lout[12], 0]),
       (MemPush.name, #[r.fp * (g ^ 6 * r.oout), r.cnt[19] + g * (r.outAll * r.cnt[19]) + r.outAll * r.cnt[19], r.lout[12] + r.oddOut * r.lout[12] + r.oddOut * r.lout[11], r.lout[13] + r.oddOut * r.lout[13] + r.oddOut * r.lout[12], 0]),
       (MemPull.name, #[r.fp * (g ^ 7 * r.oout), r.cnt[20], r.lout[14] + r.oddOut * r.lout[14] + r.oddOut * r.lout[13], r.lout[15] + r.oddOut * r.lout[15] + r.oddOut * r.lout[14], 0]),
       (MemPush.name, #[r.fp * (g ^ 7 * r.oout), r.cnt[20] + g * (r.outAll * r.cnt[20]) + r.outAll * r.cnt[20], r.lout[14] + r.oddOut * r.lout[14] + r.oddOut * r.lout[13], r.lout[15] + r.oddOut * r.lout[15] + r.oddOut * r.lout[14], 0]),
       (MemPull.name, #[r.fp * (g ^ 8 * r.oout), r.cnt[21], r.lout[16] + r.oddOut * r.lout[16] + r.oddOut * r.lout[15], r.oddOut * r.lout[16], 0]),
       (MemPush.name, #[r.fp * (g ^ 8 * r.oout), r.cnt[21] + g * (r.outAll * r.cnt[21]) + r.outAll * r.cnt[21], r.lout[16] + r.oddOut * r.lout[16] + r.oddOut * r.lout[15], r.oddOut * r.lout[16], 0]),
       (MemPull.name, #[r.fp * (g ^ 9 * r.oout), r.cnt[22], r.lout[17], r.lout[18], 0]),
       (MemPush.name, #[r.fp * (g ^ 9 * r.oout), r.cnt[22] + g * (r.outAll * r.cnt[22]) + r.outAll * r.cnt[22], r.lout[17], r.lout[18], 0]),
       (MemPull.name, #[r.fp * (g ^ 10 * r.oout), r.cnt[23], r.lout[19], r.lout[20], 0]),
       (MemPush.name, #[r.fp * (g ^ 10 * r.oout), r.cnt[23] + g * (r.outAll * r.cnt[23]) + r.outAll * r.cnt[23], r.lout[19], r.lout[20], 0]),
       (MemPull.name, #[r.fp * (g ^ 11 * r.oout), r.cnt[24], r.lout[21], r.lout[22], 0]),
       (MemPush.name, #[r.fp * (g ^ 11 * r.oout), r.cnt[24] + g * (r.outAll * r.cnt[24]) + r.outAll * r.cnt[24], r.lout[21], r.lout[22], 0]),
       (MemPull.name, #[r.fp * (g ^ 12 * r.oout), r.cnt[25], r.lout[23], r.lout[24], 0]),
       (MemPush.name, #[r.fp * (g ^ 12 * r.oout), r.cnt[25] + g * (r.outAll * r.cnt[25]) + r.outAll * r.cnt[25], r.lout[23], r.lout[24], 0])] := by
  subst hx
  obtain ⟨pc, fp, om, otail, ob8, ocap, oout, oddIn, oddOut, outTwo, outAll, free, lin, lout, cnt,
    rbc⟩ := x
  simp only [Operations.interactionValues, circuit_norm, keccakTable, memRead, memReadIf,
    bytecodeRead,
    AbstractInteraction.eval, Vector.toArray_map, regs_toArray, memMsg_toArray,
    bytecodeMsg_toArray, Vector.getElem_map, -BitVec.reduceNeg]

/-! ## The blocks and the verifier -/

/-- The sends of the memory block's row circuit: the seed push `(idx, 1, m)` and the finalize pull
`(idx, cntFin, m)`. -/
theorem mem_sends_gen (x : Var MemRow K) (env : Environment K) (n : ℕ) (r : MemRow K)
    (hx : eval env x = r) :
    (((memTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) =
      [(MemPush.name, #[r.idx, 1, r.m[0], r.m[1], r.m[2]]),
       (MemPull.name, #[r.idx, r.cntFin, r.m[0], r.m[1], r.m[2]])] := by
  subst hx
  obtain ⟨m, idx, cntFin⟩ := x
  simp only [Operations.interactionValues, circuit_norm, memTable, AbstractInteraction.eval,
    Vector.toArray_map, memMsg_toArray, -BitVec.reduceNeg]

/-- The sends of the bytecode block's row circuit: the seed push `(idx, 1, entry)` and the
finalize pull `(idx, cntFin, entry)`. -/
theorem bytecode_sends_gen (x : Var BytecodeRow K) (env : Environment K) (n : ℕ)
    (r : BytecodeRow K) (hx : eval env x = r) :
    (((bytecodeTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) =
      [(BytecodePush.name,
        #[r.idx, 1, r.opcode, r.op[0], r.op[1], r.op[2], r.op[3], r.op[4], r.op[5], r.op[6],
          r.op[7], r.op[8], r.op[9], r.op[10], r.op[11]]),
       (BytecodePull.name,
        #[r.idx, r.cntFin, r.opcode, r.op[0], r.op[1], r.op[2], r.op[3], r.op[4], r.op[5],
          r.op[6], r.op[7], r.op[8], r.op[9], r.op[10], r.op[11]])] := by
  subst hx
  obtain ⟨idx, cntFin, opcode, op⟩ := x
  simp only [Operations.interactionValues, circuit_norm, bytecodeTable, AbstractInteraction.eval,
    Vector.toArray_map, bytecodeMsg_toArray, -BitVec.reduceNeg]

/-- The sends of the verifier, a program of the ensemble rather than a table: the push of the
initial state and the pull of the final one, in every environment. -/
theorem verifier_sends (prog : LeanIsaProgram) (env : Environment K) :
    ((leanIsaVerifier prog).circuitOperations.interactionValues env).map
        (fun i ↦ (i.channel.name, i.msg)) =
      [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.pcFinal, 1])] := by
  simp only [Operations.interactionValues, circuit_norm, leanIsaVerifier, AbstractInteraction.eval,
    Vector.toArray_map, regs_toArray, -BitVec.reduceNeg]

end LeanVM.Arithmetization
