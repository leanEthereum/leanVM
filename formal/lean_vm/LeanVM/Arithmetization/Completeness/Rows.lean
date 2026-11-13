/-
  LeanVM.Arithmetization.Completeness.Rows

  The row of an instruction executed at a state: the table it belongs to, the raw row, and what
  it sends on the bus as a function of the state, the successor and the read counts.
-/

module

public import LeanVM.Arithmetization.Completeness.Messages

@[expose] public section

/-!
# The row of an executed instruction

The witness of `constraintCompleteness` writes one row per executed state, in the table of the
opcode the program holds there. `rowOf mem pc fp cnt rbc ins` is that row for the instruction `ins`
executed from `(pc, fp)` over the image `mem`: the typed row of `Arithmetization.Tables`
(`xorRowOf` and its siblings, with the `JUMP` table's honest local witnesses appended), as a raw
row. Its memory reads carry the counts `cnt 0, cnt 1, …` in the order the circuit reads them, and
its bytecode read the count `rbc`.

`sendsOf` is what any such row sends, in the shape every table shares (`Completeness.Messages`):
the state pull and push, the bytecode pull and push of `entry ins` at `pc`, and per read a
memory pull of `(addr, count, v)` and a push of `(addr, g·count, v)`. `readAddrs` lists the
cells an instruction reads, and the memory reads of the row are those cells with the limbs the
image holds there. The master lemma `rowOf_sends` says that if the instruction executes
from `(pc, fp)` to `next` then the row sends exactly `sendsOf` with `next`, and
`readAddrs_valid` that every cell it reads is an address of the image. Both are per table,
from the table's relation (`*_refines_iff`) and the closed forms of `Completeness.Messages`.

## Wrong readings excluded

* The messages carry the limbs the image holds, not the row's own formulas: the third read of an
  `XOR` row carries `v_A + v_B`, and that this is the word at `fp·o_C` is the execution's
  (`xor_refines_iff`), never the row's. A row for an instruction that does not execute sends
  something else, and the bus rejects it.
* The `DEREF` target cell is `p·o_2` for the pointer `p` the image holds at `fp·o_1`, not
  `fp·o_2`: its address is the one read that depends on another.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics
open Air.Flat (Component)

/-! ## Reading a word back as limbs -/

/-- The limbs read back at an address that holds a word are the word's. -/
theorem MemImage.limbsAt_eq_of_read {κ : ℕ} {L : MemoryImage κ} {a : K} {v : E}
    (h : L.read a = some v) : L.limbsAt a = #v[v.limb 0, v.limb 1] := by
  unfold MemoryImage.limbsAt
  rw [h]

/-- The two limbs of `E.ofLimbs`, one by one. -/
theorem limb0_ofLimbs (c0 c1 : K) : (E.ofLimbs c0 c1).limb 0 = c0 := rfl

/-- The second limb of `E.ofLimbs`. -/
theorem limb1_ofLimbs (c0 c1 : K) : (E.ofLimbs c0 c1).limb 1 = c1 := rfl

/-! ## The messages -/

/-- The array a memory message `(addr, count, v)` flattens to. -/
def memMsgOf (a c : K) (v : Vector K 2) : Array K := #[a, c, v[0], v[1]]

/-- The array a bytecode message `(pc, count, entry)` flattens to. -/
def bcMsgOf (pc c : K) (e : Vector K 13) : Array K :=
  #[pc, c, e[0], e[1], e[2], e[3], e[4], e[5], e[6], e[7], e[8], e[9], e[10], e[11], e[12]]

/-- What a row sends: the state pull `(pc, fp)` and push `next`, the bytecode pull of `e` at `pc`
with count `rbc` and the push with count `g·rbc`, then for each read `(addr, count, v)` the
memory pull and the memory push with count `g·count`, in the circuits' order. -/
def sendsOf (pc fp : K) (next : Registers K) (rbc : K) (e : Vector K 13)
    (reads : List (K × K × Vector K 2)) : List (String × Array K) :=
  [(StatePull.name, #[pc, fp]), (StatePush.name, #[next.pc, next.fp]),
    (BytecodePull.name, bcMsgOf pc rbc e), (BytecodePush.name, bcMsgOf pc (g * rbc) e)] ++
  reads.flatMap fun x ↦
    [(MemPull.name, memMsgOf x.1 x.2.1 x.2.2), (MemPush.name, memMsgOf x.1 (g * x.2.1) x.2.2)]

/-- What gated reads send: for each `(flag, addr, count, v)` the memory pull of `(addr, count, v)`
and the memory push of `(addr, gatedCount flag count, v)`, in the circuit's order. -/
def gatedSends (l : List (K × K × K × Vector K 2)) : List (String × Array K) :=
  l.flatMap fun y ↦
    [(MemPull.name, memMsgOf y.2.1 y.2.2.1 y.2.2.2),
      (MemPush.name, memMsgOf y.2.1 (gatedCount y.1 y.2.2.1) y.2.2.2)]

/-- What cancelled pairs send: for each `(addr, count, v)` the memory pull and the memory push of
the one tuple `(addr, count, v)`, a gated read at flag `0`. -/
def skipSends (l : List (K × K × Vector K 2)) : List (String × Array K) :=
  l.flatMap fun x ↦
    [(MemPull.name, memMsgOf x.1 x.2.1 x.2.2), (MemPush.name, memMsgOf x.1 x.2.1 x.2.2)]

/-- An opcode table's sends are those of its circuit's main at the row variable. -/
theorem rowSends_mk {Row : TypeMap} [ProvableType Row] (c : GeneralFormalCircuit K Row Registers)
    (env : Environment K) :
    rowSends (opcodeComponent c) env =
      (((c.main (varFromOffset Row 0)).operations (size Row)).interactionValues env).map
        (fun i ↦ (i.channel.name, i.msg)) := rfl

/-- The memory block's sends are those of `memTable`'s main at the row variable. -/
theorem rowSends_memComponent (κ : ℕ) (env : Environment K) :
    rowSends (memComponent κ) env =
      (((memTable.main (varFromOffset MemRow 0)).operations (size MemRow)).interactionValues
        env).map (fun i ↦ (i.channel.name, i.msg)) := rfl

/-- The bytecode block's sends are those of `bytecodeTable`'s main at the row variable. -/
theorem rowSends_bytecodeComponent (prog : LeanIsaProgram) (env : Environment K) :
    rowSends (bytecodeComponent prog) env =
      (((bytecodeTable.main (varFromOffset BytecodeRow 0)).operations (size BytecodeRow)).interactionValues
        env).map (fun i ↦ (i.channel.name, i.msg)) := rfl

/-! ## The cells an instruction reads -/

/-- The cells an instruction reads, in the order its row's reads carry them (the circuits'
order): the operand cells (for `KECCAK` the thirteen read, then the `outCells.cellCount` written,
as the Rust's execution bumps the counts of exactly these, `execute.rs:962-972`), and for
`DEREF` the pointer cell `fp·o₁`, the pointer's target `p·o₂`
(`p` the low limb of the word at `fp·o₁`) and the local cell `fp·o₃`. -/
noncomputable def readAddrs {κ : ℕ} (mem : MemoryImage κ) (fp : K) : LeanIsaInstruction → List K
  | .xor oA oB oC => [fp * oA, fp * oB, fp * oC]
  | .mulNative oA oB oC => [fp * oA, fp * oB, fp * oC]
  | .setConstant o _ => [fp * o]
  | .deref o1 o2 o3 _ => [fp * o1, (mem.limbsAt (fp * o1))[0] * o2, fp * o3]
  | .jump oc od of => [fp * oc, fp * od, fp * of]
  | .keccak om otail ob8 ocap oout _ _ outCells =>
      [fp * om 0,
        fp * om 1,
        fp * om 2,
        fp * om 3,
        fp * (g ^ 0 * otail),
        fp * (g ^ 1 * otail),
        fp * (g ^ 2 * otail),
        fp * (g ^ 3 * otail),
        fp * ob8,
        fp * (g ^ 0 * ocap),
        fp * (g ^ 1 * ocap),
        fp * (g ^ 2 * ocap),
        fp * (g ^ 3 * ocap)] ++
        (List.range outCells.cellCount).map fun k ↦ fp * (g ^ k * oout)

/-- The reads of an instruction's row: each cell it reads, with its count (`cnt` at its position)
and the limbs the image holds there. -/
noncomputable def readsOf {κ : ℕ} (mem : MemoryImage κ) (fp : K) (cnt : ℕ → K) (ins :
    LeanIsaInstruction) :
    List (K × K × Vector K 2) :=
  (readAddrs mem fp ins).mapIdx fun j a ↦ (a, cnt j, mem.limbsAt a)

/-- The output lanes of a `KECCAK` with these operands at `fp` over the image: Keccak-f[1600] of
the state its input cells hold in the layout `inOdd` (`keccakRowOf`'s output lanes). -/
noncomputable def keccakOutLanes {κ : ℕ} (mem : MemoryImage κ) (fp : K) (om : Fin 4 → K)
    (otail ob8 ocap : K) (inOdd : Bool) : Fin 25 → K :=
  stateLanes (keccakF1600 (stateOfCells (keccakInputCells mem fp om otail ob8 ocap) inOdd))

/-- The cancelled pairs of an instruction's row: for a `KECCAK`, each output cell `c` it does not
write (`outCells.cellCount ≤ c`), at its address, with its count (`cnt (13 + c)`, the circuit's
position) and the limbs of the output lanes in the layout `outOdd`, which the row pushes and pulls
alike; none for any other instruction. -/
noncomputable def skipsOf {κ : ℕ} (mem : MemoryImage κ) (fp : K) (cnt : ℕ → K) :
    LeanIsaInstruction → List (K × K × Vector K 2)
  | .keccak om otail ob8 ocap oout inOdd outOdd outCells =>
      ((List.range 13).filter (outCells.cellCount ≤ ·)).map fun c ↦
        (fp * (g ^ c * oout), cnt (13 + c),
          #v[laneLimb (keccakOutLanes mem fp om otail ob8 ocap inOdd) 0
              (cellLanes outOdd (Fin.ofNat 13 c)).1,
            laneLimb (keccakOutLanes mem fp om otail ob8 ocap inOdd) 0
              (cellLanes outOdd (Fin.ofNat 13 c)).2])
  | _ => []

/-! ## The six instructions -/

/-- The `XOR` row of an execution sends the `XOR` messages: the third read carries the limbs of
the word at `fp·o_C`, which the execution makes the sum. -/
theorem xor_exec_sends {κ : ℕ} {mem : MemoryImage κ} {pc fp oA oB oC : K} {next : Registers K}
    (hexec : execute mem ⟨pc, fp⟩ (.xor oA oB oC) = some next) (rA rB rC rbc : K)
    (data : ProverData K) :
    rowSends (opcodeComponent xorTable)
        (Environment.fromArray (rawRow (xorRowOf mem pc fp oA oB oC rA rB rC rbc)) data) =
      sendsOf pc fp next rbc (busEntry (.xor oA oB oC))
        [(fp * oA, rA, mem.limbsAt (fp * oA)), (fp * oB, rB, mem.limbsAt (fp * oB)),
          (fp * oC, rC, mem.limbsAt (fp * oC))] := by
  obtain ⟨⟨hA, hB⟩, hC, rfl⟩ := (xor_refines_iff _ _ _).mp (xorRowOf_refines hexec rA rB rC rbc)
  rw [rowSends_mk, xor_sends_gen _ _ _ _ (eval_rowVar _ data)]
  simp only [xorRowOf] at hC ⊢
  rw [add_limbs] at hC
  have hC' := MemImage.limbsAt_eq_of_read hC
  simp only [limb_ofLimbs] at hC'
  rw [hC']
  simp [sendsOf, memMsgOf, bcMsgOf, busEntry, Registers.next]

/-- The `MUL_NATIVE` row of an execution sends the `MUL_NATIVE` messages: the third read carries
the limbs of the word at `fp·o_C`, which the execution makes the product. -/
theorem mul_exec_sends {κ : ℕ} {mem : MemoryImage κ} {pc fp oA oB oC : K} {next : Registers K}
    (hexec : execute mem ⟨pc, fp⟩ (.mulNative oA oB oC) = some next) (rA rB rC rbc : K)
    (data : ProverData K) :
    rowSends (opcodeComponent mulTable)
        (Environment.fromArray (rawRow (mulRowOf mem pc fp oA oB oC rA rB rC rbc)) data) =
      sendsOf pc fp next rbc (busEntry (.mulNative oA oB oC))
        [(fp * oA, rA, mem.limbsAt (fp * oA)), (fp * oB, rB, mem.limbsAt (fp * oB)),
          (fp * oC, rC, mem.limbsAt (fp * oC))] := by
  obtain ⟨⟨hA, hB⟩, hC, rfl⟩ := (mul_refines_iff _ _ _).mp (mulRowOf_refines hexec rA rB rC rbc)
  rw [rowSends_mk, mul_sends_gen _ _ _ _ (eval_rowVar _ data)]
  simp only [mulRowOf] at hC ⊢
  rw [mul_limbs] at hC
  have hC' := MemImage.limbsAt_eq_of_read hC
  simp only [limb_ofLimbs] at hC'
  rw [hC']
  simp [sendsOf, memMsgOf, bcMsgOf, busEntry, Registers.next]

/-- The `SET_CONSTANT` row of an execution sends the `SET_CONSTANT` messages: its one read carries
the limbs of the immediate. -/
theorem set_exec_sends {κ : ℕ} {mem : MemoryImage κ} {pc fp o : K} {k : E} {next : Registers K}
    (hexec : execute mem ⟨pc, fp⟩ (.setConstant o k) = some next) (rc rbc : K)
    (data : ProverData K) :
    rowSends (opcodeComponent setTable) (Environment.fromArray (rawRow (setRowOf pc fp o k rc rbc)) data) =
      sendsOf pc fp next rbc (busEntry (.setConstant o k)) [(fp * o, rc, mem.limbsAt (fp *
          o))] := by
  obtain ⟨hk, rfl⟩ := (set_refines_iff _ _ _).mp (setRowOf_refines hexec rc rbc)
  rw [rowSends_mk, set_sends_gen _ _ _ _ (eval_rowVar _ data)]
  simp only [setRowOf] at hk ⊢
  have hk' := MemImage.limbsAt_eq_of_read hk
  simp only [limb_ofLimbs, Vector.getElem_mk] at hk'
  rw [hk']
  simp [sendsOf, memMsgOf, bcMsgOf, busEntry, Registers.next]

/-- The `DEREF` row of an execution sends the `DEREF` messages: the pointer cell carries
`(p, 0)`, the target `p·o₂` the limbs of the mode's source, and the local cell its word. -/
theorem deref_exec_sends {κ : ℕ} {mem : MemoryImage κ} {pc fp o1 o2 o3 : K} {mode : DerefMode}
    {next : Registers K} (hexec : execute mem ⟨pc, fp⟩ (.deref o1 o2 o3 mode) = some next)
    (r1 r2 r3 rbc : K) (data : ProverData K) :
    rowSends (opcodeComponent derefTable)
        (Environment.fromArray (rawRow (derefRowOf mem pc fp o1 o2 o3 mode r1 r2 r3 rbc)) data) =
      sendsOf pc fp next rbc (busEntry (.deref o1 o2 o3 mode))
        [(fp * o1, r1, mem.limbsAt (fp * o1)),
          ((mem.limbsAt (fp * o1))[0] * o2, r2, mem.limbsAt ((mem.limbsAt (fp * o1))[0] * o2)),
          (fp * o3, r3, mem.limbsAt (fp * o3))] := by
  obtain ⟨mode', ⟨hflags, h1, h3⟩, h2, rfl⟩ :=
    (deref_refines_iff _ _ _).mp (derefRowOf_refines hexec r1 r2 r3 rbc)
  rw [rowSends_mk, deref_sends_gen _ _ _ _ (eval_rowVar _ data)]
  simp only [derefRowOf] at hflags h1 h3 h2 ⊢
  obtain ⟨h4, h5⟩ := Prod.ext_iff.mp hflags
  -- the pointer cell holds `(p, 0)`
  have e1 := MemImage.limbsAt_eq_of_read h1
  simp only [limb0_ofLimbs, limb1_ofLimbs] at e1
  have e1' : (mem.limbsAt (fp * o1))[1] = 0 := by rw [e1]; rfl
  -- the target cell holds the limbs of the mode's source
  have e2 := MemImage.limbsAt_eq_of_read h2
  rw [← storeCoords_eval, h4, h5] at e2
  simp only [limb0_ofLimbs, limb1_ofLimbs] at e2
  simp [sendsOf, memMsgOf, bcMsgOf, busEntry, Registers.next, e1', e2]

/-- The indicator slot of a `JUMP` raw row is its second witness. -/
theorem jumpRaw_get_indicator (r : JumpRow K) (w b : K) (data : ProverData K) :
    (Environment.fromArray (jumpRaw r w b) data).get (size JumpRow + 1) = b := by
  show ((rawRow r ++ #[w, b])[size JumpRow + 1]?).getD 0 = b
  rw [Array.getElem?_append_right (by rw [rawRow_size]; omega), rawRow_size]
  simp

/-- The sends of a `JUMP` raw row, in closed form: the pushed successor reads the indicator `b`. -/
theorem jumpRaw_sends (r : JumpRow K) (w b : K) (data : ProverData K) :
    rowSends (opcodeComponent jumpTable) (Environment.fromArray (jumpRaw r w b) data) =
      [(StatePull.name, #[r.pc, r.fp]),
       (StatePush.name, #[b * r.vpc + b * (g * r.pc) + g * r.pc, b * r.vfp + b * r.fp + r.fp]),
       (BytecodePull.name, #[r.pc, r.rbc, Opcode.jump.busCode, r.oc, r.od, r.of, 0, 0, 0, 0, 0,
           0, 0, 0, 0]),
       (BytecodePush.name, #[r.pc, g * r.rbc, Opcode.jump.busCode, r.oc, r.od, r.of, 0, 0, 0, 0, 0,
           0, 0, 0, 0]),
       (MemPull.name, #[r.fp * r.oc, r.rc, r.vcond, 0]),
       (MemPush.name, #[r.fp * r.oc, g * r.rc, r.vcond, 0]),
       (MemPull.name, #[r.fp * r.od, r.rd, r.vpc, 0]),
       (MemPush.name, #[r.fp * r.od, g * r.rd, r.vpc, 0]),
       (MemPull.name, #[r.fp * r.of, r.rf, r.vfp, 0]),
       (MemPush.name, #[r.fp * r.of, g * r.rf, r.vfp, 0])] :=
  jump_sends_gen (varFromOffset JumpRow 0) (Environment.fromArray (jumpRaw r w b) data)
    (size JumpRow) r (eval_rowVar_append r #[w, b] data) b (jumpRaw_get_indicator r w b data)

/-- The `JUMP` row of an execution, with its honest local witnesses, sends the `JUMP` messages:
the condition, destination and frame cells carry `(v, 0)` for the words in `K` they hold, and
the pushed successor is the destination and frame when the condition is nonzero and the
fall-through otherwise. -/
theorem jump_exec_sends {κ : ℕ} {mem : MemoryImage κ} {pc fp oc od of : K} {next : Registers K}
    (hexec : execute mem ⟨pc, fp⟩ (.jump oc od of) = some next) (rc rd rf rbc : K)
    (data : ProverData K) :
    rowSends (opcodeComponent jumpTable)
        (Environment.fromArray
          (jumpRaw (jumpRowOf mem pc fp oc od of rc rd rf rbc)
            (if (mem.limbsAt (fp * oc))[0] = 0 then 0 else ((mem.limbsAt (fp * oc))[0])⁻¹)
            (if (mem.limbsAt (fp * oc))[0] = 0 then 0 else 1)) data) =
      sendsOf pc fp next rbc (busEntry (.jump oc od of))
        [(fp * oc, rc, mem.limbsAt (fp * oc)), (fp * od, rd, mem.limbsAt (fp * od)),
          (fp * of, rf, mem.limbsAt (fp * of))] := by
  obtain ⟨⟨hc, hd, hf⟩, hnext⟩ := (jump_refines_iff _ _ _).mp (jumpRowOf_refines hexec rc rd rf rbc)
  rw [jumpRaw_sends]
  simp only [jumpRowOf] at hc hd hf hnext ⊢
  have ec := MemImage.limbsAt_eq_of_read hc
  have ed := MemImage.limbsAt_eq_of_read hd
  have ef := MemImage.limbsAt_eq_of_read hf
  simp only [limb0_ofLimbs, limb1_ofLimbs] at ec ed ef
  have ec1 : (mem.limbsAt (fp * oc))[1] = 0 := by rw [ec]; rfl
  have ed1 : (mem.limbsAt (fp * od))[1] = 0 := by rw [ed]; rfl
  have ef1 : (mem.limbsAt (fp * of))[1] = 0 := by rw [ef]; rfl
  subst hnext
  by_cases h0 : (mem.limbsAt (fp * oc))[0] = 0
  · simp [sendsOf, memMsgOf, bcMsgOf, busEntry, Registers.next, h0, ec1, ed1, ef1]
  · simp [sendsOf, memMsgOf, bcMsgOf, busEntry, h0, ec1, ed1, ef1, add_assoc,
      CharTwo.add_self_eq_zero]

/-- A memory message is its address, its count, then its limbs. -/
theorem memMsgOf_eq (a c : K) (v : Vector K 2) : memMsgOf a c v = #[a, c] ++ v.toArray := by
  obtain ⟨⟨l⟩, hl⟩ := v
  match l, hl with
  | [_, _], _ => rfl

/-- The limbs the image holds at an address that holds a cell of lanes. -/
theorem limbsAt_laneCells {κ : ℕ} {mem : MemoryImage κ} {a : K} {L : Fin 25 → K} {odd : Bool}
    {free : K} {c : Fin 13} (h : mem.read a = some (laneCells L odd free c)) :
    mem.limbsAt a = #v[laneLimb L free (cellLanes odd c).1, laneLimb L free (cellLanes odd c).2] := by
  rw [MemImage.limbsAt_eq_of_read h]
  simp [laneCells, limb_ofLimbs]

/-- `x + y + x = y` in characteristic two. -/
theorem add_add_self_left (x y : K) : x + y + x = y := by
  rw [add_comm x y, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The `KECCAK` row of an execution sends the `KECCAK` messages: each of the cells it reads and
writes carries the limbs of its lanes in its layout, its reads numbered by
`cnt` in the circuit's order; each output cell it does not write is a cancelled pair carrying the
output lanes' limbs (`skipsOf`). -/
theorem keccak_exec_sends {κ : ℕ} {mem : MemoryImage κ} {pc fp : K} {om : Fin 4 → K}
    {otail ob8 ocap oout : K} {inOdd outOdd : Bool} {outCells : KeccakOutputCells}
    {next : Registers K}
    (hexec : execute mem ⟨pc, fp⟩ (.keccak om otail ob8 ocap oout inOdd outOdd outCells) =
      some next)
    (cnt : ℕ → K) (rbc : K) (data : ProverData K) :
    rowSends (opcodeComponent keccakTable)
        (Environment.fromArray (rawRow (keccakRowOf mem pc fp om otail ob8 ocap oout inOdd outOdd
          outCells (Vector.ofFn fun j ↦ cnt j) rbc)) data) =
      sendsOf pc fp next rbc (busEntry (.keccak om otail ob8 ocap oout inOdd outOdd outCells))
          (readsOf mem fp cnt (.keccak om otail ob8 ocap oout inOdd outOdd outCells)) ++
        skipSends (skipsOf mem fp cnt (.keccak om otail ob8 ocap oout inOdd outOdd outCells)) := by
  have hb := keccakRowOf_bindings hexec (Vector.ofFn fun j ↦ cnt j) rbc
  obtain ⟨-, -, -, -, -, rfl⟩ := (execute_keccak_eq_some_iff _ _ _ _ _ _ _ _ _ _ _).mp hexec
  set R := keccakRowOf mem pc fp om otail ob8 ocap oout inOdd outOdd outCells
    (Vector.ofFn fun j ↦ cnt j) rbc with hR
  have hRoms : R.oms = om := keccakRowOf_oms ..
  have hRf : R.fp = fp := rfl
  have hRt : R.otail = otail := rfl
  have hRb : R.ob8 = ob8 := rfl
  have hRc : R.ocap = ocap := rfl
  have hRo : R.oout = oout := rfl
  have hL0 : mem.limbsAt (fp * om 0) =
      #v[laneLimb R.inLanes R.free (cellLanes inOdd 0).1, laneLimb R.inLanes R.free (cellLanes inOdd 0).2] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInputCellOffset] using limbsAt_laneCells (hb.in_eq ⟨0, by decide⟩)
  have hL1 : mem.limbsAt (fp * om 1) =
      #v[laneLimb R.inLanes R.free (cellLanes inOdd 1).1, laneLimb R.inLanes R.free (cellLanes inOdd 1).2] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInputCellOffset] using limbsAt_laneCells (hb.in_eq ⟨1, by decide⟩)
  have hL2 : mem.limbsAt (fp * om 2) =
      #v[laneLimb R.inLanes R.free (cellLanes inOdd 2).1, laneLimb R.inLanes R.free (cellLanes inOdd 2).2] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInputCellOffset] using limbsAt_laneCells (hb.in_eq ⟨2, by decide⟩)
  have hL3 : mem.limbsAt (fp * om 3) =
      #v[laneLimb R.inLanes R.free (cellLanes inOdd 3).1, laneLimb R.inLanes R.free (cellLanes inOdd 3).2] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInputCellOffset] using limbsAt_laneCells (hb.in_eq ⟨3, by decide⟩)
  have hL4 : mem.limbsAt (fp * (g ^ 0 * otail)) =
      #v[laneLimb R.inLanes R.free (cellLanes inOdd 4).1, laneLimb R.inLanes R.free (cellLanes inOdd 4).2] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInputCellOffset] using limbsAt_laneCells (hb.in_eq ⟨4, by decide⟩)
  have hL5 : mem.limbsAt (fp * (g ^ 1 * otail)) =
      #v[laneLimb R.inLanes R.free (cellLanes inOdd 5).1, laneLimb R.inLanes R.free (cellLanes inOdd 5).2] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInputCellOffset] using limbsAt_laneCells (hb.in_eq ⟨5, by decide⟩)
  have hL6 : mem.limbsAt (fp * (g ^ 2 * otail)) =
      #v[laneLimb R.inLanes R.free (cellLanes inOdd 6).1, laneLimb R.inLanes R.free (cellLanes inOdd 6).2] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInputCellOffset] using limbsAt_laneCells (hb.in_eq ⟨6, by decide⟩)
  have hL7 : mem.limbsAt (fp * (g ^ 3 * otail)) =
      #v[laneLimb R.inLanes R.free (cellLanes inOdd 7).1, laneLimb R.inLanes R.free (cellLanes inOdd 7).2] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInputCellOffset] using limbsAt_laneCells (hb.in_eq ⟨7, by decide⟩)
  have hL8 : mem.limbsAt (fp * ob8) =
      #v[laneLimb R.inLanes R.free (cellLanes inOdd 8).1, laneLimb R.inLanes R.free (cellLanes inOdd 8).2] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInputCellOffset] using limbsAt_laneCells (hb.in_eq ⟨8, by decide⟩)
  have hL9 : mem.limbsAt (fp * (g ^ 0 * ocap)) =
      #v[laneLimb R.inLanes R.free (cellLanes inOdd 9).1, laneLimb R.inLanes R.free (cellLanes inOdd 9).2] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInputCellOffset] using limbsAt_laneCells (hb.in_eq ⟨9, by decide⟩)
  have hL10 : mem.limbsAt (fp * (g ^ 1 * ocap)) =
      #v[laneLimb R.inLanes R.free (cellLanes inOdd 10).1, laneLimb R.inLanes R.free (cellLanes inOdd 10).2] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInputCellOffset] using limbsAt_laneCells (hb.in_eq ⟨10, by decide⟩)
  have hL11 : mem.limbsAt (fp * (g ^ 2 * ocap)) =
      #v[laneLimb R.inLanes R.free (cellLanes inOdd 11).1, laneLimb R.inLanes R.free (cellLanes inOdd 11).2] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInputCellOffset] using limbsAt_laneCells (hb.in_eq ⟨11, by decide⟩)
  have hL12 : mem.limbsAt (fp * (g ^ 3 * ocap)) =
      #v[laneLimb R.inLanes R.free (cellLanes inOdd 12).1, laneLimb R.inLanes R.free (cellLanes inOdd 12).2] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInputCellOffset] using limbsAt_laneCells (hb.in_eq ⟨12, by decide⟩)
  rw [rowSends_mk, keccak_sends_gen _ _ _ _ (eval_rowVar _ data)]
  cases outCells
  · -- `one`: the first 1 output cell written
    have hO0 : mem.limbsAt (fp * (g ^ 0 * oout)) =
        #v[laneLimb R.outLanes 0 (cellLanes outOdd 0).1, laneLimb R.outLanes 0 (cellLanes outOdd 0).2] := by
      simpa [hRf, hRo] using limbsAt_laneCells (hb.out_eq ⟨0, by decide⟩ (by decide))
    simp only [sendsOf, skipSends, readsOf, readAddrs, skipsOf, KeccakOutputCells.cellCount,
      List.range_succ, List.range_zero, List.filter, List.map, List.mapIdx_cons, List.mapIdx_nil,
      List.nil_append, List.cons_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      memMsgOf_eq]
    simp only [Nat.reduceLeDiff, decide_true, decide_false] at *
    rw [hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7, hL8, hL9, hL10, hL11, hL12, hO0]
    cases inOdd <;> cases outOdd <;> simp [hR, keccakRowOf, KeccakRow.inLanes, KeccakRow.outLanes,
      bcMsgOf, laneLimb, cellLanes, busEntry, Registers.next, layoutFlagWord, keccakOutputFlags, keccakOutLanes,
      CharTwo.add_self_eq_zero]
  · -- `two`: the first 2 output cells written
    have hO0 : mem.limbsAt (fp * (g ^ 0 * oout)) =
        #v[laneLimb R.outLanes 0 (cellLanes outOdd 0).1, laneLimb R.outLanes 0 (cellLanes outOdd 0).2] := by
      simpa [hRf, hRo] using limbsAt_laneCells (hb.out_eq ⟨0, by decide⟩ (by decide))
    have hO1 : mem.limbsAt (fp * (g ^ 1 * oout)) =
        #v[laneLimb R.outLanes 0 (cellLanes outOdd 1).1, laneLimb R.outLanes 0 (cellLanes outOdd 1).2] := by
      simpa [hRf, hRo] using limbsAt_laneCells (hb.out_eq ⟨1, by decide⟩ (by decide))
    simp only [sendsOf, skipSends, readsOf, readAddrs, skipsOf, KeccakOutputCells.cellCount,
      List.range_succ, List.range_zero, List.filter, List.map, List.mapIdx_cons, List.mapIdx_nil,
      List.nil_append, List.cons_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      memMsgOf_eq]
    simp only [Nat.reduceLeDiff, decide_true, decide_false] at *
    rw [hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7, hL8, hL9, hL10, hL11, hL12, hO0, hO1]
    cases inOdd <;> cases outOdd <;> simp [hR, keccakRowOf, KeccakRow.inLanes, KeccakRow.outLanes,
      bcMsgOf, laneLimb, cellLanes, busEntry, Registers.next, layoutFlagWord, keccakOutputFlags, keccakOutLanes,
      CharTwo.add_self_eq_zero, add_add_self_left]
  · -- `all`: the first 13 output cells written
    have hO0 : mem.limbsAt (fp * (g ^ 0 * oout)) =
        #v[laneLimb R.outLanes 0 (cellLanes outOdd 0).1, laneLimb R.outLanes 0 (cellLanes outOdd 0).2] := by
      simpa [hRf, hRo] using limbsAt_laneCells (hb.out_eq ⟨0, by decide⟩ (by decide))
    have hO1 : mem.limbsAt (fp * (g ^ 1 * oout)) =
        #v[laneLimb R.outLanes 0 (cellLanes outOdd 1).1, laneLimb R.outLanes 0 (cellLanes outOdd 1).2] := by
      simpa [hRf, hRo] using limbsAt_laneCells (hb.out_eq ⟨1, by decide⟩ (by decide))
    have hO2 : mem.limbsAt (fp * (g ^ 2 * oout)) =
        #v[laneLimb R.outLanes 0 (cellLanes outOdd 2).1, laneLimb R.outLanes 0 (cellLanes outOdd 2).2] := by
      simpa [hRf, hRo] using limbsAt_laneCells (hb.out_eq ⟨2, by decide⟩ (by decide))
    have hO3 : mem.limbsAt (fp * (g ^ 3 * oout)) =
        #v[laneLimb R.outLanes 0 (cellLanes outOdd 3).1, laneLimb R.outLanes 0 (cellLanes outOdd 3).2] := by
      simpa [hRf, hRo] using limbsAt_laneCells (hb.out_eq ⟨3, by decide⟩ (by decide))
    have hO4 : mem.limbsAt (fp * (g ^ 4 * oout)) =
        #v[laneLimb R.outLanes 0 (cellLanes outOdd 4).1, laneLimb R.outLanes 0 (cellLanes outOdd 4).2] := by
      simpa [hRf, hRo] using limbsAt_laneCells (hb.out_eq ⟨4, by decide⟩ (by decide))
    have hO5 : mem.limbsAt (fp * (g ^ 5 * oout)) =
        #v[laneLimb R.outLanes 0 (cellLanes outOdd 5).1, laneLimb R.outLanes 0 (cellLanes outOdd 5).2] := by
      simpa [hRf, hRo] using limbsAt_laneCells (hb.out_eq ⟨5, by decide⟩ (by decide))
    have hO6 : mem.limbsAt (fp * (g ^ 6 * oout)) =
        #v[laneLimb R.outLanes 0 (cellLanes outOdd 6).1, laneLimb R.outLanes 0 (cellLanes outOdd 6).2] := by
      simpa [hRf, hRo] using limbsAt_laneCells (hb.out_eq ⟨6, by decide⟩ (by decide))
    have hO7 : mem.limbsAt (fp * (g ^ 7 * oout)) =
        #v[laneLimb R.outLanes 0 (cellLanes outOdd 7).1, laneLimb R.outLanes 0 (cellLanes outOdd 7).2] := by
      simpa [hRf, hRo] using limbsAt_laneCells (hb.out_eq ⟨7, by decide⟩ (by decide))
    have hO8 : mem.limbsAt (fp * (g ^ 8 * oout)) =
        #v[laneLimb R.outLanes 0 (cellLanes outOdd 8).1, laneLimb R.outLanes 0 (cellLanes outOdd 8).2] := by
      simpa [hRf, hRo] using limbsAt_laneCells (hb.out_eq ⟨8, by decide⟩ (by decide))
    have hO9 : mem.limbsAt (fp * (g ^ 9 * oout)) =
        #v[laneLimb R.outLanes 0 (cellLanes outOdd 9).1, laneLimb R.outLanes 0 (cellLanes outOdd 9).2] := by
      simpa [hRf, hRo] using limbsAt_laneCells (hb.out_eq ⟨9, by decide⟩ (by decide))
    have hO10 : mem.limbsAt (fp * (g ^ 10 * oout)) =
        #v[laneLimb R.outLanes 0 (cellLanes outOdd 10).1, laneLimb R.outLanes 0 (cellLanes outOdd 10).2] := by
      simpa [hRf, hRo] using limbsAt_laneCells (hb.out_eq ⟨10, by decide⟩ (by decide))
    have hO11 : mem.limbsAt (fp * (g ^ 11 * oout)) =
        #v[laneLimb R.outLanes 0 (cellLanes outOdd 11).1, laneLimb R.outLanes 0 (cellLanes outOdd 11).2] := by
      simpa [hRf, hRo] using limbsAt_laneCells (hb.out_eq ⟨11, by decide⟩ (by decide))
    have hO12 : mem.limbsAt (fp * (g ^ 12 * oout)) =
        #v[laneLimb R.outLanes 0 (cellLanes outOdd 12).1, laneLimb R.outLanes 0 (cellLanes outOdd 12).2] := by
      simpa [hRf, hRo] using limbsAt_laneCells (hb.out_eq ⟨12, by decide⟩ (by decide))
    simp only [sendsOf, skipSends, readsOf, readAddrs, skipsOf, KeccakOutputCells.cellCount,
      List.range_succ, List.range_zero, List.filter, List.map, List.mapIdx_cons, List.mapIdx_nil,
      List.nil_append, List.cons_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      memMsgOf_eq]
    simp only [Nat.reduceLeDiff, decide_false] at *
    rw [hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7, hL8, hL9, hL10, hL11, hL12, hO0, hO1, hO2, hO3, hO4, hO5, hO6, hO7, hO8, hO9, hO10, hO11, hO12]
    cases inOdd <;> cases outOdd <;> simp [hR, keccakRowOf, KeccakRow.inLanes, KeccakRow.outLanes,
      bcMsgOf, laneLimb, cellLanes, busEntry, Registers.next, layoutFlagWord, keccakOutputFlags, keccakOutLanes,
      CharTwo.add_self_eq_zero, add_add_self_left]

/-! ## Every cell an instruction reads is an address -/

/-- Every cell an executing instruction reads is an address of the image: the execution reads it
(`*_refines_iff`, the bindings and the result cell). -/
theorem readAddrs_valid {κ : ℕ} {mem : MemoryImage κ} {pc fp : K} {ins : LeanIsaInstruction} {next :
    Registers K}
    (hexec : execute mem ⟨pc, fp⟩ ins = some next) :
    ∀ a ∈ readAddrs mem fp ins, ∃ w, mem.read a = some w := by
  cases ins with
  | xor oA oB oC =>
    obtain ⟨⟨hA, hB⟩, hC, -⟩ := (xor_refines_iff _ _ _).mp (xorRowOf_refines hexec 1 1 1 1)
    simp only [readAddrs, List.mem_cons, List.not_mem_nil, or_false]
    rintro a (rfl | rfl | rfl)
    exacts [⟨_, hA⟩, ⟨_, hB⟩, ⟨_, hC⟩]
  | mulNative oA oB oC =>
    obtain ⟨⟨hA, hB⟩, hC, -⟩ := (mul_refines_iff _ _ _).mp (mulRowOf_refines hexec 1 1 1 1)
    simp only [readAddrs, List.mem_cons, List.not_mem_nil, or_false]
    rintro a (rfl | rfl | rfl)
    exacts [⟨_, hA⟩, ⟨_, hB⟩, ⟨_, hC⟩]
  | setConstant o k =>
    obtain ⟨hk, -⟩ := (set_refines_iff _ _ _).mp (setRowOf_refines hexec 1 1)
    simp only [readAddrs, List.mem_cons, List.not_mem_nil, or_false]
    rintro a rfl
    exact ⟨_, hk⟩
  | deref o1 o2 o3 mode =>
    obtain ⟨mode', ⟨-, h1, h3⟩, h2, -⟩ :=
      (deref_refines_iff _ _ _).mp (derefRowOf_refines hexec 1 1 1 1)
    simp only [readAddrs, List.mem_cons, List.not_mem_nil, or_false]
    rintro a (rfl | rfl | rfl)
    exacts [⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩]
  | jump oc od of =>
    obtain ⟨⟨hc, hd, hf⟩, -⟩ := (jump_refines_iff _ _ _).mp (jumpRowOf_refines hexec 1 1 1 1)
    simp only [readAddrs, List.mem_cons, List.not_mem_nil, or_false]
    rintro a (rfl | rfl | rfl)
    exacts [⟨_, hc⟩, ⟨_, hd⟩, ⟨_, hf⟩]
  | keccak om otail ob8 ocap oout inOdd outOdd outCells =>
    obtain ⟨input, output, hin, hout, -, -⟩ :=
      (execute_keccak_eq_some_iff _ _ _ _ _ _ _ _ _ _ _).mp hexec
    intro a ha
    simp only [readAddrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map, List.mem_range] at ha
    rcases ha with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
      ⟨k, hk, rfl⟩
    · exact ⟨_, by simpa [keccakInputCellOffset] using hin ⟨0, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInputCellOffset] using hin ⟨1, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInputCellOffset] using hin ⟨2, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInputCellOffset] using hin ⟨3, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInputCellOffset] using hin ⟨4, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInputCellOffset] using hin ⟨5, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInputCellOffset] using hin ⟨6, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInputCellOffset] using hin ⟨7, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInputCellOffset] using hin ⟨8, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInputCellOffset] using hin ⟨9, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInputCellOffset] using hin ⟨10, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInputCellOffset] using hin ⟨11, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInputCellOffset] using hin ⟨12, by decide⟩⟩
    · have hk13 : k < 13 := lt_of_lt_of_le hk (by cases outCells <;> decide)
      exact ⟨_, hout ⟨k, hk13⟩ hk⟩

/-! ## The row of an instruction -/

/-- The table of each opcode, in the ensemble's order (`leanIsaEnsemble`). -/
def opComponent : Opcode → Component K
  | .xor => opcodeComponent xorTable
  | .mulNative => opcodeComponent mulTable
  | .setConstant => opcodeComponent setTable
  | .deref => opcodeComponent derefTable
  | .jump => opcodeComponent jumpTable
  | .keccak => opcodeComponent keccakTable

/-- The width of a raw row of each opcode's table: the row's columns, and for `JUMP` its two
local witnesses. -/
def opWidth : Opcode → ℕ
  | .xor => size XorRow
  | .mulNative => size MulRow
  | .setConstant => size SetRow
  | .deref => size DerefRow
  | .jump => size JumpRow + 2
  | .keccak => size KeccakRow

/-- The raw row of an instruction executed from `(pc, fp)` over the image `mem`: the typed row of
its table with the read counts `cnt` (positionally, in the order the circuit reads) and the
bytecode count `rbc`, and for `JUMP` the honest inverse and indicator of the condition. -/
noncomputable def rowOf {κ : ℕ} (mem : MemoryImage κ) (pc fp : K) (cnt : ℕ → K) (rbc : K) :
    LeanIsaInstruction → Array K
  | .xor oA oB oC => rawRow (xorRowOf mem pc fp oA oB oC (cnt 0) (cnt 1) (cnt 2) rbc)
  | .mulNative oA oB oC => rawRow (mulRowOf mem pc fp oA oB oC (cnt 0) (cnt 1) (cnt 2) rbc)
  | .setConstant o k => rawRow (setRowOf pc fp o k (cnt 0) rbc)
  | .deref o1 o2 o3 mode =>
      rawRow (derefRowOf mem pc fp o1 o2 o3 mode (cnt 0) (cnt 1) (cnt 2) rbc)
  | .jump oc od of =>
      jumpRaw (jumpRowOf mem pc fp oc od of (cnt 0) (cnt 1) (cnt 2) rbc)
        (if (mem.limbsAt (fp * oc))[0] = 0 then 0 else ((mem.limbsAt (fp * oc))[0])⁻¹)
        (if (mem.limbsAt (fp * oc))[0] = 0 then 0 else 1)
  | .keccak om otail ob8 ocap oout inOdd outOdd outCells =>
      rawRow (keccakRowOf mem pc fp om otail ob8 ocap oout inOdd outOdd outCells
        (Vector.ofFn fun j ↦ cnt j) rbc)

/-- The raw row of an instruction has the width of its table. -/
theorem rowOf_size {κ : ℕ} (mem : MemoryImage κ) (pc fp : K) (cnt : ℕ → K) (rbc : K) (ins :
    LeanIsaInstruction) :
    (rowOf mem pc fp cnt rbc ins).size = opWidth ins.opcode := by
  cases ins <;> simp [rowOf, opWidth, LeanIsaInstruction.opcode, rawRow_size, jumpRaw]

/-- **The row of an executing instruction sends `sendsOf`.** If the instruction executes from
`(pc, fp)` to `next`, its row, in its table, sends the state step from `(pc, fp)` to `next`, the
bytecode read of its entry at `pc`, and the reads of the cells it reads with the counts `cnt`;
then, for a `KECCAK` writing fewer than thirteen cells, a cancelled pair per cell it does not
write (`skipsOf`). -/
theorem rowOf_sends {κ : ℕ} {mem : MemoryImage κ} {pc fp : K} {ins : LeanIsaInstruction} {next :
    Registers K}
    (hexec : execute mem ⟨pc, fp⟩ ins = some next) (cnt : ℕ → K) (rbc : K)
    (data : ProverData K) :
    rowSends (opComponent ins.opcode)
        (Environment.fromArray (rowOf mem pc fp cnt rbc ins) data) =
      sendsOf pc fp next rbc (busEntry ins) (readsOf mem fp cnt ins) ++
        skipSends (skipsOf mem fp cnt ins) := by
  cases ins with
  | xor oA oB oC =>
    simp only [LeanIsaInstruction.opcode, opComponent]
    rw [rowOf, xor_exec_sends hexec]
    simp [readsOf, readAddrs, skipsOf, skipSends]
  | mulNative oA oB oC =>
    simp only [LeanIsaInstruction.opcode, opComponent]
    rw [rowOf, mul_exec_sends hexec]
    simp [readsOf, readAddrs, skipsOf, skipSends]
  | setConstant o k =>
    simp only [LeanIsaInstruction.opcode, opComponent]
    rw [rowOf, set_exec_sends hexec]
    simp [readsOf, readAddrs, skipsOf, skipSends]
  | deref o1 o2 o3 mode =>
    simp only [LeanIsaInstruction.opcode, opComponent]
    rw [rowOf, deref_exec_sends hexec]
    simp [readsOf, readAddrs, skipsOf, skipSends]
  | jump oc od of =>
    simp only [LeanIsaInstruction.opcode, opComponent]
    rw [rowOf, jump_exec_sends hexec]
    simp [readsOf, readAddrs, skipsOf, skipSends]
  | keccak om otail ob8 ocap oout inOdd outOdd outCells =>
    simp only [LeanIsaInstruction.opcode, opComponent]
    rw [rowOf, keccak_exec_sends hexec]

end LeanVM.Arithmetization
