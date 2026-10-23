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
theorem MemImage.limbsAt_eq_of_read {κ : ℕ} {L : MemImage κ} {a : K} {v : E}
    (h : L.read a = some v) : L.limbsAt a = #v[v.limb 0, v.limb 1, v.limb 2] := by
  unfold MemImage.limbsAt
  rw [h]

/-- The three limbs of `E.ofLimbs`, one by one. -/
theorem limb0_ofLimbs (c0 c1 c2 : K) : (E.ofLimbs c0 c1 c2).limb 0 = c0 := rfl

/-- The second limb of `E.ofLimbs`. -/
theorem limb1_ofLimbs (c0 c1 c2 : K) : (E.ofLimbs c0 c1 c2).limb 1 = c1 := rfl

/-- The third limb of `E.ofLimbs`. -/
theorem limb2_ofLimbs (c0 c1 c2 : K) : (E.ofLimbs c0 c1 c2).limb 2 = c2 := rfl

/-! ## The messages -/

/-- The array a memory message `(addr, count, v)` flattens to. -/
def memMsgOf (a c : K) (v : Vector K 3) : Array K := #[a, c, v[0], v[1], v[2]]

/-- The array a bytecode message `(pc, count, entry)` flattens to. -/
def bcMsgOf (pc c : K) (e : Vector K 8) : Array K :=
  #[pc, c, e[0], e[1], e[2], e[3], e[4], e[5], e[6], e[7]]

/-- What a row sends: the state pull `(pc, fp)` and push `next`, the bytecode pull of `e` at `pc`
with count `rbc` and the push with count `g·rbc`, then for each read `(addr, count, v)` the
memory pull and the memory push with count `g·count`, in the circuits' order. -/
def sendsOf (pc fp : K) (next : Regs K) (rbc : K) (e : Vector K 8)
    (reads : List (K × K × Vector K 3)) : List (String × Array K) :=
  [(StatePull.name, #[pc, fp]), (StatePush.name, #[next.pc, next.fp]),
    (BytecodePull.name, bcMsgOf pc rbc e), (BytecodePush.name, bcMsgOf pc (g * rbc) e)] ++
  reads.flatMap fun x ↦
    [(MemPull.name, memMsgOf x.1 x.2.1 x.2.2), (MemPush.name, memMsgOf x.1 (g * x.2.1) x.2.2)]

/-- A row circuit's sends are those of its main at the row variable. -/
theorem rowSends_mk {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (c : GeneralFormalCircuit K Input Output) (env : Environment K) :
    rowSends ⟨c⟩ env =
      (((c.main (varFromOffset Input 0)).operations (size Input)).interactionValues env).map
        (fun i ↦ (i.channel.name, i.msg)) := rfl

/-! ## The cells an instruction reads -/

/-- The cells an instruction reads, in the order its row's reads carry them (the circuits'
order): the operand cells, and for `DEREF` the pointer cell `fp·o₁`, the pointer's target `p·o₂`
(`p` the low limb of the word at `fp·o₁`) and the local cell `fp·o₃`. -/
noncomputable def readAddrs {κ : ℕ} (mem : MemImage κ) (fp : K) : Instr → List K
  | .xor oA oB oC => [fp * oA, fp * oB, fp * oC]
  | .mulNative oA oB oC => [fp * oA, fp * oB, fp * oC]
  | .setConstant o _ => [fp * o]
  | .deref o1 o2 o3 _ => [fp * o1, (mem.limbsAt (fp * o1))[0] * o2, fp * o3]
  | .jump oc od of => [fp * oc, fp * od, fp * of]
  | .blake2s om ocv oout omd =>
      [fp * om 0, fp * om 1, fp * om 2, fp * om 3, fp * ocv, fp * (g * ocv), fp * oout,
        fp * (g * oout), fp * omd]

/-- The reads of an instruction's row: each cell it reads, with its count (`cnt` at its position)
and the limbs the image holds there. -/
noncomputable def readsOf {κ : ℕ} (mem : MemImage κ) (fp : K) (cnt : ℕ → K) (ins : Instr) :
    List (K × K × Vector K 3) :=
  (readAddrs mem fp ins).mapIdx fun j a ↦ (a, cnt j, mem.limbsAt a)

/-! ## The six instructions -/

/-- The `XOR` row of an execution sends the `XOR` messages: the third read carries the limbs of
the word at `fp·o_C`, which the execution makes the sum. -/
theorem xor_exec_sends {κ : ℕ} {mem : MemImage κ} {pc fp oA oB oC : K} {next : Regs K}
    (hexec : execute mem ⟨pc, fp⟩ (.xor oA oB oC) = some next) (rA rB rC rbc : K)
    (data : ProverData K) :
    rowSends ⟨xorTable⟩
        (Environment.fromArray (rawRow (xorRowOf mem pc fp oA oB oC rA rB rC rbc)) data) =
      sendsOf pc fp next rbc (entry (.xor oA oB oC))
        [(fp * oA, rA, mem.limbsAt (fp * oA)), (fp * oB, rB, mem.limbsAt (fp * oB)),
          (fp * oC, rC, mem.limbsAt (fp * oC))] := by
  obtain ⟨⟨hA, hB⟩, hC, rfl⟩ := (xor_refines_iff _ _ _).mp (xorRowOf_refines hexec rA rB rC rbc)
  rw [rowSends_mk, xor_sends_gen _ _ _ _ (eval_rowVar _ data)]
  simp only [xorRowOf] at hC ⊢
  rw [add_limbs] at hC
  have hC' := MemImage.limbsAt_eq_of_read hC
  simp only [limb_ofLimbs] at hC'
  rw [hC']
  simp [sendsOf, memMsgOf, bcMsgOf, entry, Regs.next]

/-- The `MUL_NATIVE` row of an execution sends the `MUL_NATIVE` messages: the third read carries
the limbs of the word at `fp·o_C`, which the execution makes the product. -/
theorem mul_exec_sends {κ : ℕ} {mem : MemImage κ} {pc fp oA oB oC : K} {next : Regs K}
    (hexec : execute mem ⟨pc, fp⟩ (.mulNative oA oB oC) = some next) (rA rB rC rbc : K)
    (data : ProverData K) :
    rowSends ⟨mulTable⟩
        (Environment.fromArray (rawRow (mulRowOf mem pc fp oA oB oC rA rB rC rbc)) data) =
      sendsOf pc fp next rbc (entry (.mulNative oA oB oC))
        [(fp * oA, rA, mem.limbsAt (fp * oA)), (fp * oB, rB, mem.limbsAt (fp * oB)),
          (fp * oC, rC, mem.limbsAt (fp * oC))] := by
  obtain ⟨⟨hA, hB⟩, hC, rfl⟩ := (mul_refines_iff _ _ _).mp (mulRowOf_refines hexec rA rB rC rbc)
  rw [rowSends_mk, mul_sends_gen _ _ _ _ (eval_rowVar _ data)]
  simp only [mulRowOf] at hC ⊢
  rw [mul_limbs] at hC
  have hC' := MemImage.limbsAt_eq_of_read hC
  simp only [limb_ofLimbs] at hC'
  rw [hC']
  simp [sendsOf, memMsgOf, bcMsgOf, entry, Regs.next]

/-- The `SET_CONSTANT` row of an execution sends the `SET_CONSTANT` messages: its one read carries
the limbs of the immediate. -/
theorem set_exec_sends {κ : ℕ} {mem : MemImage κ} {pc fp o : K} {k : E} {next : Regs K}
    (hexec : execute mem ⟨pc, fp⟩ (.setConstant o k) = some next) (rc rbc : K)
    (data : ProverData K) :
    rowSends ⟨setTable⟩ (Environment.fromArray (rawRow (setRowOf pc fp o k rc rbc)) data) =
      sendsOf pc fp next rbc (entry (.setConstant o k)) [(fp * o, rc, mem.limbsAt (fp * o))] := by
  obtain ⟨hk, rfl⟩ := (set_refines_iff _ _ _).mp (setRowOf_refines hexec rc rbc)
  rw [rowSends_mk, set_sends_gen _ _ _ _ (eval_rowVar _ data)]
  simp only [setRowOf] at hk ⊢
  have hk' := MemImage.limbsAt_eq_of_read hk
  simp only [limb_ofLimbs, Vector.getElem_mk] at hk'
  rw [hk']
  simp [sendsOf, memMsgOf, bcMsgOf, entry, Regs.next]

/-- The `DEREF` row of an execution sends the `DEREF` messages: the pointer cell carries
`(p, 0, 0)`, the target `p·o₂` the limbs of the mode's source, and the local cell its word. -/
theorem deref_exec_sends {κ : ℕ} {mem : MemImage κ} {pc fp o1 o2 o3 : K} {mode : DerefMode}
    {next : Regs K} (hexec : execute mem ⟨pc, fp⟩ (.deref o1 o2 o3 mode) = some next)
    (r1 r2 r3 rbc : K) (data : ProverData K) :
    rowSends ⟨derefTable⟩
        (Environment.fromArray (rawRow (derefRowOf mem pc fp o1 o2 o3 mode r1 r2 r3 rbc)) data) =
      sendsOf pc fp next rbc (entry (.deref o1 o2 o3 mode))
        [(fp * o1, r1, mem.limbsAt (fp * o1)),
          ((mem.limbsAt (fp * o1))[0] * o2, r2, mem.limbsAt ((mem.limbsAt (fp * o1))[0] * o2)),
          (fp * o3, r3, mem.limbsAt (fp * o3))] := by
  obtain ⟨mode', ⟨hflags, h1, h3⟩, h2, rfl⟩ :=
    (deref_refines_iff _ _ _).mp (derefRowOf_refines hexec r1 r2 r3 rbc)
  rw [rowSends_mk, deref_sends_gen _ _ _ _ (eval_rowVar _ data)]
  simp only [derefRowOf] at hflags h1 h3 h2 ⊢
  obtain ⟨h4, h5⟩ := Prod.ext_iff.mp hflags
  -- the pointer cell holds `(p, 0, 0)`
  have e1 := MemImage.limbsAt_eq_of_read h1
  simp only [limb0_ofLimbs, limb1_ofLimbs, limb2_ofLimbs] at e1
  have e1' : (mem.limbsAt (fp * o1))[1] = 0 := by rw [e1]; rfl
  have e1'' : (mem.limbsAt (fp * o1))[2] = 0 := by rw [e1]; rfl
  -- the target cell holds the limbs of the mode's source
  have e2 := MemImage.limbsAt_eq_of_read h2
  rw [← storeCoords_eval, h4, h5] at e2
  simp only [limb0_ofLimbs, limb1_ofLimbs, limb2_ofLimbs] at e2
  simp [sendsOf, memMsgOf, bcMsgOf, entry, Regs.next, e1', e1'', e2]

/-- The indicator slot of a `JUMP` raw row is its second witness. -/
theorem jumpRaw_get_indicator (r : JumpRow K) (w b : K) (data : ProverData K) :
    (Environment.fromArray (jumpRaw r w b) data).get (size JumpRow + 1) = b := by
  show ((rawRow r ++ #[w, b])[size JumpRow + 1]?).getD 0 = b
  rw [Array.getElem?_append_right (by rw [rawRow_size]; omega), rawRow_size]
  simp

/-- The sends of a `JUMP` raw row, in closed form: the pushed successor reads the indicator `b`. -/
theorem jumpRaw_sends (r : JumpRow K) (w b : K) (data : ProverData K) :
    rowSends ⟨jumpTable⟩ (Environment.fromArray (jumpRaw r w b) data) =
      [(StatePull.name, #[r.pc, r.fp]),
       (StatePush.name, #[b * r.vpc + b * (g * r.pc) + g * r.pc, b * r.vfp + b * r.fp + r.fp]),
       (BytecodePull.name, #[r.pc, r.rbc, Opcode.jump.code, r.oc, r.od, r.of, 0, 0, 0, 0]),
       (BytecodePush.name, #[r.pc, g * r.rbc, Opcode.jump.code, r.oc, r.od, r.of, 0, 0, 0, 0]),
       (MemPull.name, #[r.fp * r.oc, r.rc, r.vcond, 0, 0]),
       (MemPush.name, #[r.fp * r.oc, g * r.rc, r.vcond, 0, 0]),
       (MemPull.name, #[r.fp * r.od, r.rd, r.vpc, 0, 0]),
       (MemPush.name, #[r.fp * r.od, g * r.rd, r.vpc, 0, 0]),
       (MemPull.name, #[r.fp * r.of, r.rf, r.vfp, 0, 0]),
       (MemPush.name, #[r.fp * r.of, g * r.rf, r.vfp, 0, 0])] :=
  jump_sends_gen (varFromOffset JumpRow 0) (Environment.fromArray (jumpRaw r w b) data)
    (size JumpRow) r (eval_rowVar_append r #[w, b] data) b (jumpRaw_get_indicator r w b data)

/-- The `JUMP` row of an execution, with its honest local witnesses, sends the `JUMP` messages:
the condition, destination and frame cells carry `(v, 0, 0)` for the words in `K` they hold, and
the pushed successor is the destination and frame when the condition is nonzero and the
fall-through otherwise. -/
theorem jump_exec_sends {κ : ℕ} {mem : MemImage κ} {pc fp oc od of : K} {next : Regs K}
    (hexec : execute mem ⟨pc, fp⟩ (.jump oc od of) = some next) (rc rd rf rbc : K)
    (data : ProverData K) :
    rowSends ⟨jumpTable⟩
        (Environment.fromArray
          (jumpRaw (jumpRowOf mem pc fp oc od of rc rd rf rbc)
            (if (mem.limbsAt (fp * oc))[0] = 0 then 0 else ((mem.limbsAt (fp * oc))[0])⁻¹)
            (if (mem.limbsAt (fp * oc))[0] = 0 then 0 else 1)) data) =
      sendsOf pc fp next rbc (entry (.jump oc od of))
        [(fp * oc, rc, mem.limbsAt (fp * oc)), (fp * od, rd, mem.limbsAt (fp * od)),
          (fp * of, rf, mem.limbsAt (fp * of))] := by
  obtain ⟨⟨hc, hd, hf⟩, hnext⟩ := (jump_refines_iff _ _ _).mp (jumpRowOf_refines hexec rc rd rf rbc)
  rw [jumpRaw_sends]
  simp only [jumpRowOf] at hc hd hf hnext ⊢
  have ec := MemImage.limbsAt_eq_of_read hc
  have ed := MemImage.limbsAt_eq_of_read hd
  have ef := MemImage.limbsAt_eq_of_read hf
  simp only [limb0_ofLimbs, limb1_ofLimbs, limb2_ofLimbs] at ec ed ef
  have ec1 : (mem.limbsAt (fp * oc))[1] = 0 := by rw [ec]; rfl
  have ec2 : (mem.limbsAt (fp * oc))[2] = 0 := by rw [ec]; rfl
  have ed1 : (mem.limbsAt (fp * od))[1] = 0 := by rw [ed]; rfl
  have ed2 : (mem.limbsAt (fp * od))[2] = 0 := by rw [ed]; rfl
  have ef1 : (mem.limbsAt (fp * of))[1] = 0 := by rw [ef]; rfl
  have ef2 : (mem.limbsAt (fp * of))[2] = 0 := by rw [ef]; rfl
  subst hnext
  by_cases h0 : (mem.limbsAt (fp * oc))[0] = 0
  · simp [sendsOf, memMsgOf, bcMsgOf, entry, Regs.next, h0, ec1, ec2, ed1, ed2, ef1, ef2]
  · simp [sendsOf, memMsgOf, bcMsgOf, entry, h0, ec1, ec2, ed1, ed2, ef1, ef2, add_assoc,
      CharTwo.add_self_eq_zero]

/-- The message of a read of a canonical cell: the limbs the image holds at its address are the
cell's two limbs and `0`. -/
theorem memMsgOf_cell {κ : ℕ} {mem : MemImage κ} {a c : K} {cell : Vector K 2}
    (h : mem.read a = some (E.ofCell cell)) :
    memMsgOf a c (mem.limbsAt a) = #[a, c, cell[0], cell[1], 0] := by
  rw [MemImage.limbsAt_eq_of_read h]
  rfl

/-- The `BLAKE2S` row of an execution sends the `BLAKE2S` messages: each of the nine cells
carries its two limbs and a zero third limb, the canonical form the execution checks. -/
theorem blake2s_exec_sends {κ : ℕ} {mem : MemImage κ}
    {pc fp om0 om1 om2 om3 ocv oout omd : K} {next : Regs K}
    (hexec : execute mem ⟨pc, fp⟩ (.blake2s ![om0, om1, om2, om3] ocv oout omd) = some next)
    (rm0 rm1 rm2 rm3 rcv0 rcv1 rout0 rout1 rmd rbc : K) (data : ProverData K) :
    rowSends ⟨blake2sTable⟩
        (Environment.fromArray (rawRow (blake2sRowOf mem pc fp om0 om1 om2 om3 ocv oout omd
          rm0 rm1 rm2 rm3 rcv0 rcv1 rout0 rout1 rmd rbc)) data) =
      sendsOf pc fp next rbc (entry (.blake2s ![om0, om1, om2, om3] ocv oout omd))
        [(fp * om0, rm0, mem.limbsAt (fp * om0)), (fp * om1, rm1, mem.limbsAt (fp * om1)),
          (fp * om2, rm2, mem.limbsAt (fp * om2)), (fp * om3, rm3, mem.limbsAt (fp * om3)),
          (fp * ocv, rcv0, mem.limbsAt (fp * ocv)),
          (fp * (g * ocv), rcv1, mem.limbsAt (fp * (g * ocv))),
          (fp * oout, rout0, mem.limbsAt (fp * oout)),
          (fp * (g * oout), rout1, mem.limbsAt (fp * (g * oout))),
          (fp * omd, rmd, mem.limbsAt (fp * omd))] := by
  obtain ⟨⟨hm0, hm1, hm2, hm3, hcv0, hcv1, hout0, hout1, hmd⟩, -, rfl⟩ :=
    (blake2s_refines_iff _ _ _).mp
      (blake2sRowOf_refines hexec rm0 rm1 rm2 rm3 rcv0 rcv1 rout0 rout1 rmd rbc)
  rw [rowSends_mk, blake2s_sends_gen _ _ _ _ (eval_rowVar _ data)]
  simp only [blake2sRowOf] at hm0 hm1 hm2 hm3 hcv0 hcv1 hout0 hout1 hmd ⊢
  simp [sendsOf, bcMsgOf, entry, Regs.next, memMsgOf_cell hm0, memMsgOf_cell hm1,
    memMsgOf_cell hm2, memMsgOf_cell hm3, memMsgOf_cell hcv0, memMsgOf_cell hcv1,
    memMsgOf_cell hout0, memMsgOf_cell hout1, memMsgOf_cell hmd]

/-! ## Every cell an instruction reads is an address -/

/-- Every cell an executing instruction reads is an address of the image: the execution reads it
(`*_refines_iff`, the bindings and the result cell). -/
theorem readAddrs_valid {κ : ℕ} {mem : MemImage κ} {pc fp : K} {ins : Instr} {next : Regs K}
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
  | blake2s om ocv oout omd =>
    have hom : om = ![om 0, om 1, om 2, om 3] := by funext i; fin_cases i <;> rfl
    rw [hom] at hexec
    obtain ⟨⟨hm0, hm1, hm2, hm3, hcv0, hcv1, hout0, hout1, hmd⟩, -, -⟩ :=
      (blake2s_refines_iff _ _ _).mp (blake2sRowOf_refines hexec 1 1 1 1 1 1 1 1 1 1)
    simp only [readAddrs, List.mem_cons, List.not_mem_nil, or_false]
    rintro a (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨_, hm0⟩, ⟨_, hm1⟩, ⟨_, hm2⟩, ⟨_, hm3⟩, ⟨_, hcv0⟩, ⟨_, hcv1⟩, ⟨_, hout0⟩,
      ⟨_, hout1⟩, ⟨_, hmd⟩]

/-! ## The row of an instruction -/

/-- The table of each opcode, in the ensemble's order (`leanIsaEnsemble`). -/
def opComponent : Opcode → Component K
  | .xor => ⟨xorTable⟩
  | .mulNative => ⟨mulTable⟩
  | .setConstant => ⟨setTable⟩
  | .deref => ⟨derefTable⟩
  | .jump => ⟨jumpTable⟩
  | .blake2s => ⟨blake2sTable⟩

/-- The width of a raw row of each opcode's table: the row's columns, and for `JUMP` its two
local witnesses. -/
def opWidth : Opcode → ℕ
  | .xor => size XorRow
  | .mulNative => size MulRow
  | .setConstant => size SetRow
  | .deref => size DerefRow
  | .jump => size JumpRow + 2
  | .blake2s => size Blake2sRow

/-- The raw row of an instruction executed from `(pc, fp)` over the image `mem`: the typed row of
its table with the read counts `cnt` (positionally, in the order the circuit reads) and the
bytecode count `rbc`, and for `JUMP` the honest inverse and indicator of the condition. -/
noncomputable def rowOf {κ : ℕ} (mem : MemImage κ) (pc fp : K) (cnt : ℕ → K) (rbc : K) :
    Instr → Array K
  | .xor oA oB oC => rawRow (xorRowOf mem pc fp oA oB oC (cnt 0) (cnt 1) (cnt 2) rbc)
  | .mulNative oA oB oC => rawRow (mulRowOf mem pc fp oA oB oC (cnt 0) (cnt 1) (cnt 2) rbc)
  | .setConstant o k => rawRow (setRowOf pc fp o k (cnt 0) rbc)
  | .deref o1 o2 o3 mode =>
      rawRow (derefRowOf mem pc fp o1 o2 o3 mode (cnt 0) (cnt 1) (cnt 2) rbc)
  | .jump oc od of =>
      jumpRaw (jumpRowOf mem pc fp oc od of (cnt 0) (cnt 1) (cnt 2) rbc)
        (if (mem.limbsAt (fp * oc))[0] = 0 then 0 else ((mem.limbsAt (fp * oc))[0])⁻¹)
        (if (mem.limbsAt (fp * oc))[0] = 0 then 0 else 1)
  | .blake2s om ocv oout omd =>
      rawRow (blake2sRowOf mem pc fp (om 0) (om 1) (om 2) (om 3) ocv oout omd
        (cnt 0) (cnt 1) (cnt 2) (cnt 3) (cnt 4) (cnt 5) (cnt 6) (cnt 7) (cnt 8) rbc)

/-- The raw row of an instruction has the width of its table. -/
theorem rowOf_size {κ : ℕ} (mem : MemImage κ) (pc fp : K) (cnt : ℕ → K) (rbc : K) (ins : Instr) :
    (rowOf mem pc fp cnt rbc ins).size = opWidth ins.opcode := by
  cases ins <;> simp [rowOf, opWidth, Instr.opcode, rawRow_size, jumpRaw]

/-- **The row of an executing instruction sends `sendsOf`.** If the instruction executes from
`(pc, fp)` to `next`, its row, in its table, sends the state step from `(pc, fp)` to `next`, the
bytecode read of its entry at `pc`, and the reads of the cells it reads with the counts `cnt`. -/
theorem rowOf_sends {κ : ℕ} {mem : MemImage κ} {pc fp : K} {ins : Instr} {next : Regs K}
    (hexec : execute mem ⟨pc, fp⟩ ins = some next) (cnt : ℕ → K) (rbc : K)
    (data : ProverData K) :
    rowSends (opComponent ins.opcode)
        (Environment.fromArray (rowOf mem pc fp cnt rbc ins) data) =
      sendsOf pc fp next rbc (entry ins) (readsOf mem fp cnt ins) := by
  cases ins with
  | xor oA oB oC =>
    simp only [Instr.opcode, opComponent]
    rw [rowOf, xor_exec_sends hexec]
    simp [readsOf, readAddrs]
  | mulNative oA oB oC =>
    simp only [Instr.opcode, opComponent]
    rw [rowOf, mul_exec_sends hexec]
    simp [readsOf, readAddrs]
  | setConstant o k =>
    simp only [Instr.opcode, opComponent]
    rw [rowOf, set_exec_sends hexec]
    simp [readsOf, readAddrs]
  | deref o1 o2 o3 mode =>
    simp only [Instr.opcode, opComponent]
    rw [rowOf, deref_exec_sends hexec]
    simp [readsOf, readAddrs]
  | jump oc od of =>
    simp only [Instr.opcode, opComponent]
    rw [rowOf, jump_exec_sends hexec]
    simp [readsOf, readAddrs]
  | blake2s om ocv oout omd =>
    have hom : om = ![om 0, om 1, om 2, om 3] := by funext i; fin_cases i <;> rfl
    have h := blake2s_exec_sends (hom ▸ hexec) (cnt 0) (cnt 1) (cnt 2) (cnt 3) (cnt 4) (cnt 5)
      (cnt 6) (cnt 7) (cnt 8) rbc data
    rw [← hom] at h
    simp only [Instr.opcode, opComponent]
    rw [rowOf, h]
    simp [readsOf, readAddrs]

end LeanVM.Arithmetization
