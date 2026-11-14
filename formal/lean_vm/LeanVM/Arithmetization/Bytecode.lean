/-
  LeanVM.Arithmetization.Bytecode

  The sixteen-slot bytecode encoding of an instruction, its thirteen-coordinate bus entry, and the
  decoder for canonical thirteen-coordinate entries.
-/

module

public import LeanVM.Semantics.Lemmas

/-!
# The bytecode encoding

Transcribed from:

* specification §8.1 (`doc/leanvm/body/08-end-to-end-protocol.tex`): instruction `z` is sixteen
  `K` slots, the opcode in slot 3, the operands, immediate lanes and flags after it, zero
  elsewhere;
* `crates/leanvm_core/src/cpu/layout.rs` (`bytecode_columns`): the thirteen public program
  columns, the opcode then twelve operand slots (`BYTECODE_OPERANDS = 12`), offsets as
  g-powers, a `SET` immediate as its two limbs, the `DEREF` store-mode flags and `KECCAK`'s
  layout and output flags as `0` or `1`, unused slots zero; `stack_columns` stacks them at slots
  `3..16` (`BYTECODE_PUBLIC_SLOT = 3`);
* `crates/leanvm_core/src/cpu/isa.rs`: the `DEREF` store mode as the flag pair
  `(f_pc, f_fp)`, `cell = (0, 0)`, `pc = (1, 0)`, `fp = (0, 1)`;
* `crates/leanvm_core/src/cpu/isa.rs`: `KECCAK`'s output cells as the flag pair
  `(out_two, out_all)`, `one = (0, 0)`, `two = (1, 0)`, `all = (1, 1)`.

`entry i` is the bus entry of an instruction, the row of `bytecode_columns`; `instructionSlots i` is
its sixteen-slot row, the entry at slots 3 to 15. Both are defined in `Statement.LeanIsa`, since
the verifier receives a program through them; `decode`, here, consumes a thirteen-coordinate
entry. It is exact: `decode v = some i ↔ v = entry i` (`decode_eq_some_iff`); on a `DEREF`
tuple with free flags it names the mode whose flags they are (`decode_deref_eq_some_iff`).
Unknown opcodes, invalid `DEREF` flag pairs, `KECCAK` layout flags other than `0` and `1`,
`KECCAK` output flag pairs that are none of the three (`(0, 1)` among them), and nonzero spare
entry coordinates decode to `none`. These results establish the canonical entry
boundary.

`Program` already contains typed `LeanIsaInstruction` values, and `LeanIsaProgram.fetch` looks them
up by address; it does not invoke this decoder. `instructionSlots` constructs sixteen-slot vectors,
but this module does not decode arbitrary sixteen-slot vectors or prove a raw-bytecode-to-`Program`
loading/correspondence theorem. Those interfaces require separate coverage or rejection proofs.

## Wrong readings excluded

* `SET_CONSTANT`'s two limbs ride slots 5 and 6, coordinates 2 and 3 of the entry; coordinate 4,
  the slot `DEREF` uses for `f_pc`, is a spare zero; `KECCAK`'s twelve operands ride slots 4 to 15
  (`decode_entry` on every constructor).
* The flag pair `(1, 1)` decodes to nothing, and so does every pair that is not one of the
  three. Likewise `KECCAK`'s output flag pair `(0, 1)`, which would write cells `2..13` and not
  cell `1`, and is no `OutCells`'s.
* An output flag of `KECCAK` is `0` or `1`: that is what makes its gated memory pair either a
  read or a cancelled pair (`Tables.Keccak`), and `decode` is where it comes from.
* A nonzero spare entry coordinate is not ignored. Each opcode table's bytecode tuple carries
  literal zeros in its spare coordinates (`flushes_*`, `crates/verifier/src/layout.rs`),
  and `decode` rejects a tuple that violates that opcode's canonical entry shape. This is a
  thirteen-coordinate entry claim, not rejection by the typed program's address lookup.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-! ## The store-mode flags -/

/-- The store mode of a flag pair, if it is one of the three. -/
def derefMode? (fpc ffp : K) : Option DerefMode :=
  if fpc = 0 ∧ ffp = 0 then some .cell
  else if fpc = 1 ∧ ffp = 0 then some .pc
  else if fpc = 0 ∧ ffp = 1 then some .fp
  else none

/-! ## The bus entry and the sixteen slots -/

/-! ## The decoder -/

/-- A `KECCAK` layout flag, if the word is `0` or `1`. -/
def flag? (a : K) : Option Bool :=
  if a = 0 then some false else if a = 1 then some true else none

/-- The opcode of a code, if it is one of the six. -/
def opcode? (a : K) : Option Opcode :=
  if a = Opcode.xor.busCode then some .xor
  else if a = Opcode.mulNative.busCode then some .mulNative
  else if a = Opcode.setConstant.busCode then some .setConstant
  else if a = Opcode.deref.busCode then some .deref
  else if a = Opcode.jump.busCode then some .jump
  else if a = Opcode.keccak.busCode then some .keccak
  else none

/-- `KECCAK`'s output cells of a flag pair `(out_two, out_all)`, if it is one of the three. -/
def outCells? (two all : K) : Option KeccakOutputCells :=
  if two = 0 ∧ all = 0 then some .one
  else if two = 1 ∧ all = 0 then some .two
  else if two = 1 ∧ all = 1 then some .all
  else none

/-- The spare coordinates `5..12` of an entry are zero. -/
def Spare5 (v : Vector K 13) : Prop :=
  v[5] = 0 ∧ v[6] = 0 ∧ v[7] = 0 ∧ v[8] = 0 ∧ v[9] = 0 ∧ v[10] = 0 ∧ v[11] = 0 ∧ v[12] = 0

instance (v : Vector K 13) : Decidable (Spare5 v) := by unfold Spare5; infer_instance

/-- Read an entry back as an instruction: the exact inverse of `entry` (`decode_eq_some_iff`);
`none` on an unknown opcode, on a flag pair that is no mode, on a layout flag that is neither `0`
nor `1`, on an output flag pair that is none of the three, or on a nonzero spare slot. -/
def decode (v : Vector K 13) : Option LeanIsaInstruction :=
  match opcode? v[0] with
  | some .xor => if v[4] = 0 ∧ Spare5 v then some (.xor v[1] v[2] v[3]) else none
  | some .mulNative => if v[4] = 0 ∧ Spare5 v then some (.mulNative v[1] v[2] v[3]) else none
  | some .setConstant =>
      if v[4] = 0 ∧ Spare5 v then some (.setConstant v[1] (E.ofLimbs v[2] v[3])) else none
  | some .deref =>
      match derefMode? v[4] v[5] with
      | some mode =>
        if v[6] = 0 ∧ v[7] = 0 ∧ v[8] = 0 ∧ v[9] = 0 ∧ v[10] = 0 ∧ v[11] = 0 ∧ v[12] = 0 then
          some (.deref v[1] v[2] v[3] mode)
        else none
      | none => none
  | some .jump => if v[4] = 0 ∧ Spare5 v then some (.jump v[1] v[2] v[3]) else none
  | some .keccak =>
      match flag? v[9], flag? v[10], outCells? v[11] v[12] with
      | some inOdd, some outOdd, some outCells =>
          some (.keccak ![v[1], v[2], v[3], v[4]] v[5] v[6] v[7] v[8] inOdd outOdd outCells)
      | _, _, _ => none
  | none => none

/-! ## Proof helpers -/

/-- A four-vector is its four entries. -/
private theorem vecCons_apply (om : Fin 4 → K) : ![om 0, om 1, om 2, om 3] = om := by
  funext i
  fin_cases i <;> rfl

/-! ## Load-bearing lemmas -/

/-- The flags of a mode decode to that mode. -/
theorem derefMode?_flags (m : DerefMode) :
    derefMode? (derefFlags m).1 (derefFlags m).2 = some m := by
  cases m <;> simp [derefMode?, derefFlags]

/-- A flag pair decodes to a mode exactly when it is that mode's flags. -/
theorem derefMode?_eq_some_iff {fpc ffp : K} {m : DerefMode} :
    derefMode? fpc ffp = some m ↔ (fpc, ffp) = derefFlags m := by
  constructor
  · intro h
    unfold derefMode? at h
    split_ifs at h with h1 h2 h3 <;> cases h
    · exact Prod.ext h1.1 h1.2
    · exact Prod.ext h2.1 h2.2
    · exact Prod.ext h3.1 h3.2
  · intro h
    cases m <;> simp only [derefFlags, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
      simp [derefMode?]

/-- The code of an opcode decodes to that opcode. -/
theorem opcode?_code (o : Opcode) : opcode? o.busCode = some o := by
  cases o <;> simp [opcode?, Opcode.code_injective.eq_iff]

/-- A word decodes to an opcode exactly when it is that opcode's code. -/
theorem opcode?_eq_some_iff {a : K} {o : Opcode} : opcode? a = some o ↔ a = o.busCode := by
  constructor
  · intro h
    unfold opcode? at h
    split_ifs at h <;> cases h <;> assumption
  · rintro rfl
    exact opcode?_code o

/-- Slot 3 is the opcode. -/
theorem entry_getElem_zero (i : LeanIsaInstruction) : (busEntry i)[0] = i.opcode.busCode := by
  cases i <;> rfl

/-- A flag decodes to itself. -/
theorem flag?_flagK (b : Bool) : flag? (layoutFlagWord b) = some b := by
  cases b <;> simp [flag?, layoutFlagWord]

/-- A word decodes to a flag exactly when it is that flag's word. -/
theorem flag?_eq_some_iff {a : K} {b : Bool} : flag? a = some b ↔ a = layoutFlagWord b := by
  constructor
  · intro h
    unfold flag? at h
    split_ifs at h with h0 h1 <;> cases h
    · exact h0
    · exact h1
  · rintro rfl
    exact flag?_flagK b

/-- The output flags of an output-cell choice decode to it. -/
theorem outCells?_flags (o : KeccakOutputCells) :
    outCells? (keccakOutputFlags o).1 (keccakOutputFlags o).2 = some o := by
  cases o <;> simp [outCells?, keccakOutputFlags, layoutFlagWord]

/-- An output flag pair decodes to a choice exactly when it is that choice's flags. -/
theorem outCells?_eq_some_iff {two all : K} {o : KeccakOutputCells} :
    outCells? two all = some o ↔ (two, all) = keccakOutputFlags o := by
  constructor
  · intro h
    unfold outCells? at h
    split_ifs at h with h1 h2 h3 <;> cases h
    · simp [keccakOutputFlags, layoutFlagWord, h1.1, h1.2]
    · simp [keccakOutputFlags, layoutFlagWord, h2.1, h2.2]
    · simp [keccakOutputFlags, layoutFlagWord, h3.1, h3.2]
  · intro h
    rw [← outCells?_flags o, ← h]

/-- Each output flag of a choice is `0` or `1`. -/
theorem keccakOutputFlags_bits (o : KeccakOutputCells) :
    ((keccakOutputFlags o).1 = 0 ∨ (keccakOutputFlags o).1 = 1) ∧
      ((keccakOutputFlags o).2 = 0 ∨ (keccakOutputFlags o).2 = 1) := by
  cases o <;> simp [keccakOutputFlags, layoutFlagWord]

/-- Every instruction's entry decodes to it. -/
theorem decode_entry (i : LeanIsaInstruction) : decode (busEntry i) = some i := by
  cases i with
  | keccak om otail ob8 ocap oout inOdd outOdd outCells =>
    have h := vecCons_apply om
    simp [decode, busEntry, opcode?_code, h, flag?_flagK, outCells?_flags]
  | _ => simp [decode, busEntry, opcode?_code, derefMode?_flags, ofLimbs_limb, Spare5]

/-- `decode` is the exact inverse of `entry`: a vector decodes to an instruction only when it is
that instruction's entry. -/
theorem decode_eq_some_iff {v : Vector K 13} {i : LeanIsaInstruction} : decode v = some i ↔ v =
    busEntry i := by
  constructor
  · intro h
    unfold decode at h
    rcases hop : opcode? v[0] with _ | op
    · rw [hop] at h
      cases h
    · rw [hop] at h
      rw [opcode?_eq_some_iff] at hop
      cases op <;> dsimp only at h
      case deref =>
        rcases hm : derefMode? v[4] v[5] with _ | mode
        · rw [hm] at h
          cases h
        · rw [hm] at h
          dsimp only at h
          rw [derefMode?_eq_some_iff, Prod.mk.injEq] at hm
          split_ifs at h with hz
          cases h
          obtain ⟨z6, z7, z8, z9, z10, z11, z12⟩ := hz
          refine Vector.ext fun j hj ↦ ?_
          interval_cases j <;> simp [busEntry, hop, hm.1, hm.2, z6, z7, z8, z9, z10, z11, z12]
      case keccak =>
        rcases h9 : flag? v[9] with _ | inOdd <;> rcases h10 : flag? v[10] with _ | outOdd <;>
          rcases h11 : outCells? v[11] v[12] with _ | outCells <;>
          rw [h9, h10, h11] at h <;> try cases h
        rw [flag?_eq_some_iff] at h9 h10
        rw [outCells?_eq_some_iff, Prod.mk.injEq] at h11
        refine Vector.ext fun j hj ↦ ?_
        interval_cases j <;> simp [busEntry, hop, h9, h10, h11.1, h11.2]
      all_goals
        split_ifs at h with hz
        cases h
        simp only [Spare5] at hz
        refine Vector.ext fun j hj ↦ ?_
        interval_cases j <;> simp [busEntry, hop, hz]
  · rintro rfl
    exact decode_entry i

/-- A vector decodes to nothing exactly when it is no instruction's entry. -/
theorem decode_eq_none_iff {v : Vector K 13} : decode v = none ↔ ∀ i, v ≠ busEntry i := by
  simp only [Option.eq_none_iff_forall_ne_some, ne_eq, decode_eq_some_iff]

/-- A `DEREF` tuple with free flags decodes exactly to the `DEREF` with its operands and the store
mode whose flags it carries; a pair that is no mode's decodes to nothing. -/
theorem decode_deref_eq_some_iff {o1 o2 o3 fpc ffp : K} {i : LeanIsaInstruction} :
    decode #v[Opcode.deref.busCode, o1, o2, o3, fpc, ffp, 0, 0, 0, 0, 0, 0, 0] = some i ↔
      ∃ mode, i = .deref o1 o2 o3 mode ∧ (fpc, ffp) = derefFlags mode := by
  simp only [decode, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, opcode?_code, and_self, ite_true]
  constructor
  · intro h
    rcases hm : derefMode? fpc ffp with _ | mode
    · rw [hm] at h
      cases h
    · rw [hm, Option.some.injEq] at h
      exact ⟨mode, h.symm, derefMode?_eq_some_iff.mp hm⟩
  · rintro ⟨mode, rfl, hf⟩
    rw [derefMode?_eq_some_iff.mpr hf]

/-- Distinct instructions have distinct entries. -/
theorem entry_injective : Function.Injective busEntry := by
  intro i j h
  have hi := decode_entry i
  rw [h, decode_entry] at hi
  exact (Option.some.inj hi).symm

/-- The sixteen slots: the entry at slots 3 to 15, zero elsewhere (specification §8.1). -/
theorem encodeSlots_getElem (i : LeanIsaInstruction) (j : ℕ) (hj : j < 16) :
    (instructionSlots i)[j] = if h : 3 ≤ j ∧ j < 16 then (busEntry i)[j - 3] else 0 := by
  interval_cases j <;> simp [instructionSlots]

end
end LeanVM.Arithmetization
