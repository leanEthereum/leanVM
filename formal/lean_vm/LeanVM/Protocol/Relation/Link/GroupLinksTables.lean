/-
  LeanVM.Protocol.Relation.Link.GroupLinksTables

  The deployed tables' links, checked by evaluation.
-/

module

public import Statement.Verifier.Layout

/-!
# The deployed tables' links

Facts about `tables`' links that the link's cross terms rest on, each a `Bool` check over the six
tables evaluated by the kernel (`decide +kernel`), then read back as a `Prop`:
`lkt_opcode` (each table's opcodes are its index), `lkt_gated` (a gated access has no frame and no
reads), `lkt_word_read` (a word read's pointer is an ungated access's at shift `0`),
`lkt_pointers` (the pointer list's shape), `lkt_operands` and `lkt_read_slots` (the slots an
operand equation or a read names are operand slots), `lkt_cols` (every column a form names is a
non-pointer column of the table), `lkt_link_cols` (the two links share the `pc` column) and
`lkt_pcSlots` (every `Read.pc` is in `pcSlots tables`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- The columns a form's monomials name. -/
def lkFormCols (f : Form) : List ℕ := f.terms.flatMap (·.1)

/-- An operand slot of an instruction, `4 ≤ s < 2^BYTECODE_SLOT_BITS`. -/
def lktSlotOK (s : ℕ) : Bool := 4 ≤ s && s < 2 ^ bytecodeSlotBits

/-- A read of the instruction names an operand slot. -/
def lktReadSlotOK : Read → Bool
  | .word _ _ => true
  | .slot s _ => lktSlotOK s
  | .frame s _ => lktSlotOK s
  | .pc s _ => lktSlotOK s

/-- A framed address names an operand slot. -/
def lktFrameOK : Option (ℕ × ℕ) → Bool
  | some (s, _) => lktSlotOK s
  | none => true

/-- A word read's pointer is an ungated access's at shift `0`. -/
def lktWordOK (memory : List Access) : Read → Bool
  | .word p _ => memory.any fun b ↦ b.pointer == p && b.shift == 0 && b.gate.isNone
  | _ => true

/-- A non-pointer column of the table. -/
def lktNp (table : Table) (c : ℕ) : Bool := c < table.width && !table.links.pointers.contains c

/-- Every column a word read's scale names is a non-pointer column. -/
def lktWordColsOK (table : Table) : Read → Bool
  | .word _ sc => (lkFormCols sc).all (lktNp table)
  | _ => true

/-- `lkt_cols`' check of one table. -/
def lktColsOK (table : Table) : Bool :=
  let L := table.links
  let np := lktNp table
  np L.stateLink.pc && np L.stateLink.fp && np L.bytecodeLink.pc &&
    (lkFormCols L.stateLink.next.1 ++ lkFormCols L.stateLink.next.2).all np &&
    L.bytecodeLink.operands.all (fun op ↦ (lkFormCols op.2).all np) &&
    L.memory.all fun a ↦ (lkFormCols a.address ++ lkFormCols a.value).all np &&
      a.gate.toList.all np && a.reads.all (lktWordColsOK table)

local notation "𝕋" t:max => tables.getD t default

theorem lkt_opcode : ∀ t < nTables, (𝕋 t).opcode = t ∧ (𝕋 t).links.bytecodeLink.opcode = t := by
  decide +kernel

theorem lkt_gated : ∀ t < nTables, ∀ a ∈ (𝕋 t).links.memory, a.gate.isSome →
    a.frame = none ∧ a.reads = [] := by
  have h : ∀ t < nTables, ∀ a ∈ (𝕋 t).links.memory, a.gate.isSome →
      a.frame = none ∧ a.reads.isEmpty = true := by
    decide +kernel
  intro t ht a ha hg
  obtain ⟨h1, h2⟩ := h t ht a ha hg
  exact ⟨h1, List.isEmpty_iff.mp h2⟩

theorem lkt_word_read : ∀ t < nTables, ∀ a ∈ (𝕋 t).links.memory, ∀ p sc,
    Read.word p sc ∈ a.reads → ∃ b ∈ (𝕋 t).links.memory, b.pointer = p ∧ b.shift = 0 ∧
      b.gate = none := by
  have h : ∀ t < nTables, ∀ a ∈ (𝕋 t).links.memory, ∀ rd ∈ a.reads,
      lktWordOK (𝕋 t).links.memory rd = true := by
    decide +kernel
  intro t ht a ha p sc hrd
  have := h t ht a ha _ hrd
  simpa [lktWordOK, Option.isNone_iff_eq_none, and_assoc] using this

theorem lkt_pointers : ∀ t < nTables,
    (𝕋 t).links.pointers.take 2 = [(𝕋 t).links.stateLink.cycle, (𝕋 t).links.bytecodeLink.pointer] ∧
      (𝕋 t).links.pointers.Nodup ∧ ∀ a ∈ (𝕋 t).links.memory, a.pointer ∈ (𝕋 t).links.pointers.drop 2 := by
  decide +kernel

theorem lkt_operands : ∀ t < nTables,
    ((𝕋 t).links.bytecodeLink.operands.map (·.1.headD 0)).Nodup ∧
      ∀ op ∈ (𝕋 t).links.bytecodeLink.operands, op.1 ≠ [] ∧ op.1.Nodup ∧
        ∀ s ∈ op.1, 4 ≤ s ∧ s < 2 ^ bytecodeSlotBits := by
  decide +kernel

theorem lkt_read_slots : ∀ t < nTables, ∀ a ∈ (𝕋 t).links.memory,
    (∀ s e, a.frame = some (s, e) → 4 ≤ s ∧ s < 2 ^ bytecodeSlotBits) ∧
      ∀ rd ∈ a.reads, ∀ s sc, (rd = .slot s sc ∨ rd = .frame s sc ∨ rd = .pc s sc) →
        4 ≤ s ∧ s < 2 ^ bytecodeSlotBits := by
  have h : ∀ t < nTables, ∀ a ∈ (𝕋 t).links.memory,
      lktFrameOK a.frame = true ∧ ∀ rd ∈ a.reads, lktReadSlotOK rd = true := by
    decide +kernel
  intro t ht a ha
  obtain ⟨hf, hr⟩ := h t ht a ha
  refine ⟨fun s e he ↦ ?_, fun rd hrd s sc hs ↦ ?_⟩
  · rw [he] at hf
    simpa [lktFrameOK, lktSlotOK] using hf
  · have := hr rd hrd
    rcases hs with rfl | rfl | rfl <;> simpa [lktReadSlotOK, lktSlotOK] using this

theorem lkt_cols : ∀ t < nTables,
    let L := (𝕋 t).links
    let np := fun c ↦ c < (𝕋 t).width ∧ c ∉ L.pointers
    np L.stateLink.pc ∧ np L.stateLink.fp ∧ np L.bytecodeLink.pc ∧
      (∀ c ∈ lkFormCols L.stateLink.next.1 ++ lkFormCols L.stateLink.next.2, np c) ∧
      (∀ op ∈ L.bytecodeLink.operands, ∀ c ∈ lkFormCols op.2, np c) ∧
      ∀ a ∈ L.memory, (∀ c ∈ lkFormCols a.address ++ lkFormCols a.value, np c) ∧
        (∀ c, a.gate = some c → np c) ∧
        ∀ p sc, Read.word p sc ∈ a.reads → ∀ c ∈ lkFormCols sc, np c := by
  have h : ∀ t < nTables, lktColsOK (𝕋 t) = true := by
    decide +kernel
  intro t ht
  have h := h t ht
  have hnp : ∀ c, lktNp (𝕋 t) c = true ↔ c < (𝕋 t).width ∧ c ∉ (𝕋 t).links.pointers := by
    intro c
    simp [lktNp]
  simp only [lktColsOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨(hnp _).mp h1, (hnp _).mp h2, (hnp _).mp h3, fun c hc ↦ (hnp c).mp (h4 c hc),
    fun op hop c hc ↦ (hnp c).mp (h5 op hop c hc), fun a ha ↦ ?_⟩
  obtain ⟨⟨ha1, ha2⟩, ha3⟩ := h6 a ha
  refine ⟨fun c hc ↦ (hnp c).mp (ha1 c hc), fun c hc ↦ (hnp c).mp (ha2 c (by simp [hc])),
    fun p sc hrd c hc ↦ (hnp c).mp ?_⟩
  have := ha3 _ hrd
  simp only [lktWordColsOK, List.all_eq_true] at this
  exact this c hc

theorem lkt_link_cols : ∀ t < nTables, (𝕋 t).links.stateLink.pc = (𝕋 t).links.bytecodeLink.pc := by
  decide +kernel

theorem lkt_pcSlots : ∀ t < nTables, ∀ a ∈ (𝕋 t).links.memory, ∀ s sc, Read.pc s sc ∈ a.reads →
    (pcSlots tables).contains (t, s) = true := by
  intro t ht a ha s sc hrd
  have hlen : tables.length = nTables := by decide +kernel
  have hmem : (𝕋 t) ∈ tables := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ ht), Option.getD_some]
    exact List.getElem_mem _
  have hin : (t, s) ∈ pcSlots tables := by
    simp only [pcSlots, List.mem_flatMap, List.mem_filterMap]
    refine ⟨_, hmem, a, ha, _, hrd, ?_⟩
    show some ((𝕋 t).opcode, s) = some (t, s)
    rw [(lkt_opcode t ht).1]
  exact List.elem_iff.mpr hin

end

end LeanVM.Protocol.Relation
