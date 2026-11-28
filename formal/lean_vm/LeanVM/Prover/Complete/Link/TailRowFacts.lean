/-
  LeanVM.Prover.Complete.Link.TailRowFacts

  What the link's row side reads of the tables, decided: the verifier receives no pointer column,
  and nothing it evaluates reads one.
-/

module

public import LeanVM.Prover.Complete.Link.TailRowAlg

/-!
# The tables' facts the row side needs

`tableOK_all` (by `decide`): in every table, the state link's `pc`, `fp` and successor forms, the
program link's `pc` and operand forms, and every access's address, value, gate and word-read
scales read non-pointer columns only (`nonPtr`); the successor forms and the word-read scales have
degree at most one; no access uses the cycle or the program pointer; and only `JUMP` (table `4`)
has constraints. `pointerStarts_eq`: each table's first pointer column is the count before it.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover

/-- Table `t`'s non-pointer columns, in order: what the link's message carries. -/
def nonPtr (t : ℕ) : List ℕ :=
  (List.range (tables.getD t default).width).filter fun c ↦
    !(tables.getD t default).links.pointers.contains c

/-- Every monomial of `f` reads columns of `S` only. -/
def formIn (S : List ℕ) (f : Form) : Bool := f.terms.all fun m ↦ m.1.all S.contains

/-- Every monomial of `f` reads columns of `S` only, and has degree at most one. -/
def formAff (S : List ℕ) (f : Form) : Bool :=
  f.terms.all fun m ↦ decide (m.1.length ≤ 1) && m.1.all S.contains

/-- A word read's scale reads `S` only, at degree at most one. -/
def readOK (S : List ℕ) : Read → Bool
  | .word _ scale => formAff S scale
  | _ => true

/-- An access reads `S` only and uses neither the cycle nor the program pointer. -/
def accessOK (S ptrs : List ℕ) (a : Access) : Bool :=
  formIn S a.address && formIn S a.value && a.gate.all S.contains && a.reads.all (readOK S) &&
    !(ptrs.take 2).contains a.pointer

/-- What the row side reads of table `t`. -/
def tableOK (t : ℕ) : Bool :=
  let tb := tables.getD t default
  let L := tb.links
  let S := nonPtr t
  S.contains L.stateLink.pc && S.contains L.stateLink.fp && formAff S L.stateLink.next.1 &&
    formAff S L.stateLink.next.2 && S.contains L.bytecodeLink.pc &&
    L.bytecodeLink.operands.all (fun o ↦ formIn S o.2) && L.memory.all (accessOK S L.pointers) &&
    (!decide (0 < tb.nConstraints) || t == 4)

theorem tableOK_all : ∀ t < nTables, tableOK t = true := by decide +kernel

/-- `JUMP`'s columns its identities read. -/
def jumpCols : List ℕ :=
  let c := colIndex jumpColumns
  [c "pc", c "fp", c "v_cond", c "v_pc", c "v_fp", c "pc_next", c "fp_next", c "w", c "b"]

theorem jumpCols_nonPtr : ∀ c ∈ jumpCols, c ∈ nonPtr 4 := by decide +kernel

theorem jump_constraints : (tables.getD 4 default).constraints = jumpConstraints := rfl

theorem pointerStarts_eq : ∀ t < nTables, pointerStarts.getD t 0 =
    ((List.range t).map fun t' ↦ (tables.getD t' default).links.pointers.length).sum := by
  decide +kernel

theorem sum_pointers : ((List.range nTables).map fun t ↦ (tables.getD t default).links.pointers.length).sum = 33 := by
  decide +kernel

/-! ## The facts, unpacked -/

theorem formIn_spec {S : List ℕ} {f : Form} (h : formIn S f = true) :
    ∀ m ∈ f.terms, ∀ v ∈ m.1, v ∈ S := by
  intro m hm v hv
  simp only [formIn, List.all_eq_true, List.contains_iff_mem] at h
  exact h m hm v hv

theorem formAff_spec {S : List ℕ} {f : Form} (h : formAff S f = true) :
    (∀ m ∈ f.terms, m.1.length ≤ 1) ∧ ∀ m ∈ f.terms, ∀ v ∈ m.1, v ∈ S := by
  simp only [formAff, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.contains_iff_mem] at h
  exact ⟨fun m hm ↦ (h m hm).1, fun m hm v hv ↦ (h m hm).2 v hv⟩

/-- The facts of one table, as propositions. -/
structure TableFacts (t : ℕ) : Prop where
  pc : (tables.getD t default).links.stateLink.pc ∈ nonPtr t
  fp : (tables.getD t default).links.stateLink.fp ∈ nonPtr t
  next1 : formAff (nonPtr t) (tables.getD t default).links.stateLink.next.1 = true
  next2 : formAff (nonPtr t) (tables.getD t default).links.stateLink.next.2 = true
  bcPc : (tables.getD t default).links.bytecodeLink.pc ∈ nonPtr t
  operands : ∀ o ∈ (tables.getD t default).links.bytecodeLink.operands, formIn (nonPtr t) o.2 = true
  address : ∀ a ∈ (tables.getD t default).links.memory, formIn (nonPtr t) a.address = true
  value : ∀ a ∈ (tables.getD t default).links.memory, formIn (nonPtr t) a.value = true
  gate : ∀ a ∈ (tables.getD t default).links.memory, ∀ g, a.gate = some g → g ∈ nonPtr t
  reads : ∀ a ∈ (tables.getD t default).links.memory, ∀ rd ∈ a.reads, readOK (nonPtr t) rd = true
  pointer : ∀ a ∈ (tables.getD t default).links.memory,
    a.pointer ∉ (tables.getD t default).links.pointers.take 2
  jump : 0 < (tables.getD t default).nConstraints → t = 4

theorem tableFacts {t : ℕ} (ht : t < nTables) : TableFacts t := by
  have h := tableOK_all t ht
  simp only [tableOK, Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hpc, hfp⟩, hn1⟩, hn2⟩, hbc⟩, hop⟩, hmem⟩, hj⟩ := h
  have hacc : ∀ a ∈ (tables.getD t default).links.memory, accessOK (nonPtr t)
      (tables.getD t default).links.pointers a = true := hmem
  refine ⟨hpc, hfp, hn1, hn2, hbc, hop, fun a ha ↦ ?_, fun a ha ↦ ?_, fun a ha g hg ↦ ?_,
    fun a ha rd hrd ↦ ?_, fun a ha ↦ ?_, fun h0 ↦ ?_⟩
  all_goals first
    | (rcases hj with hj | hj
       · exact absurd h0 hj
       · exact hj)
    | (have h1 := hacc a ha
       simp only [accessOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h1
       first
         | exact h1.1.1.1.1
         | exact h1.1.1.1.2
         | exact h1.1.2 rd hrd
         | (simpa using h1.2)
         | (have h2 := h1.1.1.2
            rw [hg] at h2
            simpa using h2))

end LeanVM.Prover.Complete

end
