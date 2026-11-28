/-
  LeanVM.Guest.B1.Link.Arith.Lits

  The tables' coefficients as words: a table's forms and read scales with their coefficients
  replaced by given words, which is the table itself when the words are its coefficients'.
-/

module

public import LeanVM.Guest.B1.Link.Arith.Norm

/-!
# The tables' coefficients, as words

A form's coefficients are elements of `E` built from `gpow`, `Y`, `0`, `1`, sums and products
(`Form.col`, `Form.prod`, `addScaled`, `layoutLimb`), which the kernel evaluates slowly. The
normal forms of the row side therefore read the tables with each coefficient replaced by the word
of its limbs (`litLinks`, at given limbs `LinksLits`): `litLinks_self`, at a table's own limbs
(`linksLits`) the replacement changes nothing (`cw (cOf c) = c`). The limbs are checked once,
table by table, against the tables (`Arith/TablesL.lean`).
-/

namespace LeanVM.Guest.B1.Link.Arith

open LeanVM.Parameters LeanVM.Guest LeanVM.Protocol.Verifier

@[expose] public section

/-- A form, its coefficients replaced in order by the words of `l`. -/
def litForm (f : Form) (l : List Cf) : Form := ⟨(f.terms.zip l).map fun (t, c) ↦ (t.1, cw c)⟩

/-- A form's coefficients' limbs. -/
def formLits (f : Form) : List Cf := f.terms.map fun t ↦ cOf t.2

theorem zip_map_self {α β γ : Type} (xs : List α) (g : α → β) (h : α × β → γ) :
    (xs.zip (xs.map g)).map h = xs.map fun x ↦ h (x, g x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem litForm_self (f : Form) : litForm f (formLits f) = f := by
  obtain ⟨terms⟩ := f
  simp only [litForm, formLits, zip_map_self, cw_cOf]
  simp

/-- A read's coefficients' limbs: a word read's scale form's, or the scale's. -/
def readLits : Read → List Cf
  | .word _ s => formLits s
  | .slot _ c => [cOf c]
  | .frame _ c => [cOf c]
  | .pc _ c => [cOf c]

/-- A read, its coefficients replaced by the words of `l`. -/
def litRead : Read → List Cf → Read
  | .word p s, l => .word p (litForm s l)
  | .slot s _, l => .slot s (cw (l.headD (0, 0)))
  | .frame s _, l => .frame s (cw (l.headD (0, 0)))
  | .pc s _, l => .pc s (cw (l.headD (0, 0)))

theorem litRead_self (r : Read) : litRead r (readLits r) = r := by
  cases r <;> simp [litRead, readLits, litForm_self, cw_cOf]

/-- An access's coefficients' limbs: its address's, its value's, its reads'. -/
structure AccessLits where
  address : List Cf
  value : List Cf
  reads : List (List Cf)
  deriving DecidableEq, Inhabited

def accessLits (a : Access) : AccessLits := ⟨formLits a.address, formLits a.value, a.reads.map readLits⟩

/-- An access, its coefficients replaced. -/
def litAccess (a : Access) (l : AccessLits) : Access :=
  { a with
    address := litForm a.address l.address
    value := litForm a.value l.value
    reads := (a.reads.zip l.reads).map fun (r, x) ↦ litRead r x }

theorem litAccess_self (a : Access) : litAccess a (accessLits a) = a := by
  simp only [litAccess, accessLits, litForm_self, zip_map_self, litRead_self, List.map_id']

/-- A table's links' coefficients' limbs: the successor state's forms', the operand equations'
forms', each access's. -/
structure LinksLits where
  next : List Cf × List Cf
  operands : List (List Cf)
  memory : List AccessLits
  deriving DecidableEq, Inhabited

def linksLits (L : Links) : LinksLits :=
  ⟨((L.state.map fun s ↦ formLits s.next.1).getD [], (L.state.map fun s ↦ formLits s.next.2).getD []),
    (L.bytecode.map fun b ↦ b.operands.map fun o ↦ formLits o.2).getD [], L.memory.map accessLits⟩

/-- Links, their coefficients replaced. -/
def litLinks (L : Links) (l : LinksLits) : Links :=
  { L with
    state := L.state.map fun s ↦ { s with next := (litForm s.next.1 l.next.1, litForm s.next.2 l.next.2) }
    bytecode := L.bytecode.map fun b ↦
      { b with operands := (b.operands.zip l.operands).map fun (o, x) ↦ (o.1, litForm o.2 x) }
    memory := (L.memory.zip l.memory).map fun (a, x) ↦ litAccess a x }

theorem litLinks_self (L : Links) : litLinks L (linksLits L) = L := by
  obtain ⟨state, bytecode, memory⟩ := L
  simp only [litLinks, linksLits]
  congr 1
  · cases state with
    | none => rfl
    | some s => simp [litForm_self]
  · cases bytecode with
    | none => rfl
    | some b =>
      obtain ⟨p, pc, op, operands⟩ := b
      simp only [Option.map_some, Option.getD_some, zip_map_self, litForm_self]
      simp
  · simp only [zip_map_self, litAccess_self, List.map_id']

/-- A table, its links' coefficients replaced. -/
def litTable (tb : Table) (l : LinksLits) : Table := { tb with links := litLinks tb.links l }

theorem litTable_self (tb : Table) : litTable tb (linksLits tb.links) = tb := by
  simp only [litTable, litLinks_self]

end

end LeanVM.Guest.B1.Link.Arith
