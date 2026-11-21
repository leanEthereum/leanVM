module

public import NativeVm.Model.Field
public import Statement.LeanVmVerifier

/-!
# The bus blocks' forms as literal data: the format

A side's table blocks (`busBlocks`: every table's pushes, pulls or count columns, in table order)
are fixed data apart from their heights and rows. A block is `DBlk`: its owner and its entries, one
per term of each of its tuple's coordinates in order (`DEnt`: the coordinate's slot, the term's
monomial and its coefficient, an element of `K` given by its lane). `entsS` reads a statement tuple
the same way, and `FormsDataPush` (`FormsDataPull`, `FormsDataCount`) checks the literal data
against the statement's `tables` by `decide +kernel` (`pushD_eq`, ...).
-/

@[expose] public section

namespace NativeVm.Code.P3

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol.Verifier

/-- An entry of a block: the coordinate's slot, the monomial, the coefficient's limb-`0` lane. -/
abbrev DEnt := Nat × List Nat × Nat

/-- A block: its owner and its entries. -/
abbrev DBlk := Nat × List DEnt

/-- A statement tuple's entries: each coordinate's terms with its slot, coefficients as lanes. -/
def entsS (c : List Form) : List (Nat × List Nat × EW) :=
  c.zipIdx.flatMap fun (f, k) ↦ f.terms.map fun (m, e) ↦ (k, m, EW.ofE e)

/-- A block of the data as the statement's: the coefficient in limb `0`. -/
def dprojW (b : DBlk) : Nat × List (Nat × List Nat × EW) :=
  (b.1, b.2.map fun e ↦ (e.1, e.2.1, ⟨e.2.2.toUInt64, 0⟩))

/-- The statement's push blocks: owner and entries. -/
def pushS : List (Nat × List (Nat × List Nat × EW)) :=
  tables.flatMap fun t ↦ t.flushes.push.map fun c ↦ (t.opcode, entsS c)

/-- The statement's pull blocks. -/
def pullS : List (Nat × List (Nat × List Nat × EW)) :=
  tables.flatMap fun t ↦ t.flushes.pull.map fun c ↦ (t.opcode, entsS c)

/-- The statement's count blocks. -/
def countS : List (Nat × List (Nat × List Nat × EW)) :=
  tables.flatMap fun t ↦ t.countColumns.map fun l ↦ (t.opcode, entsS [Form.col l])

end NativeVm.Code.P3
