/-
  LeanVM.Protocol.Spine.Seams

  The claims that travel between the phases, and the seam relations: the output relation of
  each phase, which is the input relation of the next by definition.
-/

module

public import LeanVM.Protocol.Spine.KeccakZero

/-!
# Claims and seams

The oracle protocol's front is four phases, `commit ⟫ bus ⟫ table ⟫ pub`, then the Keccak
reduction, ring switching and the opening, each a
reduction from a statement to a statement over the one committed stack `q`. The statement
types between phases and the relations on them are fixed here, so a phase is built and proved
knowing only its two seams.

Two kinds of claim, each a statement about an extension read off `q` at a point of `E`:

* a `ColumnClaim`: one column's extension at a point equals a value;
* a `WeightedClaim`: `Σ_x W(x)·q(x)` over the stack equals a value, with `W` a weight of the
  stack's oracle interface (`LeanVM.Protocol.Field`): its cube values and an evaluator the
  verifier can run (§3, Definition 3.13).

The bus phase hands on more than claims: the point `ζ` it ended at, since the table sumcheck
runs at it (§5.5), and the *forms* it built, one per side and sumcheck table, each a weighted
sum of row polynomials of the table (`Form`); the forms' values at `ζ` must add up, side by
side, to the totals the bus phase computed (`totals`). A row polynomial is one of the instance's
degree, at most `d` by type: the table sumcheck's round polynomials have degree `d + 1`, so its
completeness is owed only on terms within the bound. No polynomial with coefficients in `E` is
built: the row polynomials are over `K` and the weights carry `E`.

* `commit`: the statement is the public input; it holds when `M3Holds` of the oracle itself.
  Completeness starts from `commitHonest`, which also asks the padding rows to be honest
  (`M3Honest`): soundness cannot extract them.
* `bus`: the point, the forms and totals, and the boundary claims; it holds when every
  constraint's extension is zero at the point, the forms sum to the totals, every claim holds,
  and so do the public lines and the Keccak predicate.
* `table`: column claims and the table sumcheck's point; it holds when every claim and the public
  lines hold, and the Keccak predicate along the point (`M3Instance.auxAt`: the table sumcheck
  turns the predicate on the cube into its multilinear test at the point it draws,
  `Spine/KeccakZero.lean`).
* `pub`: column claims and the point; it holds when every claim holds, and the Keccak predicate
  along the point.
* `done`: nothing, and holds.

The claim pools have the sizes the instance fixes (`busClaims`, `tableClaims`, `pubClaims`): one
claim per boundary column, then per column of each sumcheck table, then per public line. A seam says which
claims hold, not which values a phase pools: that is fixed by the phase's knowledge soundness.
Seams carry no challenge; the escape "violated on the cube, zero at `ζ`" is charged to the bus
phase, where `ζ` is drawn (§5.5).
-/

namespace LeanVM.Protocol

open LeanVM.Parameters CompPoly CPoly CMlPolynomialEval

@[expose] public section

/-! ## Claims -/

/-- A claim on one column of the stack: its extension at a point equals a value. -/
structure ColumnClaim (I : M3Instance) where
  /-- The column. -/
  col : I.ColumnId
  /-- The point, in `E`. -/
  point : Vector E (I.κ col)
  /-- The claimed value. -/
  value : E

/-- The claim holds of the stack `q`. -/
def ColumnClaim.Holds {I : M3Instance} (q : Column I.μ) (c : ColumnClaim I) : Prop :=
  eval₂Mle (I.column q c.col).values (algebraMap K E) c.point = c.value

/-- A weighted claim on the stack: the inner product of a weight with the stack, the stack's
oracle answer to that weight, equals a value. -/
structure WeightedClaim (I : M3Instance) where
  /-- The weight. -/
  weight : Weight E I.μ
  /-- The claimed value. -/
  value : E

/-- The claim holds of the stack `q`. -/
def WeightedClaim.Holds {I : M3Instance} (q : Column I.μ) (c : WeightedClaim I) : Prop :=
  c.weight.pair (algebraMap K E) q.values = c.value

/-! ## Row polynomials and forms -/

namespace M3Instance

variable (I : M3Instance)

/-- A polynomial of a row of table `j` within the instance's degree bound. -/
abbrev RowPoly (j : Fin I.ntab) : Type :=
  {p : CMvPolynomial (I.width j) K // p.totalDegree ≤ I.d}

/-- A form on table `j`: a weighted sum, with weights in `E`, of row polynomials. -/
abbrev Form (j : Fin I.ntab) : Type := List (E × I.RowPoly j)

/-- The virtual table of a row polynomial: its value on every row of the table, lifted to
`E`. -/
def virtualTable (q : Column I.μ) (j : Fin I.ntab) (P : CMvPolynomial (I.width j) K) :
    CMlPolynomialEval E (I.τ j) :=
  Vector.ofFn fun x ↦ ofK (P.eval (I.row q j x))

/-- The value of a form on the stack at a point of its table: the weighted sum of the virtual
tables' extensions there. -/
def Form.eval {j : Fin I.ntab} (f : I.Form j) (q : Column I.μ) (z : Vector E (I.τ j)) : E :=
  (f.map fun t ↦ t.1 * evalMle (I.virtualTable q j t.2.1) z).sum

/-- The point of a sumcheck table inside the point of the table sumcheck: its low `τ j`
coordinates. -/
def lowPoint (p : Vector E I.τmax) (j : I.SumcheckTables) : Vector E (I.τ j.1) :=
  Vector.cast (min_eq_left (I.τ_le_τmax j)) (p.take (I.τ j.1))

end M3Instance

/-! ## Seam statements -/

/-- What the bus phase hands on, in the shape of leanVM's `BusVerify`: the point `ζ` the bus
phase ended at, the forms it built per side (push, pull, count) and sumcheck table, their
totals per side, and the boundary columns' claims. -/
structure BusOut (I : M3Instance) where
  /-- The point, on the sumcheck tables' variables. -/
  point : Vector E I.τmax
  /-- The forms, per side and sumcheck table. -/
  forms : Fin 3 → (j : I.SumcheckTables) → I.Form j.1
  /-- The totals the forms must sum to, per side. -/
  totals : Fin 3 → E
  /-- The boundary columns' claims. -/
  columns : Vector (ColumnClaim I) I.busClaims

/-- What the table sumcheck hands on: column claims, and the point it ended at, along which the
Keccak predicate now holds. -/
structure TableOut (I : M3Instance) where
  /-- The column claims. -/
  columns : Vector (ColumnClaim I) I.tableClaims
  /-- The sumcheck's final point, in coordinate order. -/
  point : Vector E I.τmax

/-- What the public-input phase hands on: column claims, now with the public lines' claims, and
the table sumcheck's point. -/
structure PubOut (I : M3Instance) where
  /-- The column claims. -/
  columns : Vector (ColumnClaim I) I.pubClaims
  /-- The table sumcheck's final point. -/
  point : Vector E I.τmax

/-! ## Seam relations

Each is a set of `((statement, oracle), witness)` with the one oracle the stack and the witness
trivial: after the commit phase the oracle is the witness. -/

/-- The stack behind the one oracle. -/
abbrev theStack {I : M3Instance} (o : ∀ i, TheOracle I i) : Column I.μ := o 0

namespace Seam

variable (I : M3Instance)

/-- The seam of a predicate of the statement and the stack behind the one oracle. -/
def of {S : Type} (P : S → Column I.μ → Prop) : Set ((S × ∀ i, TheOracle I i) × Unit) :=
  {p | P p.1.1 (theStack p.1.2)}

/-- After the commit phase: `M3Holds` of the oracle itself, which pins the oracle to the witness
of record. -/
def commit := of I (M3Holds I)

/-- Before the bus phase, for completeness: `M3Honest`, the stack's padding rows honest too. -/
def commitHonest := of I (M3Honest I)

/-- After the bus phase: every constraint of every sumcheck table has extension zero at the
point, every side's forms sum to the side's total at the point, every boundary claim holds, and
what the bus did not touch. -/
def bus := of I fun (s : I.Stmt × BusOut I) q ↦
  (∀ j : I.SumcheckTables, ∀ C ∈ I.constraints j.1,
    evalMle (I.virtualTable q j.1 C) (I.lowPoint s.2.point j) = 0) ∧
  (∀ side, ∑ j : I.SumcheckTables,
    M3Instance.Form.eval I (s.2.forms side j) q (I.lowPoint s.2.point j) = s.2.totals side) ∧
  (∀ c ∈ s.2.columns.toList, c.Holds q) ∧ I.PublicLinesHold s.1 q ∧ I.aux q

/-- After the table sumcheck: every column claim holds, the public lines hold, and the Keccak
predicate holds at the point. -/
def table := of I fun (s : I.Stmt × TableOut I) q ↦
  (∀ c ∈ s.2.columns.toList, c.Holds q) ∧ I.PublicLinesHold s.1 q ∧ I.auxAt s.2.point.toList q

/-- After the public-input phase: every column claim holds, and the Keccak predicate at the table
sumcheck's point. -/
def pub := of I fun (s : I.Stmt × PubOut I) q ↦
  (∀ c ∈ s.2.columns.toList, c.Holds q) ∧ I.auxAt s.2.point.toList q

/-- After the opening phase: nothing is left to check. -/
def done := of I fun (_ : Unit) _ ↦ True

end Seam

end
end LeanVM.Protocol
