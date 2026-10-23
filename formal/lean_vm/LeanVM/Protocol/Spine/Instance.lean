/-
  LeanVM.Protocol.Spine.Instance

  The abstract instance the proof system is stated over, and the relation it proves knowledge of.
-/

module

public import LeanVM.Spec.Verifier
public import LeanVM.Protocol.Compile.Prog
public import LeanVM.Protocol.Blake2sHash
public import LeanVM.Parameters.Field
public import LeanVM.Protocol.Field
public import LeanVM.Protocol.ToArkLib.Flock.BlockR1CS
public import LeanVM.Protocol.ToArkLib.Oracles
public import LeanVM.Protocol.ToCompPoly.Multilinear
public import CompPoly.Multivariate.Basic

/-!
# The M3 instance and the relation `M3Holds`

An `M3Instance` is everything the verifier reads about an arithmetization: the tables with their
log-heights and widths; per table, the constraint polynomials that must vanish on every row
(§5.5) and the bus flushes, each a side and sixteen coordinate polynomials with the domain
separator first (§5.1); a bound `d` on the total degree of both (leanVM's is 2); the count
columns whose cells must be nonzero (§6.2); the boundary blocks, tuples the verifier's side of
the bus provides or consumes, with constant, publicly known or committed coordinates (§5.4); the
layout of every column inside the one committed stack `q`; the columns whose first two cells the
public statement fixes (§8.2); and, where the arithmetization has one, the region of the stack
the Flock argument owns, with the predicate that argument establishes of it (for leanISA, that
Flock's R1CS holds of the bits packed into `q_flock`, §4.2 and Annex C; the toy has none).
Nothing here knows leanISA: leanISA is one instance, built by the adaptor.

Four kinds of quantity are read off an instance by the protocol's schedule. The *sumcheck
tables* are those with a constraint, a flush or a count column; the others are column groups
the table sumcheck never visits. `τmax` is the largest log-height among them, `B` the number of
their constraints, `μBus` the log-height of the bus's leaf stacks, and the claim counts
(`busClaims`, `tableClaims`, `pubClaims`, `poolSize`) are how many claims the phases pool.

Each table also has a row count `rows j ≤ 2 ^ τ j`, the announced one: its rows `x < rows j`
are the *executed* rows, the others *padding* rows, which an honest prover fills with the
public row `padRow j` (§8.3). `M3Holds I input q` is the relation: constraints vanish on every
row, the tuples the executed rows and the boundary push and pull are one multiset (a
permutation, counted in the integers: in characteristic two a tuple pushed twice and never
pulled would sum to zero), executed count cells are nonzero, the public lines hold, the Flock
predicate holds of its region. A padding row is free (Proposition `prop:pad`); completeness
starts from `M3Honest`, which also asks the padding rows to be `padRow` (`PaddingHonest`). It is decidable, and every value is read from `q` through
`I.layout`, so knowledge of `q` is exactly as strong as the layout is. Polynomials are CompPoly's
computable `CMvPolynomial` and degrees its `totalDegree`; `fromCMvPolynomial` bridges to
Mathlib's, whose degree lemmas prove a concrete instance's bound. The announced sizes are not a
clause: the compiled verifier rejects inadmissible sizes before the protocol starts, so the
protocol is a family over admissible instances.

Written from the specification; nothing here transcribes Rust.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters CompPoly CPoly CMlPolynomialEval

@[expose] public section

/-! ## Columns of an instance -/

/-- A side of the bus: a tuple is provided (`push`) or consumed (`pull`). -/
inductive Side
  | push
  | pull
  deriving DecidableEq, Repr

/-- The tables of an instance: how many, and each one's log-height and width. -/
structure Shape where
  /-- Number of tables. -/
  ntab : ℕ
  /-- Log-height of each table: the announced sizes. -/
  τ : Fin ntab → ℕ
  /-- Width of each table. -/
  width : Fin ntab → ℕ

/-- A column: table `j`, column `i`. -/
abbrev Shape.ColumnId (S : Shape) : Type := Σ j : Fin S.ntab, Fin (S.width j)

/-! ## Layouts -/

/-- Read column `c` off the stack through a lift of points: cell `x` of the column is the cell
of the stack at the cube point the lift sends `x` to. -/
def Layout.readWith {μ : ℕ} {ι : Type} {κ : ι → ℕ}
    (extend : (c : ι) → Vector E (κ c) → Vector E μ) (q : Column μ) (c : ι) : Column (κ c) :=
  ⟨Vector.ofFn fun x ↦ q.values.get (boolIndex (extend c (boolVec x)))⟩

/-- How a point of a column of height `2 ^ κ c` lifts to a point of the stack of height `2 ^ μ`
(for an aligned block at selector bits `sel`, `extend c z = (z, sel)`; for a strided slot, the
slot's bits below the point), with the one law that reading the column through the lift and
evaluating it equals evaluating the stack at the lifted point (§4.1, the stacking identity, and
§5.4, equation (2)). It is a reading law, not a stacking law: it does not say the columns are
disjoint slices of `q`. The weaker law "a cube point of the column lifts to a cube point of the
stack" would not do: `z ↦ (z, z)` sends the cube to the cube and `q̃(z, z)` is no column's
extension. -/
structure Layout (μ : ℕ) (ι : Type) (κ : ι → ℕ) where
  /-- Lift a point of column `c` to the point of the stack that reads the same value. -/
  extend : (c : ι) → Vector E (κ c) → Vector E μ
  /-- The reading law: reading then evaluating is lifting then evaluating. -/
  read_eval : ∀ (q : Column μ) (c : ι) (z : Vector E (κ c)),
    eval₂Mle (Layout.readWith extend q c).values (algebraMap K E) z =
      eval₂Mle q.values (algebraMap K E) (extend c z)

/-- Read column `c` off the stack. -/
abbrev Layout.read {μ : ℕ} {ι : Type} {κ : ι → ℕ} (L : Layout μ ι κ) :
    Column μ → (c : ι) → Column (κ c) :=
  Layout.readWith L.extend

/-! ## Boundary blocks, public lines, the Flock region -/

/-- One coordinate of a boundary tuple on a block of height `2 ^ κ`: a constant, a column both
parties know (the index column `g^i`, the bytecode column), or a committed column of the same
height. -/
inductive Coord (S : Shape) (κ : ℕ)
  | const (c : K)
  | known (col : Column κ)
  | committed (c : S.ColumnId) (h : S.τ c.1 = κ)

/-- The committed column a coordinate names, if it names one. -/
def Coord.committed? {S : Shape} {κ : ℕ} : Coord S κ → Option S.ColumnId
  | .committed c _ => some c
  | _ => none

/-- A boundary block (§5.4): `2 ^ κ` tuples on one side of the bus, coordinate by coordinate. -/
structure BoundaryBlock (S : Shape) where
  /-- Log-height of the block. -/
  κ : ℕ
  /-- The side its tuples are on. -/
  side : Side
  /-- The sixteen coordinates, the separator first. -/
  coords : Vector (Coord S κ) 16

/-- A column whose first two cells the public statement fixes (§8.2: the two public words are
the first two memory cells). -/
structure PublicLine (S : Shape) where
  /-- The column. -/
  col : S.ColumnId
  /-- The value cell 0 must hold. -/
  cell0 : K
  /-- The value cell 1 must hold. -/
  cell1 : K
  /-- Whether the proof carries the value claimed for this column on the line through its two
  cells (§8.2: it does for the two low limbs of the memory, and not for the top limb, whose
  value is known to be zero). It fixes the transcript, not the relation. -/
  sent : Bool
  /-- The column has a cell 1. -/
  pos : 0 < S.τ col.1

/-- Bit `i` of a cell, the coefficient of `x ^ i`, as `0` or `1` in `E`. -/
def cellBit (a : K) (i : ℕ) : E := if a.toBitVec.getLsbD i then 1 else 0

/-- The table of bit `i` of every cell of a column: the `i`-th of the `64` Boolean tables a
column of `K` packs (Annex A, §A.1: `q(u) = Σ_i Q_i(u)·x^i`). -/
def bitTable {n : ℕ} (c : Column n) (i : Fin (2 ^ Flock.kSkip)) : CMlPolynomialEval E n :=
  Vector.ofFn fun u ↦ cellBit (c.values.get u) i

/-- Where the packed witness of the Flock argument sits: a column of height `2 ^ (8 + kBatch)`,
`2 ^ kBatch` blocks of `2 ^ 14` bits packed 64 to a cell, and the R1CS each block satisfies,
with the walks a verifier evaluates its matrices by (Annex C). -/
structure FlockRegion (S : Shape) where
  /-- The column. -/
  col : S.ColumnId
  /-- The log-count of compressions. -/
  kBatch : ℕ
  /-- The column holds `2 ^ kBatch` blocks of `2 ^ 8` cells. -/
  height : S.τ col.1 = 8 + kBatch
  /-- The R1CS of one block of `2 ^ 14` positions. -/
  r1cs : BlockR1CS E (Flock.kSkip + Flock.kIn)

/-- What the Flock phase establishes of the region (Annex C, §C.1): every block of `2 ^ 14`
bits, packed 64 to a cell, satisfies the R1CS and holds `1` at the constant position. Block `t`
holds at position `j` bit `j mod 64` of cell `j / 64 + 256·t`: within-block coordinates low,
batch coordinates high. -/
def FlockRegion.Holds {S : Shape} (r : FlockRegion S) (c : Column (8 + r.kBatch)) : Prop :=
  BlockR1CS.BatchHolds r.r1cs Flock.constPos (bitTable c)

instance {S : Shape} (r : FlockRegion S) (c : Column (8 + r.kBatch)) : Decidable (r.Holds c) :=
  inferInstanceAs (Decidable (BlockR1CS.BatchHolds _ _ _))

/-! ## The instance -/

/-- Everything the verifier reads about an arithmetization. -/
structure M3Instance extends Shape where
  /-- The public statement type (leanISA: `PublicInput`). -/
  Stmt : Type
  /-- The constraint polynomials of each table, in the row's variables. -/
  constraints : (j : Fin ntab) → List (CMvPolynomial (width j) K)
  /-- The flush tuples of each table: a side and sixteen coordinate polynomials, separator first. -/
  flushes : (j : Fin ntab) → List (Side × Vector (CMvPolynomial (width j) K) 16)
  /-- The degree bound: every constraint and every flush coordinate has total degree at most
  `d`; leanVM's is 2. -/
  d : ℕ
  /-- Every constraint has total degree at most `d`. -/
  constraints_degree : ∀ j, ∀ C ∈ constraints j, C.totalDegree ≤ d
  /-- Every flush coordinate has total degree at most `d`. -/
  flushes_degree : ∀ j, ∀ f ∈ flushes j, ∀ k, (f.2.get k).totalDegree ≤ d
  /-- The count columns of each table. -/
  counts : (j : Fin ntab) → List (Fin (width j))
  /-- The row count of each table: its rows `x < rows j` are the *executed* rows, the others
  *padding* rows (§5.1, §8.3): the announced row counts. -/
  rows : Fin ntab → ℕ
  /-- A table's rows fit in its height. -/
  rows_le : ∀ j, rows j ≤ 2 ^ τ j
  /-- The public row an honest prover fills a padding row of each table with (§8.3). -/
  padRow : (j : Fin ntab) → Fin (width j) → K
  /-- The boundary blocks. -/
  boundary : List (BoundaryBlock toShape)
  /-- Log-height of the committed stack. -/
  μ : ℕ
  /-- The stack layout. -/
  layout : Layout μ toShape.ColumnId (fun c ↦ τ c.1)
  /-- How many columns the statement fixes cells of: a constant of the instance, so that the
  number of claims the public-input phase pools is one. -/
  nLines : ℕ
  /-- The columns whose first two cells the statement fixes. -/
  publicLines : Stmt → Vector (PublicLine toShape) nLines
  /-- The region the Flock argument owns, if the arithmetization has one. -/
  flock : Option (FlockRegion toShape)

namespace M3Instance

variable (I : M3Instance)

/-- Log-height of a column: its table's. -/
abbrev κ (c : I.ColumnId) : ℕ := I.τ c.1

/-- Read one column off the stack. -/
def column (q : Column I.μ) (c : I.ColumnId) : Column (I.κ c) := I.layout.read q c

/-- Row `x` of table `j`, read off the stack. -/
def row (q : Column I.μ) (j : Fin I.ntab) (x : Fin (2 ^ I.τ j)) : Fin (I.width j) → K :=
  fun i ↦ (I.column q ⟨j, i⟩).values.get x

/-- The value of a boundary coordinate at row `x` of its block. -/
def coordCell (q : Column I.μ) {κ : ℕ} : Coord I.toShape κ → Fin (2 ^ κ) → K
  | .const c, _ => c
  | .known col, x => col.values.get x
  | .committed c h, x => (I.column q c).values.get (Fin.cast (congrArg (2 ^ ·) h.symm) x)

/-- The executed rows of table `j`, in order: the rows `x < rows j`. -/
def executed (j : Fin I.ntab) : List (Fin (2 ^ I.τ j)) :=
  (List.finRange (2 ^ I.τ j)).filter fun x ↦ decide (x.val < I.rows j)

/-- The first `m` of `N` indices, by filtering or by casting. -/
theorem filter_finRange_lt : ∀ {N m : ℕ} (h : m ≤ N),
    (List.finRange N).filter (fun x ↦ decide (x.val < m)) = (List.finRange m).map (Fin.castLE h)
  | 0, 0, _ => rfl
  | N + 1, m, h => by
    rw [List.finRange_succ_last, List.filter_append, List.filter_map]
    by_cases hm : m ≤ N
    · have hl : ¬ (Fin.last N).val < m := by simp; omega
      rw [List.filter_cons_of_neg (by simpa using hl), List.filter_nil, List.append_nil]
      have ih := filter_finRange_lt hm
      rw [show (fun x : Fin (N + 1) ↦ decide (x.val < m)) ∘ Fin.castSucc =
        fun x : Fin N ↦ decide (x.val < m) from rfl, ih, List.map_map]
      rfl
    · have hmN : m = N + 1 := by omega
      subst hmN
      rw [List.filter_cons_of_pos (by simp), List.filter_eq_self.mpr (fun x _ ↦ by simp),
        List.finRange_succ_last, List.map_append, List.map_map, List.map_cons, List.map_nil]
      rfl

/-- The executed rows of table `j` are its first `rows j` rows. -/
theorem executed_eq (j : Fin I.ntab) :
    I.executed j = (List.finRange (I.rows j)).map (Fin.castLE (I.rows_le j)) :=
  filter_finRange_lt (I.rows_le j)

/-- The tuples of one side flushed by the tables: every table, every flush of that side, every
executed row. A padding row flushes nothing (§8.3, Proposition `prop:pad`). -/
def flushTuples (q : Column I.μ) (s : Side) : List (Vector K 16) :=
  (List.finRange I.ntab).flatMap fun j ↦
    ((I.flushes j).filter fun f ↦ decide (f.1 = s)).flatMap fun f ↦
      (I.executed j).map fun x ↦ f.2.map fun P ↦ P.eval (I.row q j x)

/-- The tuples of one side on the boundary blocks. -/
def boundaryTuples (q : Column I.μ) (s : Side) : List (Vector K 16) :=
  (I.boundary.filter fun b ↦ decide (b.side = s)).flatMap fun b ↦
    (List.finRange (2 ^ b.κ)).map fun x ↦ b.coords.map fun co ↦ I.coordCell q co x

/-- Every tuple of one side of the bus. -/
def tuples (q : Column I.μ) (s : Side) : List (Vector K 16) :=
  I.flushTuples q s ++ I.boundaryTuples q s

/-- The Flock region, read off the stack at its height. -/
def flockColumn (r : FlockRegion I.toShape) (q : Column I.μ) : Column (8 + r.kBatch) :=
  ⟨Vector.cast (congrArg (2 ^ ·) r.height) (I.column q r.col).values⟩

/-! ## What the schedule reads off the instance -/

/-- A table the table sumcheck visits: one with a constraint, a flush or a count column. The
others are column groups the sumcheck never sees. -/
def SumcheckTable (j : Fin I.ntab) : Prop :=
  I.constraints j ≠ [] ∨ I.flushes j ≠ [] ∨ I.counts j ≠ []

instance instDecidableSumcheckTable (j : Fin I.ntab) : Decidable (I.SumcheckTable j) :=
  decidable_of_iff ((I.constraints j).isEmpty = false ∨ (I.flushes j).isEmpty = false ∨
    (I.counts j).isEmpty = false) (by simp [SumcheckTable])

/-- The sumcheck tables, as a type. -/
abbrev SumcheckTables : Type := {j : Fin I.ntab // I.SumcheckTable j}

/-- The largest log-height among the sumcheck tables: the number of rounds of the table
sumcheck. -/
def τmax : ℕ := Finset.univ.sup fun j : I.SumcheckTables ↦ I.τ j.1

/-- Every sumcheck table's log-height is at most `τmax`. -/
theorem τ_le_τmax (j : I.SumcheckTables) : I.τ j.1 ≤ I.τmax :=
  Finset.le_sup (f := fun j : I.SumcheckTables ↦ I.τ j.1) (Finset.mem_univ j)

/-- The number of constraints of the sumcheck tables: the batching challenge of the table
sumcheck takes one power per constraint, then three for the bus sides. -/
def B : ℕ := ∑ j : I.SumcheckTables, (I.constraints j.1).length

/-- The number of leaves of the push side of the bus: one per row of every pushing boundary
block and of every push flush of every table. -/
def pushLeaves : ℕ :=
  ((I.boundary.filter fun b ↦ decide (b.side = .push)).map fun b ↦ 2 ^ b.κ).sum +
    ((List.finRange I.ntab).map fun j ↦
      ((I.flushes j).filter fun f ↦ decide (f.1 = .push)).length * 2 ^ I.τ j).sum

/-- The log-height of the bus's leaf stacks: the push side's leaves, stacked largest first at
aligned offsets with no floor on the depth (`leaf.rs:141-148`). The pull and count trees take
the same depth, which the deployed prover asserts of its layouts (`leaf.rs:115-138`, the count
tree padded to it at `:654`; the verifier's own check, `leaf.rs:875-882` at `a386121f`, is removed
at `127510d1`, whose verifier walks the three trees at the push side's depth,
`crates/verifier/src/bus.rs:116`) and an instance does not guarantee: the bus phase assumes it of
the instance. -/
def μBus : ℕ := Nat.clog 2 I.pushLeaves

/-- The committed columns the boundary blocks name, each once, in the order in which the sides,
their blocks and their coordinates first name it: the columns the bus phase pools a claim on. -/
def boundaryColumns : List I.ColumnId :=
  (([Side.push, Side.pull].flatMap fun s ↦
    (I.boundary.filter fun b ↦ decide (b.side = s)).flatMap fun b ↦
      b.coords.toList.filterMap Coord.committed?)).eraseDups

/-- The number of columns of the sumcheck tables: one claim each after the table sumcheck. -/
def tableColumns : ℕ := ∑ j : I.SumcheckTables, I.width j.1

/-- The number of weighted claims the Flock phase pools: one if there is a region. -/
def flockClaims : ℕ :=
  match I.flock with
  | some _ => 1
  | none => 0

/-- The claims pooled after the bus phase: one per boundary column. -/
abbrev busClaims : ℕ := I.boundaryColumns.length

/-- The claims pooled after the table sumcheck: the bus phase's and one per column of each
sumcheck table. -/
abbrev tableClaims : ℕ := I.busClaims + I.tableColumns

/-- The claims pooled after the public-input phase: one more per public line. -/
abbrev pubClaims : ℕ := I.tableClaims + I.nLines

/-- The claims the opening phase batches: the column claims and the Flock phase's weighted
claims. -/
abbrev poolSize : ℕ := I.pubClaims + I.flockClaims

end M3Instance

/-! ## The relation, clause by clause -/

namespace M3Instance

variable (I : M3Instance)

/-- Every constraint vanishes on every row of its table (the zerocheck, §5.5). -/
def ConstraintsVanish (q : Column I.μ) : Prop :=
  ∀ j, ∀ C ∈ I.constraints j, ∀ x, C.eval (I.row q j x) = 0

/-- The pushed tuples are one multiset with the pulled tuples (the bus, §5.2), counted in `ℕ`. -/
def Balanced (q : Column I.μ) : Prop := (I.tuples q .push).Perm (I.tuples q .pull)

/-- Every executed cell of every count column is nonzero (the count product `R_c ≠ 0`, §6.2). -/
def CountsNonzero (q : Column I.μ) : Prop :=
  ∀ j, ∀ i ∈ I.counts j, ∀ x : Fin (2 ^ I.τ j), x.val < I.rows j →
    (I.column q ⟨j, i⟩).values.get x ≠ 0

/-- Every padding row holds its table's public padding row: what an honest prover commits
(§8.3), and what completeness, not soundness, needs. -/
def PaddingHonest (q : Column I.μ) : Prop :=
  ∀ j, ∀ x : Fin (2 ^ I.τ j), I.rows j ≤ x.val → I.row q j x = I.padRow j

/-- Cells 0 and 1 of every column the statement fixes hold their values (§8.2). -/
def PublicLinesHold (input : I.Stmt) (q : Column I.μ) : Prop :=
  ∀ l ∈ (I.publicLines input).toList,
    (I.column q l.col).values.get ⟨0, Nat.two_pow_pos _⟩ = l.cell0 ∧
      (I.column q l.col).values.get ⟨1, Nat.one_lt_two_pow l.pos.ne'⟩ = l.cell1

/-- The Flock predicate holds of the Flock region, if there is one: what the Flock phase
establishes, the statement its honest prover can convince the verifier of (for leanISA, Flock's
R1CS on the bits packed into `q_flock`; that the limb slots then compress is a consequence). -/
def aux (q : Column I.μ) : Prop := ∀ r ∈ I.flock, r.Holds (I.flockColumn r q)

instance instDecidableAux (q : Column I.μ) : Decidable (I.aux q) :=
  inferInstanceAs (Decidable (∀ r ∈ I.flock, r.Holds (I.flockColumn r q)))

deriving instance Decidable for ConstraintsVanish, Balanced, CountsNonzero, PublicLinesHold,
  PaddingHonest

end M3Instance

/-- The relation the oracle protocol proves knowledge of: what the verifier establishes about
the committed stack `q`. -/
def M3Holds (I : M3Instance) (input : I.Stmt) (q : Column I.μ) : Prop :=
  I.ConstraintsVanish q ∧ I.Balanced q ∧ I.CountsNonzero q ∧ I.PublicLinesHold input q ∧ I.aux q

-- The relation is decidable: every clause is a finite check over computable data.
deriving instance Decidable for M3Holds

/-- The relation completeness starts from: `M3Holds`, and every padding row holds its public row.
Knowledge soundness extracts `M3Holds` only, since a padding row is free (Proposition
`prop:pad`). -/
def M3Honest (I : M3Instance) (input : I.Stmt) (q : Column I.μ) : Prop :=
  M3Holds I input q ∧ I.PaddingHonest q

/-- The one oracle of the protocol from the commit phase on: the stack. -/
abbrev TheOracle (I : M3Instance) : Fin 1 → Type := OneOracle (Column I.μ)

/-- `M3Holds` as ArkLib states relations: the statement is the public input with no oracle, the
witness is the stack. -/
def M3Rel (I : M3Instance) : Set ((I.Stmt × (∀ i, NoOracle i)) × Column I.μ) :=
  {p | M3Holds I p.1.1 p.2}

/-- `M3Honest` as ArkLib states relations: the relation completeness starts from. -/
def M3HonestRel (I : M3Instance) : Set ((I.Stmt × (∀ i, NoOracle i)) × Column I.μ) :=
  {p | M3Honest I p.1.1 p.2}

end
end LeanVM.Protocol
