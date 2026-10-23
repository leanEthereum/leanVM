/-
  LeanVM.Protocol.Spine.Toy

  The toy instance: one table of width three and height two on a stack of height eight, with one
  constraint, one push, one boundary pull, one count column and one public line. Every phase is
  tested on it.
-/

module

public import LeanVM.Protocol.Spine.Instance
import CompPoly.Multivariate.MvPolyEquiv.Eval
import CompPoly.Multivariate.Operations
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# The toy instance

One table of width 3 and height 2 on a stack of height 8: column `i` at cells `2i, 2i + 1`, cells
6 and 7 padding. Column 2 must be Boolean, and it is the public line: its cell 0 is the public
statement, its cell 1 is `0`, and its value on the line is sent. The table pushes `(0, X₀, 0, …)`
on every row, slot 0 its constant domain separator, and one boundary block pulls
`(0, [1, 1], 0, …)`, the known column `[1, 1]` in slot 1, so the bus balances exactly when
column 0 is `[1, 1]` in some order; column 1 is a count column; there is no Flock region;
the degree bound is 2.
`M3Holds` on it is decided by evaluation, and each of its clauses can be made to fail alone
(`tests/LeanVMTests/Protocol/Spine.lean`).
-/

namespace LeanVM.Protocol.Toy

open LeanVM.Parameters LeanVM.Protocol CompPoly CPoly CMlPolynomialEval

@[expose] public section

/-- The tables of the toy: one table of height two and width three. -/
abbrev shape : Shape := ⟨1, fun _ ↦ 1, fun _ ↦ 3⟩

/-- The columns of the toy: one table, three columns. -/
abbrev Col : Type := shape.ColumnId

/-- Column `i` is the slice at cells `2i, 2i + 1`. -/
def slice (q : Column 3) (c : Col) : Column 1 :=
  ⟨#v[q.values.get ⟨2 * c.2.val, by have h : c.2.val < 3 := c.2.isLt; omega⟩,
      q.values.get ⟨2 * c.2.val + 1, by have h : c.2.val < 3 := c.2.isLt; omega⟩]⟩

/-- The selector of column `i` is the pair of bits `(i mod 2, i div 2)`. -/
def extend (c : Col) (z : Vector E 1) : Vector E 3 :=
  #v[z.head, if c.2.val % 2 = 1 then 1 else 0, if c.2.val / 2 = 1 then 1 else 0]

/-- Reading through the lift is taking the slice. -/
private theorem readWith_extend (q : Column 3) (c : Col) :
    Layout.readWith extend q c = slice q c := by
  fin_cases c <;>
    (apply congrArg Column.mk; apply Vector.ext; intro i hi; interval_cases i <;>
      simp [extend, boolIndex, boolVec, Vector.head])

/-- The layout law for the three slices: the slice's extension at `z` is the stack's at
`(z, i mod 2, i div 2)`. -/
theorem read_eval (q : Column 3) (c : Col) (z : Vector E 1) :
    eval₂Mle (Layout.readWith extend q c).values (algebraMap K E) z =
      eval₂Mle q.values (algebraMap K E) (extend c z) := by
  rw [readWith_extend]
  fin_cases c <;> simp [CMlPolynomialEval.eval₂Mle, CMlPolynomialEval.evalMle,
    CMlPolynomialEval.evalMleValues, CMlPolynomialEval.evalMleStep, CMlPolynomialEval.map,
    Vector.head, Vector.tail, extend, slice]

/-- The layout of the toy. -/
def layout : Layout 3 Col (fun _ ↦ 1) where
  extend := extend
  read_eval := read_eval

/-- The one constraint: column 2 is Boolean. -/
def constraint : CMvPolynomial 3 K := CMvPolynomial.X 2 * CMvPolynomial.X 2 - CMvPolynomial.X 2

/-- The constraint has total degree at most two, through Mathlib's degree lemmas. -/
private theorem constraint_totalDegree : constraint.totalDegree ≤ 2 := by
  rw [totalDegree_equiv (S := K), constraint]
  erw [CPoly.map_sub]
  rw [CPoly.map_mul, CMvPolynomial.fromCMvPolynomial_X]
  exact (MvPolynomial.totalDegree_sub _ _).trans
    (max_le ((MvPolynomial.totalDegree_mul _ _).trans (by simp)) (by simp))

/-- The one flush: `(0, X₀, 0, …)`, pushed; slot 0, the domain separator, is constant. -/
def flush : Side × Vector (CMvPolynomial 3 K) 16 :=
  (.push, Vector.ofFn fun k ↦ if k.val = 1 then CMvPolynomial.X 0 else 0)

/-- Every coordinate of the flush has total degree at most one. -/
private theorem flush_totalDegree (k : Fin 16) : (flush.2.get k).totalDegree ≤ 1 := by
  rw [totalDegree_equiv (S := K)]
  simp only [flush, Vector.get_ofFn]
  split
  · simp [CMvPolynomial.fromCMvPolynomial_X]
  · simp

/-- The one boundary block: pulls `(0, [1, 1], 0, …)`. -/
def boundary : BoundaryBlock shape where
  κ := 1
  side := .pull
  coords := Vector.ofFn fun k ↦ if k.val = 1 then .known ⟨#v[1, 1]⟩ else .const 0

/-- The toy instance. An `abbrev`, so that its fields reduce wherever a test names it. -/
abbrev toy : M3Instance where
  toShape := shape
  Stmt := K
  constraints := fun _ ↦ [constraint]
  flushes := fun _ ↦ [flush]
  d := 2
  constraints_degree := fun _ C h ↦ by
    rw [List.mem_singleton.mp h]; exact constraint_totalDegree
  flushes_degree := fun _ f h k ↦ by
    rw [List.mem_singleton.mp h]; exact (flush_totalDegree k).trans (by decide)
  counts := fun _ ↦ [1]
  rows := fun j ↦ 2 ^ shape.τ j
  rows_le := fun _ ↦ le_rfl
  padRow := fun _ _ ↦ 0
  boundary := [boundary]
  μ := 3
  layout := layout
  nLines := 1
  publicLines := fun v ↦ #v[⟨⟨0, 2⟩, v, 0, true, by decide⟩]
  flock := none

/-- The honest stack: columns `[1, 1]`, `[1, 1]`, `[1, 0]`, then padding. -/
def honest : Column 3 := ⟨#v[1, 1, 1, 1, 1, 0, 0, 0]⟩

end
end LeanVM.Protocol.Toy
