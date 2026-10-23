/-
  LeanVM.Protocol.EndToEnd.Complete.Facts

  What each phase of an honest run hands the next: the true row values of the opcode tables,
  the facts the bus phase establishes of its result for the table sumcheck, and the true slices
  the Flock phase returns for ring switching.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.Claims

/-!
# The facts an honest run threads

The verifier program's phases (`LeanVM.Protocol.Verifier.verifyExecution`,
`python-verifier/verifier.py:1358-1407` at leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`)
pass data to each other: the bus's `BusResult` to the table sumcheck, Flock's point and slices to
ring switching. Against the honest prover of a stack `q` (`inst prog s`), that data is true of
`q`; this module names what "true" means, the interface between the phases' completeness proofs.

* `rowVal prog s q t x`: row `x` of opcode table `t`, read off the stack through the instance's
  layout, as the function of the Python's local column index the forms evaluate
  (`Form.evaluate`), `0` past the table's width.
* `BusGood prog s q b`: the bus phase's result is true. Its framework claims are true
  (`TrueClaims`); its point is long enough for every table; it holds one degree-two form per table
  and side; and each side's total is the sum, over every table's rows, of the equality weight of
  the row against the point's first `τ_t` coordinates times the table's form for the side. This is
  what makes the table sumcheck's target `Σ_side ξ^side · total_side` the true batched sum.
* `flockSlice prog s q i point`: slice `i` of the Flock region at `point`, the extension of bit
  `i` of every `QFLOCK` cell (`cellBit`), the first coordinate the lowest bit of the cell index.
  `FlockGood`: Flock's result is a point of the region's `8 + τ_BLAKE2S` coordinates and the 64
  true slices there.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Complete

@[expose] public section

/-! ## The opcode tables' rows -/

/-- Row `x` of opcode table `t` read off the stack, as a function of the local column index (the
Python's `evaluations.getD · 0`): cell `i` lifted to `E`, `0` past the width. -/
def rowVal (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) (t : Fin 6)
    (x : Fin (2 ^ s.τ t)) : ℕ → E :=
  fun i ↦ if h : i < width (opIdx t) then ofK ((inst prog s).row q (opIdx t) x ⟨i, h⟩) else 0

/-! ## The bus's result -/

/-- Every form of a table has degree at most two: each monomial is at most two column indices. -/
def FormsDeg2 (forms : List (List Form)) : Prop :=
  ∀ t side, ∀ term ∈ ((forms.getD t []).getD side {}).terms, term.1.length ≤ 2

/-- The true total of a side: every table's form for the side, summed over the table's rows
against the equality weight of the point's first `τ_t` coordinates. -/
def trueTotal (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) (point : List E)
    (forms : List (List Form)) (side : ℕ) : E :=
  ∑ t : Fin 6, ∑ x : Fin (2 ^ s.τ t),
    eqEval (point.take (s.τ t)) (boolPoint (s.τ t) x) *
      ((forms.getD t []).getD side {}).evaluate (rowVal prog s q t x)

/-- **The bus's result is true**: its claims are true, its point covers every table, it holds one
degree-two form per table and side, and every side's total is the true total of its forms. -/
structure BusGood (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) (b : BusResult) :
    Prop where
  /-- The framework claims are true. -/
  claims : TrueClaims prog s q b.claims
  /-- The point covers every table's coordinates. -/
  point_length : ∀ t : Fin 6, s.τ t ≤ b.point.length
  /-- One row of forms per table. -/
  forms_length : b.forms.length = 6
  /-- Three forms per table, one per side. -/
  forms_row_length : ∀ t, t < 6 → (b.forms.getD t []).length = 3
  /-- Every form has degree at most two. -/
  forms_deg : FormsDeg2 b.forms
  /-- Three totals. -/
  totals_length : b.totals.length = 3
  /-- Every side's total is the true total. -/
  totals : ∀ side, side < 3 → b.totals.getD side 0 = trueTotal prog s q b.point b.forms side

/-! ## Flock's result -/

/-- Slice `i` of the Flock region at `point`: the extension of bit `i` of the `QFLOCK` cells,
the first coordinate the lowest bit of the cell index. -/
def flockSlice (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) (i : ℕ)
    (point : List E) : E :=
  multilinearEval (((inst prog s).column q flockCol).values.toList.map fun a ↦ cellBit a i) point

/-- **Flock's result is true**: a point of the region's coordinates and the 64 true slices
there. -/
def FlockGood (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))
    (r : List E × List E) : Prop :=
  r.1.length = 8 + s.τ 5 ∧ r.2 = (List.range 64).map fun i ↦ flockSlice prog s q i r.1

end
end LeanVM.Protocol.EndToEnd.Complete
