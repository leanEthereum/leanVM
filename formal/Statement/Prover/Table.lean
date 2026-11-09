module

public import Statement.Prover.Script
public import Statement.Prover.Mle

/-!
# The table sumcheck, executable

The prover of `tablePhase` (`tableSumcheck`): receive `ξ`, run the plain sumcheck of four
coefficients per round over `n = max_t τ_t` coordinates, the highest coordinate bound first, then
send every table's column evaluations at the point.

The state holds per table its columns folded at the challenges so far (`foldHigh`) and its running
weight. In the round binding coordinate `m` a table of log-height `τ_t ≤ m` *waits*: it
contributes the line `X·ω_t·σ_t`, `σ_t` its rows summed against the equality weights, computed
once. An *active* table contributes `ω_t·(1 + e_m + X)·Σ_x eq(e_{<m}, x)·P_t(row x at X)`, each
row a line in `X` between the folded columns' halves and `P_t` its constraints and forms batched by
the powers of `ξ`, expanded as a quadratic in `X` (`formQuad`).
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-! ## The high fold -/

/-- Fix a table's highest coordinate at `c`: the table halves, entry `i` becoming
`a[i]·(1 + c) + a[i + h]·c` for `h` the half. -/
def foldHigh (c : E) (a : Array E) : Array E :=
  let h := a.size / 2
  Array.ofFn (n := h) fun i ↦ a.getD i 0 * (1 + c) + a.getD (i + h) 0 * c

/-! ## Quadratics in the round's variable -/

/-- `a₀ + a₁·X + a₂·X²`. -/
abbrev Quad : Type := E × E × E

/-- The sum. -/
def Quad.add (a b : Quad) : Quad := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

/-- A scalar multiple. -/
def Quad.smul (s : E) (a : Quad) : Quad := (s * a.1, s * a.2.1, s * a.2.2)

/-- The product with the line `l + d·X`, the cubic term dropped: exact on a quadratic times a line
whose first factor is at most linear, which is all a monomial of two columns needs. -/
def Quad.mulLine (a : Quad) (l d : E) : Quad :=
  (a.1 * l, a.1 * d + a.2.1 * l, a.2.1 * d + a.2.2 * l)

/-- A monomial `c · Π_i x_i` with each column `x_i` the line `line i`, as a quadratic. -/
def termQuad (line : ℕ → E × E) (term : List ℕ × E) : Quad :=
  term.1.foldl (fun a i ↦ Quad.mulLine a (line i).1 (line i).2) (term.2, 0, 0)

/-- A polynomial (a `Form`'s terms) with each column a line, as a quadratic. -/
def formQuad (terms : List (List ℕ × E)) (line : ℕ → E × E) : Quad :=
  terms.foldl (fun acc term ↦ Quad.add acc (termQuad line term)) (0, 0, 0)

/-- `c₀ + c₁·X + c₂·X² + c₃·X³`. -/
abbrev Cubic : Type := E × E × E × E

/-- The sum. -/
def Cubic.add (a b : Cubic) : Cubic :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2 + b.2.2.2)

/-! ## A table's polynomial -/

/-- `JUMP`'s constraints batched by `cp`, as monomials: `cp₀·(b + cond·w) + cp₁·cond·(b + 1)`
(`jump_constraints`, `crates/verifier/src/layout.rs:294-297`; `jumpConstraints`). -/
def jumpTerms (cp : List E) : List (List ℕ × E) :=
  let c := columnIndexByName jumpColumns
  [([c "b"], cp.getD 0 0), ([c "v_cond", c "w"], cp.getD 0 0),
    ([c "v_cond", c "b"], cp.getD 1 0), ([c "v_cond"], cp.getD 1 0)]

/-- The forms batched by the form powers, as monomials: `Σ_side fp_side · form_side`. -/
def formTerms (fp : List E) (forms : List Form) : List (List ℕ × E) :=
  (fp.zip forms).flatMap fun wf ↦ wf.2.terms.map fun term ↦ (term.1, wf.1 * term.2)

/-- Table `t`'s polynomial in its row: its batched constraints (only `JUMP` has any) and its
batched forms, the terms the verifier's loop (`tableTerms`) evaluates. -/
def rowTerms (cp fp : List E) (forms : List (List Form)) (t : ℕ) : List (List ℕ × E) :=
  (if t = 4 then jumpTerms cp else []) ++ formTerms fp (forms.getD t [])

/-- The factor of coordinate `v` in the weight of a table of log-height `h` at the challenge `c`
(`tableWeights`): `1 + e_v + c` below the height, `c` above. -/
def tableFactor (e : List E) (h v : ℕ) (c : E) : E :=
  if v < h then 1 + e.getD v 0 + c else c

/-! ## The prover's state -/

/-- The table sumcheck's state: per table, its columns folded at the challenges so far, and its
running weight; and the number of free coordinates. -/
structure TableState where
  /-- Per table, per column, the folded column. -/
  cols : Array (Array (Array E))
  /-- Per table, the product of its weight's factors at the challenges so far. -/
  weights : Array E
  /-- The number of free coordinates. -/
  free : ℕ

/-- Column `i` of a table at row `x` of a folded table of `2·half` rows, as the line
`lo + X·(hi + lo)` between its two halves. -/
def rowLine (F : Array (Array E)) (half x : ℕ) (i : ℕ) : E × E :=
  let col := F.getD i #[]
  let lo := col.getD x 0
  (lo, col.getD (x + half) 0 + lo)

/-- An active table's rows summed against the equality weights: `Σ_x eq[x] · P(row x at X)`. -/
def activeQuad (terms : List (List ℕ × E)) (F : Array (Array E)) (eqm : Array E) (half : ℕ) :
    Quad :=
  Nat.fold half (fun x _ acc ↦
    Quad.add acc (Quad.smul (eqm.getD x 0) (formQuad terms (rowLine F half x))))
    (0, 0, 0)

/-- A table's contribution to the round binding coordinate `m`: `X·ω·σ` if it is waiting,
`ω·(1 + e_m + X)·Σ_x eq[x]·P(row x at X)` if it is active. -/
def tableCubic (e : List E) (m : ℕ) (eqm : Array E) (h : ℕ) (w σ : E)
    (terms : List (List ℕ × E)) (F : Array (Array E)) : Cubic :=
  if h ≤ m then (0, w * σ, 0, 0)
  else
    let g := activeQuad terms F eqm (2 ^ m)
    let a := w * (1 + e.getD m 0)
    (a * g.1, a * g.2.1 + w * g.1, a * g.2.2 + w * g.2.1, w * g.2.2)

/-- **The round polynomial**, its four coefficients constant first: the six tables'
contributions, the equality weights of the coordinates below the bound one computed once. -/
def tableRound (e : List E) (logs : List ℕ) (terms : Array (List (List ℕ × E)))
    (sigma : Array E) (st : TableState) : List E :=
  let m := st.free - 1
  let eqm := eqTable (e.take m)
  let c := Nat.fold 6 (fun t _ acc ↦ Cubic.add acc (tableCubic e m eqm (logs.getD t 0)
    (st.weights.getD t 0) (sigma.getD t 0) (terms.getD t []) (st.cols.getD t #[]))) (0, 0, 0, 0)
  [c.1, c.2.1, c.2.2.1, c.2.2.2]

/-- **The fold** at the challenge `c`, binding the highest free coordinate `m`: the active tables'
columns fixed there, every weight times its factor. -/
def tableFold (e : List E) (logs : List ℕ) (st : TableState) (c : E) : TableState :=
  let m := st.free - 1
  { cols := Array.ofFn (n := 6) fun t ↦
      if m < logs.getD t 0 then (st.cols.getD t #[]).map (foldHigh c) else st.cols.getD t #[]
    weights := Array.ofFn (n := 6) fun t ↦
      st.weights.getD t 0 * tableFactor e (logs.getD t 0) m c
    free := m }

/-! ## The tables' data -/

/-- A table's rows summed against the equality weights of the point's first `h` coordinates,
`σ = Σ_y eq(e_{<h}, y)·P(row y)`, needed when the table waits (`h < n`). -/
def tableSigma (e : List E) (n h : ℕ) (terms : List (List ℕ × E)) (F : Array (Array E)) : E :=
  if h < n then
    let eqT := eqTable (e.take h)
    Nat.fold (2 ^ h) (fun y _ acc ↦
      acc + eqT.getD y 0 * (Form.mk terms).evaluate fun i ↦ (F.getD i #[]).getD y 0) 0
  else 0

/-- A table's column evaluations at the end: each folded column's one entry. -/
def finalEvals (F : Array (Array E)) : List E :=
  F.toList.map (·.getD 0 0)

/-- Every table's column evaluations at the end, in table order. -/
def tableEvals (st : TableState) : List E :=
  (List.range 6).flatMap fun t ↦ finalEvals (st.cols.getD t #[])

/-- The constraint powers of `ξ` and its form powers, one per side
(`crates/verifier/src/lib.rs:244-247`). -/
def xiPowers (xi : E) : List E × List E :=
  let nc := (tables.map Table.nConstraints).sum
  ((powers xi (nc + 3)).take nc, (powers xi (nc + 3)).drop nc)

/-- Every table's polynomial, batched by the powers of `ξ`. -/
def tableTermsOf (xi : E) (bus : BusResult) : Array (List (List ℕ × E)) :=
  Array.ofFn (n := 6) fun t ↦ rowTerms (xiPowers xi).1 (xiPowers xi).2 bus.forms t

/-- Every table's columns, lifted to `E`, from the instance's columns by global number. -/
def tableInit (cols : Array (Array K)) : Array (Array (Array E)) :=
  Array.ofFn (n := 6) fun t ↦ Array.ofFn (n := (tables.getD t default).width) fun i ↦
    (cols.getD (globalColumnBases.getD t 0 + i.val) #[]).map ofK

/-- Every table's `σ`. -/
def tableSigmas (e : List E) (logs : List ℕ) (terms : Array (List (List ℕ × E)))
    (F0 : Array (Array (Array E))) : Array E :=
  Array.ofFn (n := 6) fun t ↦
    tableSigma e (logs.foldl max 0) (logs.getD t 0) (terms.getD t []) (F0.getD t #[])

/-- **The table phase, executable.** From the instance's columns `cols` (indexed by global
column), the tables' log-heights `logs` and the bus's result: receive `ξ`, run the rounds, send
every table's evaluations. -/
def tableFast (cols : Array (Array K)) (logs : List ℕ) (bus : BusResult) : Script Unit :=
  let F0 := tableInit cols
  Script.sampleE.bind fun xi ↦
    let terms := tableTermsOf xi bus
    let sigma := tableSigmas bus.point logs terms F0
    (sumcheckBy (tableRound bus.point logs terms sigma) (tableFold bus.point logs)
      (List.replicate (logs.foldl max 0) none) ⟨F0, Array.replicate 6 1, logs.foldl max 0⟩).bind
      fun r ↦ Script.sendList (tableEvals r.2)

end LeanVM.Prover

end
