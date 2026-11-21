/-
  LeanVM.Guest.CoreMode.Fam.ExpDefs

  The `sub` families read off a function's own products of powers of `g`: a run scaled by a factor,
  a run up to a factor's exponent and a point at a factor, each inside the run up to the product's
  exponent.
-/

module

public import LeanVM.Guest.CoreMode.Fam.FamDefs

/-!
# Runs bounded by a product's factors

The checks read the witness's atoms at the cells they name (`cellJ`), each cell inside the frame.
`kVal j as o`: cell `o` holds a constant `g^z` a `const` writes, or a product of two. `pw0`: cell `o`
holds `g^e`, `e < 2^39`, a bounded cell (`cellLt`) or a constant. `pw`: so does a cell a copy or a
quotient by the same divisor ties to such a cell, or a product of two. `eqX j w a b`: cells `a` and
`b` hold one word, through a copy or a product by the constant `1`. `mulX j w okP okU okV`: a
product `[P] = [X]·[Y]` of the witness, `okP P`, one factor `okU`, the other `okV`.

The families (`expFamB`), for the code's `[p] = [u]·[v]`, `[u] = g^eu`, `[v] = g^ev`, so `[p]`'s
exponent is `eu + ev`:
- `expShiftB`: `⟨Q·x, 0, [c], 1, d⟩` inside `⟨Q, 0, [p], 1, d⟩` (or `num H`, `H` above `[p]`'s
  exponent), `[u] = [c]` and `[v]` the factor `x`'s word or the constant `g^(k'-k)` of `Q·g^(k'-k)`.
- `expFacB`: `⟨Q, l, [x], S, d⟩` inside `⟨Q, l, [p], S, d⟩`, `[u]` the base `x`'s word.
- `expPtB`: the point `⟨Q·x, 0, 1, S, d⟩` inside `⟨Q, 0, [p] + t, 1, d⟩`, `t ≥ 1`, `[u]` the base `x`'s
  word.
-/

namespace LeanVM.Guest.Res

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (cellJ fsN)

@[expose] public section

/-- The exponent of a word `g^z`: `1`'s, or one the guest's powers name (`powOf`). -/
noncomputable def powOf1 (c : E) : Option ℕ := if c.limb 1 = 0 ∧ c.limb 0 = 1 then some 0 else powOf c

/-- The exponent of the constant a `const` of `as` writes into cell `o`, inside the frame. -/
noncomputable def kVal1 (j : ℕ) (as : List Atom) (o : ℕ) : Option ℕ :=
  as.findSome? fun
    | .const d c => if cellJ j d == o && inFr j o then powOf1 c else none
    | _ => none

/-- **Cell `o` holds a constant `g^z`**: a `const`'s, or the product of two. -/
noncomputable def kVal (j : ℕ) (as : List Atom) (o : ℕ) : Option ℕ :=
  (kVal1 j as o).or (as.findSome? fun
    | .mul d x y => if cellJ j d == o && inFr j o then
        (kVal1 j as (cellJ j x)).bind fun a ↦ (kVal1 j as (cellJ j y)).map (a + ·) else none
    | _ => none)

/-- **Cell `o` holds `g^e`, `e < 2^39`**: bounded (`cellLt`) or a constant. -/
noncomputable def pw0 (j : ℕ) (w : Wit) (o : ℕ) : Bool :=
  cellLt j w o (2 ^ 39) || match kVal j w.as o with
    | some z => decide (z < 2 ^ 39)
    | none => false

/-- A product atom's cells `(P, X, Y)`, `[P] = [X]·[Y]`, inside the frame. -/
noncomputable def mulAt (j : ℕ) : Atom → Option (ℕ × ℕ × ℕ)
  | .mul d x y => if inFr j (cellJ j d) && inFr j (cellJ j x) && inFr j (cellJ j y) then
      some (cellJ j d, cellJ j x, cellJ j y) else none
  | _ => none

/-- **Cell `o` holds `g^e`, `e < 2^40`**: `pw0`, or a copy of or a copy into a `pw0` cell, or
`[P] = [o]·[Y]` and `[P] = [X]·[Y]` with `[X]` and `[Y]` `pw0`, or the product of two `pw0` cells. -/
noncomputable def pw (j : ℕ) (w : Wit) (o : ℕ) : Bool :=
  pw0 j w o || (inFr j o && w.as.any fun m ↦
    (match m with
      | .copy d s => (cellJ j d == o && inFr j (cellJ j s) && pw0 j w (cellJ j s)) ||
          (cellJ j s == o && inFr j (cellJ j d) && pw0 j w (cellJ j d))
      | _ => false) ||
    (match mulAt j m with
      | some (P, X, Y) => (P == o && pw0 j w X && pw0 j w Y) ||
          (X == o && pw0 j w Y && w.as.any fun m' ↦ match mulAt j m' with
            | some (P', X', Y') => P' == P && Y' == Y && pw0 j w X'
            | none => false)
      | none => false))

/-- **Cells `a` and `b` hold one word**: the same cell, a copy, or a product by the constant `1`. -/
noncomputable def eqX (j : ℕ) (w : Wit) (a b : ℕ) : Bool :=
  a == b || (inFr j a && inFr j b && w.as.any fun m ↦
    (match m with
      | .copy d s => (cellJ j d == a && cellJ j s == b) || (cellJ j d == b && cellJ j s == a)
      | _ => false) ||
    (match mulAt j m with
      | some (P, X, Y) => kVal j w.as Y == some 0 && ((P == a && X == b) || (P == b && X == a))
      | none => false))

/-- **A product of the witness**: `[P] = [X]·[Y]`, `okP P`, one factor `okU` and the other `okV`. -/
noncomputable def mulX (j : ℕ) (w : Wit) (okP okU okV : ℕ → Bool) : Bool :=
  w.as.any fun m ↦ match mulAt j m with
    | some (P, X, Y) => okP P && ((okU X && okV Y) || (okU Y && okV X))
    | none => false

/-- The bound cells `expShiftB` takes for a run's bound: `[p]` itself, or a cell bounded below
`H + 1`. -/
noncomputable def expHi (j : ℕ) (w : Wit) : Mode.Idx → Option (ℕ → Bool)
  | .ex (.fr p) 0 => some fun P ↦ eqX j w P p
  | .num H => some fun P ↦ cellLt j w P (H + 1)
  | _ => none

/-- **A run scaled by a factor** inside the run up to the product's exponent. -/
noncomputable def expShiftB (j : ℕ) (w : Wit) : Mode.Res → Bool
  | .sub a [b] => match frEx a.hi, expHi j w b.hi with
    | some c, some okP =>
      a.lo == .num 0 && b.lo == .num 0 && a.S == 1 && b.S == 1 && a.d == b.d && a.q.fp == b.q.fp &&
        pw j w c &&
        ((a.q.k == b.q.k && a.q.bs.any fun be ↦ be.2 == 1 && decide (a.q.bs = Mode.insertBs (be.1, 1) b.q.bs) &&
            mulX j w okP (fun u ↦ eqX j w u c) fun v ↦ holdsBase j w v be.1 && pw j w v) ||
          (decide (a.q.bs = b.q.bs) && decide (b.q.k ≤ a.q.k) && decide (a.q.k - b.q.k < 2 ^ 39) &&
            mulX j w okP (fun u ↦ eqX j w u c) fun v ↦ kVal j w.as v == some (a.q.k - b.q.k)))
    | _, _ => false
  | _ => false

/-- **A run up to a factor's exponent** inside the run up to the product's. -/
noncomputable def expFacB (j : ℕ) (w : Wit) : Mode.Res → Bool
  | .sub a [b] => match a.hi, b.hi, a.lo with
    | .ex X 0, .ex (.fr p) 0, .num _ =>
      decide (a.q = b.q) && a.lo == b.lo && a.S == b.S && a.d == b.d &&
        mulX j w (fun P ↦ eqX j w P p) (fun u ↦ holdsBase j w u X && pw j w u) (pw j w)
    | _, _, _ => false
  | _ => false

/-- **A point at a factor** inside the run up to the product's exponent and past it. -/
noncomputable def expPtB (j : ℕ) (w : Wit) : Mode.Res → Bool
  | .sub a [b] => match b.hi with
    | .ex (.fr p) t =>
      a.lo == .num 0 && a.hi == .num 1 && b.lo == .num 0 && b.S == 1 && a.d == b.d && decide (1 ≤ t) &&
        a.q.fp == b.q.fp && a.q.k == b.q.k &&
        a.q.bs.any fun be ↦ be.2 == 1 && decide (a.q.bs = Mode.insertBs (be.1, 1) b.q.bs) &&
          mulX j w (fun P ↦ eqX j w P p) (fun u ↦ holdsBase j w u be.1 && pw j w u) (pw j w)
    | _ => false
  | _ => false

/-- **The families of a product's factors.** -/
noncomputable def expFamB (j : ℕ) (w : Wit) (x : Mode.Res) : Bool :=
  expShiftB j w x || expFacB j w x || expPtB j w x

end

end LeanVM.Guest.Res
