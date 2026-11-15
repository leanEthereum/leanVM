/-
  LeanVM.Guest.Res.FamDefs

  The shared checks of the residual families read off a function's own code: the atoms on every
  returning path, the guest's constant powers of `g`, and the exponent bounds its range checks and
  selectors put on frame cells.
-/

module

public import LeanVM.Guest.Res.SelDefs
public import LeanVM.Guest.Data.Pows
public import LeanVM.Guest.Res.CarryDefs
public import LeanVM.Guest.ExpTables
public import LeanVM.Guest.Memory.StaticCut

/-!
# The families' shared checks

`topAtoms ss`: the top-level atoms of a block before its first statement that may return; each is
on every returning path of the block. `powOf w`: the exponent `e` of a word `w = g^e` the guest's
table of powers names (`Data.powTree`). `rcBound as v`: a range check of `as` on value `v` against
a constant of `as`, `g^(N - 1)`, bounds `v`'s exponent below `N`.

`cellLt j w o N`: at function `j`'s frames, cell `o` holds `g^e`, `e < N`: a value of the cell is
range checked (`rcBound`) or a top-level selector (`topSels`), the cell inside the frame.
-/

namespace LeanVM.Guest.Res

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (PowTree)
open LeanVM.Guest.B2C (cellJ fsN)

@[expose] public section

/-- The top-level atoms of a block before its first statement that may return (`noRetR`, by the
recursor, for the kernel). -/
noncomputable def topAtoms : List Stmt → List Atom
  | [] => []
  | .atom a :: ss => a :: topAtoms ss
  | s :: ss => if Memory.noRetR s then topAtoms ss else []

/-- The exponent of a word of `K` the guest's powers name. -/
noncomputable def powOf (w : E) : Option ℕ :=
  if w.limb 1 = 0 then Data.powTree.find (w.limb 0).toBitVec.toNat else none

/-- The constant word of value `k` among the atoms. -/
def constOf (as : List Atom) (k : V) : Option E :=
  as.findSome? fun
    | .const d w => if d = k then some w else none
    | _ => none

/-- **A range check's bound** on value `v`: `rangeCheck v _ _ _ k` among the atoms, `k` the
constant `g^(N - 1)`, `N ≤ 2^33`. -/
noncomputable def rcBound (as : List Atom) (v : V) : Option ℕ :=
  as.findSome? fun
    | .rangeCheck x _ _ _ k =>
      if x = v then
        match (constOf as k).bind powOf with
        | some e => if e + 1 ≤ 2 ^ 33 then some (e + 1) else none
        | none => none
      else none
    | _ => none

/-- The top-level selectors of a block before its first statement that may return: each one's value
and count of arms. -/
noncomputable def topSels : List Stmt → List (V × ℕ)
  | [] => []
  | s :: ss => (match selOf s with
      | some p => [p]
      | none => []) ++ (if Memory.noRetR s then topSels ss else [])

/-- **A family's witness**: atoms and selectors of a function's own code it reads, each on every
returning path (`witOk`), so a family's check scans them, not the whole body. -/
structure Wit where
  as : List Atom
  ss : List (V × ℕ)

/-- The witness's atoms are top-level atoms of function `j`'s body and its selectors top-level
selectors. -/
noncomputable def witOk (j : ℕ) (w : Wit) : Bool :=
  w.as.all (fun a => (topAtoms (coreOf j).body).contains a) &&
    w.ss.all fun p => (topSels (coreOf j).body).contains p

/-- **Cell `o` of function `j` holds `g^e`, `e < N`**: inside the frame, a value of the cell range
checked on every path, or a selector named on every path. -/
noncomputable def cellLt (j : ℕ) (w : Wit) (o N : ℕ) : Bool :=
  decide (2 ≤ o) && decide (o < fsN j) && decide (N ≤ 2 ^ 62) &&
    (w.as.any (fun
      | .rangeCheck x _ _ _ _ => cellJ j x == o &&
          (match rcBound w.as x with
            | some n => decide (n ≤ N)
            | none => false)
      | _ => false) ||
      w.ss.any fun p => cellJ j p.1 == o && decide (p.2 ≤ N) &&
        (decide (p.1 ∈ (coreOf j).params) || w.as.any fun a => decide (p.1 ∈ atomUses a)))

/-- The frame cell `c` of an exponent `[c]`'s. -/
def frEx : Mode.Idx → Option ℕ
  | .ex (.fr c) 0 => some c
  | _ => none

/-- Cell `o` of function `j` holds base `B`'s word: `B` is the cell, or the word a top-level load
reads from `[q]·g^d` into it. -/
noncomputable def holdsBase (j : ℕ) (w : Wit) (o : ℕ) : Mode.Base → Bool
  | .fr b => b == o
  | .hp q d => decide (2 ≤ q) && decide (q < fsN j) && w.as.any fun
      | .load y p d' => cellJ j y == o && cellJ j p == q && d' == d
      | _ => false

/-- Cell `o` is inside function `j`'s frame. -/
noncomputable def inFr (j o : ℕ) : Bool := decide (2 ≤ o) && decide (o < fsN j)

/-- The cells of function `j` holding cell `c`'s word: `c`, and those a top-level copy ties to it. -/
noncomputable def eqCells (j : ℕ) (w : Wit) (c : ℕ) : List ℕ :=
  c :: w.as.filterMap fun
    | .copy d s => if cellJ j d == c then some (cellJ j s) else if cellJ j s == c then some (cellJ j d) else none
    | _ => none

/-- A top-level `MUL` of function `j`, one factor's cell among `cs`, the other's cell satisfying `okO`,
its product's cell satisfying `okP`, all inside the frame. -/
noncomputable def mulBy (j : ℕ) (w : Wit) (cs : List ℕ) (okP okO : ℕ → Bool) : Bool :=
  w.as.any fun
    | .mul d x y => ((cs.contains (cellJ j x) && okO (cellJ j y)) || (cs.contains (cellJ j y) && okO (cellJ j x))) &&
        inFr j (cellJ j d) && inFr j (cellJ j x) && inFr j (cellJ j y) && okP (cellJ j d)
    | _ => false

/-- The products `shiftB` takes: the run's bound `[p]` itself, or a constant `H` above a bounded
product's exponent. -/
noncomputable def shiftHi (j : ℕ) (w : Wit) (hi : Mode.Idx) (pc : ℕ) : Bool :=
  match hi with
  | .ex (.fr p) 0 => pc == p
  | .num H => cellLt j w pc (H + 1)
  | _ => false

/-- **A run over a product scaled by a factor** (F4, F6): `⟨Q·x, 0, [c], 1, d⟩` inside `⟨Q, 0, hi, 1, d⟩`,
the code's `[p] = [c]·[o]` with `[o]` the factor `x`'s word, `[c]` and `[o]` bounded cells, and `hi`
the exponent of `[p]` (F4) or a constant above it (F6). -/
noncomputable def shiftB (j : ℕ) (w : Wit) : Mode.Res → Bool
  | .sub a [b] => match frEx a.hi with
    | some c =>
      a.lo == .num 0 && b.lo == .num 0 && a.S == 1 && b.S == 1 && a.d == b.d &&
        a.q.fp == b.q.fp && a.q.k == b.q.k && cellLt j w c (2 ^ 33) &&
        a.q.bs.any fun be => be.2 == 1 && decide (a.q.bs = Mode.insertBs (be.1, 1) b.q.bs) &&
          mulBy j w (eqCells j w c) (shiftHi j w b.hi) fun o => holdsBase j w o be.1 && cellLt j w o (2 ^ 33)
    | none => false
  | _ => false

/-- Function `j`'s values carried as the exponent tables' base (`Kd.tab`). -/
noncomputable def tabVals (j : ℕ) : List V :=
  carried.filterMap fun c => if c.1 == (coreOf j).name && c.2.2 == .tab then (coreOf j).params[c.2.1]? else none

/-- **Every group below `N` whose side the word `w` is lies in `[lo, hi)`**, every group below `N`
of some side (`B1.sideGroupStart`). -/
noncomputable def sideIn (w : E) (N lo hi : ℕ) : Bool :=
  (List.range N).all fun gi =>
    (List.range B1.nGkrSides).any (fun s => decide (B1.sideGroupStart.getD s 0 ≤ gi) &&
      decide (gi < B1.sideGroupStart.getD (s + 1) 0)) &&
    (List.range B1.nGkrSides).all fun s => !(decide (B1.sideGroupStart.getD s 0 ≤ gi) &&
      decide (gi < B1.sideGroupStart.getD (s + 1) 0) && decide (w = LeanVM.Protocol.Verifier.eOfNat s)) || (decide (lo ≤ gi) && decide (gi < hi))

/-- The code reads the exponent tables' side section at value `y`'s group into a constant `w`
(`[G]·y·g^212`, `G` carried as the tables' base), every group below `N` of side `w` in `[lo, hi)`. -/
noncomputable def sideRead (j : ℕ) (w : Wit) (y : V) (N lo hi : ℕ) : Bool :=
  let as := w.as
  as.any fun
    | .mul P G y' => decide (y' = y) && decide (G ∈ tabVals j) && as.any fun
        | .load S P' off => decide (P' = P) && off == B1.sideTabAt && match constOf as S with
          | some w => sideIn w N lo hi
          | none => false
        | _ => false
    | _ => false

/-- The shape `sideB` reads: `[T]·[q]@r` and `[T]` over `[lo, hi)`, as `(q, r, lo, hi)`. -/
def sideShape (a b : Mode.Rng) : Option (ℕ × ℕ × ℕ × ℕ) :=
  match a.q.bs, b.q.bs, b.lo, b.hi with
  | [(.fr T, 1), (.hp q r, 1)], [(.fr T', 1)], .num lo, .num hi => if T = T' then some (q, r, lo, hi) else none
  | _, _, _, _ => none

/-- **A read guarded by the exponent tables' side section** (F2): `⟨[T]·[q]@r·g^c, 0, 1, 1, 0⟩` inside
`⟨[T], lo, hi, 1, c⟩`, the word `y` a top-level load reads from `[q]·g^r` range checked below `N` and
its side read (`sideRead`). -/
noncomputable def sideB (j : ℕ) (w : Wit) : Mode.Res → Bool
  | .sub a [b] => match sideShape a b with
    | some (q, r, lo, hi) =>
      a.q.fp == 0 && b.q.fp == 0 && b.q.k == 0 && a.lo == .num 0 && a.hi == .num 1 &&
        a.S == 1 && a.d == 0 && b.S == 1 && b.d == a.q.k && decide (2 ≤ q) && decide (q < fsN j) &&
        w.as.any fun
          | .load y p r' => cellJ j p == q && r' == r &&
              match rcBound w.as y with
              | some N => sideRead j w y N lo hi
              | none => false
          | _ => false
    | none => false
  | _ => false

/-- **The `sub` families read off the function's own code**: F4 and F6 (`shiftB`), F2 (`sideB`). -/
noncomputable def subFamB (j : ℕ) (w : Wit) (x : Mode.Res) : Bool := shiftB j w x || sideB j w x

end

end LeanVM.Guest.Res
