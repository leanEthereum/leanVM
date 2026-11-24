/-
  LeanVM.Guest.CoreMode.Fam.FamDefs

  The shared checks of the residual families read off a function's own code: the atoms on every
  returning path, the guest's constant powers of `g`, and the exponent bounds its range checks and
  selectors put on frame cells.
-/

module

public import LeanVM.Guest.CoreMode.Fam.SelDefs
public import LeanVM.Guest.Data.Pows
public import LeanVM.Guest.CoreMode.Fam.CarryDefs
public import LeanVM.Guest.ExpTables
public import LeanVM.Guest.Memory.StaticCut

/-!
# The families' shared checks

`topAtoms ss`: the top-level atoms of a block before its first statement that may return; each is
on every returning path of the block. `powOf w` (`CarryDefs.lean`): the exponent `e` of a word `w = g^e`
the guest's table of powers names (`Data.powTree`). `rcBound as v`: a range check of `as` on value `v` against
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

/-- The exponent of a word `g^z`: `1`'s, or one the guest's powers name (`powOf`). -/
noncomputable def powOf1 (c : E) : Option ℕ := if c.limb 1 = 0 ∧ c.limb 0 = 1 then some 0 else powOf c

/-- The top-level selectors of a block before its first statement that may return: each one's value
and count of arms. -/
noncomputable def topSels : List Stmt → List (V × ℕ)
  | [] => []
  | s :: ss => (match selOf s with
      | some p => [p]
      | none => []) ++ (if Memory.noRetR s then topSels ss else [])

/-- **A family's witness**: atoms and selectors of a function's own code it reads, each on every
returning path, so a family's check scans them, not the whole body. -/
structure Wit where
  as : List Atom
  ss : List (V × ℕ)

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

end

end LeanVM.Guest.Res
