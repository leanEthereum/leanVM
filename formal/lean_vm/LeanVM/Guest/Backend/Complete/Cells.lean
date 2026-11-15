/-
  LeanVM.Guest.Backend.Complete.Cells

  The cells of its own frame a placed function's instructions name, and the placements whose range
  check temporaries have cells of their own (`TmpsApart`).
-/

module

public import LeanVM.Guest.Backend.Place
public import LeanVM.Guest.Backend.Sound.Ops
public import LeanVM.Guest.Memory.Fresh

/-!
# Cells

`opCells` lists the cells of this frame an instruction names (a `KECCAK` names its runs; the
destination of `mulNextFrame` is a cell of the next frame and is not listed); `locBase` is the
cell a place is read from.

**Temporaries apart.** The words of a range check's temporaries are chosen last, from the final
memory (`Memory/Retemp.lean`), so the completeness proof needs their cells to be theirs alone:
`TmpsApart tf pf` says the function's temporaries are fresh (`Fn.freshB`), each is placed in a
cell, no other value the body or the parameters name is placed at a temporary's cell, and each
temporary's cell is named by exactly one instruction of the placed body (its own `DEREF`).
`tmpsApartB` decides it.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- The cells of this frame an instruction names. -/
def opCells : LOp → List Cell
  | .mulNextFrame a b _ => [a, b]
  | .set o _ => [o]
  | .xor a b c => [a, b, c]
  | .mul a b c => [a, b, c]
  | .deref o1 _ o3 _ => [o1, o3]
  | .jump oc od of => [oc, od, of]
  | .slot x _ dst => [x, dst]
  | .keccak m0 m1 m2 m3 tail b8 cap out _ _ oc =>
      [m0, m1, m2, m3, b8] ++ (List.range 4).map (tail + ·) ++ (List.range 4).map (cap + ·) ++
        (List.range oc.cellCount).map (out + ·)

/-- The cell a place is read from. -/
def locBase : Loc → Cell
  | .cell n => n
  | .shifted n _ => n

/-- A value's cell: `.shifted` and unplaced values have none. -/
def cellP (locs : VMap Loc) (v : V) : Option Cell :=
  match locs[v]? with
  | some (.cell n) => some n
  | _ => none

/-- The cells of the temporaries, as a set. -/
def tmpCellSet (locs : VMap Loc) (ts : List V) : NMap Unit :=
  ts.foldl (fun m t => match cellP locs t with
    | some n => m.insert n ()
    | none => m) {}

/-- How many times the instructions name each cell of the set. -/
def cellCounts (set : NMap Unit) (ops : List LOp) : NMap ℕ :=
  ops.foldl (fun m o => (opCells o).foldl (fun m c =>
    if set.contains c then m.insert c ((m.get? c).getD 0 + 1) else m) m) {}

/-- **Temporaries apart, decided.** -/
def tmpsApartB (tf : TracedFn) (pf : Placed) : Bool :=
  let ts := Stmt.tmpsList tf.core.body
  let set := tmpCellSet pf.locs ts
  let counts := cellCounts set (blockOps pf.fn.body 0)
  tf.core.freshB &&
    ts.all (fun t => (cellP pf.locs t).isSome) &&
    (Stmt.usesList tf.core.body ++ tf.core.params).all (fun v =>
      match pf.locs[v]? with
      | some l => !set.contains (locBase l)
      | none => true) &&
    ts.all (fun t => match cellP pf.locs t with
      | some n => counts.get? n == some 1
      | none => false)

/-- **The temporaries of a placed function have cells of their own.** -/
def TmpsApart (tf : TracedFn) (pf : Placed) : Prop := tmpsApartB tf pf = true

end
end LeanVM.Guest.Backend.Complete
