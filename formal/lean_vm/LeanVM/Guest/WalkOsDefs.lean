/-
  LeanVM.Guest.WalkOsDefs

  The check that `open_stacked`'s certificate assumes its window table and asks, at each level's
  dispatch into `level_queries`, the walk that level's `level_positions` dispatch decoded, at the
  rate's arm.
-/

module

public import LeanVM.Guest.Glob
public import LeanVM.Guest.B1.Whir.HelperAll
public import LeanVM.Guest.B1.Whir.Loops
public import LeanVM.Guest.B1.Bits.QueryWindowsT
public import LeanVM.Guest.B1.Opening.Interface

/-!
# `open_stacked`'s cuts, checked

Bool checks on the certificates and the core IR (`osOk`). `open_stacked__L{m}` takes the rate's
selector `g^r` (value `0`) and the window table `tabs` (value `10`, `tagTabs`, its certificate's
assumption). Each level matches on the selector for the rate's values (`level_rate`: among them
the squeeze count `squeezes_g = g^S`, a constant per arm), dispatches on it into
`level_positions` (the level's `S` squeezes decoded into windows at `query_win_ptrs·g^posOff`)
and then into `level_queries`, on those window pointers. Each cut before a level's queries hands
on the table and, at each rate's arm `r`, `level_queries`' windows (`lqTag`) on the pointers'
cell, conditional on the selector's cell holding `g^r` (`Check.selTag`). `osTupOk` checks such a
tuple against a witness `(pP, wv, pM, Ss)`: statement `pP < start` is the positions dispatch, its
window pointers value `wv`, its arm `r` a specialization of `lpTable` whose `S = Ss[r]` decodes
cover the tuple's walk (`lpCovers`), its squeeze count the value statement `pM < pP`'s match on
the selector sets to `g^S` in arm `r` (`sqArmOk`); the tuple's pointer cell is `wv`'s; the body
before the cut is atoms, calls, dispatches and matches of atoms (`flatD`).
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir

@[expose] public section

/-- A statement a prefix runs in order: an atom, a call, a conditional call, a dispatch or a
match whose arms are atoms. -/
def flatD : Stmt → Bool
  | .atom _ | .call .. | .callIf .. | .dispatch .. => true
  | .match_ _ arms => arms.all fun a ↦ a.all fun
    | .atom _ => true
    | _ => false
  | _ => false

/-- A statement of a body, by index (a `ret` past its end). -/
def stmtAt (body : List Stmt) (i : ℕ) : Stmt := body.getD i (.ret [])

/-- The decode's numbers a walk of `oqCount odd base n` queries at depth `d` and cap depth `cd`
needs of `sq` squeezes. -/
def lpCovers (sq n odd base d cd : ℕ) : Bool :=
  Nat.ble (oqCount odd base n) (sq * (128 / d)) && Nat.ble 1 (128 / d) &&
    digitsVal (osPowDigits (128 / d)) 1 == 128 / d && Nat.blt 0 sq && Nat.blt sq ordG &&
    queryWindowsShapes.contains (dqwName d cd, d, cd)

/-- An arm of a match sets value `sv` to `g^S`: a constant `g^S` copied into it. -/
def sqArmOk (arm : List Stmt) (sv : V) (S : ℕ) : Bool :=
  arm.any fun
    | .atom (.copy a c) => vEqb a sv && arm.any fun
      | .atom (.const c' x) => vEqb c' c && eEqb x (gpowE S)
      | _ => false
    | _ => false

/-- **A tuple of `open_stacked`'s cut at statement `start`**, by the witness `(pP, wv, pM, Ss)`:
`level_queries`' windows at `g^n` (`lqTag n odd base d cd`) conditional on arm `r`, on value
`wv`'s cell and the selector's; statement `pP < start` the dispatch on the selector into the
positions, its window pointers `wv`, the window table `10`, at most four arms, arm `r` a
specialization of `lpTable` covering the walk in `S = Ss[r]` squeezes, its squeeze count set to
`g^S` by arm `r` of statement `pM < pP`, a match on the selector. -/
def osTupOk (C : Cert) (body : List Stmt) (start : ℕ) (w : ℕ × ℕ × ℕ × List ℕ) (t : ℕ × List ℕ) : Bool :=
  let T := selBase t.1
  let r := selArm t.1
  let n := lqN T
  let base := walkKind (lqWalk T) - 2
  let odd := walkOdd (lqWalk T)
  let d := walkD (lqWalk T)
  let cd := walkCd (lqWalk T)
  let S := w.2.2.2.getD r 0
  t.1 == selTag (lqTag n odd base d cd) r && Nat.blt r 4 && Nat.ble 2 (walkKind (lqWalk T)) &&
    Nat.blt odd 2 && Nat.blt cd 64 && Nat.blt d 64 && Nat.blt n 992 && (odd == 0 || base == 1) &&
    t.2 == [C.locs.getD w.2.1 0, C.locs.getD 0 0] && Nat.blt w.1 start && Nat.blt w.2.2.1 w.1 &&
    match stmtAt body w.1, stmtAt body w.2.2.1 with
    | .dispatch x names args _, .match_ y arms =>
        x == .n 0 && y == .n 0 && Nat.ble names.length 4 && Nat.ble arms.length 4 && args.length == 10 &&
          args.getD 8 (.n 0) == .n 10 && args.getD 7 (.n 0) == .n w.2.1 &&
          sqArmOk (arms.getD r []) (args.getD 9 (.n 0)) S &&
          lpTable.any fun e ↦ e.1 == names.getD r "" && e.2.2.1 == d && e.2.2.2 == cd &&
            lpCovers S n odd base d cd
    | _, _ => false

/-- The window table's tuple: `tagTabs` on `tabs`' cell. -/
def osTabsTup (C : Cert) : ℕ × List ℕ := (tagTabs, [C.locs.getD 10 0])

/-- An `open_stacked` cut: no bound, the body before it of flat statements, its tuples the window
table's or the levels' walks (`osTupOk`, by one of the witnesses `W`). -/
def osCutOk (C : Cert) (body : List Stmt) (W : List (ℕ × ℕ × ℕ × List ℕ)) (cut : Cut) : Bool :=
  cut.known.isEmpty && cut.knownIf.isEmpty && (body.take cut.start).all flatD &&
    cut.sems.all fun t ↦ t == osTabsTup C || W.any fun w ↦ osTupOk C body cut.start w t

/-- **`open_stacked`'s certificate** (function `j`, witnesses `W`): the window table assumed,
every cut an `osCutOk`. -/
noncomputable def osOk (j : ℕ) (W : List (ℕ × ℕ × ℕ × List ℕ)) : Bool :=
  (certOf j).sem == [osTabsTup (certOf j)] &&
    (certOf j).cuts.all (osCutOk (certOf j) (coreOf j).body W)

end
end LeanVM.Guest.End
