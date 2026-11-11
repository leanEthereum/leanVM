/-
  LeanVM.Guest.WalkOsDefs

  The check that `open_stacked`'s certificate's cuts ask, at each level's dispatch into
  `level_queries`, the walk that level's `level_positions` dispatch decoded, at the rate's arm.
-/

module

public import LeanVM.Guest.Glob
public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.B1.Whir.Loops
public import LeanVM.Guest.B1.Whir.Template
public import LeanVM.Guest.B1.Opening.Meaning
public import LeanVM.Guest.B1.Bits.QueryWindowsT

/-!
# `open_stacked`'s cuts, checked

A light module of Bool checks on the certificates and the core IR (`osOk`), so their kernel checks
import no proof. `open_stacked__L{m}` dispatches on the rate's selector `g^r` (value `0`) into
`level_positions` (the level's squeezes decoded into windows at `query_win_ptrs·g^posOff`) and then
into `level_queries`, on those window pointers. Each cut before a level's queries hands on, at each
rate's arm `r`, `level_queries`' windows (`lqTag`) on the pointers' cell, conditional on the
selector's cell holding `g^r` (`Check.selTag`). `osTupOk` checks such a tuple against a witness
`(pP, wv)`: statement `pP < start` is the positions dispatch, its window pointers value `wv`, its
arm `r` a `level_positions` specialization of `lpTab` whose decodes cover the tuple's walk; the
tuple's pointer cell is `wv`'s (the queries' pointers, recomputed, share it); the body before the
cut is atoms, calls and dispatches (`flatD`), and holds the window table (`osWinTabs` from
statement `hw`).
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir

@[expose] public section

/-- A statement a prefix runs in order: an atom, a call, a conditional call or a dispatch. -/
def flatD : Stmt → Bool
  | .atom _ | .call .. | .callIf .. | .dispatch .. => true
  | _ => false

/-- A statement of a body, by index (a `ret` past its end). -/
def stmtAt (body : List Stmt) (i : ℕ) : Stmt := body.getD i (.ret [])

/-- The decode's numbers a walk of `oqCount odd base n` queries at depth `d` and cap depth `cd`
needs of `sq` squeezes. -/
def lpCovers (sq n odd base d cd : ℕ) : Bool :=
  Nat.ble (oqCount odd base n) (sq * (192 / d)) && Nat.ble 1 (192 / d) &&
    digitsVal (osPowDigits (192 / d)) 1 == 192 / d && Nat.blt 0 sq && Nat.blt sq ordG &&
    queryWindowsShapes.contains ("decode_query_windows__L" ++ natStr d ++ "_L" ++ natStr cd, d, cd)

/-- **A tuple of `open_stacked`'s cut at statement `start`**, by the witness `(pP, wv)` and the
specializations `lp` of `level_positions` (name, squeezes, depth, cap depth, loop):
`level_queries`' windows at `g^n` (`lqTag n odd base d cd`) conditional on arm `r`, on value
`wv`'s cell and the selector's; statement `pP < start` the dispatch on the selector into the
positions, its window pointers `wv`, the window table `28` (`osWin`), at most four arms, arm `r`
a specialization covering the walk. -/
def osTupOk (lp : List (String × ℕ × ℕ × ℕ × String)) (C : Cert) (body : List Stmt) (start : ℕ)
    (w : ℕ × ℕ) (t : ℕ × List ℕ) : Bool :=
  let T := selBase t.1
  let r := selArm t.1
  let n := lqN T
  let base := walkKind (lqWalk T) - 2
  let odd := walkOdd (lqWalk T)
  let d := walkD (lqWalk T)
  let cd := walkCd (lqWalk T)
  t.1 == selTag (lqTag n odd base d cd) r && Nat.blt r 4 && Nat.ble 2 (walkKind (lqWalk T)) &&
    Nat.blt odd 2 && Nat.blt cd 64 && Nat.blt d 64 && Nat.blt n 992 && (odd == 0 || base == 1) &&
    t.2 == [C.locs.getD w.2 0, C.locs.getD 0 0] && Nat.blt w.1 start &&
    match stmtAt body w.1 with
    | .dispatch x names args _ =>
        x == .n 0 && Nat.ble names.length 4 && args.length == 8 && args.getD 7 (.n 0) == .n 28 &&
          args.getD 6 (.n 0) == .n w.2 &&
          lp.any fun e ↦ e.1 == names.getD r "" && e.2.2.1 == d && e.2.2.2.1 == cd &&
            lpCovers e.2.1 n odd base d cd
    | _ => false

/-- An `open_stacked` cut: no bound, the body before it of flat statements holding the window
table from `hw`, its tuples the levels' walks (`osTupOk`, by one of the witnesses `W`). -/
noncomputable def osCutOk (lp : List (String × ℕ × ℕ × ℕ × String)) (C : Cert) (body : List Stmt)
    (W : List (ℕ × ℕ)) (hw : ℕ) (cut : Cut) : Bool :=
  cut.known.isEmpty && cut.knownIf.isEmpty && (body.take cut.start).all flatD &&
    (cut.sems.isEmpty || (Nat.ble (hw + osWinTabs.length) cut.start &&
      stmtsEqb ((body.drop hw).take osWinTabs.length) osWinTabs)) &&
    cut.sems.all fun t ↦ W.any fun w ↦ osTupOk lp C body cut.start w t

/-- **`open_stacked`'s certificate** (function `j`, witnesses `W`, the window table from `hw`):
every cut an `osCutOk`. -/
noncomputable def osOk (lp : List (String × ℕ × ℕ × ℕ × String)) (j : ℕ)
    (W : List (ℕ × ℕ)) (hw : ℕ) : Bool :=
  (certOf j).cuts.all (osCutOk lp (certOf j) (coreOf j).body W hw)

end
end LeanVM.Guest.End
