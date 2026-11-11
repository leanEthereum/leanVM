/-
  LeanVM.Guest.WalkKnownDefs

  The decided checks of the walks' certificates (`loopOk`, `mainOk`, `wpOk`): the cut obligations of
  `opening_queries`' specializations and loops and of `walk_path`'s are of the forms B1 proves on
  the templates.
-/

module

public import LeanVM.Guest.Glob
public import LeanVM.Guest.B1.Opening.QueriesT

/-!
# The walks' certificates, checked

A light module of Bool checks on the certificates (`certOf`) and whir's templates' numbers, so a
kernel check `loopOk (certOf j) … = true` imports neither the proofs nor the checker's
certificates of the windows (`WalkKnown.lean` reads them).
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check LeanVM.Guest.B1

@[expose] public section

/-- A window bound the walk hands on: on the cell of a window pointer `v` the prefix has loaded
(`v.2` statements suffice), window `m.2.1 < qwN`, bound at least its width's. -/
def winTripOk (C : Cert) (d cd : ℕ) (src : List (ℕ × ℕ)) (start : ℕ) (m : ℕ × ℕ × ℕ) : Bool :=
  src.any fun v ↦ m.1 == C.locs.getD v.1 0 && Nat.ble v.2 start && Nat.blt m.2.1 (qwN d cd) &&
    Nat.ble (2 ^ (qwWin d cd m.2.1).2) m.2.2

/-- A tuple a cut hands to a call of `walk_path`: `WinsAt` (`winsTag d cd`) on the cell of a window
pointer `v` the prefix has loaded (`v.2` statements suffice). -/
def winSemOk (C : Cert) (d cd : ℕ) (src : List (ℕ × ℕ)) (start : ℕ) (t : ℕ × List ℕ) : Bool :=
  src.any fun v ↦ t == (winsTag d cd, [C.locs.getD v.1 0]) && Nat.ble v.2 start

/-- A loop's cut: no plain bound, its window bounds and `walk_path`'s tuples of the loaded pointers
`src`, its other tuples the walk's tail `[2, xv, 1]` once `tl` statements hold. -/
def loopCutOk (C : Cert) (tag d cd : ℕ) (src : List (ℕ × ℕ)) (xv tl : ℕ) (c : Cut) : Bool :=
  c.known.isEmpty && c.knownIf.all (winTripOk C d cd src c.start) &&
    c.sems.all fun t ↦ (t == (tag, [C.locs.getD 2 0, C.locs.getD xv 0, C.locs.getD 1 0]) &&
      Nat.ble tl c.start) || winSemOk C d cd src c.start t

/-- A loop's certificate: the walk `tag` on `[2, 0, 1]` and `0 ≠ 1` assumed, every cut a
`loopCutOk`. -/
def loopOk (C : Cert) (tag d cd : ℕ) (src : List (ℕ × ℕ)) (xv tl : ℕ) : Bool :=
  C.sem == [(tag, [C.locs.getD 2 0, C.locs.getD 0 0, C.locs.getD 1 0]),
    (tagNe, [C.locs.getD 0 0, C.locs.getD 1 0])] && C.cuts.all (loopCutOk C tag d cd src xv tl)

/-- A specialization's cut: no plain bound, its window bounds and `walk_path`'s tuple of an odd
count's first query (`src`), its other tuples the loop call's walk `tagW` on `[4, x, 6]`, conditional
on `x = 1`. -/
def mainCutOk (C : Cert) (tagW d cd : ℕ) (src : List (ℕ × ℕ)) (c : Cut) : Bool :=
  c.known.isEmpty && c.knownIf.all (winTripOk C d cd src c.start) &&
    c.sems.all fun t ↦ (t.1 == impTag tagW 1 1 && t.2.length == 3 &&
      t.2.getD 0 0 == C.locs.getD 4 0 && t.2.getD 2 0 == C.locs.getD 6 0) ||
      winSemOk C d cd src c.start t

/-- A specialization's certificate: `OqMainWins` (`tagM`) on `[4, 6]` assumed, every cut a
`mainCutOk`. -/
def mainOk (C : Cert) (tagM tagW d cd : ℕ) (src : List (ℕ × ℕ)) : Bool :=
  C.sem == [(tagM, [C.locs.getD 4 0, C.locs.getD 6 0])] && C.cuts.all (mainCutOk C tagW d cd src)

/-- A cut of `walk_path`: no plain bound, no tuple, its window bounds those of its argument `wins`
(value `2`, from the function's start). -/
def wpCutOk (C : Cert) (d cd : ℕ) (c : Cut) : Bool :=
  c.known.isEmpty && c.knownIf.all (winTripOk C d cd [(2, 0)] c.start) && c.sems.isEmpty

/-- `walk_path`'s certificate: `WinsAt` (`winsTag d cd`) on `wins` (value `2`) assumed, every cut a
`wpCutOk`. -/
def wpOk (C : Cert) (d cd : ℕ) : Bool :=
  C.sem == [(winsTag d cd, [C.locs.getD 2 0])] && C.cuts.all (wpCutOk C d cd)

/-- A cut of `level_queries`: no bound, its tuples the walk `tW` (`OqMainWins`) of its call of
`opening_queries` on the window pointers' cell `3` and `n_iters_g`'s, conditional on the latter
holding the one-limb word `g^n` (`impTag tW 1 l`). -/
def lqCutOk (tW n : ℕ) (c : Cut) : Bool :=
  c.known.isEmpty && c.knownIf.isEmpty && c.sems.all fun t ↦
    t.1 == impTag tW 1 (impImm t.1) && decide (K.ofBits (impImm t.1) = gpowK n) &&
      t.2.length == 2 && t.2.getD 0 0 == 3

/-- `level_queries`' certificate: its windows (`lqTag`) on `win_ptrs` (cell `3`) assumed, every cut
an `lqCutOk`. -/
def lqOk (C : Cert) (n odd base d cd : ℕ) : Bool :=
  C.sem == [(lqTag n odd base d cd, [3])] && C.cuts.all (lqCutOk (walkTag (2 + base) odd d cd) n)

/-! ## By template -/

/-- A deeper loop's certificate (`oqLoop0T s`; its specialization's `odd` is `0`). -/
noncomputable def loop0Ok (j : ℕ) (s : Oq) : Bool :=
  loopOk (certOf j) (walkTag 0 0 (s.pd + s.cd) s.cd) (s.pd + s.cd) s.cd [(9, 2)] (oqC0 s + 9)
    (oqLoop0A s "").length

/-- A level-0 loop's certificate (`oqLoop1T s odd`). -/
noncomputable def loop1Ok (j odd : ℕ) (s : Oq) : Bool :=
  loopOk (certOf j) (walkTag 1 odd (s.pd + s.cd) s.cd) (s.pd + s.cd) s.cd
    [(10, 3), (oqE1 s, (oqQueryT s (.n 10) (.n 3) (.n 4) (.n 5) 11 true 0 "").length + 4)]
    (oqC1 s + 11) (oqLoop1A s odd "").length

/-- `walk_path__L{pd}_L{cd}`'s certificate (`wpBodyT ⟨_, _, pd, cd⟩`). -/
noncomputable def wpOkJ (j pd cd : ℕ) : Bool := wpOk (certOf j) (pd + cd) cd

/-- A specialization's certificate (`oqMainT s odd`). -/
noncomputable def mainOkS (j odd : ℕ) (s : Oq) : Bool :=
  mainOk (certOf j) (walkTag (2 + s.base) odd (s.pd + s.cd) s.cd)
    (walkTag (if s.base = 1 then 1 else 0) odd (s.pd + s.cd) s.cd) (s.pd + s.cd) s.cd
    (if odd = 1 then [(12, 6)] else [])

end
end LeanVM.Guest.End
