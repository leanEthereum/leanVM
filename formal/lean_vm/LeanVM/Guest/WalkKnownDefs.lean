/-
  LeanVM.Guest.WalkKnownDefs

  The decided checks of the walks' certificates (`loopOk`, `mainOk`, `lqOk`): the cut obligations
  of `opening_queries`' specializations and loops and of `level_queries` are of the forms B1 proves
  on the templates.
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

/-- A path-window bound the walk hands on: on the cell of a window pointer `v` the prefix has
loaded (`v.2` statements suffice), path window `m.2.1 < pwN pd`, bound at least its width's. -/
def winTripOk (C : Cert) (pd : ℕ) (src : List (ℕ × ℕ)) (start : ℕ) (m : ℕ × ℕ × ℕ) : Bool :=
  src.any fun v ↦ m.1 == C.locs.getD v.1 0 && Nat.ble v.2 start && Nat.blt m.2.1 (pwN pd) &&
    Nat.ble (2 ^ pwW pd m.2.1) m.2.2

/-- A loop's cut: no plain bound, its window bounds on the loaded pointers `src`, its tuples the
walk's tail `[qptrs, xv, N]` once `tl` statements hold. -/
def loopCutOk (C : Cert) (tag pd : ℕ) (src : List (ℕ × ℕ)) (xv tl : ℕ) (c : Cut) : Bool :=
  c.known.isEmpty && c.knownIf.all (winTripOk C pd src c.start) &&
    c.sems.all fun t ↦ t == (tag, [C.locs.getD oqQp 0, C.locs.getD xv 0, C.locs.getD oqN 0]) &&
      Nat.ble tl c.start

/-- A loop's certificate: the walk `tag` on `[qptrs, x, N]` and `x ≠ N` assumed, every cut a
`loopCutOk`. -/
def loopOk (C : Cert) (tag pd : ℕ) (src : List (ℕ × ℕ)) (xv tl : ℕ) : Bool :=
  C.sem == [(tag, [C.locs.getD oqQp 0, C.locs.getD oqX 0, C.locs.getD oqN 0]),
    (tagNe, [C.locs.getD oqX 0, C.locs.getD oqN 0])] && C.cuts.all (loopCutOk C tag pd src xv tl)

/-- A bound of a level-0 specialization read twice: path window `i` of the pointer
`qptrs[g^0]` (`memTwice 0 i` on `qptrs`' cell), which its odd first query reads under its branch
on `odd_g`. -/
def twiceOk (C : Cert) (pd : ℕ) (m : ℕ × ℕ × ℕ) : Bool :=
  m.1 == C.locs.getD oqMQp 0 && Nat.ble (2 ^ 32) m.2.1 && m.2.1 % 2 ^ 32 == 0 &&
    Nat.blt (m.2.1 / 2 ^ 32 - 1) (pwN pd) && Nat.ble (2 ^ pwW pd (m.2.1 / 2 ^ 32 - 1)) m.2.2

/-- A specialization's cut: no plain bound; at level 0 the odd query's bounds read twice
(`twiceOk`), deeper none; its tuples the loop call's walk on `[qptrs', x, N]`, conditional on
`x = 1`, `qptrs' = qptrs·odd_g` at level 0 (past the start) and `qptrs` deeper. -/
def mainCutOk (C : Cert) (s : Oq) (c : Cut) : Bool :=
  c.known.isEmpty && (s.base == 1 || c.knownIf.isEmpty) && c.knownIf.all (twiceOk C s.pd) &&
    c.sems.all fun t ↦ t.1 == impTag (oqTag (if s.base = 1 then 1 else 0) 0 s.pd) 1 1 &&
      t.2.length == 3 && t.2.getD 2 0 == C.locs.getD oqMN 0 &&
      (if s.base = 1 then t.2.getD 0 0 == C.locs.getD (oqMK s - 1) 0 && Nat.ble (oqMainA s).length c.start
       else t.2.getD 0 0 == C.locs.getD oqMQp 0)

/-- A specialization's precondition: deeper the walk from `1` on `[qptrs, N]`, at level 0
`OqStartP` for both `odd`'s on `[qptrs, N, odd_g]` and `odd_g ∈ {1, g}`. -/
def mainSem (C : Cert) (s : Oq) : List (ℕ × List ℕ) :=
  if s.base = 1 then
    [(oqTag 3 0 s.pd, [C.locs.getD oqMQp 0, C.locs.getD oqMN 0, C.locs.getD oqMOdd 0]),
      (oqTag 3 1 s.pd, [C.locs.getD oqMQp 0, C.locs.getD oqMN 0, C.locs.getD oqMOdd 0]),
      (tagOdd, [C.locs.getD oqMOdd 0])]
  else [(oqTag 2 0 s.pd, [C.locs.getD oqMQp 0, C.locs.getD oqMN 0])]

/-- A specialization's certificate: `mainSem` assumed, every cut a `mainCutOk`. -/
def mainOk (C : Cert) (s : Oq) : Bool :=
  C.sem == mainSem C s && C.cuts.all (mainCutOk C s)

/-- A cut of `level_queries`: no bound, its tuples those of its call of `opening_queries` on the
window pointers' cell `7`: the specialization's walk for `odd`, conditional on `n_iters_g`'s cell
holding the one-limb word `g^n`; at level 0 also `OqStartP` for the other `odd`, conditional on
`odd_g`'s holding `g^odd` (vacuous), and `odd_g ∈ {1, g}` on the same condition. -/
def lqCutOk (n odd base pd : ℕ) (c : Cut) : Bool :=
  c.known.isEmpty && c.knownIf.isEmpty && c.sems.all fun t ↦
    (t.1 == impTag (oqTag (2 + base) odd pd) 1 (impImm t.1) && decide (K.ofBits (impImm t.1) = gpowK n) &&
      t.2.length == (if base = 1 then 3 else 2) && t.2.getD 0 0 == 7) ||
    (base == 1 && t.1 == impTag (oqTag 3 (1 - odd) pd) 2 (impImm t.1) &&
      decide (K.ofBits (impImm t.1) = gpowK odd) && t.2.length == 3 && t.2.getD 0 0 == 7) ||
    (base == 1 && t.1 == impTag tagOdd 0 (impImm t.1) && decide (K.ofBits (impImm t.1) = gpowK odd) &&
      t.2.length == 1)

/-- `level_queries`' certificate: its windows (`lqTag`) on `win_ptrs` (cell `7`) assumed, a query
(`odd = 1` or `n ≥ 1`; `odd = 0` deeper), every cut an `lqCutOk` at the path depth `d - cd`. -/
def lqOk (C : Cert) (n odd base d cd : ℕ) : Bool :=
  C.sem == [(lqTag n odd base d cd, [7])] && (if base = 1 then odd == 1 || Nat.ble 1 n else odd == 0) &&
    C.cuts.all (lqCutOk n odd base (d - cd))

/-! ## By template -/

/-- A deeper loop's certificate (`oqLoop0T s`). -/
noncomputable def loop0Ok (j : ℕ) (s : Oq) : Bool :=
  loopOk (certOf j) (oqTag 0 0 s.pd) s.pd [(13, 4)] (oqG0 s + 4) (oqLoop0A s).length

/-- A level-0 loop's certificate (`oqLoop1T s`). -/
noncomputable def loop1Ok (j : ℕ) (s : Oq) : Bool :=
  loopOk (certOf j) (oqTag 1 0 s.pd) s.pd
    [(14, 5), (oqE1 s + 1,
      (oqQueryT s (.n 13) (.n 14) (.n oqCap) (.n oqFlags) (.n oqCoefs) (.n oqHs) 15 true 0).length + 7)]
    (oqG1 s + 4) (oqLoop1A s).length

/-- A specialization's certificate (`oqMainT s`). -/
noncomputable def mainOkS (j : ℕ) (s : Oq) : Bool := mainOk (certOf j) s

end
end LeanVM.Guest.End
