/-
  LeanVM.Guest.Count.VsOsDefs

  `open_stacked`'s words at an arm by the search tree's lookups (`osCF`), which the kernel
  evaluates one module per arm (`Count/VsOs*`), with its callees' words bounds (`wSBos`) and their
  checks (`leafOkB`). Few imports, so that each module stays small.
-/

module

public import LeanVM.Guest.Count.Fast
public import LeanVM.Guest.Count.VsOsTab
public import LeanVM.Guest.B1.Place.OsSpec

/-!
# `open_stacked`'s callees' words bounds

`wSBos f`: `wSB f`, but for the callees whose words certificates read their arguments' exponents
(`level_positions`, `level_residual`), `osRtTab`'s entry of `f`'s core index (`Count/VsOsTab.lean`,
generated). `osAsgs m f`: the exponents arm `m` passes `f` at the arguments its certificate reads,
one assignment per rate and level whose row names `f` (`B1.osArgsOk`). `statAtB pre b asg B`: a
certificate's preconditions hold and its bound is at most `B` at the assignment `asg`. `leafOkB m f`:
`f`'s certificate within `wSBos f` at every assignment, which `Count/VsOsLeaf.lean` proves sound.
-/

namespace LeanVM.Guest.Count

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest LeanVM.Guest.Data LeanVM.Guest.B1.Whir

@[expose] public section

/-- The value of key `k` in a list of pairs. -/
def alook (k : ℕ) : List (ℕ × ℕ) → Option ℕ
  | [] => none
  | q :: l => if q.1 = k then some q.2 else alook k l

/-- **`open_stacked`'s callees' words bounds**: `wSB`, but `osRtTab`'s bound for the callees it lists by core
index. -/
noncomputable def wSBos (f : String) : ℕ :=
  match wNameIdx f with
  | some j => (alook j osRtTab).getD (wSBJ j)
  | none => wSB f

/-- An affine bound at the exponents `asg` gives its arguments. -/
def affAt (asg : List (ℕ × ℕ)) (b : Aff) : ℕ := b.c + (b.cs.map fun q => q.2 * (alook q.1 asg).getD 0).sum

/-- A certificate's preconditions hold, and its bound is at most `B`, on arguments `g^e` at the pairs `(k, e)` of
`asg`. -/
def statAtB (pre : List (ℕ × ℕ)) (b : Aff) (asg : List (ℕ × ℕ)) (B : ℕ) : Bool :=
  asg.all (fun q => decide (q.2 < 2 ^ 64 - 1)) &&
    pre.all (fun q => match alook q.1 asg with
      | some e => preLt q.2 e
      | none => false) &&
    b.cs.all (fun q => (alook q.1 asg).isSome) && decide (affAt asg b ≤ B)

/-- The exponents arm `m` can pass its callee `f` at the arguments `B1.osArgsOk` constrains, one assignment per
rate and level whose row names `f`; any other callee, none. -/
def osAsgs (m : ℕ) (f : String) : List (List (ℕ × ℕ)) :=
  if f ∈ B1.osPosNames m then
    (List.range ligNRates).flatMap fun r ↦ (List.range (osNLevels m)).filterMap fun l ↦
      if f = osPositionsName (osLvR m r l) then some [(9, (osLvR m r l).squeezes)] else none
  else if f ∈ B1.osResNames m then
    (List.range ligNRates).flatMap fun r ↦ (List.range (osCfg m).yrLevel).filterMap fun l ↦
      if f = osResidualName (osLvR m 0 l) then
        some [(4, (osLvR m r l).queries / resBatch), (5, (osLvR m r l).queries % resBatch)]
      else none
  else [[]]

/-- Callee `f` of arm `m`: core function `wIdx f` is `f`, its certificate within `wSBos f` at every assignment. -/
noncomputable def leafOkB (m : ℕ) (f : String) : Bool :=
  wNameB (wIdx f) f && match wcertJ (wIdx f) with
    | .stat pre b _ => (osAsgs m f).all fun a ↦ statAtB pre b a (wSBos f)
    | _ => false

/-- `open_stacked`'s words at the arm `m`, the largest over the rates, its name spelled by `natStr`, by the search
tree's lookups. -/
noncomputable def osCF (m : ℕ) : ℕ :=
  ((List.range ligNRates).map fun ri ↦ B1.osBos fsFast wSBos ("open_stacked__L" ++ natStr m) (osCfgR m ri)).foldl
    max 0

end
end LeanVM.Guest.Count
