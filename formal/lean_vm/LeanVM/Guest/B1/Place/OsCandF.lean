/-
  LeanVM.Guest.B1.Place.OsCandF

  A configuration's facts the placed lift of f128's `open_stacked` uses, as one decidable
  proposition.
-/

module

public import LeanVM.Guest.B1.Place.OsCallV
public import LeanVM.Guest.B1.Place.OsMean

/-!
# The placed lift's facts, decided

`PlaceOk c`: the body has no `frameAddr` and its head no call; each level's calls before its
squeezes and between them and its queries are named callees (`osNamedB`: plain calls, their
names in `osKindTable`), its decoder, squeeze loop and `opening_queries` names are not, its
window pointers' slice ends by the next level's (`query_win_ptrs` from `posOff`, `squeezes · 128 /
depth` words); the closing rounds' and `fold_final_msg`'s calls are named, then come the non-final
levels' residual loops (`osResCall`), unnamed and pure. `Place/OsCandF{0..3}.lean` decide it for
the 28 candidates.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir

@[expose] public section

/-- A named call: plain, its name in `osKindTable`. -/
def osNamedB (x : Option V × String × List V × List V) : Bool :=
  x.1.isNone && (osKindOf x.2.1).isSome

/-- **The placed lift's facts of a configuration.** -/
def PlaceOk (c : OsCfg) : Prop :=
  (osBodyA c).filterMap Stmt.addrS = [] ∧
  (osHead c).1.filterMap Stmt.callS = [] ∧
  (∀ l < c.levels.length,
    ((lvA c l (osLvAt c l) (osStAt c l)).filterMap Stmt.callS).all osNamedB = true ∧
    ((lvH c l (osLvAt c l) (osStAt c l)).1.filterMap Stmt.callS).all osNamedB = true ∧
    osKindOf (osDecCall c l).2.1 = none ∧ osKindOf (c.sqLoop l) = none ∧
    osKindOf (osQueriesName c l (osLvAt c l)) = none ∧
    (osLvAt c l).posOff + (osLvAt c l).squeezes * (128 / (osLvAt c l).depth) ≤
      (if l + 1 < c.levels.length then (osLvAt c (l + 1)).posOff else c.posLen)) ∧
  (((osRest c).filterMap Stmt.callS).take (c.yrLog + 1)).all osNamedB = true ∧
  ((osRest c).filterMap Stmt.callS).drop (c.yrLog + 1) = (List.range c.yrLevel).map (osResCall c) ∧
  (∀ l < c.yrLevel, osKindOf (c.resLoop l) = none ∧
    Stmt.pureList [c.resLoop l] (resLoopBody l (osLvAt c l) (c.resLoop l)) = true)

instance (c : OsCfg) : Decidable (PlaceOk c) := by
  unfold PlaceOk; infer_instance

end
end LeanVM.Guest.B1
