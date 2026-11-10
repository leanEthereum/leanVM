/-
  LeanVM.Guest.B1.Place.OsCandF

  A configuration's facts the placed lift of f128's `open_stacked` uses, as one decidable
  proposition.
-/

module

public import LeanVM.Guest.B1.Place.OsCallV
public import LeanVM.Guest.B1.Place.OsMean
public import LeanVM.Guest.B1.Place.OsHonest
public import LeanVM.Guest.B1.Bits.QueryWindowsAtAll

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

/-- **A level's numeric facts** the lift uses: its squeezes, its decoder's and its
`opening_queries`' shapes, its slices of the buffers. -/
def LvStatic (c : OsCfg) (l : ℕ) : Prop :=
  let lv := osLvAt c l
  1 ≤ lv.squeezes ∧ lv.squeezes < ordG ∧ lv.squeezes ≤ c.maxSq ∧ 1 ≤ 128 / lv.depth ∧
  digitsVal (osPowDigits (128 / lv.depth)) 1 = 128 / lv.depth ∧ lv.posOff < u128Bound ∧
  (sqDecName lv, lv.depth, lv.capDepth) ∈ queryWindowsShapes ∧
  (oqEntry (osQueriesName c l lv)).map (·.1) = some (osQueriesName c l lv) ∧
  (oqS c l).pd + (oqS c l).cd = lv.depth ∧ (oqS c l).cd = lv.capDepth ∧ 1 ≤ (oqS c l).cd ∧
  oqN c l + 1 < ordG ∧ oqQ c l ≤ lv.squeezes * (128 / lv.depth) ∧
  lv.foldsOff + (oqS c l).folds ≤ c.nFolds ∧
  (oqS c l).final = (if l = c.yrLevel then 1 else 0) ∧
  (l = c.yrLevel → (oqS c l).nHs ≤ c.yrLen + lv.folds) ∧
  4 * lv.capOff + 2 ^ (lv.capDepth + 2) ≤ 4 * c.capLen ∧ lv.capOff + 2 ^ lv.capDepth ≤ c.capLen ∧
  lv.posOff + lv.squeezes * (128 / lv.depth) ≤ c.posLen

instance (c : OsCfg) (l : ℕ) : Decidable (LvStatic c l) := by
  unfold LvStatic; dsimp only; infer_instance

/-- The buffers' indices and sizes the lift reads. -/
def SizesOk (c : OsCfg) : Prop :=
  let sz := osSizesF c
  osIxPT c < sz.length ∧ osIxPT1 c < sz.length ∧ osIxHsF c < sz.length ∧
  sz.getD 0 0 = 4 * c.capLen ∧ sz.getD 1 0 = c.capLen ∧ sz.getD 5 0 = 3 * c.nFolds ∧
  sz.getD 11 0 = c.posLen ∧
  sz.getD (osIxHsF c) 0 = c.yrLen + (osLvAt c c.yrLevel).folds ∧
  ∀ l < c.levels.length, osIxSqz c l < sz.length ∧ osIxSqz c l ≠ osIxQbp ∧
    sz.getD (osIxSqz c l) 0 = (c.maxSq + 1) * 5

instance (c : OsCfg) : Decidable (SizesOk c) := by
  unfold SizesOk; dsimp only; infer_instance

/-- **The placed lift's facts at a candidate**: `PlaceOk`, the buffers' and every level's
numeric ones. -/
def PlaceAll (c : OsCfg) : Prop :=
  PlaceOk c ∧ c.yrLevel < c.levels.length ∧ SizesOk c ∧ ∀ l < c.levels.length, LvStatic c l

instance (c : OsCfg) : Decidable (PlaceAll c) := by
  unfold PlaceAll; infer_instance

/-- A specialization found in the table is an entry of it. -/
theorem oqEntry_mem {name : String} (h : (oqEntry name).map (·.1) = some name) :
    (name, oqLoopOf name, oqShapeOf name) ∈ openingQueriesLoops := by
  obtain ⟨e, hE, he1⟩ : ∃ e, oqEntry name = some e ∧ e.1 = name := by
    rcases hE : oqEntry name with _ | e
    · rw [hE] at h; simp at h
    · rw [hE] at h; simp at h; exact ⟨e, rfl, h⟩
  have heq : e = (name, oqLoopOf name, oqShapeOf name) := by
    obtain ⟨a, b, s⟩ := e
    simp only at he1
    simp [oqLoopOf, oqShapeOf, hE, he1]
  rw [← heq]
  exact List.mem_of_find?_eq_some hE

end
end LeanVM.Guest.B1
