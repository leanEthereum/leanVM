/-
  LeanVM.Guest.B1.Whir.CHonAlloc

  Where open_stacked's body allocates, block by block, and the buffers' pointers and sizes in
  order.
-/

module

public import LeanVM.Guest.B1.Whir.CFinEval
public import LeanVM.Guest.B1.Whir.CHead
public import LeanVM.Guest.B1.Place.OsProtoSpec

/-!
# The body's allocations

`bufsAt c b j m`: buffers `j ..< j + m`, their pointers from `b` and their sizes; `bufsAt_add`
joins them, `bufsAt_out`: all of them are `OsOutA`'s allocations.

`osStFrom`, `osStAt`, `osLvsEnd`: the states entering the levels and after them.

`BodyStatic c` (decided per arm and rate in `Whir/CHonAlloc{0..3}`): the head's, each level's
(`lvAllocsV`: a non-final level's `sent`, the final level's normalized lane) and the closing
rounds' allocation statements, and the sizes of the buffers they allocate. `osLevels_split`: the
levels' statements are each level's at its state `osStAt`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Memory

@[expose] public section

/-! ## The levels' states -/

/-- The state entering level `j` of `lvs` from level `lvl` at `s`. -/
def osStFrom (c : OsCfg) (lvl : ℕ) (lvs : List OsLv) (s : OsSt) (j : ℕ) : OsSt :=
  (osLevels c lvl (lvs.take j) s).2

/-- The state entering level `l` of the body. -/
def osStAt (c : OsCfg) (l : ℕ) : OsSt := osStFrom c 0 c.levels (osHead c).2 l

/-- The state after the levels. -/
def osLvsEnd (c : OsCfg) : OsSt := (osLevels c 0 c.levels (osHead c).2).2

/-! ## Buffers in order -/

/-- Buffers `j ..< j + m`: their pointers from `b` and sizes. -/
def bufsAt (c : OsCfg) (b j m : ℕ) : List (E × ℕ) :=
  (List.range m).map fun i ↦ (osPtrA c b (j + i), (osSizesL c).getD (j + i) 0)

theorem bufsAt_add (c : OsCfg) (b j m m' : ℕ) :
    bufsAt c b j m ++ bufsAt c b (j + m) m' = bufsAt c b j (m + m') := by
  simp only [bufsAt, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ ↦ ?_
  simp [Nat.add_assoc]

theorem bufsAt_one (c : OsCfg) (b j : ℕ) :
    bufsAt c b j 1 = [(osPtrA c b j, (osSizesL c).getD j 0)] := by
  simp [bufsAt]

/-- **All the buffers are `OsOutA`'s allocations.** -/
theorem bufsAt_out (c : OsCfg) (b : ℕ) :
    (bufsAt c b 0 (osSizesL c).length).map Prod.snd = osSizesL c ∧
      (bufsAt c b 0 (osSizesL c).length).map Prod.fst =
        (bases b (osSizesL c)).map (fun e ↦ ofK (addressOfIndex e)) := by
  refine ⟨?_, ?_⟩
  · refine List.ext_getElem (by simp [bufsAt]) fun i h1 h2 ↦ ?_
    simp [bufsAt, List.getElem?_eq_getElem h2]
  · refine List.ext_getElem (by simp [bufsAt, length_bases]) fun i h1 h2 ↦ ?_
    simp only [bufsAt, List.length_map, List.length_range] at h1
    simp [bufsAt, osPtrA, List.getElem?_eq_getElem (show i < (bases b (osSizesL c)).length by
      rw [length_bases]; exact h1)]

/-! ## The levels' statements -/

theorem osStFrom_succ (c : OsCfg) (lvl : ℕ) (lv : OsLv) (rest : List OsLv) (s : OsSt) (i : ℕ) :
    osStFrom c lvl (lv :: rest) s (i + 1) = osStFrom c (lvl + 1) rest (osLevel c lvl lv s).2 i := rfl

theorem osStFrom_zero (c : OsCfg) (lvl : ℕ) (lvs : List OsLv) (s : OsSt) :
    osStFrom c lvl lvs s 0 = s := by
  cases lvs <;> rfl

/-- **The levels' statements are each level's at its state.** -/
theorem osLevels_split (c : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLv) (s : OsSt),
    (osLevels c lvl lvs s).1 = ((List.range lvs.length).map fun i ↦
      (osLevel c (lvl + i) (lvs.getD i default) (osStFrom c lvl lvs s i)).1).flatten
  | _, [], _ => rfl
  | lvl, lv :: rest, s => by
    have ih := osLevels_split c (lvl + 1) rest (osLevel c lvl lv s).2
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.flatten_cons]
    show (osLevel c lvl lv s).1 ++ (osLevels c (lvl + 1) rest (osLevel c lvl lv s).2).1 = _
    rw [ih, Nat.add_zero, List.getD_cons_zero, osStFrom_zero]
    congr 2
    refine List.map_congr_left fun i _ ↦ ?_
    simp only [Function.comp_apply, List.getD_cons_succ, osStFrom_succ, show lvl + (i + 1) = lvl + 1 + i by ring]

/-! ## The allocation statements -/

/-- Level `l`'s allocations at its state: a non-final level's `sent` (after its rounds), the final
level's normalized lane (after its positions). -/
def lvAllocsV (c : OsCfg) (l : ℕ) : List (V × (ℕ ⊕ V)) :=
  let lv := c.levels.getD l default
  let s1 := (osRounds c.plan lv.foldsOff lv.folds (osStAt c l)).2
  if l = c.yrLevel then
    let s4 := (osPositions c l lv (osFinalMsg c lv s1).2).2
    [(.n (s4.k + 1), .inr (.n s4.k))]
  else [(.n (s1.k + 1), .inr (.n s1.k))]

/-- **The body's allocation statements and sizes at a configuration.** -/
def BodyStatic (c : OsCfg) : Prop :=
  let n := c.levels.length
  let y := c.yrLevel
  let sz := osSizesL c
  (osHead c).1.filterMap Stmt.allocSz = (List.range 11).map (fun i ↦ (.n (12 + 2 * i), .inr (.n (11 + 2 * i)))) ∧
  (∀ l < n, (osLevel c l (c.levels.getD l default) (osStAt c l)).1.filterMap Stmt.allocSz = lvAllocsV c l) ∧
  (osTail c (osLvsEnd c)).1.filterMap Stmt.allocSz =
    [(.n ((osLvsEnd c).k + 1), .inr (.n (osLvsEnd c).k))] ∧
  sz.length = 19 + y ∧ y + 1 = n ∧
  (∀ j < 11, sz.getD j 0 = (headSizes c).getD j 0) ∧
  (∀ l < y, sz.getD (11 + l) 0 = 2 + (c.levels.getD l default).folds) ∧
  sz.getD (11 + y) 0 = c.yrLen + (c.levels.getD y default).folds ∧
  sz.getD (12 + y) 0 = yrLogCap ∧ sz.getD (13 + y) 0 = pointCap ∧
  sz.getD (14 + y) 0 = pointCap ∧ sz.getD (15 + y) 0 = n * ligColsCap ∧
  sz.getD (16 + y) 0 = n ∧ sz.getD (17 + y) 0 = n ∧ sz.getD (18 + y) 0 = 2 * n ∧
  (∀ j < sz.length, sz.getD j 0 < 2 ^ 64 - 1)

instance (c : OsCfg) : Decidable (BodyStatic c) := by
  unfold BodyStatic; dsimp only; infer_instance

end
end LeanVM.Guest.B1.Whir
