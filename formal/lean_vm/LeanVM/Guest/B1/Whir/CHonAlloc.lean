/-
  LeanVM.Guest.B1.Whir.CHonAlloc

  Where open_stacked's body allocates, block by block, and the buffers' pointers and sizes in
  order.
-/

module

public import LeanVM.Guest.B1.Whir.CFinEval
public import LeanVM.Guest.B1.Place.OsCallV
public import LeanVM.Guest.B1.Place.OsLayF
public import LeanVM.Guest.B1.Whir.CHead

/-!
# The body's allocations

`bufsAt c b j m`: buffers `j ..< j + m`, their pointers from `b` and their sizes; `bufsAt_add`,
`bufsAt_levels` join them, `bufsAt_out`: all of them are `OsOutF`'s allocations.

`BodyStatic c` (decided per candidate in `Whir/CHonAlloc{0..3}`): the head's, each level's and
the closing rounds' allocation statements (`lvAllocsV`), and the sizes of the buffers they
allocate. `osLevels_split`: the levels' statements are each level's at its state `osStAt`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Memory

@[expose] public section

/-! ## Buffers in order -/

/-- Buffers `j ..< j + m`: their pointers from `b` and sizes. -/
def bufsAt (c : OsCfg) (b j m : ℕ) : List (E × ℕ) :=
  (List.range m).map fun i ↦ (osPtrF c b (j + i), (osSizesF c).getD (j + i) 0)

theorem bufsAt_add (c : OsCfg) (b j m m' : ℕ) :
    bufsAt c b j m ++ bufsAt c b (j + m) m' = bufsAt c b j (m + m') := by
  simp only [bufsAt, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ ↦ ?_
  simp [Nat.add_assoc]

theorem bufsAt_two (c : OsCfg) (b j : ℕ) :
    bufsAt c b j 2 = [(osPtrF c b j, (osSizesF c).getD j 0), (osPtrF c b (j + 1), (osSizesF c).getD (j + 1) 0)] := by
  simp [bufsAt, List.range_succ]

theorem bufsAt_one (c : OsCfg) (b j : ℕ) :
    bufsAt c b j 1 = [(osPtrF c b j, (osSizesF c).getD j 0)] := by
  simp [bufsAt]

theorem bufsAt_levels (c : OsCfg) (b j : ℕ) : ∀ n : ℕ,
    ((List.range n).map fun l ↦ bufsAt c b (j + 2 * l) 2).flatten = bufsAt c b j (2 * n)
  | 0 => by simp [bufsAt]
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.flatten_append, bufsAt_levels c b j n]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [bufsAt_add, show 2 * n + 2 = 2 * (n + 1) by ring]

/-- **All the buffers are `OsOutF`'s allocations.** -/
theorem bufsAt_out (c : OsCfg) (b : ℕ) :
    (bufsAt c b 0 (osSizesF c).length).map Prod.snd = osSizesF c ∧
      (bufsAt c b 0 (osSizesF c).length).map Prod.fst =
        (bases b (osSizesF c)).map (fun e ↦ ofK (addressOfIndex e)) := by
  refine ⟨?_, ?_⟩
  · refine List.ext_getElem (by simp [bufsAt]) fun i h1 h2 ↦ ?_
    simp [bufsAt, List.getElem?_eq_getElem h2]
  · refine List.ext_getElem (by simp [bufsAt, length_bases]) fun i h1 h2 ↦ ?_
    simp only [bufsAt, List.length_map, List.length_range] at h1
    simp [bufsAt, osPtrF, osBaseF, List.getElem?_eq_getElem (show i < (bases b (osSizesF c)).length by
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

/-- Level `l`'s allocations at its state: a non-final level's `sent` and squeeze run, the final
level's squeeze run and normalized lane. -/
def lvAllocsV (c : OsCfg) (l : ℕ) : List (V × (ℕ ⊕ V)) :=
  let lv := osLvAt c l
  let st := osStAt c l
  if l = c.yrLevel then
    [(.n ((lvM c l lv st).2.k + 1), .inr (.n (lvM c l lv st).2.k)),
      (.n (lvH c l lv st).2.hs, .inr (.n (osCap c l lv (lvS c l lv st).2).2.k))]
  else
    [(.n ((lvF c lv st).2.k + 1), .inr (.n (lvF c lv st).2.k)),
      (.n ((lvM c l lv st).2.k + 1), .inr (.n (lvM c l lv st).2.k))]

/-- **The body's allocation statements and its buffers' sizes**, checked. -/
def BodyStatic (c : OsCfg) : Prop :=
  let n := c.levels.length
  let sz := osSizesF c
  (osHead c).1.filterMap Stmt.allocSz = (List.range 13).map (fun i ↦ (.n (11 + 2 * i), .inr (.n (10 + 2 * i)))) ∧
  (∀ l < n, (osLevel c l (osLvAt c l) (osStAt c l)).1.filterMap Stmt.allocSz = lvAllocsV c l) ∧
  (osTail c (osLvsEnd c)).1.filterMap Stmt.allocSz =
    [(.n ((osLvsEnd c).k + 1), .inr (.n (osLvsEnd c).k))] ∧
  sz.length = 20 + 2 * n + c.yrLevel ∧ c.yrLevel + 1 = n ∧
  (∀ j < 13, sz.getD j 0 = (headSizes c).getD j 0) ∧
  (∀ l < n, sz.getD (13 + 2 * l) 0 =
      (if l = c.yrLevel then (c.maxSq + 1) * 5 else 2 + (osLvAt c l).folds) ∧
    sz.getD (14 + 2 * l) 0 =
      (if l = c.yrLevel then c.yrLen + (osLvAt c l).folds else (c.maxSq + 1) * 5)) ∧
  sz.getD (13 + 2 * n) 0 = yrLogCap ∧ sz.getD (14 + 2 * n) 0 = pointCap ∧
  sz.getD (15 + 2 * n) 0 = pointCap ∧ sz.getD (16 + 2 * n) 0 = n * ligColsCap ∧
  sz.getD (17 + 2 * n) 0 = n ∧ sz.getD (18 + 2 * n) 0 = n ∧ sz.getD (19 + 2 * n) 0 = 2 * n ∧
  (∀ l < c.yrLevel, sz.getD (20 + 2 * n + l) 0 = 2 * ((osLvAt c l).queries / resBatch + 1)) ∧
  (∀ j < sz.length, sz.getD j 0 < 2 ^ 64 - 1)

instance (c : OsCfg) : Decidable (BodyStatic c) := by
  unfold BodyStatic; dsimp only; infer_instance

end
end LeanVM.Guest.B1.Whir
