/-
  LeanVM.Guest.B1.Place.KidShapes

  open_stacked's frames by level, and which of their callees are named, decided per arm.
-/

module

public import LeanVM.Guest.B1.Place.KidsNames

/-!
# The frames' shapes

`osLvKOf_get`: level `j`'s frames are its blocks' (`lvA`, `level_positions`, `lvB`) from the state
the levels before it leave (`osLvSt0 c j`). `OsKidShapes c`: the named callees and the helpers'
names, read off the body's call statements (σ-free, decided per arm): every callee before a
level's positions and of the tail is named; a level's other unnamed callee is its
`level_queries`, the finish's its `level_residual`; the helpers' names are apart.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir

@[expose] public section

/-- The state before level `j`. -/
def osLvSt0 (c : OsCfg) (j : ℕ) : OsSt := (osLevels c 0 (c.levels.take j) (osHead c).2).2

theorem osLvKOf_get (σ : Val) (c : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLv) (s : OsSt) (j : ℕ)
    (hj : j < lvs.length),
    (osLvKOf σ c lvl lvs s)[j]'(by rw [osLvKOf_length]; exact hj) =
      ⟨((lvA c (lvl + j) lvs[j] (osLevels c lvl (lvs.take j) s).2).filterMap (Stmt.callSF σ)).map
          (Main.mkCall σ),
        Main.mkCall σ (lpCallS σ c (lvl + j) (lvM c (lvl + j) lvs[j] (osLevels c lvl (lvs.take j) s).2).2.1),
        ((lvB c (lvl + j) lvs[j] (osLevels c lvl (lvs.take j) s).2).filterMap (Stmt.callSF σ)).map
          (Main.mkCall σ)⟩
  | _, [], _, _, hj => absurd hj (by simp)
  | lvl, lv :: rest, s, 0, _ => by
    simp only [osLvKOf, List.getElem_cons_zero, Nat.add_zero, List.take_zero]
    rfl
  | lvl, lv :: rest, s, j + 1, hj => by
    have ih := osLvKOf_get σ c (lvl + 1) rest (osLevel c lvl lv s).2 j (by simpa using hj)
    simp only [osLvKOf, List.getElem_cons_succ, ih, show lvl + 1 + j = lvl + (j + 1) by omega]
    rfl

theorem osLevels_append (c : OsCfg) : ∀ (lvl : ℕ) (l1 l2 : List OsLv) (s : OsSt),
    (osLevels c lvl (l1 ++ l2) s).1 = (osLevels c lvl l1 s).1 ++
      (osLevels c (lvl + l1.length) l2 (osLevels c lvl l1 s).2).1
  | _, [], _, _ => by simp [osLevels]
  | lvl, lv :: l1, l2, s => by
    have ih := osLevels_append c (lvl + 1) l1 l2 (osLevel c lvl lv s).2
    simp only [List.cons_append, osLevels, ih, List.append_assoc, List.length_cons,
      show lvl + 1 + l1.length = lvl + (l1.length + 1) by omega]

/-- **Level `j`'s statements are the body's.** -/
theorem osLevel_mem_body (c : OsCfg) {j : ℕ} (hj : j < c.levels.length) {s : Stmt}
    (hs : s ∈ (osLevel c j (lvAt c j) (osLvSt0 c j)).1) : s ∈ osBodyAc c := by
  have e : c.levels = c.levels.take j ++ (lvAt c j :: c.levels.drop (j + 1)) := by
    rw [lvAt, List.getD_eq_getElem _ _ hj]; simp
  have h := osLevels_append c 0 (c.levels.take j) (lvAt c j :: c.levels.drop (j + 1)) (osHead c).2
  rw [← e] at h
  have hl : (c.levels.take j).length = j := by simp; omega
  unfold osBodyAc
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
  rw [h, hl]
  refine List.mem_append_right _ ?_
  simp only [osLevels, Nat.zero_add]
  exact List.mem_append_left _ hs

/-- The callees a block's call statements name. -/
def blockNames (l : List Stmt) : List String := (l.filterMap Stmt.calleesS).flatten

/-- **The frames' shapes**, σ-free. -/
structure OsKidShapes (c : OsCfg) : Prop where
  lvA : ∀ i < c.levels.length, ∀ f ∈ blockNames (lvA c i (lvAt c i) (osLvSt0 c i)),
    osKindOf f ≠ none
  lvB : ∀ i < c.levels.length, ∀ f ∈ blockNames (lvB c i (lvAt c i) (osLvSt0 c i)),
    osKindOf f = none → f ∈ (c.lvAt i).map (osQueriesName i)
  tail : ∀ f ∈ blockNames (osTlSt c).1, osKindOf f ≠ none
  fin : ∀ f ∈ blockNames (osFinA c (osTlSt c).2.1 (osTlSt c).2.2), osKindOf f = none →
    ∃ l < c.levels.length, f ∈ (c.lvAt l).map osResidualName
  apart : ∀ i < c.levels.length, ∀ l < c.levels.length, ∀ lv ∈ c.lvAt i, ∀ lv' ∈ c.lvAt l,
    osQueriesName i lv ≠ osPositionsName lv' ∧ osQueriesName i lv ≠ osResidualName lv' ∧
      osResidualName lv ≠ osPositionsName lv'

end
end LeanVM.Guest.B1
