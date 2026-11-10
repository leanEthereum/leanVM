/-
  LeanVM.Guest.B1.Place.OsCallK

  The levels' calls of f128's `open_stacked` template as the placed lift's level frames.
-/

module

public import LeanVM.Guest.B1.Place.OsCallV
public import LeanVM.Guest.B1.Place.OsKidsP

/-!
# The levels' frames

`osLvKs σ c lvl lvs s`: per level, the calls before its squeezes, its two squeeze calls (the first
decoder, the loop), the calls after (`OsLvKP`); `osLevels_calls`: they are the levels' calls in
order; `osLvKs_get`: level `j`'s, at its state `osStFrom`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir

@[expose] public section

/-- The levels' frames from level `lvl` at `s`. -/
noncomputable def osLvKs (σ : Val) (c : OsCfg) : ℕ → List OsLv → OsSt → List OsLvKP
  | _, [], _ => []
  | lvl, lv :: rest, s =>
    ⟨((lvA c lvl lv s).filterMap Stmt.callS).map (mkCall σ),
      [mkCall σ (osDecCallAt c lv (lvM c lvl lv s).2), mkCall σ (osSqCallAt c lvl lv (lvM c lvl lv s).2)],
      ((lvB c lvl lv s).filterMap Stmt.callS).map (mkCall σ)⟩ ::
      osLvKs σ c (lvl + 1) rest (osLevel c lvl lv s).2

theorem osLevels_calls (σ : Val) (c : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLv) (s : OsSt),
    ((osLevels c lvl lvs s).1.filterMap Stmt.callS).map (mkCall σ) =
      (osLvKs σ c lvl lvs s).flatMap OsLvKP.calls
  | _, [], _ => rfl
  | lvl, lv :: rest, s => by
    have e : (osLevels c lvl (lv :: rest) s).1 = (osLevel c lvl lv s).1 ++
        (osLevels c (lvl + 1) rest (osLevel c lvl lv s).2).1 := rfl
    rw [e, List.filterMap_append, List.map_append, osLevels_calls σ c (lvl + 1) rest,
      osLevel_callSplit, List.filterMap_append, List.filterMap_append, lvS, osSqueezes_callS]
    simp [osLvKs, OsLvKP.calls]

theorem osLvKs_length (σ : Val) (c : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLv) (s : OsSt),
    (osLvKs σ c lvl lvs s).length = lvs.length
  | _, [], _ => rfl
  | lvl, _ :: rest, s => by simp [osLvKs, osLvKs_length σ c (lvl + 1) rest]

theorem osLvKs_get (σ : Val) (c : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLv) (s : OsSt) (j : ℕ)
    (hj : j < lvs.length),
    (osLvKs σ c lvl lvs s)[j]'(by rw [osLvKs_length]; exact hj) =
      ⟨((lvA c (lvl + j) lvs[j] (osStFrom c lvl lvs s j)).filterMap Stmt.callS).map (mkCall σ),
        [mkCall σ (osDecCallAt c lvs[j] (lvM c (lvl + j) lvs[j] (osStFrom c lvl lvs s j)).2),
          mkCall σ (osSqCallAt c (lvl + j) lvs[j] (lvM c (lvl + j) lvs[j] (osStFrom c lvl lvs s j)).2)],
        ((lvB c (lvl + j) lvs[j] (osStFrom c lvl lvs s j)).filterMap Stmt.callS).map (mkCall σ)⟩
  | _, [], _, _, hj => absurd hj (by simp)
  | lvl, lv :: rest, s, 0, _ => rfl
  | lvl, lv :: rest, s, j + 1, hj => by
    have := osLvKs_get σ c (lvl + 1) rest (osLevel c lvl lv s).2 j (by simpa using hj)
    simp only [osLvKs, List.getElem_cons_succ, this]
    rw [show lvl + 1 + j = lvl + (j + 1) by omega]
    rfl

end
end LeanVM.Guest.B1
