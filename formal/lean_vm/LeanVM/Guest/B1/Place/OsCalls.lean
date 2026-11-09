/-
  LeanVM.Guest.B1.Place.OsCalls

  open_stacked's calls, level by level: before the squeeze loop, the loop, after it.
-/

module

public import LeanVM.Guest.B1.Place.OsKids
public import LeanVM.Guest.B1.Whir.Flatness

/-!
# `open_stacked`'s calls, by level

`osLevel_callSplit`: a level is its rounds, commitment (or final message) and grinding check
(`lvA`), its squeezes (`osSqueezes`), and the rest (`lvB`). `osSqueezes_callS`: the squeezes call
only the squeeze loop. `osLvKOf σ`: the levels' frames as `OsLvK`s (the loop's frame between the
two blocks); `osLevels_calls`: they are the levels' calls in order. `osBodyA_calls`: the body's
calls are the levels', then the tail's, then the finish's (the head calls nothing).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir

@[expose] public section

/-- A level's commitment, or its final message. -/
def lvM (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt × OsSt × ℕ :=
  if lvl = c.yrLevel then osFinal c (osFolds osFch lv.foldsOff lv.folds s).2
  else osCommit c.plan lvl lv (osFolds osFch lv.foldsOff lv.folds s).2

/-- A level before its squeezes. -/
def lvA (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt :=
  (osFolds osFch lv.foldsOff lv.folds s).1 ++ (lvM c lvl lv s).1 ++
    [.call ("grind_check__L" ++ natStr lv.grind) [.n (lvM c lvl lv s).2.2] []]

/-- A level after its squeezes. -/
def lvB (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt :=
  let sq := osSqueezes c lvl lv (lvM c lvl lv s).2.1
  let lam := sq.2.k - 1
  let lp := osLamPow lvl lam lv.queries sq.2.k
  let lamN := lp.2.1
  let q := osQueries c lvl lv lam lamN { sq.2 with k := lp.2.2 }
  let s1 : OsSt := { sq.2 with k := q.2.1, w0 := q.2.2.2.1, w1 := q.2.2.2.2.2,
                               co := sq.2.co + 2, mats := osQueriesMats c lv { sq.2 with k := lp.2.2 } }
  let o := if lvl = c.yrLevel then (([] : List Stmt), s1, lam) else
    let g := osOodGlue lvl lam s1
    (g.1, g.2, s1.k + 12)
  let beta := o.2.2
  let bk := o.2.1.k
  let gl := osGlue beta q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2 { o.2.1 with k := bk + 1 }
  lp.1 ++ q.1 ++ o.1 ++
    [.atom (.mul (.n bk) (.n beta) (.n lamN)), .atom (.load (.n bk) (.n osBetas) lvl)] ++ gl.1

theorem osLevel_callSplit (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osLevel c lvl lv s).1 = lvA c lvl lv s ++ ((osSqueezes c lvl lv (lvM c lvl lv s).2.1).1 ++
      lvB c lvl lv s) := by
  simp only [osLevel, lvA, lvB, lvM, List.append_assoc]

/-- The squeeze loop's frame. -/
def sqCallS (c : OsCfg) (lvl : ℕ) (k : ℕ) : Option V × String × List V × List V :=
  (some (.n (k + 2 + 2)), c.sqLoop lvl,
    .n (k + 2 + 3) :: .n (k + 2 + 4) :: [k + 1, osQpos, osQbp, osWin].map V.n, [])

theorem osSqueezes_callS (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osSqueezes c lvl lv s).1.filterMap Main.Stmt.callS = [sqCallS c lvl s.k] := by
  have hpad : (osPad s.pad (s.k + 14)).1.filterMap Main.Stmt.callS = [] := by
    unfold osPad; split <;> simp [Main.Stmt.callS]
  simp only [osSqueezes, List.filterMap_append, hpad, osHeap, osLoopCall, osSqueeze0, challengeT,
    keccakA, List.filterMap_cons, List.filterMap_nil, Main.Stmt.callS, List.filterMap_map]
  simp [Function.comp_def, Main.Stmt.callS, sqCallS]

/-- The levels' frames: per level, the calls before its squeeze loop, the loop, the calls after. -/
noncomputable def osLvKOf (σ : Val) (c : OsCfg) : ℕ → List OsLv → OsSt → List OsLvK
  | _, [], _ => []
  | lvl, lv :: rest, s =>
    ⟨((lvA c lvl lv s).filterMap Main.Stmt.callS).map (Main.mkCall σ),
      Main.mkCall σ (sqCallS c lvl (lvM c lvl lv s).2.1.k),
      ((lvB c lvl lv s).filterMap Main.Stmt.callS).map (Main.mkCall σ)⟩ ::
      osLvKOf σ c (lvl + 1) rest (osLevel c lvl lv s).2

theorem osLevels_calls (σ : Val) (c : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLv) (s : OsSt),
    ((osLevels c lvl lvs s).1.filterMap Main.Stmt.callS).map (Main.mkCall σ) =
      (osLvKOf σ c lvl lvs s).flatMap OsLvK.calls
  | _, [], _ => rfl
  | lvl, lv :: rest, s => by
    have e : (osLevels c lvl (lv :: rest) s).1 = (osLevel c lvl lv s).1 ++
        (osLevels c (lvl + 1) rest (osLevel c lvl lv s).2).1 := rfl
    rw [e, List.filterMap_append, List.map_append, osLevels_calls σ c (lvl + 1) rest, osLevel_callSplit,
      List.filterMap_append, List.filterMap_append, osSqueezes_callS]
    simp [osLvKOf, OsLvK.calls]

theorem osHead_callS (c : OsCfg) : (osHead c).1.filterMap Main.Stmt.callS = [] := by
  simp [osHead, osHeap, osWinTabs, Main.Stmt.callS]
  rintro a (⟨i, -, rfl | rfl⟩ | rfl | rfl | rfl | rfl) <;> rfl

theorem osBodyA_calls (σ : Val) (c : OsCfg) :
    ((osBodyA c).filterMap Main.Stmt.callS).map (Main.mkCall σ) =
      (osLvKOf σ c 0 c.levels (osHead c).2).flatMap OsLvK.calls ++
        (((osTail c (osLevels c 0 c.levels (osHead c).2).2).1.filterMap Main.Stmt.callS).map
          (Main.mkCall σ) ++
        ((osFinishA c (osTail c (osLevels c 0 c.levels (osHead c).2).2).2.1
          (osTail c (osLevels c 0 c.levels (osHead c).2).2).2.2).filterMap Main.Stmt.callS).map
          (Main.mkCall σ)) := by
  rw [osBodyA, List.filterMap_append, List.filterMap_append, List.filterMap_append, osHead_callS,
    List.nil_append, List.map_append, List.map_append, osLevels_calls, List.append_assoc]

end
end LeanVM.Guest.B1
