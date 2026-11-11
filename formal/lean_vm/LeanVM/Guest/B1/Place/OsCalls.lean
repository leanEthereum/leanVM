/-
  LeanVM.Guest.B1.Place.OsCalls

  open_stacked's calls, level by level: before `level_positions`, its dispatch, after it.
-/

module

public import LeanVM.Guest.B1.Place.OsKids
public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.B1.Whir.CBody
public import LeanVM.Guest.B1.Whir.Flatness
public import LeanVM.Guest.B1.Whir.BrBody

/-!
# `open_stacked`'s calls, by level

The body is flat (`osBodyAc_flatF`), its dispatches entering the callee the rate's selector names
(`Stmt.callSF σ`). `osLevel_callSplit`: a level is its rounds, commitment (or final message) and
grinding check (`lvA`), its positions (`osPositions`), and the rest (`lvB`).
`osPositions_callSF`: the positions call only the rate's `level_positions`. `osLvKOf σ`: the
levels' frames as `OsLvK`s (`level_positions`' frame between the two blocks); `osLevels_callsF`:
they are the levels' calls in order. `osBodyAc_calls`: the body's calls are the levels', then the
tail's, then the finish's (the head calls nothing).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir

@[expose] public section

/-- A statement that is an atom. -/
def Stmt.isAtomB : Stmt → Bool
  | .atom _ => true
  | _ => false

theorem callSF_atoms (σ : Val) : ∀ l : List Stmt, l.all Stmt.isAtomB = true →
    l.filterMap (Stmt.callSF σ) = []
  | [], _ => rfl
  | s :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    match s, h.1 with
    | .atom _, _ =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS]
      exact callSF_atoms σ l h.2

theorem osMatP_atoms (P : List (ℕ × ℕ × ℕ)) (m : List OsMat) (b o k : ℕ) :
    (osMatP P m b o k).1.all Stmt.isAtomB = true := by
  unfold osMatP; split_ifs <;> rfl

theorem osPad_atoms (pad : Option ℕ) (k : ℕ) : (osPad pad k).1.all Stmt.isAtomB = true := by
  cases pad <;> rfl

/-- **Whir's flat statements are flat.** -/
theorem flatF_of_flat : ∀ l : List Stmt, l.all Whir.Stmt.flat = true → l.all Core.Stmt.flat = true
  | [], _ => rfl
  | s :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h ⊢
    refine ⟨?_, flatF_of_flat l h.2⟩
    match s, h.1 with
    | .atom _, _ => rfl
    | .call .., _ => rfl
    | .callIf .., _ => rfl
    | .dispatch .., _ => rfl

theorem osBodyAc_eq (c : OsCfg) : osBodyAc c = osBodyA c := rfl

theorem osBodyAc_flatF (c : OsCfg) : (osBodyAc c).all Core.Stmt.flat = true := by
  rw [osBodyAc_eq]; exact flatF_of_flat _ (osBodyA_flat c)

/-- A level's fold rounds. -/
abbrev lvF (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt × OsSt :=
  osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds s

/-- A level's commitment, or its final message. -/
def lvM (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt × OsSt × ℕ :=
  if lvl = c.yrLevel then osFinal c (lvF c lvl lv s).2 else osCommit c.plan lvl lv (lvF c lvl lv s).2

/-- A level before its positions. -/
def lvA (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt :=
  (lvF c lvl lv s).1 ++ (lvM c lvl lv s).1 ++
    [.call ("grind_check__L" ++ natStr lv.grind) [.n (lvM c lvl lv s).2.2] []]

/-- A level after its positions. -/
def lvB (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt :=
  let sq := osPositions c lvl lv (lvM c lvl lv s).2.1
  let lam := sq.2.k - 1
  let mu := osMu lvl lam sq.2.k
  let q := osQueries c lvl lv lam { sq.2 with k := mu.2 }
  let lamN := q.2.2.2.1
  let s1 : OsSt := { sq.2 with k := q.2.1, w0 := q.2.2.2.2.1, w1 := q.2.2.2.2.2.2,
                               co := sq.2.co + 2, mats := osQueriesMats c lv { sq.2 with k := mu.2 } }
  let o := if lvl = c.yrLevel then (([] : List Stmt), s1, lam) else
    let g := osOodGlue lvl lam s1
    (g.1, g.2, s1.k + 12)
  let beta := o.2.2
  let bk := o.2.1.k
  let gl := osGlue beta q.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2 { o.2.1 with k := bk + 1 }
  mu.1 ++ q.1 ++ o.1 ++
    [.atom (.mul (.n bk) (.n beta) (.n lamN)), .atom (.load (.n bk) (.n osBetas) lvl)] ++ gl.1

theorem osLevel_callSplit (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osLevel c lvl lv s).1 = lvA c lvl lv s ++ ((osPositions c lvl lv (lvM c lvl lv s).2.1).1 ++
      lvB c lvl lv s) := by
  simp only [osLevel, lvA, lvB, lvM, lvF, List.append_assoc]

/-- `level_positions`' frame of a level, at the valuation `σ`. -/
noncomputable def lpCallS (σ : Val) (c : OsCfg) (lvl : ℕ) (s : OsSt) :
    Option V × String × List V × List V :=
  let qp := osMatP c.plan s.mats osQpos (lvAt c lvl).posOff s.k
  let m1 := osMatsAfter c.plan s.mats osQpos (lvAt c lvl).posOff s.k
  let wp := osMatP c.plan m1 osQbp (lvAt c lvl).posOff qp.2.2
  (none, ((c.lvAt lvl).map osPositionsName).getD (logG (σ (.n osRate))) "",
    (s.fs ++ [qp.2.1, wp.2.1, osWin]).map V.n, osRun wp.2.2 5)

theorem osPositions_callSF (σ : Val) (c : OsCfg) (lvl : ℕ) (s : OsSt) :
    (osPositions c lvl (lvAt c lvl) s).1.filterMap (Stmt.callSF σ) = [lpCallS σ c lvl s] := by
  simp only [osPositions, List.filterMap_append,
    callSF_atoms σ _ (osMatP_atoms _ _ _ _ _), callSF_atoms σ _ (osPad_atoms _ _),
    List.filterMap_cons, List.filterMap_nil, Stmt.callSF, List.nil_append]
  rw [callSF_atoms σ _ (by simp [Stmt.isAtomB]), callSF_atoms σ _ (by
    simp only [osSqueeze0, challengeT, keccakA]; rfl)]
  rfl

/-- The levels' frames: per level, the calls before its positions, `level_positions`, the calls
after. -/
noncomputable def osLvKOf (σ : Val) (c : OsCfg) : ℕ → List OsLv → OsSt → List OsLvK
  | _, [], _ => []
  | lvl, lv :: rest, s =>
    ⟨((lvA c lvl lv s).filterMap (Stmt.callSF σ)).map (Main.mkCall σ),
      Main.mkCall σ (lpCallS σ c lvl (lvM c lvl lv s).2.1),
      ((lvB c lvl lv s).filterMap (Stmt.callSF σ)).map (Main.mkCall σ)⟩ ::
      osLvKOf σ c (lvl + 1) rest (osLevel c lvl lv s).2

theorem osLvKOf_length (σ : Val) (c : OsCfg) :
    ∀ (lvl : ℕ) (lvs : List OsLv) (s : OsSt), (osLvKOf σ c lvl lvs s).length = lvs.length
  | _, [], _ => rfl
  | lvl, _ :: rest, _ => by simp [osLvKOf, osLvKOf_length σ c (lvl + 1) rest]

/-- The levels `lvl ..` of `c.levels.drop lvl`, their calls in order. -/
theorem osLevels_callsF (σ : Val) (c : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLv) (s : OsSt),
    (∀ i < lvs.length, lvs.getD i default = lvAt c (lvl + i)) →
    ((osLevels c lvl lvs s).1.filterMap (Stmt.callSF σ)).map (Main.mkCall σ) =
      (osLvKOf σ c lvl lvs s).flatMap OsLvK.calls
  | _, [], _, _ => rfl
  | lvl, lv :: rest, s, hlv => by
    have e : (osLevels c lvl (lv :: rest) s).1 = (osLevel c lvl lv s).1 ++
        (osLevels c (lvl + 1) rest (osLevel c lvl lv s).2).1 := rfl
    have h0 : lv = lvAt c lvl := by simpa using hlv 0 (by simp)
    have ih := osLevels_callsF σ c (lvl + 1) rest (osLevel c lvl lv s).2 fun i hi ↦ by
      have := hlv (i + 1) (by simp; omega)
      simpa [show lvl + (i + 1) = lvl + 1 + i by omega] using this
    rw [e, List.filterMap_append, List.map_append, ih, osLevel_callSplit,
      List.filterMap_append, List.filterMap_append]
    have hp := osPositions_callSF σ c lvl (lvM c lvl lv s).2.1
    rw [← h0] at hp
    rw [hp]
    simp [osLvKOf, OsLvK.calls]

theorem osHead_callSF (σ : Val) (c : OsCfg) : (osHead c).1.filterMap (Stmt.callSF σ) = [] :=
  callSF_atoms σ _ (by
    simp [osHead, osHeap, osWinTabs, Stmt.isAtomB])

theorem levels_getD_lvAt (c : OsCfg) : ∀ i < c.levels.length, c.levels.getD i default =
    lvAt c (0 + i) := fun i _ ↦ by simp [lvAt]

/-- **The body's calls**: the levels', the tail's, the finish's. -/
theorem osBodyAc_calls (σ : Val) (c : OsCfg) :
    ((osBodyAc c).filterMap (Stmt.callSF σ)).map (Main.mkCall σ) =
      (osLvKOf σ c 0 c.levels (osHead c).2).flatMap OsLvK.calls ++
        (((osTlSt c).1.filterMap (Stmt.callSF σ)).map (Main.mkCall σ) ++
        ((osFinA c (osTlSt c).2.1 (osTlSt c).2.2).filterMap (Stmt.callSF σ)).map
          (Main.mkCall σ)) := by
  rw [osBodyAc, List.filterMap_append, List.filterMap_append, List.filterMap_append, osHead_callSF,
    List.nil_append, List.map_append, List.map_append,
    osLevels_callsF σ c 0 c.levels _ (levels_getD_lvAt c), List.append_assoc]

end
end LeanVM.Guest.B1
