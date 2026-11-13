/-
  LeanVM.Guest.B1.Place.ArmCalls

  `open_stacked`'s frames at the merged template: level by level, then the closing rounds' and the
  finish's.
-/

module

public import LeanVM.Guest.B1.Place.OsProtoSpec
public import LeanVM.Guest.B1.Place.OsKids
public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.B1.Whir.Flatness

/-!
# `open_stacked`'s frames

A level (`Whir.osLevel`) is its rounds, its message and its query grind (`lvPre`, no dispatch),
its positions (one dispatch into `level_positions`, `posFrame`) and the rest (`lvPost`, one
dispatch into `level_queries`, `qFrame`). `osLvKOf σ c`: the levels' frames as `OsLvK`s;
`osLvKOf_get`: level `l`'s, at the state `osLvSt c l`. After the levels, the closing rounds' (no
dispatch), then the finish's: `fold_final_msg` and the dispatches into `level_residual`
(`resFrames`). `osBodyA_calls`: the body's frames in that order.

`kid_mem_callees`, `kids_bound_le`: each frame of a flat block names a callee of its call
statement (`Stmt.calleesS`), within the statements' `osCallB`; `osKids_names`, `osKids_bound` for
the body.
-/

namespace LeanVM.Guest.B1.Arm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B1.Whir

@[expose] public section

/-! ## Atoms and dispatch-free blocks -/

/-- An atom. -/
def atomS : Stmt → Bool
  | .atom _ => true
  | _ => false

/-- Not a dispatch. -/
def plainS : Stmt → Bool
  | .dispatch .. => false
  | _ => true

/-- A block of atoms. -/
abbrev Atoms (l : List Stmt) : Prop := l.all atomS = true

/-- A block without dispatches. -/
abbrev Plain (l : List Stmt) : Prop := l.all plainS = true

theorem atoms_append {a b : List Stmt} (ha : Atoms a) (hb : Atoms b) : Atoms (a ++ b) := by
  simp only [Atoms, List.all_append, ha, hb, Bool.and_self]

theorem plain_append {a b : List Stmt} (ha : Plain a) (hb : Plain b) : Plain (a ++ b) := by
  simp only [Plain, List.all_append, ha, hb, Bool.and_self]

theorem atoms_cons {s : Stmt} {a : List Stmt} (hs : atomS s = true) (ha : Atoms a) :
    Atoms (s :: a) := by
  simp only [Atoms, List.all_cons, hs, ha, Bool.true_and]

theorem plain_cons {s : Stmt} {a : List Stmt} (hs : plainS s = true) (ha : Plain a) :
    Plain (s :: a) := by
  simp only [Plain, List.all_cons, hs, ha, Bool.true_and]

theorem plain_of_atoms : ∀ {l : List Stmt}, Atoms l → Plain l
  | [], _ => rfl
  | s :: l, h => by
    simp only [Atoms, List.all_cons, Bool.and_eq_true] at h
    match s, h.1 with
    | .atom _, _ => exact plain_cons rfl (plain_of_atoms h.2)

theorem callSF_atoms (σ : Val) : ∀ l : List Stmt, Atoms l → l.filterMap (Stmt.callSF σ) = []
  | [], _ => rfl
  | s :: l, h => by
    simp only [Atoms, List.all_cons, Bool.and_eq_true] at h
    match s, h.1 with
    | .atom _, _ =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS]
      exact callSF_atoms σ l h.2

theorem callSF_plain (σ : Val) : ∀ l : List Stmt, Plain l →
    l.filterMap (Stmt.callSF σ) = l.filterMap Main.Stmt.callS
  | [], _ => rfl
  | s :: l, h => by
    simp only [Plain, List.all_cons, Bool.and_eq_true] at h
    have ih := callSF_plain σ l h.2
    match s, h.1 with
    | .atom _, _ => simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, ih]
    | .call .., _ => simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, ih]
    | .callIf .., _ => simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, ih]
    | .ite .., _ => simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, ih]
    | .match_ .., _ => simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, ih]
    | .ret _, _ => simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, ih]

theorem osMatP_atoms (P : List (ℕ × ℕ × ℕ)) (m : List OsMat) (b o k : ℕ) :
    Atoms (osMatP P m b o k).1 := by
  unfold osMatP; split_ifs <;> rfl

theorem osMatS_atoms (P : List (ℕ × ℕ × ℕ)) (b o : ℕ) (s : OsSt) : Atoms (osMatS P b o s).1 :=
  osMatP_atoms _ _ _ _ _

theorem osCurS_atoms (s : OsSt) : Atoms (osCurS s).1 := by
  unfold osCurS osMat; dsimp only; split_ifs <;> rfl

theorem osPad_atoms (pad : Option ℕ) (k : ℕ) : Atoms (osPad pad k).1 := by
  cases pad <;> rfl

theorem osHeap_atoms (e k : ℕ) : Atoms (osHeap e k) := rfl

theorem osLam_atoms (s : OsSt) : Atoms (osLam s).1 := by
  unfold osLam
  simp only [Atoms, List.all_append, osPad_atoms _ _]
  simp [atomS, osKeccak]

theorem osHsCoefs_atoms (src dst : ℕ) (sc : ℕ → ℕ) (si di : ℕ) :
    ∀ n i k, Atoms (osHsCoefs src dst sc si di n i k).1
  | 0, _, _ => rfl
  | n + 1, i, k => by
    refine atoms_append ?_ (osHsCoefs_atoms src dst sc si di n (i + 1) _)
    unfold osHsCoef; split_ifs <;> rfl

theorem osHsMid_atoms (lvl : ℕ) (lv : OsLv) (s : OsSt) : Atoms (osHsMid lvl lv s).1 :=
  osHsCoefs_atoms _ _ _ _ _ _ _ _

theorem osHsFinal_atoms (c : OsCfg) (lv : OsLv) (s : OsSt) : Atoms (osHsFinal c lv s).1 :=
  atoms_append (osHeap_atoms _ _) (osHsCoefs_atoms _ _ _ _ _ _ _ _)

theorem osGlue_atoms (lvl : ℕ) (s : OsSt) : Atoms (osGlue lvl s).1 := rfl

theorem osRounds_plain (P : List (ℕ × ℕ × ℕ)) : ∀ i n s, Plain (osRounds P i n s).1
  | _, 0, _ => rfl
  | i, n + 1, _ => plain_append
    (plain_append (plain_of_atoms (atoms_append (atoms_append (osCurS_atoms _) (osMatS_atoms _ _ _ _))
      (osMatS_atoms _ _ _ _))) rfl) (osRounds_plain P (i + 1) n _)

theorem osFinalMsg_plain (c : OsCfg) (lv : OsLv) (s : OsSt) : Plain (osFinalMsg c lv s).1 :=
  plain_append (plain_of_atoms (osCurS_atoms _)) rfl

theorem osCommit_plain (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : Plain (osCommit c lvl lv s).1 := by
  have h1 := plain_of_atoms (osCurS_atoms { s with k := s.k + 2 })
  have h2 : ∀ P b o (t : OsSt), Plain (osMatS P b o t).1 := fun P b o t ↦
    plain_of_atoms (osMatS_atoms P b o t)
  have h3 : ∀ pad k, Plain (osPad pad k).1 := fun pad k ↦ plain_of_atoms (osPad_atoms pad k)
  unfold osCommit
  simp only [Plain, List.all_append, List.all_cons, List.all_nil, List.all_map, plainS,
    plain_of_atoms (osHeap_atoms _ _), h1, h2, h3, Bool.and_true, Bool.true_and]
  simp [plainS, osKeccak]

theorem osTailRounds_plain (tch : ℕ) : ∀ j n s, Plain (osTailRounds tch j n s).1
  | _, 0, _ => rfl
  | j, n + 1, _ => plain_append (plain_append (plain_of_atoms (osCurS_atoms _)) rfl)
      (osTailRounds_plain tch (j + 1) n _)

theorem osTail_plain (c : OsCfg) (s : OsSt) : Plain (osTail c s).1 := by
  unfold osTail
  refine plain_append (plain_append (plain_of_atoms (osHeap_atoms _ _)) (osTailRounds_plain _ _ _ _)) ?_
  simp only [Plain, List.all_flatten, List.all_map, List.all_eq_true, List.mem_range]
  intro i _
  rfl

theorem osPtBlks_atoms (c : OsCfg) (pt pt1 tch : ℕ) : ∀ i n k, Atoms (osPtBlks c pt pt1 tch i n k).1
  | _, 0, _ => rfl
  | i, n + 1, k => by
    refine atoms_append ?_ (osPtBlks_atoms c pt pt1 tch (i + 1) n _)
    unfold osPtBlk; split <;> rfl

theorem osBasisRow_atoms (bd : ℕ) : ∀ cs sc after k, Atoms (osBasisRow bd cs sc after k).1
  | [], _, _, _ => rfl
  | (slot, src, inv) :: rest, sc, after, k => by
    refine atoms_append ?_ (osBasisRow_atoms bd rest _ _ _)
    unfold osBasisBlk
    dsimp only
    split_ifs <;> split <;> simp [Atoms, atomS]

theorem osBases_atoms (c : OsCfg) (tch bd ls la : ℕ) : ∀ lvl lvs k, Atoms (osBases c tch bd ls la lvl lvs k).1
  | _, [], _ => rfl
  | lvl, _ :: rest, _ => atoms_cons rfl (atoms_append (atoms_append (osBasisRow_atoms _ _ _ _ _) rfl)
      (osBases_atoms c tch bd ls la (lvl + 1) rest _))

theorem osOodFacs_atoms (sc : ℕ) : ∀ cs k, Atoms (osOodFacs sc cs k).1
  | [], _ => rfl
  | (_, _) :: rest, k => atoms_append rfl (osOodFacs_atoms (k + 5) rest _)

theorem osOodWeights_atoms (c : OsCfg) (tch : ℕ) :
    ∀ prevCols ol lvs acc k, Atoms (osOodWeights c tch prevCols ol lvs acc k).1
  | _, _, [], _, _ => rfl
  | _, _, _ :: rest, acc, _ => by
    refine atoms_append (atoms_append (atoms_cons rfl (osOodFacs_atoms _ _ _)) ?_)
      (osOodWeights_atoms c tch _ _ rest _ _)
    unfold osAcc; split <;> rfl

/-! ## A level's frames -/

/-- The name a dispatch on the rate's selector over `f` enters at level `lvl`. -/
noncomputable def selName (σ : Val) (c : OsCfg) (lvl : ℕ) (f : OsLv → String) : String :=
  ((c.lvAt lvl).map f).getD (logG (σ (.n osRate))) ""

/-- A level's state at its positions. -/
def lvPosSt (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : OsSt :=
  let f := osRounds c.plan lv.foldsOff lv.folds s
  (if lvl = c.yrLevel then osFinalMsg c lv f.2 else osCommit c lvl lv f.2).2

/-- A level before its positions: its rounds, its message, its query grind. -/
def lvPre (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt :=
  let f := osRounds c.plan lv.foldsOff lv.folds s
  let m := if lvl = c.yrLevel then osFinalMsg c lv f.2 else osCommit c lvl lv f.2
  f.1 ++ m.1 ++ [.call ("grind_check__L" ++ natStr queryGrind) [.n m.2.pow0, .n osTabs] []]

/-- A level after its positions. -/
def lvPost (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt :=
  let sq := osPositions c lvl lv (lvPosSt c lvl lv s)
  let la := if lvl = c.yrLevel then (([] : List Stmt), sq.2) else osLam sq.2
  let h := if lvl = c.yrLevel then osHsFinal c lv la.2 else osHsMid lvl lv la.2
  let q := osQueries c lvl lv h.2
  let g := if lvl = c.yrLevel then (([] : List Stmt), q.2) else osGlue lvl q.2
  la.1 ++ h.1 ++ q.1 ++ g.1

theorem osLevel_split (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osLevel c lvl lv s).1 =
      lvPre c lvl lv s ++ ((osPositions c lvl lv (lvPosSt c lvl lv s)).1 ++ lvPost c lvl lv s) := by
  simp only [osLevel, lvPre, lvPost, lvPosSt, List.append_assoc]

theorem lvPre_plain (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : Plain (lvPre c lvl lv s) := by
  refine plain_append (plain_append (osRounds_plain _ _ _ _) ?_) rfl
  split_ifs
  · exact osFinalMsg_plain _ _ _
  · exact osCommit_plain _ _ _ _

/-- The arguments and returns of the positions' dispatch at the state `s`. -/
def posCall (c : OsCfg) (lv : OsLv) (s : OsSt) : List V × List V :=
  let qp := osMatS c.plan osQpos lv.posOff s
  let wp := osMatS c.plan osQbp lv.posOff qp.2.2
  ((s.word0 :: s.fs ++ [qp.2.1, wp.2.1, osTabs]).map V.n, osRun wp.2.2.k 5)

theorem osPositions_callSF (σ : Val) (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osPositions c lvl lv s).1.filterMap (Stmt.callSF σ) =
      [(none, selName σ c lvl osPositionsName, (posCall c lv s).1, (posCall c lv s).2)] := by
  unfold osPositions
  dsimp only
  rw [List.filterMap_append, List.filterMap_append, callSF_atoms σ _ (osMatS_atoms _ _ _ _),
    callSF_atoms σ _ (osMatS_atoms _ _ _ _)]
  rfl

theorem osQueries_callSF (σ : Val) (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osQueries c lvl lv s).1.filterMap (Stmt.callSF σ) =
      [(none, selName σ c lvl (osQueriesName c lvl), (osQCallOf c lvl lv s).1,
        (osQCallOf c lvl lv s).2)] := by
  have hm : ∀ P b o (t : OsSt), (osMatS P b o t).1.filterMap (Stmt.callSF σ) = [] :=
    fun P b o t ↦ callSF_atoms σ _ (osMatS_atoms P b o t)
  unfold osQueries osQCallOf
  dsimp only
  split_ifs <;>
    simp only [List.filterMap_append, hm, List.filterMap_cons, List.filterMap_nil, Stmt.callSF,
      Main.Stmt.callS, List.nil_append, List.append_nil] <;> rfl

theorem lvPost_callSF (σ : Val) (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (lvPost c lvl lv s).filterMap (Stmt.callSF σ) =
      [(none, selName σ c lvl (osQueriesName c lvl), (osQCallOf c lvl lv (osPreQ c lvl lv s)).1,
        (osQCallOf c lvl lv (osPreQ c lvl lv s)).2)] := by
  unfold lvPost
  dsimp only
  rw [List.filterMap_append, List.filterMap_append, List.filterMap_append]
  have ha : ((if lvl = c.yrLevel then (([] : List Stmt), (osPositions c lvl lv (lvPosSt c lvl lv s)).2)
      else osLam (osPositions c lvl lv (lvPosSt c lvl lv s)).2).1).filterMap (Stmt.callSF σ) = [] := by
    split_ifs
    · rfl
    · exact callSF_atoms σ _ (osLam_atoms _)
  have hg : ∀ t : OsSt, ((if lvl = c.yrLevel then (([] : List Stmt), t) else osGlue lvl t).1).filterMap
      (Stmt.callSF σ) = [] := fun t ↦ by
    split_ifs
    · rfl
    · exact callSF_atoms σ _ (osGlue_atoms _ _)
  have hh : ∀ t : OsSt, ((if lvl = c.yrLevel then osHsFinal c lv t else osHsMid lvl lv t).1).filterMap
      (Stmt.callSF σ) = [] := fun t ↦ by
    split_ifs
    · exact callSF_atoms σ _ (osHsFinal_atoms _ _ _)
    · exact callSF_atoms σ _ (osHsMid_atoms _ _ _)
  rw [ha, hg, hh, osQueries_callSF]
  rfl

/-- A level's frames at the state `s`. -/
noncomputable def lvK (σ : Val) (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : OsLvK :=
  ⟨((lvPre c lvl lv s).filterMap Main.Stmt.callS).map (Main.mkCall σ),
    Main.mkCall σ (none, selName σ c lvl osPositionsName, (posCall c lv (lvPosSt c lvl lv s)).1,
      (posCall c lv (lvPosSt c lvl lv s)).2),
    [Main.mkCall σ (none, selName σ c lvl (osQueriesName c lvl),
      (osQCallOf c lvl lv (osPreQ c lvl lv s)).1, (osQCallOf c lvl lv (osPreQ c lvl lv s)).2)]⟩

theorem osLevel_callSF (σ : Val) (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    ((osLevel c lvl lv s).1.filterMap (Stmt.callSF σ)).map (Main.mkCall σ) = (lvK σ c lvl lv s).calls := by
  rw [osLevel_split, List.filterMap_append, List.filterMap_append, callSF_plain σ _ (lvPre_plain _ _ _ _),
    osPositions_callSF, lvPost_callSF]
  simp only [List.map_append, List.map_cons, List.map_nil, lvK, OsLvK.calls, List.cons_append,
    List.nil_append]

/-- The levels' frames from level `lvl` at the state `s`. -/
noncomputable def osLvKOf (σ : Val) (c : OsCfg) : ℕ → List OsLv → OsSt → List OsLvK
  | _, [], _ => []
  | lvl, lv :: rest, s => lvK σ c lvl lv s :: osLvKOf σ c (lvl + 1) rest (osLevel c lvl lv s).2

theorem osLvKOf_length (σ : Val) (c : OsCfg) :
    ∀ (lvl : ℕ) (lvs : List OsLv) (s : OsSt), (osLvKOf σ c lvl lvs s).length = lvs.length
  | _, [], _ => rfl
  | lvl, _ :: rest, _ => by simp [osLvKOf, osLvKOf_length σ c (lvl + 1) rest]

theorem osLevels_callSF (σ : Val) (c : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLv) (s : OsSt),
    ((osLevels c lvl lvs s).1.filterMap (Stmt.callSF σ)).map (Main.mkCall σ) =
      (osLvKOf σ c lvl lvs s).flatMap OsLvK.calls
  | _, [], _ => rfl
  | lvl, lv :: rest, s => by
    have e : (osLevels c lvl (lv :: rest) s).1 = (osLevel c lvl lv s).1 ++
        (osLevels c (lvl + 1) rest (osLevel c lvl lv s).2).1 := rfl
    rw [e, List.filterMap_append, List.map_append, osLevel_callSF, osLevels_callSF σ c (lvl + 1) rest]
    rfl

/-- **Level `i`'s frames** at the state the earlier levels leave. -/
theorem osLvKOf_get (σ : Val) (c : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLv) (s : OsSt) (i : ℕ)
    (h : i < lvs.length), (osLvKOf σ c lvl lvs s)[i]'(by rw [osLvKOf_length]; exact h) =
      lvK σ c (lvl + i) lvs[i] (osLevels c lvl (lvs.take i) s).2
  | _, [], _, _, h => absurd h (by simp)
  | lvl, lv :: rest, s, 0, _ => rfl
  | lvl, lv :: rest, s, i + 1, h => by
    have := osLvKOf_get σ c (lvl + 1) rest (osLevel c lvl lv s).2 i (by simpa using h)
    simp only [osLvKOf, List.getElem_cons_succ, List.take_succ_cons, List.getElem_cons_succ] at this ⊢
    rw [this, show lvl + 1 + i = lvl + (i + 1) by omega]
    rfl

/-! ## The closing rounds and the finish -/

/-- The dispatches into `level_residual` from level `lvl`: each `level_residual`'s name at its
level, its arguments and returns (`osResCallsL`). -/
noncomputable def resFrames (σ : Val) (c : OsCfg) (ich bd ls la lvl : ℕ) (lvs : List OsLv)
    (mats : List OsMat) (k : ℕ) : List (Option V × String × List V × List V) :=
  ((osResCallsL c ich bd ls la lvl lvs mats k).zipIdx lvl).map fun x ↦
    (none, selName σ c x.2 osResidualName, x.1.1, x.1.2)

theorem osResiduals_callSF (σ : Val) (c : OsCfg) (ich bd ls la : ℕ) :
    ∀ (lvl : ℕ) (lvs : List OsLv) (mats : List OsMat) (k : ℕ),
    (osResiduals c ich bd ls la lvl lvs mats k).1.filterMap (Stmt.callSF σ) =
      resFrames σ c ich bd ls la lvl lvs mats k
  | _, [], _, _ => rfl
  | lvl, lv :: rest, mats, k => by
    have e : (osResiduals c ich bd ls la lvl (lv :: rest) mats k).1 =
        (osResidual c ich bd ls la lvl lv mats k).1 ++ (osResiduals c ich bd ls la (lvl + 1) rest
          (osResidual c ich bd ls la lvl lv mats k).2.1 (osResidual c ich bd ls la lvl lv mats k).2.2).1 :=
      rfl
    rw [e, List.filterMap_append, osResiduals_callSF σ c ich bd ls la (lvl + 1) rest]
    have hm : ∀ P ms b o k, (osMatP P ms b o k).1.filterMap (Stmt.callSF σ) = [] :=
      fun P ms b o k ↦ callSF_atoms σ _ (osMatP_atoms P ms b o k)
    unfold osResidual
    dsimp only
    simp only [List.filterMap_append, hm, List.filterMap_cons, List.filterMap_nil, Stmt.callSF,
      Main.Stmt.callS, List.nil_append, List.cons_append]
    rfl

/-- The finish's frames: `fold_final_msg`, then the dispatches into `level_residual`. -/
theorem osFinishA_callSF (σ : Val) (c : OsCfg) (st : OsSt) (tch : ℕ) :
    (osFinishA c st tch).1.filterMap (Stmt.callSF σ) =
      (none, "fold_final_msg__L" ++ natStr c.yrLog, [.n osFmsg, .n tch], [.n st.k]) ::
        (let pt := st.k + 1
         let pts := osPtBlks c pt (pt + 1) tch 0 pointCap (pt + 2)
         let bs := osBases c tch (pts.2 + 1) (pts.2 + 3) (pts.2 + 5) 0 (c.levels.take c.yrLevel)
           (pts.2 + 6)
         resFrames σ c (bs.2 + 1) (pts.2 + 1) (pts.2 + 3) (pts.2 + 5) 0 (c.levels.take c.yrLevel)
           st.mats (bs.2 + 3)) := by
  unfold osFinishA
  dsimp only
  simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Stmt.callSF,
    Main.Stmt.callS, callSF_atoms σ _ (osPtBlks_atoms _ _ _ _ _ _ _),
    callSF_atoms σ _ (osHeap_atoms _ _), callSF_atoms σ _ (osBases_atoms _ _ _ _ _ _ _ _),
    callSF_atoms σ _ (osOodWeights_atoms _ _ _ _ _ _ _), osResiduals_callSF, List.nil_append,
    List.append_nil, List.cons_append]

/-! ## The body's frames -/

theorem osHead_callSF (σ : Val) (c : OsCfg) : (osHead c).1.filterMap (Stmt.callSF σ) = [] :=
  callSF_atoms σ _ rfl

/-- The closing rounds' statements. -/
def osTlA (c : OsCfg) : List Stmt := (osTail c (osLevels c 0 c.levels (osHead c).2).2).1

/-- The finish's frames. -/
noncomputable def finFrames (σ : Val) (c : OsCfg) : List (Option V × String × List V × List V) :=
  let tl := osTail c (osLevels c 0 c.levels (osHead c).2).2
  (osFinishA c tl.2.1 tl.2.2).1.filterMap (Stmt.callSF σ)

/-- **The body's frames**: the levels', the closing rounds', the finish's. -/
theorem osBodyA_calls (σ : Val) (c : OsCfg) :
    ((osBodyA c).filterMap (Stmt.callSF σ)).map (Main.mkCall σ) =
      (osLvKOf σ c 0 c.levels (osHead c).2).flatMap OsLvK.calls ++
        (((osTlA c).filterMap Main.Stmt.callS).map (Main.mkCall σ) ++
          (finFrames σ c).map (Main.mkCall σ)) := by
  unfold osBodyA
  dsimp only
  rw [List.filterMap_append, List.filterMap_append, List.filterMap_append, osHead_callSF,
    List.nil_append, List.map_append, List.map_append, osLevels_callSF, List.append_assoc,
    callSF_plain σ _ (osTail_plain _ _)]
  rfl

/-! ## The frames against the call statements -/

theorem dispatch_name_mem {σ : Val} {x : V} {fs : List String} {a r : List V}
    (h : DispOk σ (.dispatch x fs a r)) : fs.getD (logG (σ x)) "" ∈ fs := by
  obtain ⟨j, hj, hj64, hx⟩ := h
  rw [hx, logG_spec hj64, List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

/-- **A frame of a flat block names a callee of its call statements.** -/
theorem kid_mem_callees {σ : Val} : ∀ {pre : List Stmt}, (∀ s ∈ pre, DispOk σ s) →
    ∀ c ∈ (pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ),
      c.f ∈ (pre.filterMap B1.Stmt.calleesS).flatten
  | [], _, c, hc => by simp at hc
  | s :: pre, hdo, c, hc => by
    have ih := kid_mem_callees (pre := pre) (fun s' hs' ↦ hdo s' (List.mem_cons_of_mem _ hs')) c
    match s with
    | .atom _ =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS] at hc
      simpa [B1.Stmt.calleesS] using ih hc
    | .ret _ =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS] at hc
      simpa [B1.Stmt.calleesS] using ih hc
    | .ite .. =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS] at hc
      simpa [B1.Stmt.calleesS] using ih hc
    | .match_ .. =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS] at hc
      simpa [B1.Stmt.calleesS] using ih hc
    | .call f a r =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, List.map_cons,
        List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp [B1.Stmt.calleesS, Main.mkCall]
      · simpa [B1.Stmt.calleesS] using Or.inr (ih hc)
    | .callIf cv f a =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, List.map_cons,
        List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp [B1.Stmt.calleesS, Main.mkCall]
      · simpa [B1.Stmt.calleesS] using Or.inr (ih hc)
    | .dispatch x fs a r =>
      simp only [List.filterMap_cons, Stmt.callSF, List.map_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp only [B1.Stmt.calleesS, List.filterMap_cons, List.flatten_cons, List.mem_append]
        exact Or.inl (dispatch_name_mem (hdo _ (List.mem_cons_self ..)))
      · simpa [B1.Stmt.calleesS] using Or.inr (ih hc)

/-- **A flat block's frames' bound** is at most its call statements' costliest callees'. -/
theorem kids_bound_le {σ : Val} (fs Bk : String → ℕ) : ∀ {pre : List Stmt}, (∀ s ∈ pre, DispOk σ s) →
    (((pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ)).map fun c ↦ max (fs c.f) (Bk c.f)).sum ≤
      ((pre.filterMap B1.Stmt.calleesS).map (osCallB fs Bk)).sum
  | [], _ => by simp
  | s :: pre, hdo => by
    have ih := kids_bound_le fs Bk (pre := pre) fun s' hs' ↦ hdo s' (List.mem_cons_of_mem _ hs')
    match s with
    | .atom _ =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, B1.Stmt.calleesS]; exact ih
    | .ret _ =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, B1.Stmt.calleesS]; exact ih
    | .ite .. =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, B1.Stmt.calleesS]; exact ih
    | .match_ .. =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, B1.Stmt.calleesS]; exact ih
    | .call f a r =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, B1.Stmt.calleesS, List.map_cons,
        List.sum_cons, Main.mkCall]
      exact Nat.add_le_add (le_osCallB (List.mem_singleton_self f)) ih
    | .callIf cv f a =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, B1.Stmt.calleesS, List.map_cons,
        List.sum_cons, Main.mkCall]
      exact Nat.add_le_add (le_osCallB (List.mem_singleton_self f)) ih
    | .dispatch x fs' a r =>
      simp only [List.filterMap_cons, Stmt.callSF, B1.Stmt.calleesS, List.map_cons, List.sum_cons,
        Main.mkCall]
      exact Nat.add_le_add (le_osCallB (dispatch_name_mem (hdo _ (List.mem_cons_self ..)))) ih

theorem osBody_calleesS (c : OsCfg) :
    (osBody c).filterMap B1.Stmt.calleesS = (osBodyA c).filterMap B1.Stmt.calleesS := by
  rw [osBody_eq, List.filterMap_append]
  simp [B1.Stmt.calleesS]

/-- **`open_stacked`'s frames name its callees.** -/
theorem osKids_names {σ : Val} {c : OsCfg} (hdo : ∀ s ∈ osBodyA c, DispOk σ s) :
    ∀ c' ∈ ((osBodyA c).filterMap (Stmt.callSF σ)).map (Main.mkCall σ), c'.f ∈ osCalleeNames c :=
  fun c' hc' ↦ by
    unfold osCalleeNames osCallees
    rw [osBody_calleesS]
    exact kid_mem_callees hdo c' hc'

/-- **`open_stacked`'s frames within its calls' bound.** -/
theorem osKids_bound {σ : Val} {c : OsCfg} (fs Bk : String → ℕ) (hdo : ∀ s ∈ osBodyA c, DispOk σ s) :
    ((((osBodyA c).filterMap (Stmt.callSF σ)).map (Main.mkCall σ)).map
      fun c' ↦ max (fs c'.f) (Bk c'.f)).sum ≤ osKidsB fs Bk c := by
  unfold osKidsB osCallees
  rw [osBody_calleesS]
  exact kids_bound_le fs Bk hdo

end
end LeanVM.Guest.B1.Arm
