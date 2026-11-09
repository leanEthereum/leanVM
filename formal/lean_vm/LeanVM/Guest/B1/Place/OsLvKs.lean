/-
  LeanVM.Guest.B1.Place.OsLvKs

  open_stacked's level frames one at a time, and the kinds of the callees they name.
-/

module

public import LeanVM.Guest.B1.Place.OsNamesL
public import LeanVM.Guest.B1.Place.OsCallsOk
public import LeanVM.Guest.B1.Whir.CVals

/-!
# The levels' frames, one at a time

`osLvKOf_get`: level `j`'s frames are its block before the squeezes', the squeeze loop's and its
block after's, from the state the levels before it leave. `lvA_named`, `tail_named`: the callees
those blocks name have kinds (`OsNames`); `lvB_named`: those after the squeezes, but
`opening_queries`; `finish_named`: the finish's, but the residual loops.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir

@[expose] public section

theorem lvM_state (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (lvM c lvl lv s).2.1 = (osLevelA c lvl lv s).2.1 := by
  unfold lvM osLevelA; split_ifs <;> rfl

theorem osLvKOf_length (σ : Val) (c : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLv) (s : OsSt),
    (osLvKOf σ c lvl lvs s).length = lvs.length
  | _, [], _ => rfl
  | lvl, _ :: rest, s => by simp [osLvKOf, osLvKOf_length σ c (lvl + 1) rest]

/-- **Level `j`'s frames.** -/
theorem osLvKOf_get (σ : Val) (c : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLv) (s : OsSt) (j : ℕ)
    (hj : j < lvs.length),
    (osLvKOf σ c lvl lvs s)[j]'(by rw [osLvKOf_length]; exact hj) =
      ⟨((lvA c (lvl + j) lvs[j] (osLevels c lvl (lvs.take j) s).2).filterMap Main.Stmt.callS).map
          (Main.mkCall σ),
        Main.mkCall σ (sqCallS c (lvl + j)
          (osLevelA c (lvl + j) lvs[j] (osLevels c lvl (lvs.take j) s).2).2.1.k),
        ((lvB c (lvl + j) lvs[j] (osLevels c lvl (lvs.take j) s).2).filterMap Main.Stmt.callS).map
          (Main.mkCall σ)⟩
  | _, [], _, _, hj => absurd hj (by simp)
  | lvl, lv :: rest, s, 0, _ => by
    simp only [osLvKOf, List.getElem_cons_zero, Nat.add_zero, List.take_zero, lvM_state]
    rfl
  | lvl, lv :: rest, s, j + 1, hj => by
    have ih := osLvKOf_get σ c (lvl + 1) rest (osLevel c lvl lv s).2 j (by simpa using hj)
    simp only [osLvKOf, List.getElem_cons_succ, ih, show lvl + 1 + j = lvl + (j + 1) by omega]
    rfl

/-- A call's callee is one its block names. -/
theorem mem_cnames {σ : Val} {l : List Stmt} {c : Call}
    (h : c ∈ (l.filterMap Main.Stmt.callS).map (Main.mkCall σ)) : c.f ∈ cnames l := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  refine List.mem_map.mpr ⟨x, hx, ?_⟩
  obtain ⟨cv, f, a, r⟩ := x
  cases cv <;> rfl

/-- **The callees a level names before its squeezes have kinds.** -/
theorem lvA_named {c : OsCfg} (hN : OsNames c) {l : ℕ} (hl : l < c.levels.length) {f : String}
    (hf : f ∈ lvANames c l (lvAt c l)) : ∃ K, osKindOf f = some K := by
  simp only [lvANames, List.mem_append, List.mem_replicate, List.mem_singleton] at hf
  rcases hf with ((⟨-, rfl⟩ | hf) | rfl)
  · exact ⟨_, osKindOf_fold⟩
  · split_ifs at hf with hfin
    · rw [List.mem_singleton] at hf; subst hf; exact ⟨_, hN.fm⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl
      · exact ⟨_, osKindOf_can⟩
      · exact ⟨_, osKindOf_can⟩
      · exact ⟨_, hN.ood l hl hfin⟩
  · exact ⟨_, hN.grind l hl⟩

/-- **The tail's callees have kinds.** -/
theorem tail_named {c : OsCfg} {s : OsSt} {f : String} (hf : f ∈ cnames (osTail c s).1) :
    ∃ K, osKindOf f = some K := by
  rw [osTail_cnames, List.mem_replicate] at hf
  rw [hf.2]; exact ⟨_, osKindOf_fold⟩


theorem callS_nil_of_cnames {l : List Stmt} (h : cnames l = []) : l.filterMap Main.Stmt.callS = [] := by
  unfold cnames at h; exact List.map_eq_nil_iff.mp h

/-- The calls of a level's queries block: the row weights', the cap's, and `opening_queries`, its
sixth argument the row weights' pointer. -/
theorem osQueries_calls (c : OsCfg) (lvl : ℕ) (lv : OsLv) (lam lamN : ℕ) (s : OsSt)
    {x : Option V × String × List V × List V}
    (hx : x ∈ (osQueries c lvl lv lam lamN s).1.filterMap Main.Stmt.callS) :
    x.2.1 = "opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++ natStr (if lvl = 0 then 1 else 0) ∨
      x.2.1 = "verify_merkle_cap__L" ++ natStr lv.capDepth ∨
      (x.2.1 = osQueriesName lvl lv ∧ x.2.2.1.getD 5 (.n 0) = .n (s.k + 1) ∧
        x.2.2.1.length = 7) := by
  have hm : ∀ m b o k, (osMatP c.plan m b o k).1.filterMap Main.Stmt.callS = [] := fun m b o k ↦
    callS_nil_of_cnames (cnames_osMatP c.plan m b o k)
  simp only [osQueries, osHeap, List.filterMap_append, hm, List.filterMap_cons, Main.Stmt.callS,
    List.filterMap_nil, List.nil_append, List.append_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with (hx | hx) | hx <;> subst hx <;> simp

/-- **The call after a level's squeezes that names no kind is its `opening_queries`**, its sixth
argument the row weights' pointer. -/
theorem lvB_qcall {c : OsCfg} (hN : OsNames c) {l : ℕ} (hl : l < c.levels.length) {s : OsSt}
    {x : Option V × String × List V × List V}
    (hx : x ∈ (lvB c l (lvAt c l) s).filterMap Main.Stmt.callS) (hK : osKindOf x.2.1 = none) :
    x.2.1 = osQueriesName l (lvAt c l) ∧
      x.2.2.1.getD 5 (.n 0) = .n (wpVar c l (lvAt c l) (osLevelA c l (lvAt c l) s).2.1) ∧
      x.2.2.1.length = 7 := by
  unfold lvB at hx
  dsimp only at hx
  simp only [List.filterMap_append, List.mem_append] at hx
  have hl0 := callS_nil_of_cnames (cnames_osLamPow l ((osSqueezes c l (lvAt c l)
    (lvM c l (lvAt c l) s).2.1).2.k - 1) (lvAt c l).queries (osSqueezes c l (lvAt c l)
    (lvM c l (lvAt c l) s).2.1).2.k)
  rw [hl0] at hx
  rcases hx with (((hx | hx) | hx) | hx) | hx
  · simp at hx
  · rcases osQueries_calls _ _ _ _ _ _ hx with h | h | ⟨h1, h2, h3⟩
    · rw [h, hN.rw l hl] at hK; cases hK
    · rw [h, hN.cap l hl] at hK; cases hK
    · refine ⟨h1, ?_, h3⟩
      rw [h2, osLamPow_next, wpVar, lvM_state]
  · split_ifs at hx <;> simp [osOodGlue, Main.Stmt.callS] at hx
  · simp [Main.Stmt.callS] at hx
  · simp [osGlue, Main.Stmt.callS] at hx


theorem osResidual_calls (c : OsCfg) (ich bd ls lvl : ℕ) (lv : OsLv) (k : ℕ) :
    ∀ x ∈ (osResidual c ich bd ls lvl lv k).1.filterMap Main.Stmt.callS,
      x.2.1 = c.resLoop lvl ∧ x.2.2.1.length = 6 := by
  have hq : ∀ js h k', (osResSteps osQpos bd (lvl * ligColsCap) lv.vanish lv.logCols k js h
      k').1.filterMap Main.Stmt.callS = [] := fun js h k' ↦
    callS_nil_of_cnames (cnames_osResSteps _ _ _ _ _ _ js h k')
  have e : (osResidual c ich bd ls lvl lv k).1.filterMap Main.Stmt.callS =
      [(some (.n (k + 4 + 2)), c.resLoop lvl, [.n (k + 4 + 3), .n (k + 4 + 4), .n osQpos, .n bd,
        .n (k + 2), .n k], [])] := by
    unfold osResidual
    dsimp only
    simp only [osHeap, osLoopCall, List.filterMap_append, List.filterMap_cons,
      Main.Stmt.callS, List.filterMap_nil, hq, List.map_cons, List.map_nil]
    rfl
  rw [e]
  intro x hx
  rw [List.mem_singleton] at hx
  subst hx; exact ⟨rfl, rfl⟩

theorem osResiduals_calls (c : OsCfg) (ich bd ls : ℕ) : ∀ (lvl : ℕ) (levels : List OsLv) (k : ℕ),
    ∀ x ∈ (osResiduals c ich bd ls lvl levels k).1.filterMap Main.Stmt.callS,
      (∃ j < levels.length, x.2.1 = c.resLoop (lvl + j)) ∧ x.2.2.1.length = 6
  | _, [], _, x, hx => by simp [osResiduals] at hx
  | lvl, lv :: rest, k, x, hx => by
    have e : (osResiduals c ich bd ls lvl (lv :: rest) k).1 = (osResidual c ich bd ls lvl lv k).1 ++
        (osResiduals c ich bd ls (lvl + 1) rest (osResidual c ich bd ls lvl lv k).2).1 := rfl
    rw [e, List.filterMap_append, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨h1, h2⟩ := osResidual_calls c ich bd ls lvl lv k x hx
      exact ⟨⟨0, by simp, by rw [h1, Nat.add_zero]⟩, h2⟩
    · obtain ⟨⟨j, hj, h1⟩, h2⟩ := osResiduals_calls c ich bd ls (lvl + 1) rest _ x hx
      exact ⟨⟨j + 1, by simp; omega, by rw [h1]; congr 1; omega⟩, h2⟩

/-- **The finish's unnamed calls are its residual loops'**, of six arguments. -/
theorem finish_rescall {c : OsCfg} (hN : OsNames c) {st : OsSt} {tch : ℕ}
    {x : Option V × String × List V × List V}
    (hx : x ∈ (osFinishA c st tch).filterMap Main.Stmt.callS) (hK : osKindOf x.2.1 = none) :
    (∃ j < c.levels.length, x.2.1 = c.resLoop j) ∧ x.2.2.1.length = 6 := by
  have hp : ∀ pt pt1 i n k, (osPtBlks c pt pt1 tch i n k).1.filterMap Main.Stmt.callS = [] :=
    fun _ _ _ _ _ ↦ callS_nil_of_cnames (cnames_osPtBlks _ _ _ _ _ _ _)
  have hb : ∀ bd ls lvl levels k, (osBases c tch bd ls lvl levels k).1.filterMap Main.Stmt.callS = [] :=
    fun _ _ _ _ _ ↦ callS_nil_of_cnames (cnames_osBases _ _ _ _ _ _ _)
  have ho : ∀ pc ol levels acc k, (osOodWeights c tch pc ol levels acc k).1.filterMap
      Main.Stmt.callS = [] := fun _ _ _ _ _ ↦ callS_nil_of_cnames (cnames_osOodWeights _ _ _ _ _ _ _)
  unfold osFinishA at hx
  dsimp only at hx
  simp only [List.filterMap_append, hp, hb, ho, osHeap, List.filterMap_cons, Main.Stmt.callS,
    List.filterMap_nil, List.nil_append, List.append_nil, List.cons_append, List.mem_cons] at hx
  rcases hx with rfl | hx
  · simp only at hK; rw [hN.ffm] at hK; cases hK
  · obtain ⟨⟨j, hj, h1⟩, h2⟩ := osResiduals_calls c _ _ _ 0 c.levels _ x hx
    exact ⟨⟨j, hj, by rw [h1, Nat.zero_add]⟩, h2⟩

end
end LeanVM.Guest.B1
