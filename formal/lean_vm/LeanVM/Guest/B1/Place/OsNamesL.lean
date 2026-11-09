/-
  LeanVM.Guest.B1.Place.OsNamesL

  The names open_stacked's blocks call, in order.
-/

module

public import LeanVM.Guest.B1.Place.OsCalls
public import LeanVM.Guest.B1.Whir.CTail

/-!
# The names each block calls

`cnames l`: the callees a block's frames name, in order. A level before its squeezes calls
`opening_fold` per round, then `assert_canonical` twice and `opening_ood_point` (or the final
message), then `grind_check` (`lvA_cnames`); after them, `opening_row_weights`,
`verify_merkle_cap` and `opening_queries` (`lvB_cnames`). The tail calls `opening_fold` per
round (`osTail_cnames`); the finish calls `fold_final_msg`, then each level's residual loop
(`osFinishA_cnames`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir

@[expose] public section

/-- The callees a block's frames name, in order. -/
def cnames (l : List Stmt) : List String := (l.filterMap Main.Stmt.callS).map (·.2.1)

@[simp] theorem cnames_append (l l' : List Stmt) : cnames (l ++ l') = cnames l ++ cnames l' := by
  simp [cnames, List.filterMap_append]

@[simp] theorem cnames_nil : cnames [] = [] := rfl
@[simp] theorem cnames_cons_atom (a : Atom) (l : List Stmt) : cnames (.atom a :: l) = cnames l := rfl
@[simp] theorem cnames_cons_call (f : String) (a r : List V) (l : List Stmt) :
    cnames (.call f a r :: l) = f :: cnames l := rfl
@[simp] theorem cnames_cons_callIf (c : V) (f : String) (a : List V) (l : List Stmt) :
    cnames (.callIf c f a :: l) = f :: cnames l := rfl

@[simp] theorem cnames_map_atom {α : Type} (f : α → Atom) : ∀ (l : List α),
    cnames (l.map fun x ↦ Stmt.atom (f x)) = []
  | [] => rfl
  | _ :: l => cnames_map_atom f l

@[simp] theorem cnames_flatten : ∀ (L : List (List Stmt)), cnames L.flatten = (L.map cnames).flatten
  | [] => rfl
  | l :: L => by rw [List.flatten_cons, cnames_append, cnames_flatten L]; rfl

@[simp] theorem cnames_osMat (b o k : ℕ) : cnames (osMat b o k).1 = [] := by
  unfold osMat; split <;> rfl

theorem cnames_osFold (p off : ℕ) (s : OsSt) : cnames (osFold p off s).1 = ["opening_fold"] := by
  simp [osFold]

theorem cnames_osFolds (p : ℕ) : ∀ (n off : ℕ) (s : OsSt),
    cnames (osFolds p off n s).1 = List.replicate n "opening_fold"
  | 0, _, _ => rfl
  | n + 1, off, s => by
    have e : (osFolds p off (n + 1) s).1 = (osFold p off s).1 ++
        (osFolds p (off + 1) n (osFold p off s).2).1 := rfl
    rw [e, cnames_append, cnames_osFold, cnames_osFolds p n, List.replicate_succ]
    rfl

theorem cnames_osMatP (plan : List (ℕ × ℕ × ℕ)) (mats : List OsMat) (base off k : ℕ) :
    cnames (osMatP plan mats base off k).1 = [] := by
  unfold osMatP; split_ifs <;> rfl

theorem cnames_osCommit (plan : List (ℕ × ℕ × ℕ)) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    cnames (osCommit plan lvl lv s).1 =
      ["assert_canonical", "assert_canonical", "opening_ood_point__L" ++ natStr lv.logCols] := by
  simp [osCommit, fsPackT, fsNextT, keccakA, cnames_osMatP]

theorem cnames_osFinal (c : OsCfg) (s : OsSt) :
    cnames (osFinal c s).1 = ["opening_final_message__L" ++ natStr c.yrLen] := by
  simp [osFinal]

/-- The names a level calls before its squeezes. -/
def lvANames (c : OsCfg) (lvl : ℕ) (lv : OsLv) : List String :=
  List.replicate lv.folds "opening_fold" ++
    (if lvl = c.yrLevel then ["opening_final_message__L" ++ natStr c.yrLen]
      else ["assert_canonical", "assert_canonical", "opening_ood_point__L" ++ natStr lv.logCols]) ++
    ["grind_check__L" ++ natStr lv.grind]

theorem lvA_cnames (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    cnames (lvA c lvl lv s) = lvANames c lvl lv := by
  unfold lvA lvANames lvM
  rw [cnames_append, cnames_append, cnames_osFolds]
  split_ifs
  · rw [cnames_osFinal]; simp
  · rw [cnames_osCommit]; simp

theorem cnames_osPowSteps (x : ℕ) : ∀ (ds : List Bool) (acc k : ℕ),
    cnames (osPowSteps x ds acc k).1 = []
  | [], _, _ => rfl
  | true :: ds, acc, k => by
    simp [osPowSteps, cnames_osPowSteps x ds]
  | false :: ds, acc, k => by
    simp [osPowSteps, cnames_osPowSteps x ds]

theorem cnames_osLamPow (lvl lam n k : ℕ) : cnames (osLamPow lvl lam n k).1 = [] := by
  simp [osLamPow, cnames_osPowSteps]

/-- The names a level calls after its squeezes. -/
def lvBNames (lvl : ℕ) (lv : OsLv) : List String :=
  ["opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++ natStr (if lvl = 0 then 1 else 0),
    "verify_merkle_cap__L" ++ natStr lv.capDepth, osQueriesName lvl lv]

theorem cnames_osQueries (c : OsCfg) (lvl : ℕ) (lv : OsLv) (lam lamN : ℕ) (s : OsSt) :
    cnames (osQueries c lvl lv lam lamN s).1 = lvBNames lvl lv := by
  simp [osQueries, osHeap, lvBNames, cnames_osMatP]

theorem lvB_cnames (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    cnames (lvB c lvl lv s) = lvBNames lvl lv := by
  unfold lvB
  dsimp only
  rw [cnames_append, cnames_append, cnames_append, cnames_append, cnames_osLamPow,
    cnames_osQueries]
  split_ifs <;> simp [osOodGlue, osGlue]

theorem osTail_cnames (c : OsCfg) (s : OsSt) :
    cnames (osTail c s).1 = List.replicate (c.yrLog - 1) "opening_fold" := by
  rw [osTail_eq]
  dsimp only
  rw [cnames_append, cnames_append, cnames_osFolds]
  simp [osHeap, tailEnd, fsPackT, challengeT, keccakA]

theorem cnames_osPtBlks (c : OsCfg) (pt pt1 tch : ℕ) : ∀ (i n k : ℕ),
    cnames (osPtBlks c pt pt1 tch i n k).1 = []
  | _, 0, _ => rfl
  | i, n + 1, k => by
    have e : (osPtBlks c pt pt1 tch i (n + 1) k).1 = (osPtBlk pt pt1 i k (osPtSrc c tch i)).1 ++
        (osPtBlks c pt pt1 tch (i + 1) n (osPtBlk pt pt1 i k (osPtSrc c tch i)).2).1 := rfl
    rw [e, cnames_append, cnames_osPtBlks c pt pt1 tch (i + 1) n]
    unfold osPtBlk; split <;> simp

theorem cnames_osBasisRow (bd : ℕ) : ∀ (cs : List (ℕ × (ℕ × ℕ) × ℕ)) (sc k : ℕ),
    cnames (osBasisRow bd cs sc k).1 = []
  | [], _, _ => rfl
  | (slot, src, inv) :: rest, sc, k => by
    have e : (osBasisRow bd ((slot, src, inv) :: rest) sc k).1 = (osBasisBlk bd slot src inv sc k).1 ++
        (osBasisRow bd rest (osBasisBlk bd slot src inv sc k).2.1
          (osBasisBlk bd slot src inv sc k).2.2).1 := rfl
    rw [e, cnames_append, cnames_osBasisRow bd rest]
    unfold osBasisBlk; split <;> simp

theorem cnames_osBases (c : OsCfg) (tch bd ls : ℕ) : ∀ (lvl : ℕ) (levels : List OsLv) (k : ℕ),
    cnames (osBases c tch bd ls lvl levels k).1 = []
  | _, [], _ => rfl
  | lvl, lv :: rest, k => by
    simp [osBases, cnames_osBases c tch bd ls (lvl + 1) rest, cnames_osBasisRow]

theorem cnames_osResQ (pos bd row vo : ℕ) : ∀ (n t pe k : ℕ), cnames (osResQ pos bd row vo n t pe k).1 = []
  | 0, _, _, _ => rfl
  | n + 1, t, pe, k => by
    simp [osResQ, cnames_osResQ pos bd row vo n]

theorem cnames_osResSteps (pp bd row vo ncols mu : ℕ) : ∀ (js : List ℕ) (h k : ℕ),
    cnames (osResSteps pp bd row vo ncols mu js h k).1 = []
  | [], _, _ => rfl
  | j :: js, h, k => by
    simp [osResSteps, osResStep, osResQuery, cnames_osResQ, cnames_osResSteps pp bd row vo ncols mu js]

theorem cnames_osResidual (c : OsCfg) (ich bd ls lvl : ℕ) (lv : OsLv) (k : ℕ) :
    cnames (osResidual c ich bd ls lvl lv k).1 = [c.resLoop lvl] := by
  unfold osResidual
  dsimp only
  simp [cnames_osResSteps, osHeap, osLoopCall]

theorem cnames_osResiduals (c : OsCfg) (ich bd ls : ℕ) : ∀ (lvl : ℕ) (levels : List OsLv) (k : ℕ),
    cnames (osResiduals c ich bd ls lvl levels k).1 =
      (List.range levels.length).map fun i ↦ c.resLoop (lvl + i)
  | _, [], _ => rfl
  | lvl, lv :: rest, k => by
    have e : (osResiduals c ich bd ls lvl (lv :: rest) k).1 = (osResidual c ich bd ls lvl lv k).1 ++
        (osResiduals c ich bd ls (lvl + 1) rest (osResidual c ich bd ls lvl lv k).2).1 := rfl
    rw [e, cnames_append, cnames_osResidual, cnames_osResiduals c ich bd ls (lvl + 1) rest,
      List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero,
      List.singleton_append]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    congr 1
    omega

theorem cnames_osOodFacs (sc : ℕ) : ∀ (cs : List (ℕ × ℕ × ℕ)) (k : ℕ), cnames (osOodFacs sc cs k).1 = []
  | [], _ => rfl
  | (zo, src) :: rest, k => by
    simp [osOodFacs, cnames_osOodFacs (k + 5) rest]

theorem cnames_osOodWeights (c : OsCfg) (tch : ℕ) : ∀ (prevCols ol : ℕ) (levels : List OsLv)
    (acc : Option ℕ) (k : ℕ), cnames (osOodWeights c tch prevCols ol levels acc k).1 = []
  | _, _, [], _, _ => rfl
  | prevCols, ol, lv :: rest, acc, k => by
    have hw : cnames (osOodWeight c tch prevCols ol lv k).1 = [] := by
      simp only [osOodWeight]
      simp [cnames_osOodFacs]
    rcases acc with _ | x
    · simp [osOodWeights, hw, cnames_osOodWeights c tch lv.logCols (ol + 1) rest]
    · simp [osOodWeights, hw, cnames_osOodWeights c tch lv.logCols (ol + 1) rest,
        cnames_cons_atom]

theorem osFinishA_cnames (c : OsCfg) (st : OsSt) (tch : ℕ) :
    cnames (osFinishA c st tch) = ("fold_final_msg__L" ++ natStr c.yrLog) ::
      (List.range c.levels.length).map fun i ↦ c.resLoop i := by
  simp [osFinishA, cnames_osPtBlks, cnames_osBases, cnames_osResiduals,
    cnames_osOodWeights, osHeap]

end
end LeanVM.Guest.B1
