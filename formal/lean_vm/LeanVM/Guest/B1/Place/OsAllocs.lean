/-
  LeanVM.Guest.B1.Place.OsAllocs

  open_stacked's allocation hints, explicitly.
-/

module

public import LeanVM.Guest.B1.Place.OsLay
public import LeanVM.Guest.B1.Whir.Flatness

/-!
# `open_stacked`'s allocation hints

`osAllocsOf c`: the body's `HeapBuf` hints in order, each `osHeap e k` its pointer `k + 1` sized by
the value `k` (`osHeapA k`), the point's and `point1`'s by `pointCap`: the head's twelve, each
level's squeeze run and row weights (`lvsAllocs`), the tail's, the finish's five and each level's
residual chain (`resAllocs`). `osBodyA_allocs`: they are the body's (`Main.Stmt.allocSz`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir

@[expose] public section

/-! ## `allocSz` on each statement -/

variable {d a b p x s : V} {c : E} {off n : ℕ}

@[local simp] theorem allocSz_const : Main.Stmt.allocSz (.atom (.const d c)) = none := rfl
@[local simp] theorem allocSz_add : Main.Stmt.allocSz (.atom (.add d a b)) = none := rfl
@[local simp] theorem allocSz_mul : Main.Stmt.allocSz (.atom (.mul d a b)) = none := rfl
@[local simp] theorem allocSz_copy : Main.Stmt.allocSz (.atom (.copy d s)) = none := rfl
@[local simp] theorem allocSz_load : Main.Stmt.allocSz (.atom (.load d p off)) = none := rfl
@[local simp] theorem allocSz_assertInK : Main.Stmt.allocSz (.atom (.assertInK a b)) = none := rfl
@[local simp] theorem allocSz_keccak {ins outs : List V} {i o : Bool} :
    Main.Stmt.allocSz (.atom (.keccak ins outs i o)) = none := rfl
@[local simp] theorem allocSz_limbs {ds : List V} :
    Main.Stmt.allocSz (.atom (.hint (.limbs x ds))) = none := rfl
@[local simp] theorem allocSz_witness {st : String} {dst : Dest} :
    Main.Stmt.allocSz (.atom (.hint (.witness st dst))) = none := rfl
@[local simp] theorem allocSz_alloc : Main.Stmt.allocSz (.atom (.hint (.alloc d n))) = some (d, .inl n) :=
  rfl
@[local simp] theorem allocSz_allocDyn :
    Main.Stmt.allocSz (.atom (.hint (.allocDyn d s))) = some (d, .inr s) := rfl
@[local simp] theorem allocSz_call {f : String} {as rs : List V} :
    Main.Stmt.allocSz (.call f as rs) = none := rfl
@[local simp] theorem allocSz_callIf {f : String} {as : List V} :
    Main.Stmt.allocSz (.callIf x f as) = none := rfl


/-- A `HeapBuf` of `osHeap e k`: its pointer `k + 1`, sized by the value `k`. -/
def osHeapA (k : ℕ) : V × (ℕ ⊕ V) := (.n (k + 1), .inr (.n k))

theorem osHeap_allocs (e k : ℕ) : (osHeap e k).filterMap Main.Stmt.allocSz = [osHeapA k] := by
  simp [osHeap, List.filterMap_cons, osHeapA]

/-! ## Blocks with no hint -/

theorem osMat_allocs (b o k : ℕ) : (osMat b o k).1.filterMap Main.Stmt.allocSz = [] := by
  unfold osMat; split_ifs <;> simp [List.filterMap_cons]

theorem osFolds_allocs (p : ℕ) : ∀ (n off : ℕ) (s : OsSt),
    (osFolds p off n s).1.filterMap Main.Stmt.allocSz = []
  | 0, _, _ => rfl
  | n + 1, off, s => by
    have e : (osFolds p off (n + 1) s).1 = (osFold p off s).1 ++ (osFolds p (off + 1) n (osFold p off s).2).1 :=
      rfl
    rw [e, List.filterMap_append, osFolds_allocs p n (off + 1)]
    simp [osFold, osMat_allocs, List.filterMap_cons]

theorem osFinal_allocs (c : OsCfg) (s : OsSt) : (osFinal c s).1.filterMap Main.Stmt.allocSz = [] := by
  simp [osFinal, osMat_allocs, List.filterMap_cons]

theorem osMatP_allocs (plan : List (ℕ × ℕ × ℕ)) (mats : List OsMat) (b o k : ℕ) :
    (osMatP plan mats b o k).1.filterMap Main.Stmt.allocSz = [] := by
  unfold osMatP; split_ifs <;> simp [List.filterMap_cons]

theorem osCommit_allocs (plan : List (ℕ × ℕ × ℕ)) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osCommit plan lvl lv s).1.filterMap Main.Stmt.allocSz = [] := by
  simp [osCommit, fsPackT, fsNextT, keccakA, osMatP_allocs, List.filterMap_cons,
    List.filterMap_eq_nil_iff]

theorem osPowSteps_allocs (x : ℕ) : ∀ (ds : List Bool) (acc k : ℕ),
    (osPowSteps x ds acc k).1.filterMap Main.Stmt.allocSz = []
  | [], _, _ => rfl
  | true :: ds, acc, k => by simp [osPowSteps, osPowSteps_allocs x ds, List.filterMap_cons]
  | false :: ds, acc, k => by simp [osPowSteps, osPowSteps_allocs x ds, List.filterMap_cons]

theorem osLamPow_allocs (lvl lam n k : ℕ) :
    (osLamPow lvl lam n k).1.filterMap Main.Stmt.allocSz = [] := by
  simp [osLamPow, osPowSteps_allocs, List.filterMap_cons]

theorem osSqueezes_allocs (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osSqueezes c lvl lv s).1.filterMap Main.Stmt.allocSz = [osHeapA s.k] := by
  have hpad : (osPad s.pad (s.k + 14)).1.filterMap Main.Stmt.allocSz = [] := by
    unfold osPad; split <;> simp [List.filterMap_cons]
  simp only [osSqueezes, List.filterMap_append, hpad, osHeap_allocs]
  simp [osLoopCall, osSqueeze0, challengeT, keccakA, List.filterMap_cons, List.filterMap_eq_nil_iff]

theorem osQueries_allocs (c : OsCfg) (lvl : ℕ) (lv : OsLv) (lam lamN : ℕ) (s : OsSt) :
    (osQueries c lvl lv lam lamN s).1.filterMap Main.Stmt.allocSz = [osHeapA s.k] := by
  simp only [osQueries, List.filterMap_append, osHeap_allocs, osMatP_allocs]
  simp [List.filterMap_cons]

/-- A level's hints: its squeeze run and its row weights. -/
def lvAllocs (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List (V × (ℕ ⊕ V)) :=
  [osHeapA (osLevelA c lvl lv s).2.1.k,
    osHeapA (osLamPow lvl ((osSqueezes c lvl lv (osLevelA c lvl lv s).2.1).2.k - 1) lv.queries
      (osSqueezes c lvl lv (osLevelA c lvl lv s).2.1).2.k).2.2]

theorem osLevel_allocs (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osLevel c lvl lv s).1.filterMap Main.Stmt.allocSz = lvAllocs c lvl lv s := by
  rw [osLevel_split]
  simp only [List.filterMap_append, osLevelA, osLevelB, lvAllocs]
  split_ifs <;>
    simp [osFolds_allocs, osFinal_allocs, osCommit_allocs, osSqueezes_allocs, osLamPow_allocs,
      osQueries_allocs, osOodGlue, osGlue, List.filterMap_cons]

/-- The levels' hints. -/
def lvsAllocs (c : OsCfg) : ℕ → List OsLv → OsSt → List (V × (ℕ ⊕ V))
  | _, [], _ => []
  | lvl, lv :: rest, s => lvAllocs c lvl lv s ++ lvsAllocs c (lvl + 1) rest (osLevel c lvl lv s).2

theorem osLevels_allocs (c : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLv) (s : OsSt),
    (osLevels c lvl lvs s).1.filterMap Main.Stmt.allocSz = lvsAllocs c lvl lvs s
  | _, [], _ => rfl
  | lvl, lv :: rest, s => by
    have e : (osLevels c lvl (lv :: rest) s).1 = (osLevel c lvl lv s).1 ++
        (osLevels c (lvl + 1) rest (osLevel c lvl lv s).2).1 := rfl
    rw [e, List.filterMap_append, osLevel_allocs, osLevels_allocs c (lvl + 1) rest]
    rfl

theorem osTail_allocs (c : OsCfg) (s : OsSt) :
    (osTail c s).1.filterMap Main.Stmt.allocSz = [osHeapA s.k] := by
  simp only [osTail, List.filterMap_append, osHeap_allocs, osFolds_allocs]
  simp [fsPackT, keccakA, challengeT, List.filterMap_cons, List.filterMap_eq_nil_iff]

/-! ## The finish -/

theorem osPtBlks_allocs (c : OsCfg) (pt pt1 tch : ℕ) : ∀ (i n k : ℕ),
    (osPtBlks c pt pt1 tch i n k).1.filterMap Main.Stmt.allocSz = []
  | _, 0, _ => rfl
  | i, n + 1, k => by
    have e : (osPtBlks c pt pt1 tch i (n + 1) k).1 = (osPtBlk pt pt1 i k (osPtSrc c tch i)).1 ++
        (osPtBlks c pt pt1 tch (i + 1) n (osPtBlk pt pt1 i k (osPtSrc c tch i)).2).1 := rfl
    rw [e, List.filterMap_append, osPtBlks_allocs c pt pt1 tch (i + 1) n]
    unfold osPtBlk; split <;> simp [List.filterMap_cons]

theorem osBasisRow_allocs (bd : ℕ) : ∀ (cs : List (ℕ × (ℕ × ℕ) × ℕ)) (sc k : ℕ),
    (osBasisRow bd cs sc k).1.filterMap Main.Stmt.allocSz = []
  | [], _, _ => rfl
  | (slot, src, inv) :: rest, sc, k => by
    have e : (osBasisRow bd ((slot, src, inv) :: rest) sc k).1 = (osBasisBlk bd slot src inv sc k).1 ++
        (osBasisRow bd rest (osBasisBlk bd slot src inv sc k).2.1
          (osBasisBlk bd slot src inv sc k).2.2).1 := rfl
    rw [e, List.filterMap_append, osBasisRow_allocs bd rest]
    unfold osBasisBlk; split_ifs <;> simp [List.filterMap_cons]

theorem osBases_allocs (c : OsCfg) (tch bd ls : ℕ) : ∀ (lvl : ℕ) (levels : List OsLv) (k : ℕ),
    (osBases c tch bd ls lvl levels k).1.filterMap Main.Stmt.allocSz = []
  | _, [], _ => rfl
  | lvl, lv :: rest, k => by
    simp only [osBases, List.filterMap_cons, List.filterMap_append, osBasisRow_allocs,
      osBases_allocs c tch bd ls (lvl + 1) rest]
    simp

theorem osResQ_allocs (pos bd row vo : ℕ) : ∀ (n t pe k : ℕ),
    (osResQ pos bd row vo n t pe k).1.filterMap Main.Stmt.allocSz = []
  | 0, _, _, _ => rfl
  | n + 1, t, pe, k => by
    simp only [osResQ, List.filterMap_append, osResQ_allocs pos bd row vo n]
    simp [List.filterMap_cons]

theorem osResSteps_allocs (pp bd row vo ncols mu : ℕ) : ∀ (js : List ℕ) (h k : ℕ),
    (osResSteps pp bd row vo ncols mu js h k).1.filterMap Main.Stmt.allocSz = []
  | [], _, _ => rfl
  | j :: js, h, k => by
    simp only [osResSteps, osResStep, osResQuery, List.filterMap_append, osResQ_allocs,
      osResSteps_allocs pp bd row vo ncols mu js]
    simp [List.filterMap_cons]

theorem osResidual_allocs (c : OsCfg) (ich bd ls lvl : ℕ) (lv : OsLv) (k : ℕ) :
    (osResidual c ich bd ls lvl lv k).1.filterMap Main.Stmt.allocSz = [osHeapA (k + 1)] := by
  simp only [osResidual, List.filterMap_append, osHeap_allocs, osResSteps_allocs]
  simp [osLoopCall, List.filterMap_cons]

/-- The residual chains' hints. -/
def resAllocs (c : OsCfg) (ich bd ls : ℕ) : ℕ → List OsLv → ℕ → List (V × (ℕ ⊕ V))
  | _, [], _ => []
  | lvl, lv :: rest, k =>
    osHeapA (k + 1) :: resAllocs c ich bd ls (lvl + 1) rest (osResidual c ich bd ls lvl lv k).2

theorem osResiduals_allocs (c : OsCfg) (ich bd ls : ℕ) : ∀ (lvl : ℕ) (levels : List OsLv) (k : ℕ),
    (osResiduals c ich bd ls lvl levels k).1.filterMap Main.Stmt.allocSz = resAllocs c ich bd ls lvl levels k
  | _, [], _ => rfl
  | lvl, lv :: rest, k => by
    simp only [osResiduals, List.filterMap_append, osResidual_allocs,
      osResiduals_allocs c ich bd ls (lvl + 1) rest]
    rfl

theorem osOodFacs_allocs (sc : ℕ) : ∀ (cs : List (ℕ × ℕ × ℕ)) (k : ℕ),
    (osOodFacs sc cs k).1.filterMap Main.Stmt.allocSz = []
  | [], _ => rfl
  | (zo, src) :: rest, k => by
    simp only [osOodFacs, List.filterMap_append, osOodFacs_allocs (k + 5) rest]
    simp [List.filterMap_cons]

theorem osOodWeights_allocs (c : OsCfg) (tch : ℕ) : ∀ (levels : List OsLv) (prevCols ol : ℕ)
    (acc : Option ℕ) (k : ℕ), (osOodWeights c tch prevCols ol levels acc k).1.filterMap Main.Stmt.allocSz = []
  | [], _, _, _, _ => rfl
  | lv :: rest, prevCols, ol, acc, k => by
    cases acc <;>
      simp [osOodWeights, osOodWeight, osOodFacs_allocs, osOodWeights_allocs c tch rest,
        List.filterMap_cons]

/-- The finish's hints. -/
def finAllocs (c : OsCfg) (st : OsSt) (tch : ℕ) : List (V × (ℕ ⊕ V)) :=
  let pts := osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap (st.k + 1 + 2)
  let bs := osBases c tch (pts.2 + 1) (pts.2 + 3) 0 c.levels (pts.2 + 4)
  [(.n (st.k + 1), .inl pointCap), (.n (st.k + 1 + 1), .inl pointCap), osHeapA pts.2,
    osHeapA (pts.2 + 2), osHeapA bs.2] ++
    resAllocs c (bs.2 + 1) (pts.2 + 1) (pts.2 + 3) 0 c.levels (bs.2 + 3)

theorem osFinishA_allocs (c : OsCfg) (st : OsSt) (tch : ℕ) :
    (osFinishA c st tch).filterMap Main.Stmt.allocSz = finAllocs c st tch := by
  simp only [osFinishA, finAllocs, List.filterMap_append, osPtBlks_allocs, osHeap_allocs,
    osBases_allocs, osResiduals_allocs, osOodWeights_allocs]
  simp [List.filterMap_cons]

/-! ## The body -/

/-- The head's hints. -/
def headAllocs : List (V × (ℕ ⊕ V)) :=
  (List.range 10).map (fun t ↦ osHeapA (12 + 2 * t)) ++ [osHeapA 160, osHeapA 162]

theorem osWinTabs_allocs : osWinTabs.filterMap Main.Stmt.allocSz = [] := by
  refine List.filterMap_eq_nil_iff.mpr fun a ha ↦ ?_
  simp only [osWinTabs, List.mem_flatten, List.mem_map, List.mem_range] at ha
  obtain ⟨_, ⟨i, -, rfl⟩, ha⟩ := ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl <;> rfl

theorem osHead_allocs (c : OsCfg) : (osHead c).1.filterMap Main.Stmt.allocSz = headAllocs := by
  simp only [osHead, List.filterMap_append, osHeap_allocs, osWinTabs_allocs]
  simp [List.filterMap_cons, headAllocs, osHeapA, List.range_succ]

/-- **The body's hints.** -/
def osAllocsOf (c : OsCfg) : List (V × (ℕ ⊕ V)) :=
  headAllocs ++ lvsAllocs c 0 c.levels (osHead c).2 ++ [osHeapA (osLvSt c).k] ++
    finAllocs c (osTlSt c).2.1 (osTlSt c).2.2

theorem osBodyA_allocs (c : OsCfg) : (osBodyA c).filterMap Main.Stmt.allocSz = osAllocsOf c := by
  rw [osBodyA, List.filterMap_append, List.filterMap_append, List.filterMap_append, osHead_allocs,
    osLevels_allocs, osTail_allocs, osFinishA_allocs]
  rfl

end
end LeanVM.Guest.B1
