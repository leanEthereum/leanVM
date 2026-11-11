/-
  LeanVM.Guest.B1.Place.ValsAllocs

  open_stacked's allocation hints at the template, explicitly.
-/

module

public import LeanVM.Guest.B1.Place.OsCalls

/-!
# `open_stacked`'s allocation hints

`osAllocsV c`: the body's `HeapBuf` hints in order, each `osHeap e k` its pointer `k + 1` sized by
the value `k` (`osHeapAV k`), the point's and `point1`'s by `pointCap`: the head's ten, each
level's row weights (`lvsAllocsV`), the tail's, the finish's five. `osBodyAc_allocsV`: they are the
body's (`Main.Stmt.allocSz`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir

@[expose] public section

/-! ## `allocSz` on each statement -/

variable {d a b p x s : V} {c : E} {off n : ℕ}

@[local simp] theorem allocSzV_const : Main.Stmt.allocSz (.atom (.const d c)) = none := rfl
@[local simp] theorem allocSzV_add : Main.Stmt.allocSz (.atom (.add d a b)) = none := rfl
@[local simp] theorem allocSzV_mul : Main.Stmt.allocSz (.atom (.mul d a b)) = none := rfl
@[local simp] theorem allocSzV_copy : Main.Stmt.allocSz (.atom (.copy d s)) = none := rfl
@[local simp] theorem allocSzV_load : Main.Stmt.allocSz (.atom (.load d p off)) = none := rfl
@[local simp] theorem allocSzV_assertInK : Main.Stmt.allocSz (.atom (.assertInK a b)) = none := rfl
@[local simp] theorem allocSzV_keccak {ins outs : List V} {i o : Bool} :
    Main.Stmt.allocSz (.atom (.keccak ins outs i o)) = none := rfl
@[local simp] theorem allocSzV_limbs {ds : List V} :
    Main.Stmt.allocSz (.atom (.hint (.limbs x ds))) = none := rfl
@[local simp] theorem allocSzV_witness {st : String} {dst : Dest} :
    Main.Stmt.allocSz (.atom (.hint (.witness st dst))) = none := rfl
@[local simp] theorem allocSzV_alloc :
    Main.Stmt.allocSz (.atom (.hint (.alloc d n))) = some (d, .inl n) := rfl
@[local simp] theorem allocSzV_allocDyn :
    Main.Stmt.allocSz (.atom (.hint (.allocDyn d s))) = some (d, .inr s) := rfl
@[local simp] theorem allocSzV_call {f : String} {as rs : List V} :
    Main.Stmt.allocSz (.call f as rs) = none := rfl
@[local simp] theorem allocSzV_callIf {f : String} {as : List V} :
    Main.Stmt.allocSz (.callIf x f as) = none := rfl
@[local simp] theorem allocSzV_dispatch {fs : List String} {as rs : List V} :
    Main.Stmt.allocSz (.dispatch x fs as rs) = none := rfl

/-- A `HeapBuf` of `osHeap e k`: its pointer `k + 1`, sized by the value `k`. -/
def osHeapAV (k : ℕ) : V × (ℕ ⊕ V) := (.n (k + 1), .inr (.n k))

theorem osHeap_allocsV (e k : ℕ) : (osHeap e k).filterMap Main.Stmt.allocSz = [osHeapAV k] := by
  simp [osHeap, List.filterMap_cons, osHeapAV]

/-! ## Blocks with no hint -/

theorem osMat_allocsV (b o k : ℕ) : (osMat b o k).1.filterMap Main.Stmt.allocSz = [] := by
  unfold osMat; split_ifs <;> simp [List.filterMap_cons]

theorem osMatP_allocsV (plan : List (ℕ × ℕ × ℕ)) (mats : List OsMat) (b o k : ℕ) :
    (osMatP plan mats b o k).1.filterMap Main.Stmt.allocSz = [] := by
  unfold osMatP; split_ifs <;> simp [List.filterMap_cons]

theorem osFolds_allocsV (p : ℕ) : ∀ (n off : ℕ) (s : OsSt),
    (osFolds p off n s).1.filterMap Main.Stmt.allocSz = []
  | 0, _, _ => rfl
  | n + 1, off, s => by
    have e : (osFolds p off (n + 1) s).1 =
        (osFold p off s).1 ++ (osFolds p (off + 1) n (osFold p off s).2).1 := rfl
    rw [e, List.filterMap_append, osFolds_allocsV p n (off + 1)]
    simp [osFold, osMat_allocsV, List.filterMap_cons]

theorem osFinal_allocsV (c : OsCfg) (s : OsSt) :
    (osFinal c s).1.filterMap Main.Stmt.allocSz = [] := by
  simp [osFinal, osMat_allocsV, List.filterMap_cons]

theorem osCommit_allocsV (plan : List (ℕ × ℕ × ℕ)) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osCommit plan lvl lv s).1.filterMap Main.Stmt.allocSz = [] := by
  simp [osCommit, fsPackT, fsNextT, keccakA, osMatP_allocsV, List.filterMap_cons,
    List.filterMap_eq_nil_iff]

theorem osPositions_allocsV (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osPositions c lvl lv s).1.filterMap Main.Stmt.allocSz = [] := by
  have hpad : ∀ q j, (osPad q j).1.filterMap Main.Stmt.allocSz = [] := by
    intro q j; unfold osPad; split <;> simp [List.filterMap_cons]
  simp only [osPositions, List.filterMap_append, hpad, osMatP_allocsV]
  simp [osSqueeze0, challengeT, keccakA, List.filterMap_cons, List.filterMap_eq_nil_iff]

theorem osQueries_allocsV (c : OsCfg) (lvl : ℕ) (lv : OsLv) (lam : ℕ) (s : OsSt) :
    (osQueries c lvl lv lam s).1.filterMap Main.Stmt.allocSz = [osHeapAV s.k] := by
  simp only [osQueries, List.filterMap_append, osHeap_allocsV, osMatP_allocsV]
  simp [List.filterMap_cons]

/-! ## The levels -/

/-- A level's hint: its row weights, after its positions and `level_mus`. -/
def lvAllocsV (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List (V × (ℕ ⊕ V)) :=
  [osHeapAV ((osPositions c lvl lv (osLvA c lvl lv s).2.1).2.k + 2)]

theorem osLevel_allocsV (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osLevel c lvl lv s).1.filterMap Main.Stmt.allocSz = lvAllocsV c lvl lv s := by
  rw [osLevel_splitC]
  simp only [List.filterMap_append, osLvA, osLvB, lvAllocsV]
  split_ifs <;>
    simp [osFolds_allocsV, osFinal_allocsV, osCommit_allocsV, osPositions_allocsV,
      osQueries_allocsV, osMu, osOodGlue, osGlue, List.filterMap_cons]

/-- The levels' hints. -/
def lvsAllocsV (c : OsCfg) : ℕ → List OsLv → OsSt → List (V × (ℕ ⊕ V))
  | _, [], _ => []
  | lvl, lv :: rest, s => lvAllocsV c lvl lv s ++ lvsAllocsV c (lvl + 1) rest (osLevel c lvl lv s).2

theorem osLevels_allocsV (c : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLv) (s : OsSt),
    (osLevels c lvl lvs s).1.filterMap Main.Stmt.allocSz = lvsAllocsV c lvl lvs s
  | _, [], _ => rfl
  | lvl, lv :: rest, s => by
    have e : (osLevels c lvl (lv :: rest) s).1 = (osLevel c lvl lv s).1 ++
        (osLevels c (lvl + 1) rest (osLevel c lvl lv s).2).1 := rfl
    rw [e, List.filterMap_append, osLevel_allocsV, osLevels_allocsV c (lvl + 1) rest]
    rfl

theorem osTail_allocsV (c : OsCfg) (s : OsSt) :
    (osTail c s).1.filterMap Main.Stmt.allocSz = [osHeapAV s.k] := by
  simp only [osTail, List.filterMap_append, osHeap_allocsV, osFolds_allocsV]
  simp [fsPackT, keccakA, challengeT, List.filterMap_cons, List.filterMap_eq_nil_iff]

/-! ## The finish -/

theorem osPtBlks_allocsV (c : OsCfg) (pt pt1 tch : ℕ) : ∀ (i n k : ℕ),
    (osPtBlks c pt pt1 tch i n k).1.filterMap Main.Stmt.allocSz = []
  | _, 0, _ => rfl
  | i, n + 1, k => by
    have e : (osPtBlks c pt pt1 tch i (n + 1) k).1 = (osPtBlk pt pt1 i k (osPtSrc c tch i)).1 ++
        (osPtBlks c pt pt1 tch (i + 1) n (osPtBlk pt pt1 i k (osPtSrc c tch i)).2).1 := rfl
    rw [e, List.filterMap_append, osPtBlks_allocsV c pt pt1 tch (i + 1) n]
    unfold osPtBlk; split <;> simp [List.filterMap_cons]

theorem osBasisRow_allocsV (bd : ℕ) : ∀ (cs : List (ℕ × (ℕ × ℕ) × ℕ)) (sc k : ℕ),
    (osBasisRow bd cs sc k).1.filterMap Main.Stmt.allocSz = []
  | [], _, _ => rfl
  | (slot, src, inv) :: rest, sc, k => by
    have e : (osBasisRow bd ((slot, src, inv) :: rest) sc k).1 = (osBasisBlk bd slot src inv sc k).1 ++
        (osBasisRow bd rest (osBasisBlk bd slot src inv sc k).2.1
          (osBasisBlk bd slot src inv sc k).2.2).1 := rfl
    rw [e, List.filterMap_append, osBasisRow_allocsV bd rest]
    unfold osBasisBlk; split_ifs <;> simp [List.filterMap_cons]

theorem osBases_allocsV (c : OsCfg) (tch bd ls : ℕ) : ∀ (lvl : ℕ) (levels : List OsLv) (k : ℕ),
    (osBases c tch bd ls lvl levels k).1.filterMap Main.Stmt.allocSz = []
  | _, [], _ => rfl
  | lvl, lv :: rest, k => by
    simp only [osBases, List.filterMap_cons, List.filterMap_append, osBasisRow_allocsV,
      osBases_allocsV c tch bd ls (lvl + 1) rest]
    simp

theorem osResidual_allocsV (c : OsCfg) (ich bd ls lvl : ℕ) (lv : OsLv) (mats : List OsMat)
    (k : ℕ) : (osResidual c ich bd ls lvl lv mats k).1.filterMap Main.Stmt.allocSz = [] := by
  simp only [osResidual, List.filterMap_append, osMatP_allocsV]
  simp [List.filterMap_cons]

theorem osResiduals_allocsV (c : OsCfg) (ich bd ls : ℕ) : ∀ (lvl : ℕ) (levels : List OsLv)
    (mats : List OsMat) (k : ℕ),
    (osResiduals c ich bd ls lvl levels mats k).1.filterMap Main.Stmt.allocSz = []
  | _, [], _, _ => rfl
  | lvl, lv :: rest, mats, k => by
    simp only [osResiduals, List.filterMap_append, osResidual_allocsV,
      osResiduals_allocsV c ich bd ls (lvl + 1) rest]
    rfl

theorem osOodFacs_allocsV (sc : ℕ) : ∀ (cs : List (ℕ × ℕ × ℕ)) (k : ℕ),
    (osOodFacs sc cs k).1.filterMap Main.Stmt.allocSz = []
  | [], _ => rfl
  | (zo, src) :: rest, k => by
    simp only [osOodFacs, List.filterMap_append, osOodFacs_allocsV (k + 5) rest]
    simp [List.filterMap_cons]

theorem osOodWeights_allocsV (c : OsCfg) (tch : ℕ) : ∀ (levels : List OsLv) (prevCols ol : ℕ)
    (acc : Option ℕ) (k : ℕ),
    (osOodWeights c tch prevCols ol levels acc k).1.filterMap Main.Stmt.allocSz = []
  | [], _, _, _, _ => rfl
  | lv :: rest, prevCols, ol, acc, k => by
    cases acc <;>
      simp [osOodWeights, osOodWeight, osOodFacs_allocsV, osOodWeights_allocsV c tch rest,
        List.filterMap_cons]

/-- The finish's points. -/
abbrev finPtsV (c : OsCfg) (st : OsSt) (tch : ℕ) : List Stmt × ℕ :=
  osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap (st.k + 1 + 2)

/-- The finish's basis rows. -/
abbrev finBsV (c : OsCfg) (st : OsSt) (tch : ℕ) : List Stmt × ℕ :=
  osBases c tch ((finPtsV c st tch).2 + 1) ((finPtsV c st tch).2 + 3) 0 c.levels
    ((finPtsV c st tch).2 + 4)

/-- The finish's hints: the point, `point1`, `basis_d`, the scales, the inner sums. -/
def finAllocsV (c : OsCfg) (st : OsSt) (tch : ℕ) : List (V × (ℕ ⊕ V)) :=
  [(.n (st.k + 1), .inl pointCap), (.n (st.k + 1 + 1), .inl pointCap),
    osHeapAV (finPtsV c st tch).2, osHeapAV ((finPtsV c st tch).2 + 2),
    osHeapAV (finBsV c st tch).2]

theorem osFinA_allocsV (c : OsCfg) (st : OsSt) (tch : ℕ) :
    (osFinA c st tch).filterMap Main.Stmt.allocSz = finAllocsV c st tch := by
  simp only [osFinA, finAllocsV, List.filterMap_append, osPtBlks_allocsV, osHeap_allocsV,
    osBases_allocsV, osResiduals_allocsV, osOodWeights_allocsV]
  simp [List.filterMap_cons]

/-! ## The body -/

/-- The head's hints. -/
def headAllocsV : List (V × (ℕ ⊕ V)) :=
  [osHeapAV 13, osHeapAV 15, osHeapAV 17, osHeapAV 19, osHeapAV 21, osHeapAV 23, osHeapAV 25,
    osHeapAV 27, osHeapAV 157, osHeapAV 159]

theorem osWinTabs_allocsV : osWinTabs.filterMap Main.Stmt.allocSz = [] := by
  refine List.filterMap_eq_nil_iff.mpr fun a ha ↦ ?_
  simp only [osWinTabs, List.mem_flatten, List.mem_map, List.mem_range] at ha
  obtain ⟨_, ⟨i, -, rfl⟩, ha⟩ := ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl <;> rfl

theorem osHead_allocsV (c : OsCfg) : (osHead c).1.filterMap Main.Stmt.allocSz = headAllocsV := by
  simp only [osHead, List.filterMap_append, osHeap_allocsV, osWinTabs_allocsV]
  simp [List.filterMap_cons, headAllocsV]

/-- **The body's hints.** -/
def osAllocsV (c : OsCfg) : List (V × (ℕ ⊕ V)) :=
  headAllocsV ++ lvsAllocsV c 0 c.levels (osHead c).2 ++ [osHeapAV (osLvSt c).k] ++
    finAllocsV c (osTlSt c).2.1 (osTlSt c).2.2

theorem osBodyAc_allocsV (c : OsCfg) :
    (osBodyAc c).filterMap Main.Stmt.allocSz = osAllocsV c := by
  rw [osBodyAc, List.filterMap_append, List.filterMap_append, List.filterMap_append,
    osHead_allocsV, osLevels_allocsV, osTail_allocsV, osFinA_allocsV]
  rfl

end
end LeanVM.Guest.B1
