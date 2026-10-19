/-
  LeanVM.Guest.B1.Whir.StackedC12

  `open_stacked`'s point and basis rows at their honest values.
-/

module

public import LeanVM.Guest.B1.Whir.StackedC11

/-!
# The point and the basis rows, honestly (TRIAGE #36)

`osPoint_complete`: the point's buffer and its entries; `osBases_complete`: every level's basis
row, each coordinate's challenge `c` read, `1 + c` and `c·inverse` stored.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The point -/

/-- The point's values from its pointer: the pointer `ptv`, then entry `i` at `ent i`. -/
def osPtVals (ptv : E) (ent : ℕ → E) : List E := ptv :: (List.range 42).map ent

theorem os_length_ptVals (ptv : E) (ent : ℕ → E) : (osPtVals ptv ent).length = 43 := by simp [osPtVals]

/-- **The point** at its honest values: entry `i` read from its source (or zero) and stored. -/
theorem osPoint_complete {nFolds lane yrLog tch k : ℕ} {ptv : E} {ent : ℕ → E} {kret : List E → Prop}
    (hsrc : ∀ i < 42, ∀ b o, osPtSrc nFolds lane yrLog tch i = some (b, o) → LoadHolds rd (σ (.n b)) o (ent i))
    (hz : ∀ i < 42, osPtSrc nFolds lane yrLog tch i = none → ent i = 0)
    (hpt : ∀ i < 42, LoadHolds rd ptv i (ent i))
    (hv : ∀ j < 43, σ (.n (k + j)) = (osPtVals ptv ent).getD j 0) :
    Stmt.HoldsList C rd σ (osPoint nFolds lane yrLog tch k) True kret := by
  have h0 : σ (.n k) = ptv := by simpa [osPtVals] using hv 0 (by omega)
  have he : ∀ i < 42, σ (.n (k + 1 + i)) = ent i := fun i hi => by
    rw [Nat.add_assoc, hv _ (by omega), Nat.add_comm 1 i]
    simp [osPtVals, List.getD_eq_getElem?_getD, hi]
  unfold osPoint
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and]
  rw [holdsList_range_flatten _ _ (fun i => by unfold osPtBlk; split <;> rfl)]
  refine ⟨fun i hi => ?_, trivial⟩
  unfold osPtBlk
  split
  · rename_i b o hs
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    rw [he i hi, h0]
    exact ⟨hsrc i hi b o hs, hpt i hi⟩
  · rename_i hs
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    rw [he i hi, h0, hz i hi hs, word_zero]
    exact ⟨rfl, by rw [← hz i hi hs]; exact hpt i hi⟩

/-! ## The basis rows -/

/-- A basis coordinate's values from its first: the challenge `c`, `1`, `1 + c`, and when the
inverse is not `1`, the inverse and `c·inverse`. -/
def osBasisBlkVals (c : E) (inv : ℕ) : List E :=
  if inv = 1 then [c, 1, 1 + c] else [c, 1, 1 + c, word inv 0 0, c * word inv 0 0]

/-- A basis row's values, coordinate `it`'s challenge `cf it`. -/
def osBasisRowVals (cf : ℕ × (ℕ × ℕ) × ℕ → E) (items : List (ℕ × (ℕ × ℕ) × ℕ)) : List E :=
  (items.map fun it => osBasisBlkVals (cf it) it.2.2).flatten

/-- What the memory holds of a basis coordinate: its challenge at its source, `1 + c` and
`c·inverse` at its slot. -/
def OsBasisMem (rd : Reader) (σ : Val) (bav bbv : E) (c : E) (it : ℕ × (ℕ × ℕ) × ℕ) : Prop :=
  LoadHolds rd (σ (.n it.2.1.1)) it.2.1.2 c ∧ LoadHolds rd bav it.1 (1 + c) ∧
    LoadHolds rd bbv it.1 (c * eOfNat it.2.2)

theorem osBasisRow_complete {ba bb : ℕ} {bav bbv : E} (hba : σ (.n ba) = bav) (hbb : σ (.n bb) = bbv)
    {cf : ℕ × (ℕ × ℕ) × ℕ → E} {kret : List E → Prop} :
    ∀ (items : List (ℕ × (ℕ × ℕ) × ℕ)) (k : ℕ), (∀ it ∈ items, OsBasisMem rd σ bav bbv (cf it) it) →
      (∀ j < (osBasisRowVals cf items).length, σ (.n (k + j)) = (osBasisRowVals cf items).getD j 0) →
      Stmt.HoldsList C rd σ (osBasisRow ba bb items k).1 True kret ∧
        (osBasisRow ba bb items k).2 = k + (osBasisRowVals cf items).length
  | [], k, _, _ => ⟨trivial, by simp [osBasisRow, osBasisRowVals]⟩
  | (slot, src, inv) :: rest, k, hm, hv => by
    have hvs : osBasisRowVals cf ((slot, src, inv) :: rest) =
        osBasisBlkVals (cf (slot, src, inv)) inv ++ osBasisRowVals cf rest := rfl
    rw [hvs] at hv ⊢
    obtain ⟨g1, g2⟩ := os_look_app hv
    obtain ⟨m0, m1, m2⟩ := hm _ List.mem_cons_self
    simp only at m0 m1 m2
    set c := cf (slot, src, inv)
    have hblk : Stmt.HoldsList C rd σ (osBasisBlk ba bb slot src inv k).1 True kret ∧
        (osBasisBlk ba bb slot src inv k).2 = k + (osBasisBlkVals c inv).length := by
      unfold osBasisBlk osBasisBlkVals at *
      by_cases hi : inv = 1
      · simp only [hi, ↓reduceIte] at g1 ⊢
        have e0 := g1 0 (by simp); have e1 := g1 1 (by simp); have e2 := g1 2 (by simp)
        simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1 e2
        refine ⟨?_, rfl⟩
        simp only [List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
        refine ⟨by rw [e0]; exact m0, by rw [e1, word_one], by rw [e2, e1, e0], by rw [e2, hba]; exact m1,
          by rw [e0, hbb]; rw [hi, eOfNat_one, mul_one] at m2; exact m2⟩
      · simp only [hi, ↓reduceIte] at g1 ⊢
        have e0 := g1 0 (by simp); have e1 := g1 1 (by simp); have e2 := g1 2 (by simp)
        have e3 := g1 3 (by simp); have e4 := g1 4 (by simp)
        simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1 e2 e3 e4
        refine ⟨?_, rfl⟩
        simp only [List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
        refine ⟨by rw [e0]; exact m0, by rw [e1, word_one], by rw [e2, e1, e0], by rw [e2, hba]; exact m1, e3,
          by rw [e4, e0, e3], by rw [e4, hbb, word_eOfNat]; exact m2⟩
    obtain ⟨hb1, hb2⟩ := hblk
    obtain ⟨hr1, hr2⟩ := osBasisRow_complete hba hbb rest (osBasisBlk ba bb slot src inv k).2 (fun it hit => hm it (List.mem_cons_of_mem _ hit))
      (fun j hj => by rw [hb2]; exact g2 j hj)
    refine ⟨?_, ?_⟩
    · simp only [osBasisRow, holdsList_append]
      have hnr : Stmt.noRetList (osBasisBlk ba bb slot src inv k).1 = true := by
        unfold osBasisBlk; split <;> rfl
      exact (holdsList_noRet _ hnr _ _).mpr ⟨hb1, hr1⟩
    · simp only [osBasisRow]
      rw [hr2, hb2, List.length_append]; ring

/-- The basis rows' values of the levels `lvl ..`. -/
def osBasesVals (yrLog tch : ℕ) (cf : ℕ × (ℕ × ℕ) × ℕ → E) : ℕ → List OsLvl → List E
  | _, [] => []
  | lvl, lv :: rest => osBasisRowVals cf (osBasisCoords yrLog tch lvl lv) ++ osBasesVals yrLog tch cf (lvl + 1) rest

/-- **Every level's basis row** at its honest values. -/
theorem osBases_complete {yrLog tch ba bb : ℕ} {bav bbv : E} (hba : σ (.n ba) = bav) (hbb : σ (.n bb) = bbv)
    {cf : ℕ × (ℕ × ℕ) × ℕ → E} {kret : List E → Prop} :
    ∀ (lvl : ℕ) (lvs : List OsLvl) (k : ℕ),
      (∀ i < lvs.length, ∀ it ∈ osBasisCoords yrLog tch (lvl + i) (lvs.getD i default),
        OsBasisMem rd σ bav bbv (cf it) it) →
      (∀ j < (osBasesVals yrLog tch cf lvl lvs).length,
        σ (.n (k + j)) = (osBasesVals yrLog tch cf lvl lvs).getD j 0) →
      Stmt.HoldsList C rd σ (osBases yrLog tch ba bb lvl lvs k).1 True kret ∧
        (osBases yrLog tch ba bb lvl lvs k).2 = k + (osBasesVals yrLog tch cf lvl lvs).length
  | _, [], k, _, _ => ⟨trivial, by simp [osBases, osBasesVals]⟩
  | lvl, lv :: rest, k, hm, hv => by
    have hvs : osBasesVals yrLog tch cf lvl (lv :: rest) =
        osBasisRowVals cf (osBasisCoords yrLog tch lvl lv) ++ osBasesVals yrLog tch cf (lvl + 1) rest := rfl
    rw [hvs] at hv ⊢
    obtain ⟨g1, g2⟩ := os_look_app hv
    obtain ⟨hr1, hr2⟩ := osBasisRow_complete (kret := kret) hba hbb _ k
      (fun it hit => hm 0 (by simp) it (by simpa using hit)) g1
    obtain ⟨hs1, hs2⟩ := osBases_complete hba hbb (lvl + 1) rest (osBasisRow ba bb (osBasisCoords yrLog tch lvl lv) k).2
      (fun i hi it hit => hm (i + 1) (by simp; omega) it (by
        simpa [show lvl + 1 + i = lvl + (i + 1) by ring] using hit))
      (fun j hj => by rw [hr2]; exact g2 j hj)
    have hnr : ∀ items k', Stmt.noRetList (osBasisRow ba bb items k').1 = true := by
      intro items
      induction items with
      | nil => intro; rfl
      | cons it rest ih =>
        intro k'
        obtain ⟨slot, src, inv⟩ := it
        simp only [osBasisRow, noRetList_append, ih, Bool.and_true]
        unfold osBasisBlk; split <;> rfl
    refine ⟨?_, ?_⟩
    · simp only [osBases, holdsList_append]
      exact (holdsList_noRet _ (hnr _ _) _ _).mpr ⟨hr1, hs1⟩
    · simp only [osBases]
      rw [hs2, hr2, List.length_append]; ring

end
end LeanVM.Guest.B1
