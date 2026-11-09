/-
  LeanVM.Guest.B1.Whir.CFinBases

  The levels' basis rows, honestly: every coordinate's coefficient, its `d` and the scale.
-/

module

public import LeanVM.Guest.B1.Whir.CFinPt
public import LeanVM.Guest.B1.Whir.Bases

/-!
# The basis rows, honestly

`osBasisBlk_complete`: one coordinate, its challenge `cv ≠ 0` (no zero challenge) and its
vanishing inverse not zero: the coefficient `b = cv·inv`, `d = (1 + cv)/b` (stored), the scale
times `b`. `osBasisRow_complete`: a row. `osBases_complete`: every level's row, its scale stored.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- One coordinate's values. -/
def basisVals (inv : ℕ) (cv scv : E) : List E :=
  if inv = 1 then [cv, word 1 0 0, word 1 0 0 + cv, (word 1 0 0 + cv) / cv, scv * cv]
  else [cv, word inv 0 0, cv * word inv 0 0, word 1 0 0, word 1 0 0 + cv,
    (word 1 0 0 + cv) / (cv * word inv 0 0), scv * (cv * word inv 0 0)]

theorem osBasisBlk_next (bd slot : ℕ) (src : ℕ × ℕ) (inv sc k : ℕ) :
    k < (osBasisBlk bd slot src inv sc k).2.1 ∧
      (osBasisBlk bd slot src inv sc k).2.1 + 1 = (osBasisBlk bd slot src inv sc k).2.2 := by
  unfold osBasisBlk; split_ifs <;> simp

/-- **One coordinate, honestly.** -/
theorem osBasisBlk_complete {bd slot : ℕ} {src : ℕ × ℕ} {inv sc k : ℕ} {cv : E} (σ : Val)
    (hsrc : src.1 < k) (hsc : sc < k) (hbd : bd < k) (hcv : cv ≠ 0) (hinv : word inv 0 0 ≠ 0)
    (hc : LoadHolds rd (σ (.n src.1)) src.2 cv)
    (hd : LoadHolds rd (σ (.n bd)) slot ((1 + cv) / (cv * word inv 0 0))) :
    BlkF C rd σ k (osBasisBlk bd slot src inv sc k).2.2
      (fun j ↦ (basisVals inv cv (σ (.n sc))).getD (j - k) 0) (osBasisBlk bd slot src inv sc k).1
      (fun σ' ↦ σ' (.n (osBasisBlk bd slot src inv sc k).2.1) = σ (.n sc) * (cv * word inv 0 0) ∧
        AgreeBelow k σ σ') := by
  intro σ' ha hr
  have es := ha _ hsrc; have esc := ha _ hsc; have ebd := ha _ hbd
  refine ⟨?_, ?_, ha⟩
  · by_cases h1 : inv = 1
    · subst h1
      have V : ∀ j < 5, σ' (.n (k + j)) = (basisVals 1 cv (σ (.n sc))).getD j 0 := fun j hj ↦ by
        rw [hr _ (by omega) (by simp [osBasisBlk]; omega)]; simp only [Nat.add_sub_cancel_left]
      have v0 := V 0 (by omega); have v1 := V 1 (by omega); have v2 := V 2 (by omega)
      have v3 := V 3 (by omega); have v4 := V 4 (by omega)
      simp only [basisVals, ↓reduceIte, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4
      simp only [osBasisBlk, ↓reduceIte, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      rw [word_one] at v1 v2 v3 hd
      rw [mul_one] at hd
      refine ⟨by rw [v0, es]; exact hc, by rw [v1, word_one], by rw [v2, v1, v0],
        by rw [v2, v3, v0, div_mul_cancel₀ _ hcv], by rw [v3, ebd]; exact hd,
        by rw [v4, esc, v0]⟩
    · have hc1 : (inv = 1) = False := eq_false h1
      have V : ∀ j < 7, σ' (.n (k + j)) = (basisVals inv cv (σ (.n sc))).getD j 0 := fun j hj ↦ by
        rw [hr _ (by omega) (by simp [osBasisBlk, hc1]; omega)]; simp only [Nat.add_sub_cancel_left]
      have v0 := V 0 (by omega); have v1 := V 1 (by omega); have v2 := V 2 (by omega)
      have v3 := V 3 (by omega); have v4 := V 4 (by omega); have v5 := V 5 (by omega)
      have v6 := V 6 (by omega)
      simp only [basisVals, hc1, ↓reduceIte, List.getD_cons_zero, List.getD_cons_succ,
        Nat.add_zero] at v0 v1 v2 v3 v4 v5 v6
      simp only [osBasisBlk, hc1, ↓reduceIte, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      have hb : cv * word inv 0 0 ≠ 0 := mul_ne_zero hcv hinv
      rw [word_one] at v3 v4 v5
      refine ⟨by rw [v0, es]; exact hc, v1, by rw [v2, v0, v1], by rw [v3, word_one],
        by rw [v4, v3, v0], by rw [v4, v5, v2, div_mul_cancel₀ _ hb], by rw [v5, ebd]; exact hd,
        by rw [v6, esc, v2]⟩
  · by_cases h1 : inv = 1
    · subst h1
      have := hr (k + 4) (by omega) (by simp [osBasisBlk])
      simp only [osBasisBlk, ↓reduceIte] at this ⊢
      rw [this]
      simp [basisVals, word_one]
    · have hc1 : (inv = 1) = False := eq_false h1
      have := hr (k + 6) (by omega) (by simp [osBasisBlk, hc1])
      simp only [osBasisBlk, hc1, ↓reduceIte] at this ⊢
      rw [this]
      simp [basisVals, h1]

/-- The values of a basis row. -/
def rowF (bd : ℕ) : List (ℕ × (ℕ × ℕ) × ℕ) → ℕ → ℕ → Val → (ℕ → E) → ℕ → E
  | [], _, _, _, _ => fun _ ↦ 0
  | (slot, src, inv) :: rest, sc, k, σ, cv =>
    seqF σ k (osBasisBlk bd slot src inv sc k).2.2
      (fun j ↦ (basisVals inv (cv 0) (σ (.n sc))).getD (j - k) 0)
      fun σ1 ↦ rowF bd rest (osBasisBlk bd slot src inv sc k).2.1
        (osBasisBlk bd slot src inv sc k).2.2 σ1 (fun t ↦ cv (t + 1))

theorem osBasisRow_k (bd : ℕ) : ∀ (cs : List (ℕ × (ℕ × ℕ) × ℕ)) (sc k : ℕ),
    k ≤ (osBasisRow bd cs sc k).2.2 ∧ (sc < k → (osBasisRow bd cs sc k).2.1 < (osBasisRow bd cs sc k).2.2)
  | [], sc, k => ⟨le_rfl, fun h ↦ h⟩
  | (slot, src, inv) :: rest, sc, k => by
    simp only [osBasisRow]
    have h1 := osBasisBlk_next bd slot src inv sc k
    have h2 := osBasisRow_k bd rest (osBasisBlk bd slot src inv sc k).2.1
      (osBasisBlk bd slot src inv sc k).2.2
    exact ⟨by omega, fun _ ↦ h2.2 (by omega)⟩

/-- **A basis row, honestly.** -/
theorem osBasisRow_complete {bd : ℕ} : ∀ (cs : List (ℕ × (ℕ × ℕ) × ℕ)) (sc k : ℕ) (σ : Val)
    (cv : ℕ → E), sc < k → bd < k →
    (∀ t < cs.length, (cs.getD t coordD).2.1.1 < k ∧ cv t ≠ 0 ∧
      word (cs.getD t coordD).2.2 0 0 ≠ 0 ∧
      LoadHolds rd (σ (.n (cs.getD t coordD).2.1.1)) (cs.getD t coordD).2.1.2 (cv t) ∧
      LoadHolds rd (σ (.n bd)) (cs.getD t coordD).1
        ((1 + cv t) / (cv t * word (cs.getD t coordD).2.2 0 0))) →
    BlkF C rd σ k (osBasisRow bd cs sc k).2.2 (rowF bd cs sc k σ cv) (osBasisRow bd cs sc k).1
      (fun σ' ↦ σ' (.n (osBasisRow bd cs sc k).2.1) =
        σ (.n sc) * ∏ t ∈ Finset.range cs.length, (cv t * word (cs.getD t coordD).2.2 0 0) ∧
        AgreeBelow k σ σ')
  | [], sc, k, σ, cv, hsc, _, _ => by
    simp only [osBasisRow]
    exact BlkF.nil fun σ' ha ↦ ⟨by simp [ha sc hsc], ha⟩
  | (slot, src, inv) :: rest, sc, k, σ, cv, hsc, hbd, h => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := h 0 (by simp)
    simp only [List.getD_cons_zero] at h1 h2 h3 h4 h5
    have hA := osBasisBlk_complete (C := C) (rd := rd) (bd := bd) (slot := slot) (src := src)
      (inv := inv) (sc := sc) (k := k) σ h1 hsc hbd h2 h3 h4 h5
    have hn := osBasisBlk_next bd slot src inv sc k
    have hk := (osBasisRow_k bd rest (osBasisBlk bd slot src inv sc k).2.1
      (osBasisBlk bd slot src inv sc k).2.2).1
    simp only [osBasisRow]
    refine BlkF.then (k1 := (osBasisBlk bd slot src inv sc k).2.2) (by omega) hk hA
      fun σ1 _ ⟨hs1, ha1⟩ ↦ ?_
    refine BlkF.mono (osBasisRow_complete rest _ _ σ1 (fun t ↦ cv (t + 1)) (by omega) (by omega)
      fun t ht ↦ ?_) fun σ' ⟨hs, ha2⟩ ↦ ⟨?_, fun i hi ↦ (ha2 i (by omega)).trans (ha1 i hi)⟩
    · obtain ⟨g1, g2, g3, g4, g5⟩ := h (t + 1) (by simp; omega)
      simp only [List.getD_cons_succ] at g1 g2 g3 g4 g5
      exact ⟨by omega, g2, g3, by rw [ha1 _ g1]; exact g4, by rw [ha1 _ hbd]; exact g5⟩
    · rw [hs, hs1, List.length_cons, Finset.prod_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      ring

theorem BlkF.snoc {σ : Val} {k k' : ℕ} {f : ℕ → E} {ss : List Stmt} {Out : Val → Prop} {a : Atom}
    (h : BlkF C rd σ k k' f ss Out) (ha : ∀ σ', Out σ' → a.Holds rd σ') :
    BlkF C rd σ k k' f (ss ++ [.atom a]) Out := fun σ' hag hr ↦
  ⟨allOk_append.mpr ⟨(h σ' hag hr).1, allOk_cons.mpr ⟨ha σ' (h σ' hag hr).2, allOk_nil⟩⟩,
    (h σ' hag hr).2⟩

/-- A word loaded into the next value. -/
theorem load_complete {k p off : ℕ} {v : E} (σ : Val) (hp : p < k) (h : LoadHolds rd (σ (.n p)) off v) :
    BlkF C rd σ k (k + 1) (fun _ ↦ v) [.atom (.load (.n k) (.n p) off)]
      (fun σ' ↦ σ' (.n k) = v ∧ AgreeBelow k σ σ') := by
  intro σ' ha hr
  have v0 := hr k le_rfl (by omega)
  refine ⟨allOk_cons.mpr ⟨?_, allOk_nil⟩, v0, ha⟩
  show LoadHolds rd (σ' (.n p)) off (σ' (.n k))
  rw [v0, ha p hp]; exact h

/-- What a level's basis row needs: its scalar, its coordinates' sources and `d`, its scale. -/
def BasisMem (rd : Reader) (σ : Val) (c : OsCfg) (tch bd ls L : ℕ) (lv : OsLv) (β : E) (X : ℕ → E) :
    Prop :=
  LoadHolds rd (σ (.n osBetas)) L β ∧
    (∀ t < lv.prefixLen + c.yrLog, X t ≠ 0 ∧ invW lv t ≠ 0 ∧
      LoadHolds rd (σ (.n (coordSrc tch lv t).1)) (coordSrc tch lv t).2 (X t) ∧
      LoadHolds rd (σ (.n bd)) (L * ligColsCap + t) ((1 + X t) / (X t * invW lv t))) ∧
    LoadHolds rd (σ (.n ls)) L (β * ∏ t ∈ Finset.range (lv.prefixLen + c.yrLog), (X t * invW lv t))

/-- The values of the levels' basis rows. -/
def basesF (c : OsCfg) (tch bd : ℕ) (β : ℕ → E) (X : ℕ → ℕ → E) :
    ℕ → List OsLv → ℕ → Val → ℕ → E
  | lvl, lv :: rest, k, σ =>
    seqF σ k (osBasisRow bd (osBasisCoords c tch lvl lv) k (k + 1)).2.2
      (seqF σ k (k + 1) (fun _ ↦ β lvl)
        fun σ1 ↦ rowF bd (osBasisCoords c tch lvl lv) k (k + 1) σ1 (X lvl))
      fun σ2 ↦ basesF c tch bd β X (lvl + 1) rest
        (osBasisRow bd (osBasisCoords c tch lvl lv) k (k + 1)).2.2 σ2
  | _, [], _, _ => fun _ ↦ 0

theorem osBases_k (c : OsCfg) (tch bd ls : ℕ) : ∀ (lvl : ℕ) (levels : List OsLv) (k : ℕ),
    k ≤ (osBases c tch bd ls lvl levels k).2
  | _, [], _ => le_rfl
  | lvl, lv :: rest, k => by
    simp only [osBases]
    have := (osBasisRow_k bd (osBasisCoords c tch lvl lv) k (k + 1)).1
    have := osBases_k c tch bd ls (lvl + 1) rest (osBasisRow bd (osBasisCoords c tch lvl lv) k (k + 1)).2.2
    omega

/-- **Every level's basis row, honestly.** -/
theorem osBases_complete {c : OsCfg} {tch bd ls : ℕ} (β : ℕ → E) (X : ℕ → ℕ → E) :
    ∀ (levels : List OsLv) (lvl k : ℕ) (σ : Val), tch < k → bd < k → ls < k → 164 ≤ k →
      (∀ i (hi : i < levels.length), BasisMem rd σ c tch bd ls (lvl + i) levels[i] (β (lvl + i))
        (X (lvl + i))) →
      BlkF C rd σ k (osBases c tch bd ls lvl levels k).2 (basesF c tch bd β X lvl levels k σ)
        (osBases c tch bd ls lvl levels k).1 (fun σ' ↦ AgreeBelow k σ σ')
  | [], lvl, k, σ, _, _, _, _, _ => by
    simp only [osBases]; exact BlkF.nil fun _ h ↦ h
  | lv :: rest, lvl, k, σ, htch, hbd, hls, hk, h => by
    obtain ⟨hb, hx, hs⟩ := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hb hx hs
    set cs := osBasisCoords c tch lvl lv with hcs
    set r := osBasisRow bd cs k (k + 1) with hr
    have hlen : cs.length = lv.prefixLen + c.yrLog := by simp [hcs, osBasisCoords]
    have hrk1 : k + 1 ≤ r.2.2 := (osBasisRow_k bd cs k (k + 1)).1
    have hrk2 : r.2.1 < r.2.2 := (osBasisRow_k bd cs k (k + 1)).2 (by omega)
    have e : osBases c tch bd ls lvl (lv :: rest) k = ((.atom (.load (.n k) (.n osBetas) lvl) :: r.1 ++
        [.atom (.load (.n r.2.1) (.n ls) lvl)]) ++ (osBases c tch bd ls (lvl + 1) rest r.2.2).1,
        (osBases c tch bd ls (lvl + 1) rest r.2.2).2) := rfl
    rw [e]
    dsimp only
    rw [basesF]
    have hkr : r.2.2 ≤ (osBases c tch bd ls (lvl + 1) rest r.2.2).2 :=
      osBases_k c tch bd ls (lvl + 1) rest r.2.2
    refine BlkF.then (k1 := r.2.2) (OutA := fun σ' ↦ AgreeBelow k σ σ') (by omega) hkr ?_
      fun σ2 _ ha2 ↦ ?_
    · rw [← List.singleton_append]
      have hrow : BlkF C rd σ k r.2.2
          (seqF σ k (k + 1) (fun _ ↦ β lvl) fun σ1 ↦ rowF bd cs k (k + 1) σ1 (X lvl))
          ([.atom (.load (.n k) (.n osBetas) lvl)] ++ r.1)
          (fun σ' ↦ σ' (.n r.2.1) = β lvl *
            ∏ t ∈ Finset.range cs.length, (X lvl t * word (cs.getD t coordD).2.2 0 0) ∧
            AgreeBelow k σ σ') := by
        refine BlkF.then (k1 := k + 1) (by omega) (by omega)
          (load_complete σ (by unfold osBetas; omega) hb) fun σ1 _ ⟨h1, ha1⟩ ↦ ?_
        refine BlkF.mono (osBasisRow_complete cs k (k + 1) σ1 (X lvl) (by omega) (by omega)
          fun t ht ↦ ?_) fun σ' ⟨hv, ha2⟩ ↦ ⟨by rw [hv, h1], fun i hi ↦
            (ha2 i (by omega)).trans (ha1 i hi)⟩
        rw [hlen] at ht
        rw [osBasisCoords_getD ht]
        obtain ⟨g1, g2, g3, g4⟩ := hx t ht
        have hsrc : (coordSrc tch lv t).1 < k := by
          unfold coordSrc; split_ifs <;> simp only <;> first | (unfold osFch; omega) | omega
        refine ⟨by simp only; omega, g1, g2, by rw [ha1 _ hsrc]; exact g3,
          by rw [ha1 _ hbd]; exact g4⟩
      refine BlkF.mono (BlkF.snoc hrow fun σ' ⟨hv, ha⟩ ↦ ?_) fun σ' h ↦ h.2
      show LoadHolds rd (σ' (.n ls)) lvl (σ' (.n r.2.1))
      rw [hv, ha ls hls, hlen]
      rwa [Finset.prod_congr rfl fun t ht ↦ by
        rw [osBasisCoords_getD (Finset.mem_range.mp ht)]]
    · refine BlkF.mono (osBases_complete β X rest (lvl + 1) r.2.2 σ2 (by omega) (by omega)
        (by omega) (by omega) fun i hi ↦ ?_) fun σ' ha3 i hi ↦ (ha3 i (by omega)).trans (ha2 i hi)
      have := h (i + 1) (by simp; omega)
      rw [show lvl + (i + 1) = lvl + 1 + i by ring] at this
      obtain ⟨g1, g2, g3⟩ := this
      have e2 : ∀ v, v < k → σ2 (.n v) = σ (.n v) := fun v hv ↦ ha2 v (by omega)
      refine ⟨by rw [e2 _ (by unfold osBetas; omega)]; exact g1, fun t ht ↦ ?_,
        by rw [e2 _ hls]; exact g3⟩
      obtain ⟨q1, q2, q3, q4⟩ := g2 t ht
      have hsrc : (coordSrc tch rest[i] t).1 < k := by
        unfold coordSrc; split_ifs <;> simp only <;> first | (unfold osFch; omega) | omega
      exact ⟨q1, q2, by rw [e2 _ hsrc]; exact q3, by rw [e2 _ hbd]; exact q4⟩

end
end LeanVM.Guest.B1.Whir
