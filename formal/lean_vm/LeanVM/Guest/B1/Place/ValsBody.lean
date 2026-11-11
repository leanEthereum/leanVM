/-
  LeanVM.Guest.B1.Place.ValsBody

  open_stacked's body values at its buffers' pointers, the positions' pointers and the queries'
  row weights.
-/

module

public import LeanVM.Guest.B1.Place.ValsAllocs
public import LeanVM.Guest.B1.Place.ValsSpec

/-!
# The body's values the lift reads

Each pointer is a value function's entry: `lvF_wpV` (a level's row weights, the pointer its
`HeapBuf` makes and its `level_queries` call reads), `lvF_posV` (a level's positions pointer, the
first materialization of its positions' block), `lvsF_atV` (level `j`'s values in the levels'),
and the head's, the tail's and the finish's (`osBodyF_*V`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

theorem seqF_ltV {σ : Val} {k k1 : ℕ} {fA : ℕ → E} {fB : Val → ℕ → E} {i : ℕ} (h : i < k1) :
    seqF σ k k1 fA fB i = fA i := by
  simp only [seqF, h, ↓reduceIte]

theorem seqF_geV {σ : Val} {k k1 : ℕ} {fA : ℕ → E} {fB : Val → ℕ → E} {i : ℕ} (h : k1 ≤ i) :
    seqF σ k k1 fA fB i = fB (fill σ k k1 fA) i := by
  simp only [seqF, show ¬ i < k1 by omega, ↓reduceIte]

/-! ## Bounds -/

theorem osLvA_kV (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) :
    st.k ≤ (osLvA c lvl lv st).2.1.k := by
  have h := osFolds_k osFch lv.folds lv.foldsOff st
  unfold osLvA
  dsimp only
  split_ifs
  · unfold osFinal; dsimp only
    have := osMat_next (osFolds osFch lv.foldsOff lv.folds st).2.cb
      (osFolds osFch lv.foldsOff lv.folds st).2.co
      (osFolds osFch lv.foldsOff lv.folds st).2.k
    omega
  · unfold osCommit; dsimp only; omega

theorem osLvB_kV (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) :
    (osPositions c lvl lv st).2.k + 11 ≤ (osLvB c lvl lv st).2.k := by
  set S2 : OsSt := { (osPositions c lvl lv st).2 with k := (osPositions c lvl lv st).2.k + 2 }
    with hS2
  have hs2 : S2.k = (osPositions c lvl lv st).2.k + 2 := rfl
  have h2 := qPts_k c lv S2
  have h3 := osQueries_k c lvl lv ((osPositions c lvl lv st).2.k - 1) S2
  unfold osLvB
  split_ifs
  · show _ ≤ (osQueries c lvl lv ((osPositions c lvl lv st).2.k - 1) S2).2.1 + 1 + 8
    omega
  · show _ ≤ (osQueries c lvl lv ((osPositions c lvl lv st).2.k - 1) S2).2.1 + 13 + 1 + 8
    omega

/-- The value of a level's row weights' pointer. -/
abbrev wpVarV (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) : ℕ :=
  (osPositions c lvl lv (osLvA c lvl lv st).2.1).2.k + 3

theorem osLevel_wpV (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) :
    (osLvA c lvl lv st).2.1.k + 20 ≤ (osPositions c lvl lv (osLvA c lvl lv st).2.1).2.k ∧
      wpVarV c lvl lv st + 8 ≤ (osLevel c lvl lv st).2.k := by
  have h1 := osPositions_k_le c lvl lv (osLvA c lvl lv st).2.1
  have h2 := osLvB_kV c lvl lv (osLvA c lvl lv st).2.1
  rw [osLevel_splitC]
  exact ⟨h1, by unfold wpVarV; omega⟩

theorem osLevel_kV (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) :
    st.k ≤ (osLevel c lvl lv st).2.k := by
  have h1 := osLevel_wpV c lvl lv st
  have h2 := osLvA_kV c lvl lv st
  unfold wpVarV at h1
  omega

theorem osLevels_kV (c : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLv) (st : OsSt),
    st.k ≤ (osLevels c lvl lvs st).2.k
  | _, [], _ => le_rfl
  | lvl, lv :: rest, st => by
    have e : (osLevels c lvl (lv :: rest) st).2 =
        (osLevels c (lvl + 1) rest (osLevel c lvl lv st).2).2 := rfl
    rw [e]
    exact le_trans (osLevel_kV c lvl lv st) (osLevels_kV c (lvl + 1) rest _)

theorem osLevels_k_getV (c : OsCfg) : ∀ (lvs : List OsLv) (lvl : ℕ) (st : OsSt) (j : ℕ)
    (hj : j < lvs.length),
    (osLevel c (lvl + j) lvs[j] (osLevels c lvl (lvs.take j) st).2).2.k ≤
      (osLevels c lvl lvs st).2.k
  | [], _, _, _, hj => absurd hj (by simp)
  | lv :: rest, lvl, st, 0, _ => by
    show (osLevel c (lvl + 0) lv st).2.k ≤ (osLevels c (lvl + 1) rest (osLevel c lvl lv st).2).2.k
    exact osLevels_kV c (lvl + 1) rest _
  | lv :: rest, lvl, st, j + 1, hj => by
    have hj' : j < rest.length := by simpa using hj
    have := osLevels_k_getV c rest (lvl + 1) (osLevel c lvl lv st).2 j hj'
    show (osLevel c (lvl + (j + 1)) rest[j]
        (osLevels c (lvl + 1) (rest.take j) (osLevel c lvl lv st).2).2).2.k ≤
      (osLevels c (lvl + 1) rest (osLevel c lvl lv st).2).2.k
    rwa [show lvl + (j + 1) = lvl + 1 + j by omega]

/-! ## A level's values -/

/-- A level's part after its grinding check: the row weights' pointer in its values. -/
theorem lvBFinF_wpV (c : OsCfg) (lvl : ℕ) (lv : OsLv) (sA : OsSt) (σ : Val) (last : List E)
    (wp r0 r1 sum lamN ic0 ic2 : E) :
    lvBFinF c lvl lv sA σ last wp r0 r1 sum lamN ic0 ic2 ((osPositions c lvl lv sA).2.k + 3) = wp := by
  have h2 := qPts_k c lv { (osPositions c lvl lv sA).2 with k := (osPositions c lvl lv sA).2.k + 2 }
  have h3 := osQueries_k c lvl lv ((osPositions c lvl lv sA).2.k - 1)
    { (osPositions c lvl lv sA).2 with k := (osPositions c lvl lv sA).2.k + 2 }
  have h1 := osPositions_k_le c lvl lv sA
  dsimp only at h2 h3
  unfold lvBFinF
  dsimp only
  rw [seqF_geV (by omega), seqF_geV (by omega), seqF_ltV (by omega)]
  unfold queriesF
  simp only [show (osPositions c lvl lv sA).2.k + 3 ≠ (osPositions c lvl lv sA).2.k + 2 by omega,
    show (osPositions c lvl lv sA).2.k + 3 = (osPositions c lvl lv sA).2.k + 2 + 1 by omega,
    ↓reduceIte]

theorem lvBNonF_wpV (c : OsCfg) (lvl : ℕ) (lv : OsLv) (sA : OsSt) (σ : Val) (last : List E)
    (wp r0 r1 sum lamN ic0 ic2 y oc0 oc2 : E) :
    lvBNonF c lvl lv sA σ last wp r0 r1 sum lamN ic0 ic2 y oc0 oc2
      ((osPositions c lvl lv sA).2.k + 3) = wp := by
  have h2 := qPts_k c lv { (osPositions c lvl lv sA).2 with k := (osPositions c lvl lv sA).2.k + 2 }
  have h3 := osQueries_k c lvl lv ((osPositions c lvl lv sA).2.k - 1)
    { (osPositions c lvl lv sA).2 with k := (osPositions c lvl lv sA).2.k + 2 }
  have h1 := osPositions_k_le c lvl lv sA
  dsimp only at h2 h3
  unfold lvBNonF
  dsimp only
  rw [seqF_geV (by omega), seqF_geV (by omega), seqF_ltV (by omega)]
  unfold queriesF
  simp only [show (osPositions c lvl lv sA).2.k + 3 ≠ (osPositions c lvl lv sA).2.k + 2 by omega,
    show (osPositions c lvl lv sA).2.k + 3 = (osPositions c lvl lv sA).2.k + 2 + 1 by omega,
    ↓reduceIte]

theorem lvBFinF_szV (c : OsCfg) (lvl : ℕ) (lv : OsLv) (sA : OsSt) (σ : Val) (last : List E)
    (wp r0 r1 sum lamN ic0 ic2 : E) :
    lvBFinF c lvl lv sA σ last wp r0 r1 sum lamN ic0 ic2 ((osPositions c lvl lv sA).2.k + 2) =
      gw c.maxIl := by
  have h2 := qPts_k c lv { (osPositions c lvl lv sA).2 with k := (osPositions c lvl lv sA).2.k + 2 }
  have h3 := osQueries_k c lvl lv ((osPositions c lvl lv sA).2.k - 1)
    { (osPositions c lvl lv sA).2 with k := (osPositions c lvl lv sA).2.k + 2 }
  have h1 := osPositions_k_le c lvl lv sA
  dsimp only at h2 h3
  unfold lvBFinF
  dsimp only
  rw [seqF_geV (by omega), seqF_geV (by omega), seqF_ltV (by omega)]
  unfold queriesF
  simp only [↓reduceIte]

theorem lvBNonF_szV (c : OsCfg) (lvl : ℕ) (lv : OsLv) (sA : OsSt) (σ : Val) (last : List E)
    (wp r0 r1 sum lamN ic0 ic2 y oc0 oc2 : E) :
    lvBNonF c lvl lv sA σ last wp r0 r1 sum lamN ic0 ic2 y oc0 oc2
      ((osPositions c lvl lv sA).2.k + 2) = gw c.maxIl := by
  have h2 := qPts_k c lv { (osPositions c lvl lv sA).2 with k := (osPositions c lvl lv sA).2.k + 2 }
  have h3 := osQueries_k c lvl lv ((osPositions c lvl lv sA).2.k - 1)
    { (osPositions c lvl lv sA).2 with k := (osPositions c lvl lv sA).2.k + 2 }
  have h1 := osPositions_k_le c lvl lv sA
  dsimp only at h2 h3
  unfold lvBNonF
  dsimp only
  rw [seqF_geV (by omega), seqF_geV (by omega), seqF_ltV (by omega)]
  unfold queriesF
  simp only [↓reduceIte]

/-- **A level's row weights' size** in its values. -/
theorem lvF_szV (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) (σ : Val) (D : LvDat) :
    Whir.lvF c lvl lv st σ D ((osPositions c lvl lv (osLvA c lvl lv st).2.1).2.k + 2) =
      gw c.maxIl := by
  have h1 := (osLevel_wpV c lvl lv st).1
  unfold Whir.lvF
  split_ifs
  · unfold lvFinF
    rw [seqF_geV (by omega)]
    exact lvBFinF_szV _ _ _ _ _ _ _ _ _ _ _ _ _
  · unfold lvNonF
    rw [seqF_geV (by omega)]
    exact lvBNonF_szV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **A level's row weights' pointer** in its values. -/
theorem lvF_wpV (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) (σ : Val) (D : LvDat) :
    Whir.lvF c lvl lv st σ D (wpVarV c lvl lv st) = D.wp := by
  have h1 := (osLevel_wpV c lvl lv st).1
  unfold Whir.lvF
  split_ifs
  · unfold lvFinF
    rw [seqF_geV (by unfold wpVarV; omega)]
    exact lvBFinF_wpV _ _ _ _ _ _ _ _ _ _ _ _ _
  · unfold lvNonF
    rw [seqF_geV (by unfold wpVarV; omega)]
    exact lvBNonF_wpV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem lvBFinF_posV (c : OsCfg) (lvl : ℕ) (lv : OsLv) (sA : OsSt) (σ : Val) (last : List E)
    (wp r0 r1 sum lamN ic0 ic2 : E) (h0 : lv.posOff ≠ 0) :
    lvBFinF c lvl lv sA σ last wp r0 r1 sum lamN ic0 ic2 (sA.k + 1) = σ (.n osQpos) * gw lv.posOff := by
  have h1 := osPositions_k_le c lvl lv sA
  have hm : matLen lv.posOff = 2 := by simp [matLen, h0]
  unfold lvBFinF
  dsimp only
  rw [seqF_ltV (by omega)]
  simp [posSegs, segLookup, hm]

theorem lvBNonF_posV (c : OsCfg) (lvl : ℕ) (lv : OsLv) (sA : OsSt) (σ : Val) (last : List E)
    (wp r0 r1 sum lamN ic0 ic2 y oc0 oc2 : E) (h0 : lv.posOff ≠ 0) :
    lvBNonF c lvl lv sA σ last wp r0 r1 sum lamN ic0 ic2 y oc0 oc2 (sA.k + 1) =
      σ (.n osQpos) * gw lv.posOff := by
  have h1 := osPositions_k_le c lvl lv sA
  have hm : matLen lv.posOff = 2 := by simp [matLen, h0]
  unfold lvBNonF
  dsimp only
  rw [seqF_ltV (by omega)]
  simp [posSegs, segLookup, hm]

/-- **A level's positions pointer** in its values, at a nonzero offset: the base at the
valuation the positions start from. -/
theorem lvF_posV (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) (σ : Val) (D : LvDat)
    (h0 : lv.posOff ≠ 0) :
    ∃ σ', AgreeBelow st.k σ σ' ∧
      Whir.lvF c lvl lv st σ D ((osLvA c lvl lv st).2.1.k + 1) = σ' (.n osQpos) * gw lv.posOff := by
  unfold Whir.lvF
  split_ifs
  · unfold lvFinF
    rw [seqF_geV (by omega)]
    exact ⟨_, agree_fill _ _ _ _, lvBFinF_posV _ _ _ _ _ _ _ _ _ _ _ _ _ h0⟩
  · unfold lvNonF
    rw [seqF_geV (by omega)]
    exact ⟨_, agree_fill _ _ _ _, lvBNonF_posV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0⟩

/-! ## The levels' values -/

/-- **Level `j`'s values in the levels'**, from a valuation agreeing below the levels' start. -/
theorem lvsF_atV (c : OsCfg) : ∀ (lvs : List OsLv) (Ds : List LvDat) (lvl : ℕ) (st : OsSt)
    (σ : Val) (j : ℕ) (hj : j < lvs.length) (hD : j < Ds.length) (x : ℕ),
    (osLevels c lvl (lvs.take j) st).2.k ≤ x →
    x < (osLevel c (lvl + j) lvs[j] (osLevels c lvl (lvs.take j) st).2).2.k →
    ∃ σ', AgreeBelow st.k σ σ' ∧
      lvsF c lvl lvs Ds st σ x = Whir.lvF c (lvl + j) lvs[j] (osLevels c lvl (lvs.take j) st).2 σ' Ds[j] x
  | [], _, _, _, _, _, hj, _, _, _, _ => absurd hj (by simp)
  | _ :: _, [], _, _, _, _, _, hD, _, _, _ => absurd hD (by simp)
  | lv :: rest, D :: Ds, lvl, st, σ, 0, _, _, x, _, h2 => by
    refine ⟨σ, fun _ _ ↦ rfl, ?_⟩
    change x < (osLevel c lvl lv st).2.k at h2
    show seqF σ st.k (osLevel c lvl lv st).2.k (Whir.lvF c lvl lv st σ D) _ x = Whir.lvF c lvl lv st σ D x
    rw [seqF_ltV h2]
  | lv :: rest, D :: Ds, lvl, st, σ, j + 1, hj, hD, x, h1, h2 => by
    have e1 : (osLevels c lvl ((lv :: rest).take (j + 1)) st).2 =
        (osLevels c (lvl + 1) (rest.take j) (osLevel c lvl lv st).2).2 := rfl
    rw [e1] at h1 h2 ⊢
    have e2 : lvl + (j + 1) = lvl + 1 + j := by omega
    simp only [List.getElem_cons_succ, e2] at h2 ⊢
    have hge := osLevels_kV c (lvl + 1) (rest.take j) (osLevel c lvl lv st).2
    have hk1 := osLevel_kV c lvl lv st
    obtain ⟨σ', ha, he⟩ := lvsF_atV c rest Ds (lvl + 1) (osLevel c lvl lv st).2
      (fill σ st.k (osLevel c lvl lv st).2.k (Whir.lvF c lvl lv st σ D)) j (by simpa using hj)
      (by simpa using hD) x h1 h2
    refine ⟨σ', fun i hi ↦ (ha i (by omega)).trans (fill_lt hi), ?_⟩
    show seqF σ st.k (osLevel c lvl lv st).2.k (Whir.lvF c lvl lv st σ D) _ x = _
    rw [seqF_geV (by omega)]
    exact he

/-- The levels' row weights' pointers and sizes. -/
theorem lvs_alloc_valsV (c : OsCfg) (σ : Val) : ∀ (lvs : List OsLv) (Ds : List LvDat) (lvl : ℕ)
    (st : OsSt) (σ1 : Val), Ds.length = lvs.length →
    (∀ i, st.k ≤ i → i < (osLevels c lvl lvs st).2.k → σ (.n i) = lvsF c lvl lvs Ds st σ1 i) →
    ((lvsAllocsV c lvl lvs st).map Prod.fst).map σ = Ds.map LvDat.wp ∧
      (lvsAllocsV c lvl lvs st).map (fun x ↦ x.2.elim id fun s ↦ logG (σ s)) =
        lvs.map fun _ ↦ logG (gw c.maxIl)
  | [], [], _, _, _, _, _ => ⟨rfl, rfl⟩
  | [], _ :: _, _, _, _, h, _ => absurd h (by simp)
  | _ :: _, [], _, _, _, h, _ => absurd h (by simp)
  | lv :: rest, D :: Ds, lvl, st, σ1, hl, hσ => by
    have hw := osLevel_wpV c lvl lv st
    have hA := osLvA_kV c lvl lv st
    have hge := osLevels_kV c (lvl + 1) rest (osLevel c lvl lv st).2
    have hk := osLevel_kV c lvl lv st
    have e : (osLevels c lvl (lv :: rest) st).2 =
        (osLevels c (lvl + 1) rest (osLevel c lvl lv st).2).2 := rfl
    have ih := lvs_alloc_valsV c σ rest Ds (lvl + 1) (osLevel c lvl lv st).2
      (fill σ1 st.k (osLevel c lvl lv st).2.k (Whir.lvF c lvl lv st σ1 D)) (by simpa using hl)
      (fun i h1 h2 ↦ by
        rw [hσ i (by omega) (by rw [e]; exact h2)]
        show seqF σ1 st.k (osLevel c lvl lv st).2.k (Whir.lvF c lvl lv st σ1 D) _ i = _
        exact seqF_geV h1)
    have hv : σ (.n (wpVarV c lvl lv st)) = D.wp := by
      rw [hσ _ (by unfold wpVarV; omega) (by rw [e]; omega)]
      show seqF σ1 st.k (osLevel c lvl lv st).2.k (Whir.lvF c lvl lv st σ1 D) _ _ = _
      rw [seqF_ltV (by omega)]
      exact lvF_wpV c lvl lv st σ1 D
    have hs : σ (.n ((osPositions c lvl lv (osLvA c lvl lv st).2.1).2.k + 2)) = gw c.maxIl := by
      rw [hσ _ (by omega) (by rw [e]; unfold wpVarV at hw; omega)]
      show seqF σ1 st.k (osLevel c lvl lv st).2.k (Whir.lvF c lvl lv st σ1 D) _ _ = _
      rw [seqF_ltV (by unfold wpVarV at hw; omega)]
      exact lvF_szV c lvl lv st σ1 D
    simp only [lvsAllocsV, lvAllocsV, List.map_cons, osHeapAV, List.cons_append, List.nil_append]
    rw [ih.1, ih.2]
    exact ⟨congrArg (· :: Ds.map LvDat.wp) hv, by simp only [Sum.elim_inr, hs]⟩

end
end LeanVM.Guest.B1
