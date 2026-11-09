/-
  LeanVM.Guest.B1.Whir.CVals

  The values of open_stacked's body at its buffers' pointers and sizes.
-/

module

public import LeanVM.Guest.B1.Whir.CBody

/-!
# The body's values at its buffers

The placed lift needs, of the valuation the body holds (the values `bodyF`), the pointer and size
of each `HeapBuf`. Each is a value function's entry: `lvF_sqz`, `lvF_wp` (a level's squeeze run
and row weights), `lvsF_bufs` (every level's), and the head, tail and finish's.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem seqF_lt {σ : Val} {k k1 : ℕ} {fA : ℕ → E} {fB : Val → ℕ → E} {i : ℕ} (h : i < k1) :
    seqF σ k k1 fA fB i = fA i := by
  simp only [seqF, h, ↓reduceIte]

theorem seqF_ge {σ : Val} {k k1 : ℕ} {fA : ℕ → E} {fB : Val → ℕ → E} {i : ℕ} (h : k1 ≤ i) :
    seqF σ k k1 fA fB i = fB (fill σ k k1 fA) i := by
  simp only [seqF, show ¬ i < k1 by omega, ↓reduceIte]

/-! ## Bounds -/

theorem osSqueezes_k (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    s.k + 34 ≤ (osSqueezes c lvl lv s).2.k := by
  show s.k + 34 ≤ (osPad s.pad (s.k + 14)).2.2 + 20
  unfold osPad; split <;> simp

theorem osQueries_k_ge (c : OsCfg) (lvl : ℕ) (lv : OsLv) (lam lamN : ℕ) (s : OsSt) :
    s.k + 7 ≤ (osQueries c lvl lv lam lamN s).2.1 := by
  obtain ⟨g, hg, hgk⟩ := osQueries_rets c lvl lv lam lamN s
  rw [hg]; omega

/-- The value holding a level's row weights' pointer. -/
def wpVar (c : OsCfg) (lvl : ℕ) (lv : OsLv) (a : OsSt) : ℕ :=
  (osSqueezes c lvl lv a).2.k + osPowLen lv.queries + 3

theorem osLevelB_k (c : OsCfg) (lvl : ℕ) (lv : OsLv) (a : OsSt) :
    wpVar c lvl lv a + 6 ≤ (osLevelB c lvl lv a).2.k := by
  obtain ⟨g, hg, hgk⟩ := osQueries_rets c lvl lv (bLam c lvl lv a) (bLamN c lvl lv a)
    { bSq c lvl lv a with k := (bLp c lvl lv a).2.2 }
  have h2 : (bLp c lvl lv a).2.2 = (bSq c lvl lv a).k + osPowLen lv.queries + 2 := rfl
  have h3 : (bQ c lvl lv a).2.1 = g + 5 := by rw [hg]
  simp only at hgk
  unfold wpVar
  rw [osLevelB_eq]
  split_ifs
  · show _ ≤ (bQ c lvl lv a).2.1 + 1 + 8
    simp only [bSq] at h2 ⊢; omega
  · show _ ≤ (bQ c lvl lv a).2.1 + 13 + 1 + 8
    simp only [bSq] at h2 ⊢; omega

/-! ## A level's buffers -/

theorem lvBFinF_bufs {c : OsCfg} {lvl : ℕ} {lv : OsLv} {a : OsSt} {σ : Val}
    {sqz wp r0 r1 sum ic0 ic2 : E} :
    lvBFinF c lvl lv a σ sqz wp r0 r1 sum ic0 ic2 a.k = gw ((c.maxSq + 1) * 5) ∧
      lvBFinF c lvl lv a σ sqz wp r0 r1 sum ic0 ic2 (a.k + 1) = sqz ∧
      lvBFinF c lvl lv a σ sqz wp r0 r1 sum ic0 ic2 (wpVar c lvl lv a - 1) = gw c.maxIl ∧
      lvBFinF c lvl lv a σ sqz wp r0 r1 sum ic0 ic2 (wpVar c lvl lv a) = wp := by
  have h1 := osSqueezes_k c lvl lv a
  have h3 : (osLamPow lvl ((osSqueezes c lvl lv a).2.k - 1) lv.queries (osSqueezes c lvl lv a).2.k).2.2 =
      (osSqueezes c lvl lv a).2.k + osPowLen lv.queries + 2 := rfl
  have h2 : (osLamPow lvl ((osSqueezes c lvl lv a).2.k - 1) lv.queries (osSqueezes c lvl lv a).2.k).2.2 + 7 ≤
      (osQueries c lvl lv ((osSqueezes c lvl lv a).2.k - 1)
        (osLamPow lvl ((osSqueezes c lvl lv a).2.k - 1) lv.queries (osSqueezes c lvl lv a).2.k).2.1
        { (osSqueezes c lvl lv a).2 with
          k := (osLamPow lvl ((osSqueezes c lvl lv a).2.k - 1) lv.queries (osSqueezes c lvl lv a).2.k).2.2 }).2.1 :=
    osQueries_k_ge c lvl lv _ _ { (osSqueezes c lvl lv a).2 with
      k := (osLamPow lvl ((osSqueezes c lvl lv a).2.k - 1) lv.queries (osSqueezes c lvl lv a).2.k).2.2 }
  unfold wpVar lvBFinF
  dsimp only at h2 ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [seqF_lt (by omega)]; simp [segLookup, sqzSegs]
  · rw [seqF_lt (by omega)]; simp [segLookup, sqzSegs]
  · rw [seqF_ge (by omega), seqF_ge (by omega), seqF_lt (by omega)]
    simp only [queriesF, h3, show (osSqueezes c lvl lv a).2.k + osPowLen lv.queries + 3 - 1 =
      (osSqueezes c lvl lv a).2.k + osPowLen lv.queries + 2 by omega, ↓reduceIte]
  · rw [seqF_ge (by omega), seqF_ge (by omega), seqF_lt (by omega)]
    simp only [queriesF, h3, show (osSqueezes c lvl lv a).2.k + osPowLen lv.queries + 3 ≠
      (osSqueezes c lvl lv a).2.k + osPowLen lv.queries + 2 by omega,
      show (osSqueezes c lvl lv a).2.k + osPowLen lv.queries + 3 =
      (osSqueezes c lvl lv a).2.k + osPowLen lv.queries + 2 + 1 by omega, ↓reduceIte]

theorem lvBNonF_bufs {c : OsCfg} {lvl : ℕ} {lv : OsLv} {a : OsSt} {σ : Val}
    {sqz wp r0 r1 sum ic0 ic2 y oc0 oc2 : E} :
    lvBNonF c lvl lv a σ sqz wp r0 r1 sum ic0 ic2 y oc0 oc2 a.k = gw ((c.maxSq + 1) * 5) ∧
      lvBNonF c lvl lv a σ sqz wp r0 r1 sum ic0 ic2 y oc0 oc2 (a.k + 1) = sqz ∧
      lvBNonF c lvl lv a σ sqz wp r0 r1 sum ic0 ic2 y oc0 oc2 (wpVar c lvl lv a - 1) =
        gw c.maxIl ∧
      lvBNonF c lvl lv a σ sqz wp r0 r1 sum ic0 ic2 y oc0 oc2 (wpVar c lvl lv a) = wp := by
  have h1 := osSqueezes_k c lvl lv a
  have h3 : (osLamPow lvl ((osSqueezes c lvl lv a).2.k - 1) lv.queries (osSqueezes c lvl lv a).2.k).2.2 =
      (osSqueezes c lvl lv a).2.k + osPowLen lv.queries + 2 := rfl
  have h2 : (osLamPow lvl ((osSqueezes c lvl lv a).2.k - 1) lv.queries (osSqueezes c lvl lv a).2.k).2.2 + 7 ≤
      (osQueries c lvl lv ((osSqueezes c lvl lv a).2.k - 1)
        (osLamPow lvl ((osSqueezes c lvl lv a).2.k - 1) lv.queries (osSqueezes c lvl lv a).2.k).2.1
        { (osSqueezes c lvl lv a).2 with
          k := (osLamPow lvl ((osSqueezes c lvl lv a).2.k - 1) lv.queries (osSqueezes c lvl lv a).2.k).2.2 }).2.1 :=
    osQueries_k_ge c lvl lv _ _ { (osSqueezes c lvl lv a).2 with
      k := (osLamPow lvl ((osSqueezes c lvl lv a).2.k - 1) lv.queries (osSqueezes c lvl lv a).2.k).2.2 }
  unfold wpVar lvBNonF
  dsimp only at h2 ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [seqF_lt (by omega)]; simp [segLookup, sqzSegs]
  · rw [seqF_lt (by omega)]; simp [segLookup, sqzSegs]
  · rw [seqF_ge (by omega), seqF_ge (by omega), seqF_lt (by omega)]
    simp only [queriesF, h3, show (osSqueezes c lvl lv a).2.k + osPowLen lv.queries + 3 - 1 =
      (osSqueezes c lvl lv a).2.k + osPowLen lv.queries + 2 by omega, ↓reduceIte]
  · rw [seqF_ge (by omega), seqF_ge (by omega), seqF_lt (by omega)]
    simp only [queriesF, h3, show (osSqueezes c lvl lv a).2.k + osPowLen lv.queries + 3 ≠
      (osSqueezes c lvl lv a).2.k + osPowLen lv.queries + 2 by omega,
      show (osSqueezes c lvl lv a).2.k + osPowLen lv.queries + 3 =
      (osSqueezes c lvl lv a).2.k + osPowLen lv.queries + 2 + 1 by omega, ↓reduceIte]

theorem osLevelA_k_le (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) :
    st.k ≤ (osLevelA c lvl lv st).2.1.k := by
  have h := osFolds_k osFch lv.folds lv.foldsOff st
  unfold osLevelA
  dsimp only
  split_ifs
  · unfold osFinal; dsimp only
    have := osMat_next (osFolds osFch lv.foldsOff lv.folds st).2.cb
      (osFolds osFch lv.foldsOff lv.folds st).2.co (osFolds osFch lv.foldsOff lv.folds st).2.k
    omega
  · unfold osCommit; dsimp only; omega

/-- **A level's buffers' pointers and sizes in its values.** -/
theorem lvF_bufs (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) (σ : Val) (D : LvDat) :
    lvF c lvl lv st σ D (osLevelA c lvl lv st).2.1.k = gw ((c.maxSq + 1) * 5) ∧
      lvF c lvl lv st σ D ((osLevelA c lvl lv st).2.1.k + 1) = D.sqz ∧
      lvF c lvl lv st σ D (wpVar c lvl lv (osLevelA c lvl lv st).2.1 - 1) = gw c.maxIl ∧
      lvF c lvl lv st σ D (wpVar c lvl lv (osLevelA c lvl lv st).2.1) = D.wp := by
  have h1 := osSqueezes_k c lvl lv (osLevelA c lvl lv st).2.1
  have hw : (osLevelA c lvl lv st).2.1.k + 34 ≤ wpVar c lvl lv (osLevelA c lvl lv st).2.1 - 1 := by
    unfold wpVar; omega
  unfold lvF
  split_ifs
  · unfold lvFinF
    rw [seqF_ge le_rfl, seqF_ge (by omega), seqF_ge (by omega), seqF_ge (by omega)]
    exact lvBFinF_bufs
  · unfold lvNonF
    rw [seqF_ge le_rfl, seqF_ge (by omega), seqF_ge (by omega), seqF_ge (by omega)]
    exact lvBNonF_bufs


theorem osLevel_k_le (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) :
    wpVar c lvl lv (osLevelA c lvl lv st).2.1 + 6 ≤ (osLevel c lvl lv st).2.k := by
  rw [osLevel_split]
  exact osLevelB_k c lvl lv _

theorem osLevel_k_ge (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) :
    st.k ≤ (osLevel c lvl lv st).2.k := by
  have h1 := osLevel_k_le c lvl lv st
  have h2 := osLevelA_k_le c lvl lv st
  have h3 := osSqueezes_k c lvl lv (osLevelA c lvl lv st).2.1
  unfold wpVar at h1
  omega

theorem osLevels_k_ge (c : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLv) (st : OsSt),
    st.k ≤ (osLevels c lvl lvs st).2.k
  | _, [], _ => le_rfl
  | lvl, lv :: rest, st => by
    have e : (osLevels c lvl (lv :: rest) st).2 = (osLevels c (lvl + 1) rest (osLevel c lvl lv st).2).2 :=
      rfl
    rw [e]
    exact le_trans (osLevel_k_ge c lvl lv st) (osLevels_k_ge c (lvl + 1) rest _)

/-- **Every level's buffers' pointers and sizes in the levels' values.** -/
theorem lvsF_bufs (c : OsCfg) : ∀ (lvs : List OsLv) (Ds : List LvDat) (lvl : ℕ) (st : OsSt) (σ : Val)
    (j : ℕ) (hj : j < lvs.length) (hD : j < Ds.length),
    lvsF c lvl lvs Ds st σ (osLevelA c (lvl + j) lvs[j] (osLevels c lvl (lvs.take j) st).2).2.1.k =
        gw ((c.maxSq + 1) * 5) ∧
      lvsF c lvl lvs Ds st σ
        ((osLevelA c (lvl + j) lvs[j] (osLevels c lvl (lvs.take j) st).2).2.1.k + 1) = Ds[j].sqz ∧
      lvsF c lvl lvs Ds st σ (wpVar c (lvl + j) lvs[j]
        (osLevelA c (lvl + j) lvs[j] (osLevels c lvl (lvs.take j) st).2).2.1 - 1) = gw c.maxIl ∧
      lvsF c lvl lvs Ds st σ (wpVar c (lvl + j) lvs[j]
        (osLevelA c (lvl + j) lvs[j] (osLevels c lvl (lvs.take j) st).2).2.1) = Ds[j].wp
  | [], _, _, _, _, _, hj, _ => absurd hj (by simp)
  | _ :: _, [], _, _, _, _, _, hD => absurd hD (by simp)
  | lv :: rest, D :: Ds, lvl, st, σ, 0, _, _ => by
    have hb := lvF_bufs c lvl lv st σ D
    have hk := osLevel_k_le c lvl lv st
    have h3 := osSqueezes_k c lvl lv (osLevelA c lvl lv st).2.1
    have hw : (osLevelA c lvl lv st).2.1.k + 34 ≤ wpVar c lvl lv (osLevelA c lvl lv st).2.1 - 1 := by
      unfold wpVar; omega
    have e0 : osLevels c lvl [] st = ([], st) := rfl
    simp only [List.take_zero, e0, Nat.add_zero, List.getElem_cons_zero]
    show lvsF c lvl (lv :: rest) (D :: Ds) st σ _ = _ ∧ lvsF c lvl (lv :: rest) (D :: Ds) st σ _ = _ ∧
      lvsF c lvl (lv :: rest) (D :: Ds) st σ _ = _ ∧ lvsF c lvl (lv :: rest) (D :: Ds) st σ _ = _
    simp only [lvsF]
    rw [seqF_lt (by omega), seqF_lt (by omega), seqF_lt (by omega), seqF_lt (by omega)]
    exact hb
  | lv :: rest, D :: Ds, lvl, st, σ, j + 1, hj, hD => by
    have ih := lvsF_bufs c rest Ds (lvl + 1) (osLevel c lvl lv st).2
      (fill σ st.k (osLevel c lvl lv st).2.k (lvF c lvl lv st σ D)) j (by simpa using hj)
      (by simpa using hD)
    have hj' : j < rest.length := by simpa using hj
    have e1 : (osLevels c lvl ((lv :: rest).take (j + 1)) st).2 =
        (osLevels c (lvl + 1) (rest.take j) (osLevel c lvl lv st).2).2 := rfl
    have hge := osLevels_k_ge c (lvl + 1) (rest.take j) (osLevel c lvl lv st).2
    have hA := osLevelA_k_le c (lvl + 1 + j) rest[j]
      (osLevels c (lvl + 1) (rest.take j) (osLevel c lvl lv st).2).2
    have h3 := osSqueezes_k c (lvl + 1 + j) rest[j] (osLevelA c (lvl + 1 + j) rest[j]
      (osLevels c (lvl + 1) (rest.take j) (osLevel c lvl lv st).2).2).2.1
    have hw : (osLevelA c (lvl + 1 + j) rest[j]
        (osLevels c (lvl + 1) (rest.take j) (osLevel c lvl lv st).2).2).2.1.k + 34 ≤
        wpVar c (lvl + 1 + j) rest[j] (osLevelA c (lvl + 1 + j) rest[j]
          (osLevels c (lvl + 1) (rest.take j) (osLevel c lvl lv st).2).2).2.1 - 1 := by
      unfold wpVar; omega
    simp only [List.getElem_cons_succ, e1, show lvl + (j + 1) = lvl + 1 + j by omega]
    show lvsF c lvl (lv :: rest) (D :: Ds) st σ _ = _ ∧ lvsF c lvl (lv :: rest) (D :: Ds) st σ _ = _ ∧
      lvsF c lvl (lv :: rest) (D :: Ds) st σ _ = _ ∧ lvsF c lvl (lv :: rest) (D :: Ds) st σ _ = _
    simp only [lvsF]
    rw [seqF_ge (by omega), seqF_ge (by omega), seqF_ge (by omega), seqF_ge (by omega)]
    exact ih


/-! ## The squeeze loop's call -/

/-- The squeeze loop's guard and arguments: `1`, `g^n`, `1 + g^n`, `1`, `g^n` from `k + 2`. -/
def sqGuardVals (lv : OsLv) : List E :=
  [word 1 0 0, gw lv.squeezes, word 1 0 0 + gw lv.squeezes, word 1 0 0, gw lv.squeezes]

theorem lvBFinF_guard {c : OsCfg} {lvl : ℕ} {lv : OsLv} {a : OsSt} {σ : Val}
    {sqz wp r0 r1 sum ic0 ic2 : E} {j : ℕ} (hj : j < 5) :
    lvBFinF c lvl lv a σ sqz wp r0 r1 sum ic0 ic2 (a.k + 2 + j) = (sqGuardVals lv).getD j 0 := by
  have h1 := osSqueezes_k c lvl lv a
  unfold lvBFinF
  dsimp only
  rw [seqF_lt (by omega)]
  simp only [show a.k + 2 + j - a.k = 2 + j by omega]
  interval_cases j <;> simp [segLookup, sqzSegs, sqGuardVals]

theorem lvBNonF_guard {c : OsCfg} {lvl : ℕ} {lv : OsLv} {a : OsSt} {σ : Val}
    {sqz wp r0 r1 sum ic0 ic2 y oc0 oc2 : E} {j : ℕ} (hj : j < 5) :
    lvBNonF c lvl lv a σ sqz wp r0 r1 sum ic0 ic2 y oc0 oc2 (a.k + 2 + j) =
      (sqGuardVals lv).getD j 0 := by
  have h1 := osSqueezes_k c lvl lv a
  unfold lvBNonF
  dsimp only
  rw [seqF_lt (by omega)]
  simp only [show a.k + 2 + j - a.k = 2 + j by omega]
  interval_cases j <;> simp [segLookup, sqzSegs, sqGuardVals]

theorem lvF_guard (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) (σ : Val) (D : LvDat) {j : ℕ}
    (hj : j < 5) :
    lvF c lvl lv st σ D ((osLevelA c lvl lv st).2.1.k + 2 + j) = (sqGuardVals lv).getD j 0 := by
  unfold lvF
  split_ifs
  · unfold lvFinF
    rw [seqF_ge (by omega)]
    exact lvBFinF_guard hj
  · unfold lvNonF
    rw [seqF_ge (by omega)]
    exact lvBNonF_guard hj

theorem lvsF_guard (c : OsCfg) : ∀ (lvs : List OsLv) (Ds : List LvDat) (lvl : ℕ) (st : OsSt) (σ : Val)
    (j : ℕ) (hj : j < lvs.length) (_ : j < Ds.length) {t : ℕ} (_ : t < 5),
    lvsF c lvl lvs Ds st σ
        ((osLevelA c (lvl + j) lvs[j] (osLevels c lvl (lvs.take j) st).2).2.1.k + 2 + t) =
      (sqGuardVals lvs[j]).getD t 0
  | [], _, _, _, _, _, hj, _, _, _ => absurd hj (by simp)
  | _ :: _, [], _, _, _, _, _, hD, _, _ => absurd hD (by simp)
  | lv :: rest, D :: Ds, lvl, st, σ, 0, _, _, t, ht => by
    have hk := osLevel_k_le c lvl lv st
    have h3 := osSqueezes_k c lvl lv (osLevelA c lvl lv st).2.1
    have e0 : osLevels c lvl [] st = ([], st) := rfl
    simp only [List.take_zero, e0, Nat.add_zero, List.getElem_cons_zero]
    show lvsF c lvl (lv :: rest) (D :: Ds) st σ _ = _
    simp only [lvsF]
    rw [seqF_lt (by unfold wpVar at hk; omega)]
    exact lvF_guard c lvl lv st σ D ht
  | lv :: rest, D :: Ds, lvl, st, σ, j + 1, hj, hD, t, ht => by
    have ih := lvsF_guard c rest Ds (lvl + 1) (osLevel c lvl lv st).2
      (fill σ st.k (osLevel c lvl lv st).2.k (lvF c lvl lv st σ D)) j (by simpa using hj)
      (by simpa using hD) ht
    have hj' : j < rest.length := by simpa using hj
    have e1 : (osLevels c lvl ((lv :: rest).take (j + 1)) st).2 =
        (osLevels c (lvl + 1) (rest.take j) (osLevel c lvl lv st).2).2 := rfl
    have hge := osLevels_k_ge c (lvl + 1) (rest.take j) (osLevel c lvl lv st).2
    have hA := osLevelA_k_le c (lvl + 1 + j) rest[j]
      (osLevels c (lvl + 1) (rest.take j) (osLevel c lvl lv st).2).2
    simp only [List.getElem_cons_succ, e1, show lvl + (j + 1) = lvl + 1 + j by omega]
    show lvsF c lvl (lv :: rest) (D :: Ds) st σ _ = _
    simp only [lvsF]
    rw [seqF_ge (by omega)]
    exact ih

end
end LeanVM.Guest.B1.Whir
