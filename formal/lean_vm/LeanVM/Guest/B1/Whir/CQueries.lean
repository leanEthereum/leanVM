/-
  LeanVM.Guest.B1.Whir.CQueries

  A level's `level_mus` store and queries block, honestly: its calls given, the block holds.
-/

module

public import LeanVM.Guest.B1.Whir.CFold

/-!
# A level's queries block, honestly

`osMu_complete`: `level_mus[g^lvl] = 1/λ`, the batching challenge not zero. `osQueries_complete`:
given the block's calls on the arguments it passes them (`opening_row_weights` on the level's
folds and the weights' buffer `wp`; the dispatch on the rate into `level_queries`, on `λ`, the
level's window pointers and `wp`, returning the root's cells `r0, r1`, which `level_roots` holds,
the queries' sum and `λ^q`) and the intro message's two words at the cursor, the block holds, the
sum, `λ^q`, `c0`, `c1 = sum + c2` and `c2` left in its values.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- **`level_mus[g^lvl] = 1/λ`, honestly.** -/
theorem osMu_complete {lvl lam k : ℕ} (σ : Val) (hl : lam < k) (hmu : osMus < k)
    (hl0 : σ (.n lam) ≠ 0) (hm : LoadHolds rd (σ (.n osMus)) lvl (σ (.n lam))⁻¹) :
    BlkF C rd σ k (k + 2) (fun i ↦ if i = k then word 1 0 0 else (σ (.n lam))⁻¹)
      (osMu lvl lam k).1 (fun σ' ↦ AgreeBelow k σ σ') := by
  intro σ' ha hv
  have v0 := hv k le_rfl (by omega)
  have v1 := hv (k + 1) (by omega) (by omega)
  simp only [↓reduceIte, show k + 1 ≠ k by omega] at v0 v1
  refine ⟨?_, ha⟩
  simp only [osMu, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
  refine ⟨v0, ?_, ?_⟩
  · rw [v0, v1, ha lam hl, word_one, inv_mul_cancel₀ hl0]
  · rw [v1, ha _ hmu]; exact hm

theorem osMu_k (lvl lam k : ℕ) : (osMu lvl lam k).2 = k + 2 := rfl

/-- The queries block's materializations. -/
structure QPts where
  m1 : List OsMat
  fp : List Stmt × ℕ × ℕ
  bp : List Stmt × ℕ × ℕ

/-- The queries block's materializations. -/
def qPts (c : OsCfg) (lv : OsLv) (s : OsSt) : QPts :=
  let k := s.k
  let P := c.plan
  let fp := osMatP P s.mats osFch lv.foldsOff (k + 2)
  let m1 := osMatsAfter P s.mats osFch lv.foldsOff (k + 2)
  let bp := osMatP P m1 osQbp lv.posOff fp.2.2
  ⟨m1, fp, bp⟩

theorem osQueries_k (c : OsCfg) (lvl : ℕ) (lv : OsLv) (lam : ℕ) (s : OsSt) :
    (osQueries c lvl lv lam s).2.1 = (qPts c lv s).bp.2.2 + 7 := rfl

theorem osQueriesMats_eq (c : OsCfg) (lv : OsLv) (s : OsSt) :
    osQueriesMats c lv s = osMatsAfter c.plan (qPts c lv s).m1 osQbp lv.posOff (qPts c lv s).fp.2.2 :=
  rfl

theorem osQueries_rets (c : OsCfg) (lvl : ℕ) (lv : OsLv) (lam : ℕ) (s : OsSt) :
    (osQueries c lvl lv lam s).2 = ((qPts c lv s).bp.2.2 + 7, (qPts c lv s).bp.2.2 + 2,
      (qPts c lv s).bp.2.2 + 3, (qPts c lv s).bp.2.2 + 4, (qPts c lv s).bp.2.2 + 6,
      (qPts c lv s).bp.2.2 + 5) := rfl

theorem qPts_k (c : OsCfg) (lv : OsLv) (s : OsSt) : s.k + 2 ≤ (qPts c lv s).bp.2.2 := by
  have o1 : s.k + 2 ≤ (qPts c lv s).fp.2.2 := osMatP_next _ _ _ _ _
  have o2 : (qPts c lv s).fp.2.2 ≤ (qPts c lv s).bp.2.2 := osMatP_next _ _ _ _ _
  omega

/-- The values of a level's queries block. -/
def queriesF (c : OsCfg) (lv : OsLv) (s : OsSt) (σ : Val)
    (wp r0 r1 sum lamN ic0 ic2 : E) : ℕ → E :=
  let k := s.k
  let P := c.plan
  let q := qPts c lv s
  let r := q.bp.2.2
  fun i ↦
    if i = k then gw c.maxIl else if i = k + 1 then wp
    else if i < q.fp.2.2 then matPVal σ P s.mats osFch lv.foldsOff (k + 2) i
    else if i < r then matPVal σ P q.m1 osQbp lv.posOff q.fp.2.2 i
    else [r0, r1, sum, lamN, ic0, ic2, sum + ic2].getD (i - r) 0

/-- **A level's queries block, honestly.** -/
theorem osQueries_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {lam : ℕ} {s : OsSt} (σ : Val)
    {R : E} (hR : σ (.n osRate) = R)
    (hb : s.Below) (hk : 161 ≤ s.k) (hl : lam < s.k)
    (hm : MatsOk σ s.mats) (hmb : MatsBelow s.k s.mats)
    (hbo : lv.foldsOff < u128Bound ∧ lv.posOff < u128Bound)
    (wp r0 r1 sum lamN ic0 ic2 : E)
    (hRW : C ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++ natStr (if lvl = 0 then 1 else 0))
      [σ (.n osFch) * gen ^ lv.foldsOff, wp] [])
    (hQ : DispC C rd R ((c.lvAt lvl).map (osQueriesName lvl))
      [σ (.n lam), σ (.n osQbp) * gen ^ lv.posOff, wp] [r0, r1, sum, lamN])
    (hr0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl) r0)
    (hr1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) r1)
    (hi0 : LoadHolds rd (σ (.n s.cb)) s.co ic0) (hi2 : LoadHolds rd (σ (.n s.cb)) (s.co + 1) ic2) :
    BlkF C rd σ s.k (osQueries c lvl lv lam s).2.1
      (queriesF c lv s σ wp r0 r1 sum lamN ic0 ic2) (osQueries c lvl lv lam s).1
      (fun σ' ↦ σ' (.n (osQueries c lvl lv lam s).2.2.1) = sum ∧
        σ' (.n (osQueries c lvl lv lam s).2.2.2.1) = lamN ∧
        σ' (.n (osQueries c lvl lv lam s).2.2.2.2.1) = ic0 ∧
        σ' (.n (osQueries c lvl lv lam s).2.2.2.2.2.1) = sum + ic2 ∧
        σ' (.n (osQueries c lvl lv lam s).2.2.2.2.2.2) = ic2 ∧ AgreeBelow s.k σ σ' ∧
        MatsOk σ' (osQueriesMats c lv s) ∧
        MatsBelow (osQueries c lvl lv lam s).2.1 (osQueriesMats c lv s)) := by
  obtain ⟨hb1, hb4⟩ := hbo
  set k := s.k with hkdef
  set P := c.plan
  set q := qPts c lv s with hqdef
  set fp := q.fp
  set bp := q.bp
  set r := bp.2.2
  have efp : fp = osMatP P s.mats osFch lv.foldsOff (k + 2) := rfl
  have ebp : bp = osMatP P q.m1 osQbp lv.posOff fp.2.2 := rfl
  have em1 : q.m1 = osMatsAfter P s.mats osFch lv.foldsOff (k + 2) := rfl
  have o1 : k + 2 ≤ fp.2.2 := osMatP_next _ _ _ _ _
  have o2 : fp.2.2 ≤ r := osMatP_next _ _ _ _ _
  have hst : (osQueries c lvl lv lam s).1 = osHeap c.maxIl k ++ fp.1 ++
      [.call ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++
        natStr (if lvl = 0 then 1 else 0)) [.n fp.2.1, .n (k + 1)] []] ++
      bp.1 ++
      [.dispatch (.n osRate) ((c.lvAt lvl).map (osQueriesName lvl)) [.n lam, .n bp.2.1, .n (k + 1)]
          (osRun r 4),
        .atom (.load (.n r) (.n osRoots) (2 * lvl)), .atom (.load (.n (r + 1)) (.n osRoots) (2 * lvl + 1)),
        .atom (.load (.n (r + 4)) (.n s.cb) s.co), .atom (.load (.n (r + 5)) (.n s.cb) (s.co + 1)),
        .atom (.add (.n (r + 6)) (.n (r + 2)) (.n (r + 5)))] := rfl
  have hr : (osQueries c lvl lv lam s).2 = (r + 7, r + 2, r + 3, r + 4, r + 6, r + 5) := rfl
  have hmats : osQueriesMats c lv s = osMatsAfter P q.m1 osQbp lv.posOff fp.2.2 := rfl
  rw [hst, hr, hmats]
  set f := queriesF c lv s σ wp r0 r1 sum lamN ic0 ic2 with hfdef
  have hfv : ∀ i, f i =
      if i = k then gw c.maxIl else if i = k + 1 then wp
      else if i < fp.2.2 then matPVal σ P s.mats osFch lv.foldsOff (k + 2) i
      else if i < r then matPVal σ P q.m1 osQbp lv.posOff fp.2.2 i
      else [r0, r1, sum, lamN, ic0, ic2, sum + ic2].getD (i - r) 0 :=
    fun i ↦ rfl
  intro σ' ha hv
  have eF : σ' (.n osFch) = σ (.n osFch) := ha _ (by unfold osFch; omega)
  have eR : σ' (.n osRoots) = σ (.n osRoots) := ha _ (by unfold osRoots; omega)
  have eQ : σ' (.n osQbp) = σ (.n osQbp) := ha _ (by unfold osQbp; omega)
  have el : σ' (.n lam) = σ (.n lam) := ha _ hl
  have ecb : σ' (.n s.cb) = σ (.n s.cb) := ha _ hb.cb
  have eRt : σ' (.n osRate) = R := by rw [ha _ (by unfold osRate; omega), hR]
  have hm0 : MatsOk σ' s.mats := matsOk_agree hm hmb ha
  -- the pointers
  have rF : RangeVals σ' (k + 2) fp.2.2 (matPVal σ P s.mats osFch lv.foldsOff (k + 2)) :=
    rangeVals_sub (k' := r + 7) hv (by omega) (by omega) fun i h1 h2 ↦ by
      rw [hfv]
      simp only [show i ≠ k by omega, show i ≠ k + 1 by omega, show i < fp.2.2 by omega,
        ↓reduceIte]
  obtain ⟨okF, vF⟩ : AllOk C rd σ' fp.1 ∧ σ' (.n fp.2.1) = σ (.n osFch) * gen ^ lv.foldsOff :=
    osMatP_complete (C := C) (rd := rd) hb1 hm0 eF (rF)
  have hm1 : MatsOk σ' q.m1 := em1 ▸ osMatsAfter_ok hm0 hb1 okF
  have rQ : RangeVals σ' fp.2.2 r (matPVal σ P q.m1 osQbp lv.posOff fp.2.2) :=
    rangeVals_sub (k' := r + 7) hv (by omega) (by omega) fun i h1 h2 ↦ by
      rw [hfv]
      simp only [show i ≠ k by omega, show i ≠ k + 1 by omega, show ¬ i < fp.2.2 by omega,
        show i < r from h2, ↓reduceIte]
  obtain ⟨okQ, vQ⟩ : AllOk C rd σ' bp.1 ∧ σ' (.n bp.2.1) = σ (.n osQbp) * gen ^ lv.posOff :=
    osMatP_complete (C := C) (rd := rd) hb4 hm1 eQ (rQ)
  have hm4 : MatsOk σ' (osMatsAfter P q.m1 osQbp lv.posOff fp.2.2) := osMatsAfter_ok hm1 hb4 okQ
  -- below
  have hB1 : MatsBelow (r + 7) q.m1 :=
    em1 ▸ matsBelow_after hmb (by unfold osFch; omega) (by omega) (by omega)
  have hB4 : MatsBelow (r + 7) (osMatsAfter P q.m1 osQbp lv.posOff fp.2.2) :=
    matsBelow_after hB1 (by unfold osQbp; omega) le_rfl (by omega)
  -- the single values
  have tail : ∀ j < 7, σ' (.n (r + j)) = [r0, r1, sum, lamN, ic0, ic2, sum + ic2].getD j 0 :=
    fun j hj ↦ by
      rw [hv (r + j) (by omega) (by omega)]; rw [hfv]
      simp only [show r + j ≠ k by omega, show r + j ≠ k + 1 by omega,
        show ¬ r + j < fp.2.2 by omega, show ¬ r + j < r by omega, ↓reduceIte,
        Nat.add_sub_cancel_left]
  have v0 := tail 0 (by omega); have v1 := tail 1 (by omega); have v2 := tail 2 (by omega)
  have v3 := tail 3 (by omega); have v4 := tail 4 (by omega); have v5 := tail 5 (by omega)
  have v6 := tail 6 (by omega)
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4 v5 v6
  have vk : σ' (.n k) = gw c.maxIl := by rw [hv k le_rfl (by omega)]; simp [hfv]
  have vk1 : σ' (.n (k + 1)) = wp := by rw [hv (k + 1) (by omega) (by omega)]; simp [hfv]
  refine ⟨?_, by rw [v2], by rw [v3], by rw [v4], by rw [v6], by rw [v5], ha, hm4, hB4⟩
  simp only [osHeap, allOk_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds,
    List.map_cons, List.map_nil]
  simp only [and_assoc]
  refine ⟨vk, okF, ?_, okQ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vF, vk1]; exact hRW
  · have h1 : ([.n lam, .n bp.2.1, .n (k + 1)] : List V).map σ' =
        [σ (.n lam), σ (.n osQbp) * gen ^ lv.posOff, wp] := by
      simp only [List.map_cons, List.map_nil]; rw [el, vQ, vk1]
    have h2 : (osRun r 4).map σ' = [r0, r1, sum, lamN] := by
      simp only [osRun, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
        List.nil_append, List.cons_append, Nat.add_zero, v0, v1, v2, v3]
    exact hQ σ' eRt [.n lam, .n bp.2.1, .n (k + 1)] (osRun r 4) h1 h2
  · rw [v0, eR]; exact hr0
  · rw [v1, eR]; exact hr1
  · rw [v4, ecb]; exact hi0
  · rw [v5, ecb]; exact hi2
  · rw [v6, v2, v5]

end
end LeanVM.Guest.B1.Whir
