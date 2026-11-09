/-
  LeanVM.Guest.B1.Whir.CQueries

  A level's queries block, honestly: its three calls given, the block holds.
-/

module

public import LeanVM.Guest.B1.Whir.CFold

/-!
# A level's queries block, honestly

`osQueries_complete`: given the three calls of the block on the arguments the block passes them
(`opening_row_weights` on the level's folds and the weights' buffer `wp`, `verify_merkle_cap` on the
level's cap returning the root's cells `r0, r1`, which `level_roots` holds, `opening_queries`
returning `sum`) and the intro message's two words at the cursor, the block holds, the queries'
sum, `c0`, `c1 = sum + c2` and `c2` left in its values.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

theorem rangeVals_sub {σ : Val} {k k' a b : ℕ} {f g : ℕ → E} (h : RangeVals σ k k' f)
    (ha : k ≤ a) (hb : b ≤ k') (hfg : ∀ i, a ≤ i → i < b → f i = g i) : RangeVals σ a b g :=
  fun i h1 h2 ↦ (h i (by omega) (by omega)).trans (hfg i h1 h2)

theorem matsBelow_mono {K K' : ℕ} {mats : List OsMat} (h : MatsBelow K mats) (hK : K ≤ K') :
    MatsBelow K' mats := fun m hm ↦ by
  obtain ⟨h1, h2, h3⟩ := h m hm; exact ⟨by omega, by omega, by omega⟩

/-- The values of `osMatP plan mats base off k`: the distance's power, then the pointer. -/
def matPVal (σ : Val) (plan : List (ℕ × ℕ × ℕ)) (mats : List OsMat) (base off k i : ℕ) : E :=
  if i = k then gw (osMatSD plan mats base off).2 else σ (.n base) * gw off

/-- **A materialized pointer, from earlier ones.** -/
theorem osMatP_complete {plan : List (ℕ × ℕ × ℕ)} {mats : List OsMat} {base off k : ℕ}
    (hoff : off < u128Bound) {σ σ' : Val} (hm : MatsOk σ' mats) (hbase : σ' (.n base) = σ (.n base))
    (hv : RangeVals σ' k (osMatP plan mats base off k).2.2 (matPVal σ plan mats base off k)) :
    AllOk C rd σ' (osMatP plan mats base off k).1 ∧
      σ' (.n (osMatP plan mats base off k).2.1) = σ (.n base) * gen ^ off := by
  by_cases h0 : off = 0
  · subst h0
    simp only [osMatP, ↓reduceIte, pow_zero, mul_one]
    exact ⟨allOk_nil, hbase⟩
  · rw [osMatP_eq k h0] at hv ⊢
    have e0 := hv k le_rfl (by simp)
    have e1 := hv (k + 1) (by omega) (by simp)
    simp only [matPVal, ↓reduceIte, show k + 1 ≠ k by omega] at e0 e1
    obtain ⟨hd, hs⟩ := osMatSD_ok (plan := plan) hm (base := base) hoff
    refine ⟨?_, by rw [e1, gw_eq hoff]⟩
    simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
    exact ⟨e0, by rw [e1, e0, gw_eq hd, hs, hbase, gw_eq hoff]⟩

theorem osMatP_k (plan : List (ℕ × ℕ × ℕ)) (mats : List OsMat) (base off k : ℕ) :
    (osMatP plan mats base off k).2.2 = if off = 0 then k else k + 2 := by
  unfold osMatP; split_ifs <;> rfl

/-- The queries block's materializations' next values. -/
structure QPts where
  m1 : List OsMat
  m2 : List OsMat
  m3 : List OsMat
  fp : List Stmt × ℕ × ℕ
  cp : List Stmt × ℕ × ℕ
  flp : List Stmt × ℕ × ℕ
  cp2 : List Stmt × ℕ × ℕ
  flp2 : List Stmt × ℕ × ℕ
  bp : List Stmt × ℕ × ℕ

/-- The queries block's materializations. -/
def qPts (c : OsCfg) (lv : OsLv) (s : OsSt) : QPts :=
  let k := s.k
  let P := c.plan
  let m0 := s.mats
  let fp := osMatP P m0 osFch lv.foldsOff (k + 2)
  let m1 := osMatsAfter P m0 osFch lv.foldsOff (k + 2)
  let cp := osMatP P m1 osCaps (4 * lv.capOff) fp.2.2
  let m2 := osMatsAfter P m1 osCaps (4 * lv.capOff) fp.2.2
  let flp := osMatP P m2 osFlags lv.capOff cp.2.2
  let m3 := osMatsAfter P m2 osFlags lv.capOff cp.2.2
  let r := flp.2.2
  let cp2 := osMatP P m3 osCaps (4 * lv.capOff) (r + 2)
  let flp2 := osMatP P m3 osFlags lv.capOff cp2.2.2
  let bp := osMatP P m3 osQbp lv.posOff flp2.2.2
  ⟨m1, m2, m3, fp, cp, flp, cp2, flp2, bp⟩

/-- The queries block's number of statements' values: the next free value. -/
theorem osQueries_k (c : OsCfg) (lvl : ℕ) (lv : OsLv) (lam lamN : ℕ) (s : OsSt) :
    (osQueries c lvl lv lam lamN s).2.1 = (qPts c lv s).bp.2.2 + 5 := rfl

theorem osQueriesMats_eq (c : OsCfg) (lv : OsLv) (s : OsSt) :
    osQueriesMats c lv s = osMatsAfter c.plan (qPts c lv s).m3 osQbp lv.posOff (qPts c lv s).flp2.2.2 :=
  rfl

/-- The values of a level's queries block. -/
def queriesF (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) (σ : Val)
    (wp r0 r1 sum ic0 ic2 : E) : ℕ → E :=
  let k := s.k
  let P := c.plan
  let q := qPts c lv s
  let r := q.flp.2.2
  let g := q.bp.2.2
  fun i ↦
    if i = k then gw c.maxIl else if i = k + 1 then wp
    else if i < q.fp.2.2 then matPVal σ P s.mats osFch lv.foldsOff (k + 2) i
    else if i < q.cp.2.2 then matPVal σ P q.m1 osCaps (4 * lv.capOff) q.fp.2.2 i
    else if i < r then matPVal σ P q.m2 osFlags lv.capOff q.cp.2.2 i
    else if i = r then r0 else if i = r + 1 then r1
    else if i < q.cp2.2.2 then matPVal σ P q.m3 osCaps (4 * lv.capOff) (r + 2) i
    else if i < q.flp2.2.2 then matPVal σ P q.m3 osFlags lv.capOff q.cp2.2.2 i
    else if i < g then matPVal σ P q.m3 osQbp lv.posOff q.flp2.2.2 i
    else [gw (lv.queries / (1 + if lvl = 0 then 1 else 0)), sum, ic0, ic2, sum + ic2].getD (i - g) 0

/-- **A level's queries block, honestly.** -/
theorem osQueries_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {lam lamN : ℕ} {s : OsSt} (σ : Val)
    (hb : s.Below) (hk : 164 ≤ s.k) (hl : lam < s.k) (hlN : lamN < s.k)
    (hm : MatsOk σ s.mats) (hmb : MatsBelow s.k s.mats)
    (hbo : lv.foldsOff < u128Bound ∧ 4 * lv.capOff < u128Bound ∧ lv.capOff < u128Bound ∧
      lv.posOff < u128Bound ∧ lv.queries / (1 + if lvl = 0 then 1 else 0) < u128Bound)
    (wp r0 r1 sum ic0 ic2 : E)
    (hRW : C ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++ natStr (if lvl = 0 then 1 else 0))
      [σ (.n osFch) * gen ^ lv.foldsOff, wp] [])
    (hCap : C ("verify_merkle_cap__L" ++ natStr lv.capDepth)
      [σ (.n osCaps) * gen ^ (4 * lv.capOff), σ (.n osFlags) * gen ^ lv.capOff] [r0, r1])
    (hr0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl) r0)
    (hr1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) r1)
    (hQ : C (osQueriesName lvl lv) [σ (.n osCaps) * gen ^ (4 * lv.capOff),
      σ (.n osFlags) * gen ^ lv.capOff, σ (.n lam), σ (.n lamN), σ (.n osQbp) * gen ^ lv.posOff, wp,
      gen ^ (lv.queries / (1 + if lvl = 0 then 1 else 0))] [sum])
    (hi0 : LoadHolds rd (σ (.n s.cb)) s.co ic0) (hi2 : LoadHolds rd (σ (.n s.cb)) (s.co + 1) ic2) :
    BlkF C rd σ s.k (osQueries c lvl lv lam lamN s).2.1
      (queriesF c lvl lv s σ wp r0 r1 sum ic0 ic2) (osQueries c lvl lv lam lamN s).1
      (fun σ' ↦ σ' (.n (osQueries c lvl lv lam lamN s).2.2.1) = sum ∧
        σ' (.n (osQueries c lvl lv lam lamN s).2.2.2.1) = ic0 ∧
        σ' (.n (osQueries c lvl lv lam lamN s).2.2.2.2.2) = ic2 ∧
        σ' (.n (osQueries c lvl lv lam lamN s).2.2.2.2.1) = sum + ic2 ∧ AgreeBelow s.k σ σ' ∧
        MatsOk σ' (osQueriesMats c lv s) ∧
        MatsBelow (osQueries c lvl lv lam lamN s).2.1 (osQueriesMats c lv s)) := by
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hbo
  set k := s.k with hkdef
  set P := c.plan
  set q := qPts c lv s with hqdef
  set fp := q.fp
  set cp := q.cp
  set flp := q.flp
  set r := flp.2.2
  set cp2 := q.cp2
  set flp2 := q.flp2
  set bp := q.bp
  set g := bp.2.2
  set N0 := lv.queries / (1 + if lvl = 0 then 1 else 0)
  have efp : fp = osMatP P s.mats osFch lv.foldsOff (k + 2) := rfl
  have ecp : cp = osMatP P q.m1 osCaps (4 * lv.capOff) fp.2.2 := rfl
  have eflp : flp = osMatP P q.m2 osFlags lv.capOff cp.2.2 := rfl
  have ecp2 : cp2 = osMatP P q.m3 osCaps (4 * lv.capOff) (r + 2) := rfl
  have eflp2 : flp2 = osMatP P q.m3 osFlags lv.capOff cp2.2.2 := rfl
  have ebp : bp = osMatP P q.m3 osQbp lv.posOff flp2.2.2 := rfl
  have em1 : q.m1 = osMatsAfter P s.mats osFch lv.foldsOff (k + 2) := rfl
  have em2 : q.m2 = osMatsAfter P q.m1 osCaps (4 * lv.capOff) fp.2.2 := rfl
  have em3 : q.m3 = osMatsAfter P q.m2 osFlags lv.capOff cp.2.2 := rfl
  have o1 : k + 2 ≤ fp.2.2 := osMatP_next _ _ _ _ _
  have o2 : fp.2.2 ≤ cp.2.2 := osMatP_next _ _ _ _ _
  have o3 : cp.2.2 ≤ r := osMatP_next _ _ _ _ _
  have o4 : r + 2 ≤ cp2.2.2 := osMatP_next _ _ _ _ _
  have o5 : cp2.2.2 ≤ flp2.2.2 := osMatP_next _ _ _ _ _
  have o6 : flp2.2.2 ≤ g := osMatP_next _ _ _ _ _
  have hst : (osQueries c lvl lv lam lamN s).1 = osHeap c.maxIl k ++ fp.1 ++
      [.call ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++
        natStr (if lvl = 0 then 1 else 0)) [.n fp.2.1, .n (k + 1)] []] ++
      cp.1 ++ flp.1 ++
      [.call ("verify_merkle_cap__L" ++ natStr lv.capDepth) [.n cp.2.1, .n flp.2.1] [.n r, .n (r + 1)],
        .atom (.load (.n r) (.n osRoots) (2 * lvl)),
        .atom (.load (.n (r + 1)) (.n osRoots) (2 * lvl + 1))] ++
      cp2.1 ++ flp2.1 ++ bp.1 ++
      [.atom (.const (.n g) (gw N0)),
        .call (osQueriesName lvl lv) [.n cp2.2.1, .n flp2.2.1, .n lam, .n lamN, .n bp.2.1,
          .n (k + 1), .n g] [.n (g + 1)],
        .atom (.load (.n (g + 2)) (.n s.cb) s.co), .atom (.load (.n (g + 3)) (.n s.cb) (s.co + 1)),
        .atom (.add (.n (g + 4)) (.n (g + 1)) (.n (g + 3)))] := rfl
  have hr : (osQueries c lvl lv lam lamN s).2 = (g + 5, g + 1, g + 2, g + 4, g + 3) := rfl
  have hmats : osQueriesMats c lv s = osMatsAfter P q.m3 osQbp lv.posOff flp2.2.2 := rfl
  rw [hst, hr, hmats]
  set f := queriesF c lvl lv s σ wp r0 r1 sum ic0 ic2 with hfdef
  have hfv : ∀ i, f i =
      if i = k then gw c.maxIl else if i = k + 1 then wp
      else if i < fp.2.2 then matPVal σ P s.mats osFch lv.foldsOff (k + 2) i
      else if i < cp.2.2 then matPVal σ P q.m1 osCaps (4 * lv.capOff) fp.2.2 i
      else if i < r then matPVal σ P q.m2 osFlags lv.capOff cp.2.2 i
      else if i = r then r0 else if i = r + 1 then r1
      else if i < cp2.2.2 then matPVal σ P q.m3 osCaps (4 * lv.capOff) (r + 2) i
      else if i < flp2.2.2 then matPVal σ P q.m3 osFlags lv.capOff cp2.2.2 i
      else if i < g then matPVal σ P q.m3 osQbp lv.posOff flp2.2.2 i
      else [gw N0, sum, ic0, ic2, sum + ic2].getD (i - g) 0 :=
    fun i ↦ rfl
  intro σ' ha hv
  have eF : σ' (.n osFch) = σ (.n osFch) := ha _ (by unfold osFch; omega)
  have eC : σ' (.n osCaps) = σ (.n osCaps) := ha _ (by unfold osCaps; omega)
  have eL : σ' (.n osFlags) = σ (.n osFlags) := ha _ (by unfold osFlags; omega)
  have eR : σ' (.n osRoots) = σ (.n osRoots) := ha _ (by unfold osRoots; omega)
  have eQ : σ' (.n osQbp) = σ (.n osQbp) := ha _ (by unfold osQbp; omega)
  have el : σ' (.n lam) = σ (.n lam) := ha _ hl
  have elN : σ' (.n lamN) = σ (.n lamN) := ha _ hlN
  have ecb : σ' (.n s.cb) = σ (.n s.cb) := ha _ hb.cb
  have hm0 : MatsOk σ' s.mats := matsOk_agree hm hmb ha
  -- the pointers
  have rF : RangeVals σ' (k + 2) fp.2.2 (matPVal σ P s.mats osFch lv.foldsOff (k + 2)) :=
    rangeVals_sub (k' := g + 5) hv (by omega) (by omega) fun i h1 h2 ↦ by
      rw [hfv]
      simp only [show i ≠ k by omega, show i ≠ k + 1 by omega, show i < fp.2.2 by omega,
        ↓reduceIte]
  obtain ⟨okF, vF⟩ : AllOk C rd σ' fp.1 ∧ σ' (.n fp.2.1) = σ (.n osFch) * gen ^ lv.foldsOff :=
    osMatP_complete (C := C) (rd := rd) hb1 hm0 eF (rF)
  have hm1 : MatsOk σ' q.m1 := em1 ▸ osMatsAfter_ok hm0 hb1 okF
  have rC : RangeVals σ' fp.2.2 cp.2.2 (matPVal σ P q.m1 osCaps (4 * lv.capOff) fp.2.2) :=
    rangeVals_sub (k' := g + 5) hv (by omega) (by omega) fun i h1 h2 ↦ by
      rw [hfv]
      simp only [show i ≠ k by omega, show i ≠ k + 1 by omega, show ¬ i < fp.2.2 by omega,
        show i < cp.2.2 by omega, ↓reduceIte]
  obtain ⟨okC, vC⟩ : AllOk C rd σ' cp.1 ∧ σ' (.n cp.2.1) = σ (.n osCaps) * gen ^ (4 * lv.capOff) :=
    osMatP_complete (C := C) (rd := rd) hb2 hm1 eC (rC)
  have hm2 : MatsOk σ' q.m2 := em2 ▸ osMatsAfter_ok hm1 hb2 okC
  have rL : RangeVals σ' cp.2.2 r (matPVal σ P q.m2 osFlags lv.capOff cp.2.2) :=
    rangeVals_sub (k' := g + 5) hv (by omega) (by omega) fun i h1 h2 ↦ by
      rw [hfv]
      simp only [show i ≠ k by omega, show i ≠ k + 1 by omega, show ¬ i < fp.2.2 by omega,
        show ¬ i < cp.2.2 by omega, show i < r from h2, ↓reduceIte]
  obtain ⟨okL, vL⟩ : AllOk C rd σ' flp.1 ∧ σ' (.n flp.2.1) = σ (.n osFlags) * gen ^ lv.capOff :=
    osMatP_complete (C := C) (rd := rd) hb3 hm2 eL (rL)
  have hm3 : MatsOk σ' q.m3 := em3 ▸ osMatsAfter_ok hm2 hb3 okL
  have rC2 : RangeVals σ' (r + 2) cp2.2.2 (matPVal σ P q.m3 osCaps (4 * lv.capOff) (r + 2)) :=
    rangeVals_sub (k' := g + 5) hv (by omega) (by omega) fun i h1 h2 ↦ by
      rw [hfv]
      simp only [show i ≠ k by omega, show i ≠ k + 1 by omega, show ¬ i < fp.2.2 by omega,
        show ¬ i < cp.2.2 by omega, show ¬ i < r by omega, show i ≠ r by omega,
        show i ≠ r + 1 by omega, show i < cp2.2.2 by omega, ↓reduceIte]
  obtain ⟨okC2, vC2⟩ : AllOk C rd σ' cp2.1 ∧ σ' (.n cp2.2.1) = σ (.n osCaps) * gen ^ (4 * lv.capOff) :=
    osMatP_complete (C := C) (rd := rd) hb2 hm3 eC (rC2)
  have rL2 : RangeVals σ' cp2.2.2 flp2.2.2 (matPVal σ P q.m3 osFlags lv.capOff cp2.2.2) :=
    rangeVals_sub (k' := g + 5) hv (by omega) (by omega) fun i h1 h2 ↦ by
      rw [hfv]
      simp only [show i ≠ k by omega, show i ≠ k + 1 by omega, show ¬ i < fp.2.2 by omega,
        show ¬ i < cp.2.2 by omega, show ¬ i < r by omega, show i ≠ r by omega,
        show i ≠ r + 1 by omega, show ¬ i < cp2.2.2 by omega, show i < flp2.2.2 by omega,
        ↓reduceIte]
  obtain ⟨okL2, vL2⟩ : AllOk C rd σ' flp2.1 ∧ σ' (.n flp2.2.1) = σ (.n osFlags) * gen ^ lv.capOff :=
    osMatP_complete (C := C) (rd := rd) hb3 hm3 eL (rL2)
  have rQ : RangeVals σ' flp2.2.2 g (matPVal σ P q.m3 osQbp lv.posOff flp2.2.2) :=
    rangeVals_sub (k' := g + 5) hv (by omega) (by omega) fun i h1 h2 ↦ by
      rw [hfv]
      simp only [show i ≠ k by omega, show i ≠ k + 1 by omega, show ¬ i < fp.2.2 by omega,
        show ¬ i < cp.2.2 by omega, show ¬ i < r by omega, show i ≠ r by omega,
        show i ≠ r + 1 by omega, show ¬ i < cp2.2.2 by omega, show ¬ i < flp2.2.2 by omega,
        show i < g from h2, ↓reduceIte]
  obtain ⟨okQ, vQ⟩ : AllOk C rd σ' bp.1 ∧ σ' (.n bp.2.1) = σ (.n osQbp) * gen ^ lv.posOff :=
    osMatP_complete (C := C) (rd := rd) hb4 hm3 eQ (rQ)
  have hm4 : MatsOk σ' (osMatsAfter P q.m3 osQbp lv.posOff flp2.2.2) := osMatsAfter_ok hm3 hb4 okQ
  -- below
  have hB1 : MatsBelow (g + 5) q.m1 :=
    em1 ▸ matsBelow_after hmb (by unfold osFch; omega) (by omega) (by omega)
  have hB2 : MatsBelow (g + 5) q.m2 :=
    em2 ▸ matsBelow_after hB1 (by unfold osCaps; omega) le_rfl (by omega)
  have hB3 : MatsBelow (g + 5) q.m3 :=
    em3 ▸ matsBelow_after hB2 (by unfold osFlags; omega) le_rfl (by omega)
  have hB4 : MatsBelow (g + 5) (osMatsAfter P q.m3 osQbp lv.posOff flp2.2.2) :=
    matsBelow_after hB3 (by unfold osQbp; omega) le_rfl (by omega)
  -- the single values
  have tail : ∀ j < 5, σ' (.n (g + j)) = [gw N0, sum, ic0, ic2, sum + ic2].getD j 0 := fun j hj ↦ by
    rw [hv (g + j) (by omega) (by omega)]; rw [hfv]
    simp only [show g + j ≠ k by omega, show g + j ≠ k + 1 by omega, show ¬ g + j < fp.2.2 by omega,
      show ¬ g + j < cp.2.2 by omega, show ¬ g + j < r by omega, show g + j ≠ r by omega,
      show g + j ≠ r + 1 by omega, show ¬ g + j < cp2.2.2 by omega,
      show ¬ g + j < flp2.2.2 by omega, show ¬ g + j < g by omega, ↓reduceIte,
      Nat.add_sub_cancel_left]
  have v0 := tail 0 (by omega); have v1 := tail 1 (by omega); have v2 := tail 2 (by omega)
  have v3 := tail 3 (by omega); have v4 := tail 4 (by omega)
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4
  have vk : σ' (.n k) = gw c.maxIl := by rw [hv k le_rfl (by omega)]; simp [hfv]
  have vk1 : σ' (.n (k + 1)) = wp := by rw [hv (k + 1) (by omega) (by omega)]; simp [hfv]
  have vr : σ' (.n r) = r0 := by
    rw [hv r (by omega) (by omega)]; rw [hfv]
    simp only [show r ≠ k by omega, show r ≠ k + 1 by omega, show ¬ r < fp.2.2 by omega,
      show ¬ r < cp.2.2 by omega, lt_irrefl, ↓reduceIte]
  have vr1 : σ' (.n (r + 1)) = r1 := by
    rw [hv (r + 1) (by omega) (by omega)]; rw [hfv]
    simp only [show r + 1 ≠ k by omega, show r + 1 ≠ k + 1 by omega,
      show ¬ r + 1 < fp.2.2 by omega, show ¬ r + 1 < cp.2.2 by omega, show ¬ r + 1 < r by omega,
      show r + 1 ≠ r by omega, ↓reduceIte]
  refine ⟨?_, by rw [v1], by rw [v2], by rw [v3], by rw [v4], ha, hm4, hB4⟩
  simp only [osHeap, allOk_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds,
    List.map_cons, List.map_nil]
  simp only [and_assoc]
  refine ⟨vk, okF, ?_, okC, okL, ?_, ?_, ?_, okC2, okL2, okQ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vF, vk1]; exact hRW
  · rw [vC, vL, vr, vr1]; exact hCap
  · rw [vr, eR]; exact hr0
  · rw [vr1, eR]; exact hr1
  · exact v0
  · rw [vC2, vL2, el, elN, vQ, vk1, v0, gw_eq hb5, v1]; exact hQ
  · rw [v2, ecb]; exact hi0
  · rw [v3, ecb]; exact hi2
  · rw [v4, v1, v3]

end
end LeanVM.Guest.B1.Whir
