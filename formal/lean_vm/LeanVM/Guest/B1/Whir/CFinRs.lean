/-
  LeanVM.Guest.B1.Whir.CFinRs

  A non-final level's residual chains and their sums into the inner chain, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CFinR
public import LeanVM.Guest.B1.Whir.Residuals

/-!
# The residuals, honestly (G:1826-1862)

`rcC`: a level's chains' buffer, the two chains `h ← (h + P(p))·μ`, `hh ← (hh + H(p))·μ` over the
first `8j` positions at entries `2j`, `2j + 1`. `osResidual_complete`: `μ` loaded, the buffer
allocated at `RC` and started at `0, 0`, its loop called (the call relation's), its last batch
read back, the remaining queries inline (`osResSteps`), the level's sums stored into
`inner_chain`; the chains are `resAll`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {H : CallRel → Reader → Prop}

/-- The chains after the first `8j` of a level's positions. -/
def rcAt (lv : OsLv) (D : ℕ → E) (hsv : List E) (Pos : ℕ → E) (mu : E) (j : ℕ) : E × E :=
  resFold (resP lv D) (resH lv hsv) mu (0, 0) ((List.range (resBatch * j)).map Pos)

/-- **A level's chains' buffer**: entries `2j`, `2j + 1` the chains after `8j` positions. -/
def rcC (lv : OsLv) (D : ℕ → E) (hsv : List E) (Pos : ℕ → E) (mu : E) : List E :=
  (List.range (2 * (lv.queries / resBatch + 1))).map fun e ↦
    if e % 2 = 0 then (rcAt lv D hsv Pos mu (e / 2)).1 else (rcAt lv D hsv Pos mu (e / 2)).2

theorem rcC_length (lv : OsLv) (D : ℕ → E) (hsv : List E) (Pos : ℕ → E) (mu : E) :
    (rcC lv D hsv Pos mu).length = 2 * (lv.queries / resBatch + 1) := by simp [rcC]

theorem rcC_get (lv : OsLv) (D : ℕ → E) (hsv : List E) (Pos : ℕ → E) (mu : E) {j : ℕ}
    (hj : j ≤ lv.queries / resBatch) :
    (rcC lv D hsv Pos mu).getD (2 * j) 0 = (rcAt lv D hsv Pos mu j).1 ∧
      (rcC lv D hsv Pos mu).getD (2 * j + 1) 0 = (rcAt lv D hsv Pos mu j).2 := by
  constructor
  · rw [List.getD_eq_getElem _ _ (by rw [rcC_length]; omega)]
    simp [rcC, show 2 * j / 2 = j by omega]
  · rw [List.getD_eq_getElem _ _ (by rw [rcC_length]; omega)]
    simp [rcC, show (2 * j + 1) / 2 = j by omega, show (2 * j + 1) % 2 = 1 by omega]

/-- What memory holds for a level's residual: `μ`, the positions, the basis row, the high part,
the chains' buffer at `RC`, the inner chain's entries before and after, the scale, `β` and the
product of the coordinates. -/
structure ResMem (rd : Reader) (σ : Val) (lvl : ℕ) (lv : OsLv) (bd ich ls la : ℕ) (RC : E)
    (D : ℕ → E) (hsv : List E) (Pos : ℕ → E) (mu i0 i1 s b a : E) : Prop where
  mus : LoadHolds rd (σ (.n osMus)) lvl mu
  pos : ∀ k < lv.queries, LoadHolds rd (σ (.n osQpos)) (lv.posOff + k) (Pos k)
  row : ∀ t < lv.logCols, LoadHolds rd (σ (.n bd)) (lvl * ligColsCap + t) (D t)
  hs : ∀ c < lv.folds, LoadHolds rd (σ (.n osHs)) (lvl * hsStride + c) (hsv.getD c 0)
  rc : ReadsAt rd RC (rcC lv D hsv Pos mu)
  li0 : LoadHolds rd (σ (.n ich)) (2 * lvl) i0
  li1 : LoadHolds rd (σ (.n ich)) (2 * lvl + 1) i1
  lsc : LoadHolds rd (σ (.n ls)) lvl s
  lbe : LoadHolds rd (σ (.n osBetas)) lvl b
  laf : LoadHolds rd (σ (.n la)) lvl a
  st0 : LoadHolds rd (σ (.n ich)) (2 * lvl + 2) (i0 + s * (resAll lv D hsv Pos mu).1)
  st1 : LoadHolds rd (σ (.n ich)) (2 * lvl + 3) (i1 + b * a * (resAll lv D hsv Pos mu).2)

/-- A level's residual's static facts. -/
structure ResStatic (lv : OsLv) (hsv : List E) : Prop where
  cols : 1 ≤ lv.logCols
  nhs : 1 ≤ lv.folds
  b3 : lv.highBits ≤ 3
  bn : lv.highBits ≤ lv.logCols + 1
  len : hsv.length = lv.folds
  nbu : lv.queries / resBatch < u128Bound
  nb64 : 2 * (lv.queries / resBatch + 1) < 2 ^ 64 - 1

/-- A level's remaining queries inline. -/
abbrev resTl (bd lvl : ℕ) (lv : OsLv) (k : ℕ) : List Stmt × ℕ × ℕ × ℕ :=
  osResSteps osQpos bd (lvl * ligColsCap) osHs (lvl * hsStride) lv.vanish lv.logCols lv.folds
    lv.highBits k (osResTail lv) (k + 10) (k + 11) (k + 12)

/-- A level's residual up to its sums: `μ`, the buffer, the loop, the inline queries. -/
def resA (c : OsCfg) (bd lvl : ℕ) (lv : OsLv) (k : ℕ) : List Stmt :=
  [osLd k osMus lvl] ++ osHeap (2 * (lv.queries / resBatch + 1)) (k + 1) ++
    [osCst (k + 3) (word 0 0), osLd (k + 3) (k + 2) 0, osCst (k + 4) (word 0 0), osLd (k + 4) (k + 2) 1] ++
    osLoopCall (c.resLoop lvl) 0 (lv.queries / resBatch) [osQpos, bd, osHs, k + 2, k] (k + 5) ++
    [osLd (k + 10) (k + 2) (2 * (lv.queries / resBatch)),
      osLd (k + 11) (k + 2) (2 * (lv.queries / resBatch) + 1)] ++ (resTl bd lvl lv k).1

/-- A level's sums into the inner chain, from the chains `h`, `hh`, at `a`. -/
def resB (ich ls la lvl h hh a : ℕ) : List Stmt :=
  [osLd a ich (2 * lvl), osLd (a + 1) ls lvl, osMul (a + 2) (a + 1) h, osAdd (a + 3) a (a + 2),
    osLd (a + 3) ich (2 * lvl + 2), osLd (a + 4) ich (2 * lvl + 1), osLd (a + 5) osBetas lvl,
    osLd (a + 6) la lvl, osMul (a + 7) (a + 5) (a + 6), osMul (a + 8) (a + 7) hh,
    osAdd (a + 9) (a + 4) (a + 8), osLd (a + 9) ich (2 * lvl + 3)]

theorem osResidual_eq (c : OsCfg) (ich bd ls la lvl : ℕ) (lv : OsLv) (k : ℕ) :
    osResidual c ich bd ls la lvl lv k =
      (resA c bd lvl lv k ++ resB ich ls la lvl (resTl bd lvl lv k).2.1 (resTl bd lvl lv k).2.2.1
        (resTl bd lvl lv k).2.2.2, (resTl bd lvl lv k).2.2.2 + 10) := by
  simp only [osResidual, resA, resB, resTl, List.append_assoc, List.cons_append, List.nil_append]

theorem resTl_ssa {bd lvl : ℕ} {lv : OsLv} {hsv : List E} {k : ℕ} (hst : ResStatic lv hsv) (hbd : bd < k)
    (hk : 36 ≤ k) :
    SsaP (k + 12) (resTl bd lvl lv k).1 (resTl bd lvl lv k).2.2.2 ∧
      (resTl bd lvl lv k).2.1 < (resTl bd lvl lv k).2.2.2 ∧
      (resTl bd lvl lv k).2.2.1 < (resTl bd lvl lv k).2.2.2 ∧
      (∀ p o, (p, o) ∈ loadsOf (resTl bd lvl lv k).1 →
        (p = osQpos ∧ o ∈ osResTail lv) ∨ (p = bd ∧ ∃ s, s < lv.logCols ∧ o = lvl * ligColsCap + s) ∨
          (p = osHs ∧ ∃ c, c < lv.folds ∧ o = lvl * hsStride + c)) :=
  osResSteps_ssa _ _ _ _ _ _ _ _ _ _ (by have := hst.nhs; omega) (by have := hst.cols; omega) _ _ _ _
    (by show 33 < k + 12; omega) (by omega) (by show 27 < k + 12; omega) (by omega) (by omega)
    (by omega)

theorem osResTail_pos (lv : OsLv) {o : ℕ} (h : o ∈ osResTail lv) :
    ∃ q, q < lv.queries ∧ q = resBatch * (lv.queries / resBatch) + (o - lv.posOff - resBatch *
      (lv.queries / resBatch)) ∧ o = lv.posOff + q := by
  simp only [osResTail, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  have := Nat.div_add_mod lv.queries resBatch
  refine ⟨resBatch * (lv.queries / resBatch) + i, by omega, by omega, by omega⟩

/-- **A level's residual up to its sums, honestly**: `μ` read, the chains' buffer at `RC`, the
loop called, the remaining queries inline; the chains are `resAll`. -/
theorem resA_complete {c : OsCfg} {ich bd ls la lvl : ℕ} {lv : OsLv} {k : ℕ} {σ : Val} {RC : E}
    {D : ℕ → E} {hsv : List E} {Pos : ℕ → E} {mu i0 i1 s b a : E} (hst : ResStatic lv hsv)
    (hbd : bd < k) (hk : 36 ≤ k)
    (hm : ∀ C rd, H C rd → ResMem rd σ lvl lv bd ich ls la RC D hsv Pos mu i0 i1 s b a)
    (hC : ∀ C rd, H C rd → 1 + gen ^ (lv.queries / resBatch) ≠ 0 →
      C (c.resLoop lvl) [1, gen ^ (lv.queries / resBatch), σ (.n osQpos), σ (.n bd), σ (.n osHs), RC, mu] []) :
    BlkA H σ k (resTl bd lvl lv k).2.2.2 (resA c bd lvl lv k)
      (fun σ' ↦ σ' (.n k) = mu ∧ σ' (.n (k + 1)) = gw (2 * (lv.queries / resBatch + 1)) ∧
        σ' (.n (k + 2)) = RC ∧
        (σ' (.n (resTl bd lvl lv k).2.1), σ' (.n (resTl bd lvl lv k).2.2.1)) = resAll lv D hsv Pos mu ∧
        σ' (.n (k + 7)) = 1 + gen ^ (lv.queries / resBatch) ∧ σ' (.n (k + 8)) = 1 ∧
        σ' (.n (k + 9)) = gen ^ (lv.queries / resBatch)) := by
  set nb := lv.queries / resBatch with hnb
  obtain ⟨t1, t2, t3, t4⟩ := resTl_ssa (lvl := lvl) hst hbd hk
  set tl := resTl bd lvl lv k with htl
  have hlit : Ssa k ([osLd k osMus lvl] ++ osHeap (2 * (nb + 1)) (k + 1) ++
      [osCst (k + 3) (word 0 0), osLd (k + 3) (k + 2) 0, osCst (k + 4) (word 0 0), osLd (k + 4) (k + 2) 1] ++
      osLoopCall (c.resLoop lvl) 0 nb [osQpos, bd, osHs, k + 2, k] (k + 5) ++
      [osLd (k + 10) (k + 2) (2 * nb), osLd (k + 11) (k + 2) (2 * nb + 1)]) (k + 12) :=
    .cons (.load le_rfl (by show 25 < k; omega)) (.cons (.const (by omega)) (.cons (.allocDyn (by omega) (by omega))
      (.cons (.const (by omega)) (.cons (.store (by omega) (by omega)) (.cons (.const (by omega))
        (.cons (.store (by omega) (by omega)) (.cons (.const (by omega)) (.cons (.const (by omega))
          (.cons (.add (by omega) (by omega) (by omega)) (.cons (.const (by omega)) (.cons (.const (by omega))
            (.cons (.callIf (args := [k + 5 + 3, k + 5 + 4, osQpos, bd, osHs, k + 2, k]) (by omega)
              (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false, osQpos, osHs] at hx; omega))
              (.cons (.load (by omega) (by omega)) (.cons (.load (by omega) (by omega)) .nil))))))))))))))
  have hS : Ssa k (resA c bd lvl lv k) tl.2.2.2 := hlit.append t1.toSsa
  have hv : ∀ (v : ℕ → E) j, j < k + 12 →
      evalV (memOf H) (fun i ↦ if i = k + 2 then RC else 0) k v (resA c bd lvl lv k) j =
        evalV (memOf H) (fun i ↦ if i = k + 2 then RC else 0) k v ([osLd k osMus lvl] ++
          osHeap (2 * (nb + 1)) (k + 1) ++ [osCst (k + 3) (word 0 0), osLd (k + 3) (k + 2) 0,
          osCst (k + 4) (word 0 0), osLd (k + 4) (k + 2) 1] ++
          osLoopCall (c.resLoop lvl) 0 nb [osQpos, bd, osHs, k + 2, k] (k + 5) ++
          [osLd (k + 10) (k + 2) (2 * nb), osLd (k + 11) (k + 2) (2 * nb + 1)]) j :=
    fun v j hj ↦ hlit.evalV_lt t1.toSsa v hj
  have hvals : ∀ σ', RangeVals σ' k tl.2.2.2
      (evalV (memOf H) (fun i ↦ if i = k + 2 then RC else 0) k (fun i ↦ σ (.n i)) (resA c bd lvl lv k)) →
      σ' (.n k) = memOf H (σ (.n osMus)) lvl ∧ σ' (.n (k + 1)) = gw (2 * (nb + 1)) ∧
        σ' (.n (k + 2)) = RC ∧ σ' (.n (k + 3)) = word 0 0 ∧ σ' (.n (k + 4)) = word 0 0 ∧
        σ' (.n (k + 7)) = gw 0 + gw nb ∧ σ' (.n (k + 8)) = gw 0 ∧ σ' (.n (k + 9)) = gw nb ∧
        σ' (.n (k + 10)) = memOf H RC (2 * nb) ∧ σ' (.n (k + 11)) = memOf H RC (2 * nb + 1) := by
    intro σ' hr
    have := t1.le
    have e := fun j (h1 : k ≤ j) (h2 : j < k + 12) ↦ (hr j h1 (by omega)).trans (hv _ j h2)
    have e0 := e k le_rfl (by omega)
    have e1 := e (k + 1) (by omega) (by omega)
    have e2 := e (k + 2) (by omega) (by omega)
    have e3 := e (k + 3) (by omega) (by omega)
    have e4 := e (k + 4) (by omega) (by omega)
    have e7 := e (k + 7) (by omega) (by omega)
    have e8 := e (k + 8) (by omega) (by omega)
    have e9 := e (k + 9) (by omega) (by omega)
    have e10 := e (k + 10) (by omega) (by omega)
    have e11 := e (k + 11) (by omega) (by omega)
    simp +arith [evalV, stepV, stepW, osHeap, osLoopCall] at e0 e1 e2 e3 e4 e7 e8 e9 e10 e11
    exact ⟨e0, e1, e2, e3, e4, e7, e8, e9, e10, e11⟩
  have hrc : ∀ C rd, H C rd → ∀ j (hj : j < 2 * (nb + 1)),
      memOf H RC j = (rcC lv D hsv Pos mu).getD j 0 := fun C rd hH j hj ↦
    memOf_eq (fun C rd hH ↦ by
      have := (hm C rd hH).rc j (by rw [rcC_length]; exact hj)
      rwa [List.getD_eq_getElem _ _ (by rw [rcC_length]; exact hj)]) hH
  refine ssa_blk (Pt := fun i ↦ if i = k + 2 then RC else 0) hS ?_ ?_
  · intro C rd hH σ' ha hr hok
    obtain ⟨e0, e1, e2, -, -, e7, e8, e9, e10, e11⟩ := hvals σ' hr
    have hM := hm C rd hH
    have emu : memOf H (σ (.n osMus)) lvl = mu := memOf_eq (fun C rd hH ↦ (hm C rd hH).mus) hH
    refine ⟨by rw [e0, emu], e1, e2, ?_, by rw [e7, gw_eq (by decide), gw_eq hst.nbu, pow_zero],
      by rw [e8, gw_eq (by decide), pow_zero], by rw [e9, gw_eq hst.nbu]⟩
    have hok' : AllOk C rd σ' tl.1 := (allOk_append.mp hok).2
    have hD : ∀ t < lv.logCols, LoadHolds rd (σ' (.n bd)) (lvl * ligColsCap + t) (D t) := by
      rw [ha _ hbd]; exact hM.row
    have hH' : ∀ c' < lv.folds, LoadHolds rd (σ' (.n osHs)) (lvl * hsStride + c') (hsv.getD c' 0) := by
      rw [ha _ (by show 27 < k; omega)]; exact hM.hs
    obtain ⟨ps, hF, hres⟩ := osResSteps_val hst.cols hst.nhs hst.b3 hst.bn hD hst.len hH' (osResTail lv)
      (k + 10) (k + 11) (k + 12) hok'
    have hps : ps = (List.range (lv.queries % resBatch)).map fun i ↦ Pos (resBatch * nb + i) := by
      have hl := hF.length_eq
      refine List.ext_getElem (by simp [← hl, osResTail]) fun i h1 h2 ↦ ?_
      have := List.forall₂_iff_get.mp hF
      have h3 := this.2 i (by rw [hl]; exact h1) h1
      simp only [List.get_eq_getElem, osResTail, List.getElem_map, List.getElem_range] at h3
      simp only [List.getElem_map, List.getElem_range]
      refine loadHolds_unique h3 ?_
      rw [ha _ (by show 33 < k; omega)]
      have hq := hM.pos (resBatch * nb + i) (by
        have := Nat.div_add_mod lv.queries resBatch
        simp at h2; rw [hnb]; omega)
      rw [show lv.posOff + (lv.queries - lv.queries % resBatch) + i = lv.posOff + (resBatch * nb + i) by
        have := Nat.div_add_mod lv.queries resBatch; rw [hnb]; omega]
      exact hq
    have hall : (List.range lv.queries).map Pos = (List.range (resBatch * nb)).map Pos ++ ps := by
      have hQ : resBatch * nb + lv.queries % resBatch = lv.queries := by
        rw [hnb]; exact Nat.div_add_mod _ _
      rw [hps, show List.range lv.queries = List.range (resBatch * nb + lv.queries % resBatch) by
        rw [hQ], List.range_add, List.map_append, List.map_map]
      rfl
    obtain ⟨g0, g1⟩ := rcC_get lv D hsv Pos mu (j := nb) le_rfl
    have e10' : σ' (.n (k + 10)) = (rcAt lv D hsv Pos mu nb).1 := by
      rw [e10, hrc C rd hH _ (by omega), g0]
    have e11' : σ' (.n (k + 11)) = (rcAt lv D hsv Pos mu nb).2 := by
      rw [e11, hrc C rd hH _ (by omega), g1]
    have emu' : σ' (.n k) = mu := by rw [e0, emu]
    rw [hres, e10', e11', emu', resAll, hall, resFold_append]
    rfl
  · intro C rd hH σ' ha hr
    have hM := hm C rd hH
    change SidesOk _ _ C rd σ' k (_ ++ tl.1)
    rw [sidesOk_append hlit]
    refine ⟨?_, t1.sidesOk fun p o hpo ↦ ?_⟩
    · obtain ⟨e0, e1, e2, e3, e4, e7, e8, e9, e10, e11⟩ := hvals σ' hr
      simp only [osHeap, osLoopCall, List.cons_append, List.nil_append]
      simp +arith only [SidesOk, Side, stepW, List.map_cons, List.map_nil, ↓reduceIte, true_and,
        and_true]
      have hsum : IsInK (gw 0 + gw nb) := by
        rw [gw_eq (by decide), gw_eq hst.nbu]; exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
      rw [ha _ (by show 25 < k; omega), e2, e3, e4, e7, e8, e9, ha _ (by show 33 < k; omega),
        ha _ hbd, ha _ (by show 27 < k; omega), e0, memOf_eq (fun C rd hH ↦ (hm C rd hH).mus) hH]
      have hrl : ∀ C rd, H C rd → ∀ j < 2 * (nb + 1),
          LoadHolds rd RC j ((rcC lv D hsv Pos mu).getD j 0) := fun C rd hH j hj ↦ by
        have hl : j < (rcC lv D hsv Pos mu).length := by rw [rcC_length, ← hnb]; exact hj
        have := (hm C rd hH).rc j hl
        rwa [List.getD_eq_getElem _ _ hl]
      have h2 : 2 ≤ 2 * (nb + 1) := Nat.le_mul_of_pos_right 2 (Nat.succ_pos nb)
      have r0 := hrl C rd hH 0 (by omega)
      have r1 := hrl C rd hH 1 (by omega)
      obtain ⟨z0, z1⟩ := rcC_get lv D hsv Pos mu (j := 0) (Nat.zero_le _)
      simp only [Nat.mul_zero, Nat.zero_add] at z0 z1
      rw [z0] at r0
      rw [z1] at r1
      simp only [rcAt, Nat.mul_zero, List.range_zero, List.map_nil, resFold, List.foldl_nil] at r0 r1
      refine ⟨hM.mus, by rw [word_zero]; exact r0, by rw [word_zero]; exact r1, ⟨hsum, fun hne ↦ ?_⟩, ?_, ?_⟩
      · have := hC C rd hH (by rwa [gw_eq (by decide), gw_eq hst.nbu, pow_zero] at hne)
        rwa [gw_eq (by decide), gw_eq hst.nbu, pow_zero]
      · rw [memOf_eq (fun C rd hH ↦ hrl C rd hH (2 * nb) (by omega)) hH]
        exact hrl C rd hH (2 * nb) (by omega)
      · rw [memOf_eq (fun C rd hH ↦ hrl C rd hH (2 * nb + 1) (by omega)) hH]
        exact hrl C rd hH (2 * nb + 1) (by omega)
    · rcases t4 p o hpo with ⟨rfl, ho⟩ | ⟨rfl, s', hs, rfl⟩ | ⟨rfl, c', hc, rfl⟩
      · obtain ⟨q, hq, -, rfl⟩ := osResTail_pos lv ho
        rw [ha _ (by show 33 < k; omega)]
        rw [memOf_eq (fun C rd hH ↦ (hm C rd hH).pos q hq) hH]
        exact hM.pos q hq
      · rw [ha _ hbd, memOf_eq (fun C rd hH ↦ (hm C rd hH).row s' hs) hH]
        exact hM.row s' hs
      · rw [ha _ (by show 27 < k; omega), memOf_eq (fun C rd hH ↦ (hm C rd hH).hs c' hc) hH]
        exact hM.hs c' hc

/-- **A level's sums into the inner chain, honestly.** -/
theorem resB_complete {ich ls la lvl h hh a : ℕ} {σ : Val} {i0 i1 s b af P Q : E} (hich : ich < a)
    (hls : ls < a) (hla : la < a) (hh1 : h < a) (hh2 : hh < a) (ha36 : 36 ≤ a)
    (hv : ∀ C rd, H C rd → σ (.n h) = P ∧ σ (.n hh) = Q)
    (hm : ∀ C rd, H C rd → LoadHolds rd (σ (.n ich)) (2 * lvl) i0 ∧
      LoadHolds rd (σ (.n ls)) lvl s ∧ LoadHolds rd (σ (.n ich)) (2 * lvl + 1) i1 ∧
      LoadHolds rd (σ (.n osBetas)) lvl b ∧ LoadHolds rd (σ (.n la)) lvl af ∧
      LoadHolds rd (σ (.n ich)) (2 * lvl + 2) (i0 + s * P) ∧
      LoadHolds rd (σ (.n ich)) (2 * lvl + 3) (i1 + b * af * Q)) :
    BlkA H σ a (a + 10) (resB ich ls la lvl h hh a) (fun _ ↦ True) := by
  have hS : Ssa a (resB ich ls la lvl h hh a) (a + 10) :=
    .cons (.load le_rfl (by omega)) (.cons (.load (by omega) (by omega)) (.cons (.mul (by omega) (by omega) (by omega))
      (.cons (.add (by omega) (by omega) (by omega)) (.cons (.store (by omega) (by omega))
        (.cons (.load (by omega) (by omega)) (.cons (.load (by omega) (by show 23 < a + 5; omega))
          (.cons (.load (by omega) (by omega)) (.cons (.mul (by omega) (by omega) (by omega))
            (.cons (.mul (by omega) (by omega) (by omega)) (.cons (.add (by omega) (by omega) (by omega))
              (.cons (.store (by omega) (by omega)) .nil)))))))))))
  refine ssa_blk (Pt := fun _ ↦ 0) hS (fun _ _ _ _ _ _ _ ↦ trivial) fun C rd hH σ' ha hr ↦ ?_
  obtain ⟨m0, m1, m2, m3, m4, m5, m6⟩ := hm C rd hH
  obtain ⟨v1, v2⟩ := hv C rd hH
  have q0 := memOf_eq (fun C rd hH ↦ (hm C rd hH).1) hH
  have q1 := memOf_eq (fun C rd hH ↦ (hm C rd hH).2.1) hH
  have q2 := memOf_eq (fun C rd hH ↦ (hm C rd hH).2.2.1) hH
  have q3 := memOf_eq (fun C rd hH ↦ (hm C rd hH).2.2.2.1) hH
  have q4 := memOf_eq (fun C rd hH ↦ (hm C rd hH).2.2.2.2.1) hH
  have e3 := hr (a + 3) (by omega) (by omega)
  have e9 := hr (a + 9) (by omega) (by omega)
  simp +arith (disch := omega) only [resB, evalV, stepV, stepW, Function.update_of_ne,
    Function.update_self, le_refl, ↓reduceIte, V.n, osBetas] at e3 e9
  simp +arith only [resB, SidesOk, Side, stepW, ↓reduceIte, true_and, and_true]
  simp only [ha _ hich, ha _ hls, ha _ hla, ha _ (show 23 < a by omega), ha _ hh1, ha _ hh2, e3, e9,
    v1, v2, q0, q1, q2, q3, q4, false_implies, true_and]
  exact ⟨m0, m1, m5, m2, m3, m4, m6⟩

theorem resMem_agree {rd : Reader} {σ σ' : Val} {lvl : ℕ} {lv : OsLv} {bd ich ls la k : ℕ} {RC : E}
    {D : ℕ → E} {hsv : List E} {Pos : ℕ → E} {mu i0 i1 s b a : E} (hbd : bd < k) (hich : ich < k)
    (hls : ls < k) (hla : la < k) (hk : 36 ≤ k) (ha : AgreeBelow k σ σ')
    (h : ResMem rd σ lvl lv bd ich ls la RC D hsv Pos mu i0 i1 s b a) :
    ResMem rd σ' lvl lv bd ich ls la RC D hsv Pos mu i0 i1 s b a where
  mus := by rw [ha osMus (by show 25 < k; omega)]; exact h.mus
  pos := by rw [ha osQpos (by show 33 < k; omega)]; exact h.pos
  row := by rw [ha _ hbd]; exact h.row
  hs := by rw [ha osHs (by show 27 < k; omega)]; exact h.hs
  rc := h.rc
  li0 := by rw [ha _ hich]; exact h.li0
  li1 := by rw [ha _ hich]; exact h.li1
  lsc := by rw [ha _ hls]; exact h.lsc
  lbe := by rw [ha osBetas (by show 23 < k; omega)]; exact h.lbe
  laf := by rw [ha _ hla]; exact h.laf
  st0 := by rw [ha _ hich]; exact h.st0
  st1 := by rw [ha _ hich]; exact h.st1

/-- A level's residual loop call's values from `k`: `μ`, the chains' buffer, the guard, the
bounds. -/
def ResCallV (σ : Val) (k q : ℕ) (mu RC : E) : Prop :=
  σ (.n k) = mu ∧ σ (.n (k + 2)) = RC ∧ σ (.n (k + 7)) = 1 + gen ^ (q / resBatch) ∧
    σ (.n (k + 8)) = 1 ∧ σ (.n (k + 9)) = gen ^ (q / resBatch)

/-- **A level's residual, honestly**: its chains' buffer allocated at `RC`, its loop call's
values. -/
theorem osResidual_complete {c : OsCfg} {ich bd ls la lvl : ℕ} {lv : OsLv} {k : ℕ} {σ : Val} {RC : E}
    {D : ℕ → E} {hsv : List E} {Pos : ℕ → E} {mu i0 i1 s b a : E} (hst : ResStatic lv hsv)
    (hbd : bd < k) (hich : ich < k) (hls : ls < k) (hla : la < k) (hk : 36 ≤ k)
    (hm : ∀ C rd, H C rd → ResMem rd σ lvl lv bd ich ls la RC D hsv Pos mu i0 i1 s b a)
    (hC : ∀ C rd, H C rd → 1 + gen ^ (lv.queries / resBatch) ≠ 0 →
      C (c.resLoop lvl) [1, gen ^ (lv.queries / resBatch), σ (.n osQpos), σ (.n bd), σ (.n osHs), RC,
        mu] []) :
    BlkA H σ k (osResidual c ich bd ls la lvl lv k).2 (osResidual c ich bd ls la lvl lv k).1
      (fun σ' ↦ AllocsAt σ' (osResidual c ich bd ls la lvl lv k).1 =
        [(RC, 2 * (lv.queries / resBatch + 1))] ∧ ResCallV σ' k lv.queries mu RC) := by
  rw [osResidual_eq]
  obtain ⟨t1, t2, t3, -⟩ := resTl_ssa (lvl := lvl) hst hbd hk
  have hA := resA_complete (c := c) (ich := ich) (ls := ls) (la := la) hst hbd hk hm hC
  have hle := t1.le
  have hB := BlkA.seq (H := H) (by omega) (by omega) hA.agree fun σ1 ha1 hO ↦
    resB_complete (H := H) (ich := ich) (ls := ls) (la := la) (lvl := lvl)
      (h := (resTl bd lvl lv k).2.1) (hh := (resTl bd lvl lv k).2.2.1) (a := (resTl bd lvl lv k).2.2.2)
      (i0 := i0) (i1 := i1) (s := s) (b := b) (af := a)
      (P := (resAll lv D hsv Pos mu).1) (Q := (resAll lv D hsv Pos mu).2) (by omega) (by omega)
      (by omega) t2 t3 (by omega) (fun C rd hH ↦ by
        have := (hO C rd hH).1.2.2.2.1
        exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩) fun C rd hH ↦ by
        have h := resMem_agree hbd hich hls hla hk ha1 (hm C rd hH)
        exact ⟨h.li0, h.lsc, h.li1, h.lbe, h.laf, h.st0, h.st1⟩
  refine hB.mono fun σ' hσ' ↦ ?_
  obtain ⟨⟨⟨e0, e1, e2, -, e7, e8, e9⟩, -⟩, -⟩ := hσ'
  refine ⟨?_, e0, e2, e7, e8, e9⟩
  have hnb : 2 * (lv.queries / resBatch + 1) < 2 ^ 64 - 1 := hst.nb64
  rw [allocsAt_append]
  have hB0 : AllocsAt σ' (resB ich ls la lvl (resTl bd lvl lv k).2.1 (resTl bd lvl lv k).2.2.1
      (resTl bd lvl lv k).2.2.2) = [] := rfl
  rw [hB0, List.append_nil]
  simp only [resA, allocsAt_append, t1.allocs, List.append_nil]
  rw [allocsAt_heap σ' _ _ hnb e1, e2]
  rfl

theorem osResidual_next (c : OsCfg) (ich bd ls la lvl : ℕ) {lv : OsLv} {hsv : List E} {k : ℕ}
    (hst : ResStatic lv hsv) (hbd : bd < k) (hk : 36 ≤ k) :
    k ≤ (osResidual c ich bd ls la lvl lv k).2 := by
  rw [osResidual_eq]
  have := (resTl_ssa (lvl := lvl) hst hbd hk).1.le
  dsimp only
  omega

theorem osResiduals_next (c : OsCfg) (ich bd ls la : ℕ) (hsv : ℕ → List E) :
    ∀ (lvs : List OsLv) (lvl k : ℕ), bd < k → 36 ≤ k →
      (∀ i (hi : i < lvs.length), ResStatic lvs[i] (hsv (lvl + i))) →
      k ≤ (osResiduals c ich bd ls la lvl lvs k).2
  | [], _, _, _, _, _ => le_rfl
  | lv :: rest, lvl, k, hbd, hk, hst => by
    have hn : k ≤ (osResidual c ich bd ls la lvl lv k).2 := osResidual_next c ich bd ls la lvl (k := k) (by have := hst 0 (by simp); simpa only [List.getElem_cons_zero, Nat.add_zero] using this) hbd hk
    simp only [osResiduals]
    exact le_trans hn (osResiduals_next c ich bd ls la hsv rest (lvl + 1) _ (by omega) (by omega)
      fun i hi ↦ by
        have := hst (i + 1) (by simp; omega)
        simpa [show lvl + (i + 1) = lvl + 1 + i by ring] using this)

/-- **Every non-final level's residual, honestly**, the levels `lvl ..`: each chains' buffer
allocated at `RC`, each loop call's values. -/
theorem osResiduals_complete {c : OsCfg} {ich bd ls la : ℕ} (RC : ℕ → E) (D : ℕ → ℕ → E)
    (hsv : ℕ → List E) (Pos : ℕ → ℕ → E) (mu I0 I1 S B A : ℕ → E) :
    ∀ (lvs : List OsLv) (lvl k : ℕ) (σ : Val), bd < k → ich < k → ls < k → la < k → 36 ≤ k →
      (∀ i (hi : i < lvs.length), ResStatic lvs[i] (hsv (lvl + i))) →
      (∀ i (hi : i < lvs.length), ∀ C rd, H C rd →
        ResMem rd σ (lvl + i) lvs[i] bd ich ls la (RC (lvl + i)) (D (lvl + i)) (hsv (lvl + i))
          (Pos (lvl + i)) (mu (lvl + i)) (I0 (lvl + i)) (I1 (lvl + i)) (S (lvl + i)) (B (lvl + i))
          (A (lvl + i))) →
      (∀ i (hi : i < lvs.length), ∀ C rd, H C rd → 1 + gen ^ (lvs[i].queries / resBatch) ≠ 0 →
        C (c.resLoop (lvl + i)) [1, gen ^ (lvs[i].queries / resBatch), σ (.n osQpos), σ (.n bd),
          σ (.n osHs), RC (lvl + i), mu (lvl + i)] []) →
      BlkA H σ k (osResiduals c ich bd ls la lvl lvs k).2 (osResiduals c ich bd ls la lvl lvs k).1
        (fun σ' ↦ AllocsAt σ' (osResiduals c ich bd ls la lvl lvs k).1 =
          (List.range lvs.length).map (fun i ↦
            (RC (lvl + i), 2 * ((lvs.getD i default).queries / resBatch + 1))) ∧
          ∀ i < lvs.length, ResCallV σ' (osResiduals c ich bd ls la lvl (lvs.take i) k).2
            (lvs.getD i default).queries (mu (lvl + i)) (RC (lvl + i)))
  | [], _, _, _, _, _, _, _, _, _, _, _ => BlkA.nil fun _ _ ↦ ⟨rfl, fun i hi ↦ absurd hi (by simp)⟩
  | lv :: rest, lvl, k, σ, hbd, hich, hls, hla, hk, hst, hm, hC => by
    have h0 := osResidual_complete (H := H) (c := c) (ich := ich) (ls := ls) (la := la) (lvl := lvl)
      (lv := lv) (k := k) (σ := σ) (RC := RC lvl) (D := D lvl) (hsv := hsv lvl) (Pos := Pos lvl)
      (mu := mu lvl) (i0 := I0 lvl) (i1 := I1 lvl) (s := S lvl) (b := B lvl) (a := A lvl)
      (by have := hst 0 (by simp); simpa only [List.getElem_cons_zero, Nat.add_zero] using this) hbd hich hls hla hk (fun C rd hH ↦ by
        have := hm 0 (by simp) C rd hH; simpa only [List.getElem_cons_zero, Nat.add_zero] using this)
      (fun C rd hH h ↦ by
        have := hC 0 (by simp) C rd hH (by simpa only [List.getElem_cons_zero] using h)
        simpa only [List.getElem_cons_zero, Nat.add_zero] using this)
    have hn : k ≤ (osResidual c ich bd ls la lvl lv k).2 := osResidual_next c ich bd ls la lvl (k := k) (by have := hst 0 (by simp); simpa only [List.getElem_cons_zero, Nat.add_zero] using this) hbd hk
    set r := osResidual c ich bd ls la lvl lv k with hr
    have hst' : ∀ i (hi : i < rest.length), ResStatic rest[i] (hsv (lvl + 1 + i)) := fun i hi ↦ by
      have := hst (i + 1) (by simp; omega)
      simpa [show lvl + (i + 1) = lvl + 1 + i by ring] using this
    have hn2 := osResiduals_next c ich bd ls la hsv rest (lvl + 1) r.2 (by omega) (by omega) hst'
    have hB := BlkA.seq (H := H) hn hn2 h0.agree fun σ1 ha1 _ ↦
      osResiduals_complete RC D hsv Pos mu I0 I1 S B A rest (lvl + 1) r.2 σ1 (by omega) (by omega)
        (by omega) (by omega) (by omega) hst'
        (fun i hi C rd hH ↦ by
          have := resMem_agree hbd hich hls hla hk (ha1.mono le_rfl) (hm (i + 1) (by simp; omega) C rd hH)
          simpa [show lvl + (i + 1) = lvl + 1 + i by ring] using this)
        fun i hi C rd hH hne ↦ by
          have := hC (i + 1) (by simp; omega) C rd hH (by simpa using hne)
          rw [ha1 osQpos (by show 33 < k; omega), ha1 _ hbd, ha1 osHs (by show 27 < k; omega)]
          simpa [show lvl + (i + 1) = lvl + 1 + i by ring] using this
    refine (hB.congr (by simp only [osResiduals, ← hr])).mono fun σ' hσ' ↦ ?_
    obtain ⟨⟨⟨h1, v0⟩, -⟩, h2, vs⟩ := hσ'
    refine ⟨?_, fun i hi ↦ ?_⟩
    swap
    · rcases i with _ | i
      · simpa [osResiduals] using v0
      · have := vs i (by simp at hi; omega)
        rw [show (osResiduals c ich bd ls la lvl (List.take (i + 1) (lv :: rest)) k).2 =
          (osResiduals c ich bd ls la (lvl + 1) (rest.take i) r.2).2 from rfl]
        simpa [show lvl + 1 + i = lvl + (i + 1) by ring] using this
    simp only [osResiduals, ← hr]
    rw [allocsAt_append, h1, h2, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Nat.add_zero, List.getD_cons_zero, List.cons_append, List.nil_append]
    congr 1
    refine List.map_congr_left fun i _ ↦ ?_
    simp [show lvl + 1 + i = lvl + (i + 1) by ring]

end
end LeanVM.Guest.B1.Whir
