/-
  LeanVM.Guest.B1.Selectors.SelPartialComplete

  `sel_partial_nibble` is complete: for `w < 4` coordinates, complements and shares in memory,
  with their eq levels and `g`-power table written, the run is an outcome of
  `sel_partial_nibble__L{w}`.
-/

module

public import LeanVM.Guest.B1.Selectors.SelPartial

/-!
# `sel_partial_nibble` is complete (TRIAGE G #45-47)

The valuation `spVal` gives each value of `sel_partial_nibble__L{w}`'s body its role: the
parameters; the eq levels' entries (`spLvV t i = Π_{s ≤ t} (bit s of i ? z_s : z1_s)`) and the
coordinates and complements each level loads; the `g` table's entries
(`spGV w u = Π_{s < w} (bit s of u ? g_s : 1)`) and the shares each step loads; and the returned
`0`. Every statement holds of it: the products by the bits of the entries' indices, the loads by
the tables in memory (`eqLevels_getD`, `gTable_getD`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Finset

@[expose] public section

/-- Entry `i` of eq level `t`. -/
def spLvV (zs zs1 : List E) (t i : ℕ) : E :=
  ∏ s ∈ range (t + 1), bitPick i s (zs.getD s 0) (zs1.getD s 0)

/-- Entry `u` of the `g` table over `w` shares. -/
def spGV (w : ℕ) (gl : List E) (u : ℕ) : E := ∏ s ∈ range w, bitPick u s (gl.getD s 0) 1

/-- Value `k` of `sel_partial_nibble__L{w}` (`w ≤ 3`). -/
def spVal (w : ℕ) (P zs zs1 gl : List E) (k : ℕ) : E :=
  if k < 5 then P.getD k 0
  else if k = spC w + 2 ^ w + w - 1 then 0
  else if k < spC w then
    if k < 7 then spLvV zs zs1 0 (k - 5)
    else
      let t := if k < 13 then 1 else 2
      if k = spM t - 2 then zs.getD t 0 else if k = spM t - 1 then zs1.getD t 0
      else spLvV zs zs1 t (if (k - spM t) % 2 = 0 then (k - spM t) / 2
        else 2 ^ t + (k - spM t) / 2)
  else
    let j := k - spC w
    if j = 0 then spGV w gl 0 else if j = 1 then spGV w gl 1 else if j = 2 then gl.getD 1 0
    else if j < 5 then spGV w gl (j - 1) else if j = 5 then gl.getD 2 0 else spGV w gl (j - 2)

/-! ## The roles -/

theorem spVal_lv {w : ℕ} (hw : w ≤ 3) (P zs zs1 gl : List E) {t i : ℕ} (ht : t < w)
    (hi : i < 2 ^ (t + 1)) : spVal w P zs zs1 gl (spLv t i) = spLvV zs zs1 t i := by
  interval_cases w <;> interval_cases t <;> interval_cases i <;> simp [spVal, spLv, spM, spC]

theorem spVal_z {w : ℕ} (hw : w ≤ 3) (P zs zs1 gl : List E) {t : ℕ} (ht1 : 1 ≤ t) (ht : t < w) :
    spVal w P zs zs1 gl (spM t - 2) = zs.getD t 0 ∧
      spVal w P zs zs1 gl (spM t - 1) = zs1.getD t 0 := by
  interval_cases w <;> interval_cases t <;> simp [spVal, spM, spC]

theorem spVal_gl {w : ℕ} (hw : w ≤ 3) (P zs zs1 gl : List E) {t : ℕ} (ht1 : 1 ≤ t)
    (ht : t < w) : spVal w P zs zs1 gl (spC w + 2 ^ t + t - 1) = gl.getD t 0 := by
  interval_cases w <;> interval_cases t <;> simp [spVal, spC]

theorem sp_log2 : Nat.log2 2 = 1 ∧ Nat.log2 3 = 1 ∧ Nat.log2 4 = 2 ∧ Nat.log2 5 = 2 ∧
    Nat.log2 6 = 2 ∧ Nat.log2 7 = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact (Nat.log2_eq_iff (by norm_num)).mpr ⟨by norm_num, by norm_num⟩

theorem spVal_G {w : ℕ} (hw1 : 1 ≤ w) (hw : w ≤ 3) (P zs zs1 gl : List E) {u : ℕ}
    (hu : u < 2 ^ w) : spVal w P zs zs1 gl (spG w u) = spGV w gl u := by
  obtain ⟨l2, l3, l4, l5, l6, l7⟩ := sp_log2
  interval_cases w <;> interval_cases u <;> simp [spVal, spG, spC, l2, l3, l4, l5, l6, l7]

theorem spVal_Gstep {w : ℕ} (hw : w ≤ 3) (P zs zs1 gl : List E) {t i : ℕ} (ht1 : 1 ≤ t)
    (ht : t < w) (hi : i < 2 ^ t) :
    spVal w P zs zs1 gl (spC w + 2 ^ t + t + i) = spGV w gl (2 ^ t + i) := by
  interval_cases w <;> interval_cases t <;> interval_cases i <;> simp [spVal, spC]

theorem spVal_last {w : ℕ} (P zs zs1 gl : List E) :
    spVal w P zs zs1 gl (spC w + 2 ^ w + w - 1) = 0 := by
  have := Nat.one_le_two_pow (n := w)
  have : ¬ spC w + 2 ^ w + w - 1 < 5 := by simp only [spC]; omega
  simp [spVal, this]

theorem spVal_param {w : ℕ} (P zs zs1 gl : List E) {k : ℕ} (hk : k < 5) :
    spVal w P zs zs1 gl k = P.getD k 0 := by
  simp [spVal, hk]

/-! ## The products -/

theorem spLvV_lo (zs zs1 : List E) {t i : ℕ} (hi : i < 2 ^ t) :
    spLvV zs zs1 t i = spLvV zs zs1 (t - 1) i * zs1.getD t 0 ∨ t = 0 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact Or.inr rfl
  · left
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rw [spLvV, prod_range_succ, bitPick, testBit_lt_two_pow hi, Nat.add_sub_cancel]
    rfl

theorem spLvV_hi (zs zs1 : List E) {t i : ℕ} (ht : 1 ≤ t) (hi : i < 2 ^ t) :
    spLvV zs zs1 t (2 ^ t + i) = spLvV zs zs1 (t - 1) i * zs.getD t 0 := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [spLvV, prod_range_succ, bitPick, testBit_two_pow_add_self hi, Nat.add_sub_cancel]
  simp only [↓reduceIte, spLvV]
  congr 1
  exact prod_congr rfl fun r hr => by
    simp only [bitPick, testBit_two_pow_add hi (by simpa using hr)]

theorem spGV_step (w : ℕ) (gl : List E) {t i : ℕ} (ht : t < w) (hi : i < 2 ^ t) :
    spGV w gl (2 ^ t + i) = spGV w gl i * gl.getD t 0 := by
  have key : ∀ s ∈ range w, bitPick (2 ^ t + i) s (gl.getD s 0) 1 =
      bitPick i s (gl.getD s 0) 1 * (if s = t then gl.getD t 0 else 1) := by
    intro s hs
    rcases lt_trichotomy s t with h1 | rfl | h1
    · simp only [bitPick, testBit_two_pow_add hi h1, show s ≠ t by omega, ↓reduceIte, mul_one]
    · simp [bitPick, testBit_two_pow_add_self hi, testBit_lt_two_pow hi]
    · have e1 : (2 ^ t + i).testBit s = false := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le (show 2 ^ t + i < 2 ^ (t + 1) by rw [pow_succ]; omega)
          (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have e2 : i.testBit s = false := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [bitPick, e1, e2, show s ≠ t by omega]
  rw [spGV, spGV, prod_congr rfl key, prod_mul_distrib, prod_ite_eq' (range w) t]
  simp only [mem_range, ht, ↓reduceIte]

/-! ## The body -/

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

theorem holds_spLevel_iff {t : ℕ} :
    Stmt.HoldsList C rd σ (spLevel t) True kret ↔
      (LoadHolds rd (σ (.n 2)) t (σ (.n (spM t - 2))) ∧
        LoadHolds rd (σ (.n 3)) t (σ (.n (spM t - 1)))) ∧
      ∀ i < 2 ^ t, σ (.n (spM t + 2 * i)) = σ (.n (spLv (t - 1) i)) * σ (.n (spM t - 1)) ∧
        σ (.n (spM t + 2 * i + 1)) = σ (.n (spLv (t - 1) i)) * σ (.n (spM t - 2)) := by
  rw [spLevel, tb_holdsList_append_noRet rfl, tb_holdsList_flatten_range _ _ (fun _ => rfl)]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]

theorem holds_spGStep_iff {w t : ℕ} :
    Stmt.HoldsList C rd σ (spGStep w t) True kret ↔
      LoadHolds rd (σ (.n 4)) t (σ (.n (spC w + 2 ^ t + t - 1))) ∧
      ∀ i < 2 ^ t, σ (.n (spC w + 2 ^ t + t + i)) =
        σ (.n (spG w i)) * σ (.n (spC w + 2 ^ t + t - 1)) := by
  rw [spGStep, show ∀ (a : Stmt) (l : List Stmt), a :: l = [a] ++ l from fun _ _ => rfl,
    tb_holdsList_append_noRet rfl, tb_holdsList_mapAtoms]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]

theorem holds_spPre_iff {w : ℕ} :
    Stmt.HoldsList C rd σ (spPre w) True kret ↔
    ((((((LoadHolds rd (σ (.n 3)) 0 (σ (.n 5)) ∧ LoadHolds rd (σ (.n 2)) 0 (σ (.n 6))) ∧
    (∀ t < w - 1, Stmt.HoldsList C rd σ (spLevel (t + 1)) True kret)) ∧
    (∀ e < 2 ^ (w + 1) - 2, LoadHolds rd (σ (.n 0)) e (σ (.n (spEq e))))) ∧
    (σ (.n (spC w)) = word 1 0 0 ∧ LoadHolds rd (σ (.n 4)) 0 (σ (.n (spC w + 1))))) ∧
    (∀ t < w - 1, Stmt.HoldsList C rd σ (spGStep w (t + 1)) True kret)) ∧
    (∀ u < 2 ^ w, LoadHolds rd (σ (.n 1)) u (σ (.n (spG w u))))) ∧
    σ (.n (spC w + 2 ^ w + w - 1)) = word 0 0 0 := by
  have nL := tb_noRetList_flatten_range (w - 1) _ (fun t => spLevel_noRet (t + 1))
  have nG := tb_noRetList_flatten_range (w - 1) _ (fun t => spGStep_noRet w (t + 1))
  have nA := tb_noRetList_mapAtoms (2 ^ (w + 1) - 2) (fun e ↦ .load (.n (spEq e)) (.n 0) e)
  have nB := tb_noRetList_mapAtoms (2 ^ w) (fun u ↦ .load (.n (spG w u)) (.n 1) u)
  have n0 : Stmt.noRetList [Stmt.atom (.load (.n 5) (.n 3) 0), Stmt.atom (.load (.n 6) (.n 2) 0)] =
    true := rfl
  have n1 : Stmt.noRetList [Stmt.atom (.const (.n (spC w)) (word 1 0 0)),
    Stmt.atom (.load (.n (spC w + 1)) (.n 4) 0)] = true := rfl
  rw [spPre]
  rw [tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nL, nG, nA, nB, n0, n1,
      Bool.and_self]),
    tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nL, nG, nA, n0, n1,
      Bool.and_self]),
    tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nL, nA, n0, n1, Bool.and_self]),
    tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nL, nA, n0, Bool.and_self]),
    tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nL, n0, Bool.and_self]),
    tb_holdsList_append_noRet n0, tb_holdsList_mapAtoms, tb_holdsList_mapAtoms,
    tb_holdsList_flatten_range _ _ (fun t => spLevel_noRet (t + 1)),
    tb_holdsList_flatten_range _ _ (fun t => spGStep_noRet w (t + 1))]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]

end Sem

/-- **`sel_partial_nibble` is complete** at its four specializations. -/
theorem sel_partial_nibble_complete_holds : sel_partial_nibble_complete_Spec := by
  intro w hw rd args rets h
  match args, rets, h with
  | [eqo, go, z, z1, gs], [r], ⟨hr, zs, zs1, gl, hzl, hz1l, hgl, hzr, hz1r, hglr, heqr, hgr⟩ =>
    obtain ⟨fn, hf, hp, hb⟩ := spFound hw
    set P : List E := [eqo, go, z, z1, gs]
    set F := spVal w P zs zs1 gl with hF
    have hw3 : w ≤ 3 := by omega
    refine (tb_rel_iff_sem hf _ _).mpr ⟨fun x ↦ F x.idx, ?_, ?_⟩
    · rw [hp]; simp only [List.map_cons, List.map_nil]
      simp [hF, spVal_param, P]
    have l0 : spVal w P zs zs1 gl 0 = eqo := by simp [spVal_param, P]
    have l1 : spVal w P zs zs1 gl 1 = go := by simp [spVal_param, P]
    have l2 : spVal w P zs zs1 gl 2 = z := by simp [spVal_param, P]
    have l3 : spVal w P zs zs1 gl 3 = z1 := by simp [spVal_param, P]
    have l4 : spVal w P zs zs1 gl 4 = gs := by simp [spVal_param, P]
    have hlast := spVal_last (w := w) P zs zs1 gl
    rw [hb]
    by_cases hw0 : w = 0
    · subst hw0
      simp only [spBody, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
        List.map_nil]
      have : F 5 = 0 := hlast
      exact ⟨by rw [this, tb_word_zero], by rw [this, hr]⟩
    simp only [spBody, hw0, ↓reduceIte]
    rw [holdsList_append, holdsList_noRet _ (spPre_noRet w)]
    refine ⟨holds_spPre_iff.mpr ?_, ?_⟩
    swap
    · simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil]
      show [F (spC w + 2 ^ w + w - 1)] = [r]
      rw [hF, hlast, hr]
    have lz : ∀ t < w, LoadHolds rd z t (zs.getD t 0) := fun t ht ↦ by
      have := hzr t (by omega); rwa [← List.getD_eq_getElem _ 0] at this
    have lz1 : ∀ t < w, LoadHolds rd z1 t (zs1.getD t 0) := fun t ht ↦ by
      have := hz1r t (by omega); rwa [← List.getD_eq_getElem _ 0] at this
    have lgl : ∀ t < w, LoadHolds rd gs t (gl.getD t 0) := fun t ht ↦ by
      have := hglr t (by omega); rwa [← List.getD_eq_getElem _ 0] at this
    have lv0 : ∀ i < 2, spLvV zs zs1 0 i = bitPick i 0 (zs.getD 0 0) (zs1.getD 0 0) := by
      intro i _; simp [spLvV]
    refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · -- the first coordinate and complement
      show LoadHolds rd (F 3) 0 (F 5) ∧ LoadHolds rd (F 2) 0 (F 6)
      have e5 : F 5 = spLvV zs zs1 0 0 := spVal_lv hw3 P zs zs1 gl (t := 0) (i := 0)
        (by omega) (by norm_num)
      have e6 : F 6 = spLvV zs zs1 0 1 := spVal_lv hw3 P zs zs1 gl (t := 0) (i := 1)
        (by omega) (by norm_num)
      rw [hF, l3, l2] at *
      rw [e5, e6, lv0 0 (by norm_num), lv0 1 (by norm_num)]
      simp only [bitPick, Nat.zero_testBit, Nat.testBit_one_zero, Bool.false_eq_true, ↓reduceIte]
      exact ⟨lz1 0 (by omega), lz 0 (by omega)⟩
    · -- the levels
      intro t ht
      rw [holds_spLevel_iff]
      obtain ⟨ez, ez1⟩ := spVal_z hw3 P zs zs1 gl (t := t + 1) (by omega) (by omega)
      show (LoadHolds rd (F 2) (t + 1) (F (spM (t + 1) - 2)) ∧
        LoadHolds rd (F 3) (t + 1) (F (spM (t + 1) - 1))) ∧ ∀ i < 2 ^ (t + 1),
          F (spM (t + 1) + 2 * i) = F (spLv (t + 1 - 1) i) * F (spM (t + 1) - 1) ∧
          F (spM (t + 1) + 2 * i + 1) = F (spLv (t + 1 - 1) i) * F (spM (t + 1) - 2)
      rw [hF, l2, l3, ez, ez1]
      refine ⟨⟨lz _ (by omega), lz1 _ (by omega)⟩, fun i hi ↦ ?_⟩
      have a1 : spM (t + 1) + 2 * i = spLv (t + 1) i := by
        simp only [spLv, Nat.succ_ne_zero, ↓reduceIte, hi]
      have a2 : spM (t + 1) + 2 * i + 1 = spLv (t + 1) (2 ^ (t + 1) + i) := by
        simp only [spLv, Nat.succ_ne_zero, ↓reduceIte, show ¬ 2 ^ (t + 1) + i < 2 ^ (t + 1) by omega,
          Nat.add_sub_cancel_left]
      have h2 : 2 ^ (t + 1) + i < 2 ^ (t + 1 + 1) := by rw [pow_succ 2 (t + 1)]; omega
      rw [a2, a1, spVal_lv hw3 P zs zs1 gl (by omega) (by rw [pow_succ]; omega),
        spVal_lv hw3 P zs zs1 gl (by omega) h2, Nat.add_sub_cancel,
        spVal_lv hw3 P zs zs1 gl (by omega) (by rw [pow_succ] at hi ⊢; omega),
        spLvV_hi zs zs1 (by omega) hi, Nat.add_sub_cancel]
      refine ⟨?_, rfl⟩
      rcases spLvV_lo zs zs1 (t := t + 1) hi with h | h
      · rw [h, Nat.add_sub_cancel]
      · omega
    · -- the eq levels
      intro e he
      show LoadHolds rd (F 0) e (F (spEq e))
      obtain ⟨t, i, ht, hi, hei, hst⟩ : ∃ t i, t < w ∧ i < 2 ^ (t + 1) ∧
          e = 2 ^ (t + 1) - 2 + i ∧ spEq e = spLv t i := by
        by_cases e2 : e < 2
        · exact ⟨0, e, by omega, by simpa using e2, by simp, by simp [spEq, e2]⟩
        by_cases e6 : e < 6
        · have hw2 : 2 ≤ w := by
            by_contra hc
            have : w = 1 := by omega
            subst this; simp at he; omega
          exact ⟨1, e - 2, by omega, by simp; omega, by simp; omega, by simp [spEq, e2, e6]⟩
        · have hw3' : w = 3 := by
            interval_cases w <;> simp at he <;> omega
          subst hw3'
          have e14 : e < 14 := by simp at he; omega
          exact ⟨2, e - 6, by omega, by simp; omega, by simp; omega,
            by simp [spEq, e2, e6, e14]⟩
      rw [hst, hF, l0, spVal_lv hw3 P zs zs1 gl ht hi]
      have hlen := eqLevels_length hzl hz1l
      have hv : (eqLevels zs zs1).getD e 0 = spLvV zs zs1 t i := by
        rw [hei, eqLevels_getD (hzl.trans hz1l.symm) (by omega) (by omega) hi, spLvV]
      have := heqr e (by rw [hlen]; exact he)
      rwa [← List.getD_eq_getElem _ 0, hv] at this
    · -- the one
      show F (spC w) = word 1 0 0
      have := spVal_G (by omega) hw3 P zs zs1 gl (u := 0) (by positivity)
      simp only [spG, ↓reduceIte] at this
      rw [hF, this, tb_word_one, spGV]
      exact prod_eq_one fun s _ ↦ by simp [bitPick]
    · -- the first share
      show LoadHolds rd (F 4) 0 (F (spC w + 1))
      have := spVal_G (by omega) hw3 P zs zs1 gl (u := 1) (Nat.one_lt_two_pow (by omega))
      simp only [spG, one_ne_zero, ↓reduceIte] at this
      rw [hF, this, l4]
      have hg1 : spGV w gl 1 = gl.getD 0 0 := by
        obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
        have := spGV_step (v + 1) gl (t := 0) (i := 0) (by omega) (by norm_num)
        simp only [pow_zero, add_zero] at this
        rw [this]
        rw [show spGV (v + 1) gl 0 = 1 from prod_eq_one fun s _ ↦ by simp [bitPick], one_mul]
      rw [hg1]; exact lgl 0 (by omega)
    · -- the g steps
      intro t ht
      rw [holds_spGStep_iff]
      show LoadHolds rd (F 4) (t + 1) (F (spC w + 2 ^ (t + 1) + (t + 1) - 1)) ∧
        ∀ i < 2 ^ (t + 1), F (spC w + 2 ^ (t + 1) + (t + 1) + i) =
          F (spG w i) * F (spC w + 2 ^ (t + 1) + (t + 1) - 1)
      rw [hF, l4, spVal_gl hw3 P zs zs1 gl (by omega) (by omega)]
      refine ⟨lgl _ (by omega), fun i hi ↦ ?_⟩
      rw [spVal_Gstep hw3 P zs zs1 gl (by omega) (by omega) hi,
        spVal_G (by omega) hw3 P zs zs1 gl (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num)
          (by omega))), spGV_step w gl (by omega) hi]
    · -- the g table
      intro u hu
      show LoadHolds rd (F 1) u (F (spG w u))
      rw [hF, l1, spVal_G (by omega) hw3 P zs zs1 gl hu]
      have hlen := gTable_length hgl
      have := hgr
      simp only [hw0, ↓reduceIte] at this
      have h2 := this u (by rw [hlen]; exact hu)
      rwa [← List.getD_eq_getElem _ 0, gTable_getD hgl hu] at h2
    · -- the return
      show F (spC w + 2 ^ w + w - 1) = word 0 0 0
      rw [hF, hlast, tb_word_zero]
  | [], _, h => simp [SelPartialOut] at h
  | [_], _, h => simp [SelPartialOut] at h
  | [_, _], _, h => simp [SelPartialOut] at h
  | [_, _, _], _, h => simp [SelPartialOut] at h
  | [_, _, _, _], _, h => simp [SelPartialOut] at h
  | _ :: _ :: _ :: _ :: _ :: _ :: _, _, h => simp [SelPartialOut] at h
  | [_, _, _, _, _], [], h => simp [SelPartialOut] at h
  | [_, _, _, _, _], _ :: _ :: _, h => simp [SelPartialOut] at h

end
end LeanVM.Guest.B1.Tables
