/-
  LeanVM.Guest.B1.Selectors.SharedTablesComplete

  `shared_selector_tables` is complete: for `n < 64` coordinates, complements and shares in
  memory, with their nibble tables written, the run is an outcome of `shared_selector_tables`.
-/

module

public import LeanVM.Guest.B1.Selectors.SharedTables
public import LeanVM.Guest.B1.Selectors.SelPartialComplete

/-!
# `shared_selector_tables` is complete (TRIAGE G #48)

* `__loop8`: the valuation `lpVal` gives each value of an iteration at `x = g^j` its role: the
  powers of `x` and the pointers; the eq levels' entries of nibble `j` (`spLvV`) and the
  coordinates and complements each level loads; the `g` table's entries (`spGV`) and the shares
  each step loads; the next `x`. `lp_complete`: from `g^j`, `j < q`, the iterations run to `g^q`.
* `shared_selector_tables`: the valuation `ssVal` gives the hint's six bits of `n`, the factors,
  `g^r`, `g^q` (`n = 4q + r`), the pointers of the partial nibble; the loop runs the full nibbles
  and `sel_partial_nibble__L{r}` the partial one (`sel_partial_nibble_complete_holds`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Finset

@[expose] public section

/-! ## The loop's roles -/

/-- Value `o` of the eq levels' block (value `15 + o`) of nibble coordinates `zz`, `zz1`. -/
def lpEq (zz zz1 : List E) (o : ℕ) : E :=
  if o < 2 then spLvV zz zz1 0 o
  else if o < 8 then
    if o = 2 then zz.getD 1 0 else if o = 3 then zz1.getD 1 0
    else if (o - 4) % 2 = 0 then spLvV zz zz1 1 ((o - 4) / 2) else spLvV zz zz1 1 (2 + (o - 4) / 2)
  else if o < 18 then
    if o = 8 then zz.getD 2 0 else if o = 9 then zz1.getD 2 0
    else if (o - 10) % 2 = 0 then spLvV zz zz1 2 ((o - 10) / 2)
    else spLvV zz zz1 2 (4 + (o - 10) / 2)
  else
    if o = 18 then zz.getD 3 0 else if o = 19 then zz1.getD 3 0
    else if (o - 20) % 2 = 0 then spLvV zz zz1 3 ((o - 20) / 2)
    else spLvV zz zz1 3 (8 + (o - 20) / 2)

/-- Value `o` of the `g` table's block (value `53 + o`) of nibble shares `gl`. -/
def lpG (gl : List E) (o : ℕ) : E :=
  if o < 2 then spGV 4 gl o
  else if o = 2 then gl.getD 1 0 else if o < 5 then spGV 4 gl (o - 1)
  else if o = 5 then gl.getD 2 0 else if o < 10 then spGV 4 gl (o - 2)
  else if o = 10 then gl.getD 3 0 else spGV 4 gl (o - 3)

/-- **Value `x` of `__loop8`'s iteration at `g^j`.** -/
def lpVal (j : ℕ) (N eqt z z1 gt gsq : E) (zs zs1 gs : List E) (x : ℕ) : E :=
  if x < 7 then [gen ^ j, N, eqt, z, z1, gt, gsq].getD x 0
  else if x < 15 then
    [gen ^ j * gen ^ j, gen ^ j * gen ^ j * (gen ^ j * gen ^ j),
      gen ^ j * gen ^ j * (gen ^ j * gen ^ j) * (gen ^ j * gen ^ j * (gen ^ j * gen ^ j)),
      gen ^ j * gen ^ j * (gen ^ j * gen ^ j) * (gen ^ j * gen ^ j * (gen ^ j * gen ^ j)) *
        (gen ^ j * gen ^ j * (gen ^ j * gen ^ j) * (gen ^ j * gen ^ j * (gen ^ j * gen ^ j))),
      eqt * gen ^ (16 * j), eqt * gen ^ (16 * j) * gen ^ (16 * j),
      z * (gen ^ j * gen ^ j * (gen ^ j * gen ^ j)),
      z1 * (gen ^ j * gen ^ j * (gen ^ j * gen ^ j))].getD (x - 7) 0
  else if x < 51 then lpEq (nib zs j) (nib zs1 j) (x - 15)
  else if x = 51 then gt * gen ^ (16 * j)
  else if x = 52 then gsq * (gen ^ j * gen ^ j * (gen ^ j * gen ^ j))
  else if x < 72 then lpG (nib gs j) (x - 53)
  else [word 2 0 0, gen ^ j * word 2 0 0, gen ^ j * word 2 0 0 + N, word 2 0 0,
    gen ^ j * word 2 0 0].getD (x - 72) 0

theorem lp_pow4 (j : ℕ) : gen ^ j * gen ^ j * (gen ^ j * gen ^ j) = gen ^ (4 * j) := by ring

/-! ## The loop's roles at the template's values -/

section Roles

variable (j : ℕ) (N eqt z z1 gt gsq : E) (zs zs1 gs : List E)

theorem lpVal_lv {t i : ℕ} (ht : t < 4) (hi : i < 2 ^ (t + 1)) :
    lpVal j N eqt z z1 gt gsq zs zs1 gs (nbLv 15 t i) = spLvV (nib zs j) (nib zs1 j) t i := by
  interval_cases t <;> interval_cases i <;> simp [lpVal, lpEq, nbLv, nbM]

theorem lpVal_z {t : ℕ} (ht : t < 4) :
    lpVal j N eqt z z1 gt gsq zs zs1 gs (nbZ 15 t) = (nib zs j).getD t 0 := by
  interval_cases t <;> simp [lpVal, lpEq, nbZ, nbM, spLvV, bitPick]

theorem lpVal_z1 {t : ℕ} (ht : t < 4) :
    lpVal j N eqt z z1 gt gsq zs zs1 gs (nbZ1 15 t) = (nib zs1 j).getD t 0 := by
  interval_cases t <;> simp [lpVal, lpEq, nbZ1, nbM, spLvV, bitPick]

theorem lpVal_g {u : ℕ} (hu : u < 16) :
    lpVal j N eqt z z1 gt gsq zs zs1 gs (nbGV 53 u) = spGV 4 (nib gs j) u := by
  have l2 : Nat.log2 2 = 1 ∧ Nat.log2 3 = 1 ∧ Nat.log2 4 = 2 ∧ Nat.log2 5 = 2 ∧
      Nat.log2 6 = 2 ∧ Nat.log2 7 = 2 := sp_log2
  have l8 : ∀ v < 8, Nat.log2 (8 + v) = 3 := fun v hv ↦
    (Nat.log2_eq_iff (by omega)).mpr ⟨by norm_num, by norm_num; omega⟩
  obtain ⟨l2, l3, l4, l5, l6, l7⟩ := l2
  interval_cases u <;>
    simp [lpVal, lpG, nbGV, l2, l3, l4, l5, l6, l7, l8 0 (by norm_num), l8 1 (by norm_num),
      l8 2 (by norm_num), l8 3 (by norm_num), l8 4 (by norm_num), l8 5 (by norm_num),
      l8 6 (by norm_num), l8 7 (by norm_num)]

theorem lpVal_gl {t : ℕ} (ht1 : 1 ≤ t) (ht : t < 4) :
    lpVal j N eqt z z1 gt gsq zs zs1 gs (53 + 2 ^ t + t - 1) = (nib gs j).getD t 0 := by
  interval_cases t <;> simp [lpVal, lpG]

theorem lpVal_gstep {t i : ℕ} (ht1 : 1 ≤ t) (ht : t < 4) (hi : i < 2 ^ t) :
    lpVal j N eqt z z1 gt gsq zs zs1 gs (53 + 2 ^ t + t + i) = spGV 4 (nib gs j) (2 ^ t + i) := by
  interval_cases t <;> interval_cases i <;> simp [lpVal, lpG]

end Roles

/-! ## An iteration -/

/-- Unfold `lpVal` at a numeral. -/
local macro "sv" : tactic => `(tactic| simp (config := { decide := true }) only [lpVal, ↓reduceIte,
  List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
  Nat.reduceSub, Nat.reduceAdd])

theorem lp_isInK_add_pow (a b : ℕ) : IsInK (gen ^ a + gen ^ b) := by
  rw [gen_pow_eq_ofK, gen_pow_eq_ofK, ← ofK_add]
  exact (isInK_iff _).mpr ⟨_, rfl⟩

/-- The nibble's eq levels' entry `e` is level `t`'s entry `i`. -/
theorem lp_eqEntry {e : ℕ} (he : e < 30) : ∃ t i, t < 4 ∧ i < 2 ^ (t + 1) ∧
    e = 2 ^ (t + 1) - 2 + i ∧ nbEqV 15 e = nbLv 15 t i := by
  by_cases e2 : e < 2
  · exact ⟨0, e, by omega, by simpa using e2, by simp, by simp [nbEqV, e2]⟩
  by_cases e6 : e < 6
  · exact ⟨1, e - 2, by omega, by simp; omega, by simp; omega, by simp [nbEqV, e2, e6]⟩
  by_cases e14 : e < 14
  · exact ⟨2, e - 6, by omega, by simp; omega, by simp; omega, by simp [nbEqV, e2, e6, e14]⟩
  exact ⟨3, e - 14, by omega, by simp; omega, by simp; omega, by simp [nbEqV, e2, e6, e14]⟩

/-- **An iteration of `__loop8`** at `g^j`: its nibble's coordinates, complements and shares in
memory and their tables written, and the next iteration's relation unless `j + 1 = q`. -/
theorem lp_iter {rd : Reader} {eqt z z1 gt gsq : E} {q j : ℕ} (hj : j < q)
    {zs zs1 gs : List E} (hlz : 4 * q ≤ zs.length) (hlz1 : 4 * q ≤ zs1.length)
    (hlg : 4 * q ≤ gs.length) (hz : TbReadsAt rd z zs) (hz1 : TbReadsAt rd z1 zs1)
    (hg : TbReadsAt rd gsq gs)
    (htab : TbReadsAt rd (eqt * gen ^ (32 * j)) (eqLevels (nib zs j) (nib zs1 j)) ∧
      TbReadsAt rd (gt * gen ^ (16 * j)) (gTable (nib gs j)))
    (hnext : j + 1 < q → coreProgram.Rel rd "__loop8"
      [gen ^ (j + 1), gen ^ q, eqt, z, z1, gt, gsq] []) :
    coreProgram.Rel rd "__loop8" [gen ^ j, gen ^ q, eqt, z, z1, gt, gsq] [] := by
  obtain ⟨fn, hf, hp, hb⟩ := lpFound
  set F := lpVal j (gen ^ q) eqt z z1 gt gsq zs zs1 gs with hF
  have hlen : ∀ l : List E, 4 * q ≤ l.length → (nib l j).length = 4 := fun l hl ↦ by
    simp [nib]; omega
  have hzz := hlen zs hlz
  have hzz1 := hlen zs1 hlz1
  have hgl := hlen gs hlg
  have rz : TbReadsAt rd (z * gen ^ (4 * j)) (nib zs j) := tbReadsAt_nib hz j
  have rz1 : TbReadsAt rd (z1 * gen ^ (4 * j)) (nib zs1 j) := tbReadsAt_nib hz1 j
  have rg : TbReadsAt rd (gsq * gen ^ (4 * j)) (nib gs j) := tbReadsAt_nib hg j
  have lz : ∀ t < 4, LoadHolds rd (z * gen ^ (4 * j)) t ((nib zs j).getD t 0) := fun t ht ↦
    tbReadsAt_getD rz (by omega)
  have lz1 : ∀ t < 4, LoadHolds rd (z1 * gen ^ (4 * j)) t ((nib zs1 j).getD t 0) := fun t ht ↦
    tbReadsAt_getD rz1 (by omega)
  have lg : ∀ t < 4, LoadHolds rd (gsq * gen ^ (4 * j)) t ((nib gs j).getD t 0) := fun t ht ↦
    tbReadsAt_getD rg (by omega)
  have f2 : F 2 = eqt := by simp [hF, lpVal]
  have f12 : F 12 = eqt * gen ^ (32 * j) := by
    rw [hF]; sv
    rw [mul_assoc, ← pow_add, show 16 * j + 16 * j = 32 * j by ring]
  have f13 : F 13 = z * gen ^ (4 * j) := by
    rw [hF]; sv
    rw [lp_pow4]
  have f14 : F 14 = z1 * gen ^ (4 * j) := by
    rw [hF]; sv
    rw [lp_pow4]
  have f51 : F 51 = gt * gen ^ (16 * j) := by rw [hF]; sv
  have f52 : F 52 = gsq * gen ^ (4 * j) := by
    rw [hF]; sv
    rw [lp_pow4]
  have lv : ∀ t i, t < 4 → i < 2 ^ (t + 1) → F (nbLv 15 t i) = spLvV (nib zs j) (nib zs1 j) t i :=
    fun t i ht hi ↦ lpVal_lv j (gen ^ q) eqt z z1 gt gsq zs zs1 gs ht hi
  have gv : ∀ u, u < 16 → F (nbGV 53 u) = spGV 4 (nib gs j) u :=
    fun u hu ↦ lpVal_g j (gen ^ q) eqt z z1 gt gsq zs zs1 gs hu
  refine (tb_rel_iff_sem hf _ _).mpr ⟨fun x ↦ F x.idx, by rw [hp]; simp [hF, lpVal], ?_⟩
  rw [hb, lpBody, holdsList_append, holdsList_noRet _ lpPre_noRet]
  have n0 : ∀ l : List Stmt, (∀ s ∈ l, ∃ a, s = Stmt.atom a) → Stmt.noRetList l = true := by
    intro l hl
    induction l with
    | nil => rfl
    | cons s l ih =>
      obtain ⟨a, rfl⟩ := hl s (by simp)
      simp only [Stmt.noRetList, Stmt.noRet, Bool.true_and]
      exact ih fun s hs => hl s (by simp [hs])
  refine ⟨?_, ?_⟩
  · rw [lpPre, tb_holdsList_append_noRet (by
        simp only [tb_noRetList_append, nbEq_noRet, nbG_noRet]; rfl),
      tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nbEq_noRet]; rfl),
      tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nbEq_noRet]; rfl),
      tb_holdsList_append_noRet (n0 _ (by simp))]
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · -- the powers and pointers
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rw [hF]; sv) <;> ring
    · -- the eq levels
      have nL := tb_noRetList_flatten_range (4 - 1) _
        (fun t => nbLevel_noRet 15 (.n 13) (.n 14) (t + 1))
      have nn : Stmt.noRetList [Stmt.atom (.load (.n 15) (.n 14) 0),
        Stmt.atom (.load (.n (15 + 1)) (.n 13) 0)] = true := rfl
      rw [nbEq, tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nL, nn,
          Bool.and_self]),
        tb_holdsList_append_noRet nn, tb_holdsList_mapAtoms,
        tb_holdsList_flatten_range _ _ (fun t => nbLevel_noRet 15 (.n 13) (.n 14) (t + 1))]
      refine ⟨⟨?_, fun t ht ↦ ?_⟩, fun e he ↦ ?_⟩
      · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
        rw [f13, f14]
        have e15 : F 15 = (nib zs1 j).getD 0 0 := by
          simpa [nbZ1] using lpVal_z1 j (gen ^ q) eqt z z1 gt gsq zs zs1 gs (t := 0) (by norm_num)
        have e16 : F 16 = (nib zs j).getD 0 0 := by
          simpa [nbZ] using lpVal_z j (gen ^ q) eqt z z1 gt gsq zs zs1 gs (t := 0) (by norm_num)
        rw [e15, e16]
        exact ⟨lz1 0 (by norm_num), lz 0 (by norm_num)⟩
      · rw [nbLevel, tb_holdsList_append_noRet rfl, tb_holdsList_flatten_range _ _ (fun _ => rfl)]
        have hT : t + 1 < 4 := by omega
        have ez : F (nbM 15 (t + 1) - 2) = (nib zs j).getD (t + 1) 0 := by
          simpa [nbZ] using lpVal_z j (gen ^ q) eqt z z1 gt gsq zs zs1 gs hT
        have ez1 : F (nbM 15 (t + 1) - 1) = (nib zs1 j).getD (t + 1) 0 := by
          simpa [nbZ1] using lpVal_z1 j (gen ^ q) eqt z z1 gt gsq zs zs1 gs hT
        refine ⟨?_, fun i hi ↦ ?_⟩
        · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
          rw [f13, f14, ez, ez1]
          exact ⟨lz _ hT, lz1 _ hT⟩
        · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
          have hi' : i < 2 ^ (t + 1 + 1) := by rw [pow_succ 2 (t + 1)]; omega
          have a1 : nbM 15 (t + 1) + 2 * i = nbLv 15 (t + 1) i := by
            simp only [nbLv, Nat.succ_ne_zero, ↓reduceIte, hi]
          have a2 : nbM 15 (t + 1) + 2 * i + 1 = nbLv 15 (t + 1) (2 ^ (t + 1) + i) := by
            simp only [nbLv, Nat.succ_ne_zero, ↓reduceIte,
              show ¬ 2 ^ (t + 1) + i < 2 ^ (t + 1) by omega, Nat.add_sub_cancel_left]
          have h2 : 2 ^ (t + 1) + i < 2 ^ (t + 1 + 1) := by rw [pow_succ 2 (t + 1)]; omega
          rw [a2, a1, ez, ez1, Nat.add_sub_cancel, lv _ _ hT hi', lv _ _ hT h2,
            lv _ _ (by omega) (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) (by omega))),
            spLvV_hi _ _ (by omega) hi, Nat.add_sub_cancel]
          refine ⟨?_, rfl⟩
          rcases spLvV_lo (nib zs j) (nib zs1 j) (t := t + 1) hi with h | h
          · rw [h, Nat.add_sub_cancel]
          · omega
      · show LoadHolds rd (F 12) e (F (nbEqV 15 e))
        obtain ⟨t, i, ht, hi, hei, hst⟩ := lp_eqEntry (by simpa using he)
        rw [hst, lv t i ht hi, f12]
        have hv : (eqLevels (nib zs j) (nib zs1 j)).getD e 0 = spLvV (nib zs j) (nib zs1 j) t i := by
          rw [hei, eqLevels_getD (hzz.trans hzz1.symm) (by omega) (by omega) hi, spLvV]
        rw [← hv]
        exact tbReadsAt_getD htab.1 (by rw [eqLevels_length hzz hzz1]; simpa using he)
    · -- the `g` table's pointers
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      refine ⟨?_, ?_⟩ <;> (rw [hF]; sv)
      ring
    · -- the `g` table
      have nG := tb_noRetList_flatten_range (4 - 1) _ (fun t => nbGStep_noRet 53 (.n 52) (t + 1))
      have nn : Stmt.noRetList [Stmt.atom (.const (.n 53) (word 1 0 0)),
        Stmt.atom (.load (.n (53 + 1)) (.n 52) 0)] = true := rfl
      rw [nbG, tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nG, nn,
          Bool.and_self]),
        tb_holdsList_append_noRet nn, tb_holdsList_mapAtoms,
        tb_holdsList_flatten_range _ _ (fun t => nbGStep_noRet 53 (.n 52) (t + 1))]
      have g0 : F 53 = word 1 0 0 := by
        have := gv 0 (by norm_num)
        simp only [nbGV, ↓reduceIte] at this
        rw [this, tb_word_one, spGV]
        exact prod_eq_one fun s _ ↦ by simp [bitPick]
      have g1 : F 54 = (nib gs j).getD 0 0 := by
        have := gv 1 (by norm_num)
        simp only [nbGV, one_ne_zero, ↓reduceIte] at this
        rw [this]
        have := spGV_step 4 (nib gs j) (t := 0) (i := 0) (by omega) (by norm_num)
        simp only [pow_zero, add_zero] at this
        rw [this, show spGV 4 (nib gs j) 0 = 1 from prod_eq_one fun s _ ↦ by simp [bitPick],
          one_mul]
      refine ⟨⟨?_, fun t ht ↦ ?_⟩, fun u hu ↦ ?_⟩
      · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
        rw [g0, g1, f52]
        exact ⟨rfl, lg 0 (by norm_num)⟩
      · rw [nbGStep, show ∀ (a : Stmt) (l : List Stmt), a :: l = [a] ++ l from fun _ _ => rfl,
          tb_holdsList_append_noRet rfl, tb_holdsList_mapAtoms]
        have hT : t + 1 < 4 := by omega
        have eg : F (53 + 2 ^ (t + 1) + (t + 1) - 1) = (nib gs j).getD (t + 1) 0 :=
          lpVal_gl j (gen ^ q) eqt z z1 gt gsq zs zs1 gs (by omega) hT
        refine ⟨?_, fun i hi ↦ ?_⟩
        · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
          rw [f52, eg]
          exact lg _ hT
        · show F (53 + 2 ^ (t + 1) + (t + 1) + i) =
            F (nbGV 53 i) * F (53 + 2 ^ (t + 1) + (t + 1) - 1)
          have gs' : F (53 + 2 ^ (t + 1) + (t + 1) + i) = spGV 4 (nib gs j) (2 ^ (t + 1) + i) :=
            lpVal_gstep j (gen ^ q) eqt z z1 gt gsq zs zs1 gs (by omega) hT hi
          rw [eg, gs', gv i (by have : 2 ^ (t + 1) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega); omega),
            spGV_step 4 _ hT hi]
      · show LoadHolds rd (F 51) u (F (nbGV 53 u))
        have hu16 : u < 16 := by simpa using hu
        rw [gv u hu16, f51]
        have hv : (gTable (nib gs j)).getD u 0 = spGV 4 (nib gs j) u := by
          rw [gTable_getD hgl hu16, spGV]
        rw [← hv]
        exact tbReadsAt_getD htab.2 (by rw [gTable_length hgl]; exact hu16)
    · -- the next `x`
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [hF, lpVal]
  · -- the call
    simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil]
    have e74 : F 74 = gen ^ (j + 1) + gen ^ q := by
      simp [hF, lpVal, tb_word_gen, pow_succ]
    have e76 : F 76 = gen ^ (j + 1) := by simp [hF, lpVal, tb_word_gen, pow_succ]
    refine ⟨by rw [e74]; exact lp_isInK_add_pow _ _, fun hne ↦ ?_, trivial⟩
    have hjq : j + 1 < q := by
      rcases Nat.lt_or_ge (j + 1) q with h | h
      · exact h
      · exfalso; apply hne; rw [e74, show j + 1 = q by omega]; exact e_add_self _
    have := hnext hjq
    rw [e76]
    simpa [hF, lpVal] using this

/-- **The loop**: from `g^j`, `j < q`, the iterations run to `g^q`. -/
theorem lp_chain {rd : Reader} {eqt z z1 gt gsq : E} {q : ℕ} {zs zs1 gs : List E}
    (hlz : 4 * q ≤ zs.length) (hlz1 : 4 * q ≤ zs1.length) (hlg : 4 * q ≤ gs.length)
    (hz : TbReadsAt rd z zs) (hz1 : TbReadsAt rd z1 zs1) (hg : TbReadsAt rd gsq gs)
    (htab : ∀ j < q, TbReadsAt rd (eqt * gen ^ (32 * j)) (eqLevels (nib zs j) (nib zs1 j)) ∧
      TbReadsAt rd (gt * gen ^ (16 * j)) (gTable (nib gs j))) :
    ∀ j < q, coreProgram.Rel rd "__loop8" [gen ^ j, gen ^ q, eqt, z, z1, gt, gsq] [] := by
  intro j hj
  obtain ⟨m, hm⟩ : ∃ m, q = j + 1 + m := ⟨q - j - 1, by omega⟩
  induction m generalizing j with
  | zero =>
    exact lp_iter hj hlz hlz1 hlg hz hz1 hg (htab j hj) (fun h ↦ absurd h (by omega))
  | succ m ih =>
    exact lp_iter hj hlz hlz1 hlg hz hz1 hg (htab j hj) (fun _ ↦ ih (j + 1) (by omega) (by omega))

/-! ## The function -/

/-- Bit `k` of `n` as a word. -/
def ssB (n k : ℕ) : E := bitE (n.testBit k)

/-- The factor of bit `k` of `n` at share `t`. -/
def ssF (n k t : ℕ) : E := word 1 0 0 + ssB n k * word (imFactor t) 0 0

/-- **Value `x` of `shared_selector_tables`.** -/
def ssVal (eqt gt z z1 gsq : E) (n x : ℕ) : E :=
  let v20 := ssF n 0 0 * ssF n 1 1
  let v39 := ssF n 2 0 * ssF n 3 1 * ssF n 4 2 * ssF n 5 3
  let v41 := v39 * v39 * (v39 * v39)
  let v47 := v41 * v41 * (v41 * v41)
  [eqt, gt, z, z1, gsq, gen ^ n, ssB n 0, ssB n 1, ssB n 2, ssB n 3, ssB n 4, ssB n 5,
    word 1 0 0, word (imFactor 0) 0 0, ssB n 0 * word (imFactor 0) 0 0, ssF n 0 0,
    word 1 0 0, word (imFactor 1) 0 0, ssB n 1 * word (imFactor 1) 0 0, ssF n 1 1, v20,
    word 1 0 0, word (imFactor 0) 0 0, ssB n 2 * word (imFactor 0) 0 0, ssF n 2 0,
    word 1 0 0, word (imFactor 1) 0 0, ssB n 3 * word (imFactor 1) 0 0, ssF n 3 1,
    ssF n 2 0 * ssF n 3 1,
    word 1 0 0, word (imFactor 2) 0 0, ssB n 4 * word (imFactor 2) 0 0, ssF n 4 2,
    ssF n 2 0 * ssF n 3 1 * ssF n 4 2,
    word 1 0 0, word (imFactor 3) 0 0, ssB n 5 * word (imFactor 3) 0 0, ssF n 5 3, v39,
    v39 * v39, v41, v41 * v20, word 1 0 0, word 1 0 0 + v39, word 1 0 0, v41 * v41, v47,
    eqt * v47, eqt * v47 * v47, gt * v47, z * v41, z1 * v41, gsq * v41, 0].getD x 0

theorem ssF_eq (n k t : ℕ) (ht : t < 34) :
    ssF n k t = gen ^ (2 ^ t * (n.testBit k).toNat) := by
  rw [ssF, ssB, imFactor_eq ht, tb_word_one]
  cases n.testBit k
  · simp [bitE]
  · simp only [bitE, ↓reduceIte, one_mul, Bool.toNat_true, mul_one]
    rw [← add_assoc, e_add_self, zero_add]

theorem ss_bits {n : ℕ} (hn : n < 64) :
    n % 4 = (n.testBit 0).toNat + 2 * (n.testBit 1).toNat ∧
      n / 4 = (n.testBit 2).toNat + 2 * (n.testBit 3).toNat + 4 * (n.testBit 4).toNat +
        8 * (n.testBit 5).toNat := by
  have h := bitsVal_testBit (n := 6) hn
  simp only [bitsVal, Nat.reducePow, one_mul, zero_add] at h
  have b0 := Bool.toNat_le (n.testBit 0); have b1 := Bool.toNat_le (n.testBit 1)
  have b2 := Bool.toNat_le (n.testBit 2); have b3 := Bool.toNat_le (n.testBit 3)
  have b4 := Bool.toNat_le (n.testBit 4); have b5 := Bool.toNat_le (n.testBit 5)
  omega

theorem ssB_mul_self (n k : ℕ) : ssB n k = ssB n k * ssB n k := by rw [ssB, bitE_mul_self]

/-- **`shared_selector_tables` is complete.** -/
theorem shared_selector_tables_complete_holds : shared_selector_tables_complete_Spec := by
  intro rd eqt gt z z1 gsq n zs zs1 gs hn hzl hz1l hgl hz hz1 hg hrt
  obtain ⟨fn, hf, hp, hb⟩ := ssFound
  obtain ⟨hr, hq⟩ := ss_bits hn
  have v20 : ssF n 0 0 * ssF n 1 1 = gen ^ (n % 4) := by
    rw [ssF_eq n 0 0 (by norm_num), ssF_eq n 1 1 (by norm_num), ← pow_add, hr]; ring_nf
  have v39 : ssF n 2 0 * ssF n 3 1 * ssF n 4 2 * ssF n 5 3 = gen ^ (n / 4) := by
    rw [ssF_eq n 2 0 (by norm_num), ssF_eq n 3 1 (by norm_num), ssF_eq n 4 2 (by norm_num),
      ssF_eq n 5 3 (by norm_num), ← pow_add, ← pow_add, ← pow_add, hq]; ring_nf
  have hn4 : n = 4 * (n / 4) + n % 4 := by omega
  refine (tb_rel_pre hf hb ssPre_noRet _ _).mpr ⟨fun x ↦ ssVal eqt gt z z1 gsq n x.idx,
    by rw [hp]; rfl, ?_, rfl⟩
  simp only [ssPre, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, and_true, List.map_cons,
    List.map_nil]
  simp (config := { decide := true }) only [ssVal, List.getD_eq_getElem?_getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, true_and, v20, v39]
  set q := n / 4 with hqd
  have p4 : gen ^ q * gen ^ q * (gen ^ q * gen ^ q) = gen ^ (4 * q) := by
    simp only [← pow_add]; congr 1; omega
  have p16 : gen ^ (4 * q) * gen ^ (4 * q) * (gen ^ (4 * q) * gen ^ (4 * q)) = gen ^ (16 * q) := by
    simp only [← pow_add]; congr 1; omega
  rw [p4, p16]
  have hlz : 4 * q ≤ zs.length := by omega
  have hlz1 : 4 * q ≤ zs1.length := by omega
  have hlg : 4 * q ≤ gs.length := by omega
  refine ⟨ssB_mul_self n 0, ssB_mul_self n 1, ssB_mul_self n 2, ssB_mul_self n 3, ssB_mul_self n 4,
    ssB_mul_self n 5, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, fun hne ↦ ?_, ?_⟩
  · -- the assertion `q_g^4·r_g = len_g`
    rw [← pow_add, show 4 * q + n % 4 = n by omega]
    exact e_add_self _
  · rw [tb_word_one, ← pow_zero gen]; exact lp_isInK_add_pow 0 _
  · -- the loop over the full nibbles
    have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · exfalso; apply hne; rw [h0, tb_word_one, pow_zero]; exact e_add_self 1
      · exact h0
    rw [tb_word_one, ← pow_zero gen]
    exact lp_chain hlz hlz1 hlg hz hz1 hg (fun j hj ↦ hrt j (by omega)) 0 hq0
  · -- the partial nibble
    have hr4 : n % 4 < 4 := by omega
    refine ⟨n % 4, by simpa using hr4, gen_pow_eq_ofK _, ?_⟩
    rw [lName_sel_partial (n % 4) hr4, mul_assoc, ← pow_add, show 16 * q + 16 * q = 32 * q by omega]
    have hlen : ∀ l : List E, l.length = n → (nib l q).length = n % 4 := fun l hl ↦ by
      simp [nib, hl]; omega
    refine sel_partial_nibble_complete_holds (n % 4) hr4 rd _ _
      ⟨rfl, nib zs q, nib zs1 q, nib gs q, hlen zs hzl, hlen zs1 hz1l, hlen gs hgl,
        tbReadsAt_nib hz q, tbReadsAt_nib hz1 q, tbReadsAt_nib hg q, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos (n % 4) with h0 | h0
      · have e0 : nib zs q = [] := List.length_eq_zero_iff.mp ((hlen zs hzl).trans h0)
        have e1 : nib zs1 q = [] := List.length_eq_zero_iff.mp ((hlen zs1 hz1l).trans h0)
        rw [e0, e1]
        exact fun k hk ↦ absurd hk (by simp [eqLevels])
      · exact (hrt q (by omega)).1
    · rcases Nat.eq_zero_or_pos (n % 4) with h0 | h0
      · rw [h0]; exact tbReadsAt_nil _ _
      · rw [tb_ite_neg'' (show ¬ n % 4 = 0 by omega)]; exact (hrt q (by omega)).2

end
end LeanVM.Guest.B1.Tables
