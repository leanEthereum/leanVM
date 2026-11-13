/-
  LeanVM.Guest.B1.Selectors.SelPartial

  B1 for `sel_partial_nibble`: its four specializations write a nibble's eq levels and its
  `g`-power table.
-/

module

public import LeanVM.Guest.B1.Selectors.SelectorTables

/-!
# `sel_partial_nibble` (TRIAGE G #45-47)

`sel_partial_nibble(eq_out, g_out, z, z1, gs, w)` (G:2096-2100) runs, for `w > 0`, the inline
`sel_eq_nibble` (G:2064-2078: the eq levels over `z[0 .. w]`, level `t` from level `t - 1`, entry
`i` times `z1[t]`, then times `z[t]`, stored at `eq_out[0 ..]`) and `sel_g_nibble` (G:1924-1935:
`vals[2^t + i] = vals[i]·gs[t]`, stored at `g_out[0 ..]`), and returns `0`.

The body of `sel_partial_nibble__L{w}` is `spBody w` (`spFound`, by kernel evaluation): the eq
levels from value `5`, level `t`'s entry `i` at `spLv t i` (the layout of `selector_tables`'s
nibble), the `g` values from `spC w`, entry `u` at `spG w u`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- Level `t ≥ 1`'s first product, past its two loads. -/
def spM (t : ℕ) : ℕ := 5 + [0, 4, 10, 20].getD t 0

/-- The value of level `t`'s entry `i`. -/
def spLv (t i : ℕ) : ℕ :=
  if t = 0 then 5 + i
  else if i < 2 ^ t then spM t + 2 * i else spM t + 2 * (i - 2 ^ t) + 1

/-- Level `t ≥ 1`: the coordinate and its complement, then the products. -/
def spLevel (t : ℕ) : List Stmt :=
  [.atom (.load (.n (spM t - 2)) (.n 2) t), .atom (.load (.n (spM t - 1)) (.n 3) t)] ++
  ((List.range (2 ^ t)).map fun i ↦
    [.atom (.mul (.n (spM t + 2 * i)) (.n (spLv (t - 1) i)) (.n (spM t - 1))),
      .atom (.mul (.n (spM t + 2 * i + 1)) (.n (spLv (t - 1) i)) (.n (spM t - 2)))]).flatten

/-- The value of the eq levels' entry `e`, level by level. -/
def spEq (e : ℕ) : ℕ :=
  if e < 2 then spLv 0 e else if e < 6 then spLv 1 (e - 2) else if e < 14 then spLv 2 (e - 6)
  else spLv 3 (e - 14)

/-- The first `g` value at width `w`. -/
def spC (w : ℕ) : ℕ := 5 + [0, 2, 8, 18, 36].getD w 0

/-- The `g` value of entry `u` at width `w`. -/
def spG (w u : ℕ) : ℕ :=
  if u = 0 then spC w else if u = 1 then spC w + 1 else spC w + u + Nat.log2 u

/-- The `g` table's step `t ≥ 1`: the share, then the products. -/
def spGStep (w t : ℕ) : List Stmt :=
  .atom (.load (.n (spC w + 2 ^ t + t - 1)) (.n 4) t) ::
    (List.range (2 ^ t)).map fun i ↦
      .atom (.mul (.n (spC w + 2 ^ t + t + i)) (.n (spG w i)) (.n (spC w + 2 ^ t + t - 1)))

/-- `sel_partial_nibble__L{w}`'s statements before its `ret`, `w ≥ 1`. -/
def spPre (w : ℕ) : List Stmt :=
  [.atom (.load (.n 5) (.n 3) 0), .atom (.load (.n 6) (.n 2) 0)] ++
    ((List.range (w - 1)).map fun t ↦ spLevel (t + 1)).flatten ++
    (List.range (2 ^ (w + 1) - 2)).map (fun e ↦ .atom (.load (.n (spEq e)) (.n 0) e)) ++
    [.atom (.const (.n (spC w)) (word 1 0)), .atom (.load (.n (spC w + 1)) (.n 4) 0)] ++
    ((List.range (w - 1)).map fun t ↦ spGStep w (t + 1)).flatten ++
    (List.range (2 ^ w)).map (fun u ↦ .atom (.load (.n (spG w u)) (.n 1) u)) ++
    [.atom (.const (.n (spC w + 2 ^ w + w - 1)) (word 0 0))]

/-- The body of `sel_partial_nibble__L{w}`. -/
def spBody (w : ℕ) : List Stmt :=
  if w = 0 then [.atom (.const (.n 5) (word 0 0)), .ret [.n 5]]
  else spPre w ++ [.ret [.n (spC w + 2 ^ w + w - 1)]]

/-- The function found by name is the template. -/
noncomputable def spCheck (w : ℕ) : Bool :=
  match coreProgram.find? (lName "sel_partial_nibble" w) with
  | some fn => decide (fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4]) && tbStmtsEqb fn.body (spBody w)
  | none => false

theorem spCheck_all : (List.range 4).all spCheck = true := by decide +kernel

theorem spFound {w : ℕ} (hw : w < 4) : ∃ fn : Fn,
    coreProgram.find? (lName "sel_partial_nibble" w) = some fn ∧
      fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4] ∧ fn.body = spBody w := by
  have h := List.all_eq_true.mp spCheck_all w (List.mem_range.mpr hw)
  unfold spCheck at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

theorem spLevel_noRet (t : ℕ) : Stmt.noRetList (spLevel t) = true := by
  rw [spLevel, tb_noRetList_append, tb_noRetList_flatten_range _ _ (fun _ => rfl)]; rfl

theorem spGStep_noRet (w t : ℕ) : Stmt.noRetList (spGStep w t) = true := by
  rw [spGStep, Stmt.noRetList, tb_noRetList_mapAtoms]; rfl

theorem spPre_noRet (w : ℕ) : Stmt.noRetList (spPre w) = true := by
  simp only [spPre, tb_noRetList_append, tb_noRetList_flatten_range _ _ (fun _ => spLevel_noRet _),
    tb_noRetList_flatten_range _ _ (fun _ => spGStep_noRet _ _), tb_noRetList_mapAtoms]
  rfl

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- The parts of `sel_partial_nibble__L{w}`. -/
theorem holds_spPre {w : ℕ} (h : Stmt.HoldsList C rd σ (spPre w) True kret) :
    (LoadHolds rd (σ (.n 3)) 0 (σ (.n 5)) ∧ LoadHolds rd (σ (.n 2)) 0 (σ (.n 6))) ∧
    (∀ t < w - 1, Stmt.HoldsList C rd σ (spLevel (t + 1)) True kret) ∧
    (∀ e < 2 ^ (w + 1) - 2, LoadHolds rd (σ (.n 0)) e (σ (.n (spEq e)))) ∧
    (σ (.n (spC w)) = word 1 0 ∧ LoadHolds rd (σ (.n 4)) 0 (σ (.n (spC w + 1)))) ∧
    (∀ t < w - 1, Stmt.HoldsList C rd σ (spGStep w (t + 1)) True kret) ∧
    (∀ u < 2 ^ w, LoadHolds rd (σ (.n 1)) u (σ (.n (spG w u)))) ∧
    σ (.n (spC w + 2 ^ w + w - 1)) = word 0 0 := by
  have nL := tb_noRetList_flatten_range (w - 1) _ (fun t => spLevel_noRet (t + 1))
  have nG := tb_noRetList_flatten_range (w - 1) _ (fun t => spGStep_noRet w (t + 1))
  have nA := tb_noRetList_mapAtoms (2 ^ (w + 1) - 2) (fun e ↦ .load (.n (spEq e)) (.n 0) e)
  have nB := tb_noRetList_mapAtoms (2 ^ w) (fun u ↦ .load (.n (spG w u)) (.n 1) u)
  have n0 : Stmt.noRetList [Stmt.atom (.load (.n 5) (.n 3) 0), Stmt.atom (.load (.n 6) (.n 2) 0)] =
    true := rfl
  have n1 : Stmt.noRetList [Stmt.atom (.const (.n (spC w)) (word 1 0)),
    Stmt.atom (.load (.n (spC w + 1)) (.n 4) 0)] = true := rfl
  rw [spPre] at h
  rw [tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nL, nG, nA, nB, n0, n1,
      Bool.and_self]),
    tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nL, nG, nA, n0, n1,
      Bool.and_self]),
    tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nL, nA, n0, n1, Bool.and_self]),
    tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nL, nA, n0, Bool.and_self]),
    tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nL, n0, Bool.and_self]),
    tb_holdsList_append_noRet n0, tb_holdsList_mapAtoms, tb_holdsList_mapAtoms,
    tb_holdsList_flatten_range _ _ (fun t => spLevel_noRet (t + 1)),
    tb_holdsList_flatten_range _ _ (fun t => spGStep_noRet w (t + 1))] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h0 h3 h6
  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

theorem holds_spLevel {t : ℕ} (h : Stmt.HoldsList C rd σ (spLevel t) True kret) :
    LoadHolds rd (σ (.n 2)) t (σ (.n (spM t - 2))) ∧
    LoadHolds rd (σ (.n 3)) t (σ (.n (spM t - 1))) ∧
    ∀ i < 2 ^ t, σ (.n (spM t + 2 * i)) = σ (.n (spLv (t - 1) i)) * σ (.n (spM t - 1)) ∧
      σ (.n (spM t + 2 * i + 1)) = σ (.n (spLv (t - 1) i)) * σ (.n (spM t - 2)) := by
  rw [spLevel, tb_holdsList_append_noRet rfl, tb_holdsList_flatten_range _ _ (fun _ => rfl)] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h1
  refine ⟨h1.1, h1.2, fun i hi => ?_⟩
  have := h2 i hi
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
  exact this

theorem holds_spGStep {w t : ℕ} (h : Stmt.HoldsList C rd σ (spGStep w t) True kret) :
    LoadHolds rd (σ (.n 4)) t (σ (.n (spC w + 2 ^ t + t - 1))) ∧
    ∀ i < 2 ^ t, σ (.n (spC w + 2 ^ t + t + i)) =
      σ (.n (spG w i)) * σ (.n (spC w + 2 ^ t + t - 1)) := by
  rw [spGStep, show ∀ (a : Stmt) (l : List Stmt), a :: l = [a] ++ l from fun _ _ => rfl,
    tb_holdsList_append_noRet rfl, tb_holdsList_mapAtoms] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h1
  exact ⟨h1, h2⟩

end Sem

/-- The value loaded as coordinate `t`, and its complement. -/
def spZ (t : ℕ) : ℕ := if t = 0 then 6 else spM t - 2
def spZ1 (t : ℕ) : ℕ := if t = 0 then 5 else spM t - 1

/-- The value loaded as share `t`. -/
def spGL (w t : ℕ) : ℕ := if t = 0 then spC w + 1 else spC w + 2 ^ t + t - 1

section Sem2

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

theorem spLevels {w : ℕ} (h : Stmt.HoldsList C rd σ (spPre w) True kret) :
    ∀ t < w, ∀ i < 2 ^ (t + 1), σ (.n (spLv t i)) = ∏ s ∈ Finset.range (t + 1),
      bitPick i s (σ (.n (spZ s))) (σ (.n (spZ1 s))) := by
  obtain ⟨⟨l0, l1⟩, hL, -, -, -, -, -⟩ := holds_spPre h
  intro t ht
  induction t with
  | zero =>
    intro i hi
    rw [Finset.prod_range_one]
    interval_cases i
    · simp [spLv, bitPick, spZ1]
    · simp [spLv, bitPick, spZ]
  | succ t ih =>
    intro i hi
    obtain ⟨-, -, hm⟩ := holds_spLevel (hL t (by omega))
    rw [Finset.prod_range_succ]
    by_cases hlo : i < 2 ^ (t + 1)
    · obtain ⟨h1, -⟩ := hm i hlo
      have hv : spLv (t + 1) i = spM (t + 1) + 2 * i := by
        simp only [spLv, Nat.succ_ne_zero, ↓reduceIte, hlo]
      rw [hv, h1, Nat.add_sub_cancel, ih (by omega) i hlo, bitPick, testBit_lt_two_pow hlo]
      simp [spZ1]
    · obtain ⟨v, rfl⟩ : ∃ v, i = 2 ^ (t + 1) + v := ⟨i - 2 ^ (t + 1), by omega⟩
      have hv' : v < 2 ^ (t + 1) := by rw [pow_succ 2 (t + 1)] at hi; omega
      obtain ⟨-, h2⟩ := hm v hv'
      have hv : spLv (t + 1) (2 ^ (t + 1) + v) = spM (t + 1) + 2 * v + 1 := by
        simp only [spLv, Nat.succ_ne_zero, ↓reduceIte, hlo, Nat.add_sub_cancel_left]
      rw [hv, h2, Nat.add_sub_cancel, ih (by omega) v hv', bitPick,
        testBit_two_pow_add_self hv']
      simp only [↓reduceIte, spZ, Nat.succ_ne_zero]
      exact congrArg (· * _) (Finset.prod_congr rfl fun s hs => by
        simp only [bitPick, testBit_two_pow_add hv' (Finset.mem_range.mp hs)])

theorem log2_two_pow_add {t v : ℕ} (hv : v < 2 ^ t) : Nat.log2 (2 ^ t + v) = t :=
  (Nat.log2_eq_iff (by positivity)).mpr ⟨by omega, by rw [pow_succ]; omega⟩

theorem spGs {w : ℕ} (h : Stmt.HoldsList C rd σ (spPre w) True kret) :
    ∀ t < w, ∀ u < 2 ^ (t + 1), σ (.n (spG w u)) = ∏ s ∈ Finset.range (t + 1),
      bitPick u s (σ (.n (spGL w s))) 1 := by
  obtain ⟨-, -, -, ⟨g0, g1⟩, hG, -, -⟩ := holds_spPre h
  intro t ht
  induction t with
  | zero =>
    intro u hu
    rw [Finset.prod_range_one]
    interval_cases u
    · simp [spG, bitPick, g0, tb_word_one]
    · simp [spG, bitPick, spGL]
  | succ t ih =>
    intro u hu
    obtain ⟨-, hm⟩ := holds_spGStep (hG t (by omega))
    rw [Finset.prod_range_succ]
    by_cases hlo : u < 2 ^ (t + 1)
    · rw [ih (by omega) u hlo, bitPick, testBit_lt_two_pow hlo]
      simp
    · obtain ⟨v, rfl⟩ : ∃ v, u = 2 ^ (t + 1) + v := ⟨u - 2 ^ (t + 1), by omega⟩
      have hv' : v < 2 ^ (t + 1) := by rw [pow_succ 2 (t + 1)] at hu; omega
      have hp1 : 2 ≤ 2 ^ (t + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (t + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hv : spG w (2 ^ (t + 1) + v) = spC w + 2 ^ (t + 1) + (t + 1) + v := by
        simp only [spG, show 2 ^ (t + 1) + v ≠ 0 by omega, show 2 ^ (t + 1) + v ≠ 1 by omega,
          ↓reduceIte, log2_two_pow_add hv']
        omega
      rw [hv, hm v hv', ih (by omega) v hv', bitPick, testBit_two_pow_add_self hv']
      simp only [↓reduceIte, spGL, Nat.succ_ne_zero]
      exact congrArg (· * _) (Finset.prod_congr rfl fun s hs => by
        simp only [bitPick, testBit_two_pow_add hv' (Finset.mem_range.mp hs)])

end Sem2

/-- **`sel_partial_nibble` is sound** at its four specializations. -/
theorem sel_partial_nibble_holds : sel_partial_nibble_Spec := by
  intro w hw rd args rets h
  obtain ⟨fn, hf, hp, hb⟩ := spFound hw
  obtain ⟨σ, hpar, hbody⟩ := (tb_rel_iff_sem hf args rets).mp h
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil] at hpar
  subst hpar
  by_cases hw0 : w = 0
  · subst hw0
    simp only [hb, spBody, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
      List.map_nil] at hbody
    obtain ⟨h5, rfl⟩ := hbody
    refine ⟨by rw [h5, tb_word_zero], [], [], [], rfl, rfl, rfl, tbReadsAt_nil _ _,
      tbReadsAt_nil _ _, tbReadsAt_nil _ _, ?_, ?_⟩
    · simpa [eqLevels] using tbReadsAt_nil rd (σ (.n 0))
    · simpa using tbReadsAt_nil rd (σ (.n 1))
  · simp only [hb, spBody, hw0, ↓reduceIte] at hbody
    rw [holdsList_append, holdsList_noRet _ (spPre_noRet w)] at hbody
    obtain ⟨hpre, hret⟩ := hbody
    simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hret
    subst hret
    obtain ⟨⟨l0, l1⟩, hL, hEq, ⟨-, g1⟩, hG, hGs, hr⟩ := holds_spPre hpre
    have hlev := spLevels hpre
    have hgs := spGs hpre
    let zs := (List.range w).map fun t ↦ σ (.n (spZ t))
    let zs1 := (List.range w).map fun t ↦ σ (.n (spZ1 t))
    let gl := (List.range w).map fun t ↦ σ (.n (spGL w t))
    have ezs : ∀ t < w, zs.getD t 0 = σ (.n (spZ t)) := fun t ht => by
      simp [zs, List.getD_eq_getElem?_getD, ht]
    have ezs1 : ∀ t < w, zs1.getD t 0 = σ (.n (spZ1 t)) := fun t ht => by
      simp [zs1, List.getD_eq_getElem?_getD, ht]
    have egl : ∀ t < w, gl.getD t 0 = σ (.n (spGL w t)) := fun t ht => by
      simp [gl, List.getD_eq_getElem?_getD, ht]
    have hlz : zs.length = w := by simp [zs]
    have hlz1 : zs1.length = w := by simp [zs1]
    have hlg : gl.length = w := by simp [gl]
    refine ⟨by rw [hr, tb_word_zero], zs, zs1, gl, hlz, hlz1, hlg, fun t ht => ?_,
      fun t ht => ?_, fun t ht => ?_, fun e he => ?_, ?_⟩
    · rw [hlz] at ht
      rw [← List.getD_eq_getElem _ 0 (by rw [hlz]; exact ht), ezs t ht]
      rcases Nat.eq_zero_or_pos t with rfl | ht0
      · exact l1
      · have := (holds_spLevel (hL (t - 1) (by omega))).1
        rw [show t - 1 + 1 = t by omega] at this
        simpa [spZ, show t ≠ 0 by omega] using this
    · rw [hlz1] at ht
      rw [← List.getD_eq_getElem _ 0 (by rw [hlz1]; exact ht), ezs1 t ht]
      rcases Nat.eq_zero_or_pos t with rfl | ht0
      · exact l0
      · have := (holds_spLevel (hL (t - 1) (by omega))).2.1
        rw [show t - 1 + 1 = t by omega] at this
        simpa [spZ1, show t ≠ 0 by omega] using this
    · rw [hlg] at ht
      rw [← List.getD_eq_getElem _ 0 (by rw [hlg]; exact ht), egl t ht]
      rcases Nat.eq_zero_or_pos t with rfl | ht0
      · simpa [spGL] using g1
      · have := (holds_spGStep (hG (t - 1) (by omega))).1
        rw [show t - 1 + 1 = t by omega] at this
        simpa [spGL, show t ≠ 0 by omega] using this
    · have hlen := eqLevels_length hlz hlz1
      rw [hlen] at he
      have hval : σ (.n (spEq e)) = (eqLevels zs zs1).getD e 0 := by
        obtain ⟨t, i, ht, hi, hei, hst⟩ : ∃ t i, t < w ∧ i < 2 ^ (t + 1) ∧
            e = 2 ^ (t + 1) - 2 + i ∧ spEq e = spLv t i := by
          have hw4 : w ≤ 3 := by omega
          by_cases e2 : e < 2
          · exact ⟨0, e, by omega, by simpa using e2, by simp, by simp [spEq, e2]⟩
          have hw1 : 1 ≤ w := by omega
          by_cases e6 : e < 6
          · have hw2 : 2 ≤ w := by
              by_contra hc
              have : w = 1 := by omega
              subst this; simp at he; omega
            exact ⟨1, e - 2, by omega, by simp; omega, by simp; omega, by simp [spEq, e2, e6]⟩
          · have hw3 : w = 3 := by
              interval_cases w <;> simp at he <;> omega
            subst hw3
            have e14 : e < 14 := by simp at he; omega
            exact ⟨2, e - 6, by omega, by simp; omega, by simp; omega,
              by simp [spEq, e2, e6, e14]⟩
        rw [hst, hlev t ht i hi, hei, eqLevels_getD (hlz.trans hlz1.symm) (by omega)
          (by omega) hi]
        refine Finset.prod_congr rfl fun s hs => ?_
        have hs' := Finset.mem_range.mp hs
        rw [ezs s (by omega), ezs1 s (by omega)]
      rw [← List.getD_eq_getElem _ 0 (by rw [hlen]; exact he), ← hval]
      exact hEq e he
    · simp only [hw0, ↓reduceIte]
      intro u hu
      rw [gTable_length hlg] at hu
      rw [← List.getD_eq_getElem _ 0 (by rw [gTable_length hlg]; exact hu),
        gTable_getD hlg hu]
      have := hgs (w - 1) (by omega) u (by rw [show w - 1 + 1 = w by omega]; exact hu)
      rw [show w - 1 + 1 = w by omega] at this
      rw [Finset.prod_congr rfl fun s hs => by rw [egl s (Finset.mem_range.mp hs)], ← this]
      exact hGs u hu

end
end LeanVM.Guest.B1.Tables
