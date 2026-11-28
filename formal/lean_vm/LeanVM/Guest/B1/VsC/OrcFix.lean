/-
  LeanVM.Guest.B1.VsC.OrcFix

  `verify_sub`'s forward valuation reads the oracle causally, so an oracle can be defined from the
  valuation's earlier values.
-/

module

public import LeanVM.Guest.B1.VsC.VsEval

/-!
# The oracle as a causal fixpoint

The forward evaluator `ev` defines value `.n j` from older values and the oracle's word `w j` alone
(`newS_orc`: a statement's new words read `w` only at their own indices), so `ev`'s first `N` words read `w`
only below `N` (`ev_take`), and so does `verify_sub`'s valuation through its branches (`vsEv_take`):
`vsVal_causal`, value `.n j` reads the oracle only at indices `≤ j`.

An oracle word that is a function of the valuation's older values (a callee's returns of its arguments, a
heap buffer's base of the earlier allocations) is then a fixpoint without circularity: `fixW Φ F` for a
causal evaluator `Φ` and a causal rule `F` (`F i` reads its valuation below `i` only) satisfies
`fixW Φ F i = F i (Φ (fixW Φ F))` (`fixW_eq`), built index by index (`fixList`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## Lists agreeing on a prefix -/

theorem take_of_ext {N : ℕ} {L L' B B' : List E} (hB : ∃ m, L = B ++ m) (hB' : ∃ m, L' = B' ++ m)
    (hN : N ≤ B.length) (hl : B.length = B'.length) (ht : B.take N = B'.take N) : L.take N = L'.take N := by
  obtain ⟨m, rfl⟩ := hB
  obtain ⟨m', rfl⟩ := hB'
  rw [List.take_append_of_le_length hN, List.take_append_of_le_length (hl ▸ hN), ht]

theorem eq_of_take {N : ℕ} {L L' : List E} (hl : L.length = L'.length) (hN : L.length ≤ N)
    (ht : L.take N = L'.take N) : L = L' := by
  rw [← List.take_of_length_le hN, ht, List.take_of_length_le (hl ▸ hN)]

theorem padZ_take {N n : ℕ} {l l' : List E} (hl : l.length = l'.length) (ht : l.take N = l'.take N) :
    (padZ l n).take N = (padZ l' n).take N := by
  unfold padZ
  rw [List.take_append, List.take_append, ht, hl]

theorem getD_of_take {N j : ℕ} {L L' : List E} (ht : L.take N = L'.take N) (hj : j < N) :
    L.getD j 0 = L'.getD j 0 := by
  have h1 : L.getD j 0 = (L.take N).getD j 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hj, ite_true]
  have h2 : L'.getD j 0 = (L'.take N).getD j 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hj, ite_true]
  rw [h1, h2, ht]

/-! ## The evaluator reads the oracle causally -/

section
variable (rd : Reader) (w w' : ℕ → E)

/-- A statement's new words either do not read the oracle or are its words from their first index. -/
theorem newS_orc (l : List E) (s : Stmt) :
    newS rd w l s = newS rd w' l s ∨
      ∃ n, newS rd w l s = orc w l.length n ∧ newS rd w' l s = orc w' l.length n := by
  cases s with
  | atom a =>
    cases a with
    | frameAddr p run => exact .inr ⟨1, rfl, rfl⟩
    | hint h =>
      cases h with
      | witness _ d => cases d <;> first | exact .inl rfl | exact .inr ⟨_, rfl, rfl⟩
      | bits _ _ _ d => cases d <;> first | exact .inl rfl | exact .inr ⟨_, rfl, rfl⟩
      | bitsExp _ _ d => cases d <;> first | exact .inl rfl | exact .inr ⟨_, rfl, rfl⟩
      | digitsExp _ _ _ _ _ _ d => cases d <;> first | exact .inl rfl | exact .inr ⟨_, rfl, rfl⟩
      | windowsExp _ _ _ _ d => cases d <;> first | exact .inl rfl | exact .inr ⟨_, rfl, rfl⟩
      | _ => first | exact .inl rfl | exact .inr ⟨1, rfl, rfl⟩
    | _ => exact .inl rfl
  | call _ _ rets => exact .inr ⟨rets.length, rfl, rfl⟩
  | dispatch _ _ _ rets => exact .inr ⟨rets.length, rfl, rfl⟩
  | _ => exact .inl rfl

theorem ev_ext : ∀ (ss : List Stmt) (l : List E), ∃ m, ev rd w l ss = l ++ m
  | [], l => ⟨[], by simp [ev]⟩
  | s :: ss, l => by
    obtain ⟨m, hm⟩ := ev_ext ss (l ++ newS rd w l s)
    exact ⟨newS rd w l s ++ m, by rw [ev, hm, List.append_assoc]⟩

variable {rd w w'}

theorem orc_take {l : List E} {n N : ℕ} (h : ∀ i < N, w i = w' i) :
    (l ++ orc w l.length n).take N = (l ++ orc w' l.length n).take N := by
  rw [List.take_append, List.take_append]
  congr 1
  apply List.ext_getElem
  · simp [orc]
  · intro j h1 _
    simp only [orc, List.getElem_take, List.getElem_map, List.getElem_range]
    simp only [orc, List.length_take, List.length_map, List.length_range] at h1
    exact h _ (by omega)

/-- **`ev`'s first `N` words read the oracle below `N` only.** -/
theorem ev_take {N : ℕ} (h : ∀ i < N, w i = w' i) : ∀ (ss : List Stmt) (l l' : List E),
    l.length = l'.length → l.take N = l'.take N → (ev rd w l ss).take N = (ev rd w' l' ss).take N
  | [], l, l', _, ht => by simpa [ev] using ht
  | s :: ss, l, l', hl, ht => by
    by_cases hN : N ≤ l.length
    · exact take_of_ext (ev_ext rd w (s :: ss) l) (ev_ext rd w' (s :: ss) l') hN hl ht
    · have e : l = l' := eq_of_take hl (by omega) ht
      subst e
      simp only [ev]
      rcases newS_orc rd w w' l s with e | ⟨n, e, e'⟩
      · rw [e]; exact ev_take h ss _ _ rfl rfl
      · rw [e, e']
        exact ev_take h ss _ _ (by simp [orc]) (orc_take h)

end

/-! ## `verify_sub`'s valuation reads the oracle causally -/

section
variable {rd : Reader} {w w' : ℕ → E} {args : List E}

theorem ev_length {l : List E} {ss : List Stmt} {c' : ℕ} (h : chk l.length ss = some c') (v : ℕ → E) :
    (ev rd v l ss).length = c' :=
  (ev_spec rd v ss l h).1

/-- **`verify_sub`'s first `N` words read the oracle below `N` only.** -/
theorem vsEv_take (ha : args.length = 6) {N : ℕ} (h : ∀ i < N, w i = w' i) :
    (vsEv rd w args).take N = (vsEv rd w' args).take N := by
  have l1 := (vsL1_spec (rd := rd) (w := w) ha).1
  have l1' := (vsL1_spec (rd := rd) (w := w') ha).1
  have l2 := (vsL2_spec (rd := rd) (w := w) ha).1
  have l2' := (vsL2_spec (rd := rd) (w := w') ha).1
  have l3 := (vsL3_spec (rd := rd) (w := w) ha).1
  have l3' := (vsL3_spec (rd := rd) (w := w') ha).1
  have l4 := (vsL4_spec (rd := rd) (w := w) ha).1
  have l4' := (vsL4_spec (rd := rd) (w := w') ha).1
  have t1 : (vsL1 rd w args).take N = (vsL1 rd w' args).take N := ev_take h _ _ _ rfl rfl
  have t2 : (vsL2 rd w args).take N = (vsL2 rd w' args).take N := by
    by_cases hN : N ≤ 235
    · exact take_of_ext (vsL2_spec ha).2 (vsL2_spec ha).2 (by omega) (l1.trans l1'.symm) t1
    · have e := eq_of_take (l1.trans l1'.symm) (by omega) t1
      unfold vsL2
      rw [e]
      split_ifs
      · rfl
      · exact ev_take h _ _ _ rfl rfl
  have t3 : (vsL3 rd w args).take N = (vsL3 rd w' args).take N :=
    ev_take h _ _ _ (l2.trans l2'.symm) t2
  have t4 : (vsL4 rd w args).take N = (vsL4 rd w' args).take N := by
    by_cases hN : N ≤ 472
    · exact take_of_ext (vsL4_spec ha).2 (vsL4_spec ha).2 (by omega) (l3.trans l3'.symm) t3
    · have e := eq_of_take (l3.trans l3'.symm) (by omega) t3
      unfold vsL4
      rw [e]
      split_ifs
      · have c : chk (vsL3 rd w' args).length vsI2z = some 477 := by rw [l3']; exact chk_vsI2z
        exact padZ_take ((ev_length c w).trans (ev_length c w').symm) (ev_take h _ _ _ rfl rfl)
      · exact ev_take h _ _ _ rfl rfl
  exact ev_take h _ _ _ (l4.trans l4'.symm) t4

/-- **`verify_sub`'s value `.n j` reads the oracle at indices `≤ j` only.** -/
theorem vsVal_causal (ha : args.length = 6) {j : ℕ} (h : ∀ i ≤ j, w i = w' i) :
    vsVal rd w args (.n j) = vsVal rd w' args (.n j) := by
  unfold vsVal B1.Val.ofArgs
  exact getD_of_take (N := j + 1) (j := (V.n j).idx) (vsEv_take ha fun i hi => h i (by omega))
    (by show j < j + 1; omega)

end

/-! ## Causal fixpoints -/

/-- An evaluator whose value `j` reads its oracle at indices `≤ j` only. -/
def CausalEv (Φ : (ℕ → E) → ℕ → E) : Prop := ∀ w w' j, (∀ i ≤ j, w i = w' i) → Φ w j = Φ w' j

/-- A rule whose word `i` reads its valuation below `i` only. -/
def CausalRule (F : ℕ → (ℕ → E) → E) : Prop := ∀ i σ σ', (∀ j < i, σ j = σ' j) → F i σ = F i σ'

/-- The fixpoint's first words, index by index. -/
def fixList (Φ : (ℕ → E) → ℕ → E) (F : ℕ → (ℕ → E) → E) : ℕ → List E
  | 0 => []
  | i + 1 => fixList Φ F i ++ [F i (Φ fun m => (fixList Φ F i).getD m 0)]

/-- **The causal fixpoint**: word `i` is `F i` of the evaluator on the words below `i`. -/
def fixW (Φ : (ℕ → E) → ℕ → E) (F : ℕ → (ℕ → E) → E) (i : ℕ) : E := (fixList Φ F (i + 1)).getD i 0

section
variable {Φ : (ℕ → E) → ℕ → E} {F : ℕ → (ℕ → E) → E}

theorem fixList_length : ∀ i, (fixList Φ F i).length = i
  | 0 => rfl
  | i + 1 => by rw [fixList, List.length_append, fixList_length i]; rfl

theorem fixList_getD : ∀ (d i m : ℕ), m < i → (fixList Φ F (i + d)).getD m 0 = (fixList Φ F i).getD m 0
  | 0, _, _, _ => rfl
  | d + 1, i, m, hm => by
    rw [← Nat.add_assoc, fixList, List.getD_append _ _ _ _ (by rw [fixList_length]; omega)]
    exact fixList_getD d i m hm

theorem fixList_fixW {i m : ℕ} (hm : m < i) : (fixList Φ F i).getD m 0 = fixW Φ F m := by
  obtain ⟨d, rfl⟩ : ∃ d, i = m + 1 + d := ⟨i - (m + 1), by omega⟩
  exact fixList_getD d (m + 1) m (by omega)

/-- **The causal fixpoint's equation.** -/
theorem fixW_eq (hΦ : CausalEv Φ) (hF : CausalRule F) (i : ℕ) : fixW Φ F i = F i (Φ (fixW Φ F)) := by
  have e : fixW Φ F i = F i (Φ fun m => (fixList Φ F i).getD m 0) := by
    unfold fixW
    rw [fixList, List.getD_append_right _ _ _ _ (by rw [fixList_length])]
    simp [fixList_length]
  rw [e]
  exact hF i _ _ fun j hj => hΦ _ _ j fun m hm => fixList_fixW (by omega)

end

/-- `verify_sub`'s valuation as a causal evaluator. -/
noncomputable def vsΦ (rd : Reader) (args : List E) : (ℕ → E) → ℕ → E := fun w j => vsVal rd w args (.n j)

theorem vsΦ_causal {rd : Reader} {args : List E} (ha : args.length = 6) : CausalEv (vsΦ rd args) :=
  fun _ _ _ h => vsVal_causal ha h

/-- **An oracle defined from `verify_sub`'s earlier values**: at `fixW (vsΦ rd args) F`, word `i` is `F i` of
the valuation. -/
theorem vsFix_eq {rd : Reader} {args : List E} {F : ℕ → (ℕ → E) → E} (ha : args.length = 6)
    (hF : CausalRule F) (i : ℕ) :
    fixW (vsΦ rd args) F i = F i fun j => vsVal rd (fixW (vsΦ rd args) F) args (.n j) :=
  fixW_eq (vsΦ_causal ha) hF i

end
end LeanVM.Guest.B1.VsC
