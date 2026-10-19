/-
  LeanVM.Guest.B1.Tables.VerifyTablesFinal

  The table sumcheck's final value at the guest's values: each table's term is its
  `constraint_eval`.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesClaims

/-!
# The final value

`CeExEval` is the statement of `ceEx`'s value (piece (2) of `VT-SPEC-PIECES.md`), taken as a
hypothesis until it lands. With it, each table's term in `ttVal` (its constraints and its forms on
the three sides, at its evaluations) is the guest's `constraint_eval` (`vt_term`), so the final
value is the guest's sum (`vt_final`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Complete

@[expose] public section

/-- Piece (2): `ceEx`'s value. -/
def CeExEval : Prop :=
  ∀ (t : Fin 6) (ρ χ : ℕ → E) (xi : E), (∀ k < 5, ρ (vtXiVars.getD k 0) = xi ^ k) →
    let ev : ℕ → E := fun c => ρ ((vtEvalVars.getD t []).getD c 0)
    let side : ℕ → List (List Form) → E := fun s blocks =>
      sumE ((List.zip ((vtEqhiVars.getD t []).getD s []) blocks).map fun p =>
        ρ p.1 * (blockForm ⟨0, 0, p.2, t⟩ ((List.range 16).map χ) (ρ 12)).evaluate ev)
    (ceEx t).eval ρ χ =
      (if (t : ℕ) = 4 then dot [1, xi] (jumpConstraints ((List.range 14).map ev)) else 0) +
      dot [xi ^ 2, xi ^ 3, xi ^ 4]
        [side 0 ((tables.getD t default).flushes.push),
         side 1 ((tables.getD t default).flushes.pull),
         sumE ((List.zip ((vtEqhiVars.getD t []).getD 2 []) (vtCountCols.getD t [])).map fun p =>
           ρ p.1 * ev p.2)]

theorem powers_five (xi : E) : powers xi 5 = [1, xi, xi ^ 2, xi ^ 3, xi ^ 4] := by
  simp only [powers, powersFrom, List.cons.injEq, and_true]
  refine ⟨trivial, by ring, by ring, by ring, by ring⟩

theorem vt_le_foldl_max : ∀ (l : List ℕ) (a x : ℕ), (x ∈ l ∨ x ≤ a) → x ≤ l.foldl max a
  | [], a, x, h => by simp at h; simpa using h
  | y :: l, a, x, h => by
    rw [List.foldl_cons]
    refine vt_le_foldl_max l _ x ?_
    rcases h with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (le_max_right _ _)
      · exact Or.inl h
    · exact Or.inr (le_trans h (le_max_left _ _))

/-- The guest's evaluations of table `t`, as a column function. -/
abbrev vtCol (ρ : ℕ → E) (t : ℕ) (c : ℕ) : E := ((vtEvalVars.getD t []).map ρ).getD c 0

theorem vtCol_eq {ρ : ℕ → E} {t c : ℕ} (hc : c < (vtEvalVars.getD t []).length) :
    vtCol ρ t c = ρ ((vtEvalVars.getD t []).getD c 0) := by
  rw [vtCol, List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map,
    List.getD_eq_getElem _ _ hc]

/-- A side's sum at the table's evaluations is the sum at `ρ` through its value numbers. -/
theorem side_congr (ρ χ : ℕ → E) (t : Fin 6) (eqh : List ℕ) (fl : List (List Form))
    (hfl : fl = (pySideC t .push).map (·.map FormC.toForm) ∨
      fl = (pySideC t .pull).map (·.map FormC.toForm)) :
    sumE ((List.zip eqh fl).map fun p =>
        ρ p.1 * (blockForm ⟨0, 0, p.2, t⟩ ((List.range 16).map χ) (ρ 12)).evaluate (vtCol ρ t)) =
      sumE ((List.zip eqh fl).map fun p =>
        ρ p.1 * (blockForm ⟨0, 0, p.2, t⟩ ((List.range 16).map χ) (ρ 12)).evaluate
          fun c => ρ ((vtEvalVars.getD t []).getD c 0)) := by
  refine congrArg sumE (List.map_congr_left fun p hp => ?_)
  refine congrArg (ρ p.1 * ·) (vt_blockForm_congr _ _ _ fun f hf tm htm i hi => vtCol_eq ?_)
  have hp2 := (List.of_mem_zip hp).2
  rcases hfl with rfl | rfl
  · obtain ⟨cs, hcs, hcs'⟩ := List.mem_map.mp hp2
    rw [← hcs'] at hf
    obtain ⟨fc, hfc, rfl⟩ := List.mem_map.mp hf
    obtain ⟨tc, htc, rfl⟩ := List.mem_map.mp htm
    exact flush_cols_push t cs hcs fc hfc tc htc i hi
  · obtain ⟨cs, hcs, hcs'⟩ := List.mem_map.mp hp2
    rw [← hcs'] at hf
    obtain ⟨fc, hfc, rfl⟩ := List.mem_map.mp hf
    obtain ⟨tc, htc, rfl⟩ := List.mem_map.mp htm
    exact flush_cols_pull t cs hcs fc hfc tc htc i hi

/-- **A table's term** is its `constraint_eval`. -/
theorem vt_term (hP2 : CeExEval) {ρ χ : ℕ → E} {xi : E}
    (hxi : ∀ k < 5, ρ (vtXiVars.getD k 0) = xi ^ k)
    (hce : ∀ t : Fin 6, ρ (vtCeVars.getD t 0) = (ceEx t).eval ρ χ) (t : Fin 6) (F : List Form)
    (hF : F.length = 3)
    (h0 : (F.getD 0 {}).evaluate (vtCol ρ t) =
      sumE ((List.zip ((vtEqhiVars.getD t []).getD 0 []) (tables.getD t default).flushes.push).map
        fun p => ρ p.1 * (blockForm ⟨0, 0, p.2, t⟩ ((List.range 16).map χ) (ρ 12)).evaluate
          (vtCol ρ t)))
    (h1 : (F.getD 1 {}).evaluate (vtCol ρ t) =
      sumE ((List.zip ((vtEqhiVars.getD t []).getD 1 []) (tables.getD t default).flushes.pull).map
        fun p => ρ p.1 * (blockForm ⟨0, 0, p.2, t⟩ ((List.range 16).map χ) (ρ 12)).evaluate
          (vtCol ρ t)))
    (h2 : (F.getD 2 {}).evaluate (vtCol ρ t) =
      sumE ((List.zip ((vtEqhiVars.getD t []).getD 2 []) (vtCountCols.getD t [])).map
        fun p => ρ p.1 * vtCol ρ t p.2)) :
    (if (t : ℕ) = 4 then dot [1, xi] (jumpConstraints ((vtEvalVars.getD t []).map ρ)) else 0) +
      dot [xi ^ 2, xi ^ 3, xi ^ 4] (F.map (·.evaluate (vtCol ρ t))) = ρ (vtCeVars.getD t 0) := by
  rw [hce t, hP2 t ρ χ xi hxi]
  obtain ⟨f0, f1, f2, rfl⟩ : ∃ f0 f1 f2, F = [f0, f1, f2] := by
    match F, hF with
    | [f0, f1, f2], _ => exact ⟨f0, f1, f2, rfl⟩
  simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2
  simp only [List.map_cons, List.map_nil, h0, h1, h2]
  have hpu := side_congr ρ χ t ((vtEqhiVars.getD t []).getD 0 []) _
    (Or.inl (pySide_eq t .push))
  have hpl := side_congr ρ χ t ((vtEqhiVars.getD t []).getD 1 []) _
    (Or.inr (pySide_eq t .pull))
  simp only [pySide] at hpu hpl
  rw [hpu, hpl]
  have hc : sumE ((List.zip ((vtEqhiVars.getD t []).getD 2 []) (vtCountCols.getD t [])).map
      fun p => ρ p.1 * vtCol ρ t p.2) =
      sumE ((List.zip ((vtEqhiVars.getD t []).getD 2 []) (vtCountCols.getD t [])).map
        fun p => ρ p.1 * ρ ((vtEvalVars.getD t []).getD p.2 0)) :=
    congrArg sumE (List.map_congr_left fun p hp =>
      congrArg (ρ p.1 * ·) (vtCol_eq (count_cols t t.2 p.2 (List.of_mem_zip hp).2)))
  rw [hc]
  refine congrArg (· + _) ?_
  split_ifs with h4
  · have : t = 4 := Fin.ext h4
    subst this
    refine congrArg (fun l => dot [1, xi] (jumpConstraints l)) ?_
    apply List.ext_getElem (by simp; decide)
    intro i h1 h2
    simp only [List.length_map] at h1
    rw [List.getElem_map, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem _ _ h1]
  · rfl

/-- **The final value**: the tables' weighted terms are the guest's weighted `constraint_eval`. -/
theorem vt_final (hP2 : CeExEval) {ρ χ : ℕ → E} {xi : E}
    (hxi : ∀ k < 5, ρ (vtXiVars.getD k 0) = xi ^ k)
    (hce : ∀ t : Fin 6, ρ (vtCeVars.getD t 0) = (ceEx t).eval ρ χ) (pt : List E) (hs : List ℕ)
    (hhs : hs.length = 6) (forms : List (List Form)) (hfl : forms.length = 6)
    (hsh : ∀ t < 6, (forms.getD t default).length = 3)
    (hF : ∀ t : Fin 6, (formAt forms t 0).evaluate (vtCol ρ t) =
        sumE ((List.zip ((vtEqhiVars.getD t []).getD 0 []) (tables.getD t default).flushes.push).map
          fun p => ρ p.1 * (blockForm ⟨0, 0, p.2, t⟩ ((List.range 16).map χ) (ρ 12)).evaluate
            (vtCol ρ t)) ∧
      (formAt forms t 1).evaluate (vtCol ρ t) =
        sumE ((List.zip ((vtEqhiVars.getD t []).getD 1 []) (tables.getD t default).flushes.pull).map
          fun p => ρ p.1 * (blockForm ⟨0, 0, p.2, t⟩ ((List.range 16).map χ) (ρ 12)).evaluate
            (vtCol ρ t)) ∧
      (formAt forms t 2).evaluate (vtCol ρ t) =
        sumE ((List.zip ((vtEqhiVars.getD t []).getD 2 []) (vtCountCols.getD t [])).map
          fun p => ρ p.1 * vtCol ρ t p.2))
    (ws : List E) (hws : ws.length = 6) :
    (ttVal [1, xi] [xi ^ 2, xi ^ 3, xi ^ 4] pt (List.zip tables (List.zip hs (List.zip forms ws)))
      (vtEvalVars.map (·.map ρ)) 0 0 []).1 =
      ((List.range 6).map fun t => ws.getD t 0 * ρ (vtCeVars.getD t 0)).sum := by
  have term := fun t : Fin 6 => vt_term hP2 hxi hce t (forms.getD t default) (hsh t t.2)
    (hF t).1 (hF t).2.1 (hF t).2.2
  obtain ⟨h0, h1, h2, h3, h4, h5, rfl⟩ : ∃ h0 h1 h2 h3 h4 h5, hs = [h0, h1, h2, h3, h4, h5] := by
    match hs, hhs with
    | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩
  obtain ⟨f0, f1, f2, f3, f4, f5, rfl⟩ :
      ∃ f0 f1 f2 f3 f4 f5, forms = [f0, f1, f2, f3, f4, f5] := by
    match forms, hfl with
    | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩
  obtain ⟨w0, w1, w2, w3, w4, w5, rfl⟩ : ∃ w0 w1 w2 w3 w4 w5, ws = [w0, w1, w2, w3, w4, w5] := by
    match ws, hws with
    | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩
  rw [show vtEvalVars.map (·.map ρ) = [(vtEvalVars.getD 0 []).map ρ, (vtEvalVars.getD 1 []).map ρ,
    (vtEvalVars.getD 2 []).map ρ, (vtEvalVars.getD 3 []).map ρ, (vtEvalVars.getD 4 []).map ρ,
    (vtEvalVars.getD 5 []).map ρ] from rfl, ttVal_fst6]
  have t0 : dot [xi ^ 2, xi ^ 3, xi ^ 4] (f0.map (·.evaluate (vtCol ρ 0))) =
      ρ (vtCeVars.getD 0 0) := by
    have h := term 0
    rw [ite_neg' (by decide), zero_add] at h
    exact h
  have t1 : dot [xi ^ 2, xi ^ 3, xi ^ 4] (f1.map (·.evaluate (vtCol ρ 1))) =
      ρ (vtCeVars.getD 1 0) := by
    have h := term 1
    rw [ite_neg' (by decide), zero_add] at h
    exact h
  have t2 : dot [xi ^ 2, xi ^ 3, xi ^ 4] (f2.map (·.evaluate (vtCol ρ 2))) =
      ρ (vtCeVars.getD 2 0) := by
    have h := term 2
    rw [ite_neg' (by decide), zero_add] at h
    exact h
  have t3 : dot [xi ^ 2, xi ^ 3, xi ^ 4] (f3.map (·.evaluate (vtCol ρ 3))) =
      ρ (vtCeVars.getD 3 0) := by
    have h := term 3
    rw [ite_neg' (by decide), zero_add] at h
    exact h
  have t4 : dot [1, xi] (jumpConstraints ((vtEvalVars.getD 4 []).map ρ)) +
      dot [xi ^ 2, xi ^ 3, xi ^ 4] (f4.map (·.evaluate (vtCol ρ 4))) = ρ (vtCeVars.getD 4 0) := by
    have h := term 4
    rw [ite_pos' (by decide)] at h
    exact h
  have t5 : dot [xi ^ 2, xi ^ 3, xi ^ 4] (f5.map (·.evaluate (vtCol ρ 5))) =
      ρ (vtCeVars.getD 5 0) := by
    have h := term 5
    rw [ite_neg' (by decide), zero_add] at h
    exact h
  rw [show ([1, xi] : List E).take 2 = [1, xi] from rfl, t0, t1, t2, t3, t4, t5]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, List.getD_cons_zero,
    List.getD_cons_succ]
  ring

end
end LeanVM.Guest.B1.VerifySub
