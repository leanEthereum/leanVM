/-
  LeanVM.Guest.B1.Tables.VerifyTablesSpecCe

  The value of a table's constraint evaluation `ceEx` (VerifyTablesAir): its sides' block forms
  and count columns weighted by their `eq_hi` and by `ξ^2, ξ^3, ξ^4`, plus `JUMP`'s constraints.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesAir
public import LeanVM.Guest.B1.Tables.VerifyTablesForms

/-!
# `ceEx`'s value

`ceEx_eval`: the expression `ceEx t` evaluates to the specification's constraint combination of
table `t` (V:618-639): the push and pull sides' forms (`blockForm`, the flushes of the table) and
the count columns, each weighted by its block's `eq_hi`, the three sides by `ξ^2, ξ^3, ξ^4`, and
for `JUMP` its two constraints by `1, ξ`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Complete

@[expose] public section

variable (ρ χ : ℕ → E)

theorem sumEx_eval : ∀ l : List Ex, (sumEx l).eval ρ χ = sumE (l.map (Ex.eval ρ χ))
  | [] => by simp [sumEx, Ex.eval, vt_sumE_nil]
  | a :: l => by
    rw [List.map_cons, vt_sumE_cons, ← sumEx_eval l]
    rfl

theorem prodVarsEx_eval : ∀ vs : List ℕ, (prodVarsEx vs).eval ρ χ = (vs.map ρ).prod
  | [] => by simp [prodVarsEx, Ex.eval]
  | v :: vs => by simp only [prodVarsEx, Ex.eval, prodVarsEx_eval vs, List.map_cons, List.prod_cons]

theorem termVal_eq (column : ℕ → E) (t : List ℕ × E) :
    termVal column t = t.2 * (t.1.map column).prod := by
  obtain ⟨m, c⟩ := t
  rw [termVal_coef]
  congr 1
  simp only [termVal]
  induction m with
  | nil => simp
  | cons i m ih =>
    rw [List.foldl_cons, foldl_mul_col, ih, List.map_cons, List.prod_cons]; ring

/-- A coordinate's expression is its form's value at the column evaluations. -/
theorem coordEx_eval (ev : List ℕ) (f : FormC) :
    (coordEx ev f).eval ρ χ = f.toForm.evaluate fun c => ρ (ev.getD c 0) := by
  rw [coordEx, sumEx_eval, evaluate_eq, FormC.toForm, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, Ex.eval, prodVarsEx_eval, termVal_eq, List.map_map,
    Coef.ev_eq]
  rfl

theorem getD_map_range' {α : Type} (f : ℕ → α) (d : α) {n k : ℕ} (hk : k < n) :
    ((List.range n).map f).getD k d = f k := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range]

theorem pySideC_short' : ∀ t : Fin 6, ((pySideC t .push).all fun c => decide (c.length ≤ 16)) &&
    ((pySideC t .pull).all fun c => decide (c.length ≤ 16)) = true := by
  decide +kernel

theorem pySideC_short (t : Fin 6) (side : Side) : ∀ c ∈ pySideC t side, c.length ≤ 16 := by
  intro c hc
  have h := pySideC_short' t
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  cases side
  · exact h.1 c hc
  · exact h.2 c hc

/-- A block's expression is its form's value. -/
theorem blockEx_eval (ev : List ℕ) (coords : List FormC) (hc : coords.length ≤ 16) (t : ℕ) :
    (blockEx ev coords).eval ρ χ = (blockForm ⟨0, 0, coords.map FormC.toForm, t⟩
      ((List.range 16).map χ) (ρ 12)).evaluate fun c => ρ (ev.getD c 0) := by
  rw [evaluate_blockForm, blockEx, Ex.eval, sumEx_eval]
  congr 2
  simp only [List.map_map]
  rw [List.zipIdx_map]
  simp only [List.map_map]
  refine List.map_congr_left fun p hp => ?_
  have hp2 : p.2 < 16 := by
    have := List.mem_zipIdx hp
    omega
  simp only [Function.comp_apply, Ex.eval, coordEx_eval]
  rw [show (Prod.map FormC.toForm id p).2 = p.2 from rfl,
    show (Prod.map FormC.toForm id p).1 = p.1.toForm from rfl, getD_map_range' _ _ hp2]

theorem sideEx_eval (eqh : List ℕ) (forms : List Ex) :
    (sideEx eqh forms).eval ρ χ =
      sumE ((List.zip eqh forms).map fun p => ρ p.1 * p.2.eval ρ χ) := by
  rw [sideEx, sumEx_eval, List.map_map]
  rfl

theorem dot_two (a b c d : E) : dot [a, b] [c, d] = a * c + b * d := by
  show 0 + a * c + b * d = a * c + b * d
  rw [zero_add]

theorem dot_three (a b c d e f : E) : dot [a, b, c] [d, e, f] = a * d + b * e + c * f := by
  show 0 + a * d + b * e + c * f = a * d + b * e + c * f
  rw [zero_add]

/-- A side of table `t` at the guest's values. -/
theorem side_eval (t : Fin 6) (s : Side) (k : ℕ) :
    (sideEx ((vtEqhiVars.getD t []).getD k [])
      ((pySideC t s).map (blockEx (vtEvalVars.getD t [])))).eval ρ χ =
    sumE ((List.zip ((vtEqhiVars.getD t []).getD k []) (pySide t s)).map fun p =>
      ρ p.1 * (blockForm ⟨0, 0, p.2, t⟩ ((List.range 16).map χ) (ρ 12)).evaluate
        fun c => ρ ((vtEvalVars.getD t []).getD c 0)) := by
  rw [sideEx_eval, pySide_eq, List.zip_map_right, List.map_map, List.zip_map_right, List.map_map]
  refine congrArg sumE (List.map_congr_left fun p hp => ?_)
  simp only [Function.comp_apply, Prod.map, id]
  rw [blockEx_eval ρ χ _ _ (pySideC_short t s p.2 (List.of_mem_zip hp).2) t]

/-- **A table's constraint evaluation** (V:618-639): `ceEx t` at the guest's values. -/
theorem ceEx_eval (t : Fin 6) (ρ χ : ℕ → E) (xi : E)
    (hxi : ∀ k < 5, ρ (vtXiVars.getD k 0) = xi ^ k) :
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
           ρ p.1 * ev p.2)] := by
  intro ev side
  have x2 : ρ 4624 = xi ^ 2 := hxi 2 (by omega)
  have x3 : ρ 4625 = xi ^ 3 := hxi 3 (by omega)
  have x4 : ρ 4626 = xi ^ 4 := hxi 4 (by omega)
  have hp := side_eval ρ χ t .push 0
  have hl := side_eval ρ χ t .pull 1
  simp only [pySide] at hp hl
  have hc : (sideEx ((vtEqhiVars.getD t []).getD 2 [])
      ((vtCountCols.getD t []).map fun l => Ex.var ((vtEvalVars.getD t []).getD l 0))).eval ρ χ =
      sumE ((List.zip ((vtEqhiVars.getD t []).getD 2 []) (vtCountCols.getD t [])).map fun p =>
        ρ p.1 * ev p.2) := by
    rw [sideEx_eval, List.zip_map_right, List.map_map]
    rfl
  have hforms : (Ex.add (.mul (.var 4624) (sideEx ((vtEqhiVars.getD t []).getD 0 [])
      ((pySideC t .push).map (blockEx (vtEvalVars.getD t [])))))
      (.add (.mul (.var 4625) (sideEx ((vtEqhiVars.getD t []).getD 1 [])
        ((pySideC t .pull).map (blockEx (vtEvalVars.getD t [])))))
        (.mul (.var 4626) (sideEx ((vtEqhiVars.getD t []).getD 2 [])
          ((vtCountCols.getD t []).map fun l => Ex.var ((vtEvalVars.getD t []).getD l 0)))))).eval
      ρ χ = dot [xi ^ 2, xi ^ 3, xi ^ 4]
        [side 0 ((tables.getD t default).flushes.push),
         side 1 ((tables.getD t default).flushes.pull),
         sumE ((List.zip ((vtEqhiVars.getD t []).getD 2 []) (vtCountCols.getD t [])).map fun p =>
           ρ p.1 * ev p.2)] := by
    show ρ 4624 * _ + (ρ 4625 * _ + ρ 4626 * _) = _
    rw [hp, hl, hc, x2, x3, x4, dot_three]
    ring
  unfold ceEx
  by_cases h4 : t = 4
  · subst h4
    rw [ite_pos' (show ((4 : Fin 6) : ℕ) = 4 from rfl)]
    show Ex.eval ρ χ (jumpEx _) + Ex.eval ρ χ _ = _
    rw [hforms]
    refine congrArg (· + _) ?_
    have x0 : ρ 4622 = 1 := by have := hxi 0 (by omega); rw [pow_zero] at this; exact this
    have x1 : ρ 4623 = xi := by have := hxi 1 (by omega); rw [pow_one] at this; exact this
    simp only [jumpEx, Ex.eval, x0, x1, ofK_one]
    rw [jumpConstraints, dot_two]
    simp only [colIdx, show jumpColumns.idxOf "v_cond" = 5 by decide,
      show jumpColumns.idxOf "w" = 12 by decide, show jumpColumns.idxOf "b" = 13 by decide,
      getD_map_range' _ _ (show 5 < 14 by omega), getD_map_range' _ _ (show 12 < 14 by omega),
      getD_map_range' _ _ (show 13 < 14 by omega)]
    ring
  · have h4' : ¬ ((t : ℕ) = 4) := fun h => h4 (Fin.ext h)
    simp only [h4, h4', ↓reduceIte]
    rw [hforms, zero_add]

end
end LeanVM.Guest.B1.VerifySub
