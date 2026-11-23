/-
  LeanVM.Guest.B1.Whir.CFinRs

  A non-final level's residual chains and their sums into the inner chain, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CFinR
public import LeanVM.Guest.B1.Whir.Residuals

/-!
# The residuals, honestly

`rcC`: a level's chains' buffer, the two chains `h ← (h + P(p))·μ`, `hh ← (hh + H(p))·μ` over the
first `8j` positions at entries `2j`, `2j + 1`. `resB_complete`: the level's sums stored into
`inner_chain`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {M : Reader → Prop} {H : CallRel → Reader → Prop}

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

/-- A level's residual's static facts. -/
structure ResStatic (lv : OsLv) (hsv : List E) : Prop where
  cols : 1 ≤ lv.logCols
  nhs : 1 ≤ lv.folds
  b3 : lv.highBits ≤ 3
  bn : lv.highBits ≤ lv.logCols + 1
  len : hsv.length = lv.folds
  nbu : lv.queries / resBatch < u128Bound
  nb64 : 2 * (lv.queries / resBatch + 1) < 2 ^ 64 - 1

/-- A level's sums into the inner chain, from the chains `h`, `hh` and the slow sum `sl`, at
`a`. -/
def resB (ich ls la lvl h hh sl a : ℕ) : List Stmt :=
  [osLd a ich (2 * lvl), osLd (a + 1) ls lvl, osMul (a + 2) (a + 1) h, osAdd (a + 3) a (a + 2),
    osAdd (a + 4) (a + 3) sl, osLd (a + 4) ich (2 * lvl + 2), osLd (a + 5) ich (2 * lvl + 1),
    osLd (a + 6) osBetas lvl, osLd (a + 7) la lvl, osMul (a + 8) (a + 6) (a + 7),
    osMul (a + 9) (a + 8) hh, osAdd (a + 10) (a + 5) (a + 9), osLd (a + 10) ich (2 * lvl + 3)]

theorem resB_complete {ich ls la lvl h hh sl a : ℕ} {σ : Val} {i0 i1 s b af P Q SL : E}
    (hich : ich < a) (hls : ls < a) (hla : la < a) (hh1 : h < a) (hh2 : hh < a) (hsl : sl < a)
    (ha36 : 43 ≤ a)
    (hv : ∀ C rd, HM M H C rd → σ (.n h) = P ∧ σ (.n hh) = Q ∧ σ (.n sl) = SL)
    (hm : ∀ C rd, HM M H C rd → LoadHolds rd (σ (.n ich)) (2 * lvl) i0 ∧
      LoadHolds rd (σ (.n ls)) lvl s ∧ LoadHolds rd (σ (.n ich)) (2 * lvl + 1) i1 ∧
      LoadHolds rd (σ (.n osBetas)) lvl b ∧ LoadHolds rd (σ (.n la)) lvl af ∧
      LoadHolds rd (σ (.n ich)) (2 * lvl + 2) (i0 + s * P + SL) ∧
      LoadHolds rd (σ (.n ich)) (2 * lvl + 3) (i1 + b * af * Q)) :
    BlkA M H σ a (a + 11) (resB ich ls la lvl h hh sl a) (fun _ ↦ True) := by
  refine BlkA.ofHM (lstF a [i0, s, s * P, i0 + s * P, i0 + s * P + SL, i1, b, af, b * af, b * af * Q,
    i1 + b * af * Q]) fun C rd hH σ' ha hr ↦ ?_
  have hv' : ∀ j < 11, σ' (.n (a + j)) = [i0, s, s * P, i0 + s * P, i0 + s * P + SL, i1, b, af,
      b * af, b * af * Q, i1 + b * af * Q].getD j 0 := fun j hj ↦ lstF_at hr (by simp) j (by simp; omega)
  have v0 := hv' 0 (by omega)
  have v1 := hv' 1 (by omega)
  have v2 := hv' 2 (by omega)
  have v3 := hv' 3 (by omega)
  have v4 := hv' 4 (by omega)
  have v5 := hv' 5 (by omega)
  have v6 := hv' 6 (by omega)
  have v7 := hv' 7 (by omega)
  have v8 := hv' 8 (by omega)
  have v9 := hv' 9 (by omega)
  have v10 := hv' 10 (by omega)
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  obtain ⟨m0, m1, m2, m3, m4, m5, m6⟩ := hm C rd hH
  obtain ⟨e1, e2, e3⟩ := hv C rd hH
  refine ⟨?_, trivial⟩
  simp only [resB, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, holds_mul, holds_add,
    osLd, osMul, osAdd]
  rw [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, ha _ hich, ha _ hls, ha _ hla,
    ha _ (show osBetas < a by show 20 < a; omega), ha _ hh1, ha _ hh2, ha _ hsl, e1, e2, e3]
  exact ⟨m0, m1, rfl, rfl, rfl, m5, m2, m3, m4, rfl, rfl, rfl, m6⟩

end
end LeanVM.Guest.B1.Whir
