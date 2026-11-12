/-
  LeanVM.Guest.B1.Whir.CFinRs

  A non-final level's residual chains and their sums into the inner chain, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CFinR
public import LeanVM.Guest.B1.Whir.Residuals

/-!
# The residuals, honestly (G:1802-1837)

`rcC`: a level's chains' buffer, the two chains `h ← (h + P(p))·μ`, `hh ← (hh + H(p))·μ` over the
first `8j` positions at entries `2j`, `2j + 1`. `resB_complete`: the level's sums stored into
`inner_chain`.
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


/-- A level's sums into the inner chain, from the chains `h`, `hh`, at `a`. -/
def resB (ich ls la lvl h hh a : ℕ) : List Stmt :=
  [osLd a ich (2 * lvl), osLd (a + 1) ls lvl, osMul (a + 2) (a + 1) h, osAdd (a + 3) a (a + 2),
    osLd (a + 3) ich (2 * lvl + 2), osLd (a + 4) ich (2 * lvl + 1), osLd (a + 5) osBetas lvl,
    osLd (a + 6) la lvl, osMul (a + 7) (a + 5) (a + 6), osMul (a + 8) (a + 7) hh,
    osAdd (a + 9) (a + 4) (a + 8), osLd (a + 9) ich (2 * lvl + 3)]

theorem resB_complete {ich ls la lvl h hh a : ℕ} {σ : Val} {i0 i1 s b af P Q : E} (hich : ich < a)
    (hls : ls < a) (hla : la < a) (hh1 : h < a) (hh2 : hh < a) (ha36 : 33 ≤ a)
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
        (.cons (.load (by omega) (by omega)) (.cons (.load (by omega) (by show 20 < a + 5; omega))
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
  simp only [ha _ hich, ha _ hls, ha _ hla, ha _ (show 20 < a by omega), ha _ hh1, ha _ hh2, e3, e9,
    v1, v2, q0, q1, q2, q3, q4, false_implies, true_and]
  exact ⟨m0, m1, m5, m2, m3, m4, m6⟩


end
end LeanVM.Guest.B1.Whir
