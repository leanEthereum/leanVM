/-
  LeanVM.Prover.TableSpec

  The specification's running claim of the table sumcheck, one round split table by table: the
  waiting tables' line and the active tables' equality-weighted sums over the lower coordinates.
-/

module

public import LeanVM.Prover.TableMle

/-!
# The table sumcheck's round, table by table

The specification's running claim after the challenges `pre` and `X`
(`LeanVM.Protocol.EndToEnd.Complete.claimOf`) sums the honest summand over the `m` coordinates
below the one `X` binds. `claimOf_snoc_split` splits it table by table, with `ω_t` the product of
the table weight's factors at `pre` (`preWeight`):

* a table no taller than `m` (waiting) contributes `ω_t · X · σ_t`, `σ_t` the equality-weighted
  sum of its rows (`waitSum`): its weight's factors above its height are the coordinates
  themselves, whose product only the all-ones corner survives (`sum_cube_weight`);
* a taller table (active) contributes `ω_t · (1 + e_m + X) · Σ_x eq(e_{<m}, x) · Q_t(x, X)`.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Complete Finset
open LeanVM.Protocol.EndToEnd (boolPoint)
open LeanVM.Protocol.EndToEnd.Complete

@[expose] public section

variable (prog : LeanIsaProgram) (s : Sizes) (q : LeanVM.Protocol.Column (leanIsaμ prog s))

/-- Table `t`'s constraints and forms at the evaluations `ev`. -/
def rowPart (cp fp : List E) (bus : BusResult) (t : Fin 6) (ev : List E) : E :=
  consPart cp t ev + formPart fp bus t ev

/-- The product of table `t`'s weight's factors at the challenges `pre`, the last binding the
lowest bound coordinate. -/
def preWeight (bus : BusResult) (t : Fin 6) (pre : List E) : E :=
  ∏ i ∈ range pre.length,
    weightFactor bus.point (s.τ t) (nRounds s - pre.length + i) (pre.reverse.getD i 0)

/-- Table `t`'s rows summed against the equality weights of the bus point's first `τ_t`
coordinates. -/
def waitSum (cp fp : List E) (bus : BusResult) (t : Fin 6) : E :=
  ∑ y : Fin (2 ^ s.τ t), eqEval (bus.point.take (s.τ t)) (boolPoint (s.τ t) y) *
    rowPart cp fp bus t (rowEvals prog s q t y)

/-- The weight of table `t` at `boolPoint m x ++ X :: pre.reverse`, split at the coordinate `m`
`X` binds. -/
theorem weight_split (bus : BusResult) (t : Fin 6) (pre : List E) (hk : pre.length < nRounds s)
    (x : ℕ) (X : E) :
    (tableWeights (tableLogs s) bus.point
        (boolPoint (nRounds s - pre.length - 1) x ++ X :: pre.reverse)).getD t 0 =
      (∏ v ∈ range (nRounds s - pre.length - 1), weightFactor bus.point (s.τ t) v
          ((boolPoint (nRounds s - pre.length - 1) x).getD v 0)) *
        weightFactor bus.point (s.τ t) (nRounds s - pre.length - 1) X * preWeight s bus t pre := by
  rw [getD_tableWeights _ _ _ _ (by simp [tableLogs]), getD_tableLogs, preWeight]
  have hnk : nRounds s - pre.length = nRounds s - pre.length - 1 + 1 := by omega
  generalize hm : nRounds s - pre.length - 1 = m at hnk ⊢
  have hb : (boolPoint m x).length = m := LeanVM.Protocol.Whir.Complete.length_boolPoint m x
  have hlen : (boolPoint m x ++ X :: pre.reverse).length = m + (pre.length + 1) := by
    simp only [List.length_append, hb, List.length_cons, List.length_reverse]
  rw [hlen, prod_range_add, prod_range_succ']
  simp only [add_zero]
  have e1 : ∏ v ∈ range m, weightFactor bus.point (s.τ t) v
      ((boolPoint m x ++ X :: pre.reverse).getD v 0) =
      ∏ v ∈ range m, weightFactor bus.point (s.τ t) v ((boolPoint m x).getD v 0) :=
    prod_congr rfl fun v hv ↦ by
      rw [List.getD_append _ _ _ _ (by rw [hb]; exact mem_range.mp hv)]
  have e2 : (boolPoint m x ++ X :: pre.reverse).getD m 0 = X := by
    rw [List.getD_append_right _ _ _ _ (by omega), hb, Nat.sub_self]
    simp
  have e3 : ∏ i ∈ range pre.length, weightFactor bus.point (s.τ t) (m + (i + 1))
      ((boolPoint m x ++ X :: pre.reverse).getD (m + (i + 1)) 0) =
      ∏ i ∈ range pre.length, weightFactor bus.point (s.τ t) (nRounds s - pre.length + i)
        (pre.reverse.getD i 0) :=
    prod_congr rfl fun i _ ↦ by
      rw [List.getD_append_right _ _ _ _ (by omega), hb,
        show m + (i + 1) - m = i + 1 by omega, List.getD_cons_succ,
        show m + (i + 1) = nRounds s - pre.length + i by omega]
  rw [e1, e2, e3]
  ring

/-- **The running claim, split table by table.** -/
theorem claimOf_snoc_split {bus : BusResult} (hb : BusGood prog s q bus) (cp fp : List E)
    (pre : List E) (hk : pre.length < nRounds s) (X : E) :
    claimOf prog s q cp fp bus (pre ++ [X]) = ∑ t : Fin 6, preWeight s bus t pre *
      (if s.τ t ≤ nRounds s - pre.length - 1 then X * waitSum prog s q cp fp bus t
      else (1 + bus.point.getD (nRounds s - pre.length - 1) 0 + X) *
        ∑ x ∈ range (2 ^ (nRounds s - pre.length - 1)),
          eqEval (bus.point.take (nRounds s - pre.length - 1))
              (boolPoint (nRounds s - pre.length - 1) x) *
            rowPart cp fp bus t (evalsAt prog s q t
              (boolPoint (nRounds s - pre.length - 1) x ++ X :: pre.reverse))) := by
  rw [claimOf_snoc]
  simp only [summand_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  simp only [weight_split s bus t pre hk]
  generalize nRounds s - pre.length - 1 = m
  by_cases hτ : s.τ t ≤ m
  · rw [ite_eq_left hτ]
    have hwf : weightFactor bus.point (s.τ t) m X = X := by
      simp [weightFactor, not_lt.mpr hτ]
    have hev : ∀ x, evalsAt prog s q t (boolPoint m x ++ X :: pre.reverse) =
        evalsAt prog s q t (boolPoint m x) := fun x ↦ by
      unfold evalsAt
      rw [List.take_append_of_le_length (by rw [LeanVM.Protocol.Whir.Complete.length_boolPoint]; exact hτ)]
    simp only [hwf, hev]
    have hsum : ∑ x ∈ range (2 ^ m), (∏ v ∈ range m, weightFactor bus.point (s.τ t) v
        ((boolPoint m x).getD v 0)) * rowPart cp fp bus t (evalsAt prog s q t (boolPoint m x)) =
        waitSum prog s q cp fp bus t := by
      rw [sum_cube_weight bus.point hτ (hb.point_length t)
        (fun r ↦ rowPart cp fp bus t (evalsAt prog s q t r))
        (fun r ↦ by simp only [evalsAt, List.take_take, min_self]), waitSum]
      simp only [evalsAt_boolPoint]
    rw [← hsum, mul_sum, mul_sum]
    refine sum_congr rfl fun x _ ↦ ?_
    simp only [rowPart]
    ring
  · rw [ite_eq_right hτ]
    have hmτ : m < s.τ t := not_le.mp hτ
    have hlen : (bus.point.take m).length = m := by
      have := hb.point_length t
      simp only [List.length_take]
      omega
    have hwf : weightFactor bus.point (s.τ t) m X = 1 + bus.point.getD m 0 + X := by
      simp [weightFactor, hmτ]
    have heq : ∀ x, ∏ v ∈ range m, weightFactor bus.point (s.τ t) v ((boolPoint m x).getD v 0) =
        eqEval (bus.point.take m) (boolPoint m x) := fun x ↦ by
      rw [eqEval_eq_prod_range _ _ m hlen (LeanVM.Protocol.Whir.Complete.length_boolPoint m x)]
      refine prod_congr rfl fun v hv ↦ ?_
      have hv' := mem_range.mp hv
      simp only [weightFactor, show v < s.τ t by omega, ↓reduceIte, getD_take_of_lt _ hv']
    simp only [hwf, heq]
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun x _ ↦ ?_
    simp only [rowPart]
    ring

end
end LeanVM.Prover
