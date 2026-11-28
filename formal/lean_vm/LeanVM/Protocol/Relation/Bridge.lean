/-
  LeanVM.Protocol.Relation.Bridge

  A column claim placed on the stack holds of the stack exactly when it holds of its column.
-/

module

public import LeanVM.Protocol.Relation.Placement
public import LeanVM.Protocol.Relation.Stack
import LeanVM.Protocol.Tables
import LeanVM.ToMathlib.Finset

/-!
# Column claims on the stack

`ColumnClaim.onStack` (`lib.rs`) weighs the stack by `eq` of the claim's stack point, its point
then its placement's selector (`Placement.stackPoint`). The selector's kernel on the cube is the
indicator of the placement's block (`eqEval_selectorPoint_boolPoint`), and a placement of a layout
`buildLayout` gives is aligned and within the stack (`placement_aligned`), so the stack claim's sum
is the column's multilinear extension at the point (`stackClaimHolds_onStack_iff`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Tables Finset

@[expose] public section

theorem eOfNat_bit (b : ℕ) (hb : b < 2) : eOfNat b = if b = 1 then 1 else 0 := by
  interval_cases b <;> rfl

/-- A selector's coordinates: its low bit, then the rest. -/
theorem selectorPoint_succ (s m : ℕ) :
    selectorPoint s (m + 1) = eOfNat (s % 2) :: selectorPoint (s / 2) m := by
  simp only [selectorPoint, List.range_succ_eq_map, List.map_cons, List.map_map,
    Nat.shiftRight_zero]
  congr 1
  refine List.map_congr_left fun i _ ↦ ?_
  simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, pow_succ']

/-- **The selector's kernel on the cube is the block's indicator.** -/
theorem eqEval_selectorPoint_boolPoint :
    ∀ (m s z : ℕ), s < 2 ^ m → z < 2 ^ m →
      eqEval (selectorPoint s m) (boolPoint m z) = if z = s then 1 else 0
  | 0, s, z, hs, hz => by simp at hs hz; subst hs; subst hz; simp [selectorPoint, eqEval]
  | m + 1, s, z, hs, hz => by
    rw [selectorPoint_succ, boolPoint_succ, eqEval_cons,
      eqEval_selectorPoint_boolPoint m (s / 2) (z / 2) (by rw [pow_succ] at hs; omega)
        (by rw [pow_succ] at hz; omega)]
    rw [eOfNat_bit _ (Nat.mod_lt _ (by norm_num)), Nat.testBit_zero]
    have hsz : z = s ↔ z % 2 = s % 2 ∧ z / 2 = s / 2 := by omega
    have h2 := two_eq_zero_E
    rcases Nat.mod_two_eq_zero_or_one s with h0 | h0 <;>
      rcases Nat.mod_two_eq_zero_or_one z with h1 | h1 <;>
      by_cases h3 : z / 2 = s / 2 <;>
      simp [h0, h1, h3, hsz] <;> linear_combination h2

/-- The bytes of `Nat`: `2^a ≤ 2^b` gives `a ≤ b`. -/
theorem le_of_two_pow_le {a b : ℕ} (h : 2 ^ a ≤ 2 ^ b) : a ≤ b :=
  (Nat.pow_le_pow_iff_right (by norm_num)).mp h

/-- The stack's sum under a stack point: the block the selector names, summed with `eq` of the
point. -/
theorem sum_stackPoint (μ vc s : ℕ) (q : Column μ) (point : List E) (hlen : point.length = vc)
    (hvc : vc ≤ μ) (hsμ : s < 2 ^ (μ - vc)) :
    ∑ x : Fin (2 ^ μ), eqEval (point ++ selectorPoint s (μ - vc)) (boolPoint μ x) * ofK (cell q x) =
      ∑ y ∈ range (2 ^ vc), eqEval (boolPoint vc y) point * ofK (cell q (2 ^ vc * s + y)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hvc
  rw [show vc + k - vc = k by omega] at hsμ ⊢
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ eqEval (point ++ selectorPoint s k)
    (boolPoint (vc + k) x) * ofK (cell q x)), pow_add, sum_range_mul']
  have hinner : ∀ z ∈ range (2 ^ k), ∑ y ∈ range (2 ^ vc),
      eqEval (point ++ selectorPoint s k) (boolPoint (vc + k) (y + 2 ^ vc * z)) *
        ofK (cell q (y + 2 ^ vc * z)) =
      if z = s then ∑ y ∈ range (2 ^ vc),
        eqEval (boolPoint vc y) point * ofK (cell q (2 ^ vc * s + y)) else 0 := by
    intro z hz
    split_ifs with hzs
    · subst hzs
      refine sum_congr rfl fun y hy ↦ ?_
      rw [boolPoint_add _ _ _ _ (mem_range.mp hy),
        eqEval_append _ _ _ _ (by rw [hlen, length_boolPoint]),
        eqEval_selectorPoint_boolPoint _ _ _ hsμ hsμ, eqEval_comm]
      simp [add_comm]
    · refine sum_eq_zero fun y hy ↦ ?_
      rw [boolPoint_add _ _ _ _ (mem_range.mp hy),
        eqEval_append _ _ _ _ (by rw [hlen, length_boolPoint]),
        eqEval_selectorPoint_boolPoint _ _ _ hsμ (mem_range.mp hz)]
      simp [hzs]
  rw [sum_congr rfl hinner, sum_ite_eq']
  simp [hsμ]

/-- **A column claim placed on the stack holds of the stack exactly when it holds of its
column**, for a layout `buildLayout` gives, a claim at a point of its placement's variables, on a
column that is not a `KECCAK` output lane. -/
theorem stackClaimHolds_onStack_iff {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hb : buildLayout bytecode lm rows = some layout) (q : Column layout.stackLog)
    {c : ColumnClaim} {p : Placement} (hp : layout.placements.getD c.column none = some p)
    (hlen : c.point.length = p.variableCount) (hk : keccakOutputLane c.column = none) :
    StackClaimHolds (fun x ↦ eqEval (p.stackPoint c.point layout.stackLog) x, c.value) q ↔
      ColumnClaimHolds layout q c := by
  obtain ⟨⟨s, hs⟩, hfit⟩ := placement_aligned hb hp
  have hvc : p.variableCount ≤ layout.stackLog := le_of_two_pow_le (by omega)
  have hsμ : s < 2 ^ (layout.stackLog - p.variableCount) := by
    have h1 : 2 ^ layout.stackLog = 2 ^ p.variableCount * 2 ^ (layout.stackLog - p.variableCount) := by
      rw [← pow_add]; congr 1; omega
    have h3 : 2 ^ p.variableCount * (s + 1) ≤
        2 ^ p.variableCount * 2 ^ (layout.stackLog - p.variableCount) := by
      rw [mul_add, mul_one, ← h1, ← hs]; exact hfit
    have := Nat.le_of_mul_le_mul_left h3 (by positivity)
    omega
  have hsel : p.index >>> p.variableCount = s := by
    rw [Nat.shiftRight_eq_div_pow, hs, Nat.mul_div_cancel_left _ (by positivity)]
  unfold StackClaimHolds ColumnClaimHolds rowMle
  simp only [Placement.stackPoint, hsel]
  rw [sum_stackPoint _ _ _ q _ hlen hvc hsμ, hlen,
    multilinearEval_eq_sum p.variableCount _ _ (by simp) hlen, eq_comm]
  refine iff_of_eq (congrArg₂ _ rfl (sum_congr rfl fun y hy ↦ ?_))
  have hy := mem_range.mp hy
  have hp' : layout.placements[c.column]?.getD none = some p := by
    rwa [List.getD_eq_getElem?_getD] at hp
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hy,
    Option.map_some, Option.getD_some, columnValue, hk, columnRow, hp']
  rw [hs]
  ring_nf

end

end LeanVM.Protocol.Relation
