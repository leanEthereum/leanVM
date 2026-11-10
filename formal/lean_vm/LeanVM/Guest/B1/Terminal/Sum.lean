/-
  LeanVM.Guest.B1.Terminal.Sum

  The stacked opening's batched weight (`stackWeight`) as the guest sums it: the ring switch's
  claim, then each pooled claim but the output lanes' at `λ^(1 + rank)`, the outputs' claim, the
  out-of-domain claim.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.B1.Terminal.Interface

/-!
# The batched weight, as a sum

`stackWeight_eq`: `dot (powers λ n)` over the ring switch's claim, the kept pooled claims, the
outputs' claim and the out-of-domain claim is the ring claim's weight, plus
`Σ_j λ^(1 + poolRank j)·w_j` over the pooled claims `j` not on an output lane, plus
`λ^(1 + poolRank 159)` times the outputs' claim's weight and `λ^(2 + poolRank 159)·eq(z, x)`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier Finset

@[expose] public section

theorem foldl_add_eq (a : E) : ∀ l : List E, l.foldl (· + ·) a = a + l.sum
  | [] => by simp
  | b :: l => by rw [List.foldl_cons, foldl_add_eq _ l, List.sum_cons, add_assoc]

theorem dot_cons (a b : E) (l r : List E) : dot (a :: l) (b :: r) = a * b + dot l r := by
  simp only [dot, List.zipWith_cons_cons, foldl_add_eq, zero_add, List.sum_cons]

theorem dot_powersFrom (b : E) : ∀ (n : ℕ) (a : E) (l : List E),
    dot (powersFrom a b n) l = ∑ i ∈ range (min n l.length), a * b ^ i * l.getD i 0
  | 0, a, l => by simp [powersFrom, dot]
  | n + 1, a, [] => by simp [powersFrom, dot]
  | n + 1, a, c :: l => by
    rw [powersFrom, dot_cons, dot_powersFrom b n, List.length_cons,
      show min (n + 1) (l.length + 1) = min n l.length + 1 by omega, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    refine congrArg (· + _) (sum_congr rfl fun i _ ↦ by ring)

/-- The rank of `j` among the kept entries of `l`. -/
def keptRank {α : Type} [Inhabited α] (P : α → Bool) (l : List α) (j : ℕ) : ℕ :=
  ((List.range j).filter fun i ↦ P (l.getD i default)).length

theorem keptRank_cons {α : Type} [Inhabited α] (P : α → Bool) (a : α) (t : List α) (j : ℕ) :
    keptRank P (a :: t) (j + 1) = (if P a then 1 else 0) + keptRank P t j := by
  unfold keptRank
  rw [List.range_succ_eq_map, List.filter_cons, List.filter_map]
  simp only [List.getD_cons_zero, Function.comp_def, List.getD_cons_succ]
  split <;> simp [add_comm]

/-- **Kept entries, at their ranks.** -/
theorem filter_pow_sum {α : Type} [Inhabited α] (P : α → Bool) (f : α → E) (b : E) :
    ∀ (l : List α) (s : ℕ),
      ∑ i ∈ range (l.filter P).length, b ^ (s + i) * f ((l.filter P).getD i default) =
        ∑ j ∈ range l.length,
          if P (l.getD j default) then b ^ (s + keptRank P l j) * f (l.getD j default) else 0
  | [], s => by simp
  | a :: t, s => by
    rw [List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, keptRank_cons]
    have h0 : keptRank P (a :: t) 0 = 0 := by simp [keptRank]
    rw [h0, List.filter_cons]
    by_cases hp : P a
    · simp only [hp, ↓reduceIte, List.length_cons, add_zero]
      rw [sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
      rw [show (fun i ↦ b ^ (s + (i + 1)) * f ((List.filter P t).getD i default)) =
        fun i ↦ b ^ (s + 1 + i) * f ((List.filter P t).getD i default) from
          funext fun i ↦ by rw [show s + (i + 1) = s + 1 + i by ring]]
      rw [filter_pow_sum P f b t (s + 1)]
      refine congrArg (· + _) (sum_congr rfl fun j _ ↦ ?_)
      rw [show s + (1 + keptRank P t j) = s + 1 + keptRank P t j by ring]
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, zero_add, add_zero]
      rw [filter_pow_sum P f b t s]

theorem filter_length_rank {α : Type} [Inhabited α] (P : α → Bool) :
    ∀ l : List α, (l.filter P).length = keptRank P l l.length
  | [] => by simp [keptRank]
  | a :: t => by
    rw [List.length_cons, keptRank_cons, List.filter_cons, ← filter_length_rank P t]
    split <;> simp [add_comm]

/-- The batch of the ring claim `R`, the weights `Ws`, the outputs' weight `wo` and the
out-of-domain weight `wd`. -/
theorem stack_dot (R wo wd lam : E) (Ws : List E) :
    dot (powers lam (R :: (Ws ++ [wo, wd])).length) (R :: (Ws ++ [wo, wd])) =
      R + ∑ i ∈ range Ws.length, lam ^ (1 + i) * Ws.getD i 0 + lam ^ (1 + Ws.length) * wo +
        lam ^ (2 + Ws.length) * wd := by
  have hlen : (R :: (Ws ++ [wo, wd])).length = Ws.length + 1 + 1 + 1 := by simp
  rw [powers, dot_powersFrom, min_self, hlen, sum_range_succ', sum_range_succ, sum_range_succ]
  simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, one_mul, mul_one]
  have hlast : (Ws ++ [wo, wd]).getD Ws.length 0 = wo := by simp [List.getD_eq_getElem?_getD]
  have hlast2 : (Ws ++ [wo, wd]).getD (Ws.length + 1) 0 = wd := by
    simp [List.getD_eq_getElem?_getD]
  have hs : ∑ i ∈ range Ws.length, lam ^ (i + 1) * (Ws ++ [wo, wd]).getD i 0 =
      ∑ i ∈ range Ws.length, lam ^ (1 + i) * Ws.getD i 0 := by
    refine sum_congr rfl fun i hi ↦ ?_
    have hi' := mem_range.mp hi
    rw [add_comm i 1]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi']
  rw [hs, hlast, hlast2]
  ring

/-- A pooled claim's weight on the stack at `x`. -/
def wOf (layout : Layout) (x : List E) (c : ColumnClaim) : E := (c.stackClaim layout).1 x

/-- **The batched weight, as the guest sums it.** -/
theorem stackWeight_eq (layout : Layout) {claims : List ColumnClaim} (out : ColumnClaim)
    (ringPoint coeffs oodPoint : List E) (lam : E) (x : List E)
    (hcols : claims.map (·.column) = Tables.claimColumns) :
    stackWeight layout (openedClaims claims [out]) ringPoint coeffs oodPoint lam x =
      (ringSwitchClaim layout 0 (fun rP ↦ ringWeight ringPoint rP coeffs)).1 x +
      (∑ j ∈ range Tables.nClaims, if Tables.claimColumns.getD j 0 ∉ keccakOutputColumns then
        lam ^ (1 + poolRank j) * wOf layout x (claims.getD j default) else 0) +
      lam ^ (1 + poolRank Tables.nClaims) * wOf layout x out +
      lam ^ (2 + poolRank Tables.nClaims) * eqEval oodPoint x := by
  have hlen : claims.length = Tables.nClaims := by
    rw [← List.length_map (f := (·.column)), hcols]; decide +kernel
  have hcol : ∀ i < claims.length,
      (claims.getD i default).column = Tables.claimColumns.getD i 0 := by
    intro i hi
    rw [← hcols, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by simpa using hi),
      List.getElem_map]
  let P : ColumnClaim → Bool := fun c ↦ decide (c.column ∉ keccakOutputColumns)
  have hrank : ∀ j ≤ claims.length, keptRank P claims j = poolRank j := by
    intro j hj
    unfold keptRank poolRank
    congr 1
    refine List.filter_congr fun i hi ↦ ?_
    simp only [P]
    rw [hcol i (by have := List.mem_range.mp hi; omega)]
  have hmap : ((ringSwitchClaim layout 0 (fun rP ↦ ringWeight ringPoint rP coeffs) ::
      (openedClaims claims [out]).map (·.stackClaim layout)) ++
        [((fun y ↦ eqEval oodPoint y), (0 : E))]).map (fun c ↦ c.1 x) =
      (ringSwitchClaim layout 0 (fun rP ↦ ringWeight ringPoint rP coeffs)).1 x ::
        ((claims.filter P).map (wOf layout x) ++ [wOf layout x out, eqEval oodPoint x]) := by
    simp [openedClaims, wOf, P]
  simp only [stackWeight]
  rw [← List.length_map (fun c : StackClaim ↦ c.1 x), hmap, stack_dot, List.length_map,
    filter_length_rank P claims, hrank _ le_rfl, hlen]
  have e : ∀ i ∈ range (poolRank Tables.nClaims),
      lam ^ (1 + i) * ((claims.filter P).map (wOf layout x)).getD i 0 =
        lam ^ (1 + i) * wOf layout x ((claims.filter P).getD i default) := by
    intro i hi
    have hi' : i < (claims.filter P).length := by
      rw [filter_length_rank P claims, hrank _ le_rfl, hlen]; exact mem_range.mp hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map,
      List.getD_eq_getElem _ _ hi']
  have hF := filter_pow_sum P (wOf layout x) lam claims 1
  rw [filter_length_rank P claims, hrank _ le_rfl, hlen] at hF
  have hsum : ∑ i ∈ range (poolRank Tables.nClaims),
      lam ^ (1 + i) * ((claims.filter P).map (wOf layout x)).getD i 0 =
      ∑ j ∈ range Tables.nClaims, if Tables.claimColumns.getD j 0 ∉ keccakOutputColumns then
        lam ^ (1 + poolRank j) * wOf layout x (claims.getD j default) else 0 := by
    rw [sum_congr rfl e, hF]
    refine sum_congr rfl fun j hj ↦ ?_
    have hj' := mem_range.mp hj
    simp only [P]
    rw [hcol j (by omega), hrank j (by omega)]
    simp only [decide_eq_true_eq]
  rw [hsum]

end
end LeanVM.Guest.B1.VerifySub
