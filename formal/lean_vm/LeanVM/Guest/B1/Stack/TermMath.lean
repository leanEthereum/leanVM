/-
  LeanVM.Guest.B1.Stack.TermMath

  The terminal's arithmetic: a stacked claim's weight as the products the guest builds.
-/

module

public import LeanVM.Guest.B1.Stack.Interface
public import LeanVM.Guest.B1.Eq.MeaningP
public import LeanVM.Protocol.Tables
public import LeanVM.Protocol.RingVerifier

/-!
# The terminal's arithmetic

* `eqEval_append`, `selectorPoint_split`: `eq` splits along a point's parts, a selector point along
  its bits;
* `stackPoint_eqEval`: a column claim's weight is `eq` over the column's own coordinates times its
  placement's `eqAbove`;
* `slot_eqAbove`: a `q_keccak` slot's `eqAbove` is the slot's `eq` weight over the six coordinates
  above the slot times `q_keccak`'s;
* `prefixProd_eq`, `ringRow_eq`: the guest's prefix products and ring rows at `x`, from `1 + x`;
* `frobenius_getD`: the Frobenius powers;
* `dot_powers_cons`: a batch by the powers of `λ`, by Horner.
-/

namespace LeanVM.Guest.B1.Stack

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `eq` and selector points -/

theorem eqEval_append {a b : List E} (c d : List E) (h : a.length = b.length) :
    eqEval (a ++ c) (b ++ d) = eqEval a b * eqEval c d := by
  rw [Ring.eqEval_eq_prod, Ring.eqEval_eq_prod, Ring.eqEval_eq_prod, List.zipWith_append h,
    List.prod_append]

theorem shr_mod_two (x i : ℕ) : (x >>> i) % 2 = if x.testBit i then 1 else 0 := by
  unfold Nat.testBit
  rw [Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (x >>> i) with h | h <;> simp [h]

theorem selectorPoint_split (s A m n : ℕ) (hs : s < 2 ^ m) :
    selectorPoint (2 ^ m * A + s) (m + n) = selectorPoint s m ++ selectorPoint A n := by
  unfold selectorPoint
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  · refine List.map_congr_left fun i hi ↦ ?_
    have hi := List.mem_range.1 hi
    rw [shr_mod_two, shr_mod_two, Nat.testBit_two_pow_mul_add _ hs]
    simp [hi]
  · refine List.map_congr_left fun i _ ↦ ?_
    simp only [Function.comp]
    rw [shr_mod_two, shr_mod_two, Nat.testBit_two_pow_mul_add _ hs]
    simp

theorem selectorPoint_length (s n : ℕ) : (selectorPoint s n).length = n := by simp [selectorPoint]

theorem selectorPoint_eq_boolPoint (s n : ℕ) : selectorPoint s n = Tables.boolPoint n s := by
  unfold selectorPoint Tables.boolPoint
  refine List.map_congr_left fun i _ ↦ ?_
  rw [shr_mod_two]
  split_ifs
  · exact Value.eOfNat_one
  · exact Value.eOfNat_zero

/-- **A column claim's weight**: `eq` of the point over the column's coordinates, times `eqAbove`. -/
theorem stackPoint_eqEval (p : Placement) {pt x : List E} (hpt : pt.length = p.variableCount)
    (hx : p.variableCount ≤ x.length) :
    eqEval (p.stackPoint pt x.length) x = eqEval pt (x.take p.variableCount) * p.eqAbove x := by
  rw [Placement.stackPoint]
  conv_lhs => arg 2; rw [← List.take_append_drop p.variableCount x]
  rw [eqEval_append _ _ (by simp [hpt]; omega), Placement.eqAbove]

/-- **A `q_keccak` slot's `eqAbove`**: in `q_keccak`'s block (`h + 6` coordinates, aligned), slot
`s`'s is the slot's `eq` weight at the six coordinates from `h`, times `q_keccak`'s. -/
theorem slot_eqAbove {h I s : ℕ} {x : List E} (hal : 2 ^ (h + 6) ∣ I) (hs : s < 64)
    (hx : h + 6 ≤ x.length) :
    ({ variableCount := h, index := I + (s <<< h) } : Placement).eqAbove x =
      (eqKernel ((x.drop h).take 6)).getD s 0 *
        ({ variableCount := h + 6, index := I } : Placement).eqAbove x := by
  obtain ⟨A, rfl⟩ := hal
  unfold Placement.eqAbove
  simp only
  have hsh : (2 ^ (h + 6) * A + (s <<< h)) >>> h = 2 ^ 6 * A + s := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, pow_add,
      show 2 ^ h * 2 ^ 6 * A + s * 2 ^ h = 2 ^ h * (2 ^ 6 * A + s) by ring,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hsh' : (2 ^ (h + 6) * A) >>> (h + 6) = A := by
    rw [Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel_left _ (by positivity)]
  rw [hsh, hsh', show x.length - h = 6 + (x.length - (h + 6)) by omega,
    selectorPoint_split _ _ _ _ (by norm_num; omega)]
  conv_lhs => rw [← List.take_append_drop 6 (x.drop h)]
  rw [eqEval_append _ _ (by simp [selectorPoint_length]; omega), List.drop_drop]
  congr 1
  rw [Tables.getD_eqKernel _ _ (by
      rw [List.length_take, List.length_drop, show min 6 (x.length - h) = 6 by omega]; norm_num; omega),
    selectorPoint_eq_boolPoint]
  congr 2
  simp; omega

/-! ## The guest's products -/

theorem zipWith_one_add (l r : List E) :
    List.zipWith (· + ·) l (r.map (1 + ·)) = List.zipWith (fun a y ↦ 1 + a + y) l r := by
  rw [List.zipWith_map_right]
  congr 1
  funext a y
  ring

/-- **A prefix product at `x`**, from the words `1 + x`. -/
theorem prefixProd_eq (as x pad : List E) {n : ℕ} (hn : n ≤ x.length) :
    prefixProd 1 as (x.map (1 + ·) ++ pad) n = eqEval (as.take n) (x.take n) := by
  rw [prefixProd, List.take_append_of_le_length (by simpa using hn), ← List.map_take,
    zipWith_one_add, eqEval]

/-- **A ring row at `x`**: `c` times `eq` of the coordinates' `2^k`-th powers. -/
theorem ringRow_eq (c : E) (zs ys : List E) (k : ℕ) :
    ringRow c zs (ys.map (1 + ·)) k = c * eqEval (zs.map (· ^ 2 ^ k)) ys := by
  unfold ringRow
  induction zs generalizing ys c with
  | nil => simp [eqEval]
  | cons z zs ih =>
    cases ys with
    | nil => simp [eqEval]
    | cons y ys =>
      rw [List.map_cons, List.zipWith_cons_cons, List.foldl_cons, ih, List.map_cons,
        Ring.eqEval_eq_prod, Ring.eqEval_eq_prod, List.zipWith_cons_cons, List.prod_cons]
      ring

/-! ## Frobenius powers -/

theorem frobenius_fold (v : E) : ∀ (n : ℕ) (l : List E) (w : E),
    (List.range n).foldl (fun (acc : List E × E) _ ↦ (acc.1 ++ [acc.2], acc.2 * acc.2)) (l, w) =
      (l ++ (List.range n).map (fun i ↦ w ^ 2 ^ i), w ^ 2 ^ n)
  | 0, l, w => by simp
  | n + 1, l, w => by
    rw [List.range_succ, List.foldl_append, frobenius_fold v n l w]
    simp only [List.foldl_cons, List.foldl_nil, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, Prod.mk.injEq, true_and]
    rw [← pow_two, ← pow_mul, pow_succ]

theorem frobenius_eq (v : E) : Verifier.frobenius v = (List.range kBits).map (fun i ↦ v ^ 2 ^ i) := by
  unfold Verifier.frobenius
  rw [frobenius_fold v kBits [] v, List.nil_append]

theorem frobenius_getD (v : E) {k : ℕ} (hk : k < kBits) : (Verifier.frobenius v).getD k 0 = v ^ 2 ^ k := by
  rw [frobenius_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  simp

/-! ## Horner -/

theorem powersFrom_eq (acc base : E) : ∀ n, powersFrom acc base n = (powersFrom 1 base n).map (acc * ·)
  | 0 => by simp [powersFrom]
  | n + 1 => by
    simp only [powersFrom, List.map_cons, mul_one]
    rw [powersFrom_eq (acc * base) base n, powersFrom_eq (1 * base) base n, List.map_map,
      List.cons.injEq]
    refine ⟨rfl, List.map_congr_left fun y _ ↦ ?_⟩
    simp only [Function.comp, one_mul, mul_assoc]

theorem dot_map_mul_left (c : E) : ∀ (a b : List E), dot (a.map (c * ·)) b = c * dot a b
  | [], _ => by simp [dot]
  | _ :: _, [] => by simp [dot]
  | a :: as, b :: bs => by
    rw [List.map_cons, Tables.dot_cons, Tables.dot_cons, dot_map_mul_left c as bs]
    ring

/-- **A batch by Horner**: `Σ λ^i a_i = a_0 + λ Σ λ^i a_(i+1)`. -/
theorem dot_powers_cons (lam a : E) (l : List E) :
    dot (powers lam (l.length + 1)) (a :: l) = a + lam * dot (powers lam l.length) l := by
  simp only [powers, powersFrom]
  rw [Tables.dot_cons, powersFrom_eq, one_mul, dot_map_mul_left, one_mul]

end
end LeanVM.Guest.B1.Stack
