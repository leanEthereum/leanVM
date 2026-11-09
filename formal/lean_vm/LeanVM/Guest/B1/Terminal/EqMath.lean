/-
  LeanVM.Guest.B1.Terminal.EqMath

  The equality weights `check_opening_terminal` multiplies, against the specification's
  `eqEval` on the stacked points.
-/

module

public import LeanVM.Guest.B1.Terminal.Interface
public import LeanVM.Guest.B1.Eq.Meaning

/-!
# Equality weights, factored

A claim's stacked point is its point followed by its block's offset bits (`stackPoint`), so its
equality weight at `x` is the point's against `x`'s first coordinates times the bits' against the
rest (`eqEval_append`). The bits' weight is `selProd o κ n x`, the product of `bitF` over bits
`κ .. κ + n` of `o` (`eqEval_sel`); the guest's selector computes it over the padded point
(`bitsEq_sel`, `selProd_pad`). A `q_keccak` lane's offset carries its slot's six bits above the
lane's `τ` (`selProd_lane`). The prefix chains are the points' weights (`prefixProd_eq`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier Finset

@[expose] public section

/-- The eq factor of a bit `b` against `z`: `z` at a one, `1 + z` at a zero. -/
def bitF (b : Bool) (z : E) : E := if b then z else 1 + z

/-- The eq weight of bits `κ .. κ + n` of `o` against the same coordinates of `x`. -/
def selProd (o κ n : ℕ) (x : List E) : E := ∏ i ∈ range n, bitF (o.testBit (κ + i)) (x.getD (κ + i) 0)

theorem foldl_mul_eq (a : E) : ∀ l : List E, l.foldl (· * ·) a = a * l.prod
  | [] => by simp
  | b :: l => by rw [List.foldl_cons, foldl_mul_eq _ l, List.prod_cons, mul_assoc]

theorem zipWith_prod (f : E → E → E) : ∀ l r : List E,
    (List.zipWith f l r).prod = ∏ i ∈ range (min l.length r.length), f (l.getD i 0) (r.getD i 0)
  | [], r => by simp
  | a :: l, [] => by simp
  | a :: l, b :: r => by
    rw [List.zipWith_cons_cons, List.prod_cons, zipWith_prod f l r, List.length_cons,
      List.length_cons, Nat.min_def, Nat.min_def]
    split <;> split
    · rw [prod_range_succ']; simp [mul_comm]
    · omega
    · omega
    · rw [prod_range_succ']; simp [mul_comm]

theorem eqEval_prod (l r : List E) :
    eqEval l r = ∏ i ∈ range (min l.length r.length), (1 + l.getD i 0 + r.getD i 0) := by
  rw [eqEval, foldl_mul_eq, one_mul, zipWith_prod]

theorem eqEval_append {p q xa xb : List E} (h : p.length = xa.length) :
    eqEval (p ++ q) (xa ++ xb) = eqEval p xa * eqEval q xb := by
  rw [eqEval, eqEval, eqEval, List.zipWith_append h, List.foldl_append, foldl_mul_eq _ (List.zipWith _ q xb),
    foldl_mul_eq 1 (List.zipWith _ p xa), one_mul, foldl_mul_eq 1, one_mul]

theorem shift_mod_two (o b : ℕ) : (o >>> b) % 2 = if o.testBit b then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (o >>> b) with h | h <;> simp [h]

theorem eOfNat_bit (o b : ℕ) (z : E) :
    1 + eOfNat ((o >>> b) % 2) + z = bitF (o.testBit b) z := by
  rw [shift_mod_two, bitF]
  split
  · rw [eOfNat_one, e_add_self, zero_add]
  · rw [eOfNat_zero, add_zero]

theorem selectorPoint_getD {o L k : ℕ} (hk : k < L) :
    (selectorPoint o L).getD k 0 = eOfNat ((o >>> k) % 2) := by
  rw [selectorPoint, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
    List.getElem_range]

theorem getD_drop' (l : List E) (κ i : ℕ) : (l.drop κ).getD i 0 = l.getD (κ + i) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **The bits' weight**: the offset bits of a stacked point against `x` above `κ`. -/
theorem eqEval_sel (o : ℕ) {L κ : ℕ} {x : List E} (hx : x.length = L) (hκ : κ ≤ L) :
    eqEval ((selectorPoint o L).drop κ) (x.drop κ) = selProd o κ (L - κ) x := by
  rw [eqEval_prod, selProd]
  simp only [List.length_drop, selectorPoint, List.length_map, List.length_range, hx, min_self]
  refine prod_congr rfl fun i hi ↦ ?_
  have hi' := mem_range.mp hi
  rw [getD_drop', getD_drop', ← selectorPoint, selectorPoint_getD (by omega), eOfNat_bit]

theorem padPoint_getD (x : List E) (i : ℕ) : (padPoint x).getD i 0 = x.getD i 0 := by
  unfold padPoint
  by_cases h : i < x.length
  · rw [List.getD_append _ _ _ _ h]
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), List.getElem?_eq_none (show x.length ≤ i by omega)]
    simp only [List.getElem?_replicate, Option.getD_none]
    split <;> rfl

theorem padPoint_length {x : List E} (h : x.length ≤ termPointCap) :
    (padPoint x).length = termPointCap := by
  simp [padPoint]; omega

/-- `bitsEq` over a list of bits and two coordinate lists, as a product. -/
theorem bitsEq_prod : ∀ (bs : List Bool) (zs zs1 : List E),
    Tables.bitsEq bs zs zs1 = ∏ i ∈ range (min bs.length (min zs.length zs1.length)),
      (if bs.getD i false then zs.getD i 0 else zs1.getD i 0)
  | [], zs, zs1 => by simp [Tables.bitsEq]
  | b :: bs, [], zs1 => by simp [Tables.bitsEq]
  | b :: bs, z :: zs, [] => by simp [Tables.bitsEq]
  | b :: bs, z :: zs, z1 :: zs1 => by
    have ih := bitsEq_prod bs zs zs1
    simp only [Tables.bitsEq, List.zip_cons_cons, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, List.length_cons, List.length_cons, List.length_cons,
      show min (bs.length + 1) (min (zs.length + 1) (zs1.length + 1)) =
        min bs.length (min zs.length zs1.length) + 1 by omega, prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [mul_comm]

theorem getD_take' {l : List E} {n k : ℕ} (h : k < n) : (l.take n).getD k 0 = l.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_map_one {l : List E} {k : ℕ} (h : k < l.length) :
    (l.map (1 + ·)).getD k 0 = 1 + l.getD k 0 := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map,
    List.getD_eq_getElem _ _ h]

/-- **The guest's selector** (`column_selector`, over the padded point and its complements) is
the bits' weight over bits `κ .. 28`. -/
theorem bitsEq_sel (o : ℕ) {κ : ℕ} (hκ : κ ≤ 28) {x : List E} (hx : x.length ≤ termPointCap) :
    Tables.bitsEq ((List.range (28 - κ)).map fun i ↦ o.testBit (κ + i))
        (((padPoint x).take 28).drop κ) ((((padPoint x).map (1 + ·)).take 28).drop κ) =
      selProd o κ (28 - κ) x := by
  have hp := padPoint_length hx
  rw [bitsEq_prod, selProd]
  simp only [List.length_map, List.length_range, List.length_drop, List.length_take, hp,
    termPointCap]
  rw [show min (28 - κ) (min (min 28 40 - κ) (min 28 40 - κ)) = 28 - κ by omega]
  refine prod_congr rfl fun i hi ↦ ?_
  have hi' := mem_range.mp hi
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range,
    getD_drop', getD_drop', getD_take' (by omega), getD_take' (by omega),
    getD_map_one (by rw [hp]; simp only [termPointCap]; omega), padPoint_getD]
  rfl

/-- Past the point's length the padded coordinates are `0` and the offset's bits are zero: the
selector's extra factors are `1`. -/
theorem selProd_pad {o κ L n : ℕ} {x : List E} (hx : x.length = L) (ho : o < 2 ^ L)
    (hκ : κ ≤ L) (hn : L ≤ κ + n) : selProd o κ n x = selProd o κ (L - κ) x := by
  unfold selProd
  rw [show n = (L - κ) + (n - (L - κ)) by omega, prod_range_add]
  have h2 : ∏ i ∈ range (n - (L - κ)),
      bitF (o.testBit (κ + (L - κ + i))) (x.getD (κ + (L - κ + i)) 0) = 1 := by
    refine prod_eq_one fun i _ ↦ ?_
    have hb : o.testBit (κ + (L - κ + i)) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hb, List.getD_eq_default _ _ (by omega), bitF]
    simp
  rw [h2, mul_one]

/-- **A prefix chain is the point's weight**: `seed = 1`, the words `as` and `bs = 1 + x`. -/
theorem prefixProd_eq {as bs x : List E} {n : ℕ} (ha : n ≤ as.length) (hb : n ≤ bs.length)
    (hx : n ≤ x.length) (hbx : ∀ i < n, bs.getD i 0 = 1 + x.getD i 0) :
    prefixProd 1 as bs n = eqEval (as.take n) (x.take n) := by
  rw [prefixProd, foldl_mul_eq, one_mul, zipWith_prod, eqEval_prod]
  simp only [List.length_take]
  rw [show min (min n as.length) (min n bs.length) = n by omega,
    show min (min n as.length) (min n x.length) = n by omega]
  refine prod_congr rfl fun i hi ↦ ?_
  have hi' := mem_range.mp hi
  rw [getD_take' hi', getD_take' hi', getD_take' hi', hbx i hi']
  ring

/-- The ring switch's weight reads `1 + point1 = x` on `q_keccak`'s coordinates. -/
theorem map_one_take {x : List E} {n : ℕ} (hn : n ≤ x.length) :
    (((padPoint x).map (1 + ·)).take n).map (1 + ·) = x.take n := by
  have hp : n ≤ (padPoint x).length := by simp [padPoint]; omega
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_take]
  rw [← add_assoc, e_add_self, zero_add]
  have := padPoint_getD x i
  rw [List.getD_eq_getElem _ _ (by simp at h1; omega),
    List.getD_eq_getElem _ _ (by simp at h2; omega)] at this
  exact this

/-- **A `q_keccak` lane's bits**: its offset `oq + s·2^τ`, `oq` a multiple of `2^(τ + 6)`, carries
the slot `s`'s six bits above `τ`, then `oq`'s. -/
theorem selProd_lane {oq s τ n : ℕ} (hq : 2 ^ (τ + 6) ∣ oq) (hs : s < 64) (hn : 6 ≤ n)
    (x : List E) :
    selProd (oq + s * 2 ^ τ) τ n x =
      (∏ i ∈ range 6, bitF (s.testBit i) (x.getD (τ + i) 0)) * selProd oq (τ + 6) (n - 6) x := by
  obtain ⟨q, rfl⟩ := hq
  have hT : ∀ m i, (2 ^ τ * m).testBit (τ + i) = m.testBit i := by
    intro m i; rw [Nat.testBit_two_pow_mul]; simp
  have e1 : 2 ^ (τ + 6) * q + s * 2 ^ τ = 2 ^ τ * (2 ^ 6 * q + s) := by ring
  have e2 : 2 ^ (τ + 6) * q = 2 ^ τ * (2 ^ 6 * q) := by ring
  unfold selProd
  rw [show n = 6 + (n - 6) by omega, prod_range_add, show 6 + (n - 6) - 6 = n - 6 by omega]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine prod_congr rfl fun i hi ↦ ?_
    have hi' := mem_range.mp hi
    rw [e1, hT, Nat.testBit_two_pow_mul_add _ hs]
    simp only [hi', ↓reduceIte]
  · refine prod_congr rfl fun i _ ↦ ?_
    rw [e1, e2, show τ + 6 + i = τ + (6 + i) by omega, hT, hT,
      Nat.testBit_two_pow_mul_add _ hs, Nat.testBit_two_pow_mul]
    simp

/-- **The public input's chain is its point's weight**: `(rm, 0, …, 0)` against `x`. -/
theorem piChain_eq {rm : E} {x : List E} {m : ℕ} (h1 : 1 ≤ m) (hm : m ≤ x.length) :
    (rm + (1 + x.getD 0 0)) * ∏ i ∈ Ico 1 m, (1 + x.getD i 0) =
      eqEval (rm :: List.replicate (m - 1) 0) (x.take m) := by
  rw [eqEval_prod]
  simp only [List.length_cons, List.length_replicate, List.length_take]
  rw [show min (m - 1 + 1) (min m x.length) = m by omega,
    show m = 1 + (m - 1) by omega, prod_range_add, prod_range_one, Finset.prod_Ico_eq_prod_range,
    show 1 + (m - 1) - 1 = m - 1 by omega]
  refine congrArg₂ (· * ·) ?_ ?_
  · rw [getD_take' (by omega)]; simp only [List.getD_cons_zero]; ring
  · refine prod_congr rfl fun i hi ↦ ?_
    have hi' := mem_range.mp hi
    rw [getD_take' (by omega), add_comm 1 i, List.getD_cons_succ]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> simp

end
end LeanVM.Guest.B1.VerifySub
