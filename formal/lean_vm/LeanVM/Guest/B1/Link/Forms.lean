/-
  LeanVM.Guest.B1.Link.Forms

  The link's in-circuit forms (`verify_sub`'s link section and its callees) are the Statement's
  (`verifyLink`, `Statement/Verifier/Link.lean`).
-/

module

public import Statement.Verifier.Lib
public import LeanVM.Facts.Hotwire
import LeanVM.Parameters.Field
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.List.GetD

/-!
# The link's forms in the circuit

The guest (`guests/lean_ethereum.py`, G below) computes the link's terms by its own loops, over
field elements; the Statement by `link.rs`'s. Each guest form is defined here as G's loop, over
lists of field elements, and proved equal to the Statement's form:

* `state_ends`: `endsProd (bitsE n w) zs = linkEqAt zs n` (`linkEqAt_eq_endsProd`), and
  `prodE (zs.map (1 + ·)) = linkEqAt zs 0`;
* `index_side`: `sideFold zs rs` is `(eqEval zs rs, linkShiftEq zs rs)` (`sideFold_eq`), and the
  suffix products `belowE` are the Statement's `below`;
* `table_point`: from the complement bits of a row count `rows ≤ 2^h` and its bit `h`,
  `tpTotal` is `prefixSum` (`omegaAt_eq_tp`), `tpPad` is `lessThan`'s (`lessThan_eq_tp`), and
  `tpFull` is `eqEval` (`eqEval_eq_tpFull`).

`bitE n k`, bit `k` of `n` as `0` or `1` in `E`; `cbitE`, its complement `1 + bitE n k`, which
`table_size` hints.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Hotwire

@[expose] public section

/-! ## Products and sums -/

theorem foldl_mul_eq (l : List E) (a : E) : l.foldl (· * ·) a = a * prodE l := by
  induction l generalizing a with
  | nil => simp [prodE]
  | cons x l ih =>
    simp only [List.foldl_cons, prodE]
    rw [ih, ih (1 * x)]
    ring

theorem prodE_nil : prodE [] = 1 := rfl

theorem prodE_cons (x : E) (l : List E) : prodE (x :: l) = x * prodE l := by
  rw [prodE, List.foldl_cons, foldl_mul_eq]
  ring

theorem prodE_append (a b : List E) : prodE (a ++ b) = prodE a * prodE b := by
  rw [prodE, List.foldl_append, foldl_mul_eq]
  rfl

theorem foldl_add_eq (l : List E) (a : E) : l.foldl (· + ·) a = a + sumE l := by
  induction l generalizing a with
  | nil => simp [sumE]
  | cons x l ih =>
    simp only [List.foldl_cons, sumE]
    rw [ih, ih (0 + x)]
    ring

theorem sumE_nil : sumE [] = 0 := rfl

theorem sumE_cons (x : E) (l : List E) : sumE (x :: l) = x + sumE l := by
  rw [sumE, List.foldl_cons, foldl_add_eq]
  ring

theorem sumE_append (a b : List E) : sumE (a ++ b) = sumE a + sumE b := by
  rw [sumE, List.foldl_append, foldl_add_eq]
  rfl

theorem two_eq_zero_E : (2 : E) = 0 := CharTwo.two_eq_zero

theorem add_self_E (x : E) : x + x = 0 := by
  linear_combination x * two_eq_zero_E

/-! ## Bits -/

/-- Bit `k` of `n`, `0` or `1` in `E`. -/
def bitE (n k : ℕ) : E := eOfNat ((n >>> k) % 2)

theorem bitE_eq (n k : ℕ) : bitE n k = if (n >>> k) % 2 = 1 then 1 else 0 :=
  eOfNat_mod_two _

theorem bitE_zero (n : ℕ) : bitE n 0 = if n % 2 = 1 then 1 else 0 := by
  rw [bitE_eq, Nat.shiftRight_zero]

theorem bitE_succ (n k : ℕ) : bitE n (k + 1) = bitE (n / 2) k := by
  rw [bitE, bitE, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
    pow_succ']

/-- `n`'s first `w` bits, low first. -/
def bitsE (n w : ℕ) : List E := (List.range w).map (bitE n)

theorem bitsE_length (n w : ℕ) : (bitsE n w).length = w := by simp [bitsE]

theorem bitsE_succ (n w : ℕ) : bitsE n (w + 1) = bitE n 0 :: bitsE (n / 2) w := by
  rw [bitsE, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  rw [bitsE]
  exact List.map_congr_left fun k _ ↦ bitE_succ n k

theorem bitsE_zero (n : ℕ) : bitsE n 0 = [] := rfl

/-! ## `state_ends`: `eq(ζ, 0)` and `eq(ζ, cycles)` -/

/-- `state_ends`' second fold: `Π (1 + c_k + z_k)`, left to right. -/
def endsProd (cs zs : List E) : E := prodE (List.zipWith (fun c z ↦ 1 + c + z) cs zs)

theorem endsProd_cons (c z : E) (cs zs : List E) :
    endsProd (c :: cs) (z :: zs) = (1 + c + z) * endsProd cs zs := by
  rw [endsProd, List.zipWith_cons_cons, prodE_cons, endsProd]

/-- **`Π (1 + bit_k(n) + z_k)` is `eq(ζ, n)`.** -/
theorem endsProd_bitsE : ∀ (zs : List E) (n : ℕ), endsProd (bitsE n zs.length) zs = eqAt zs n
  | [], n => rfl
  | z :: zs, n => by
    rw [List.length_cons, bitsE_succ, endsProd_cons, endsProd_bitsE zs (n / 2),
      eqAt_cons_of_charTwo, bitE_zero]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · simp [h]
    · simp only [h, ↓reduceIte]
      rw [show (1 + 1 + z : E) = z by linear_combination two_eq_zero_E]

/-- **`state_ends`' second end** is the Statement's `eq_at(ζ, n)`. -/
theorem linkEqAt_eq_endsProd (zs : List E) (n : ℕ) :
    linkEqAt zs n = endsProd (bitsE n zs.length) zs := by
  rw [endsProd_bitsE, linkEqAt, linkEqAt_eq]

/-- `Π (1 + z_k)` is `endsProd` at zero bits. -/
theorem prodE_one_add_eq_endsProd : ∀ zs : List E,
    prodE (zs.map (1 + ·)) = endsProd (bitsE 0 zs.length) zs
  | [] => rfl
  | z :: zs => by
    rw [List.map_cons, prodE_cons, List.length_cons, bitsE_succ, endsProd_cons,
      prodE_one_add_eq_endsProd zs, bitE_zero]
    simp

/-- **`state_ends`' first end** is the Statement's `eq_at(ζ, 0)`. -/
theorem linkEqAt_zero_eq (zs : List E) : linkEqAt zs 0 = prodE (zs.map (1 + ·)) := by
  rw [linkEqAt_eq_endsProd, prodE_one_add_eq_endsProd]

/-! ## `index_side`: `eq(ζ, r)` and its shift -/

/-- `index_side`'s step over `(z, x)`: `(eq, shift, carry)`, as G updates them. -/
def sideStep (acc : E × E × E) (zx : E × E) : E × E × E :=
  (acc.1 * (1 + zx.1 + zx.2), acc.2.1 * (1 + zx.1 + zx.2) + acc.2.2 * (1 + zx.2) * zx.1,
    acc.2.2 * zx.2 * (1 + zx.1))

/-- `index_side`'s fold from `(1, 0, 1)`. -/
def sideFold (zs rs : List E) : E × E × E := (zs.zip rs).foldl sideStep (1, 0, 1)

theorem sideFold_fst_aux : ∀ (l : List (E × E)) (acc : E × E × E),
    (l.foldl sideStep acc).1 = acc.1 * (l.map fun zx ↦ 1 + zx.1 + zx.2).foldl (· * ·) 1
  | [], acc => by simp
  | zx :: l, acc => by
    rw [List.foldl_cons, sideFold_fst_aux l, List.map_cons, List.foldl_cons, foldl_mul_eq,
      foldl_mul_eq (l.map _) (1 * _)]
    simp only [sideStep]
    ring

theorem sideFold_snd_aux : ∀ (l : List (E × E)) (a : E × E × E) (b : E × E),
    a.2 = b → (l.foldl sideStep a).2.1 = (l.foldl (fun acc zx ↦ (acc.1 * (1 + zx.1 + zx.2) +
      acc.2 * (1 + zx.2) * zx.1, acc.2 * (zx.2 * (1 + zx.1)))) b).1
  | [], a, b, h => by simp [h]
  | zx :: l, a, b, h => by
    rw [List.foldl_cons, List.foldl_cons]
    refine sideFold_snd_aux l _ _ ?_
    subst h
    simp only [sideStep, Prod.mk.injEq]
    exact ⟨trivial, by ring⟩

/-- **`index_side`'s fold** is `(eq_eval(ζ, r), shift_eq(ζ, r))`. -/
theorem zipWith_eq_map_zip' {α β γ : Type} (f : α → β → γ) : ∀ (a : List α) (b : List β),
    List.zipWith f a b = (a.zip b).map fun p ↦ f p.1 p.2
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: a, y :: b => by
    rw [List.zipWith_cons_cons, List.zip_cons_cons, List.map_cons, zipWith_eq_map_zip' f a b]

theorem sideFold_eq (zs rs : List E) :
    (sideFold zs rs).1 = eqEval zs rs ∧ (sideFold zs rs).2.1 = linkShiftEq zs rs := by
  refine ⟨?_, ?_⟩
  · rw [sideFold, sideFold_fst_aux, one_mul, eqEval, zipWith_eq_map_zip']
  · exact sideFold_snd_aux _ _ _ rfl

/-- `Π_{k ≤ i < |r|} (1 + r_i)`: link's `below k`, G's `below[k]`. -/
def belowE (rs : List E) (k : ℕ) : E := prodE ((rs.drop k).map (1 + ·))

/-! ## `table_point`: the row weight, `LT_rows` and `eq(τ, χ)` -/

/-- `table_point`'s `pad` fold over `(c, x)`, `c` a complement bit. -/
def tpPad (cs xs : List E) : E :=
  (cs.zip xs).foldl (fun pad cx ↦ cx.1 * cx.2 + (cx.1 + cx.2) * pad) 1

/-- The complement of bit `k` of `n`, `1` or `0` in `E`: what `table_size` hints below bit `h`. -/
def cbitE (n k : ℕ) : E := 1 + bitE n k

/-- `n`'s first `w` complement bits. -/
def cbitsE (n w : ℕ) : List E := (List.range w).map (cbitE n)

theorem cbitsE_length (n w : ℕ) : (cbitsE n w).length = w := by simp [cbitsE]

theorem cbitsE_succ (n w : ℕ) : cbitsE n (w + 1) = cbitE n 0 :: cbitsE (n / 2) w := by
  rw [cbitsE, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  rw [cbitsE]
  exact List.map_congr_left fun k _ ↦ by simp only [Function.comp, cbitE, bitE_succ]

theorem zip_cbitsE_eq (n : ℕ) (xs : List E) :
    (cbitsE n xs.length).zip xs = xs.zipIdx.map fun p ↦ (1 + bitE n p.2, p.1) := by
  apply List.ext_getElem
  · simp [cbitsE]
  · intro i h1 h2
    simp [cbitsE, cbitE, List.getElem_zipIdx]

theorem tpPad_eq (n : ℕ) (xs : List E) :
    tpPad (cbitsE n xs.length) xs = xs.zipIdx.foldl (fun pad (r, k) ↦
      let b := eOfNat ((n >>> k) % 2)
      (1 + b) * r + (1 + b + r) * pad) 1 := by
  rw [tpPad, zip_cbitsE_eq, List.foldl_map]
  rfl

/-- **`table_point`'s second return** is `LT_rows(χ)`: from the complement bits of `rows` below
`h` and its bit `h`. -/
theorem lessThan_eq_tp (n : ℕ) (xs : List E) :
    lessThan xs n = 1 + (1 + bitE n xs.length) * tpPad (cbitsE n xs.length) xs := by
  rw [lessThan, paddingWeight, tpPad_eq]
  rfl

/-- `table_point`'s `full[h]`: `Π_{k < h} (1 + t_k + x_k)`. -/
def tpFull (ts xs : List E) : E := prodE (List.zipWith (fun t x ↦ 1 + t + x) ts xs)

theorem eqEval_eq_tpFull (ts xs : List E) : eqEval ts xs = tpFull ts xs := rfl

/-- `table_point`'s walk from the top, coordinate `j` (`h - 1` down to `0`): `low_j`, `high_j`,
`full_j` and the bit `b_j = 1 + c_j`, on the running total and prefix. -/
def tpStep (low high full b : ℕ → E) (acc : E × E) (j : ℕ) : E × E :=
  (acc.1 + b j * acc.2 * low j * full j, acc.2 * (low j + b j * (high j + low j)))

/-- `table_point`'s total before `θ`: `top·full_h`, then the walk. -/
def tpTotal (low high full b : ℕ → E) (top : E) (h : ℕ) : E :=
  ((List.range h).reverse.foldl (tpStep low high full b) (top * full h, 1)).1

/-- The Statement's walk (`prefixSum`'s `else` branch), generalized to an initial total. -/
def psWalk (low high full : ℕ → E) (n : ℕ) (acc : E × E) (l : List ℕ) : E × E :=
  l.foldl (fun (acc : E × E) h ↦
    if n >>> h % 2 = 1 then (acc.1 + acc.2 * low h * full h, acc.2 * high h)
    else (acc.1, acc.2 * low h)) acc

theorem tpStep_eq (low high full : ℕ → E) (n : ℕ) :
    tpStep low high full (bitE n) = fun (acc : E × E) h ↦
      if n >>> h % 2 = 1 then (acc.1 + acc.2 * low h * full h, acc.2 * high h)
      else (acc.1, acc.2 * low h) := by
  funext acc j
  simp only [tpStep, bitE_eq]
  split_ifs
  · refine Prod.ext ?_ ?_
    · simp only [one_mul]
    · simp only [one_mul]
      linear_combination (acc.2 * low j) * two_eq_zero_E
  · refine Prod.ext ?_ ?_ <;> simp

theorem tpStep_fold_eq (low high full : ℕ → E) (n : ℕ) (l : List ℕ) (acc : E × E) :
    l.foldl (tpStep low high full (bitE n)) acc = psWalk low high full n acc l := by
  rw [tpStep_eq]
  rfl

/-- The walk's bits below `j` are zero: nothing added, the prefix multiplied by the lows. -/
theorem psWalk_zero_bits (low high full : ℕ → E) (n : ℕ) : ∀ (l : List ℕ) (acc : E × E),
    (∀ j ∈ l, n >>> j % 2 = 0) → (psWalk low high full n acc l).1 = acc.1
  | [], _, _ => rfl
  | j :: l, acc, h => by
    rw [psWalk, List.foldl_cons, ← psWalk, psWalk_zero_bits low high full n l _
      fun i hi ↦ h i (List.mem_cons_of_mem j hi)]
    rw [h j List.mem_cons_self]
    simp

/-- `prefixSum`'s `full` list. -/
def psFull (low high : List E) : List E :=
  (List.range low.length).foldl
    (fun acc h ↦ acc ++ [acc.getD h 0 * (low.getD h 0 + high.getD h 0)]) [(1 : E)]

theorem psFull_aux (low high : List E) : ∀ k, k ≤ low.length →
    ((List.range k).foldl (fun acc h ↦ acc ++ [acc.getD h 0 * (low.getD h 0 + high.getD h 0)])
        [(1 : E)]).length = k + 1 ∧
      ∀ j ≤ k, ((List.range k).foldl (fun acc h ↦ acc ++ [acc.getD h 0 * (low.getD h 0 +
        high.getD h 0)]) [(1 : E)]).getD j 0 =
        prodE ((List.range j).map fun i ↦ low.getD i 0 + high.getD i 0)
  | 0, _ => ⟨rfl, fun j hj ↦ by obtain rfl : j = 0 := by omega
                                rfl⟩
  | k + 1, hk => by
    obtain ⟨hl, hv⟩ := psFull_aux low high k (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [List.length_append, hl]; rfl, fun j hj ↦ ?_⟩
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · rw [List.getD_append _ _ _ _ (by omega), hv j (by omega)]
    · obtain rfl : j = k + 1 := by omega
      rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self, List.getD_cons_zero,
        hv k le_rfl, List.range_succ, List.map_append, prodE_append]
      simp [prodE_cons, prodE_nil]

/-- **`table_point`'s total is `prefix_sum`**, from the bits of `n ≤ 2^h`: `top` its bit `h`,
`b` its bits below. -/
theorem prefixSum_eq_tp (low high : List E) (n : ℕ) (hn : n ≤ 2 ^ low.length) :
    prefixSum low high n = tpTotal (low.getD · 0) (high.getD · 0)
      (fun j ↦ prodE ((List.range j).map fun i ↦ low.getD i 0 + high.getD i 0)) (bitE n)
      (bitE n low.length) low.length := by
  have hfull := psFull_aux low high low.length le_rfl
  unfold prefixSum
  simp only
  rw [tpTotal, tpStep_fold_eq]
  split_ifs with hge
  · -- `n = 2^h`: the top bit, no bit below
    obtain rfl : n = 2 ^ low.length := le_antisymm hn hge
    have hz : ∀ j ∈ (List.range low.length).reverse, 2 ^ low.length >>> j % 2 = 0 := by
      intro j hj
      have hj' : j < low.length := List.mem_range.mp (List.mem_reverse.mp hj)
      rw [Nat.shiftRight_eq_div_pow, Nat.pow_div hj'.le (by norm_num),
        show low.length - j = (low.length - j - 1) + 1 by omega, pow_succ, Nat.mul_mod_left]
    rw [hfull.2 _ le_rfl, psWalk_zero_bits _ _ _ _ _ _ hz, bitE_eq]
    simp [Nat.shiftRight_eq_div_pow, Nat.div_self (Nat.two_pow_pos _)]
  · -- `n < 2^h`: bit `h` is zero, the walk is the Statement's
    have hlt : n < 2 ^ low.length := by omega
    have htop : bitE n low.length = 0 := by
      rw [bitE_eq, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]
      simp
    rw [htop, zero_mul, psWalk]
    refine congrArg Prod.fst (List.foldl_ext _ _ _ fun acc j hj ↦ ?_)
    have hj' : j < low.length := List.mem_range.mp (List.mem_reverse.mp hj)
    rw [hfull.2 j hj'.le]

end
end LeanVM.Guest.B1.Link
