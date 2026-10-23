/-
  LeanVM.Protocol.EndToEnd.Front.BusPadding

  The verifier's `padding_weight` is the multilinear extension of the padding rows' indicator, the
  weight the bus phase gives a table block's padding term.
-/

module

public import LeanVM.Protocol.Bus

/-!
# The padding weight

The verifier (`python-verifier/verifier.py:270-276` at leanVM
`3a37fb6e1c7423e36b67d1cac4eda70c3ad4dd45`) computes `pad_n(point)`, the multilinear extension
of `[x ≥ n]` on the cube of `point`'s length, in one pass from the low bit (`paddingWeight`);
the bus phase writes it as the extension of the indicator table (`Bus.padWeight`). They agree for
every `n ≤ 2^|point|` (`paddingWeight_eq_padWeight`), which is `doc/leanvm` Lemma `lem:suffix`:

* `padWeight_append`: adding a top coordinate `r` splits the cube on its top bit,
  `pad_n(z, r) = (1 − r)·pad_n(z) + r·pad_{n − 2^m}(z)`, for every `n`;
* `foldPad_eq`: after the first `m` coordinates, the verifier's running value is
  `pad_{n mod 2^m}` of them, each step being the split above at the bit `n_m`;
* the last factor `1 + n_m` is `1` when `n < 2^m`, and `0` when `n = 2^m`, where every row is
  executed and `pad_{2^m} = 0`.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol CompPoly CMlPolynomialEval

@[expose] public section

/-- `E(0)` is zero. -/
private theorem eOfNat_zero' : eOfNat 0 = 0 := by
  unfold eOfNat
  rw [show K.ofBits 0 = 0 by decide +kernel]
  simp

/-- `E(1)` is one. -/
private theorem eOfNat_one' : eOfNat 1 = 1 := by
  unfold eOfNat
  rw [show K.ofBits 1 = 1 by decide +kernel]
  simp

/-- `1 + 1 = 0` in `E`. -/
private theorem one_add_one' : (1 : E) + 1 = 0 := by
  rw [one_add_one_eq_two]
  exact CharTwo.two_eq_zero

/-- Nothing lies above every row: no row of `2^m` is at least `2^m`. -/
theorem padWeight_of_le {m n : ℕ} (z : Vector E m) (h : 2 ^ m ≤ n) : Bus.padWeight n z = 0 := by
  rw [Bus.padWeight, evalMle_eq_sum]
  refine Finset.sum_eq_zero fun x _ ↦ ?_
  have : ¬ n ≤ x.val := by have := x.isLt; omega
  simp [this]

/-- Every row lies above `0`. -/
theorem padWeight_zero {m : ℕ} (z : Vector E m) : Bus.padWeight 0 z = 1 := by
  rw [Bus.padWeight, show (Vector.ofFn fun x : Fin (2 ^ m) ↦
    if 0 ≤ x.val then (1 : E) else 0) = Vector.replicate (2 ^ m) 1 from
    Vector.ext fun i hi ↦ by simp]
  exact evalMle_replicate 1 z

/-- **Splitting on the top bit** (Lemma `lem:suffix`): with a top coordinate `r`, the rows above
`n` are those of the lower half above `n`, at weight `1 − r`, and those of the upper half above
`n − 2^m`, at weight `r`. -/
theorem padWeight_append {m : ℕ} (n : ℕ) (z : Vector E m) (r : E) :
    Bus.padWeight n (z ++ #v[r]) = (1 - r) * Bus.padWeight n z + r * Bus.padWeight (n - 2 ^ m) z := by
  have h2 : ∀ f : Fin (2 ^ 1) → E, ∑ j, f j = f 0 + f 1 := fun f ↦ Fin.sum_univ_two f
  rw [Bus.padWeight, evalMle_split, h2]
  have hl0 : (lagrangeBasis #v[r])[(0 : Fin (2 ^ 1))] = 1 - r := by
    rw [Fin.getElem_fin, lagrangeBasis_getElem_nat _ (by norm_num)]
    simp
  have hl1 : (lagrangeBasis #v[r])[(1 : Fin (2 ^ 1))] = r := by
    rw [Fin.getElem_fin, lagrangeBasis_getElem_nat _ (by norm_num)]
    simp
  rw [hl0, hl1]
  congr 2
  · refine congrArg (evalMle · z) (Vector.ext fun i hi ↦ ?_)
    simp [slice]
  · refine congrArg (evalMle · z) (Vector.ext fun i hi ↦ ?_)
    rw [slice_getElem_nat _ _ hi, Vector.getElem_ofFn, Vector.getElem_ofFn]
    have h1 : ((1 : Fin (2 ^ 1)) : ℕ) = 1 := rfl
    have : n ≤ i + 2 ^ m * ((1 : Fin (2 ^ 1)) : ℕ) ↔ n - 2 ^ m ≤ i := by
      rw [h1]
      omega
    simp only [this]

/-- The verifier's running value after the coordinates `l`: its loop, from `1`. -/
def foldPad (l : List E) (n : ℕ) : E :=
  l.zipIdx.foldl (fun pad (r, k) ↦
    let b := eOfNat ((n >>> k) % 2)
    (1 + b) * r + (1 + b + r) * pad) 1

/-- A point as a vector of its own length. -/
abbrev vecList (l : List E) : Vector E l.length := Vector.ofFn fun i ↦ l.getD i 0

private theorem vecList_append (l : List E) (r : E) :
    vecList (l ++ [r]) = Vector.cast (by simp) (vecList l ++ #v[r]) := by
  apply Vector.ext
  intro k hk
  simp only [vecList, Vector.getElem_ofFn, Vector.getElem_cast, Vector.getElem_append]
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · have hk' : k = l.length := by simp at hk; omega
    subst hk'
    simp [List.getD_eq_getElem?_getD]

theorem padWeight_cast {m m' : ℕ} (h : m = m') (n : ℕ) (z : Vector E m) :
    Bus.padWeight n (Vector.cast h z) = Bus.padWeight n z := by
  subst h
  rfl

/-- **The verifier's loop**: after the coordinates `l`, its running value is
`pad_{n mod 2^|l|}(l)`. -/
theorem foldPad_eq (n : ℕ) : ∀ l : List E,
    foldPad l n = Bus.padWeight (n % 2 ^ l.length) (vecList l) := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    have h0 : n % 2 ^ ([] : List E).length = 0 := Nat.mod_one n
    rw [foldPad, List.zipIdx_nil, List.foldl_nil, h0, padWeight_zero]
  | append_singleton l r ih =>
    have hstep : foldPad (l ++ [r]) n =
        (1 + eOfNat ((n >>> l.length) % 2)) * r +
          (1 + eOfNat ((n >>> l.length) % 2) + r) * foldPad l n := by
      simp [foldPad, List.zipIdx_append, List.foldl_append]
    have hsplit : n % 2 ^ (l ++ [r]).length =
        n % 2 ^ l.length + 2 ^ l.length * ((n >>> l.length) % 2) := by
      rw [List.length_append, List.length_singleton, Nat.shiftRight_eq_div_pow, pow_succ,
        Nat.mod_mul, add_comm]
    have hlt := Nat.mod_lt n (Nat.two_pow_pos l.length)
    rw [hstep, ih, hsplit, vecList_append, padWeight_cast, padWeight_append]
    rcases Nat.mod_two_eq_zero_or_one (n >>> l.length) with hb | hb
    · rw [hb, eOfNat_zero', Nat.mul_zero, Nat.add_zero,
        show n % 2 ^ l.length - 2 ^ l.length = 0 by omega, padWeight_zero]
      linear_combination (r * Bus.padWeight (n % 2 ^ l.length) (vecList l)) * one_add_one'
    · rw [hb, eOfNat_one', Nat.mul_one, padWeight_of_le (vecList l)
        (show 2 ^ l.length ≤ n % 2 ^ l.length + 2 ^ l.length by omega), Nat.add_sub_cancel]
      linear_combination (r + Bus.padWeight (n % 2 ^ l.length) (vecList l)) * one_add_one'

/-- **`padding_weight` is the padding rows' weight** (Lemma `lem:suffix`): for `n ≤ 2^|point|`,
the verifier's `pad_n(point)` is the extension at `point` of the indicator of the rows `x ≥ n`. -/
theorem paddingWeight_eq_padWeight (l : List E) (n : ℕ) (h : n ≤ 2 ^ l.length) :
    paddingWeight l n = Bus.padWeight n (vecList l) := by
  have hfold : paddingWeight l n = (1 + eOfNat ((n >>> l.length) % 2)) * foldPad l n := rfl
  rw [hfold, foldPad_eq]
  rcases h.lt_or_eq with hlt | heq
  · rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt, Nat.zero_mod, eOfNat_zero', add_zero,
      one_mul, Nat.mod_eq_of_lt hlt]
  · rw [heq, Nat.shiftRight_eq_div_pow, Nat.div_self (Nat.two_pow_pos _), Nat.one_mod,
      eOfNat_one', one_add_one', zero_mul, padWeight_of_le _ le_rfl]

/-- `padding_weight` of a point's first `m` coordinates, for `n ≤ 2^m`, is the padding rows'
weight at them. -/
theorem padWeight_ofFn_take (p : List E) {m : ℕ} (n : ℕ) (hm : m ≤ p.length) (hn : n ≤ 2 ^ m) :
    Bus.padWeight n (Vector.ofFn fun i : Fin m ↦ p.getD i 0) = paddingWeight (p.take m) n := by
  have hl : (p.take m).length = m := by rw [List.length_take]; omega
  rw [paddingWeight_eq_padWeight _ _ (by rw [hl]; exact hn)]
  have hv : (Vector.ofFn fun i : Fin m ↦ p.getD i 0) = Vector.cast hl (vecList (p.take m)) := by
    apply Vector.ext
    intro i hi
    simp [vecList, List.getD_eq_getElem?_getD, List.getElem?_take, hi]
  rw [hv, padWeight_cast]

end

end LeanVM.Protocol.EndToEnd.Front
