module

public import NativeVm.Field.Fold

/-!
# The bytecode's multilinear extension, streamed: the arithmetic

`multilinearEval L R` folds the table `L` once per coordinate of `R` (`foldPairs`, which drops an
odd last element); node `j` of level `l` of that fold tree is `bcNode L R l j`
(`T(l+1, j) = T(l, 2j) + (T(l, 2j) + T(l, 2j+1))·r_l`, which is `T(l,2j)·(1+r_l) + T(l,2j+1)·r_l`).
`multilinearEval_eq_node`: the extension is `bcNode L R |R| 0` when `2^|R| ≤ |L|`, `0` otherwise.

The streaming code keeps the pending left children of the tree as a binary counter `i` (the words
read so far) keeps its bits: level `l` holds `T(l, 2⌊i / 2^(l+1)⌋)` when bit `l` of `i` is set.
`bc_carry` is one carry, `bc_div_succ_*` the counter's bits after `i + 1`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open LeanVM.Parameters LeanVM.Protocol.Verifier NativeVm.Field

/-- Node `j` of level `l` of the fold tree of `L` at the point `R`. -/
def bcNode (L R : List E) : Nat → Nat → E
  | 0, j => L.getD j 0
  | l + 1, j => bcNode L R l (2 * j) + (bcNode L R l (2 * j) + bcNode L R l (2 * j + 1)) * R.getD l 0

theorem bcNode_succ (L R : List E) (l j : Nat) :
    bcNode L R (l + 1) j =
      bcNode L R l (2 * j) + (bcNode L R l (2 * j) + bcNode L R l (2 * j + 1)) * R.getD l 0 := (rfl)

/-- The table after the first `l` coordinates: its length and its elements, the tree's nodes. -/
theorem fold_take_node (L R : List E) : ∀ l, l ≤ R.length →
    ((R.take l).foldl (fun cur r ↦ foldPairs r cur) L).length = L.length / 2 ^ l ∧
    ∀ j < L.length / 2 ^ l,
      ((R.take l).foldl (fun cur r ↦ foldPairs r cur) L).getD j 0 = bcNode L R l j
  | 0, _ => ⟨by simp, fun j _ ↦ by simp [bcNode]⟩
  | l + 1, hl => by
    obtain ⟨h1, h2⟩ := fold_take_node L R l (by omega)
    have ht : R.take (l + 1) = R.take l ++ [R.getD l 0] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega), List.getElem_eq_getD 0]
      rfl
    rw [ht, List.foldl_append, List.foldl_cons, List.foldl_nil, foldPairs_length, h1,
      Nat.div_div_eq_div_mul, ← pow_succ]
    refine ⟨rfl, fun j hj ↦ ?_⟩
    have hj' : j < ((R.take l).foldl (fun cur r ↦ foldPairs r cur) L).length / 2 := by
      rw [h1, Nat.div_div_eq_div_mul, ← pow_succ]; exact hj
    have hj2 : 2 * j + 1 < L.length / 2 ^ l := by
      rw [pow_succ, ← Nat.div_div_eq_div_mul] at hj; omega
    rw [foldPairs_getD _ _ _ hj', h2 _ (by omega), h2 _ hj2, bcNode_succ]
    ring

/-- **The multilinear extension as the fold tree's root**: over the first `2^|R|` elements when
there are that many, `0` otherwise. -/
theorem multilinearEval_eq_node (L R : List E) :
    multilinearEval L R = if 2 ^ R.length ≤ L.length then bcNode L R R.length 0 else 0 := by
  obtain ⟨h1, h2⟩ := fold_take_node L R R.length le_rfl
  rw [List.take_length] at h1 h2
  rw [multilinearEval, List.headD_eq_getD]
  split
  · exact h2 0 (Nat.div_pos (by assumption) (Nat.pow_pos (by norm_num)))
  · rename_i h
    rw [Nat.div_eq_of_lt (by omega)] at h1
    rw [List.eq_nil_of_length_eq_zero h1]
    rfl

/-! ## The counter's bits -/

/-- **One carry**: the pending left child at level `l` and the right child `v` make their parent. -/
theorem bc_carry (L R : List E) {i l : Nat} (hb : i / 2 ^ l % 2 = 1) :
    (bcNode L R l (i / 2 ^ l) + bcNode L R l (2 * (i / 2 ^ (l + 1)))) * R.getD l 0 +
      bcNode L R l (2 * (i / 2 ^ (l + 1))) = bcNode L R (l + 1) (i / 2 ^ (l + 1)) := by
  have e : i / 2 ^ l = 2 * (i / 2 ^ (l + 1)) + 1 := by
    rw [pow_succ, ← Nat.div_div_eq_div_mul]; omega
  rw [e, bcNode_succ]
  ring

/-- Through a carry the low bits stay set. -/
theorem bc_low_succ {i l : Nat} (h : i % 2 ^ l = 2 ^ l - 1) (hb : i / 2 ^ l % 2 = 1) :
    i % 2 ^ (l + 1) = 2 ^ (l + 1) - 1 := by
  rw [Nat.mod_pow_succ, h, hb, pow_succ]
  have := Nat.one_le_two_pow (n := l)
  omega

/-- The counter after `i` when its low `l` bits are set and bit `l` is not. -/
theorem bc_succ_eq {i l : Nat} (h : i % 2 ^ l = 2 ^ l - 1) :
    i + 1 = 2 ^ l * (i / 2 ^ l + 1) := by
  have := Nat.div_add_mod i (2 ^ l)
  have := Nat.one_le_two_pow (n := l)
  rw [Nat.mul_add, Nat.mul_one]
  omega

theorem bc_div_succ_low {i l k : Nat} (h : i % 2 ^ l = 2 ^ l - 1) (hk : k < l) :
    (i + 1) / 2 ^ k % 2 = 0 := by
  rw [bc_succ_eq h, show l = k + 1 + (l - k - 1) by omega, pow_add, pow_add, Nat.mul_assoc,
    Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos k), pow_one, Nat.mul_mod_right]

theorem bc_div_succ_at {i l : Nat} (h : i % 2 ^ l = 2 ^ l - 1) :
    (i + 1) / 2 ^ l = i / 2 ^ l + 1 := by
  rw [bc_succ_eq h, Nat.mul_div_cancel_left _ (Nat.two_pow_pos l)]

theorem bc_div_succ_high {i l k : Nat} (h : i % 2 ^ l = 2 ^ l - 1) (hb : i / 2 ^ l % 2 = 0)
    (hk : l < k) : (i + 1) / 2 ^ k = i / 2 ^ k := by
  rw [show k = l + 1 + (k - l - 1) by omega, pow_add, pow_add, ← Nat.div_div_eq_div_mul,
    ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    bc_div_succ_at h, pow_one]
  congr 1
  omega

/-- The new pending node at level `l` is the one just stored. -/
theorem bc_div_succ_store {i l : Nat} (h : i % 2 ^ l = 2 ^ l - 1) (hb : i / 2 ^ l % 2 = 0) :
    (i + 1) / 2 ^ l % 2 = 1 ∧ 2 * ((i + 1) / 2 ^ (l + 1)) = i / 2 ^ l := by
  have e : (i + 1) / 2 ^ (l + 1) = ((i + 1) / 2 ^ l) / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [e, bc_div_succ_at h]
  omega

/-- A set bit `l` of `i < 2^m` is below `m`. -/
theorem bc_bit_lt {i l m : Nat} (hi : i < 2 ^ m) (hb : i / 2 ^ l % 2 = 1) : l < m := by
  by_contra hl
  have : i / 2 ^ l = 0 :=
    Nat.div_eq_of_lt (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) (by omega)))
  omega

/-- The level a carry stops at, for `i < 2^m`, is at most `m`. -/
theorem bc_stop_le {i l m : Nat} (hi : i < 2 ^ m) (h : i % 2 ^ l = 2 ^ l - 1) : l ≤ m := by
  by_contra hl
  have hlt : i < 2 ^ l := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [Nat.mod_eq_of_lt hlt] at h
  have : 2 ^ m < 2 ^ l := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

end NativeVm.Code.P3
