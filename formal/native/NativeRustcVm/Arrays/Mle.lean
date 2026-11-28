module

public import NativeVm.Model.Field

/-!
# `multilinear_eval_by`: the streaming fold is `multilinearEval`

`field.rs`'s `multilinear_eval_by` folds the entries as they arrive, one pending entry per level
(`pending`, `full`): an entry carried to level `k` pairs with the entry pending there, as
`foldPairs` pairs entries `2 j`, `2 j + 1`, or waits there; the first entry carried to level
`|point|` is the result, else `0`. Its transcription: `carry` (one entry's carries, `pend k` the
entry pending at level `k`), `stream` (the entries in turn).

The levels of the model's fold (`lev k`, the entries after `k` folds) and, after `i` entries
(`Pend i`), level `k` holds an entry iff bit `k` of `i` is set, entry `i / 2^k - 1` of level `k`
(`pending_of_bit`). One entry's carries (`carry_none`, `carry_some`, `carry_top`), then the stream:
`stream_eq`, `stream point mle none = multilinearEval mle point` for every `|point|`; and at
`|point| ≥ 64` with fewer than `2^64` entries the model's value is `0`
(`multilinearEval_eq_zero`), the Rust's early exit.
-/

namespace NativeRustcVm.Mle

open NativeVm.Model

@[expose] public section

/-- `foldPairs` on lists: entries `2 j`, `2 j + 1` become `a·(1 + r) + b·r`. -/
def fp (r : EW) (l : List EW) : List EW :=
  (List.range (l.length / 2)).map fun j ↦ l.getD (2 * j) 0 * (1 + r) + l.getD (2 * j + 1) 0 * r

/-- The entries after `k` folds. -/
def lev (mle point : List EW) : Nat → List EW
  | 0 => mle
  | k + 1 => fp (point.getD k 0) (lev mle point k)

/-- `pend` with level `k` set to `o`. -/
def setP (pend : Nat → Option EW) (k : Nat) (o : Option EW) : Nat → Option EW :=
  fun j ↦ if j = k then o else pend j

/-- One entry's carries from level `k` with value `v`: the levels it waits at (`inl`, the levels'
new pending entries), or the value it reaches level `|point|` with (`inr`). -/
def carry (point : List EW) (pend : Nat → Option EW) (k : Nat) (v : EW) :
    (Nat → Option EW) ⊕ EW :=
  if h : point.length ≤ k then .inr v
  else match pend k with
    | none => .inl (setP pend k (some v))
    | some a => carry point (setP pend k none) (k + 1) (a * (1 + point[k]) + v * point[k])
termination_by point.length - k

/-- The entries in turn, from the pending entries `pend`: the first value to reach level
`|point|`, else `0`. -/
def stream (point : List EW) : List EW → (Nat → Option EW) → EW
  | [], _ => 0
  | e :: es, pend =>
    match carry point pend 0 e with
    | .inr v => v
    | .inl p => stream point es p

end

public section

theorem getD_of_lt {α : Type} {l : List α} {i : Nat} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-! ## The model's levels -/

theorem foldPairs_toList (r : EW) (a : Array EW) : (foldPairs r a).toList = fp r a.toList := by
  unfold foldPairs fp
  rw [Array.toList_map, Array.toList_range, Array.length_toList]
  apply List.map_congr_left
  intro j _
  simp only [getElem!_def, Array.getElem?_toList, List.getD_eq_getElem?_getD]
  rfl

theorem length_fp (r : EW) (l : List EW) : (fp r l).length = l.length / 2 := by simp [fp]

theorem length_lev (mle point : List EW) (k : Nat) :
    (lev mle point k).length = mle.length / 2 ^ k := by
  induction k with
  | zero => simp [lev]
  | succ k ih => rw [lev, length_fp, ih, Nat.pow_succ, Nat.div_div_eq_div_mul]

theorem getD_lev_succ (mle point : List EW) (k j : Nat) (hj : j < mle.length / 2 ^ (k + 1)) :
    (lev mle point (k + 1)).getD j 0 = (lev mle point k).getD (2 * j) 0 * (1 + point.getD k 0) +
      (lev mle point k).getD (2 * j + 1) 0 * point.getD k 0 := by
  have hj' : j < (lev mle point k).length / 2 := by
    rw [length_lev, Nat.div_div_eq_div_mul, ← Nat.pow_succ]; exact hj
  rw [lev, fp, getD_of_lt (by simp; exact hj'), List.getElem_map, List.getElem_range]

theorem foldl_take (mle point : List EW) (k : Nat) (hk : k ≤ point.length) :
    (point.take k).foldl (fun cur r ↦ fp r cur) mle = lev mle point k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.take_add_one, List.foldl_append, ih (by omega), List.getElem?_eq_getElem (by omega)]
    simp only [Option.toList_some, List.foldl_cons, List.foldl_nil, lev]
    rw [getD_of_lt (by omega)]

/-- **The model as levels**: `multilinearEval mle point` is level `|point|`'s first entry, or `0`. -/
theorem multilinearEval_eq_lev (mle point : Array EW) :
    multilinearEval mle point = (lev mle.toList point.toList point.size).headD 0 := by
  unfold multilinearEval
  rw [← Array.foldl_toList]
  have h : point.toList.foldl (fun cur r ↦ foldPairs r cur) mle =
      (point.toList.foldl (fun cur r ↦ fp r cur) mle.toList).toArray := by
    generalize mle = a
    induction point.toList generalizing a with
    | nil => simp
    | cons r l ih =>
      rw [List.foldl_cons, List.foldl_cons, ih, foldPairs_toList]
  rw [h, ← foldl_take mle.toList point.toList point.size (by simp), List.take_of_length_le
    (by simp)]
  cases point.toList.foldl (fun cur r ↦ fp r cur) mle.toList <;> rfl

/-- At `2^|point|` entries or more no entry reaches level `|point|`: the model's value is `0`. -/
theorem multilinearEval_eq_zero (mle point : Array EW) (h : mle.size < 2 ^ point.size) :
    multilinearEval mle point = 0 := by
  rw [multilinearEval_eq_lev]
  have : (lev mle.toList point.toList point.size).length = 0 := by
    rw [length_lev, Array.length_toList, Nat.div_eq_of_lt h]
  rw [List.length_eq_zero_iff.mp this]
  rfl

/-! ## Bits -/

theorem bit_iff (i k : Nat) : i.testBit k = true ↔ i / 2 ^ k % 2 = 1 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp

/-- After `i` entries: level `k` (below `|point|`) holds entry `i / 2^k - 1` of level `k` when
bit `k` of `i` is set, else nothing. -/
def Pend (mle point : List EW) (i : Nat) (pend : Nat → Option EW) : Prop :=
  ∀ k < point.length, pend k =
    if i / 2 ^ k % 2 = 1 then some ((lev mle point k).getD (i / 2 ^ k - 1) 0) else none

/-- An entry `i` carried to level `k` (bits below `k` of `i` set): the levels below `k` emptied,
the others as after `i` entries. -/
def CarryInv (mle point : List EW) (i k : Nat) (pend : Nat → Option EW) : Prop :=
  i % 2 ^ k = 2 ^ k - 1 ∧ (∀ j < k, pend j = none) ∧
    ∀ j, k ≤ j → j < point.length → pend j =
      if i / 2 ^ j % 2 = 1 then some ((lev mle point j).getD (i / 2 ^ j - 1) 0) else none

theorem carryInv_zero {mle point : List EW} {i : Nat} {pend : Nat → Option EW}
    (h : Pend mle point i pend) : CarryInv mle point i 0 pend :=
  ⟨by simp [Nat.mod_one], fun _ h => absurd h (Nat.not_lt_zero _), fun j _ hj => h j hj⟩

theorem div_pow_succ (i k : Nat) : i / 2 ^ (k + 1) = i / 2 ^ k / 2 := by
  rw [Nat.pow_succ, Nat.div_div_eq_div_mul]

/-- `i`'s bits below `k` set and bit `k` clear: `i + 1`'s bits below `k + 1` are `k`'s only,
those above `i`'s. -/
theorem bits_succ {i k : Nat} (hlow : i % 2 ^ k = 2 ^ k - 1) (hk : i / 2 ^ k % 2 = 0) (j : Nat) :
    ((i + 1) / 2 ^ j % 2 = 1 ↔ (j = k ∨ (k < j ∧ i / 2 ^ j % 2 = 1))) ∧
      (k < j → (i + 1) / 2 ^ j = i / 2 ^ j) ∧ (i + 1) / 2 ^ k = i / 2 ^ k + 1 := by
  have hP := Nat.two_pow_pos k
  obtain ⟨q, hq⟩ : ∃ q, i = 2 ^ k * q + (2 ^ k - 1) := ⟨i / 2 ^ k, by
    have := Nat.div_add_mod i (2 ^ k); omega⟩
  have hqi : i / 2 ^ k = q := by
    rw [hq, Nat.mul_add_div hP, Nat.div_eq_of_lt (by omega)]; rfl
  have hi1 : (i + 1) / 2 ^ k = q + 1 := by
    rw [show i + 1 = 2 ^ k * (q + 1) by rw [hq, Nat.mul_add]; omega, Nat.mul_div_cancel_left _ hP]
  rw [hqi] at hk
  refine ⟨?_, fun hkj => ?_, by rw [hi1, hqi]⟩
  · rcases Nat.lt_trichotomy j k with hjk | rfl | hjk
    · have : (i + 1) / 2 ^ j = 2 ^ (k - j) * (q + 1) := by
        rw [show i + 1 = 2 ^ j * (2 ^ (k - j) * (q + 1)) by
          rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' (by omega), hq, Nat.mul_add]
          omega, Nat.mul_div_cancel_left _ (Nat.two_pow_pos j)]
      rw [this, show k - j = (k - j - 1) + 1 by omega, Nat.pow_succ]
      constructor
      · intro h
        rw [Nat.mul_assoc, Nat.mul_comm 2, ← Nat.mul_assoc] at h
        generalize 2 ^ (k - j - 1) * (q + 1) = X at h
        omega
      · intro h; omega
    · rw [hi1]; omega
    · have h1 : ∀ x, x / 2 ^ j = x / 2 ^ k / 2 ^ (j - k) := fun x => by
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
      rw [h1, h1 i, hi1, hqi, show j - k = (j - k - 1) + 1 by omega, Nat.pow_succ',
        ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, show (q + 1) / 2 = q / 2 by omega]
      omega
  · have h1 : ∀ x, x / 2 ^ j = x / 2 ^ k / 2 ^ (j - k) := fun x => by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
    rw [h1, h1 i, hi1, hqi, show j - k = (j - k - 1) + 1 by omega, Nat.pow_succ',
      ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, show (q + 1) / 2 = q / 2 by omega]

/-- Bit `k < m` of `i` clear: `i`'s bits below `m` are not all set. -/
theorem not_full_of_bit {i k m : Nat} (hk : k < m) (h : i / 2 ^ k % 2 = 0) :
    i % 2 ^ m ≠ 2 ^ m - 1 := by
  intro hm
  have h1 : (i % 2 ^ m).testBit k = (2 ^ m - 1).testBit k := by rw [hm]
  rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one] at h1
  simp only [hk, decide_true, Bool.true_and] at h1
  rw [bit_iff] at h1
  omega

/-! ## One entry's carries -/

/-- **Waiting at level `k`**: an entry carried to level `k` (`k < |point|`) where nothing waits
waits there; `i + 1` entries done, and not all bits below `|point|` of `i` set. -/
theorem carry_none {mle point : List EW} {i k : Nat} {pend : Nat → Option EW} {v : EW}
    (hc : CarryInv mle point i k pend) (hk : k < point.length) (hv : v = (lev mle point k).getD
      (i / 2 ^ k) 0) (hp : pend k = none) :
    Pend mle point (i + 1) (setP pend k (some v)) ∧ i % 2 ^ point.length ≠ 2 ^ point.length - 1 := by
  obtain ⟨hlow, hbelow, habove⟩ := hc
  have hbit : i / 2 ^ k % 2 = 0 := by
    have := habove k (Nat.le_refl _) hk
    rw [hp] at this
    split at this
    · cases this
    · omega
  refine ⟨fun j hj => ?_, not_full_of_bit hk hbit⟩
  obtain ⟨hb, hhi, hk1⟩ := bits_succ hlow hbit j
  unfold setP
  by_cases hjk : j = k
  · subst hjk
    rw [ite_eq_left rfl, ite_eq_left (hb.mpr (Or.inl rfl)), hk1, Nat.add_sub_cancel, hv]
  · rw [ite_eq_right hjk]
    rcases Nat.lt_or_gt_of_ne hjk with hlt | hgt
    · rw [hbelow j hlt, ite_eq_right (fun h => by rcases hb.mp h with h | h <;> omega)]
    · rw [habove j (by omega) hj, hhi hgt]

/-- **Pairing at level `k`**: an entry carried to level `k` where an entry waits pairs with it,
`a·(1 + r) + v·r`, carried to level `k + 1`. -/
theorem carry_some {mle point : List EW} {i k : Nat} {pend : Nat → Option EW} {v a : EW}
    (hc : CarryInv mle point i k pend) (hi : i < mle.length) (hk : k < point.length)
    (hv : v = (lev mle point k).getD (i / 2 ^ k) 0) (hp : pend k = some a) :
    CarryInv mle point i (k + 1) (setP pend k none) ∧
      a * (1 + point.getD k 0) + v * point.getD k 0 =
        (lev mle point (k + 1)).getD (i / 2 ^ (k + 1)) 0 := by
  obtain ⟨hlow, hbelow, habove⟩ := hc
  have hpk := habove k (Nat.le_refl _) hk
  rw [hp] at hpk
  have hbit : i / 2 ^ k % 2 = 1 := by
    split at hpk
    · assumption
    · cases hpk
  rw [ite_eq_left hbit, Option.some.injEq] at hpk
  have hP := Nat.two_pow_pos k
  obtain ⟨q, hq⟩ : ∃ q, i = 2 ^ k * q + (2 ^ k - 1) := ⟨i / 2 ^ k, by
    have := Nat.div_add_mod i (2 ^ k); omega⟩
  have hqi : i / 2 ^ k = q := by
    rw [hq, Nat.mul_add_div hP, Nat.div_eq_of_lt (by omega)]; rfl
  rw [hqi] at hbit hpk hv
  refine ⟨⟨?_, fun j hj => ?_, fun j hj hjm => ?_⟩, ?_⟩
  · rw [Nat.pow_succ, hq]
    obtain ⟨t, rfl⟩ : ∃ t, q = 2 * t + 1 := ⟨q / 2, by omega⟩
    rw [show 2 ^ k * (2 * t + 1) + (2 ^ k - 1) = (2 ^ k * 2) * t + (2 ^ k * 2 - 1) by
      rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (2 ^ k) 2]; omega,
      Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  · unfold setP
    by_cases hjk : j = k
    · rw [ite_eq_left hjk]
    · rw [ite_eq_right hjk]; exact hbelow j (by omega)
  · unfold setP
    rw [ite_eq_right (by omega)]
    exact habove j (by omega) hjm
  · have hn : q / 2 < mle.length / 2 ^ (k + 1) := by
      rw [div_pow_succ]
      have : q + 1 ≤ mle.length / 2 ^ k := by
        rw [Nat.le_div_iff_mul_le hP]
        rw [hq] at hi
        rw [Nat.mul_comm]
        rw [Nat.mul_add, Nat.mul_one]
        omega
      omega
    rw [div_pow_succ, hqi, getD_lev_succ _ _ _ _ hn,
      show 2 * (q / 2) = q - 1 by omega, show q - 1 + 1 = q by omega, ← hpk, hv]

/-- **Reaching level `|point|`**: an entry carried there (all bits below `|point|` of `i` set) is
entry `i / 2^|point|` of the last level. -/
theorem carry_top {mle point : List EW} {i : Nat} {pend : Nat → Option EW}
    (hc : CarryInv mle point i point.length pend) : i % 2 ^ point.length = 2 ^ point.length - 1 :=
  hc.1

theorem carry_eq {mle point : List EW} {i : Nat} (hi : i < mle.length) :
    ∀ (n k : Nat) (pend : Nat → Option EW) (v : EW), n = point.length - k → k ≤ point.length →
      CarryInv mle point i k pend → v = (lev mle point k).getD (i / 2 ^ k) 0 →
      match carry point pend k v with
      | .inr w => i % 2 ^ point.length = 2 ^ point.length - 1 ∧
          w = (lev mle point point.length).getD (i / 2 ^ point.length) 0
      | .inl p => i % 2 ^ point.length ≠ 2 ^ point.length - 1 ∧ Pend mle point (i + 1) p := by
  intro n
  induction n with
  | zero =>
    intro k pend v hn hk hc hv
    have hkm : k = point.length := by omega
    subst hkm
    rw [carry, dite_eq_left (Nat.le_refl _)]
    exact ⟨hc.1, hv⟩
  | succ n ih =>
    intro k pend v hn hk hc hv
    have hk' : k < point.length := by omega
    rw [carry, dite_eq_right (by omega)]
    cases hp : pend k with
    | none => exact ⟨(carry_none hc hk' hv hp).2, (carry_none hc hk' hv hp).1⟩
    | some a =>
      obtain ⟨hc', hv'⟩ := carry_some hc hi hk' hv hp
      rw [getD_of_lt hk'] at hv'
      exact ih (k + 1) _ _ (by omega) (by omega) hc' hv'

theorem pend_none (mle point : List EW) : Pend mle point 0 fun _ ↦ none := by
  intro k _
  rw [Nat.zero_div, Nat.zero_mod, ite_eq_right (by decide)]

/-- **The stream is the model**: from entry `i` on (`Pend` after `i` entries, no entry yet at the
last level), the stream's value is the last level's first entry, or `0`. -/
theorem stream_drop (mle point : List EW) :
    ∀ (n i : Nat) (pend : Nat → Option EW), n = mle.length - i → i ≤ mle.length →
      i < 2 ^ point.length → Pend mle point i pend →
      stream point (mle.drop i) pend = (lev mle point point.length).headD 0 := by
  intro n
  induction n with
  | zero =>
    intro i pend hn hi hlt _
    have : i = mle.length := by omega
    subst this
    rw [List.drop_length, stream]
    have : (lev mle point point.length).length = 0 := by
      rw [length_lev, Nat.div_eq_of_lt hlt]
    rw [List.length_eq_zero_iff.mp this]
    rfl
  | succ n ih =>
    intro i pend hn hi hlt hp
    have hi' : i < mle.length := by omega
    rw [List.drop_eq_getElem_cons hi', stream]
    have hc := carry_eq (point := point) hi' _ 0 pend mle[i] rfl (Nat.zero_le _)
      (carryInv_zero hp) (by rw [Nat.pow_zero, Nat.div_one]; exact (getD_of_lt hi').symm)
    split
    · rename_i w hw
      rw [hw] at hc
      obtain ⟨hfull, hw⟩ := hc
      have : i = 2 ^ point.length - 1 := by rw [Nat.mod_eq_of_lt hlt] at hfull; exact hfull
      rw [hw, this, Nat.div_eq_of_lt (by omega)]
      cases lev mle point point.length <;> rfl
    · rename_i p hpq
      rw [hpq] at hc
      obtain ⟨hnf, hp'⟩ := hc
      rw [show List.drop (i + 1) mle = mle.drop (i + 1) from rfl]
      have := ih (i + 1) p (by omega) (by omega) (by rw [Nat.mod_eq_of_lt hlt] at hnf; omega) hp'
      exact this

/-- **`multilinear_eval_by` is `multilinearEval`**, for every `|point|`. -/
theorem stream_eq (mle point : Array EW) :
    stream point.toList mle.toList (fun _ ↦ none) = multilinearEval mle point := by
  rw [multilinearEval_eq_lev, ← Array.length_toList (xs := point)]
  have := stream_drop mle.toList point.toList _ 0 _ rfl (Nat.zero_le _)
    (Nat.two_pow_pos _) (pend_none _ _)
  rwa [List.drop_zero] at this

end

/-! ## The stream in the middle of an entry's carries -/

@[expose] public section

/-- The stream's value with an entry `v` carried to level `k` and the entries `es` still to
come. -/
def cont (point es : List EW) (pend : Nat → Option EW) (k : Nat) (v : EW) : EW :=
  match carry point pend k v with
  | .inr w => w
  | .inl p => stream point es p

end

public section

theorem stream_cons (point : List EW) (e : EW) (es : List EW) (pend : Nat → Option EW) :
    stream point (e :: es) pend = cont point es pend 0 e := by
  rw [stream, cont]

/-- An entry at level `|point|` is the value. -/
theorem cont_top {point es : List EW} {pend : Nat → Option EW} {k : Nat} (v : EW)
    (h : point.length ≤ k) : cont point es pend k v = v := by
  rw [cont, carry, dite_eq_left h]

/-- An entry where nothing waits waits there; the stream goes on. -/
theorem cont_none {point es : List EW} {pend : Nat → Option EW} {k : Nat} (v : EW)
    (h : k < point.length) (hp : pend k = none) :
    cont point es pend k v = stream point es (setP pend k (some v)) := by
  rw [cont, carry, dite_eq_right (by omega)]
  simp only [hp]

/-- An entry where `a` waits pairs with it, carried to level `k + 1`. -/
theorem cont_some {point es : List EW} {pend : Nat → Option EW} {k : Nat} (v a : EW)
    (h : k < point.length) (hp : pend k = some a) :
    cont point es pend k v =
      cont point es (setP pend k none) (k + 1) (a * (1 + point[k]) + v * point[k]) := by
  rw [cont, carry, dite_eq_right (by omega)]
  simp only [hp]
  rfl

end

end NativeRustcVm.Mle
