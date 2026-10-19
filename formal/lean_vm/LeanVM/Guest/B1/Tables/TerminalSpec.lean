/-
  LeanVM.Guest.B1.Tables.TerminalSpec

  The stacked opening's weight (V:1781-1785) as `check_opening_terminal` computes it: the
  placements of the claims' columns, each claim's weight as products over the coordinates, the
  ring-switch weight as a sum of rows.
-/

module

public import LeanVM.Guest.B1.Tables.TerminalBody
public import LeanVM.Guest.B1.Tables.TCtx
public import LeanVM.Guest.B1.Tables.Kappas

/-!
# The stacked weight, coordinate by coordinate

* `claim_cols`: the guest's baked tables (`claimKind`, `claimCol`, `claimSlot`) are the
  specification's: claim `j`'s global column `claimColumns[j]` is committed column `claimCol j`,
  or `BLAKE2S` limb `claimSlot j` of `q_flock`.
* `placementsOf_getD`: a column's placement (V:906-916).
* `stackPoint_lo`, `stackPoint_q`: a claim's point on the stack, entry by entry.
* `ringWeight_eq`: `ringWeight` (V:2011) is the sum of `ringRow`s.
* `column_selector_any_iff`: the 29 arms of `column_selector` at once.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-! ## The baked tables -/

/-- **The claims' columns** (`CLAIM_POINT_BUF`, `CLAIM_COMMITTED_COL`,
`CLAIM_QFLOCK_SLOT_BITS`, G:2039-2056): a limb's claim carries its `q_flock` slot, any other
claim its committed column. -/
theorem claim_cols : ∀ j < 112, claimColumns.getD j 0 < 110 ∧
    (claimKind j = 2 → limbSlot (claimColumns.getD j 0) = some (claimSlot j) ∧
      claimSlot j < 256 ∧ 82 ≤ claimColumns.getD j 0 ∧ claimColumns.getD j 0 < 100) ∧
    (claimKind j ≠ 2 → limbSlot (claimColumns.getD j 0) = none ∧ claimCol j < 92 ∧
      (blockCols 110).idxOf (claimColumns.getD j 0) = claimCol j ∧
      (blockCols 110).getD (claimCol j) 0 = claimColumns.getD j 0) := by
  decide +kernel

theorem blockCols_lo : ∀ c < 82, (blockCols 110).getD c 0 = c := by decide +kernel

theorem qflock_col : limbSlot qflock = none ∧ (blockCols 110).idxOf qflock = 5 ∧
    (blockCols 110).getD 5 0 = qflock := by decide +kernel

theorem claimKind_pi {j : ℕ} (h1 : 109 ≤ j) (h2 : j < 112) :
    claimKind j = 3 ∧ claimColumns.getD j 0 = j - 109 ∧ claimCol j = j - 109 := by
  interval_cases j <;> decide +kernel

/-! ## The columns' sizes -/

theorem columnKappas_eq_gen (lm lb : ℕ) (hs : List ℕ) :
    columnKappas lm lb hs = [lm, lm, lm, lm, lb, hs.getD 5 0 + 8] ++
      List.replicate 15 (hs.getD 0 0) ++ List.replicate 15 (hs.getD 1 0) ++
      List.replicate 8 (hs.getD 2 0) ++ List.replicate 15 (hs.getD 3 0) ++
      List.replicate 14 (hs.getD 4 0) ++ List.replicate 37 (hs.getD 5 0) := by
  have e : tables.flatMap (fun t ↦ List.replicate t.width (hs.getD t.opcode 0)) =
      (tables.map fun t ↦ (t.width, t.opcode)).flatMap
        (fun p ↦ List.replicate p.1 (hs.getD p.2 0)) := by
    rw [List.flatMap_map]
  unfold columnKappas
  rw [e, tables_shape]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
    List.nil_append, List.append_assoc]
  rfl

theorem columnKappas_mem (lm lb : ℕ) (hs : List ℕ) {c : ℕ} (hc : c < 4) :
    (columnKappas lm lb hs).getD c 0 = lm := by
  rw [columnKappas_eq_gen]; interval_cases c <;> rfl

theorem columnKappas_qflock (lm lb : ℕ) (hs : List ℕ) :
    (columnKappas lm lb hs).getD 5 0 = hs.getD 5 0 + 8 := by
  rw [columnKappas_eq_gen]; rfl

theorem columnKappas_blake (lm lb : ℕ) (hs : List ℕ) {k : ℕ} (hk : k < 37) :
    (columnKappas lm lb hs).getD (73 + k) 0 = hs.getD 5 0 := by
  rw [columnKappas_eq_gen]
  have hl : ([lm, lm, lm, lm, lb, hs.getD 5 0 + 8] ++ List.replicate 15 (hs.getD 0 0) ++
      List.replicate 15 (hs.getD 1 0) ++ List.replicate 8 (hs.getD 2 0) ++
      List.replicate 15 (hs.getD 3 0) ++ List.replicate 14 (hs.getD 4 0)).length = 73 := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hl]; omega), hl,
    Nat.add_sub_cancel_left, List.getElem?_replicate, ite_pos' hk, Option.getD_some]

theorem committedKappas_getD (kappas : List ℕ) (hl : kappas.length = 110) {c : ℕ} (hc : c < 92) :
    (committedKappas kappas).getD c 0 = kappas.getD ((blockCols 110).getD c 0) 0 := by
  have h : c < (blockCols 110).length := by rw [blockCols_110_length]; exact hc
  rw [committedKappas, hl, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem h, Option.map_some, Option.getD_some, List.getD_eq_getElem _ _ h]

/-! ## Placements -/

/-- Committed column `c`'s offset on the stack. -/
def offAt (kappas : List ℕ) (c : ℕ) : ℕ := (stackOffsets (committedKappas kappas)).1.getD c 0

/-- **A column's placement** (V:906-916): a limb sits at `q_flock`'s offset plus its slot, below
`q_flock`'s slot bits; any other column at its own offset. -/
theorem placementsOf_getD (kappas : List ℕ) {col : ℕ} (hc : col < kappas.length) :
    (placementsOf kappas).1.getD col default =
      match limbSlot col with
      | some slot =>
        ⟨kappas.getD col 0, offAt kappas ((blockCols kappas.length).idxOf qflock) + slot,
          qflockSlotBits⟩
      | none => ⟨kappas.getD col 0, offAt kappas ((blockCols kappas.length).idxOf col), 0⟩ := by
  unfold placementsOf offAt committedKappas blockCols
  simp only
  rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_zipIdx,
    List.getD_eq_getElem _ _ hc, Nat.zero_add]
  rfl

/-! ## A claim's point on the stack -/

theorem selectorPoint_length (sel n : ℕ) : (selectorPoint sel n).length = n := by
  simp [selectorPoint]

theorem selectorPoint_getD (sel n k : ℕ) (hk : k < n) :
    (selectorPoint sel n).getD k 0 = bitE (sel.testBit k) := by
  rw [selectorPoint, getD_map_range _ _ hk, eOfNat_shift_mod]

theorem getD_append' {l1 l2 : List E} {k : ℕ} :
    (l1 ++ l2).getD k 0 = if k < l1.length then l1.getD k 0 else l2.getD (k - l1.length) 0 := by
  split_ifs with h
  · exact getD_append_lt h
  · obtain ⟨t, rfl⟩ : ∃ t, k = l1.length + t := ⟨k - l1.length, by omega⟩
    rw [getD_append_ge, Nat.add_sub_cancel_left]

theorem getD_drop' (l : List E) (a k : ℕ) : (l.drop a).getD k 0 = l.getD (a + k) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_take' (l : List E) {a k : ℕ} (h : k < a) : (l.take a).getD k 0 = l.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, h, ↓reduceIte]

/-- An unplaced column's point on the stack (`low = 0`): its own point, then its offset's bits. -/
theorem stackPoint_lo {κ off μ : ℕ} {p : List E} (hp : p.length = κ) (hκ : κ ≤ μ) :
    (({ vars := κ, index := off } : Placement).stackPoint p μ).length = μ ∧
      ∀ k < μ, (({ vars := κ, index := off } : Placement).stackPoint p μ).getD k 0 =
        if k < κ then p.getD k 0 else bitE (off.testBit k) := by
  simp only [Placement.stackPoint, List.take_zero, List.nil_append, Nat.zero_add]
  refine ⟨by simp [hp, selectorPoint_length]; omega, fun k hk => ?_⟩
  rw [getD_append', hp]
  split_ifs with h
  · rfl
  · rw [getD_drop', show κ + (k - κ) = k by omega, selectorPoint_getD _ _ _ hk]

/-- A limb's point on the stack (`low = 8`): its slot's bits, its point, `q_flock`'s offset's
bits. -/
theorem stackPoint_q {τ off s μ : ℕ} {p : List E} (hp : p.length = τ) (hμ : 8 + τ ≤ μ)
    (hal : 2 ^ (8 + τ) ∣ off) (hs : s < 256) :
    (({ vars := τ, index := off + s, low := 8 } : Placement).stackPoint p μ).length = μ ∧
      ∀ k < μ, (({ vars := τ, index := off + s, low := 8 } : Placement).stackPoint p μ).getD k 0 =
        if k < 8 then bitE (s.testBit k) else if k < 8 + τ then p.getD (k - 8) 0
        else bitE (off.testBit k) := by
  obtain ⟨a, rfl⟩ := hal
  have hs' : s < 2 ^ (8 + τ) := lt_of_lt_of_le hs
    (le_trans (by norm_num : 256 ≤ 2 ^ 8) (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hbit : ∀ k, (2 ^ (8 + τ) * a + s).testBit k =
      if k < 8 then s.testBit k else if k < 8 + τ then false else (2 ^ (8 + τ) * a).testBit k := by
    intro k
    rw [Nat.testBit_two_pow_mul_add a hs' k, Nat.testBit_two_pow_mul]
    by_cases h1 : k < 8 + τ
    · rw [ite_pos' h1]
      by_cases h2 : k < 8
      · rw [ite_pos' h2]
      · rw [ite_neg' h2, ite_pos' h1]
        exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hs
          (le_trans (by norm_num : 256 ≤ 2 ^ 8) (Nat.pow_le_pow_right (by norm_num) (by omega))))
    · rw [ite_neg' h1, ite_neg' (by omega), ite_neg' h1]
      simp [show 8 + τ ≤ k by omega]
  simp only [Placement.stackPoint]
  refine ⟨by simp [hp, selectorPoint_length]; omega, fun k hk => ?_⟩
  simp only [getD_append', List.length_append, List.length_take, selectorPoint_length, hp,
    show min 8 μ = 8 by omega]
  split_ifs <;> first
    | omega
    | rfl
    | (rw [getD_take' _ (by omega), selectorPoint_getD _ _ _ hk, hbit, ite_pos' (by omega)])
    | (rw [getD_drop', show 8 + τ + (k - (8 + τ)) = k by omega, selectorPoint_getD _ _ _ hk, hbit,
        ite_neg' (by omega), ite_neg' (by omega)])

/-! ## Weights as products over the coordinates -/

theorem getD_ge {l : List E} {k : ℕ} (h : l.length ≤ k) : l.getD k 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

/-- Past the stack's log, the offset's bits and the point's padding are zero: the factors are 1. -/
theorem prod_extend (x : List E) {off μ κ : ℕ} (hx : x.length = μ) (hoff : off < 2 ^ μ)
    (hκ : κ ≤ μ) (hμ : μ ≤ 28) :
    ∏ t ∈ Finset.range (μ - κ), (1 + bitE (off.testBit (κ + t)) + x.getD (κ + t) 0) =
      ∏ t ∈ Finset.range (28 - κ), (1 + bitE (off.testBit (κ + t)) + x.getD (κ + t) 0) := by
  rw [show 28 - κ = (μ - κ) + (28 - μ) by omega, Finset.prod_range_add]
  have h1 : ∏ t ∈ Finset.range (28 - μ),
      (1 + bitE (off.testBit (κ + (μ - κ + t))) + x.getD (κ + (μ - κ + t)) 0) = 1 := by
    refine Finset.prod_eq_one fun t _ => ?_
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hoff (Nat.pow_le_pow_right (by norm_num)
      (by omega))), getD_ge (by omega)]
    simp [bitE]
  rw [h1, mul_one]

/-- **An unplaced column's claim weight** (V:1227) at the opening point `x` of the stack's log
`μ ≤ 28`: its own coordinates, then the column's selector over 28 coordinates. -/
theorem weight_lo (x p : List E) {κ off μ : ℕ} (hx : x.length = μ) (hp : p.length = κ)
    (hκ : κ ≤ μ) (hμ : μ ≤ 28) (hoff : off < 2 ^ μ) :
    eqEval (({ vars := κ, index := off } : Placement).stackPoint p μ) x =
      (∏ k ∈ Finset.range κ, (1 + p.getD k 0 + x.getD k 0)) *
        ∏ t ∈ Finset.range (28 - κ), (1 + bitE (off.testBit (κ + t)) + x.getD (κ + t) 0) := by
  obtain ⟨hl, hg⟩ := stackPoint_lo (off := off) hp hκ
  rw [Main.eqEval_prod _ _ μ hl hx, show Finset.range μ = Finset.range (κ + (μ - κ)) by
    rw [Nat.add_sub_cancel' hκ], Finset.prod_range_add, ← prod_extend x hx hoff hκ hμ]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k hk => ?_)
    (Finset.prod_congr rfl fun t ht => ?_)
  · have := Finset.mem_range.mp hk
    rw [hg k (by omega), ite_pos' this]
  · have := Finset.mem_range.mp ht
    rw [hg (κ + t) (by omega), ite_neg' (by omega)]

/-- **A limb's claim weight**: its slot's bits, its own coordinates after them, then
`q_flock`'s selector over 28 coordinates. -/
theorem weight_q (x p : List E) {τ off s μ : ℕ} (hx : x.length = μ) (hp : p.length = τ)
    (hτ : 8 + τ ≤ μ) (hμ : μ ≤ 28) (hal : 2 ^ (8 + τ) ∣ off) (hs : s < 256) (hoff : off < 2 ^ μ) :
    eqEval (({ vars := τ, index := off + s, low := 8 } : Placement).stackPoint p μ) x =
      (∏ t ∈ Finset.range 8, (1 + bitE (s.testBit t) + x.getD t 0)) *
        (∏ i ∈ Finset.range τ, (1 + p.getD i 0 + x.getD (8 + i) 0)) *
        ∏ t ∈ Finset.range (28 - (8 + τ)),
          (1 + bitE (off.testBit (8 + τ + t)) + x.getD (8 + τ + t) 0) := by
  obtain ⟨hl, hg⟩ := stackPoint_q hp hτ hal hs
  rw [Main.eqEval_prod _ _ μ hl hx, show Finset.range μ = Finset.range (8 + τ + (μ - (8 + τ))) by
    rw [Nat.add_sub_cancel' hτ], Finset.prod_range_add, Finset.prod_range_add,
    ← prod_extend x hx hoff hτ hμ]
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k hk => ?_)
    (Finset.prod_congr rfl fun i hi => ?_)) (Finset.prod_congr rfl fun t ht => ?_)
  · have := Finset.mem_range.mp hk
    rw [hg k (by omega), ite_pos' this]
  · have := Finset.mem_range.mp hi
    rw [hg (8 + i) (by omega), ite_neg' (by omega), ite_pos' (by omega), Nat.add_sub_cancel_left]
  · have := Finset.mem_range.mp ht
    rw [hg (8 + τ + t) (by omega), ite_neg' (by omega), ite_neg' (by omega)]

/-- **A column's selector** (V:870) at the opening point, over 28 coordinates. -/
theorem eqAbove_lo (x : List E) {κ off μ : ℕ} (hx : x.length = μ) (hκ : κ ≤ μ) (hμ : μ ≤ 28)
    (hoff : off < 2 ^ μ) :
    ({ vars := κ, index := off } : Placement).eqAbove x =
      ∏ t ∈ Finset.range (28 - κ), (1 + bitE (off.testBit (κ + t)) + x.getD (κ + t) 0) := by
  simp only [Placement.eqAbove, Nat.zero_add, Nat.sub_zero, hx]
  rw [Main.eqEval_prod _ _ (μ - κ) (selectorPoint_length _ _) (by simp [hx]),
    ← prod_extend x hx hoff hκ hμ]
  refine Finset.prod_congr rfl fun t ht => ?_
  rw [selectorPoint_getD _ _ _ (Finset.mem_range.mp ht), Nat.testBit_shiftRight, getD_drop']

/-- An unplaced column's claim weight on a prefix `p` of the list `A`. -/
theorem weight_lo' (x p A : List E) {κ off μ : ℕ} (hx : x.length = μ) (hpA : p = A.take p.length)
    (hp : p.length = κ) (hκ : κ ≤ μ) (hμ : μ ≤ 28) (hoff : off < 2 ^ μ) :
    eqEval (({ vars := κ, index := off } : Placement).stackPoint p μ) x =
      (∏ k ∈ Finset.range κ, (1 + A.getD k 0 + x.getD k 0)) *
        ∏ t ∈ Finset.range (28 - κ), (1 + bitE (off.testBit (κ + t)) + x.getD (κ + t) 0) := by
  rw [weight_lo x p hx hp hκ hμ hoff]
  refine congrArg (· * _) (Finset.prod_congr rfl fun k hk => ?_)
  have hk' := Finset.mem_range.mp hk
  rw [hpA, getD_take' _ (by omega)]

/-- A limb's claim weight on a prefix `p` of the list `A`. -/
theorem weight_q' (x p A : List E) {τ off s μ : ℕ} (hx : x.length = μ) (hpA : p = A.take p.length)
    (hp : p.length = τ) (hτ : 8 + τ ≤ μ) (hμ : μ ≤ 28) (hal : 2 ^ (8 + τ) ∣ off) (hs : s < 256)
    (hoff : off < 2 ^ μ) :
    eqEval (({ vars := τ, index := off + s, low := 8 } : Placement).stackPoint p μ) x =
      (∏ t ∈ Finset.range 8, (1 + bitE (s.testBit t) + x.getD t 0)) *
        (∏ i ∈ Finset.range τ, (1 + A.getD i 0 + x.getD (8 + i) 0)) *
        ∏ t ∈ Finset.range (28 - (8 + τ)),
          (1 + bitE (off.testBit (8 + τ + t)) + x.getD (8 + τ + t) 0) := by
  rw [weight_q x p hx hp hτ hμ hal hs hoff]
  refine congrArg (· * _) (congrArg (_ * ·) (Finset.prod_congr rfl fun k hk => ?_))
  have hk' := Finset.mem_range.mp hk
  rw [hpA, getD_take' _ (by omega)]

/-! ## The ring-switch weight -/

theorem ringWeight_fold (r rp : List E) : ∀ (cs : List E) (a : E) (k0 : ℕ),
    (cs.foldl (fun (acc : E × List E) c ↦
      ((acc.1 + (List.zip acc.2 rp).foldl
        (fun product (value, challenge) ↦ product * (1 + value + challenge)) c),
        acc.2.map (· ^ 2))) (a, r.map (· ^ 2 ^ k0))).1 =
      a + ∑ k ∈ Finset.range cs.length, ringRow (cs.getD k 0) r rp (k0 + k)
  | [], a, k0 => by simp
  | c :: cs, a, k0 => by
    rw [List.foldl_cons]
    have hm : (r.map (· ^ 2 ^ k0)).map (· ^ 2) = r.map (· ^ 2 ^ (k0 + 1)) := by
      rw [List.map_map]
      exact List.map_congr_left fun x _ => by
        simp only [Function.comp_apply]; rw [← pow_mul, pow_succ 2 k0]
    simp only
    rw [hm, ringWeight_fold r rp cs _ (k0 + 1), List.length_cons, Finset.sum_range_succ',
      List.getD_cons_zero, Nat.add_zero]
    simp only [List.getD_cons_succ, show ∀ k, k0 + 1 + k = k0 + (k + 1) from fun k => by omega]
    rw [ringRow, add_assoc]
    congr 1
    exact add_comm _ _

/-- **`ringWeight`** (V:2011) is the sum of the coefficients' rows. -/
theorem ringWeight_eq (r rp cs : List E) :
    ringWeight r rp cs = ∑ k ∈ Finset.range cs.length, ringRow (cs.getD k 0) r rp k := by
  have h := ringWeight_fold r rp cs 0 0
  simp only [pow_zero, pow_one, List.map_id', zero_add] at h
  exact h

/-! ## The stacked weight -/

theorem powersFrom_getD (a b : E) : ∀ (n i : ℕ), i < n → (powersFrom a b n).getD i 0 = a * b ^ i
  | 0, _, h => absurd h (by omega)
  | n + 1, 0, _ => by simp [powersFrom]
  | n + 1, i + 1, h => by
    rw [powersFrom, List.getD_cons_succ, powersFrom_getD (a * b) b n i (by omega)]
    ring

theorem length_powersFrom' (a b : E) : ∀ n, (powersFrom a b n).length = n
  | 0 => rfl
  | n + 1 => by rw [powersFrom, List.length_cons, length_powersFrom']

/-- **The stacked opening's weight** (V:1781-1785): the ring-switch claim's, then claim `j`'s
times `λ^(j+1)`. -/
theorem stackWeight_eq (layout : Layout) (claims : List ColumnClaim) (fp cs : List E) (lam : E)
    (x : List E) (hl : claims.length = 112) :
    stackWeight layout claims fp cs lam x =
      (ringSwitchClaim layout 0 (fun rPrime ↦ ringWeight fp rPrime cs)).1 x +
        ∑ j ∈ Finset.range 112, lam ^ (j + 1) *
          (claims.map fun c ↦ (c.onStack layout).1 x).getD j 0 := by
  unfold stackWeight
  simp only
  rw [dot_eq_sum _ _ 113 (by rw [powers, length_powersFrom', List.length_cons, List.length_map, hl])
    (by rw [List.length_map, List.length_cons, List.length_map, hl]),
    Finset.sum_range_succ']
  rw [add_comm]
  refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun j hj => ?_)
  · rw [powers, powersFrom_getD _ _ _ _ (by simp [hl])]
    simp
  · have hj' := Finset.mem_range.mp hj
    rw [powers, powersFrom_getD _ _ _ _ (by simp [hl]; omega), one_mul, List.map_cons,
      List.getD_cons_succ, List.map_map]
    rfl

end
end LeanVM.Guest.B1
