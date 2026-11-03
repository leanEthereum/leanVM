import FORS.CoverBound.PerIndex

/-! **The class law of the cover probability at `n` views.** At an index with `n` views, each FORS
tree has `D ∈ {n, n - 1, ≤ n - 2}` distinct disclosed leaves, with the exact occupancy probabilities
`q0 = A^(n) / A^n` (all distinct), `q1 = C(n, 2) A^(n-1) / A^n` (one repeat) and `q2 = 1 - q0 - q1`.
The trees are independent, so the number `w` of trees with a repeat and the number `v ≤ w` of them
with more than one repeat follow the law `C(k, w) C(w, v) q0^(k-w) q1^(w-v) q2^v`. The cover
probability is at most the representative `κ n^(k-w) (n-1)^(w-v) (n-2)^v / A^k` of its class, and at
most the one of `(T, 0)` once `w ≥ T`; a monotone function of it averages to at most the sum over the
classes `w < T` and the overflow. -/

open ENNReal

namespace FORS.Security.H0

variable [Params]

open Concrete ForsPrice FORS.Base.Domination H0Avg

set_option linter.unusedSectionVars false

/-! ### The law in integers (what the kernel computes) -/

/-- The numerator over `A^n` of `q0`, all `n` leaves distinct: `A (A - 1) ⋯ (A - n + 1)`. -/
def lawW0 (a n : ℕ) : ℕ := (2 ^ a).descFactorial n

/-- The numerator over `A^n` of `q1`, exactly one repeat: `C(n, 2) A (A - 1) ⋯ (A - n + 2)`. -/
def lawW1 (a n : ℕ) : ℕ := n * (n - 1) / 2 * (2 ^ a).descFactorial (n - 1)

/-- The numerator over `A^n` of `q2`, more than one repeat. -/
def lawW2 (a n : ℕ) : ℕ := (2 ^ a) ^ n - lawW0 a n - lawW1 a n

/-- `C(n, r)` through factorials. -/
def chooseF (n r : ℕ) : ℕ := n.factorial / (r.factorial * (n - r).factorial)

/-- The numerator over `A^(n k)` of the weight of the class `(w, v)`. -/
def lawWt (k a n w v : ℕ) : ℕ :=
  chooseF k w * chooseF w v * lawW0 a n ^ (k - w) * lawW1 a n ^ (w - v) * lawW2 a n ^ v

/-- The numerator over `A^k` of the representative of the class `(w, v)`. -/
def lawY (k n w v : ℕ) : ℕ := n ^ (k - w) * (n - 1) ^ (w - v) * (n - 2) ^ v

/-- The classes `(w, v)`, `v ≤ w < T`. -/
def lawStates (T : ℕ) : List (ℕ × ℕ) :=
  (List.range T).flatMap fun w => (List.range (w + 1)).map fun v => (w, v)

/-- The numerator over `A^(n k)` of the total weight of the classes `w < T`. -/
def lawMass (k a n T : ℕ) : ℕ := ((lawStates T).map fun p => lawWt k a n p.1 p.2).sum

/-! ### The number of distinct leaves -/

/-- The number of distinct disclosed leaves of a tree. -/
def distinctD (Xs : Multiset FLeaf) : ℕ := Xs.toFinset.card

/-- `A⁻¹`, `A = 2^a` the number of leaves of a tree. -/
noncomputable def leafInv : ℝ≥0∞ := ((2 ^ forsHeight : ℕ) : ℝ≥0∞)⁻¹

theorem φF_eq_distinct (Xs : Multiset FLeaf) : φF Xs = leafInv * (distinctD Xs : ℝ≥0∞) := by
  classical
  unfold φF freshAvg leafInv distinctD CoverF
  rw [Finset.card_univ, Fintype.card_fin]
  congr 1
  have h : (Finset.univ.filter fun t : FLeaf => t ∈ Xs) = Xs.toFinset := by ext; simp
  rw [← h, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

theorem φF_toReal (Xs : Multiset FLeaf) : (φF Xs).toReal = (distinctD Xs : ℝ) / leavesR := by
  rw [φF_eq_distinct, leafInv, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, leavesR]
  push_cast
  ring

theorem distinctD_le_card (Xs : Multiset FLeaf) : distinctD Xs ≤ Xs.card := Multiset.toFinset_card_le Xs

/-! ### The support bound -/

/-- **The support bound**: `y ≤ (n / A)^k` with `n` views. -/
theorem yM_toReal_le_card (Ms : Multiset (FTree → FLeaf)) :
    (yM Ms).toReal ≤ ((Ms.card : ℝ) / leavesR) ^ forsTrees := by
  unfold yM
  rw [ENNReal.toReal_prod]
  calc ∏ κ, (φF (Ms.map fun m => m κ)).toReal ≤ ∏ _κ : FTree, ((Ms.card : ℝ) / leavesR) := by
        refine Finset.prod_le_prod (fun κ _ => ENNReal.toReal_nonneg) fun κ _ => ?_
        rw [φF_toReal]
        have h := distinctD_le_card (Ms.map fun m => m κ)
        rw [Multiset.card_map] at h
        have : (distinctD (Ms.map fun m => m κ) : ℝ) ≤ Ms.card := by exact_mod_cast h
        exact div_le_div_of_nonneg_right this leavesR_pos.le
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, card_ftree]

/-! ### The occupancy law of one tree -/

/-- One more uniform leaf: the distinct count stays at `d` with probability `d / A`. -/
noncomputable def topD (f : ℕ → ℝ≥0∞) (d : ℕ) : ℝ≥0∞ :=
  leafInv * ((d : ℝ≥0∞) * f d + ((2 ^ forsHeight - d : ℕ) : ℝ≥0∞) * f (d + 1))

theorem distinctD_add (X : Multiset FLeaf) (u : FLeaf) :
    distinctD (X + {u}) = if u ∈ X.toFinset then distinctD X else distinctD X + 1 := by
  classical
  unfold distinctD
  rw [Multiset.toFinset_add, Multiset.toFinset_singleton, Finset.union_comm, ← Finset.insert_eq]
  split_ifs with h
  · rw [Finset.insert_eq_of_mem h]
  · rw [Finset.card_insert_of_notMem h]

theorem freshAvg_distinct (g : ℕ → ℝ≥0∞) (X : Multiset FLeaf) :
    freshAvg Finset.univ (fun u : FLeaf => g (distinctD (X + {u}))) = topD g (distinctD X) := by
  classical
  unfold freshAvg topD leafInv
  rw [Finset.card_univ, Fintype.card_fin]
  congr 1
  simp only [distinctD_add, apply_ite g]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have h1 : (Finset.univ.filter fun u : FLeaf => u ∈ X.toFinset) = X.toFinset := by ext; simp
  have h2 : (Finset.univ.filter fun u : FLeaf => u ∉ X.toFinset) = X.toFinsetᶜ := by ext; simp
  rw [h1, h2, Finset.card_compl, Fintype.card_fin]
  rfl

theorem avgN_distinct (f : ℕ → ℝ≥0∞) :
    ∀ n X, avgN (fun Xs => f (distinctD Xs)) n X = (topD^[n] f) (distinctD X)
  | 0, _ => rfl
  | n + 1, X => by
      simp only [avgN, avgN_distinct f n]
      rw [freshAvg_distinct, Function.iterate_succ_apply']

/-- The numerators over `A^n` of the law of the number of distinct leaves after `n` leaves. -/
def occW (A : ℕ) : ℕ → ℕ → ℕ
  | 0, d => if d = 0 then 1 else 0
  | n + 1, d => d * occW A n d + if d = 0 then 0 else (A + 1 - d) * occW A n (d - 1)

theorem occW_succ (A n d : ℕ) :
    occW A (n + 1) d = d * occW A n d + if d = 0 then 0 else (A + 1 - d) * occW A n (d - 1) := rfl

theorem occW_gt (A : ℕ) : ∀ n d, n < d → occW A n d = 0
  | 0, d, h => by simp only [occW]; rw [if_neg (by omega)]
  | n + 1, d, h => by
      rw [occW_succ, occW_gt A n d (by omega), occW_gt A n (d - 1) (by omega), if_neg (by omega)]
      simp

theorem occW_self (A : ℕ) : ∀ n, occW A n n = A.descFactorial n
  | 0 => by simp [occW]
  | n + 1 => by
      rw [occW_succ, occW_gt A n (n + 1) (by omega), if_neg (by omega), Nat.add_sub_cancel, occW_self A n,
        Nat.descFactorial_succ, Nat.add_sub_add_right]
      ring

theorem occW_pred (A : ℕ) : ∀ n, occW A (n + 1) n = (n + 1).choose 2 * A.descFactorial n
  | 0 => by simp [occW]
  | n + 1 => by
      rw [occW_succ, if_neg (by omega), Nat.add_sub_cancel, occW_self, occW_pred A n, Nat.descFactorial_succ,
        Nat.add_sub_add_right, Nat.choose_succ_succ (n + 1) 1, Nat.choose_one_right]
      ring

/-- **The occupancy law**: after `n` uniform leaves the distinct count is `d` with probability
`occW n d / A^n`. -/
theorem topD_iter_zero : ∀ n (f : ℕ → ℝ≥0∞), (topD^[n] f) 0 =
    ∑ d ∈ Finset.range (n + 1), (occW (2 ^ forsHeight) n d : ℝ≥0∞) * leafInv ^ n * f d
  | 0, f => by simp [occW]
  | n + 1, f => by
      rw [Function.iterate_succ_apply, topD_iter_zero n (topD f)]
      have h1 : ∀ d, (occW (2 ^ forsHeight) (n + 1) d : ℝ≥0∞) = (d : ℝ≥0∞) * occW (2 ^ forsHeight) n d +
          if d = 0 then 0 else ((2 ^ forsHeight + 1 - d : ℕ) : ℝ≥0∞) * occW (2 ^ forsHeight) n (d - 1) := by
        intro d
        rw [occW_succ]
        split_ifs <;> push_cast <;> ring
      simp only [h1, add_mul, Finset.sum_add_distrib]
      rw [Finset.sum_range_succ (fun d => (d : ℝ≥0∞) * _ * _ * _), occW_gt _ n (n + 1) (by omega),
        Finset.sum_range_succ' (fun d => (if d = 0 then 0 else _) * _ * _)]
      simp only [if_pos, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, Nat.add_sub_add_right, Nat.cast_zero,
        mul_zero, zero_mul, add_zero, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      unfold topD
      ring

/-! ### The three classes of a tree -/

/-- No repeat among the `n` leaves of a tree. -/
noncomputable def clsI0 (n : ℕ) (Xs : Multiset FLeaf) : ℝ≥0∞ := if distinctD Xs = n then 1 else 0

/-- Exactly one repeat. -/
noncomputable def clsI1 (n : ℕ) (Xs : Multiset FLeaf) : ℝ≥0∞ := if distinctD Xs = n - 1 then 1 else 0

/-- More than one repeat. -/
noncomputable def clsI2 (n : ℕ) (Xs : Multiset FLeaf) : ℝ≥0∞ :=
  if distinctD Xs ≠ n ∧ distinctD Xs ≠ n - 1 then 1 else 0

theorem distinctD_zero : distinctD (0 : Multiset FLeaf) = 0 := by simp [distinctD]

theorem avgN_ind (n e : ℕ) (he : e ≤ n) :
    avgN (fun Xs => if distinctD Xs = e then (1 : ℝ≥0∞) else 0) n 0 =
      (occW (2 ^ forsHeight) n e : ℝ≥0∞) * leafInv ^ n := by
  rw [avgN_distinct (fun d => if d = e then (1 : ℝ≥0∞) else 0) n 0, distinctD_zero, topD_iter_zero]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.2 (by omega))]

theorem avgN_clsI0 (n : ℕ) : avgN (clsI0 n) n 0 = (lawW0 forsHeight n : ℝ≥0∞) * leafInv ^ n := by
  rw [show clsI0 n = fun Xs => if distinctD Xs = n then (1 : ℝ≥0∞) else 0 from rfl, avgN_ind n n le_rfl,
    occW_self, lawW0]

theorem avgN_clsI1 (n : ℕ) (hn : 1 ≤ n) : avgN (clsI1 n) n 0 = (lawW1 forsHeight n : ℝ≥0∞) * leafInv ^ n := by
  rw [show clsI1 n = fun Xs => if distinctD Xs = n - 1 then (1 : ℝ≥0∞) else 0 from rfl,
    avgN_ind n (n - 1) (by omega)]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, occW_pred, lawW1, Nat.choose_two_right, Nat.add_sub_cancel]

theorem leafInv_ne_zero : leafInv ≠ 0 := by
  unfold leafInv; exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)

theorem leafInv_ne_top : leafInv ≠ ⊤ := by
  unfold leafInv; exact ENNReal.inv_ne_top.2 (by exact_mod_cast (Nat.two_pow_pos _).ne')

theorem pow_mul_leafInv (n : ℕ) : (((2 ^ forsHeight) ^ n : ℕ) : ℝ≥0∞) * leafInv ^ n = 1 := by
  rw [Nat.cast_pow, ← mul_pow, leafInv, ENNReal.mul_inv_cancel (by exact_mod_cast (Nat.two_pow_pos _).ne')
    (ENNReal.natCast_ne_top _), one_pow]

theorem clsI_sum (n : ℕ) (hn : 1 ≤ n) (Xs : Multiset FLeaf) : clsI0 n Xs + clsI1 n Xs + clsI2 n Xs = 1 := by
  unfold clsI0 clsI1 clsI2
  by_cases h0 : distinctD Xs = n
  · rw [if_pos h0, if_neg (by omega), if_neg (by omega)]; simp
  · by_cases h1 : distinctD Xs = n - 1
    · rw [if_neg h0, if_pos h1, if_neg (by omega)]; simp
    · rw [if_neg h0, if_neg h1, if_pos ⟨h0, h1⟩]; simp

theorem avgN_clsI_sum (n : ℕ) (hn : 1 ≤ n) :
    (lawW0 forsHeight n : ℝ≥0∞) * leafInv ^ n + (lawW1 forsHeight n : ℝ≥0∞) * leafInv ^ n +
      avgN (clsI2 n) n 0 = 1 := by
  rw [← avgN_clsI0, ← avgN_clsI1 n hn, ← avgN_add, ← avgN_add]
  simp only [clsI_sum n hn]
  exact avgN_const 1 n 0

theorem lawW01_le (n : ℕ) (hn : 1 ≤ n) : lawW0 forsHeight n + lawW1 forsHeight n ≤ (2 ^ forsHeight) ^ n := by
  have h := avgN_clsI_sum n hn
  have h' : ((lawW0 forsHeight n + lawW1 forsHeight n : ℕ) : ℝ≥0∞) * leafInv ^ n ≤
      (((2 ^ forsHeight) ^ n : ℕ) : ℝ≥0∞) * leafInv ^ n := by
    rw [pow_mul_leafInv, ← h, Nat.cast_add, add_mul]
    exact le_self_add
  exact_mod_cast (ENNReal.mul_le_mul_iff_left (pow_ne_zero _ leafInv_ne_zero) (pow_ne_top leafInv_ne_top)).1 h'

theorem avgN_clsI2 (n : ℕ) (hn : 1 ≤ n) : avgN (clsI2 n) n 0 = (lawW2 forsHeight n : ℝ≥0∞) * leafInv ^ n := by
  have h := avgN_clsI_sum n hn
  have hle := lawW01_le n hn
  rw [lawW2, Nat.sub_sub, ENNReal.natCast_sub, ENNReal.sub_mul (fun _ _ => pow_ne_top leafInv_ne_top),
    pow_mul_leafInv, Nat.cast_add, add_mul]
  refine ENNReal.eq_sub_of_add_eq (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (pow_ne_top leafInv_ne_top), ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (pow_ne_top leafInv_ne_top)⟩) ?_
  rw [add_comm]
  exact h

/-! ### Counting the classes -/

theorem prod_three {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M] (t t2 : Finset ι) (ht : t2 ⊆ t)
    (x0 x1 x2 : M) :
    ∏ i, (if i ∈ t2 then x2 else if i ∈ t then x1 else x0) =
      x2 ^ t2.card * x1 ^ (t.card - t2.card) * x0 ^ (Fintype.card ι - t.card) := by
  rw [Finset.prod_ite, Finset.prod_ite, Finset.prod_const, Finset.prod_const, Finset.prod_const,
    Finset.filter_filter, Finset.filter_filter]
  have e1 : (Finset.univ.filter fun i => i ∈ t2) = t2 := by ext; simp
  have e2 : (Finset.univ.filter fun i => i ∉ t2 ∧ i ∈ t) = t \ t2 := by ext; simp [and_comm]
  have e3 : (Finset.univ.filter fun i => i ∉ t2 ∧ i ∉ t) = tᶜ := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    exact ⟨fun h => h.2, fun h => ⟨fun h2 => h (ht h2), h⟩⟩
  rw [e1, e2, e3, Finset.card_sdiff_of_subset ht, Finset.card_compl, mul_assoc]

theorem lawY_le_over (k n T w v : ℕ) (hTw : T ≤ w) (hwk : w ≤ k) (hvw : v ≤ w) :
    lawY k n w v ≤ lawY k n T 0 := by
  unfold lawY
  calc n ^ (k - w) * (n - 1) ^ (w - v) * (n - 2) ^ v ≤ n ^ (k - w) * (n - 1) ^ (w - v) * (n - 1) ^ v :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) v)
    _ = n ^ (k - w) * ((n - 1) ^ (w - T) * (n - 1) ^ T) := by
        rw [mul_assoc, ← pow_add, ← pow_add]; congr 2; omega
    _ ≤ n ^ (k - w) * (n ^ (w - T) * (n - 1) ^ T) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _))
    _ = n ^ (k - T) * (n - 1) ^ (T - 0) * (n - 2) ^ 0 := by
        rw [← mul_assoc, ← pow_add, pow_zero, mul_one, Nat.sub_zero]; congr 2; omega

theorem chooseF_eq (n r : ℕ) (h : r ≤ n) : chooseF n r = n.choose r :=
  (Nat.choose_eq_factorial_div_factorial h).symm

theorem list_sum_range' {M : Type*} [AddCommMonoid M] (f : ℕ → M) : ∀ n,
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by
      rw [List.range_succ, List.map_append, List.sum_append, list_sum_range' f n, Finset.sum_range_succ]
      simp

theorem lawStates_sum {M : Type*} [AddCommMonoid M] (g : ℕ × ℕ → M) :
    ∀ T, ((lawStates T).map g).sum = ∑ w ∈ Finset.range T, ∑ v ∈ Finset.range (w + 1), g (w, v)
  | 0 => by simp [lawStates]
  | T + 1 => by
      rw [Finset.sum_range_succ, ← lawStates_sum g T, ← list_sum_range']
      simp [lawStates, List.range_succ, List.flatMap_append, List.map_flatMap, Function.comp_def]

/-- The class weights add up to `A^(n k)`. -/
theorem lawWt_total (k n : ℕ) (hn : 1 ≤ n) :
    ∑ w ∈ Finset.range (k + 1), ∑ v ∈ Finset.range (w + 1), lawWt k forsHeight n w v =
      (2 ^ forsHeight) ^ (n * k) := by
  have hW : lawW0 forsHeight n + lawW1 forsHeight n + lawW2 forsHeight n = (2 ^ forsHeight) ^ n := by
    have := lawW01_le n hn; unfold lawW2; omega
  rw [pow_mul, ← hW, show lawW0 forsHeight n + lawW1 forsHeight n + lawW2 forsHeight n =
    (lawW2 forsHeight n + lawW1 forsHeight n) + lawW0 forsHeight n by ring, add_pow]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [add_pow, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hw' := Finset.mem_range.1 hw
  have hv' := Finset.mem_range.1 hv
  unfold lawWt
  rw [chooseF_eq _ _ (by omega), chooseF_eq _ _ (by omega)]
  simp only [Nat.cast_id]
  ring

/-! ### Averages over multisets of a given size -/

theorem avgN_mono_card {U : Type} [Fintype U] [Nonempty U] {φ ψ : Multiset U → ℝ≥0∞} :
    ∀ n X0, (∀ X : Multiset U, X.card = n + X0.card → φ X ≤ ψ X) → avgN φ n X0 ≤ avgN ψ n X0
  | 0, X0, h => h X0 (by simp)
  | n + 1, X0, h => freshAvg_mono _ fun u _ => avgN_mono_card n _ fun X hX => h X (by
      rw [hX, Multiset.card_add, Multiset.card_singleton]; omega)

theorem avgN_finset_sum {U β : Type} [Fintype U] [Nonempty U] (s : Finset β) (φ : β → Multiset U → ℝ≥0∞) :
    ∀ n X, avgN (fun Y => ∑ b ∈ s, φ b Y) n X = ∑ b ∈ s, avgN (φ b) n X
  | 0, _ => rfl
  | n + 1, X => by
      simp only [avgN, avgN_finset_sum s φ n]
      unfold freshAvg
      rw [Finset.sum_comm, Finset.mul_sum]

/-! ### The expansion over the classes -/

/-- The factor of a tree in the expansion over the classes: more than one repeat on `t2`, one repeat
on `t \ t2`, none off `t`. -/
noncomputable def clsPsi (n : ℕ) (t t2 : Finset FTree) (κ : FTree) : Multiset FLeaf → ℝ≥0∞ :=
  if κ ∈ t2 then clsI2 n else if κ ∈ t then clsI1 n else clsI0 n

/-- The representative of the class `(w, v)`, the one of `(T, 0)` once `w ≥ T`. -/
noncomputable def clsRep (n T w v : ℕ) : ℝ :=
  κE.toReal * ((if w < T then lawY forsTrees n w v else lawY forsTrees n T 0 : ℕ) : ℝ) / leavesR ^ forsTrees

/-- **Pointwise**: with `n` views, `F(y)` is at most the sum over the classes of `F` at their
representatives times the indicator of the class. -/
theorem classLaw_pointwise (n T : ℕ) (F : ℝ → ℝ) (hFm : Monotone F)
    (Ms : Multiset (FTree → FLeaf)) (hMs : Ms.card = n) :
    ENNReal.ofReal (F (κE.toReal * (yM Ms).toReal)) ≤
      ∑ t ∈ (Finset.univ : Finset FTree).powerset, ∑ t2 ∈ t.powerset,
        ENNReal.ofReal (F (clsRep n T t.card t2.card)) * ∏ κ, clsPsi n t t2 κ (Ms.map fun m => m κ) := by
  classical
  have hD : ∀ κ, distinctD (Ms.map fun m => m κ) ≤ n := fun κ => by
    have := distinctD_le_card (Ms.map fun m => m κ); rwa [Multiset.card_map, hMs] at this
  set t := Finset.univ.filter fun κ => distinctD (Ms.map fun m => m κ) ≠ n with htdef
  set t2 := Finset.univ.filter fun κ =>
    distinctD (Ms.map fun m => m κ) ≠ n ∧ distinctD (Ms.map fun m => m κ) ≠ n - 1 with ht2def
  have ht2 : t2 ⊆ t := fun κ h => by
    simp only [t, t2, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; exact h.1
  have hprod : ∏ κ, clsPsi n t t2 κ (Ms.map fun m => m κ) = 1 := by
    refine Finset.prod_eq_one fun κ _ => ?_
    unfold clsPsi
    by_cases h2 : κ ∈ t2
    · rw [if_pos h2]
      simp only [t2, Finset.mem_filter, Finset.mem_univ, true_and] at h2
      unfold clsI2; exact if_pos h2
    · rw [if_neg h2]
      by_cases h1 : κ ∈ t
      · rw [if_pos h1]
        simp only [t, t2, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        unfold clsI1; exact if_pos (by by_contra h; exact h2 ⟨h1, h⟩)
      · rw [if_neg h1]
        simp only [t, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at h1
        unfold clsI0; exact if_pos h1
  have hr : ∀ κ, distinctD (Ms.map fun m => m κ) ≤ if κ ∈ t2 then n - 2 else if κ ∈ t then n - 1 else n := by
    intro κ
    have := hD κ
    split_ifs with h2 h1
    · simp only [t2, Finset.mem_filter, Finset.mem_univ, true_and] at h2; omega
    · simp only [t, t2, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2; omega
    · exact this
  have hY : lawY forsTrees n t.card t2.card = ∏ κ, (if κ ∈ t2 then n - 2 else if κ ∈ t then n - 1 else n) := by
    rw [prod_three t t2 ht2, card_ftree, lawY]; ring
  have hy : (yM Ms).toReal ≤ ((lawY forsTrees n t.card t2.card : ℕ) : ℝ) / leavesR ^ forsTrees := by
    unfold yM
    rw [ENNReal.toReal_prod]
    calc ∏ κ, (φF (Ms.map fun m => m κ)).toReal = ∏ κ, ((distinctD (Ms.map fun m => m κ) : ℝ) / leavesR) :=
          Finset.prod_congr rfl fun κ _ => φF_toReal _
      _ ≤ ∏ κ, (((if κ ∈ t2 then n - 2 else if κ ∈ t then n - 1 else n : ℕ) : ℝ) / leavesR) :=
          Finset.prod_le_prod (fun _ _ => div_nonneg (Nat.cast_nonneg _) leavesR_pos.le) fun κ _ =>
            div_le_div_of_nonneg_right (by exact_mod_cast hr κ) leavesR_pos.le
      _ = _ := by rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, card_ftree, hY, Nat.cast_prod]
  have hrep : lawY forsTrees n t.card t2.card ≤
      if t.card < T then lawY forsTrees n t.card t2.card else lawY forsTrees n T 0 := by
    split_ifs with h
    · exact le_rfl
    · exact lawY_le_over _ _ _ _ _ (by omega)
        (by have := Finset.card_le_univ t; rwa [card_ftree] at this) (Finset.card_le_card ht2)
  have hF : F (κE.toReal * (yM Ms).toReal) ≤ F (clsRep n T t.card t2.card) := by
    apply hFm
    unfold clsRep
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left (hy.trans (div_le_div_of_nonneg_right ?_ (pow_pos leavesR_pos _).le)) ENNReal.toReal_nonneg
    exact_mod_cast hrep
  calc ENNReal.ofReal (F (κE.toReal * (yM Ms).toReal))
      ≤ ENNReal.ofReal (F (clsRep n T t.card t2.card)) * ∏ κ, clsPsi n t t2 κ (Ms.map fun m => m κ) := by
        rw [hprod, mul_one]; exact ENNReal.ofReal_le_ofReal hF
    _ ≤ ∑ t2' ∈ t.powerset, ENNReal.ofReal (F (clsRep n T t.card t2'.card)) *
          ∏ κ, clsPsi n t t2' κ (Ms.map fun m => m κ) :=
        Finset.single_le_sum (f := fun t2' => ENNReal.ofReal (F (clsRep n T t.card t2'.card)) *
          ∏ κ, clsPsi n t t2' κ (Ms.map fun m => m κ)) (fun _ _ => bot_le) (Finset.mem_powerset.2 ht2)
    _ ≤ _ :=
        Finset.single_le_sum (f := fun t' => ∑ t2' ∈ t'.powerset, ENNReal.ofReal (F (clsRep n T t'.card t2'.card)) *
          ∏ κ, clsPsi n t' t2' κ (Ms.map fun m => m κ)) (fun _ _ => bot_le)
          (Finset.mem_powerset.2 (Finset.subset_univ t))

/-! ### The class law -/

/-- **The class law.** For `F` monotone and nonnegative, the average of `F(y)` over `n ≥ 2` views is
at most the sum over the classes `w < T` of their weights times `F` at their representatives, plus
the rest of the mass times `F` at the representative of `(T, 0)`. -/
theorem avgN_classLaw (k a n T : ℕ) (hk : forsTrees = k) (ha : forsHeight = a) (hn : 2 ≤ n)
    (hT : T ≤ k) (F : ℝ → ℝ) (hF0 : ∀ x, 0 ≤ F x) (hFm : Monotone F) :
    avgN (fun Ms => ENNReal.ofReal (F (κE.toReal * (yM Ms).toReal))) n 0 ≤
      ENNReal.ofReal ((((lawStates T).map fun p =>
          (lawWt k a n p.1 p.2 : ℝ) * F (κE.toReal * (lawY k n p.1 p.2 : ℝ) / (2 ^ a : ℝ) ^ k)).sum +
        (((2 ^ a) ^ (n * k) - lawMass k a n T : ℕ) : ℝ) * F (κE.toReal * (lawY k n T 0 : ℝ) / (2 ^ a : ℝ) ^ k)) /
        ((2 ^ a : ℝ) ^ (n * k))) := by
  subst hk ha
  have hn1 : 1 ≤ n := by omega
  set L : ℝ := (2 : ℝ) ^ forsHeight with hL
  have hL0 : 0 < L := by positivity
  -- pointwise, then average over the views
  have h1 : avgN (fun Ms : Multiset (FTree → FLeaf) => ENNReal.ofReal (F (κE.toReal * (yM Ms).toReal))) n 0 ≤
      avgN (fun Ms : Multiset (FTree → FLeaf) => ∑ t ∈ (Finset.univ : Finset FTree).powerset, ∑ t2 ∈ t.powerset,
        ENNReal.ofReal (F (clsRep n T t.card t2.card)) * ∏ κ, clsPsi n t t2 κ (Ms.map fun m => m κ)) n 0 := by
    refine avgN_mono_card n 0 fun X hX => classLaw_pointwise n T F hFm X ?_
    rw [hX, Multiset.card_zero, add_zero]
  refine h1.trans (le_of_eq ?_)
  simp only [avgN_finset_sum, avgN_const_mul, avgN_prod_coords, Multiset.map_zero]
  have hpsi : ∀ (t t2 : Finset FTree) (κ : FTree), avgN (clsPsi n t t2 κ) n 0 =
      if κ ∈ t2 then (lawW2 forsHeight n : ℝ≥0∞) * leafInv ^ n else if κ ∈ t then
        (lawW1 forsHeight n : ℝ≥0∞) * leafInv ^ n else (lawW0 forsHeight n : ℝ≥0∞) * leafInv ^ n := by
    intro t t2 κ
    unfold clsPsi
    split_ifs
    · exact avgN_clsI2 n hn1
    · exact avgN_clsI1 n hn1
    · exact avgN_clsI0 n
  simp only [hpsi]
  -- the term of the classes `(w, v)`
  set G : ℕ → ℕ → ℝ≥0∞ := fun w v => ENNReal.ofReal (F (clsRep n T w v)) *
    (((lawW2 forsHeight n : ℝ≥0∞) * leafInv ^ n) ^ v * ((lawW1 forsHeight n : ℝ≥0∞) * leafInv ^ n) ^ (w - v) *
      ((lawW0 forsHeight n : ℝ≥0∞) * leafInv ^ n) ^ (forsTrees - w)) with hG
  have e0 : ∀ t ∈ (Finset.univ : Finset FTree).powerset, ∑ t2 ∈ t.powerset, ENNReal.ofReal (F (clsRep n T t.card t2.card)) *
      ∏ κ, (if κ ∈ t2 then (lawW2 forsHeight n : ℝ≥0∞) * leafInv ^ n else if κ ∈ t then
        (lawW1 forsHeight n : ℝ≥0∞) * leafInv ^ n else (lawW0 forsHeight n : ℝ≥0∞) * leafInv ^ n) =
      ∑ v ∈ Finset.range (t.card + 1), t.card.choose v • G t.card v := by
    intro t _
    rw [← Finset.sum_powerset_apply_card (G t.card)]
    refine Finset.sum_congr rfl fun t2 ht2 => ?_
    rw [prod_three t t2 (Finset.mem_powerset.1 ht2), card_ftree]
  rw [Finset.sum_congr rfl e0,
    Finset.sum_powerset_apply_card (fun w => ∑ v ∈ Finset.range (w + 1), w.choose v • G w v),
    Finset.card_univ, card_ftree]
  -- the weights
  have hp : ∀ w v, v ≤ w → w ≤ forsTrees → forsTrees.choose w • (w.choose v • G w v) =
      (lawWt forsTrees forsHeight n w v : ℝ≥0∞) * leafInv ^ (n * forsTrees) *
        ENNReal.ofReal (F (clsRep n T w v)) := by
    intro w v hvw hwk
    have e : (leafInv ^ n) ^ v * (leafInv ^ n) ^ (w - v) * (leafInv ^ n) ^ (forsTrees - w) =
        leafInv ^ (n * forsTrees) := by
      rw [← pow_add, ← pow_add, ← pow_mul]; congr 2; omega
    rw [hG, lawWt, chooseF_eq _ _ hwk, chooseF_eq _ _ hvw, ← e]
    simp only [nsmul_eq_mul, mul_pow]
    push_cast
    ring
  have hsum : ∀ w ∈ Finset.range (forsTrees + 1), forsTrees.choose w • ∑ v ∈ Finset.range (w + 1), w.choose v • G w v =
      ∑ v ∈ Finset.range (w + 1), (lawWt forsTrees forsHeight n w v : ℝ≥0∞) * leafInv ^ (n * forsTrees) *
        ENNReal.ofReal (F (clsRep n T w v)) := by
    intro w hw
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun v hv => hp w v (by have := Finset.mem_range.1 hv; omega)
      (by have := Finset.mem_range.1 hw; omega)
  rw [Finset.sum_congr rfl hsum, ← Finset.sum_range_add_sum_Ico _ (by omega : T ≤ forsTrees + 1)]
  -- the overflow
  set FT : ℝ := F (κE.toReal * (lawY forsTrees n T 0 : ℝ) / L ^ forsTrees) with hFT
  have hover : ∑ w ∈ Finset.Ico T (forsTrees + 1), ∑ v ∈ Finset.range (w + 1),
      (lawWt forsTrees forsHeight n w v : ℝ≥0∞) * leafInv ^ (n * forsTrees) * ENNReal.ofReal (F (clsRep n T w v)) =
      (((2 ^ forsHeight) ^ (n * forsTrees) - lawMass forsTrees forsHeight n T : ℕ) : ℝ≥0∞) *
        leafInv ^ (n * forsTrees) * ENNReal.ofReal FT := by
    have hrep : ∀ w ∈ Finset.Ico T (forsTrees + 1), ∀ v, clsRep n T w v = κE.toReal * (lawY forsTrees n T 0 : ℝ) /
        L ^ forsTrees := by
      intro w hw v
      rw [clsRep, if_neg (by have := Finset.mem_Ico.1 hw; omega), hL, leavesR]
    have hmass : ∑ w ∈ Finset.Ico T (forsTrees + 1), ∑ v ∈ Finset.range (w + 1), lawWt forsTrees forsHeight n w v =
        (2 ^ forsHeight) ^ (n * forsTrees) - lawMass forsTrees forsHeight n T := by
      have h := lawWt_total forsTrees n hn1
      rw [← Finset.sum_range_add_sum_Ico _ (by omega : T ≤ forsTrees + 1)] at h
      rw [lawMass, lawStates_sum (fun p => lawWt forsTrees forsHeight n p.1 p.2)]
      dsimp only
      omega
    rw [← hmass, Nat.cast_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [Nat.cast_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hrep w hw v]
  rw [hover]
  -- to reals
  have hLi : leafInv ^ (n * forsTrees) = ENNReal.ofReal (1 / L ^ (n * forsTrees)) := by
    rw [leafInv, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one, one_div, ← ENNReal.inv_pow,
      ENNReal.ofReal_pow hL0.le, hL, ENNReal.ofReal_pow (by norm_num)]
    push_cast
    rw [ENNReal.ofReal_ofNat]
  have key : ∀ (x : ℕ) (y : ℝ), (x : ℝ≥0∞) * leafInv ^ (n * forsTrees) * ENNReal.ofReal (F y) =
      ENNReal.ofReal ((x : ℝ) * F y * (1 / L ^ (n * forsTrees))) := by
    intro x y
    rw [hLi, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) (by positivity))]
    ring_nf
  have hrep' : ∀ w ∈ Finset.range T, ∀ v, clsRep n T w v = κE.toReal * (lawY forsTrees n w v : ℝ) /
      L ^ forsTrees := by
    intro w hw v
    rw [clsRep, if_pos (Finset.mem_range.1 hw), hL, leavesR]
  have hnn : ∀ (x : ℕ) (y : ℝ), 0 ≤ (x : ℝ) * F y * (1 / L ^ (n * forsTrees)) := fun x y =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hF0 y)) (by positivity)
  simp only [key]
  rw [hFT, key]
  have hin : ∀ w ∈ Finset.range T, ∑ v ∈ Finset.range (w + 1),
      ENNReal.ofReal ((lawWt forsTrees forsHeight n w v : ℝ) * F (clsRep n T w v) * (1 / L ^ (n * forsTrees))) =
      ENNReal.ofReal (∑ v ∈ Finset.range (w + 1),
        (lawWt forsTrees forsHeight n w v : ℝ) * F (clsRep n T w v) * (1 / L ^ (n * forsTrees))) :=
    fun w _ => (ENNReal.ofReal_sum_of_nonneg fun v _ => hnn _ _).symm
  rw [Finset.sum_congr rfl hin, ← ENNReal.ofReal_sum_of_nonneg (fun w _ => Finset.sum_nonneg fun v _ => hnn _ _),
    ← ENNReal.ofReal_add (Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun v _ => hnn _ _) (hnn _ _)]
  congr 1
  rw [lawStates_sum (fun p => (lawWt forsTrees forsHeight n p.1 p.2 : ℝ) *
    F (κE.toReal * (lawY forsTrees n p.1 p.2 : ℝ) / (2 ^ forsHeight : ℝ) ^ forsTrees)), add_div, Finset.sum_div]
  dsimp only
  congr 1
  · refine Finset.sum_congr rfl fun w hw => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hrep' w hw v, mul_one_div]
  · rw [mul_one_div]

end FORS.Security.H0
