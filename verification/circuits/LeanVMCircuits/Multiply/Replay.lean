module

public import LeanVMCircuits.Multiply.Csa

@[expose] public section

/-!
The plan replayed on bits: the multiplier's output is `a b` modulo `2^n`.

`check n` replays the plan on the rows' masks, checking every step's conditions (`StepOK`) and the ripple's
(`RippleOK`); it holds for both widths by kernel evaluation. Given it, the rows' total over the live rows stays `a b`
modulo `2^n` through every step, and the ripple's output is that total.
-/

namespace LeanVMCircuits.Multiply

open BigOperators Finset

/-- A step's conditions at every position below 128, on masks below `2^128`. -/
def stepCheck (n : ℕ) (s : Csa) (px py pz : ℕ) : Bool :=
  (List.range 128).all fun p =>
    let c := (if bit px p then 1 else 0) + (if bit py p then 1 else 0) + (if bit pz p then 1 else 0)
    (!(decide (p + 1 < n) && decide (2 ≤ c)) || bit s.products p || bit s.moveY p || bit s.moveZ p) &&
      (!bit s.products p || decide (p + 1 < n)) &&
      (!bit s.moveZ p || (bit pz p && (bit px p != bit py p) && !bit s.products p)) &&
      (!bit s.moveY p || (bit px p && bit py p && !bit pz p && !bit s.moveZ p && !bit s.products p)) &&
      (!(decide (0 < p) && bit s.products (p - 1)) || (!bit s.moveZ p && !bit s.moveY p))

/-- The carries of the ripple addition, as `Multiplier::build` takes them. -/
def carries (n px py : ℕ) : ℕ :=
  ((List.range n).foldl (fun (cm, carryIn) p =>
    let c := (if bit px p then 1 else 0) + (if bit py p then 1 else 0) + (if carryIn then 1 else 0)
    if p + 1 < n && 2 ≤ c then (cm ||| 2 ^ p, true) else (cm, false)) (0, false)).1

def rippleCheck (n cm px py : ℕ) : Bool :=
  (List.range 128).all fun p =>
    let c := (if bit px p then 1 else 0) + (if bit py p then 1 else 0) +
      (if decide (0 < p) && bit cm (p - 1) then 1 else 0)
    (!(decide (p + 1 < n) && decide (2 ≤ c)) || bit cm p) && (!bit cm p || decide (p + 1 < n))

/-- The rows a step leaves untouched. -/
def keep (s : Csa) (r : ℕ) : Bool := r ≠ s.x && r ≠ s.y && r ≠ s.z

/-- The plan's steps replayed on the live rows and their masks, every condition checked. -/
def checkFrom (n : ℕ) : List Csa → List ℕ → (ℕ → ℕ) → Bool
  | [], live, present =>
    live.length == 2 && (live.all fun r => decide (present r < 2 ^ 128)) &&
      rippleCheck n (carries n (present (live.getD 0 0)) (present (live.getD 1 0))) (present (live.getD 0 0))
        (present (live.getD 1 0)) && decide (carries n (present (live.getD 0 0)) (present (live.getD 1 0)) < 2 ^ 128)
  | s :: steps, live, present =>
    live.contains s.x && live.contains s.y && live.contains s.z && s.x != s.y && s.x != s.z && s.y != s.z &&
      (live.all fun r => decide (present r < 2 ^ 128)) &&
      decide (s.products < 2 ^ 128) && decide (s.moveY < 2 ^ 128) && decide (s.moveZ < 2 ^ 128) &&
      stepCheck n s (present s.x) (present s.y) (present s.z) &&
      checkFrom n steps (live.filter (keep s) ++ [s.x, s.y])
        (fun r => if r = s.x then present s.x ||| present s.y ||| present s.z
          else if r = s.y then (s.products <<< 1) ||| (s.moveY ||| s.moveZ) else present r)

/-- The live rows after the steps. -/
def liveAfter : List Csa → List ℕ → List ℕ
  | [], live => live
  | s :: steps, live => liveAfter steps (live.filter (keep s) ++ [s.x, s.y])

/-- The plan's conditions for an `n`-bit product, from the initial rows, and its last two rows. -/
def check (n : ℕ) : Bool :=
  checkFrom n (plan n).1 (List.range nRows) (initialPresent n) &&
    (liveAfter (plan n).1 (List.range nRows) == [(plan n).2.1, (plan n).2.2])


/-! Masks. -/

theorem bit_or (a b p : ℕ) : bit (a ||| b) p = (bit a p || bit b p) := Nat.testBit_or a b p

theorem bit_two_pow (p q : ℕ) : bit (2 ^ q) p = decide (q = p) := by
  simp [bit, Nat.testBit_two_pow]

theorem maskOf_bit (n : ℕ) (f : ℕ → Bool) (p : ℕ) : bit (maskOf n f) p = (decide (p < n) && f p) := by
  unfold maskOf
  suffices h : ∀ m k, bit ((List.range k).foldl (fun m p => if f p then m ||| 2 ^ p else m) m) p =
      (bit m p || (decide (p < k) && f p)) by
    rw [h]; simp [bit]
  intro m k
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    split
    · rename_i hf
      rw [bit_or, ih, bit_two_pow]
      by_cases hk : k = p
      · subst hk; simp [hf]
      · have : (p < k + 1) = (p < k) := by apply propext; omega
        simp [hk, this]
    · rename_i hf
      rw [ih]
      by_cases hk : k = p
      · subst hk; simp [hf]
      · have : (p < k + 1) = (p < k) := by apply propext; omega
        simp [this]

theorem bit_lt (m p : ℕ) (hm : m < 2 ^ 128) (hp : 128 ≤ p) : bit m p = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) hp))


attribute [local irreducible] bit

/-- A step's checked conditions are its conditions. -/
theorem stepOK_of_check (n : ℕ) (s : Csa) (px py pz : ℕ) (h : stepCheck n s px py pz = true)
    (hx : px < 2 ^ 128) (hy : py < 2 ^ 128) (hz : pz < 2 ^ 128) (hp : s.products < 2 ^ 128)
    (hmy : s.moveY < 2 ^ 128) (hmz : s.moveZ < 2 ^ 128) (hn : n ≤ 128) : StepOK n s px py pz := by
  have hall := fun p (hp : p < 128) => List.all_eq_true.mp h p (List.mem_range.mpr hp)
  simp only [Bool.and_eq_true] at hall
  -- Past bit 127 every mask is zero.
  have zx := fun p (hp : 128 ≤ p) => bit_lt px p hx hp
  have zy := fun p (hp : 128 ≤ p) => bit_lt py p hy hp
  have zz := fun p (hp : 128 ≤ p) => bit_lt pz p hz hp
  have zp := fun p (hq : 128 ≤ p) => bit_lt _ p hp hq
  have zmy := fun p (hp : 128 ≤ p) => bit_lt _ p hmy hp
  have zmz := fun p (hp : 128 ≤ p) => bit_lt _ p hmz hp
  have low : ∀ p, bit s.products p → p + 1 < n := by
    intro p hb
    by_cases hp' : p < 128
    · have h2 := (hall p hp').1.1.1.2
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h2
      rcases h2 with h2 | h2
      · simp_all
      · exact h2
    · simp_all [zp p (by omega)]
  refine ⟨fun p hpn hc => ?_, low, fun p hb => ?_, fun p hb => ?_, fun q hq hb => ?_⟩
  · have hp' : p < 128 := by omega
    have h1 := (hall p hp').1.1.1.1
    rw [show decide (p + 1 < n) = true by simpa using hpn, show decide (2 ≤ _) = true by simpa using hc] at h1
    revert h1
    cases bit s.products p <;> cases bit s.moveY p <;> cases bit s.moveZ p <;> simp
  · by_cases hp' : p < 128
    · have h3 := (hall p hp').1.1.2
      rw [hb] at h3
      cases hz' : bit pz p <;> cases hx' : bit px p <;> cases hy' : bit py p <;>
        cases hpr : bit s.products p <;> simp_all
    · simp_all [zmz p (by omega)]
  · by_cases hp' : p < 128
    · have h3 := (hall p hp').1.2
      rw [hb] at h3
      cases hz' : bit pz p <;> cases hx' : bit px p <;> cases hy' : bit py p <;>
        cases hpr : bit s.products p <;> cases hm : bit s.moveZ p <;> simp_all
    · simp_all [zmy p (by omega)]
  · have := low (q - 1) hb
    have hq' : q < 128 := by omega
    have h3 := (hall q hq').2
    rw [hb, show decide (0 < q) = true by simpa using hq] at h3
    revert h3
    cases bit s.moveZ q <;> cases bit s.moveY q <;> simp


theorem rippleOK_of_check (n cm px py : ℕ) (h : rippleCheck n cm px py = true) (hcm : cm < 2 ^ 128)
    (hn : n ≤ 128) : RippleOK n cm px py := by
  have hall := fun p (hp : p < 128) => List.all_eq_true.mp h p (List.mem_range.mpr hp)
  simp only [Bool.and_eq_true] at hall
  refine ⟨fun p hpn hc => ?_, fun p hb => ?_⟩
  · have h1 := (hall p (by omega)).1
    rw [show decide (p + 1 < n) = true by simpa using hpn, show decide (2 ≤ _) = true by simpa using hc] at h1
    simpa using h1
  · by_cases hp : p < 128
    · have h2 := (hall p hp).2
      rw [hb] at h2
      simpa using h2
    · rw [bit_lt cm p hcm (by omega)] at hb; cases hb


/-! The replay on bits. -/

/-- A step's rows: the sum row in `x`, the carry row in `y`. -/
def stepRows (s : Csa) (rows : ℕ → ℕ → Bit) (r : ℕ) : ℕ → Bit :=
  if r = s.x then sumRow s (rows s.x) (rows s.y) (rows s.z)
  else if r = s.y then carryRow s (rows s.x) (rows s.y) (rows s.z) else rows r

def stepPresent (s : Csa) (present : ℕ → ℕ) (r : ℕ) : ℕ :=
  if r = s.x then present s.x ||| present s.y ||| present s.z
  else if r = s.y then (s.products <<< 1) ||| (s.moveY ||| s.moveZ) else present r

def rowsFrom : List Csa → (ℕ → ℕ → Bit) → ℕ → ℕ → Bit
  | [], rows => rows
  | s :: steps, rows => rowsFrom steps (stepRows s rows)

def presentFrom : List Csa → (ℕ → ℕ) → ℕ → ℕ
  | [], present => present
  | s :: steps, present => presentFrom steps (stepPresent s present)

theorem sumRow_zeroOff (s : Csa) (x y z : ℕ → Bit) (px py pz : ℕ) (hx : ZeroOff x px) (hy : ZeroOff y py)
    (hz : ZeroOff z pz) : ZeroOff (sumRow s x y z) (px ||| py ||| pz) := by
  intro p hp
  simp only [bit_or, Bool.or_eq_false_iff] at hp
  rw [sumRow, hx p hp.1.1, hy p hp.1.2, hz p hp.2]
  simp

theorem carryRow_zeroOff (s : Csa) (x y z : ℕ → Bit) :
    ZeroOff (carryRow s x y z) ((s.products <<< 1) ||| (s.moveY ||| s.moveZ)) := by
  intro q hq
  simp only [bit_or, Bool.or_eq_false_iff] at hq
  have hshift : bit (s.products <<< 1) q = (decide (0 < q) && bit s.products (q - 1)) := by
    simp only [bit, Nat.testBit_shiftLeft]
    by_cases h : 1 ≤ q
    · simp [h, show 0 < q by omega]
    · simp [h, show ¬ 0 < q by omega]
  rw [hshift] at hq
  unfold carryRow
  rw [if_neg (by simpa using hq.1), if_neg (by simp [hq.2.2]), if_neg (by simp [hq.2.1])]


theorem sum_three (L : List ℕ) (s : Csa) (hx : s.x ∈ L) (hy : s.y ∈ L) (hz : s.z ∈ L) (hxy : s.x ≠ s.y)
    (hxz : s.x ≠ s.z) (hyz : s.y ≠ s.z) (f : ℕ → ℤ) :
    ∑ r ∈ L.toFinset, f r = ∑ r ∈ (L.filter (keep s)).toFinset, f r + f s.x + f s.y + f s.z := by
  rw [← Finset.sum_filter_add_sum_filter_not L.toFinset (fun r => keep s r = true), List.toFinset_filter]
  have : L.toFinset.filter (fun r => ¬ keep s r = true) = {s.x, s.y, s.z} := by
    ext r
    simp only [mem_filter, List.mem_toFinset, keep, Bool.and_eq_true, decide_eq_true_eq, not_and, not_not,
      mem_insert, mem_singleton]
    constructor
    · rintro ⟨_, h⟩
      by_cases h1 : r = s.x
      · exact Or.inl h1
      · by_cases h2 : r = s.y
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (h ⟨h1, h2⟩))
    · rintro (rfl | rfl | rfl)
      · exact ⟨hx, fun h => absurd rfl h.1⟩
      · exact ⟨hy, fun h => absurd rfl h.2⟩
      · exact ⟨hz, fun _ => rfl⟩
  rw [this, sum_insert (by simp [hxy, hxz]), sum_insert (by simp [hyz]), sum_singleton]
  ring

theorem sum_two (L : List ℕ) (s : Csa) (hxy : s.x ≠ s.y) (f : ℕ → ℤ) :
    ∑ r ∈ (L.filter (keep s) ++ [s.x, s.y]).toFinset, f r =
      ∑ r ∈ (L.filter (keep s)).toFinset, f r + f s.x + f s.y := by
  rw [List.toFinset_append]
  have hdisj : Disjoint (L.filter (keep s)).toFinset [s.x, s.y].toFinset := by
    rw [Finset.disjoint_left]
    intro r hr hr'
    simp only [List.mem_toFinset, List.mem_filter, keep, Bool.and_eq_true, decide_eq_true_eq] at hr
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact hr.2.1.1 rfl
    · exact hr.2.1.2 rfl
  rw [sum_union hdisj]
  simp [sum_insert, hxy]
  ring


/-- The ripple of the last two rows a replay leaves. -/
def finalSum (n : ℕ) (steps : List Csa) (live : List ℕ) (present : ℕ → ℕ) (rows : ℕ → ℕ → Bit) : ℕ → Bit :=
  let live' := liveAfter steps live
  let present' := presentFrom steps present
  let rows' := rowsFrom steps rows
  ripple (carries n (present' (live'.getD 0 0)) (present' (live'.getD 1 0))) (rows' (live'.getD 0 0))
    (rows' (live'.getD 1 0))

/-- Through a checked replay, the rows' total modulo `2^n` becomes the ripple's output. -/
theorem replay (n : ℕ) (hn : n ≤ 128) : ∀ (steps : List Csa) (live : List ℕ) (present : ℕ → ℕ)
    (rows : ℕ → ℕ → Bit) (T : ℤ), checkFrom n steps live present = true → live.Nodup →
    (∀ r ∈ live, ZeroOff (rows r) (present r)) →
    (∃ k : ℤ, ∑ r ∈ live.toFinset, rowValue n (rows r) = T + 2 ^ n * k) →
    ∃ k : ℤ, rowValue n (finalSum n steps live present rows) = T + 2 ^ n * k
  | [], live, present, rows, T, hc, hnd, hz, ⟨k, hk⟩ => by
    simp only [checkFrom, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hc
    obtain ⟨⟨⟨hlen, hsmall⟩, hr⟩, hcm⟩ := hc
    match live, hlen, hnd with
    | [l0, l1], _, hnd =>
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hr hcm
      have hne : l0 ≠ l1 := by simpa using hnd
      obtain ⟨k', hk'⟩ := ripple_value n _ _ _ (rippleOK_of_check n _ _ _ hr hcm hn) (rows l0) (rows l1)
        (hz l0 (by simp)) (hz l1 (by simp))
      refine ⟨k - k', ?_⟩
      simp only [finalSum, liveAfter, presentFrom, rowsFrom, List.getD_cons_zero, List.getD_cons_succ]
      rw [List.toFinset_cons, List.toFinset_cons, List.toFinset_nil, insert_empty_eq, sum_insert (by simp [hne]),
        sum_singleton] at hk
      linarith
  | st :: steps, live, present, rows, T, hc, hnd, hz, ⟨k, hk⟩ => by
    simp only [checkFrom, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem, bne_iff_ne, ne_eq,
      List.all_eq_true] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hx, hy⟩, hz'⟩, hxy⟩, hxz⟩, hyz⟩, hsmall⟩, hp⟩, hmy⟩, hmz⟩, hstep⟩, hrest⟩ := hc
    have hok := stepOK_of_check n st _ _ _ hstep (hsmall _ hx) (hsmall _ hy) (hsmall _ hz') hp hmy hmz hn
    obtain ⟨k1, hk1⟩ := step_value n st _ _ _ hok (rows st.x) (rows st.y) (rows st.z) (hz _ hx) (hz _ hy) (hz _ hz')
    apply replay n hn steps _ (stepPresent st present) (stepRows st rows) T hrest
    · refine List.Nodup.append (List.Nodup.filter _ hnd) (by simp [hxy]) ?_
      intro r hr hr'
      simp only [List.mem_filter, keep, Bool.and_eq_true, decide_eq_true_eq] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact hr.2.1.1 rfl
      · exact hr.2.1.2 rfl
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · simp only [List.mem_filter, keep, Bool.and_eq_true, decide_eq_true_eq] at hr
        simp only [stepRows, stepPresent, if_neg hr.2.1.1, if_neg hr.2.1.2]
        exact hz r hr.1
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simp only [stepRows, stepPresent, if_true]
          exact sumRow_zeroOff st _ _ _ _ _ _ (hz _ hx) (hz _ hy) (hz _ hz')
        · simp only [stepRows, stepPresent, if_neg (Ne.symm hxy), if_true]
          exact carryRow_zeroOff st _ _ _
    · refine ⟨k - k1, ?_⟩
      have h3 := sum_three live st hx hy hz' hxy hxz hyz (fun r => rowValue n (rows r))
      have h2 := sum_two live st hxy (fun r => rowValue n (stepRows st rows r))
      have hkeep : ∑ r ∈ (live.filter (keep st)).toFinset, rowValue n (stepRows st rows r) =
          ∑ r ∈ (live.filter (keep st)).toFinset, rowValue n (rows r) := by
        apply sum_congr rfl
        intro r hr
        simp only [List.mem_toFinset, List.mem_filter, keep, Bool.and_eq_true, decide_eq_true_eq] at hr
        simp only [stepRows, if_neg hr.2.1.1, if_neg hr.2.1.2]
      have hsx : stepRows st rows st.x = sumRow st (rows st.x) (rows st.y) (rows st.z) := by simp [stepRows]
      have hsy : stepRows st rows st.y = carryRow st (rows st.x) (rows st.y) (rows st.z) := by
        simp [stepRows, Ne.symm hxy]
      rw [hsx, hsy] at h2
      rw [h2, hkeep]
      linarith


/-! From the inputs' bits to the product. -/

/-- The rows before any step, positions from `n` up dropped. -/
def cellN (n : ℕ) (a b : ℕ → Bit) (r p : ℕ) : Bit := if p < n then cell n a b r p else 0

theorem initial_zeroOff (n : ℕ) (hn : n = 64 ∨ n = 128) (a b : ℕ → Bit) (r : ℕ) (hr : r < nRows) :
    ZeroOff (cellN n a b r) (initialPresent n r) := by
  intro p hp
  unfold initialPresent at hp
  rw [maskOf_bit] at hp
  unfold cellN
  by_cases hpn : p < n
  · rw [if_pos hpn]
    simp only [hpn, decide_true, Bool.true_and] at hp
    unfold cell
    by_cases h64 : r < 64
    · simp only [h64, if_true] at hp ⊢
      have h1 : ¬ (r ≤ p + 1 ∧ p + 1 - r < 64) := by
        intro hc; revert hp; simp [hc.1, hc.2]
      have h2 : ¬ (p = 0 ∧ r = 2) := by rintro ⟨rfl, rfl⟩; revert hp; simp
      have h3 : ¬ (p = 0 ∧ r = 3) := by rintro ⟨rfl, rfl⟩; revert hp; simp
      rw [if_neg h1, if_neg h2, if_neg h3]
    · simp only [h64, if_false] at hp ⊢
      have hr' : r = aRow ∨ r = bRow := by simp only [nRows, aRow, bRow] at hr ⊢; omega
      simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hp
      rcases hr' with rfl | rfl
      · simp only [if_true]
        rw [if_neg (by omega)]
        rcases hn with rfl | rfl
        · rw [if_neg (by omega), if_neg (by omega)]
        · rw [if_neg (by omega), if_neg (by simp at hp; omega)]
      · simp only [show bRow ≠ aRow by decide, if_false, if_true]
        rcases hn with rfl | rfl
        · rw [if_neg (by omega), if_neg (by omega)]
        · rw [if_neg (by omega), if_neg (by omega)]
  · rw [if_neg hpn]


/-- Positions from `n` up are multiples of `2^n`. -/
theorem rowValue_mod (n k : ℕ) (hnk : n ≤ k) (f : ℕ → Bit) : ∃ m : ℤ, rowValue k f = rowValue n f + 2 ^ n * m := by
  refine ⟨∑ p ∈ range (k - n), 2 ^ p * iv (f (n + p)), ?_⟩
  have h : ∑ p ∈ range (k - n), (2 : ℤ) ^ (n + p) * iv (f (n + p)) =
      ∑ p ∈ range (k - n), 2 ^ n * (2 ^ p * iv (f (n + p))) :=
    sum_congr rfl fun p _ => by rw [pow_add]; ring
  rw [rowValue, rowValue, show k = n + (k - n) by omega, sum_range_add, mul_sum, h, Nat.add_sub_cancel_left]

theorem rowValue_clip (n : ℕ) (a b : ℕ → Bit) (r : ℕ) : rowValue n (cellN n a b r) = rowValue n (cell n a b r) := by
  apply sum_congr rfl
  intro p hp
  simp [cellN, mem_range.mp hp]

/-- The plan's output is the product modulo `2^n`. -/
theorem product_value (n : ℕ) (hn : n = 64 ∨ n = 128) (hc : check n = true) (a b : ℕ → Bit) :
    ∃ k : ℤ, rowValue n (finalSum n (plan n).1 (List.range nRows) (initialPresent n) (cellN n a b)) =
      word a * word b + 2 ^ n * k := by
  have hn' : n ≤ 128 := by omega
  simp only [check, Bool.and_eq_true] at hc
  apply replay n hn' _ _ _ _ _ hc.1 (List.nodup_range) fun r hr => initial_zeroOff n hn a b r (List.mem_range.mp hr)
  -- The rows' total: positions above the width drop out, the constants are multiples of `2^n`.
  have hsum := rows_sum n a b
  choose m hm using fun r => rowValue_mod n 128 hn' (cell n a b r)
  refine ⟨-(∑ r ∈ range nRows, m r) + (if n = 128 then 1 else 2 ^ 63), ?_⟩
  rw [List.toFinset_range]
  simp only [rowValue_clip]
  have : ∑ r ∈ range nRows, rowValue 128 (cell n a b r) =
      ∑ r ∈ range nRows, rowValue n (cell n a b r) + 2 ^ n * ∑ r ∈ range nRows, m r := by
    rw [mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun r _ => hm r
  rcases hn with rfl | rfl <;> norm_num at hsum this ⊢ <;> linarith

end LeanVMCircuits.Multiply
