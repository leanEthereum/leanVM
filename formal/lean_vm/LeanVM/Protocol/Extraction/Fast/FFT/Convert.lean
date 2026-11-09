module

public import LeanVM.Protocol.Extraction.Fast.FFT.Plan

/-!
# Monomial ↔ novel conversions by in-place level passes

The recursive conversions (`toNovelRec`, `fromNovelRec`, `Fast/FFT/Basis`) build `≈ 6` arrays per
coefficient and level (halves, quotient blocks, `++`) and run every sparse sum over all `i`
terms. Here the same conversions on the whole buffer of `N = 2^j` coefficients, level by level:

* `toLevel` (monomial → novel, levels `j − 1, …, 0`): one pass for the quotients of every block of
  `2H = 2^(i+1)` by `W_i` (`N/2` entries: the top `H − h` read off, the low `h` through them),
  one pass for the output (`N` entries: the remainder `r` in the block's low half, `β_i·q` in its
  high half);
* `fromLevel` (novel → monomial, levels `0, …, j − 1`): one pass (`N` entries:
  `r + (β_i^{-1}·q̂)·W_i`, with the plan's `s_{i,t}·β_i^{-1}`);
* the sparse sums stop at the first vanishing term (`sumAsc`, `sumDesc`: the terms `2^t ≤ e`
  ascending, `2^t > e` descending), the level's table entry and powers read once per pass.

The `K` products are the recursive ones' (`N·j(j+1)/4` each way). **Proved**, for `j ≤ 64`:
`toNovelInPlace_eq : toNovelInPlace (mkPlan j) a = toNovel j a` and
`fromNovelInPlace_eq : fromNovelInPlace (mkPlan j) c = fromNovel j c`, through the block lemmas
`toLevel_getD`, `fromLevel_getD` (each block of a pass is one step of the recursion) and the
composition lemmas `toLevels_getD`, `fromLevels_getD`.
-/

namespace LeanVM.Extraction.Fast.FFT

open LeanVM.Parameters LeanVM.Extraction

public section

/-! ## Sums that stop at the first vanishing term -/

/-- `Σ_{t ≥ t₀, 2^t ≤ x} f t` over `n` terms, stopping at the first `2^t > x`. -/
@[expose] def sumAsc (pw : Array ℕ) (f : ℕ → K) (x : ℕ) : ℕ → ℕ → K
  | _, 0 => 0
  | t, n + 1 => if pw.getD t 0 ≤ x then f t + sumAsc pw f x (t + 1) n else 0

/-- `Σ_{t < T, 2^t > x} f t`, descending, stopping at the first `2^t ≤ x`. -/
@[expose] def sumDesc (pw : Array ℕ) (f : ℕ → K) (x : ℕ) : ℕ → K
  | 0 => 0
  | t + 1 => if x < pw.getD t 0 then f t + sumDesc pw f x t else 0

theorem sumAsc_eq {pw : Array ℕ} (f : ℕ → K) (x : ℕ) {t₀ n : ℕ}
    (hpw : ∀ t < t₀ + n, pw.getD t 0 = 2 ^ t) :
    sumAsc pw f x t₀ n = ∑ k ∈ Finset.range n, if 2 ^ (t₀ + k) ≤ x then f (t₀ + k) else 0 := by
  induction n generalizing t₀ with
  | zero => rfl
  | succ n ih =>
    rw [sumAsc, hpw t₀ (by omega), Finset.sum_range_succ']
    simp only [Nat.add_zero]
    by_cases h : 2 ^ t₀ ≤ x
    · rw [ite_eq_left h, ite_eq_left h, ih (t₀ := t₀ + 1) fun t ht ↦ hpw t (by omega), add_comm]
      congr 1
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [show t₀ + 1 + k = t₀ + (k + 1) by omega]
    · rw [ite_eq_right h, ite_eq_right h, add_zero]
      symm
      refine Finset.sum_eq_zero fun k _ ↦ ite_eq_right fun h' ↦ h ?_
      exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) h'

theorem sumDesc_eq {pw : Array ℕ} (f : ℕ → K) (x : ℕ) {T : ℕ} (hpw : ∀ t < T, pw.getD t 0 = 2 ^ t) :
    sumDesc pw f x T = ∑ t ∈ Finset.range T, if x < 2 ^ t then f t else 0 := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [sumDesc, hpw T (by omega), Finset.sum_range_succ]
    by_cases h : x < 2 ^ T
    · rw [ite_eq_left h, ite_eq_left h, ih fun t ht ↦ hpw t (by omega), add_comm]
    · rw [ite_eq_right h, ite_eq_right h, add_zero]
      symm
      refine Finset.sum_eq_zero fun t ht ↦ ite_eq_right fun h' ↦ h ?_
      exact lt_of_lt_of_le h' (Nat.pow_le_pow_right (by norm_num) (by simp at ht; omega))

theorem linCoeff_eq_sum (s q : Array K) (n d T : ℕ) :
    linCoeff s q n d T = ∑ t ∈ Finset.range T,
      if 2 ^ t ≤ d ∧ d - 2 ^ t < n then s.getD t 0 * q.getD (d - 2 ^ t) 0 else 0 := by
  induction T with
  | zero => rfl
  | succ T ih => rw [linCoeff, ih, Finset.sum_range_succ]

/-! ## Slices and blocks -/

theorem getD_sliceArr (n o : ℕ) (c : Array K) (e : ℕ) :
    (sliceArr n o c).getD e 0 = if e < n then c.getD (o + e) 0 else 0 := by
  split
  · rw [sliceArr, getD_ofFn _ (by assumption)]
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp [sliceArr]; omega)]
    rfl

theorem size_sliceArr (n o : ℕ) (c : Array K) : (sliceArr n o c).size = n := Array.size_ofFn

theorem sliceArr_append_left (x y : Array K) {n : ℕ} (hx : x.size = n) : sliceArr n 0 (x ++ y) = x := by
  apply array_eq_of_getD (by rw [size_sliceArr, hx])
  intro e he
  rw [size_sliceArr] at he
  rw [getD_sliceArr, ite_eq_left he, getD_append, hx, ite_eq_left (by omega), Nat.zero_add]

theorem sliceArr_append_right (x y : Array K) {n : ℕ} (hx : x.size = n) (hy : y.size = n) :
    sliceArr n n (x ++ y) = y := by
  apply array_eq_of_getD (by rw [size_sliceArr, hy])
  intro e he
  rw [size_sliceArr] at he
  rw [getD_sliceArr, ite_eq_left he, getD_append, hx, ite_eq_right (by omega),
    Nat.add_sub_cancel_left]

theorem sliceArr_sliceArr (c : Array K) {n m o o' : ℕ} (h : o' + n ≤ m) :
    sliceArr n o' (sliceArr m o c) = sliceArr n (o + o') c := by
  apply array_eq_of_getD (by rw [size_sliceArr, size_sliceArr])
  intro e he
  rw [size_sliceArr] at he
  rw [getD_sliceArr, ite_eq_left he, getD_sliceArr, ite_eq_left (by omega), getD_sliceArr,
    ite_eq_left he, Nat.add_assoc]

theorem size_toNovelRec (tab : List (Array K × K)) (a : Array K) :
    (toNovelRec tab a).size = 2 ^ tab.length := by
  induction tab generalizing a with
  | nil => rfl
  | cons d tab ih =>
    obtain ⟨s, β⟩ := d
    rw [toNovelRec, Array.size_append, ih, ih, List.length_cons, pow_succ]
    ring

theorem size_fromNovelRec (tab : List (Array K × K)) (c : Array K) :
    (fromNovelRec tab c).size = 2 ^ tab.length := by
  cases tab with
  | nil => rfl
  | cons d tab =>
    obtain ⟨s, β⟩ := d
    rw [fromNovelRec, mulAddW, Array.size_ofFn, List.length_cons, pow_succ]
    ring

/-- One step of `toNovelRec` on a block of `2^(i+1)`: the remainder by `W_i`, then `β·q`. -/
@[expose] noncomputable def toStep (s : Array K) (β : K) (i : ℕ) (b : Array K) : Array K :=
  divRem s i b (divQuot s i b) ++ scaleArr (2 ^ i) β (divQuot s i b)

theorem size_divRem (s : Array K) (i : ℕ) (a q : Array K) : (divRem s i a q).size = 2 ^ i :=
  Array.size_ofFn

/-- The quotient's entries, the low ones through the sparse sum over `2^t > x`. -/
theorem divQuot_getD (s b : Array K) (i : ℕ) {x : ℕ} (hx : x < 2 ^ i) :
    (divQuot s i b).getD x 0 =
      if x < 2 ^ i / 2 then b.getD (2 ^ i + x) 0 - ∑ t ∈ Finset.range i,
        (if x < 2 ^ t then s.getD t 0 * b.getD (2 * 2 ^ i + x - 2 ^ t) 0 else 0)
      else b.getD (2 ^ i + x) 0 := by
  obtain ⟨hH, hT⟩ := level_facts i
  rw [divQuot, getD_append, Array.size_ofFn]
  split
  · rename_i hxh
    have hH2 : 2 ^ i = 2 * (2 ^ i / 2) := by rcases hH with hH | ⟨_, h0⟩ <;> omega
    rw [getD_ofFn _ hxh, linCoeff_eq_sum]
    dsimp only
    congr 1
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    have ht' := hT t (Finset.mem_range.mp ht)
    by_cases hc : x < 2 ^ t
    · rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_left hc, getD_ofFn _ (by omega)]
      dsimp only
      congr 2
      omega
    · rw [ite_eq_right fun h ↦ hc (by omega), ite_eq_right hc]
  · rw [getD_ofFn _ (by omega)]
    dsimp only
    congr 1
    omega

theorem divRem_getD (s b q : Array K) (i : ℕ) {e : ℕ} (he : e < 2 ^ i) :
    (divRem s i b q).getD e 0 = b.getD e 0 - ∑ t ∈ Finset.range i,
      (if 2 ^ t ≤ e then s.getD t 0 * q.getD (e - 2 ^ t) 0 else 0) := by
  rw [divRem, getD_ofFn _ he, linCoeff_eq_sum]
  dsimp only
  congr 1
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  by_cases hc : 2 ^ t ≤ e
  · have := Nat.two_pow_pos t
    rw [ite_eq_left ⟨hc, by omega⟩, ite_eq_left hc]
  · rw [ite_eq_right fun h ↦ hc h.1, ite_eq_right hc]

/-! ## The monomial-to-novel level pass -/

/-- The quotients by `W_i` of every block of `2H = 2^(i+1)` of the buffer: `N/2` entries, block
`k`'s at `H·k`; the top `H − h` read off, the low `h` through the sparse sum over `2^t > x`. -/
@[expose] def toQuot (pw : Array ℕ) (N i : ℕ) (s B : Array K) : Array K :=
  let H := pw.getD i 0
  let h := H / 2
  let H2 := 2 * H
  Array.ofFn fun m : Fin (N / 2) ↦
    let x := m.val % H
    let base := 2 * (m.val - x)
    if x < h then
      B.getD (base + H + x) 0 -
        sumDesc pw (fun t ↦ s.getD t 0 * B.getD (base + H2 + x - pw.getD t 0) 0) x i
    else B.getD (base + H + x) 0

/-- **Level `i` of monomial → novel on the whole buffer** of `N`: the quotients of every block by
`W_i` (`toQuot`, `N/2` entries), then the remainders and `β·q` (`N` entries). -/
@[expose] def toLevel (pw : Array ℕ) (N i : ℕ) (d : Array K × K) (B : Array K) : Array K :=
  let s := d.1
  let β := d.2
  let H := pw.getD i 0
  let H2 := 2 * H
  let Q := toQuot pw N i s B
  Array.ofFn fun p : Fin N ↦
    let e := p.val % H2
    let qb := (p.val - e) / 2
    if e < H then
      B.getD p.val 0 - sumAsc pw (fun t ↦ s.getD t 0 * Q.getD (qb + e - pw.getD t 0) 0) e 0 i
    else β * Q.getD (qb + e - H) 0

theorem block_mod {M k e : ℕ} (he : e < M) : (M * k + e) % M = e := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt he]

theorem toQuot_getD {pw : Array ℕ} {N i : ℕ} (hpw : ∀ t ≤ i, pw.getD t 0 = 2 ^ t)
    (s B : Array K) {k x : ℕ} (hx : x < 2 ^ i) (hN : 2 * 2 ^ i * (k + 1) ≤ N) :
    (toQuot pw N i s B).getD (2 ^ i * k + x) 0 =
      (divQuot s i (sliceArr (2 * 2 ^ i) (2 * 2 ^ i * k) B)).getD x 0 := by
  have hpw' : ∀ t < i, pw.getD t 0 = 2 ^ t := fun t ht ↦ hpw t ht.le
  obtain ⟨_, hT⟩ := level_facts i
  have hHpos := Nat.two_pow_pos i
  have e1 : 2 * 2 ^ i * k = 2 * (2 ^ i * k) := by ring
  have e2 : 2 * 2 ^ i * (k + 1) = 2 * (2 ^ i * k) + 2 * 2 ^ i := by ring
  rw [e1]
  rw [e2] at hN
  have hmod : (2 ^ i * k + x) % 2 ^ i = x := block_mod hx
  have hm : 2 ^ i * k + x < N / 2 := by
    generalize 2 ^ i * k = P at *; generalize 2 ^ i = H at *; omega
  rw [toQuot]
  simp only [hpw i le_rfl]
  rw [getD_ofFn _ hm]
  dsimp only
  rw [hmod, Nat.add_sub_cancel, divQuot_getD _ _ _ hx, sumDesc_eq _ _ hpw']
  split
  · refine congrArg₂ (· - ·) ?_ ?_
    · rw [getD_sliceArr, ite_eq_left (by generalize 2 ^ i = H at *; omega), Nat.add_assoc]
    · refine Finset.sum_congr rfl fun t ht ↦ ?_
      have ht' := hT t (Finset.mem_range.mp ht)
      have h2t := Nat.two_pow_pos t
      split
      · rw [hpw' t (Finset.mem_range.mp ht), getD_sliceArr,
          ite_eq_left (by generalize 2 ^ i = H at *; omega)]
        congr 2
        generalize 2 ^ i * k = P at *; generalize 2 ^ i = H at *; omega
      · rfl
  · rw [getD_sliceArr, ite_eq_left (by generalize 2 ^ i = H at *; omega), Nat.add_assoc]

/-- **Each block of a `toLevel` pass is a step of the recursion.** -/
theorem toLevel_getD {pw : Array ℕ} {N i : ℕ} (hpw : ∀ t ≤ i, pw.getD t 0 = 2 ^ t)
    (s : Array K) (β : K) (B : Array K) {k e : ℕ} (he : e < 2 * 2 ^ i)
    (hN : 2 * 2 ^ i * (k + 1) ≤ N) :
    (toLevel pw N i (s, β) B).getD (2 * 2 ^ i * k + e) 0 =
      (toStep s β i (sliceArr (2 * 2 ^ i) (2 * 2 ^ i * k) B)).getD e 0 := by
  have hpw' : ∀ t < i, pw.getD t 0 = 2 ^ t := fun t ht ↦ hpw t ht.le
  have hQ := fun x (hx : x < 2 ^ i) ↦ toQuot_getD hpw s B hx hN
  have hHpos := Nat.two_pow_pos i
  have e2 : 2 * 2 ^ i * (k + 1) = 2 * 2 ^ i * k + 2 * 2 ^ i := by ring
  have hp : 2 * 2 ^ i * k + e < N := by
    rw [e2] at hN; generalize 2 * 2 ^ i * k = P at *; generalize 2 ^ i = H at *; omega
  have hmod : (2 * 2 ^ i * k + e) % (2 * 2 ^ i) = e := block_mod he
  have hdiv : 2 * 2 ^ i * k / 2 = 2 ^ i * k := by
    rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [toLevel]
  simp only [hpw i le_rfl]
  rw [getD_ofFn _ hp]
  dsimp only
  rw [hmod, Nat.add_sub_cancel, hdiv, toStep, getD_append, size_divRem]
  split
  · rename_i heH
    rw [divRem_getD _ _ _ _ heH, sumAsc_eq _ _ (t₀ := 0) (by simpa using hpw'),
      getD_sliceArr, ite_eq_left he]
    refine congrArg₂ (· - ·) rfl ?_
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    simp only [Nat.zero_add]
    have h2t := Nat.two_pow_pos t
    split
    · rename_i hc
      rw [hpw' t (Finset.mem_range.mp ht), show 2 ^ i * k + e - 2 ^ t = 2 ^ i * k + (e - 2 ^ t) by
        generalize 2 ^ i * k = P at *; omega, hQ _ (by generalize 2 ^ i = H at *; omega)]
    · rfl
  · rename_i heH
    rw [scaleArr, getD_ofFn _ (by generalize 2 ^ i = H at *; omega)]
    dsimp only
    rw [show 2 ^ i * k + e - 2 ^ i = 2 ^ i * k + (e - 2 ^ i) by
      generalize 2 ^ i * k = P at *; generalize 2 ^ i = H at *; omega,
      hQ _ (by generalize 2 ^ i = H at *; omega)]

/-! ## The novel-to-monomial level pass -/

/-- **Level `i` of novel → monomial on the whole buffer** of `N`: in every block of `2H`, with
the low half `r` and the high half `q̂` (both monomial), `r + (β^{-1}·q̂)·W_i`, from the plan's
`ŝ_t = s_t·β^{-1}` and `β^{-1}`. -/
@[expose] def fromLevel (pw : Array ℕ) (N i : ℕ) (d : Array K × K) (B : Array K) : Array K :=
  let ŝ := d.1
  let βinv := d.2
  let H := pw.getD i 0
  let H2 := 2 * H
  Array.ofFn fun p : Fin N ↦
    let e := p.val % H2
    let hb := p.val - e + H
    if e < H then
      B.getD p.val 0 + sumAsc pw (fun t ↦ ŝ.getD t 0 * B.getD (hb + e - pw.getD t 0) 0) e 0 i
    else
      βinv * B.getD p.val 0 +
        sumDesc pw (fun t ↦ ŝ.getD t 0 * B.getD (hb + e - pw.getD t 0) 0) (e - H) i

/-- **Each block of a `fromLevel` pass is a step of the recursion.** -/
theorem fromLevel_getD {pw : Array ℕ} {N i : ℕ} (hpw : ∀ t ≤ i, pw.getD t 0 = 2 ^ t)
    (s ŝ : Array K) (βinv : K) (hŝ : ∀ t < i, ŝ.getD t 0 = s.getD t 0 * βinv) (B : Array K)
    {k e : ℕ} (he : e < 2 * 2 ^ i) (hN : 2 * 2 ^ i * (k + 1) ≤ N) :
    (fromLevel pw N i (ŝ, βinv) B).getD (2 * 2 ^ i * k + e) 0 =
      (mulAddW s i (sliceArr (2 ^ i) (2 * 2 ^ i * k) B)
        (scaleArr (2 ^ i) βinv (sliceArr (2 ^ i) (2 * 2 ^ i * k + 2 ^ i) B))).getD e 0 := by
  have hpw' : ∀ t < i, pw.getD t 0 = 2 ^ t := fun t ht ↦ hpw t ht.le
  obtain ⟨_, hT⟩ := level_facts i
  have hHpos := Nat.two_pow_pos i
  have e2 : 2 * 2 ^ i * (k + 1) = 2 * 2 ^ i * k + 2 * 2 ^ i := by ring
  have hp : 2 * 2 ^ i * k + e < N := by
    rw [e2] at hN; generalize 2 * 2 ^ i * k = P at *; generalize 2 ^ i = H at *; omega
  have hmod : (2 * 2 ^ i * k + e) % (2 * 2 ^ i) = e := block_mod he
  have hq : ∀ y < 2 ^ i, (scaleArr (2 ^ i) βinv (sliceArr (2 ^ i) (2 * 2 ^ i * k + 2 ^ i) B)).getD y 0 =
      βinv * B.getD (2 * 2 ^ i * k + 2 ^ i + y) 0 := by
    intro y hy
    rw [scaleArr, getD_ofFn _ hy]
    dsimp only
    rw [getD_sliceArr, ite_eq_left hy]
  rw [fromLevel]
  simp only [hpw i le_rfl]
  rw [getD_ofFn _ hp]
  dsimp only
  rw [hmod, Nat.add_sub_cancel, mulAddW, getD_ofFn _ he]
  dsimp only
  rw [linCoeff_eq_sum]
  split
  · rename_i heH
    rw [getD_sliceArr, ite_eq_left heH, sumAsc_eq _ _ (t₀ := 0) (by simpa using hpw')]
    refine congrArg₂ (· + ·) rfl ?_
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    simp only [Nat.zero_add]
    have h2t := Nat.two_pow_pos t
    by_cases hc : 2 ^ t ≤ e
    · rw [ite_eq_left hc, ite_eq_left ⟨hc, by generalize 2 ^ i = H at *; omega⟩,
        hpw' t (Finset.mem_range.mp ht), hŝ t (Finset.mem_range.mp ht),
        hq _ (by generalize 2 ^ i = H at *; omega), show 2 * 2 ^ i * k + 2 ^ i + e - 2 ^ t =
          2 * 2 ^ i * k + 2 ^ i + (e - 2 ^ t) by
          generalize 2 * 2 ^ i * k = P at *; generalize 2 ^ i = H at *; omega]
      ring
    · rw [ite_eq_right hc, ite_eq_right fun h ↦ hc h.1]
  · rename_i heH
    rw [hq _ (by generalize 2 ^ i = H at *; omega), sumDesc_eq _ _ hpw',
      show 2 * 2 ^ i * k + 2 ^ i + (e - 2 ^ i) = 2 * 2 ^ i * k + e by
        generalize 2 * 2 ^ i * k = P at *; generalize 2 ^ i = H at *; omega]
    refine congrArg₂ (· + ·) rfl ?_
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    have ht' := hT t (Finset.mem_range.mp ht)
    have h2t := Nat.two_pow_pos t
    by_cases hc : e - 2 ^ i < 2 ^ t
    · rw [ite_eq_left hc, ite_eq_left ⟨by generalize 2 ^ i = H at *; omega,
          by generalize 2 ^ i = H at *; omega⟩, hpw' t (Finset.mem_range.mp ht),
        hŝ t (Finset.mem_range.mp ht), hq _ (by generalize 2 ^ i = H at *; omega),
        show 2 * 2 ^ i * k + 2 ^ i + e - 2 ^ t = 2 * 2 ^ i * k + 2 ^ i + (e - 2 ^ t) by
          generalize 2 * 2 ^ i * k = P at *; generalize 2 ^ i = H at *; omega]
      ring
    · rw [ite_eq_right hc, ite_eq_right fun h ↦ hc (by generalize 2 ^ i = H at *; omega)]

/-! ## The conversions -/

/-- Levels `L − 1, …, 0` of monomial → novel on the buffer of `N`. -/
@[expose] def toLevels (pw : Array ℕ) (N : ℕ) (D : Array (Array K × K)) (L : ℕ) (B : Array K) :
    Array K :=
  (List.range L).foldr (fun i B ↦ toLevel pw N i (D.getD i (#[], 0)) B) B

/-- Levels `0, …, L − 1` of novel → monomial on the buffer of `N`. -/
@[expose] def fromLevels (pw : Array ℕ) (N : ℕ) (D : Array (Array K × K)) (L : ℕ) (B : Array K) :
    Array K :=
  (List.range L).foldl (fun B i ↦ fromLevel pw N i (D.getD i (#[], 0)) B) B

/-- **Monomial → novel by the plan**, in place, level by level. -/
@[expose] def toNovelInPlace (P : FFTPlan) (a : Array K) : Array K :=
  let N := 2 ^ P.log
  toLevels P.pows N P.convFwd P.log (Array.ofFn fun p : Fin N ↦ a.getD p.val 0)

/-- **Novel → monomial by the plan**, in place, level by level. -/
@[expose] def fromNovelInPlace (P : FFTPlan) (c : Array K) : Array K :=
  let N := 2 ^ P.log
  fromLevels P.pows N P.convInv P.log (Array.ofFn fun p : Fin N ↦ c.getD p.val 0)

theorem size_toLevels (pw : Array ℕ) (N : ℕ) (D : Array (Array K × K)) (L : ℕ) {B : Array K}
    (hB : B.size = N) : (toLevels pw N D L B).size = N := by
  cases L with
  | zero => exact hB
  | succ L =>
    rw [toLevels, List.range_succ_eq_map, List.foldr_cons, toLevel]
    exact Array.size_ofFn

theorem size_fromLevels (pw : Array ℕ) (N : ℕ) (D : Array (Array K × K)) (L : ℕ) {B : Array K}
    (hB : B.size = N) : (fromLevels pw N D L B).size = N := by
  cases L with
  | zero => exact hB
  | succ L =>
    rw [fromLevels, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, fromLevel]
    exact Array.size_ofFn

theorem two_pow_succ' (L : ℕ) : 2 ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ, mul_comm]

/-- The digit decomposition `e = 2^L·b + e'` below `2^(L+1)`. -/
theorem digit {L e : ℕ} (he : e < 2 * 2 ^ L) :
    ∃ b e', b < 2 ∧ e' < 2 ^ L ∧ e = 2 ^ L * b + e' := by
  refine ⟨e / 2 ^ L, e % 2 ^ L, Nat.div_lt_of_lt_mul (by rwa [mul_comm]),
    Nat.mod_lt _ (Nat.two_pow_pos L), (Nat.div_add_mod e (2 ^ L)).symm⟩

/-- **The passes compose to the recursion**: after levels `L − 1, …, 0`, block `k` of `2^L` is
`toNovelRec` of block `k` of the input. -/
theorem toLevels_getD {pw : Array ℕ} {N : ℕ} {Dfun : ℕ → Array K × K} {D : Array (Array K × K)}
    (L : ℕ) (hpw : ∀ t < L, pw.getD t 0 = 2 ^ t) (hD : ∀ i < L, D.getD i (#[], 0) = Dfun i)
    (B : Array K) : ∀ k e, e < 2 ^ L → 2 ^ L * (k + 1) ≤ N →
      (toLevels pw N D L B).getD (2 ^ L * k + e) 0 =
        (toNovelRec ((List.range L).reverse.map Dfun) (sliceArr (2 ^ L) (2 ^ L * k) B)).getD e 0 := by
  induction L generalizing B with
  | zero =>
    intro k e he _
    have he0 : e = 0 := by simpa using he
    subst he0
    simp only [toLevels, List.range_zero, List.foldr_nil, List.reverse_nil, List.map_nil,
      toNovelRec, pow_zero, one_mul, Nat.add_zero]
    rw [getD_sliceArr, ite_eq_left (by norm_num), Nat.add_zero]
    rfl
  | succ L ih =>
    intro k e he hN
    rw [two_pow_succ'] at he hN ⊢
    have hpwL : ∀ t ≤ L, pw.getD t 0 = 2 ^ t := fun t ht ↦ hpw t (by omega)
    obtain ⟨b, e', hb, he', rfl⟩ := digit he
    rcases hdl : Dfun L with ⟨s, β⟩
    have hDL : D.getD L (#[], 0) = (s, β) := by rw [hD L (by omega), hdl]
    have hfold : toLevels pw N D (L + 1) B = toLevels pw N D L (toLevel pw N L (s, β) B) := by
      rw [toLevels, List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, hDL]
      rfl
    have hidx : 2 * 2 ^ L * k + (2 ^ L * b + e') = 2 ^ L * (2 * k + b) + e' := by ring
    have hN' : 2 ^ L * (2 * k + b + 1) ≤ N := by
      have : 2 ^ L * (2 * k + b + 1) ≤ 2 * 2 ^ L * (k + 1) := by
        have : 2 * k + b + 1 ≤ 2 * (k + 1) := by omega
        calc 2 ^ L * (2 * k + b + 1) ≤ 2 ^ L * (2 * (k + 1)) := Nat.mul_le_mul_left _ this
          _ = 2 * 2 ^ L * (k + 1) := by ring
      omega
    rw [hfold, hidx, ih (fun t ht ↦ hpw t (by omega)) (fun i hi ↦ hD i (by omega)) _ _ _ he' hN']
    -- the block of the pass is a half of the recursion's step
    have hslice : sliceArr (2 ^ L) (2 ^ L * (2 * k + b)) (toLevel pw N L (s, β) B) =
        sliceArr (2 ^ L) (2 ^ L * b) (toStep s β L (sliceArr (2 * 2 ^ L) (2 * 2 ^ L * k) B)) := by
      apply array_eq_of_getD (by rw [size_sliceArr, size_sliceArr])
      intro x hx
      rw [size_sliceArr] at hx
      rw [getD_sliceArr, ite_eq_left hx, getD_sliceArr, ite_eq_left hx,
        show 2 ^ L * (2 * k + b) + x = 2 * 2 ^ L * k + (2 ^ L * b + x) by ring,
        toLevel_getD hpwL s β B (by interval_cases b <;> omega) hN]
    rw [hslice, List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, hdl, toNovelRec]
    simp only [List.length_map, List.length_reverse, List.length_range]
    rw [getD_append, size_toNovelRec]
    simp only [List.length_map, List.length_reverse, List.length_range]
    interval_cases b
    · rw [ite_eq_left (by omega), Nat.mul_zero, toStep,
        sliceArr_append_left _ _ (size_divRem _ _ _ _), Nat.zero_add]
    · rw [ite_eq_right (by omega), Nat.mul_one, toStep,
        sliceArr_append_right _ _ (size_divRem _ _ _ _) (size_scaleArr _ _ _),
        show 2 ^ L + e' - 2 ^ L = e' by omega]

/-- **The passes compose to the recursion**: after levels `0, …, L − 1`, block `k` of `2^L` is
`fromNovelRec` of block `k` of the input. -/
theorem fromLevels_getD {pw : Array ℕ} {N : ℕ} {Dfun : ℕ → Array K × K} {D : Array (Array K × K)}
    (L : ℕ) (hpw : ∀ t < L, pw.getD t 0 = 2 ^ t)
    (hD : ∀ i < L, (D.getD i (#[], 0)).2 = (Dfun i).2 ∧
      ∀ t < i, (D.getD i (#[], 0)).1.getD t 0 = (Dfun i).1.getD t 0 * (Dfun i).2)
    (B : Array K) : ∀ k e, e < 2 ^ L → 2 ^ L * (k + 1) ≤ N →
      (fromLevels pw N D L B).getD (2 ^ L * k + e) 0 =
        (fromNovelRec ((List.range L).reverse.map Dfun) (sliceArr (2 ^ L) (2 ^ L * k) B)).getD e 0 := by
  induction L generalizing B with
  | zero =>
    intro k e he _
    have he0 : e = 0 := by simpa using he
    subst he0
    simp only [fromLevels, List.range_zero, List.foldl_nil, List.reverse_nil, List.map_nil,
      fromNovelRec, pow_zero, one_mul, Nat.add_zero]
    rw [getD_sliceArr, ite_eq_left (by norm_num), Nat.add_zero]
    rfl
  | succ L ih =>
    intro k e he hN
    rw [two_pow_succ'] at he hN ⊢
    have hpwL : ∀ t ≤ L, pw.getD t 0 = 2 ^ t := fun t ht ↦ hpw t (by omega)
    rcases hdl : Dfun L with ⟨s, βinv⟩
    rcases hdp : D.getD L (#[], 0) with ⟨ŝ, β'⟩
    obtain ⟨hβ, hŝ⟩ := hD L (by omega)
    rw [hdp, hdl] at hβ hŝ
    simp only at hβ hŝ
    subst hβ
    have hfold : fromLevels pw N D (L + 1) B = fromLevel pw N L (ŝ, β') (fromLevels pw N D L B) := by
      rw [fromLevels, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hdp]
      rfl
    have hih := ih (fun t ht ↦ hpw t (by omega)) (fun i hi ↦ hD i (by omega)) B
    have hhalf : ∀ c < 2, sliceArr (2 ^ L) (2 * 2 ^ L * k + 2 ^ L * c) (fromLevels pw N D L B) =
        fromNovelRec ((List.range L).reverse.map Dfun) (sliceArr (2 ^ L) (2 * 2 ^ L * k + 2 ^ L * c) B) := by
      intro c hc
      apply array_eq_of_getD (by rw [size_sliceArr, size_fromNovelRec]; simp)
      intro x hx
      rw [size_sliceArr] at hx
      have hN' : 2 ^ L * (2 * k + c + 1) ≤ N := by
        have : 2 ^ L * (2 * k + c + 1) ≤ 2 * 2 ^ L * (k + 1) := by
          have : 2 * k + c + 1 ≤ 2 * (k + 1) := by omega
          calc 2 ^ L * (2 * k + c + 1) ≤ 2 ^ L * (2 * (k + 1)) := Nat.mul_le_mul_left _ this
            _ = 2 * 2 ^ L * (k + 1) := by ring
        omega
      rw [getD_sliceArr, ite_eq_left hx, show 2 * 2 ^ L * k + 2 ^ L * c + x = 2 ^ L * (2 * k + c) + x by
        ring, hih _ _ hx hN', show 2 ^ L * (2 * k + c) = 2 * 2 ^ L * k + 2 ^ L * c by ring]
    rw [hfold, fromLevel_getD hpwL s ŝ β' hŝ _ he hN]
    have h0 := hhalf 0 (by norm_num)
    have h1 := hhalf 1 (by norm_num)
    rw [Nat.mul_zero, Nat.add_zero] at h0
    rw [Nat.mul_one] at h1
    rw [h0, h1, List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, hdl, fromNovelRec]
    simp only [List.length_map, List.length_reverse, List.length_range]
    rw [sliceArr_sliceArr _ (by omega), sliceArr_sliceArr _ (by omega), Nat.add_zero]

theorem novelSum_congr {n : ℕ} {c c' : Array K} (h : ∀ t < n, c.getD t 0 = c'.getD t 0) :
    novelSum n c = novelSum n c' :=
  Finset.sum_congr rfl fun t ht ↦ by rw [h t (Finset.mem_range.mp ht)]

theorem polyN_congr {n : ℕ} {c c' : Array K} (h : ∀ t < n, c.getD t 0 = c'.getD t 0) :
    polyN n c = polyN n c' :=
  Finset.sum_congr rfl fun t ht ↦ by rw [h t (Finset.mem_range.mp ht)]

/-- **The in-place monomial → novel conversion is `toNovel`.** -/
theorem toNovelInPlace_eq {j : ℕ} (hj : j ≤ 64) (a : Array K) :
    toNovelInPlace (mkPlan j) a = toNovel j a := by
  have hsz : (toNovelInPlace (mkPlan j) a).size = 2 ^ j :=
    size_toLevels _ _ _ _ (by rw [mkPlan_log, Array.size_ofFn])
  set init := (Array.ofFn fun p : Fin (2 ^ j) ↦ a.getD p.val 0) with hinit
  have hslice : toNovel j (sliceArr (2 ^ j) 0 init) = toNovel j a := by
    refine novelSum_injective hj (toNovel_spec hj _).1 (toNovel_spec hj _).1 ?_
    rw [(toNovel_spec hj _).2, (toNovel_spec hj _).2]
    refine polyN_congr fun t ht ↦ ?_
    rw [getD_sliceArr, ite_eq_left ht, Nat.zero_add, hinit, getD_ofFn _ ht]
  apply array_eq_of_getD (by rw [hsz, (toNovel_spec hj a).1])
  intro e he
  rw [hsz] at he
  have h := toLevels_getD (Dfun := linData) (pw := (mkPlan j).pows) (N := 2 ^ j)
    (D := (mkPlan j).convFwd) j (fun t ht ↦ mkPlan_pows ht) (fun i hi ↦ mkPlan_convFwd hi) init 0 e he
    (by simp)
  rw [Nat.mul_zero, Nat.zero_add] at h
  rw [← hslice, toNovel, tableUpTo_eq, ← h]
  rfl

/-- **The in-place novel → monomial conversion is `fromNovel`.** -/
theorem fromNovelInPlace_eq {j : ℕ} (hj : j ≤ 64) (c : Array K) :
    fromNovelInPlace (mkPlan j) c = fromNovel j c := by
  have hsz : (fromNovelInPlace (mkPlan j) c).size = 2 ^ j :=
    size_fromLevels _ _ _ _ (by rw [mkPlan_log, Array.size_ofFn])
  set init := (Array.ofFn fun p : Fin (2 ^ j) ↦ c.getD p.val 0) with hinit
  have hslice : fromNovel j (sliceArr (2 ^ j) 0 init) = fromNovel j c := by
    refine polyN_injective (fromNovel_spec hj _).1 (fromNovel_spec hj _).1 ?_
    rw [(fromNovel_spec hj _).2, (fromNovel_spec hj _).2]
    refine novelSum_congr fun t ht ↦ ?_
    rw [getD_sliceArr, ite_eq_left ht, Nat.zero_add, hinit, getD_ofFn _ ht]
  apply array_eq_of_getD (by rw [hsz, (fromNovel_spec hj c).1])
  intro e he
  rw [hsz] at he
  have hD : ∀ i < j, ((mkPlan j).convInv.getD i (#[], 0)).2 =
      ((linData i).1, (linData i).2⁻¹).2 ∧ ∀ t < i, ((mkPlan j).convInv.getD i (#[], 0)).1.getD t 0 =
        ((linData i).1, (linData i).2⁻¹).1.getD t 0 * ((linData i).1, (linData i).2⁻¹).2 := by
    intro i hi
    rw [mkPlan_convInv hj hi]
    exact ⟨rfl, fun t ht ↦ getD_ofFn _ ht⟩
  have h := fromLevels_getD (Dfun := fun i ↦ ((linData i).1, (linData i).2⁻¹)) (pw := (mkPlan j).pows)
    (N := 2 ^ j) (D := (mkPlan j).convInv) j (fun t ht ↦ mkPlan_pows ht) hD init 0 e he (by simp)
  rw [Nat.mul_zero, Nat.zero_add] at h
  have htab : tableInvUpTo j = (List.range j).reverse.map fun i ↦ ((linData i).1, (linData i).2⁻¹) := by
    rw [tableInvUpTo, tableUpTo_eq, List.map_map]
    rfl
  rw [← hslice, fromNovel, htab, ← h]
  rfl

end

end LeanVM.Extraction.Fast.FFT
