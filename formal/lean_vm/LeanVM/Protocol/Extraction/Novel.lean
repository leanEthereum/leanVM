module

public import LeanVM.Protocol.Extraction.Defs
public import LeanVM.Protocol.Extraction.Subspace
public import CompPoly.Univariate.ToPoly.Impl

/-!
# The novel-basis transforms are correct (proofs)

For `κ ≤ 64`, with `X_j = novelBasis j` and `x_v = K.ofBits v`:

* `novelFwd_getD`: entry `v < 2^(κ+R)` of `novelFwd κ R c` is `Σ_{j<2^κ} c_j·X_j(x_v)`;
* `novelInv_eval`: if `y_v = Σ_{j<2^κ} c_j·X_j(x_v)` for `v < 2^κ`, then `novelInv κ y = c`;
* the round trips `novelInv_novelFwd` (coefficients → evaluations → coefficients) and
  `novelFwd_novelInv` (evaluations → coefficients → evaluations), the latter from the stage
  identities `novelFwdStage_novelInvStage`, which are pure characteristic-two algebra;
* `toNovel_eq`, `toNovel_of_toPoly`: the conversion of a monomial-basis polynomial whose values
  on `U_κ` (or whose `toPoly`) is `Σ_j c_j·X_j` returns `c`: `toNovel (msgPoly c) = c`.

**The invariant.** Before stage `i` of the inverse (after stage `i` of the forward transform),
entry `p` of the buffer is `lvl κ i c p = Σ_{j<2^(κ−i)} c_{s + 2^i·j}·X_{2^i·j}(x_{p − s})` with
`s = p mod 2^i`: the partial sums over the coefficients whose low `i` index bits are `s`, at the
point `x_{p−s}`. Level `0` is the evaluation, level `κ` the coefficients. A stage is the identity
`P_s = P'_s + Ŵ_i·P'_{s+2^i}` (`lvlSum_succ`) at the two points `a` and `a + x^i`, where the
level-`i+1` sums agree (they are invariant under `U_{i+1}`, `lvlSum_add_ofBits`) and
`Ŵ_i(a + x^i) = Ŵ_i(a) + 1`.

Credits: the transforms are the additive NTT of Lin, Chung and Han (FOCS 2014), as in Diamond and
Posen, *Polylogarithmic proofs for multilinears over binary towers* (2024), Algorithm 2; CompPoly's
`AdditiveNTT` (github.com/Verified-zkEVM/CompPoly at `572f997390aa4fc131ef30b1186fa1dcf292ca10`,
Apache-2.0; Chung Thai Nguyen and Quang Dao) has the same forward stage and point order. No code
is copied. `CPolynomial`, its `eval` and `toPoly` are CompPoly's.
-/

namespace LeanVM.Extraction.NovelProofs

open LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Words LeanVM.Extraction.Subspace

public section

attribute [local simp] LeanVM.Extraction.Words.ofBits_zero

/-! ## Bits -/

/-- Below `2^k`, adding to a multiple of `2^k` is the exclusive or. -/
theorem mul_two_pow_add_eq_xor {k a v : ℕ} (hv : v < 2 ^ k) : 2 ^ k * a + v = 2 ^ k * a ^^^ v := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_two_pow_mul_add _ hv, Nat.testBit_xor, Nat.testBit_two_pow_mul]
  by_cases hj : j < k
  · have : ¬ j ≥ k := by omega
    simp [hj, this]
  · have : j ≥ k := by omega
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) this))]
    simp [hj, this]

theorem ofBits_mul_two_pow_add {k a v : ℕ} (hv : v < 2 ^ k) :
    K.ofBits (2 ^ k * a + v) = K.ofBits (2 ^ k * a) + K.ofBits v := by
  rw [mul_two_pow_add_eq_xor hv, ofBits_xor]

/-! ## The novel basis -/

theorem novelBasis_zero (a : K) : novelBasis 0 a = 1 := by
  simp [novelBasis]

/-- Disjoint bits multiply: `X_{2^i·m + r} = X_{2^i·m}·X_r` for `r < 2^i`. -/
theorem novelBasis_mul_two_pow_add {i m r : ℕ} (hr : r < 2 ^ i) (a : K) :
    novelBasis (2 ^ i * m + r) a = novelBasis (2 ^ i * m) a * novelBasis r a := by
  unfold novelBasis
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [Nat.testBit_two_pow_mul_add _ hr, Nat.testBit_two_pow_mul]
  by_cases hk : k < i
  · have : ¬ k ≥ i := by omega
    simp [hk, this]
  · have hge : k ≥ i := by omega
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) hge))]
    simp [hk, hge]

/-- `X_{2^i} = Ŵ_i` for `i < 64`. -/
theorem novelBasis_two_pow {i : ℕ} (hi : i < 64) (a : K) :
    novelBasis (2 ^ i) a = normSubspacePoly i a := by
  unfold novelBasis
  simp only [Nat.testBit_two_pow]
  rw [Finset.prod_eq_single i]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_range.mpr hi) h

/-- `X_{2^i·m}` is invariant under `U_i`. -/
theorem novelBasis_mul_two_pow_add_ofBits {i m v : ℕ} (hv : v < 2 ^ i) (a : K) :
    novelBasis (2 ^ i * m) (a + K.ofBits v) = novelBasis (2 ^ i * m) a := by
  unfold novelBasis
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [Nat.testBit_two_pow_mul]
  by_cases hk : k ≥ i
  · have hvk : v < 2 ^ k := lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hk)
    rw [normSubspacePoly_add, normSubspacePoly_of_lt hvk, add_zero]
  · simp [hk]

/-! ## The level sums -/

/-- The level-`i` partial sum at offset `s`: `Σ_{j<2^(κ−i)} c_{s + 2^i·j}·X_{2^i·j}(a)`. -/
noncomputable def lvlSum (κ i s : ℕ) (c : ℕ → K) (a : K) : K :=
  ∑ j ∈ Finset.range (2 ^ (κ - i)), c (s + 2 ^ i * j) * novelBasis (2 ^ i * j) a

theorem sum_range_two_mul (f : ℕ → K) (N : ℕ) :
    ∑ j ∈ Finset.range (2 * N), f j = ∑ j ∈ Finset.range N, (f (2 * j) + f (2 * j + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

/-- **One level**: `P_s = P'_s + Ŵ_i·P'_{s+2^i}`. -/
theorem lvlSum_succ {κ i : ℕ} (hi : i < κ) (hκ : κ ≤ 64) (s : ℕ) (c : ℕ → K) (a : K) :
    lvlSum κ i s c a = lvlSum κ (i + 1) s c a + normSubspacePoly i a * lvlSum κ (i + 1) (s + 2 ^ i) c a := by
  unfold lvlSum
  obtain ⟨d, hd⟩ : ∃ d, κ - i = d + 1 := ⟨κ - i - 1, by omega⟩
  have hd' : κ - (i + 1) = d := by omega
  rw [hd, hd', pow_succ', sum_range_two_mul, Finset.sum_add_distrib, Finset.mul_sum]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [show 2 ^ i * (2 * j) = 2 ^ (i + 1) * j by ring]
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hlt : 2 ^ i < 2 ^ (i + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [show 2 ^ i * (2 * j + 1) = 2 ^ (i + 1) * j + 2 ^ i by ring,
      show s + (2 ^ (i + 1) * j + 2 ^ i) = s + 2 ^ i + 2 ^ (i + 1) * j by ring,
      novelBasis_mul_two_pow_add hlt, novelBasis_two_pow (by omega)]
    ring

/-- The level-`i + 1` sums are invariant under `U_{i+1}`. -/
theorem lvlSum_add_ofBits {κ i v : ℕ} (hv : v < 2 ^ i) (s : ℕ) (c : ℕ → K) (a : K) :
    lvlSum κ i s c (a + K.ofBits v) = lvlSum κ i s c a := by
  unfold lvlSum
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [novelBasis_mul_two_pow_add_ofBits hv]

theorem lvlSum_zero (κ : ℕ) (c : ℕ → K) (a : K) :
    lvlSum κ 0 0 c a = ∑ j ∈ Finset.range (2 ^ κ), c j * novelBasis j a := by
  simp [lvlSum]

theorem lvlSum_top (κ s : ℕ) (c : ℕ → K) (a : K) : lvlSum κ κ s c a = c s := by
  simp [lvlSum, novelBasis_zero]

/-! ## The buffer invariant -/

/-- Entry `p` of the buffer at level `i`. -/
noncomputable def lvl (κ i : ℕ) (c : ℕ → K) (p : ℕ) : K :=
  lvlSum κ i (p % 2 ^ i) c (K.ofBits (p / 2 ^ i * 2 ^ i))

theorem decompose (i p : ℕ) :
    ∃ q s b, s < 2 ^ i ∧ b < 2 ∧ p = 2 ^ (i + 1) * q + 2 ^ i * b + s := by
  refine ⟨p / 2 ^ (i + 1), p % 2 ^ (i + 1) % 2 ^ i, p % 2 ^ (i + 1) / 2 ^ i,
    Nat.mod_lt _ (Nat.two_pow_pos i), ?_, ?_⟩
  · exact Nat.div_lt_of_lt_mul (by rw [← pow_succ]; exact Nat.mod_lt _ (Nat.two_pow_pos _))
  · have h1 := Nat.div_add_mod p (2 ^ (i + 1))
    have h2 := Nat.div_add_mod (p % 2 ^ (i + 1)) (2 ^ i)
    omega

section NormalForm

variable {i q s : ℕ}

theorem nf_eq (b : ℕ) : 2 ^ (i + 1) * q + 2 ^ i * b + s = 2 ^ i * (2 * q + b) + s := by ring

theorem nf_mod (hs : s < 2 ^ i) (b : ℕ) : (2 ^ (i + 1) * q + 2 ^ i * b + s) % 2 ^ i = s := by
  rw [nf_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt hs]

theorem nf_div (hs : s < 2 ^ i) (b : ℕ) : (2 ^ (i + 1) * q + 2 ^ i * b + s) / 2 ^ i = 2 * q + b := by
  rw [nf_eq, Nat.mul_add_div (Nat.two_pow_pos i), Nat.div_eq_of_lt hs, add_zero]

theorem nf_div2 (hs : s < 2 ^ i) {b : ℕ} (hb : b < 2) :
    (2 ^ (i + 1) * q + 2 ^ i * b + s) / 2 ^ (i + 1) = q := by
  have hlt : 2 ^ i * b + s < 2 ^ (i + 1) := by
    interval_cases b <;> rw [pow_succ] <;> omega
  rw [add_assoc, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt, add_zero]

theorem nf_mod2 (hs : s < 2 ^ i) {b : ℕ} (hb : b < 2) :
    (2 ^ (i + 1) * q + 2 ^ i * b + s) % 2 ^ (i + 1) = 2 ^ i * b + s := by
  have hlt : 2 ^ i * b + s < 2 ^ (i + 1) := by
    interval_cases b <;> rw [pow_succ] <;> omega
  rw [add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

theorem nf_testBit0 (hs : s < 2 ^ i) : (2 ^ (i + 1) * q + 2 ^ i * 0 + s).testBit i = false := by
  rw [Nat.testBit_eq_decide_div_mod_eq, nf_div hs]
  simp

theorem nf_testBit1 (hs : s < 2 ^ i) : (2 ^ (i + 1) * q + 2 ^ i * 1 + s).testBit i = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq, nf_div hs]
  simp [Nat.add_mod]

end NormalForm

/-- The four entries of a butterfly, at `a = x_{2^(i+1)·q}`. -/
theorem lvl_nf {κ i q s : ℕ} (hi : i < κ) (hκ : κ ≤ 64) (hs : s < 2 ^ i) (c : ℕ → K) :
    let a := K.ofBits (2 ^ (i + 1) * q)
    let A := lvlSum κ (i + 1) s c a
    let B := lvlSum κ (i + 1) (s + 2 ^ i) c a
    lvl κ i c (2 ^ (i + 1) * q + 2 ^ i * 0 + s) = A + normSubspacePoly i a * B ∧
      lvl κ i c (2 ^ (i + 1) * q + 2 ^ i * 1 + s) = A + (normSubspacePoly i a + 1) * B ∧
      lvl κ (i + 1) c (2 ^ (i + 1) * q + 2 ^ i * 0 + s) = A ∧
      lvl κ (i + 1) c (2 ^ (i + 1) * q + 2 ^ i * 1 + s) = B := by
  intro a A B
  have hi2 : 2 ^ i < 2 ^ (i + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hpt0 : (2 ^ (i + 1) * q + 2 ^ i * 0 + s) / 2 ^ i * 2 ^ i = 2 ^ (i + 1) * q := by
    rw [nf_div hs]; ring
  have hpt1 : (2 ^ (i + 1) * q + 2 ^ i * 1 + s) / 2 ^ i * 2 ^ i = 2 ^ (i + 1) * q + 2 ^ i := by
    rw [nf_div hs]; ring
  have hpt0' : (2 ^ (i + 1) * q + 2 ^ i * 0 + s) / 2 ^ (i + 1) * 2 ^ (i + 1) = 2 ^ (i + 1) * q := by
    rw [nf_div2 hs (by norm_num)]; ring
  have hpt1' : (2 ^ (i + 1) * q + 2 ^ i * 1 + s) / 2 ^ (i + 1) * 2 ^ (i + 1) = 2 ^ (i + 1) * q := by
    rw [nf_div2 hs (by norm_num)]; ring
  have hshift : K.ofBits (2 ^ (i + 1) * q + 2 ^ i) = a + K.ofBits (2 ^ i) :=
    ofBits_mul_two_pow_add hi2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lvl, nf_mod hs, hpt0, lvlSum_succ hi hκ]
  · rw [lvl, nf_mod hs, hpt1, hshift, lvlSum_succ hi hκ, lvlSum_add_ofBits hi2,
      lvlSum_add_ofBits hi2, normSubspacePoly_add_basis (by omega)]
  · rw [lvl, nf_mod2 hs (by norm_num), hpt0']
    simp [A, a]
  · rw [lvl, nf_mod2 hs (by norm_num), hpt1', mul_one, add_comm (2 ^ i) s]

/-! ## The stages -/

theorem getD_ofFn {n p : ℕ} (f : Fin n → K) (hp : p < n) : (Array.ofFn f).getD p 0 = f ⟨p, hp⟩ := by
  simp [Array.getD, hp]

theorem novelTwiddles_getD {m i q : ℕ} (hq : q < 2 ^ (m - (i + 1))) :
    (novelTwiddles m i).getD q 0 = normSubspacePoly i (K.ofBits (2 ^ (i + 1) * q)) := by
  rw [novelTwiddles, getD_ofFn _ hq, normSubspacePoly, Nat.mul_comm]

/-- The high part of an index below `2^m` is below `2^(m − (i+1))`. -/
theorem nf_bounds {m i q s b : ℕ} (him : i < m) (hs : s < 2 ^ i)
    (hp : 2 ^ (i + 1) * q + 2 ^ i * b + s < 2 ^ m) :
    q < 2 ^ (m - (i + 1)) ∧ 2 ^ (i + 1) * q + 2 ^ i * 1 + s < 2 ^ m := by
  have hm : 2 ^ m = 2 ^ (i + 1) * 2 ^ (m - (i + 1)) := by rw [← pow_add]; congr 1; omega
  have hq : q < 2 ^ (m - (i + 1)) := by
    have : 2 ^ (i + 1) * q < 2 ^ (i + 1) * 2 ^ (m - (i + 1)) := by rw [← hm]; omega
    exact Nat.lt_of_mul_lt_mul_left this
  refine ⟨hq, ?_⟩
  have h1 : 2 ^ (i + 1) * (q + 1) ≤ 2 ^ (i + 1) * 2 ^ (m - (i + 1)) := Nat.mul_le_mul_left _ hq
  have h2 : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
  rw [← hm] at h1
  rw [Nat.mul_add, mul_one] at h1
  omega

/-- **The inverse stage** takes level `i` to level `i + 1`. -/
theorem novelInvStage_getD {κ m i : ℕ} (hi : i < κ) (hκ : κ ≤ 64) (him : i < m) (c : ℕ → K)
    (b : Array K) (hb : ∀ p < 2 ^ m, b.getD p 0 = lvl κ i c p) :
    ∀ p < 2 ^ m, (novelInvStage m i b).getD p 0 = lvl κ (i + 1) c p := by
  intro p hp
  rw [novelInvStage, getD_ofFn _ hp]
  obtain ⟨q, s, bit, hs, hbit, rfl⟩ := decompose i p
  obtain ⟨hq, hp1⟩ := nf_bounds him hs hp
  obtain ⟨h0, h1, h0', h1'⟩ := lvl_nf (q := q) hi hκ hs c
  dsimp only
  rw [nf_div2 hs hbit, novelTwiddles_getD hq]
  interval_cases bit
  · have hp0 : 2 ^ (i + 1) * q + 2 ^ i * 0 + s + 2 ^ i = 2 ^ (i + 1) * q + 2 ^ i * 1 + s := by ring
    rw [nf_testBit0 hs]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hp0, hb _ hp, hb _ hp1, h0, h1, h0']
    linear_combination (CharTwo.two_eq_zero : (2 : K) = 0) *
      (normSubspacePoly i (K.ofBits (2 ^ (i + 1) * q)) *
        (lvlSum κ (i + 1) s c (K.ofBits (2 ^ (i + 1) * q)) +
          (normSubspacePoly i (K.ofBits (2 ^ (i + 1) * q)) + 1) *
            lvlSum κ (i + 1) (s + 2 ^ i) c (K.ofBits (2 ^ (i + 1) * q))))
  · have hm1 : 2 ^ (i + 1) * q + 2 ^ i * 1 + s - 2 ^ i = 2 ^ (i + 1) * q + 2 ^ i * 0 + s := by
      omega
    have hp0 : 2 ^ (i + 1) * q + 2 ^ i * 0 + s < 2 ^ m := by omega
    rw [nf_testBit1 hs]
    simp only [↓reduceIte]
    rw [hm1, hb _ hp0, hb _ hp, h0, h1, h1']
    linear_combination (CharTwo.two_eq_zero : (2 : K) = 0) *
      (lvlSum κ (i + 1) s c (K.ofBits (2 ^ (i + 1) * q)) +
        normSubspacePoly i (K.ofBits (2 ^ (i + 1) * q)) *
          lvlSum κ (i + 1) (s + 2 ^ i) c (K.ofBits (2 ^ (i + 1) * q)))

/-- **The forward stage** takes level `i + 1` to level `i`. -/
theorem novelFwdStage_getD {κ m i : ℕ} (hi : i < κ) (hκ : κ ≤ 64) (him : i < m) (c : ℕ → K)
    (b : Array K) (hb : ∀ p < 2 ^ m, b.getD p 0 = lvl κ (i + 1) c p) :
    ∀ p < 2 ^ m, (novelFwdStage m i b).getD p 0 = lvl κ i c p := by
  intro p hp
  rw [novelFwdStage, getD_ofFn _ hp]
  obtain ⟨q, s, bit, hs, hbit, rfl⟩ := decompose i p
  obtain ⟨hq, hp1⟩ := nf_bounds him hs hp
  obtain ⟨h0, h1, h0', h1'⟩ := lvl_nf (q := q) hi hκ hs c
  dsimp only
  rw [nf_div2 hs hbit, novelTwiddles_getD hq]
  interval_cases bit
  · have hp0 : 2 ^ (i + 1) * q + 2 ^ i * 0 + s + 2 ^ i = 2 ^ (i + 1) * q + 2 ^ i * 1 + s := by ring
    rw [nf_testBit0 hs]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hp0, hb _ hp, hb _ hp1, h0, h0', h1']
  · have hm1 : 2 ^ (i + 1) * q + 2 ^ i * 1 + s - 2 ^ i = 2 ^ (i + 1) * q + 2 ^ i * 0 + s := by
      omega
    have hp0 : 2 ^ (i + 1) * q + 2 ^ i * 0 + s < 2 ^ m := by omega
    rw [nf_testBit1 hs]
    simp only [↓reduceIte]
    rw [hm1, hb _ hp0, hb _ hp, h1, h0', h1']

/-! ## The transforms -/

theorem size_novelFwdStage (m i : ℕ) (b : Array K) : (novelFwdStage m i b).size = 2 ^ m :=
  Array.size_ofFn

theorem size_novelInvStage (m i : ℕ) (b : Array K) : (novelInvStage m i b).size = 2 ^ m :=
  Array.size_ofFn

/-- The forward transform after the stages `j, …, κ − 1` is at level `j`. -/
theorem novelFwd_levels {κ R : ℕ} (hκ : κ ≤ 64) (c : Array K) (d : ℕ) (hd : d ≤ κ) :
    ∀ p < 2 ^ (κ + R),
      ((List.range' (κ - d) d).foldr (fun i b ↦ novelFwdStage (κ + R) i b)
          (Array.ofFn fun p : Fin (2 ^ (κ + R)) ↦ c.getD (p.val % 2 ^ κ) 0)).getD p 0 =
        lvl κ (κ - d) (fun j ↦ c.getD j 0) p := by
  induction d with
  | zero =>
    intro p hp
    rw [List.range'_zero, List.foldr_nil, getD_ofFn _ hp, Nat.sub_zero, lvl, lvlSum_top]
  | succ d ih =>
    intro p hp
    have hsucc : κ - (d + 1) + 1 = κ - d := by omega
    rw [List.range'_succ, List.foldr_cons, hsucc]
    have hi : κ - (d + 1) < κ := by omega
    refine novelFwdStage_getD hi hκ (by omega) _ _ ?_ p hp
    rw [show κ - (d + 1) + 1 = κ - d by omega]
    exact ih (by omega)

/-- **The forward transform evaluates**: entry `v < 2^(κ+R)` of `novelFwd κ R c` is
`Σ_{j<2^κ} c_j·X_j(x_v)`. -/
theorem novelFwd_getD {κ R : ℕ} (hκ : κ ≤ 64) (c : Array K) {v : ℕ} (hv : v < 2 ^ (κ + R)) :
    (novelFwd κ R c).getD v 0 = ∑ j ∈ Finset.range (2 ^ κ), c.getD j 0 * novelBasis j (K.ofBits v) := by
  have h := novelFwd_levels (R := R) hκ c κ le_rfl v hv
  rw [Nat.sub_self] at h
  rw [novelFwd, List.range_eq_range', h, lvl, Nat.pow_zero, Nat.mod_one, Nat.div_one, Nat.mul_one,
    lvlSum_zero]

theorem size_novelFwd {κ R : ℕ} (c : Array K) : (novelFwd κ R c).size = 2 ^ (κ + R) := by
  unfold novelFwd
  cases κ with
  | zero => simp
  | succ κ => rw [List.range_succ_eq_map, List.foldr_cons, size_novelFwdStage]

/-- The inverse transform after the stages `0, …, d − 1` is at level `d`. -/
theorem novelInv_levels {κ : ℕ} (hκ : κ ≤ 64) (c : ℕ → K) (y : Array K)
    (hy : ∀ v < 2 ^ κ, y.getD v 0 = ∑ j ∈ Finset.range (2 ^ κ), c j * novelBasis j (K.ofBits v))
    (d : ℕ) (hd : d ≤ κ) :
    ∀ p < 2 ^ κ, ((List.range d).foldl (fun b i ↦ novelInvStage κ i b) y).getD p 0 = lvl κ d c p := by
  induction d with
  | zero =>
    intro p hp
    simp [lvl, Nat.mod_one, lvlSum_zero, hy p hp]
  | succ d ih =>
    intro p hp
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact novelInvStage_getD (by omega) hκ (by omega) c _ (ih (by omega)) p hp

/-- **The inverse transform recovers the coefficients.** -/
theorem novelInv_getD {κ : ℕ} (hκ : κ ≤ 64) (c : ℕ → K) (y : Array K)
    (hy : ∀ v < 2 ^ κ, y.getD v 0 = ∑ j ∈ Finset.range (2 ^ κ), c j * novelBasis j (K.ofBits v))
    {p : ℕ} (hp : p < 2 ^ κ) : (novelInv κ y).getD p 0 = c p := by
  rw [novelInv, novelInv_levels hκ c y hy κ le_rfl p hp, lvl, lvlSum_top, Nat.mod_eq_of_lt hp]

theorem size_novelInv {κ : ℕ} (y : Array K) (hy : y.size = 2 ^ κ) : (novelInv κ y).size = 2 ^ κ := by
  unfold novelInv
  cases κ with
  | zero => simpa using hy
  | succ κ => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      size_novelInvStage]

theorem array_ext_getD {a b : Array K} (h : a.size = b.size)
    (hg : ∀ p < a.size, a.getD p 0 = b.getD p 0) : a = b := by
  apply Array.ext h
  intro p h1 h2
  have := hg p h1
  simp only [Array.getD, h1, h2, dite_true] at this
  exact this

/-- **The inverse transform**, as an equation of arrays. -/
theorem novelInv_eval {κ : ℕ} (hκ : κ ≤ 64) (c : ℕ → K) (y : Array K) (hsize : y.size = 2 ^ κ)
    (hy : ∀ v < 2 ^ κ, y.getD v 0 = ∑ j ∈ Finset.range (2 ^ κ), c j * novelBasis j (K.ofBits v)) :
    novelInv κ y = Array.ofFn fun j : Fin (2 ^ κ) ↦ c j := by
  apply array_ext_getD (by rw [size_novelInv y hsize, Array.size_ofFn])
  intro p hp
  rw [size_novelInv y hsize] at hp
  rw [novelInv_getD hκ c y hy hp, getD_ofFn _ hp]

/-- **Round trip**: coefficients → evaluations → coefficients. -/
theorem novelInv_novelFwd {κ : ℕ} (hκ : κ ≤ 64) (c : Array K) (hc : c.size = 2 ^ κ) :
    novelInv κ (novelFwd κ 0 c) = c := by
  rw [novelInv_eval hκ (fun j ↦ c.getD j 0) _ (by rw [size_novelFwd, Nat.add_zero])
    fun v hv ↦ novelFwd_getD hκ c (by rwa [Nat.add_zero])]
  apply array_ext_getD (by rw [Array.size_ofFn, hc])
  intro p hp
  rw [Array.size_ofFn] at hp
  rw [getD_ofFn _ hp]

/-! ## The stages invert each other (characteristic-two algebra) -/

theorem novelFwdStage_novelInvStage {m i : ℕ} (him : i < m) (b : Array K) (hb : b.size = 2 ^ m) :
    novelFwdStage m i (novelInvStage m i b) = b := by
  apply array_ext_getD (by rw [size_novelFwdStage, hb])
  intro p hp
  rw [size_novelFwdStage] at hp
  rw [novelFwdStage, getD_ofFn _ hp]
  obtain ⟨q, s, bit, hs, hbit, rfl⟩ := decompose i p
  obtain ⟨hq, hp1⟩ := nf_bounds him hs hp
  dsimp only
  rw [nf_div2 hs hbit]
  have hp0' : 2 ^ (i + 1) * q + 2 ^ i * 0 + s + 2 ^ i = 2 ^ (i + 1) * q + 2 ^ i * 1 + s := by ring
  have hm1 : 2 ^ (i + 1) * q + 2 ^ i * 1 + s - 2 ^ i = 2 ^ (i + 1) * q + 2 ^ i * 0 + s := by
    omega
  have hp0 : 2 ^ (i + 1) * q + 2 ^ i * 0 + s < 2 ^ m := by
    interval_cases bit
    · exact hp
    · omega
  have hlo : (novelInvStage m i b).getD (2 ^ (i + 1) * q + 2 ^ i * 0 + s) 0 =
      b.getD (2 ^ (i + 1) * q + 2 ^ i * 0 + s) 0 + (novelTwiddles m i).getD q 0 *
        (b.getD (2 ^ (i + 1) * q + 2 ^ i * 0 + s) 0 + b.getD (2 ^ (i + 1) * q + 2 ^ i * 1 + s) 0) := by
    rw [novelInvStage, getD_ofFn _ hp0]
    dsimp only
    rw [nf_testBit0 hs, nf_div2 hs (by norm_num), hp0']
    simp only [Bool.false_eq_true, ↓reduceIte]
  have hhi : (novelInvStage m i b).getD (2 ^ (i + 1) * q + 2 ^ i * 1 + s) 0 =
      b.getD (2 ^ (i + 1) * q + 2 ^ i * 0 + s) 0 + b.getD (2 ^ (i + 1) * q + 2 ^ i * 1 + s) 0 := by
    rw [novelInvStage, getD_ofFn _ hp1]
    dsimp only
    rw [nf_testBit1 hs, hm1]
    simp only [↓reduceIte]
  interval_cases bit
  · rw [nf_testBit0 hs]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hp0', hlo, hhi]
    linear_combination (CharTwo.two_eq_zero : (2 : K) = 0) *
      ((novelTwiddles m i).getD q 0 *
        (b.getD (2 ^ (i + 1) * q + 2 ^ i * 0 + s) 0 + b.getD (2 ^ (i + 1) * q + 2 ^ i * 1 + s) 0))
  · rw [nf_testBit1 hs]
    simp only [↓reduceIte]
    rw [hm1, hlo, hhi]
    linear_combination (CharTwo.two_eq_zero : (2 : K) = 0) *
      (b.getD (2 ^ (i + 1) * q + 2 ^ i * 0 + s) 0 + (novelTwiddles m i).getD q 0 *
        (b.getD (2 ^ (i + 1) * q + 2 ^ i * 0 + s) 0 + b.getD (2 ^ (i + 1) * q + 2 ^ i * 1 + s) 0))

/-- **Round trip**: evaluations on `U_κ` → coefficients → evaluations. -/
theorem novelFwd_novelInv {κ : ℕ} (y : Array K) (hy : y.size = 2 ^ κ) :
    novelFwd κ 0 (novelInv κ y) = y := by
  have htile : (Array.ofFn fun p : Fin (2 ^ (κ + 0)) ↦ (novelInv κ y).getD (p.val % 2 ^ κ) 0) =
      novelInv κ y := by
    apply array_ext_getD (by rw [Array.size_ofFn, size_novelInv y hy, Nat.add_zero])
    intro p hp
    rw [Array.size_ofFn] at hp
    rw [getD_ofFn _ hp, Nat.mod_eq_of_lt (by simpa using hp)]
  rw [novelFwd, htile, novelInv]
  -- peel the stages from the top: `fwd_{0..d−1} ∘ inv_{0..d−1} = id`
  have key : ∀ d ≤ κ, (List.range d).foldr (fun i b ↦ novelFwdStage (κ + 0) i b)
      ((List.range d).foldl (fun b i ↦ novelInvStage κ i b) y) = y := by
    intro d hd
    induction d with
    | zero => simp
    | succ d ih =>
      rw [List.range_succ, List.foldl_append, List.foldr_append, List.foldl_cons, List.foldl_nil,
        List.foldr_cons, List.foldr_nil, Nat.add_zero,
        novelFwdStage_novelInvStage (by omega) _ ?_]
      · exact ih (by omega)
      · clear ih
        induction d with
        | zero => simpa using hy
        | succ d ih' =>
          rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
            size_novelInvStage]
  exact key κ le_rfl

/-- **The forward transform is the statement's encoding**: `encode q u v` is entry `v` of the
forward transform of lane `u`, for every column `v < 2^(κ+R)`, `κ = μ − 6 ≤ 64`. -/
theorem encode_eq_novelFwd {μ R : ℕ} (hμ : μ - LeanVM.Parameters.Whir.initialFold ≤ 64)
    (q : Vector K (2 ^ μ)) (u : ℕ) {v : ℕ}
    (hv : v < 2 ^ (μ - LeanVM.Parameters.Whir.initialFold + R)) :
    encode q u v = (novelFwd (μ - LeanVM.Parameters.Whir.initialFold) R (laneCoeffs q u)).getD v 0 := by
  rw [novelFwd_getD hμ _ hv, encode]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [laneCoeffs, getD_ofFn _ (Finset.mem_range.mp hj)]

/-! ## Monomial to novel basis -/

/-- **`toNovel` returns the novel-basis coefficients** of a polynomial whose values on `U_κ`
are those of `Σ_{j<2^κ} c_j·X_j`. -/
theorem toNovel_eq {κ : ℕ} (hκ : κ ≤ 64) (p : CompPoly.CPolynomial K) (c : ℕ → K)
    (h : ∀ v < 2 ^ κ, p.eval (K.ofBits v) =
      ∑ j ∈ Finset.range (2 ^ κ), c j * novelBasis j (K.ofBits v)) :
    toNovel κ p = Array.ofFn fun j : Fin (2 ^ κ) ↦ c j := by
  apply novelInv_eval hκ c _ Array.size_ofFn
  intro v hv
  rw [getD_ofFn _ hv, h v hv]

/-- The novel basis polynomial `X_j = ∏_{bit i of j} Ŵ_i` as a Mathlib polynomial. -/
@[expose] noncomputable def novelPoly (j : ℕ) : Polynomial K :=
  ∏ i ∈ Finset.range 64,
    if j.testBit i then Polynomial.C (subspacePoly i (K.ofBits (2 ^ i)))⁻¹ * vanishing i else 1

theorem eval_novelPoly (j : ℕ) (a : K) : (novelPoly j).eval a = novelBasis j a := by
  rw [novelPoly, novelBasis, Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  split
  · rw [Polynomial.eval_mul, Polynomial.eval_C, eval_vanishing, normSubspacePoly, mul_comm]
  · simp

/-- **`toNovel (msgPoly c) = c`**: if `p.toPoly = Σ_{j<2^κ} c_j·X_j`, then `toNovel κ p = c`. -/
theorem toNovel_of_toPoly {κ : ℕ} (hκ : κ ≤ 64) (p : CompPoly.CPolynomial K) (c : ℕ → K)
    (h : p.toPoly = ∑ j ∈ Finset.range (2 ^ κ), Polynomial.C (c j) * novelPoly j) :
    toNovel κ p = Array.ofFn fun j : Fin (2 ^ κ) ↦ c j := by
  refine toNovel_eq hκ p c fun v _ ↦ ?_
  rw [CompPoly.CPolynomial.eval_toPoly, h, Polynomial.eval_finsetSum]
  simp [eval_novelPoly]

end
end LeanVM.Extraction.NovelProofs
