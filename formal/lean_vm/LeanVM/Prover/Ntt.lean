/-
  LeanVM.Prover.Ntt

  The additive NTT computes the encoder of leanVM's binary Reed-Solomon code: the executable
  committed words are the specification's, at every position.
-/

module

public import Statement.Prover.Ntt
public import LeanVM.Protocol.Whir.Complete.Encoding

/-!
# The additive NTT is the encoder

* `hatAt_eq`: the table of `Ŵ_c(e_m)` (by the recurrence `W_{c+1}(a) = W_c(a)·(W_c(a) +
  W_c(e_c))`) gives `Ŵ_c(x_n)` by additivity.
* `ntt_getD`: the transform's entry at `p < 2^(κ+R)` is `encKAt κ msg p`. The invariant
  (`stageVal`): after the variables `κ-1, …, i` are folded, position `p` holds the lane
  `p mod 2^i` of the message folded at `Ŵ_i(x_p), …, Ŵ_{κ-1}(x_p)` in the monomial basis
  (`mono`); a stage keeps it (`stageVal_step`) because `Ŵ_m` is additive and vanishes on `U_m`,
  and `Ŵ_i(e_i) = 1`.
* `ntt_getD'`: past the domain, the transform's array reads `0`, as the specification's words
  hold there.
* `stackWordFast_eq`: the executable stack word is `stackWord μ R q` at every position, for the
  stack array `q.values.toArray`; `levelWordFast_eq`: the executable level word is
  `levelWord κ k R g` at every position.
-/

namespace LeanVM.Prover.Enc

open LeanVM.Parameters LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Complete LeanVM.Protocol
open LeanVM.Protocol.EndToEnd Finset

@[expose] public section

/-! ## Arrays -/

theorem getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) (d : α) (hi : i < n) :
    (Array.ofFn f).getD i d = f ⟨i, hi⟩ := by
  simp [hi]

theorem getD_map_of_lt {α β : Type} (f : α → β) (a : Array α) (i : ℕ) (d : α) (d' : β)
    (hi : i < a.size) : (a.map f).getD i d' = f (a.getD i d) := by
  simp [hi]

/-! ## The subspace polynomials on the basis -/

theorem size_vanRow : ∀ c, (vanRow c).size = 64
  | 0 => by simp [vanRow]
  | c + 1 => by simp [vanRow, size_vanRow c]

theorem vanishingAt_zero_left (a : K) : vanishingAt 0 a = a := by simp [vanishingAt]

theorem vanRow_getD : ∀ c, c < 64 → ∀ m, m < 64 → (vanRow c).getD m 0 = vanishingAt c (basisVec m)
  | 0, _, m, hm => by
    rw [vanRow, getD_ofFn _ _ _ hm, vanishingAt_zero_left]
    rfl
  | c + 1, hc, m, hm => by
    simp only [vanRow]
    rw [getD_map_of_lt _ _ _ 0 _ (by rw [size_vanRow]; exact hm), vanRow_getD c (by omega) m hm,
      vanRow_getD c (by omega) c (by omega), vanishingAt_succ, sq]

theorem hatRow_getD {c m : ℕ} (hc : c < 64) (hm : m < 64) :
    (hatRow c).getD m 0 = normVanishingAt c (basisVec m) := by
  simp only [hatRow]
  rw [getD_map_of_lt _ _ _ 0 _ (by rw [size_vanRow]; exact hm), vanRow_getD c hc m hm,
    vanRow_getD c hc c hc, normVanishingAt]

theorem hatTable_getD {c : ℕ} (hc : c < 64) : hatTable.getD c #[] = hatRow c := by
  rw [hatTable, getD_ofFn _ _ _ hc]

theorem foldl_range_ite (P : ℕ → Bool) (f : ℕ → K) :
    ∀ (n : ℕ) (a : K), (List.range n).foldl (fun acc m ↦ if P m then acc + f m else acc) a =
      a + ∑ m ∈ range n, if P m then f m else 0
  | 0, a => by simp
  | n + 1, a => by
    rw [List.range_succ, List.foldl_append, foldl_range_ite P f n a, sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    split <;> simp [add_assoc]

/-- `Ŵ_c` as an additive map. -/
def normHom (c : ℕ) : K →+ K where
  toFun := normVanishingAt c
  map_zero' := by simp [normVanishingAt]
  map_add' := normVanishingAt_add c

theorem ofBits_mod (n : ℕ) : K.ofBits (n % 2 ^ 64) = K.ofBits n := by
  simp only [K.ofBits]
  congr 1
  exact BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_ofNat])

/-- **`Ŵ_c(x_n)` from the table.** -/
theorem hatAt_eq {c : ℕ} (hc : c < 64) (n : ℕ) : hatAt c n = normVanishingAt c (K.ofBits n) := by
  simp only [hatAt]
  rw [foldl_range_ite, zero_add, hatTable_getD hc, ← ofBits_mod,
    ofBits_eq_sum (Nat.mod_lt _ (by positivity))]
  change _ = normHom c _
  rw [map_sum]
  refine sum_congr rfl fun m hm ↦ ?_
  have hm' := mem_range.mp hm
  rw [Nat.testBit_mod_two_pow, decide_eq_true hm', Bool.true_and, hatRow_getD hc hm']
  split <;> simp [normHom, normVanishingAt]

/-! ## The monomial-basis fold -/

theorem sum_range_two_mul {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ range (2 * n), f i = ∑ j ∈ range n, (f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

/-- `Σ_{v < 2^n} f(v)·∏_{k < n, v_k} w(k)`: the message `f` on `n` variables evaluated in the
monomial basis at `w`. -/
def mono (n : ℕ) (f w : ℕ → K) : K :=
  ∑ v ∈ range (2 ^ n), f v * ∏ k ∈ range n, if v.testBit k then w k else 1

theorem mono_zero (f w : ℕ → K) : mono 0 f w = f 0 := by simp [mono]

theorem testBit_two_mul_zero (v : ℕ) : (2 * v).testBit 0 = false := by simp

theorem testBit_two_mul_add_one_zero (v : ℕ) : (2 * v + 1).testBit 0 = true := by simp

theorem testBit_two_mul_succ (v k : ℕ) : (2 * v).testBit (k + 1) = v.testBit k := by
  rw [Nat.testBit_add_one, Nat.mul_div_cancel_left _ (by norm_num)]

theorem testBit_two_mul_add_one_succ (v k : ℕ) : (2 * v + 1).testBit (k + 1) = v.testBit k := by
  rw [Nat.testBit_add_one, show (2 * v + 1) / 2 = v by omega]

/-- **Folding the low variable** of the monomial-basis evaluation. -/
theorem mono_succ (n : ℕ) (f w : ℕ → K) :
    mono (n + 1) f w = mono n (fun v ↦ f (2 * v)) (fun k ↦ w (k + 1)) +
      w 0 * mono n (fun v ↦ f (2 * v + 1)) (fun k ↦ w (k + 1)) := by
  rw [mono, pow_succ, mul_comm, sum_range_two_mul, mono, mono, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun v _ ↦ ?_
  rw [prod_range_succ', prod_range_succ']
  simp only [testBit_two_mul_zero, testBit_two_mul_add_one_zero, testBit_two_mul_succ,
    testBit_two_mul_add_one_succ, Bool.false_eq_true, ↓reduceIte]
  ring

/-! ## The subspace polynomials on positions -/

theorem add_two_pow_mul_eq_xor {s j : ℕ} (hj : j < 2 ^ s) (c : ℕ) :
    j + 2 ^ s * c = j ^^^ 2 ^ s * c := by
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_xor, add_comm, Nat.testBit_two_pow_mul_add _ hj, Nat.testBit_two_pow_mul]
  by_cases hn : n < s
  · simp [hn, show ¬ s ≤ n by omega]
  · have : j.testBit n = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hn, this, show s ≤ n by omega]

theorem normVanishingAt_ofBits_lt {m j : ℕ} (hj : j < 2 ^ m) :
    normVanishingAt m (K.ofBits j) = 0 := by
  have : vanishingAt m (K.ofBits j) = 0 :=
    (vanishingAt_eq_zero_iff m _).mpr (mem_image.mpr ⟨j, mem_range.mpr hj, rfl⟩)
  rw [normVanishingAt, this, zero_mul]

/-- `Ŵ_m` ignores the bits below `s ≤ m`. -/
theorem normVanishingAt_add_two_pow_mul {s m j : ℕ} (hsm : s ≤ m) (hj : j < 2 ^ s) (c : ℕ) :
    normVanishingAt m (K.ofBits (j + 2 ^ s * c)) = normVanishingAt m (K.ofBits (2 ^ s * c)) := by
  rw [add_two_pow_mul_eq_xor hj, ofBits_xor, normVanishingAt_add,
    normVanishingAt_ofBits_lt (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) hsm)),
    zero_add]

/-- `Ŵ_i` on the block `b` of `2^(i+1)` positions: the twiddle, plus `1` on the upper half. -/
theorem normVanishingAt_block {i r : ℕ} (hi : i < 64) (hr : r < 2 ^ (i + 1)) (b : ℕ) :
    normVanishingAt i (K.ofBits (r + 2 ^ (i + 1) * b)) =
      normVanishingAt i (K.ofBits (2 ^ (i + 1) * b)) + if r < 2 ^ i then 0 else 1 := by
  rw [add_two_pow_mul_eq_xor hr, ofBits_xor, normVanishingAt_add, add_comm]
  suffices h : normVanishingAt i (K.ofBits r) = if r < 2 ^ i then 0 else 1 by rw [h]
  by_cases hri : r < 2 ^ i
  · simp only [hri, ↓reduceIte]
    exact normVanishingAt_ofBits_lt hri
  · simp only [hri, ↓reduceIte]
    have h1 : r - 2 ^ i < 2 ^ i := by rw [pow_succ] at hr; omega
    rw [show r = 2 ^ i + (r - 2 ^ i) by omega, ofBits_two_pow_add h1, normVanishingAt_add,
      normVanishingAt_basisVec hi, normVanishingAt_ofBits_lt h1, add_zero]

/-! ## The stages -/

/-- The table after the variables `κ-1, …, i` are folded: position `p` holds the lane
`p mod 2^i` of the message folded at `Ŵ_i(x_p), …, Ŵ_{κ-1}(x_p)`. -/
def stageVal (κ : ℕ) (msg : ℕ → K) (i p : ℕ) : K :=
  mono (κ - i) (fun v ↦ msg (p % 2 ^ i + 2 ^ i * v))
    (fun k ↦ normVanishingAt (i + k) (K.ofBits p))

theorem stageVal_top (κ : ℕ) (msg : ℕ → K) (p : ℕ) : stageVal κ msg κ p = msg (p % 2 ^ κ) := by
  simp [stageVal, mono_zero]

/-- **A stage of the transform**: at `p = r + 2^(i+1)·b` (`r < 2^(i+1)`), the table at `i` is the
pair at `lo = r mod 2^i + 2^(i+1)·b` and `lo + 2^i` of the table at `i + 1`, combined with the
block's twiddle, plus `1` on the upper half. -/
theorem stageVal_step {κ i : ℕ} (hi : i < κ) (hκ : κ ≤ 64) (msg : ℕ → K) (p : ℕ) :
    stageVal κ msg i p =
      stageVal κ msg (i + 1) (p / 2 ^ (i + 1) * 2 ^ (i + 1) + p % 2 ^ (i + 1) % 2 ^ i) +
        (normVanishingAt i (K.ofBits (p / 2 ^ (i + 1) * 2 ^ (i + 1))) +
          if p % 2 ^ (i + 1) < 2 ^ i then 0 else 1) *
        stageVal κ msg (i + 1)
          (p / 2 ^ (i + 1) * 2 ^ (i + 1) + p % 2 ^ (i + 1) % 2 ^ i + 2 ^ i) := by
  set b := p / 2 ^ (i + 1)
  set r := p % 2 ^ (i + 1)
  have hr : r < 2 ^ (i + 1) := Nat.mod_lt _ (by positivity)
  have hp : p = r + 2 ^ (i + 1) * b := by rw [Nat.mod_add_div]
  have hj : r % 2 ^ i < 2 ^ i := Nat.mod_lt _ (by positivity)
  have hj1 : r % 2 ^ i < 2 ^ (i + 1) := lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hj2 : r % 2 ^ i + 2 ^ i < 2 ^ (i + 1) := by rw [pow_succ]; omega
  have hrp : p % 2 ^ i = r % 2 ^ i := by
    rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (Nat.le_succ i))]
  have hlo : b * 2 ^ (i + 1) + r % 2 ^ i = r % 2 ^ i + 2 ^ (i + 1) * b := by ring
  have hhi : b * 2 ^ (i + 1) + r % 2 ^ i + 2 ^ i = (r % 2 ^ i + 2 ^ i) + 2 ^ (i + 1) * b := by ring
  have hκi : κ - i = κ - (i + 1) + 1 := by omega
  -- the evaluation points: `Ŵ_m` for `m > i` reads the block only
  have hW : ∀ k, normVanishingAt (i + (k + 1)) (K.ofBits p) =
      normVanishingAt (i + 1 + k) (K.ofBits (2 ^ (i + 1) * b)) := fun k ↦ by
    rw [hp, normVanishingAt_add_two_pow_mul (by omega) hr, show i + (k + 1) = i + 1 + k by ring]
  have hWlo : ∀ k, normVanishingAt (i + 1 + k) (K.ofBits (b * 2 ^ (i + 1) + r % 2 ^ i)) =
      normVanishingAt (i + 1 + k) (K.ofBits (2 ^ (i + 1) * b)) := fun k ↦ by
    rw [hlo, normVanishingAt_add_two_pow_mul (by omega) hj1]
  have hWhi : ∀ k, normVanishingAt (i + 1 + k) (K.ofBits (b * 2 ^ (i + 1) + r % 2 ^ i + 2 ^ i)) =
      normVanishingAt (i + 1 + k) (K.ofBits (2 ^ (i + 1) * b)) := fun k ↦ by
    rw [hhi, normVanishingAt_add_two_pow_mul (by omega) hj2]
  have hW0 : normVanishingAt i (K.ofBits p) =
      normVanishingAt i (K.ofBits (b * 2 ^ (i + 1))) + if r < 2 ^ i then 0 else 1 := by
    rw [hp, normVanishingAt_block (by omega) hr, mul_comm b]
  rw [stageVal, hκi, mono_succ, add_zero, hW0, stageVal, stageVal]
  simp only [hW, hWlo, hWhi]
  have hmlo : (b * 2 ^ (i + 1) + r % 2 ^ i) % 2 ^ (i + 1) = r % 2 ^ i := by
    rw [hlo, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj1]
  have hmhi : (b * 2 ^ (i + 1) + r % 2 ^ i + 2 ^ i) % 2 ^ (i + 1) = r % 2 ^ i + 2 ^ i := by
    rw [hhi, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj2]
  rw [hmlo, hmhi, hrp]
  have e1 : (fun v ↦ msg (r % 2 ^ i + 2 ^ i * (2 * v))) =
      fun v ↦ msg (r % 2 ^ i + 2 ^ (i + 1) * v) := by
    funext v; congr 1; rw [pow_succ]; ring
  have e2 : (fun v ↦ msg (r % 2 ^ i + 2 ^ i * (2 * v + 1))) =
      fun v ↦ msg (r % 2 ^ i + 2 ^ i + 2 ^ (i + 1) * v) := by
    funext v; congr 1; rw [pow_succ]; ring
  rw [e1, e2]

/-! ## The sum over the cube -/

theorem sum_cube_K (κ : ℕ) (F : (Fin κ → Bool) → K) :
    ∑ u, F u = ∑ i ∈ range (2 ^ κ), F fun k ↦ i.testBit k := by
  rw [← Equiv.sum_comp (bitsEquiv κ).symm,
    ← Fin.sum_univ_eq_sum_range (fun i ↦ F fun k ↦ i.testBit k)]
  exact sum_congr rfl fun j _ ↦ by
    congr 1; funext k; exact bitsEquiv_symm_apply j k

theorem stageVal_bottom {κ : ℕ} (hκ : κ ≤ 64) (msg : ℕ → K) (p : ℕ) :
    stageVal κ msg 0 p = encKAt κ (fun u ↦ msg (bitsToNat u)) p := by
  rw [stageVal, encKAt, sum_cube_K, mono, Nat.sub_zero]
  refine sum_congr rfl fun v hv ↦ ?_
  have hv' := mem_range.mp hv
  simp only [pow_zero, Nat.mod_one, one_mul, zero_add]
  rw [bitsToNat_testBit hv']
  congr 1
  conv_rhs => rw [← bitsToNat_testBit hv']
  rw [novelAt_bitsToNat hκ, ← Fin.prod_univ_eq_prod_range
    (fun k ↦ if v.testBit k then normVanishingAt k (K.ofBits p) else 1)]

/-! ## The transform -/

theorem size_nttStage (N i : ℕ) (tw a : Array K) : (nttStage N i tw a).size = 2 ^ N := by
  simp [nttStage, nttStage.nttStageAt]

/-- **One stage** takes the table at `i + 1` to the table at `i`. -/
theorem nttStage_getD {κ N i : ℕ} (hi : i < κ) (hκ : κ ≤ 64) (hκN : κ ≤ N) (msg : ℕ → K)
    (a : Array K) (ha : ∀ q < 2 ^ N, a.getD q 0 = stageVal κ msg (i + 1) q) (p : ℕ)
    (hp : p < 2 ^ N) : (nttStage N i (stageTwiddles N i) a).getD p 0 = stageVal κ msg i p := by
  set b := p / 2 ^ (i + 1) with hb
  set r := p % 2 ^ (i + 1) with hr
  have hNi : N = (N - (i + 1)) + (i + 1) := by omega
  have hb' : b < 2 ^ (N - (i + 1)) := by
    rw [hb, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, ← hNi]; exact hp
  have hr' : r < 2 ^ (i + 1) := Nat.mod_lt _ (by positivity)
  have hj : r % 2 ^ i < 2 ^ i := Nat.mod_lt _ (by positivity)
  have hNpow : 2 ^ N = 2 ^ (N - (i + 1)) * 2 ^ (i + 1) := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have hbN : (b + 1) * 2 ^ (i + 1) ≤ 2 ^ N := by
    rw [hNpow]; exact Nat.mul_le_mul_right _ hb'
  have hj1 : r % 2 ^ i < 2 ^ (i + 1) :=
    lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hj2 : r % 2 ^ i + 2 ^ i < 2 ^ (i + 1) := by rw [pow_succ]; omega
  have hlo : b * 2 ^ (i + 1) + r % 2 ^ i < 2 ^ N :=
    calc b * 2 ^ (i + 1) + r % 2 ^ i < b * 2 ^ (i + 1) + 2 ^ (i + 1) := Nat.add_lt_add_left hj1 _
      _ = (b + 1) * 2 ^ (i + 1) := by ring
      _ ≤ 2 ^ N := hbN
  have hhi : b * 2 ^ (i + 1) + r % 2 ^ i + 2 ^ i < 2 ^ N :=
    calc b * 2 ^ (i + 1) + r % 2 ^ i + 2 ^ i < b * 2 ^ (i + 1) + 2 ^ (i + 1) := by
          rw [add_assoc]; exact Nat.add_lt_add_left hj2 _
      _ = (b + 1) * 2 ^ (i + 1) := by ring
      _ ≤ 2 ^ N := hbN
  have hq : b * 2 ^ i + r % 2 ^ i < 2 ^ (N - 1) := by
    have hN1 : 2 ^ (N - 1) = 2 ^ (N - (i + 1)) * 2 ^ i := by
      rw [← pow_add, show N - (i + 1) + i = N - 1 by omega]
    have : (b + 1) * 2 ^ i ≤ 2 ^ (N - 1) := by
      rw [hN1]; exact Nat.mul_le_mul_right _ hb'
    calc b * 2 ^ i + r % 2 ^ i < b * 2 ^ i + 2 ^ i := Nat.add_lt_add_left hj _
      _ = (b + 1) * 2 ^ i := by ring
      _ ≤ 2 ^ (N - 1) := this
  have hqd : (b * 2 ^ i + r % 2 ^ i) / 2 ^ i = b := by
    rw [mul_comm, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hj, add_zero]
  have hqm : (b * 2 ^ i + r % 2 ^ i) % 2 ^ i = r % 2 ^ i := by
    rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  rw [stageVal_step hi hκ msg p]
  simp only [nttStage, nttStage.nttStageAt]
  rw [getD_ofFn _ _ _ hp]
  simp only [← hb, ← hr]
  rw [getD_ofFn _ _ _ hq]
  simp only
  rw [hqd, hqm, show b * 2 ^ (i + 1) + 2 ^ i + r % 2 ^ i = b * 2 ^ (i + 1) + r % 2 ^ i + 2 ^ i by
      ring, ha _ hlo, ha _ hhi, stageTwiddles, getD_ofFn _ _ _ hb', hatAt_eq (by omega)]
  by_cases hri : r < 2 ^ i
  · simp only [hri, ↓reduceIte]; ring
  · simp only [hri, ↓reduceIte]; ring

theorem ntt_go_getD {κ R : ℕ} (hκ : κ ≤ 64) (msg : ℕ → K) :
    ∀ i, i ≤ κ → ∀ a : Array K, a.size = 2 ^ (κ + R) →
      (∀ q < 2 ^ (κ + R), a.getD q 0 = stageVal κ msg i q) →
      ∀ p < 2 ^ (κ + R), (ntt.go (nttTwiddles (κ + R) κ) κ R i a).getD p 0 = stageVal κ msg 0 p
  | 0, _, a, _, ha, p, hp => by rw [ntt.go]; exact ha p hp
  | i + 1, hi, a, hs, ha, p, hp => by
    rw [ntt.go, nttTwiddles, getD_ofFn _ _ _ (by omega)]
    exact ntt_go_getD hκ msg i (by omega) _ (size_nttStage _ _ _ _)
      (fun q hq ↦ nttStage_getD (by omega) hκ (by omega) msg a ha q hq) p hp

/-- **The additive NTT is the encoder**: its entry at `p < 2^(κ+R)` is `Enc(msg)(x_p)`. -/
theorem ntt_getD {κ R : ℕ} (hκ : κ ≤ 64) (msg : Array K) {p : ℕ} (hp : p < 2 ^ (κ + R)) :
    (ntt (nttTwiddles (κ + R) κ) κ R msg).getD p 0 =
      encKAt κ (fun u ↦ msg.getD (bitsToNat u) 0) p := by
  rw [ntt, ntt_go_getD hκ (fun v ↦ msg.getD v 0) κ le_rfl _ (by simp) (fun q hq ↦ ?_) p hp,
    stageVal_bottom hκ]
  rw [getD_ofFn _ _ _ hq, stageVal_top]

theorem size_ntt_go (tws : Array (Array K)) (κ R : ℕ) :
    ∀ i (a : Array K), a.size = 2 ^ (κ + R) → (ntt.go tws κ R i a).size = 2 ^ (κ + R)
  | 0, _, h => by rw [ntt.go]; exact h
  | i + 1, _, _ => by rw [ntt.go]; exact size_ntt_go tws κ R i _ (size_nttStage _ _ _ _)

/-- The transform's entry at every `p`: the encoder on the domain, `0` past the array's end. -/
theorem ntt_getD' {κ R : ℕ} (hκ : κ ≤ 64) (msg : Array K) (p : ℕ) :
    (ntt (nttTwiddles (κ + R) κ) κ R msg).getD p 0 =
      if p < 2 ^ (κ + R) then encKAt κ (fun u ↦ msg.getD (bitsToNat u) 0) p else 0 := by
  split
  · exact ntt_getD hκ msg (by assumption)
  · rename_i hp
    rw [ntt, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none]
    · rfl
    · rw [size_ntt_go _ _ _ _ _ Array.size_ofFn]
      omega

/-! ## The stack's word -/

theorem vector_getD {n : ℕ} (v : Vector K n) (i : ℕ) : v.getD i 0 = v.toArray.getD i 0 := rfl

/-- **The executable stack word is the specification's**, at every position. -/
theorem stackWordFast_eq {μ : ℕ} (hμ : μ ≤ 64) (R : ℕ) (q : Column μ) :
    stackWordFast μ R q.values.toArray = stackWord μ R q := by
  funext p
  simp only [stackWordFast, stackWordFast.stackWordOf, stackWord, laneBits]
  refine congrArg List.reverse ?_
  rw [show (2 : ℕ) ^ 6 = 64 from rfl]
  refine List.map_congr_left fun u hu ↦ ?_
  have hu' : u < 64 := by simpa using hu
  rw [stackCodes, getD_ofFn _ _ _ hu']
  simp only
  rw [ntt_getD' (by omega)]
  congr 2
  funext x
  rw [getD_ofFn _ _ _ (bitsToNat_lt x), blockK, vector_getD]

/-! ## The level words -/

theorem limb_ofK_mul (a : K) (x : E) (l : Fin 2) : (ofK a * x).limb l = a * x.limb l := by
  rw [← ofLimbs_limb x, ofK_eq_ofLimbs, mul_limbs]
  fin_cases l <;> simp [ofLimbs_limb]

theorem limb_sum {ι : Type} (s : Finset ι) (f : ι → E) (l : Fin 2) :
    (∑ i ∈ s, f i).limb l = ∑ i ∈ s, (f i).limb l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [limb_zero]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, limb_add, ih]

theorem limb_encAt (κ : ℕ) (g : (Fin κ → Bool) → E) (p : ℕ) (l : Fin 2) :
    (encAt κ g p).limb l = encKAt κ (fun u ↦ (g u).limb l) p := by
  rw [encAt, encKAt, limb_sum]
  refine sum_congr rfl fun u _ ↦ ?_
  rw [mul_comm, limb_ofK_mul, mul_comm]

theorem array_getD_toList {α : Type} (a : Array α) (i : ℕ) (d : α) :
    a.toList.getD i d = a.getD i d := by
  simp [List.getD_eq_getElem?_getD]

theorem levelCodes_getD {κ k R : ℕ} (hκ : κ ≤ 64) (g : Array E) {j : ℕ} (hj : j < 2 ^ k)
    (l : Fin 2) (p : ℕ) :
    ((levelCodes κ k R g).getD (2 * j + l) #[]).getD p 0 =
      (if p < 2 ^ (κ + R) then encAt κ (laneMsg κ k g.toList j) p else 0).limb l := by
  rw [levelCodes, getD_ofFn _ _ _ (by omega)]
  simp only
  rw [ntt_getD' hκ, apply_ite (E.limb · l), limb_encAt, limb_zero]
  congr 2
  funext u
  rw [getD_ofFn _ _ _ (bitsToNat_lt u), laneMsg, array_getD_toList,
    show (2 * j + (l : ℕ)) / 2 = j by omega]
  exact congrArg _ (Fin.ext (show (2 * j + (l : ℕ)) % 2 = l by omega))

/-- **The executable level word is the specification's**, at every position. -/
theorem levelWordFast_eq {κ : ℕ} (hκ : κ ≤ 64) (k R : ℕ) (g : Array E) :
    levelWordFast κ k R g = levelWord κ k R g.toList := by
  funext p
  rw [levelWordFast, levelWordFast.levelWordOf, levelWord, List.flatMap_map]
  refine List.flatMap_congr fun j hj ↦ ?_
  have hj' : j < 2 ^ k := List.mem_range.mp hj
  rw [limbsOf, ← levelCodes_getD hκ g hj' 0 p, ← levelCodes_getD hκ g hj' 1 p]
  rfl

end
end LeanVM.Prover.Enc
