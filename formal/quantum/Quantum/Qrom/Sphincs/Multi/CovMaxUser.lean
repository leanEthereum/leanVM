module

public import Quantum.Qrom.Sphincs.Multi.CovMaxCount
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

/-!
# One user's coverage price above a threshold

For one user's stream `d : Fin n → View` of uniform signed views, write the stream as an index
stream `x` and a leaf stream `y`. The price is `Σ_idx X_idx / 2^26`, `X_idx = Π_κ |S idx κ| / 2^240`
the covered fraction at `idx` (`price_eq_sum`), at most `(m / 2^10)^24` for the load `m` of `idx`
(`covFrac_le_loadCap`). Cut each `X_idx` at `θ = loadCap k0`:

* below the cap, `price - t ≤ e^{λ(A - t)} / (e λ)` with `A = Σ min(X_idx, θ) / 2^26`,
  `λ = s 2^26`, and `e^{s min(X, θ)} ≤ 1 + slope · min(X, θ)` by convexity (`exp_mul_le`);
* above it, only instances with load beyond `k0` contribute.

Given the index stream the fibers of the leaf stream are independent (`uavg_prod_fiber`) and the
mean covered fraction of an instance with load `m` is `coverProb m` (`uavg_covFrac`); averaging the
index stream gives `loadSum` for the cut part and a binomial mean for the rest
(`uavg_price_sub_le`).
-/

open Finset
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Quantum.Sphincs (View Disclosures coverMass price revealed ForsLeaves coverProb binomMean
  card_cover_leaves sum_count_eq card_forsLeaf card_forsTree card_forsLeaves card_index)
open Quantum.Xmss.Hybrid (uavg uavg_add uavg_const_mul uavg_mono)

namespace Quantum.Qrom.Sphincs.Multi

-- Keep elaboration from unfolding `univ` of the large `Fin` types.
attribute [local irreducible] Fin.fintype

/-! ## Exponential slopes -/

/-- The slope of `v ↦ e^{s v}` from `0`. -/
noncomputable def expSlope (s v : ℝ) : ℝ := (Real.exp (s * v) - 1) / v

theorem expSlope_nonneg {s v : ℝ} (hs : 0 ≤ s) (hv : 0 ≤ v) : 0 ≤ expSlope s v :=
  div_nonneg (by linarith [Real.one_le_exp (mul_nonneg hs hv)]) hv

/-- **Convexity**: on `[0, v]`, `e^{s z} ≤ 1 + slope · z`. -/
theorem exp_mul_le {s z v : ℝ} (hz : 0 ≤ z) (hzv : z ≤ v) :
    Real.exp (s * z) ≤ 1 + expSlope s v * z := by
  by_cases hv : v = 0
  · have hz0 : z = 0 := le_antisymm (hzv.trans hv.le) hz
    simp [hz0]
  have hvpos : 0 < v := lt_of_le_of_ne (hz.trans hzv) (Ne.symm hv)
  have ha0 : 0 ≤ z / v := div_nonneg hz hvpos.le
  have ha1 : z / v ≤ 1 := (div_le_one hvpos).2 hzv
  have h := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ (s * v)) (sub_nonneg.2 ha1) ha0
    (by ring : 1 - z / v + z / v = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  have e1 : z / v * (s * v) = s * z := by field_simp
  rw [e1] at h
  calc Real.exp (s * z) ≤ 1 - z / v + z / v * Real.exp (s * v) := h
    _ = 1 + expSlope s v * z := by unfold expSlope; field_simp; ring

theorem expSlope_mono {s v v' : ℝ} (hs : 0 ≤ s) (hv : 0 ≤ v) (hvv : v ≤ v') :
    expSlope s v ≤ expSlope s v' := by
  rcases hv.eq_or_lt with h0 | hpos
  · rw [← h0]
    simpa [expSlope] using expSlope_nonneg hs (hv.trans hvv)
  · have h := exp_mul_le (s := s) hpos.le hvv
    unfold expSlope at h ⊢
    rw [div_le_iff₀ hpos]
    linarith

/-! ## Loads, caps and weights -/

/-- `(m / 2^10)^24`: the covered fraction of an instance with load `m` is at most this. -/
noncomputable def loadCap (m : ℕ) : ℝ := (m : ℝ) ^ 24 / 2 ^ 240

theorem loadCap_nonneg (m : ℕ) : 0 ≤ loadCap m := by unfold loadCap; positivity

theorem loadCap_mono : Monotone loadCap := fun a b h ↦ by
  unfold loadCap
  gcongr

theorem coverProb_cast (m : ℕ) : (coverProb m : ℝ) = (1 - (1 - 1 / 2 ^ 10) ^ m) ^ 24 := by
  simp [Quantum.Sphincs.coverProb]

theorem coverProb_mono : Monotone fun m ↦ (coverProb m : ℝ) := fun a b h ↦ by
  simp only [coverProb_cast]
  have hq0 : (0 : ℝ) ≤ 1 - 1 / 2 ^ 10 := by norm_num
  have hq1 : (1 : ℝ) - 1 / 2 ^ 10 ≤ 1 := by norm_num
  have h1 : ((1 : ℝ) - 1 / 2 ^ 10) ^ b ≤ (1 - 1 / 2 ^ 10) ^ a := pow_le_pow_of_le_one hq0 hq1 h
  have h2 : ((1 : ℝ) - 1 / 2 ^ 10) ^ a ≤ 1 := pow_le_one₀ hq0 hq1
  exact pow_le_pow_left₀ (by linarith) (by linarith) 24

theorem coverProb_le_loadCap (m : ℕ) : (coverProb m : ℝ) ≤ loadCap m := by
  have hb : 1 + (m : ℝ) * (-(1 / 2 ^ 10)) ≤ (1 + -(1 / 2 ^ 10)) ^ m :=
    one_add_mul_le_pow (by norm_num) m
  have h1 : ((1 : ℝ) - 1 / 2 ^ 10) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rw [coverProb_cast, loadCap, show (2 : ℝ) ^ 240 = (2 ^ 10) ^ 24 by norm_num, ← div_pow]
  refine pow_le_pow_left₀ (by linarith) ?_ 24
  rw [le_div_iff₀ (by norm_num)]
  linarith

/-- The cap of an instance with load `m` under the cut at `k0`. -/
noncomputable def capAt (k0 m : ℕ) : ℝ := min (loadCap m) (loadCap k0)

/-- The load weight: the cover probability up to the cut, the cap beyond it. -/
noncomputable def loadWeight (k0 m : ℕ) : ℝ := if m ≤ k0 then (coverProb m : ℝ) else loadCap k0

/-- The per-instance factor `1 + slope(cap) · weight` of the exponential moment. -/
noncomputable def loadFactor (s : ℝ) (k0 m : ℕ) : ℝ :=
  1 + expSlope s (capAt k0 m) * loadWeight k0 m

theorem capAt_nonneg (k0 m : ℕ) : 0 ≤ capAt k0 m := le_min (loadCap_nonneg m) (loadCap_nonneg k0)

theorem loadWeight_nonneg (k0 m : ℕ) : 0 ≤ loadWeight k0 m := by
  unfold loadWeight
  split_ifs
  · exact_mod_cast Quantum.Sphincs.coverProb_nonneg m
  · exact loadCap_nonneg k0

theorem loadWeight_mono (k0 : ℕ) : Monotone (loadWeight k0) := fun a b hab ↦ by
  unfold loadWeight
  split_ifs with ha hb hb
  · exact coverProb_mono hab
  · exact (coverProb_le_loadCap a).trans (loadCap_mono ha)
  · omega
  · exact le_rfl

theorem loadFactor_mono {s : ℝ} (hs : 0 ≤ s) (k0 : ℕ) : Monotone (loadFactor s k0) :=
  fun a b hab ↦ add_le_add le_rfl (mul_le_mul
    (expSlope_mono hs (capAt_nonneg k0 a) (min_le_min (loadCap_mono hab) le_rfl))
    (loadWeight_mono k0 hab) (loadWeight_nonneg k0 a)
    (expSlope_nonneg hs (capAt_nonneg k0 b)))

theorem loadFactor_nonneg {s : ℝ} (hs : 0 ≤ s) (k0 m : ℕ) : 0 ≤ loadFactor s k0 m :=
  add_nonneg zero_le_one
    (mul_nonneg (expSlope_nonneg hs (capAt_nonneg k0 m)) (loadWeight_nonneg k0 m))

/-! ## The price as a sum over instances -/

/-- The covered views at instance `idx`, `Π_κ |S idx κ|`. -/
def idxMass (S : Disclosures) (idx : Index) : ℕ := ∏ κ, #(S idx κ)

/-- The covered fraction at `idx`, `Π_κ |S idx κ| / 2^240`. -/
noncomputable def covFrac (S : Disclosures) (idx : Index) : ℝ := idxMass S idx / 2 ^ 240

theorem covFrac_nonneg (S : Disclosures) (idx : Index) : 0 ≤ covFrac S idx := by
  unfold covFrac; positivity

theorem price_eq_sum (S : Disclosures) : (price S : ℝ) = ∑ idx, covFrac S idx / 2 ^ 26 := by
  rw [Quantum.Sphincs.price]
  push_cast
  simp only [coverMass, covFrac, idxMass, Nat.cast_sum, Nat.cast_prod]
  rw [show (2 : ℝ) ^ 266 = 2 ^ 240 * 2 ^ 26 by rw [← pow_add], Finset.sum_div]
  exact Finset.sum_congr rfl fun _ _ ↦ (div_div _ _ _).symm

/-- The load of instance `idx` in the index stream `x`. -/
def load {n : ℕ} (x : Fin n → Index) (idx : Index) : ℕ := #(univ.filter fun j ↦ x j = idx)

theorem load_le {n : ℕ} (x : Fin n → Index) (idx : Index) : load x idx ≤ n :=
  (card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])

theorem revealed_join {n : ℕ} (x : Fin n → Index) (y : Fin n → ForsLeaves) (idx : Index)
    (κ : ForsTreeIndex) :
    revealed (fun j ↦ (x j, y j)) idx κ = univ.image fun j : {j // x j = idx} ↦ y j.1 κ := by
  ext a
  simp [revealed, mem_image]

theorem covFrac_le_loadCap {n : ℕ} (x : Fin n → Index) (y : Fin n → ForsLeaves) (idx : Index) :
    covFrac (revealed fun j ↦ (x j, y j)) idx ≤ loadCap (load x idx) := by
  have h : idxMass (revealed fun j ↦ (x j, y j)) idx ≤ load x idx ^ 24 := by
    unfold idxMass
    calc ∏ κ, #(revealed (fun j ↦ (x j, y j)) idx κ) ≤ ∏ _κ : ForsTreeIndex, load x idx :=
          Finset.prod_le_prod fun κ _ ↦ card_image_le
      _ = load x idx ^ 24 := by rw [Finset.prod_const, Finset.card_univ, card_forsTree]
  unfold covFrac loadCap
  gcongr
  exact_mod_cast h

/-- The fiber's covered views: the instance's mass as a function of its own leaves. -/
def fiberMass {n : ℕ} {x : Fin n → Index} {idx : Index} (z : {j // x j = idx} → ForsLeaves) : ℕ :=
  ∏ κ, #(univ.image fun j ↦ z j κ)

theorem idxMass_join {n : ℕ} (x : Fin n → Index) (y : Fin n → ForsLeaves) (idx : Index) :
    idxMass (revealed fun j ↦ (x j, y j)) idx = fiberMass (x := x) (idx := idx) fun j ↦ y j.1 := by
  unfold idxMass fiberMass
  simp only [revealed_join]

/-! ## The mean covered fraction of an instance -/

theorem uavg_ofReal {Θ : Type*} [Fintype Θ] [Nonempty Θ] (f : Θ → ℝ) (hf : ∀ θ, 0 ≤ f θ) :
    uavg (fun θ ↦ ENNReal.ofReal (f θ)) = ENNReal.ofReal ((∑ θ, f θ) / Fintype.card Θ) := by
  unfold uavg
  rw [← ENNReal.ofReal_sum_of_nonneg fun θ _ ↦ hf θ,
    ENNReal.ofReal_div_of_pos (Nat.cast_pos.2 Fintype.card_pos), ENNReal.ofReal_natCast,
    div_eq_mul_inv, mul_comm]

/-- The covering leaf streams, counted by `card_cover_leaves`. -/
theorem sum_idxMass_join {n : ℕ} (x : Fin n → Index) (idx : Index) :
    (∑ y : Fin n → ForsLeaves, (idxMass (revealed fun j ↦ (x j, y j)) idx : ℚ)) =
      Fintype.card ForsLeaves * (((Fintype.card ForsLeafIndex : ℚ) ^ n -
        ((Fintype.card ForsLeafIndex - 1 : ℕ) : ℚ) ^ load x idx *
          (Fintype.card ForsLeafIndex : ℚ) ^ (n - load x idx)) ^ Fintype.card ForsTreeIndex) := by
  have h1 : ∀ y : Fin n → ForsLeaves, idxMass (revealed fun j ↦ (x j, y j)) idx =
      #(univ.filter fun ℓ : ForsLeaves ↦ ∀ κ, ∃ j, x j = idx ∧ y j κ = ℓ κ) := fun y ↦ by
    unfold idxMass
    rw [← Fintype.card_piFinset]
    refine congrArg card (Finset.ext fun ℓ ↦ ?_)
    simp [Fintype.mem_piFinset, revealed, mem_image]
  calc (∑ y : Fin n → ForsLeaves, (idxMass (revealed fun j ↦ (x j, y j)) idx : ℚ))
      = ∑ ℓ : ForsLeaves,
          (#(univ.filter fun y : Fin n → ForsLeaves ↦ ∀ κ, ∃ j, x j = idx ∧ y j κ = ℓ κ) : ℚ) := by
        simp only [h1, natCast_card_filter]
        exact Finset.sum_comm
    _ = ∑ _ℓ : ForsLeaves, (((Fintype.card ForsLeafIndex : ℚ) ^ n -
          ((Fintype.card ForsLeafIndex - 1 : ℕ) : ℚ) ^ load x idx *
            (Fintype.card ForsLeafIndex : ℚ) ^ (n - load x idx)) ^ Fintype.card ForsTreeIndex) :=
        Finset.sum_congr rfl fun ℓ _ ↦ by convert card_cover_leaves n x idx ℓ <;> rfl
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- `F^K (F^n - (F-1)^m F^(n-m))^K / F^K / (F^K)^n = (1 - (1 - 1/F)^m)^K`. -/
private theorem cover_frac_identity (F K : ℕ) (hF : 0 < F) {m n : ℕ} (h : m ≤ n) :
    (F : ℝ) ^ K * ((F : ℝ) ^ n - ((F - 1 : ℕ) : ℝ) ^ m * (F : ℝ) ^ (n - m)) ^ K / (F : ℝ) ^ K /
      ((F : ℝ) ^ K) ^ n = (1 - (1 - 1 / (F : ℝ)) ^ m) ^ K := by
  have hF0 : (F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hF.ne'
  rw [mul_div_cancel_left₀ _ (pow_ne_zero K hF0), ← pow_mul, mul_comm K n, pow_mul, ← div_pow,
    Nat.cast_sub hF, Nat.cast_one]
  congr 1
  rw [← pow_mul_pow_sub (F : ℝ) h, one_sub_div hF0, div_pow]
  have h1 : (F : ℝ) ^ m ≠ 0 := pow_ne_zero m hF0
  have h2 : (F : ℝ) ^ (n - m) ≠ 0 := pow_ne_zero (n - m) hF0
  field_simp

/-- **The mean covered fraction** of an instance with load `m` is `coverProb m`. -/
theorem uavg_covFrac {n : ℕ} (x : Fin n → Index) (idx : Index) :
    uavg (fun y : Fin n → ForsLeaves ↦ ENNReal.ofReal (covFrac (revealed fun j ↦ (x j, y j)) idx))
      = ENNReal.ofReal (coverProb (load x idx)) := by
  rw [uavg_ofReal _ fun y ↦ covFrac_nonneg _ _]
  congr 1
  have h240 : (2 : ℝ) ^ 240 = (Fintype.card ForsLeaves : ℝ) := by
    rw [card_forsLeaves]; push_cast; ring
  have hsum : ∑ y : Fin n → ForsLeaves, covFrac (revealed fun j ↦ (x j, y j)) idx =
      ((∑ y : Fin n → ForsLeaves, (idxMass (revealed fun j ↦ (x j, y j)) idx : ℚ) : ℚ) : ℝ) /
        (Fintype.card ForsLeaves : ℝ) := by
    simp only [covFrac, h240, ← Finset.sum_div]
    push_cast
    rfl
  have hc : (coverProb (load x idx) : ℝ) = (1 - (1 - 1 / (Fintype.card ForsLeafIndex : ℝ)) ^
      load x idx) ^ Fintype.card ForsTreeIndex := by
    rw [coverProb_cast, card_forsLeaf, card_forsTree]
    push_cast
    norm_num
  have hcF : Fintype.card (Fin n → ForsLeaves) = Fintype.card ForsLeaves ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin]
  have hcL : Fintype.card ForsLeaves = Fintype.card ForsLeafIndex ^ Fintype.card ForsTreeIndex :=
    Fintype.card_fun
  rw [hsum, sum_idxMass_join, hcF, hcL, hc]
  push_cast
  exact cover_frac_identity _ _ Fintype.card_pos (load_le x idx)

/-! ## The bound for one stream -/

/-- `e^{-λ t} / (e λ)`, `λ = s 2^26`. -/
noncomputable def expCoef (s t : ℝ) : ℝ :=
  Real.exp (-(s * 2 ^ 26 * t)) / (Real.exp 1 * (s * 2 ^ 26))

theorem expCoef_nonneg {s : ℝ} (hs : 0 ≤ s) (t : ℝ) : 0 ≤ expCoef s t := by
  unfold expCoef; positivity

/-- **The pointwise bound**: with the cut at `k0`,
`price - t ≤ expCoef · Π_idx (1 + slope · min(X_idx, θ)) + Σ_{load > k0} X_idx / 2^26`. -/
theorem price_sub_le (S : Disclosures) (m : Index → ℕ) (hm : ∀ idx, covFrac S idx ≤ loadCap (m idx))
    (k0 : ℕ) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    ENNReal.ofReal (price S - t) ≤
      ENNReal.ofReal (expCoef s t) * ∏ idx, ENNReal.ofReal (1 + expSlope s (capAt k0 (m idx)) *
        min (covFrac S idx) (loadCap k0)) +
      ∑ idx, ENNReal.ofReal (if k0 < m idx then covFrac S idx / 2 ^ 26 else 0) := by
  set θ := loadCap k0
  set Z : Index → ℝ := fun idx ↦ min (covFrac S idx) θ
  have hZ0 : ∀ idx, 0 ≤ Z idx := fun idx ↦ le_min (covFrac_nonneg S idx) (loadCap_nonneg k0)
  have hP0 : ∀ idx, 0 ≤ 1 + expSlope s (capAt k0 (m idx)) * Z idx := fun idx ↦
    add_nonneg zero_le_one (mul_nonneg (expSlope_nonneg hs.le (capAt_nonneg k0 _)) (hZ0 idx))
  have hQ0 : ∀ idx, 0 ≤ if k0 < m idx then covFrac S idx / 2 ^ 26 else 0 := fun idx ↦ by
    split_ifs
    · exact div_nonneg (covFrac_nonneg S idx) (by positivity)
    · exact le_rfl
  -- the excess above the cap
  have hB : ∀ idx, (covFrac S idx - Z idx) / 2 ^ 26 ≤
      if k0 < m idx then covFrac S idx / 2 ^ 26 else 0 := fun idx ↦ by
    split_ifs with h
    · exact div_le_div_of_nonneg_right (by linarith [hZ0 idx]) (by positivity)
    · have hle : covFrac S idx ≤ θ := (hm idx).trans (loadCap_mono (not_lt.1 h))
      simp [Z, min_eq_left hle]
  -- the capped part through the exponential moment
  have hlam : 0 < s * 2 ^ 26 := by positivity
  have hA : (∑ idx, Z idx / 2 ^ 26) - t ≤
      expCoef s t * ∏ idx, (1 + expSlope s (capAt k0 (m idx)) * Z idx) := by
    set u := (∑ idx, Z idx / 2 ^ 26) - t
    have h1 : s * 2 ^ 26 * u * Real.exp 1 ≤ Real.exp (s * 2 ^ 26 * u) := by
      have h := Real.add_one_le_exp (s * 2 ^ 26 * u - 1)
      rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos 1)] at h
      linarith
    have h2 : Real.exp (s * 2 ^ 26 * u) =
        Real.exp (-(s * 2 ^ 26 * t)) * ∏ idx, Real.exp (s * Z idx) := by
      rw [← Real.exp_sum, ← Real.exp_add]
      congr 1
      simp only [u, mul_sub, Finset.mul_sum]
      rw [Finset.sum_congr rfl fun idx _ ↦ by rw [show s * 2 ^ 26 * (Z idx / 2 ^ 26) = s * Z idx
        by field_simp]]
      ring
    have h3 : ∏ idx, Real.exp (s * Z idx) ≤ ∏ idx, (1 + expSlope s (capAt k0 (m idx)) * Z idx) :=
      Finset.prod_le_prod₀ (fun _ _ ↦ (Real.exp_pos _).le) fun idx _ ↦
        exp_mul_le (hZ0 idx) (min_le_min (hm idx) le_rfl)
    have h4 : u ≤ Real.exp (s * 2 ^ 26 * u) / (Real.exp 1 * (s * 2 ^ 26)) := by
      rw [le_div_iff₀ (by positivity)]
      calc u * (Real.exp 1 * (s * 2 ^ 26)) = s * 2 ^ 26 * u * Real.exp 1 := by ring
        _ ≤ _ := h1
    calc u ≤ Real.exp (s * 2 ^ 26 * u) / (Real.exp 1 * (s * 2 ^ 26)) := h4
      _ = expCoef s t * ∏ idx, Real.exp (s * Z idx) := by
          rw [h2, expCoef]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (expCoef_nonneg hs.le t)
  have hreal : (price S : ℝ) - t ≤
      expCoef s t * ∏ idx, (1 + expSlope s (capAt k0 (m idx)) * Z idx) +
        ∑ idx, (if k0 < m idx then covFrac S idx / 2 ^ 26 else 0) := by
    have hsplit : (price S : ℝ) =
        ∑ idx, Z idx / 2 ^ 26 + ∑ idx, (covFrac S idx - Z idx) / 2 ^ 26 := by
      rw [price_eq_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun _ _ ↦ ?_
      ring
    rw [hsplit]
    linarith [Finset.sum_le_sum fun idx (_ : idx ∈ univ) ↦ hB idx]
  calc ENNReal.ofReal ((price S : ℝ) - t)
      ≤ ENNReal.ofReal (expCoef s t * ∏ idx, (1 + expSlope s (capAt k0 (m idx)) * Z idx) +
          ∑ idx, (if k0 < m idx then covFrac S idx / 2 ^ 26 else 0)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
        rw [ENNReal.ofReal_add (mul_nonneg (expCoef_nonneg hs.le t) (prod_nonneg fun i _ ↦ hP0 i))
          (sum_nonneg fun i _ ↦ hQ0 i), ENNReal.ofReal_mul (expCoef_nonneg hs.le t),
          ENNReal.ofReal_prod_of_nonneg fun i _ ↦ hP0 i,
          ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hQ0 i]

/-! ## Averaging the leaves, then the indices -/

/-- **The leaves**: given the index stream, the capped product averages to the product of the load
factors. -/
theorem uavg_prod_capped_le {n : ℕ} (x : Fin n → Index) (k0 : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    uavg (fun y : Fin n → ForsLeaves ↦
        ∏ idx, ENNReal.ofReal (1 + expSlope s (capAt k0 (load x idx)) *
          min (covFrac (revealed fun j ↦ (x j, y j)) idx) (loadCap k0))) ≤
      ∏ idx, ENNReal.ofReal (loadFactor s k0 (load x idx)) := by
  have hcov : ∀ (y : Fin n → ForsLeaves) idx, covFrac (revealed fun j ↦ (x j, y j)) idx =
      (fiberMass (x := x) (idx := idx) (fun j ↦ y j.1) : ℝ) / 2 ^ 240 := fun y idx ↦ by
    rw [covFrac, idxMass_join]
  simp only [hcov]
  refine (uavg_prod_fiber x fun idx (z : {j // x j = idx} → ForsLeaves) ↦
    ENNReal.ofReal (1 + expSlope s (capAt k0 (load x idx)) *
      min ((fiberMass z : ℝ) / 2 ^ 240) (loadCap k0))).trans_le ?_
  refine Finset.prod_le_prod fun idx _ ↦ ?_
  simp only [← hcov]
  set a := expSlope s (capAt k0 (load x idx))
  have ha : 0 ≤ a := expSlope_nonneg hs (capAt_nonneg k0 _)
  have hpt : ∀ y : Fin n → ForsLeaves,
      ENNReal.ofReal (1 + a * min (covFrac (revealed fun j ↦ (x j, y j)) idx) (loadCap k0)) =
      1 + ENNReal.ofReal a * ENNReal.ofReal (min (covFrac (revealed fun j ↦ (x j, y j)) idx)
        (loadCap k0)) := fun y ↦ by
    rw [ENNReal.ofReal_add zero_le_one (mul_nonneg ha (le_min (covFrac_nonneg _ _)
      (loadCap_nonneg k0))), ENNReal.ofReal_one, ENNReal.ofReal_mul ha]
  simp only [hpt]
  rw [uavg_add, uavg_const_mul]
  have hmin : uavg (fun y : Fin n → ForsLeaves ↦ ENNReal.ofReal
      (min (covFrac (revealed fun j ↦ (x j, y j)) idx) (loadCap k0))) ≤
      ENNReal.ofReal (loadWeight k0 (load x idx)) := by
    unfold loadWeight
    split_ifs with h
    · rw [← uavg_covFrac x idx]
      exact uavg_mono fun y ↦ ENNReal.ofReal_le_ofReal (min_le_left _ _)
    · exact (uavg_mono fun y ↦ ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans
        (uavg_const_le _)
  calc uavg (fun _ : Fin n → ForsLeaves ↦ (1 : ℝ≥0∞)) + ENNReal.ofReal a *
        uavg (fun y : Fin n → ForsLeaves ↦ ENNReal.ofReal
          (min (covFrac (revealed fun j ↦ (x j, y j)) idx) (loadCap k0)))
      ≤ 1 + ENNReal.ofReal a * ENNReal.ofReal (loadWeight k0 (load x idx)) := by
        gcongr
        exact uavg_const_le 1
    _ = ENNReal.ofReal (loadFactor s k0 (load x idx)) := by
        rw [loadFactor, ENNReal.ofReal_add zero_le_one (mul_nonneg ha (loadWeight_nonneg k0 _)),
          ENNReal.ofReal_one, ENNReal.ofReal_mul ha]

/-- `Σ_m C(n,m) (K-1)^(n-m) h(m) / K^n` is the binomial mean at `1/K`. -/
theorem sum_choose_div_eq_binomMean (n K : ℕ) (hK : 0 < K) (h : ℕ → ℚ) :
    (∑ m ∈ range (n + 1), (n.choose m : ℚ) * ((K - 1 : ℕ) : ℚ) ^ (n - m) * h m) / (K : ℚ) ^ n =
      binomMean n (1 / K) h := by
  rw [Quantum.Sphincs.binomMean, Finset.sum_div]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hm)
  have hK0 : (K : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hK.ne'
  rw [Nat.cast_sub hK, Nat.cast_one, ← pow_mul_pow_sub (K : ℚ) hmn, one_sub_div hK0, div_pow,
    div_pow, one_pow]
  field_simp

/-- **The indices**: the binomial part. -/
theorem uavg_excess_eq {n : ℕ} (k0 : ℕ) (idx : Index) :
    uavg (fun x : Fin n → Index ↦
        ENNReal.ofReal (if k0 < load x idx then (coverProb (load x idx) : ℝ) / 2 ^ 26 else 0)) =
      ENNReal.ofReal ((binomMean n (1 / 2 ^ 26) fun m ↦ if k0 < m then coverProb m else 0 : ℚ) /
        2 ^ 26) := by
  set h : ℕ → ℚ := fun m ↦ if k0 < m then coverProb m else 0 with hh
  have h0 : ∀ m, 0 ≤ h m := fun m ↦ by
    simp only [hh]
    split_ifs
    · exact Quantum.Sphincs.coverProb_nonneg m
    · exact le_rfl
  have hpt : ∀ x : Fin n → Index,
      (if k0 < load x idx then (coverProb (load x idx) : ℝ) / 2 ^ 26 else 0) =
        (h (load x idx) : ℝ) / 2 ^ 26 := fun x ↦ by
    simp only [hh]
    split_ifs <;> simp
  simp only [hpt]
  rw [uavg_ofReal _ fun x ↦ div_nonneg (Rat.cast_nonneg.2 (h0 _)) (by positivity)]
  congr 1
  have hsum : (∑ x : Fin n → Index, h (load x idx)) / (2 ^ 26 : ℚ) ^ n =
      binomMean n (1 / 2 ^ 26) h := by
    have hc := sum_count_eq n idx h
    rw [card_index] at hc
    have hb := sum_choose_div_eq_binomMean n (2 ^ 26) (by positivity) h
    rw [Nat.cast_pow, Nat.cast_ofNat] at hb
    rw [← hb, ← hc]
    rfl
  rw [Fintype.card_fun, card_index, Fintype.card_fin n, ← hsum]
  push_cast
  rw [← Finset.sum_div]
  ring

/-- **One user's price above `t`**: the cut part through the loads, the rest a binomial mean. -/
theorem uavg_price_sub_le (n k0 : ℕ) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    uavg (fun d : Fin n → View ↦ ENNReal.ofReal (price (revealed d) - t)) ≤
      ENNReal.ofReal (expCoef s t) *
        (loadSum (fun m ↦ ENNReal.ofReal (loadFactor s k0 m)) (Fin n) (2 ^ indexBits) /
          ((2 ^ indexBits : ℕ) : ℝ≥0∞) ^ n) +
      ENNReal.ofReal (binomMean n (1 / 2 ^ 26) fun m ↦ if k0 < m then coverProb m else 0) := by
  set e := (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ ↦ Index) fun _ ↦ ForsLeaves).symm
  rw [← Quantum.Sphincs.uavg_comp_equiv e, uavg_prod_eq]
  have hpt : ∀ x : Fin n → Index, uavg (fun y : Fin n → ForsLeaves ↦
      ENNReal.ofReal (price (revealed (e (x, y))) - t)) ≤
      ENNReal.ofReal (expCoef s t) * ∏ idx, ENNReal.ofReal (loadFactor s k0 (load x idx)) +
        ∑ idx, ENNReal.ofReal (if k0 < load x idx then (coverProb (load x idx) : ℝ) / 2 ^ 26
          else 0) := fun x ↦ by
    calc uavg (fun y : Fin n → ForsLeaves ↦ ENNReal.ofReal (price (revealed (e (x, y))) - t))
        ≤ uavg (fun y : Fin n → ForsLeaves ↦ ENNReal.ofReal (expCoef s t) *
            ∏ idx, ENNReal.ofReal (1 + expSlope s (capAt k0 (load x idx)) *
              min (covFrac (revealed fun j ↦ (x j, y j)) idx) (loadCap k0)) +
            ∑ idx, ENNReal.ofReal (if k0 < load x idx then
              covFrac (revealed fun j ↦ (x j, y j)) idx / 2 ^ 26 else 0)) :=
          uavg_mono fun y ↦ price_sub_le _ (load x) (covFrac_le_loadCap x y) k0 hs t
      _ = ENNReal.ofReal (expCoef s t) * uavg (fun y : Fin n → ForsLeaves ↦
            ∏ idx, ENNReal.ofReal (1 + expSlope s (capAt k0 (load x idx)) *
              min (covFrac (revealed fun j ↦ (x j, y j)) idx) (loadCap k0))) +
            ∑ idx, uavg (fun y : Fin n → ForsLeaves ↦ ENNReal.ofReal (if k0 < load x idx then
              covFrac (revealed fun j ↦ (x j, y j)) idx / 2 ^ 26 else 0)) := by
          rw [uavg_add, uavg_const_mul, uavg_sum]
      _ ≤ _ := by
          gcongr with idx
          · exact uavg_prod_capped_le x k0 hs.le
          · split_ifs
            · rw [show (fun y : Fin n → ForsLeaves ↦ ENNReal.ofReal
                  (covFrac (revealed fun j ↦ (x j, y j)) idx / 2 ^ 26)) =
                  fun y ↦ ENNReal.ofReal (1 / 2 ^ 26) *
                    ENNReal.ofReal (covFrac (revealed fun j ↦ (x j, y j)) idx) from
                  funext fun y ↦ by rw [← ENNReal.ofReal_mul (by positivity), one_div_mul_eq_div],
                uavg_const_mul, uavg_covFrac, ← ENNReal.ofReal_mul (by positivity),
                one_div_mul_eq_div]
            · exact uavg_const_le _
  refine (uavg_mono hpt).trans ?_
  rw [uavg_add, uavg_const_mul, uavg_sum]
  gcongr
  · -- the product over the loads
    refine le_of_eq ?_
    unfold uavg loadSum
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow, ENNReal.div_eq_inv_mul]
    rfl
  · -- the binomial part
    simp only [uavg_excess_eq]
    rw [Finset.sum_const, Finset.card_univ, card_index, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    push_cast
    field_simp
    ring

end Quantum.Qrom.Sphincs.Multi

end
