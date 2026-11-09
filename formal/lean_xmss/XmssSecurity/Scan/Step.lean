module

public import XmssSecurity.Scan.Potential
public import XmssSecurity.Proof.AdaptiveFreshTarget

@[expose] public section

/-!
# One encoding query and the partner potential

A query at a fresh position `x` of the leaf index, its output `u` uniform. With `ex f` the mean of `f u`:

* `line_cacheQuery_self`, `line_cacheQuery_of_ne`: the query sets the status of `x` by the `outcome` of `u`.
* `nextRand_no_return`: the successor does not return within the attempt limit.
* `probOutput_valid`, `probOutput_truncate`: `u` lands w.p. `landing` and hits a digest w.p. `N⁻¹`.
* `ex_W`, `ex_sum_W`: the reach to any position is a martingale.
* `ex_Φ_le`: the partner step, `E[Φ'] ≤ Φ + (V · W x + H) · N⁻¹`.
* `ex_V_mul_H`: the compensator step, `E[V' · H'] ≥ V · H + landing · (H + V · W x)`.
* `landing_mul_H_le`: the mass bound, `landing · H ≤ landing · C + V · (1 − landing)`.
* `potentials_cacheQuery_of_not_input`: other inputs change nothing.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Partner

open LoopWalk

theorem nextRand_pow_apply (j : ℕ) (ρ : Randomness) : (nextRand ^ j) ρ = ρ + BitVec.ofNat _ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    simp only [nextRand, Equiv.coe_addRight]
    rw [BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add]

theorem nextRand_no_return (ρ : Randomness) (j : ℕ) (h0 : 0 < j) (hj : j < signingAttemptLimit) :
    (nextRand ^ j) ρ ≠ ρ := by
  rw [nextRand_pow_apply]
  intro h
  have h2 : BitVec.ofNat randomnessBits j = 0 := by
    have := congrArg (· - ρ) h
    simpa using this
  have := congrArg BitVec.toNat h2
  simp [randomnessBits] at this
  simp [signingAttemptLimit] at hj
  omega


/-! ### Expectations over a fresh output -/

/-- The mean of `f` over a uniform oracle output. -/
noncomputable def ex (f : HashOutput → ℝ≥0∞) : ℝ≥0∞ := ∑ u, Pr{let x ← $ᵗ HashOutput}[x = u] * f u

theorem ex_const (c : ℝ≥0∞) : ex (fun _ => c) = c := by
  simp only [ex, SampleableType.prEvent_uniformSample_eq_singleton, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

theorem ex_add (f g : HashOutput → ℝ≥0∞) : ex (fun u => f u + g u) = ex f + ex g := by
  simp only [ex, mul_add, Finset.sum_add_distrib]

theorem ex_mul_const (f : HashOutput → ℝ≥0∞) (c : ℝ≥0∞) : ex (fun u => f u * c) = ex f * c := by
  simp only [ex, Finset.sum_mul, mul_assoc]

theorem ex_const_mul (f : HashOutput → ℝ≥0∞) (c : ℝ≥0∞) : ex (fun u => c * f u) = c * ex f := by
  simp only [ex, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring

theorem ex_sum {ι : Type} (s : Finset ι) (f : ι → HashOutput → ℝ≥0∞) :
    ex (fun u => ∑ i ∈ s, f i u) = ∑ i ∈ s, ex (f i) := by
  simp only [ex, Finset.mul_sum]; exact Finset.sum_comm

theorem ex_ite (P : Prop) [Decidable P] (f : HashOutput → ℝ≥0∞) :
    ex (fun u => if P then f u else 0) = if P then ex f else 0 := by
  split_ifs
  · rfl
  · exact ex_const 0

theorem ex_mono {f g : HashOutput → ℝ≥0∞} (h : ∀ u, f u ≤ g u) : ex f ≤ ex g :=
  Finset.sum_le_sum fun u _ => mul_le_mul' le_rfl (h u)

/-- `N⁻¹`, the probability of one digest. -/
theorem ex_digest (d : Digest) :
    ex (fun u => if truncateHash u = d then 1 else 0) = ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [← Rom.uniform_truncate_probability d, OracleComp.prEvent_eq_tsum_ite, tsum_fintype, ex]
  exact Finset.sum_congr rfl fun u _ => by split_ifs <;> simp only [mul_one, mul_zero]

theorem ex_valid : ex (fun u => if TargetSum.ValidDigest (truncateHash u) then 1 else 0) = landing := by
  have h : ∀ u : HashOutput, (if TargetSum.ValidDigest (truncateHash u) then (1 : ℝ≥0∞) else 0) =
      ∑ d ∈ TargetSum.validDigests, if truncateHash u = d then 1 else 0 := fun u => by
    rw [Finset.sum_ite_eq]
    simp [TargetSum.validDigests]
  simp_rw [h]
  rw [ex_sum]
  simp_rw [ex_digest]
  rw [Finset.sum_const, nsmul_eq_mul, landing]

theorem probOutput_valid :
    Pr{let u ← $ᵗ HashOutput}[TargetSum.ValidDigest (truncateHash u)] = landing := by
  rw [← ex_valid, OracleComp.prEvent_eq_tsum_ite, tsum_fintype, ex]
  exact Finset.sum_congr rfl fun u _ => by split_ifs <;> simp only [mul_one, mul_zero]

theorem landing_le_one : landing ≤ 1 := by
  rw [← probOutput_valid]; exact (prEvent_le_one _)

theorem landing_ne_top : landing ≠ ⊤ := ne_top_of_le_ne_top one_ne_top landing_le_one

/-- The status a fresh output gives its position. -/
noncomputable def outcome (u : HashOutput) : St :=
  if TargetSum.ValidDigest (truncateHash u) then .hit else .miss

/-- A function of the outcome has mean `landing · F hit + (1 − landing) · F miss`. -/
theorem ex_outcome (F : St → ℝ≥0∞) :
    ex (fun u => F (outcome u)) = landing * F .hit + (1 - landing) * F .miss := by
  have hinv : ex (fun u => if TargetSum.ValidDigest (truncateHash u) then 0 else 1) = 1 - landing := by
    refine ENNReal.eq_sub_of_add_eq landing_ne_top ?_
    rw [← ex_valid, ← ex_add]
    convert ex_const (1 : ℝ≥0∞) using 2
    funext u
    split_ifs <;> simp
  have h : ∀ u, F (outcome u) = (if TargetSum.ValidDigest (truncateHash u) then 1 else 0) * F .hit +
      (if TargetSum.ValidDigest (truncateHash u) then 0 else 1) * F .miss := fun u => by
    unfold outcome; split_ifs <;> simp
  simp_rw [h]
  rw [ex_add, ex_mul_const, ex_mul_const, ex_valid, hinv]


/-! ### One query at a position -/

open Classical

variable (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex)

/-- The statuses on a message's line. -/
noncomputable def line (m : Message) (ρ : Randomness) : St := status cache parameter leafIndex (m, ρ)

/-- The digest cached at a position, `0` if none. -/
def dig (y : Position) : Digest := ((cache (input parameter leafIndex y)).map truncateHash).getD 0

theorem input_injective : Function.Injective (input parameter leafIndex) :=
  Concrete.CacheView.encodingInput_injective parameter leafIndex

variable {cache parameter leafIndex}

theorem W_eq (y : Position) :
    W cache parameter leafIndex y = ∑ r, reach nextRand landing (line cache parameter leafIndex y.1) y.2
      signingAttemptLimit r := rfl

theorem isHit_iff (y : Position) : IsHit cache parameter leafIndex y ↔ status cache parameter leafIndex y = .hit := by
  unfold IsHit status
  cases h : cache (input parameter leafIndex y) with
  | none => simp
  | some o => by_cases hv : TargetSum.ValidDigest (truncateHash o) <;> simp [hv]

theorem status_ne_fresh_iff (y : Position) :
    status cache parameter leafIndex y ≠ .fresh ↔ (cache (input parameter leafIndex y)).isSome := by
  unfold status
  cases cache (input parameter leafIndex y) with
  | none => simp
  | some o => simp only [Option.isSome_some, iff_true]; split_ifs <;> simp

theorem cacheQuery_input_of_ne (x y : Position) (u : HashOutput) (h : y ≠ x) :
    cache.cacheQuery (input parameter leafIndex x) u (input parameter leafIndex y) =
      cache (input parameter leafIndex y) :=
  QueryCache.cacheQuery_of_ne _ _ fun he => h (input_injective parameter leafIndex he)

theorem status_cacheQuery (x y : Position) (u : HashOutput) :
    status (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex y =
      if y = x then outcome u else status cache parameter leafIndex y := by
  split_ifs with h
  · subst h; simp [status, outcome]
  · unfold status; rw [cacheQuery_input_of_ne x y u h]

/-- **Line facts.** The query rewrites the status of `x` on its line by the outcome. -/
theorem line_cacheQuery_self (x : Position) (u : HashOutput) :
    line (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex x.1 =
      Function.update (line cache parameter leafIndex x.1) x.2 (outcome u) := by
  funext ρ
  rw [line, status_cacheQuery]
  by_cases h : ρ = x.2
  · subst h; simp
  · rw [ite_eq_right fun he => h (by rw [← he]), Function.update_of_ne h, line]

/-- **Line facts.** Other messages' lines are unchanged. -/
theorem line_cacheQuery_of_ne (x : Position) (u : HashOutput) {m : Message} (hm : m ≠ x.1) :
    line (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex m =
      line cache parameter leafIndex m := by
  funext ρ
  rw [line, status_cacheQuery, ite_eq_right fun he => hm (by rw [← he]), line]


/-! ### Other inputs -/

section Agree

variable {c₁ c₂ : QueryCache HashSpec}
  (h : ∀ y, c₁ (input parameter leafIndex y) = c₂ (input parameter leafIndex y))
include h

theorem status_congr : status c₁ parameter leafIndex = status c₂ parameter leafIndex := by
  funext y; simp only [status, h]

theorem W_congr : W c₁ parameter leafIndex = W c₂ parameter leafIndex := by
  funext y; simp only [W, status_congr h]

theorem Φ_congr : Φ c₁ parameter leafIndex = Φ c₂ parameter leafIndex := by
  refine Finset.sum_congr rfl fun y _ => if_congr ?_ (by rw [W_congr h]) rfl
  simp only [IsPartnered, h]

theorem H_congr : H c₁ parameter leafIndex = H c₂ parameter leafIndex := by
  refine Finset.sum_congr rfl fun y _ => if_congr ?_ (by rw [W_congr h]) rfl
  simp only [IsHit, h]

theorem C_congr : C c₁ parameter leafIndex = C c₂ parameter leafIndex := by
  simp only [C, h]

theorem V_congr : V c₁ parameter leafIndex = V c₂ parameter leafIndex := by
  unfold V
  exact congrArg Finset.card (Finset.filter_congr fun y _ => by simp only [IsHit, h])

end Agree

/-- **Other inputs.** A query outside the leaf index's encoding inputs changes none of the potentials. -/
theorem potentials_cacheQuery_of_not_input {i : HashInput} (hi : ∀ y, i ≠ input parameter leafIndex y)
    (u : HashOutput) :
    Φ (cache.cacheQuery i u) parameter leafIndex = Φ cache parameter leafIndex ∧
      H (cache.cacheQuery i u) parameter leafIndex = H cache parameter leafIndex ∧
      C (cache.cacheQuery i u) parameter leafIndex = C cache parameter leafIndex ∧
      V (cache.cacheQuery i u) parameter leafIndex = V cache parameter leafIndex := by
  have h : ∀ y, cache.cacheQuery i u (input parameter leafIndex y) = cache (input parameter leafIndex y) :=
    fun y => QueryCache.cacheQuery_of_ne _ _ fun he => hi y he.symm
  exact ⟨Φ_congr h, H_congr h, C_congr h, V_congr h⟩


/-! ### The mass on the hits -/

theorem card_filter_prod (P : Position → Prop) [DecidablePred P] :
    ((Finset.univ.filter P).card : ℝ≥0∞) = ∑ m, ((Finset.univ.filter fun ρ => P (m, ρ)).card : ℝ≥0∞) := by
  simp only [Finset.natCast_card_filter]
  rw [Fintype.sum_prod_type]

theorem C_eq : (C cache parameter leafIndex : ℝ≥0∞) =
    ∑ m, ((Finset.univ.filter fun ρ => line cache parameter leafIndex m ρ ≠ .fresh).card : ℝ≥0∞) := by
  rw [C, card_filter_prod]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.filter_congr fun ρ _ => (status_ne_fresh_iff (m, ρ)).symm]
  rfl

theorem V_eq : (V cache parameter leafIndex : ℝ≥0∞) =
    ∑ m, ((Finset.univ.filter fun ρ => line cache parameter leafIndex m ρ = .hit).card : ℝ≥0∞) := by
  rw [V, card_filter_prod]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.filter_congr fun ρ _ => isHit_iff (m, ρ)]
  rfl

theorem H_eq : H cache parameter leafIndex =
    ∑ m, ∑ z, if line cache parameter leafIndex m z = .hit then
      ∑ r, reach nextRand landing (line cache parameter leafIndex m) z signingAttemptLimit r else 0 := by
  rw [H, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun z _ => ?_
  exact if_congr (isHit_iff (m, z)) rfl rfl

theorem H_eq_hitReach : H cache parameter leafIndex =
    ∑ m, ∑ r, hitReach nextRand landing (line cache parameter leafIndex m) signingAttemptLimit r := by
  rw [H_eq]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [hitReach]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> simp

/-- **Mass bound.** -/
theorem landing_mul_H_le :
    landing * H cache parameter leafIndex ≤
      landing * C cache parameter leafIndex + V cache parameter leafIndex * (1 - landing) := by
  rw [H_eq, C_eq, V_eq, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun m _ =>
    mass_hit_le landing_le_one (line cache parameter leafIndex m) signingAttemptLimit nextRand_no_return


/-- A new hit only cuts walks. -/
theorem reach_update_hit_le {α : Type} [DecidableEq α] {σ : Equiv.Perm α} {p : ℝ≥0∞} (st : α → St) (x y : α) :
    ∀ (A : ℕ) (r : α), reach σ p (Function.update st x .hit) y A r ≤ reach σ p st y A r
  | 0, _ => le_rfl
  | A + 1, r => by
      by_cases hr : r = y
      · rw [hr, reach_self, reach_self]
      by_cases hrx : r = x
      · rw [reach_succ_hit A hr (by rw [hrx, Function.update_self])]; exact bot_le
      have hst : Function.update st x St.hit r = st r := Function.update_of_ne hrx _ _
      have ih := reach_update_hit_le (σ := σ) (p := p) st x y A (σ r)
      cases h : st r with
      | hit => rw [reach_succ_hit A hr (hst.trans h), reach_succ_hit A hr h]
      | miss => rw [reach_succ_miss A hr (hst.trans h), reach_succ_miss A hr h]; exact ih
      | fresh => rw [reach_succ_fresh A hr (hst.trans h), reach_succ_fresh A hr h]; gcongr

/-! ### The reach under the query -/

section Query

variable (x : Position)

theorem W_cacheQuery_of_ne (u : HashOutput) {y : Position} (hm : y.1 ≠ x.1) :
    W (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex y = W cache parameter leafIndex y := by
  rw [W_eq, W_eq, line_cacheQuery_of_ne x u hm]

theorem W_cacheQuery_line (u : HashOutput) (ρ : Randomness) :
    W (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex (x.1, ρ) =
      ∑ r, reach nextRand landing (Function.update (line cache parameter leafIndex x.1) x.2 (outcome u)) ρ
        signingAttemptLimit r := by
  rw [W_eq, line_cacheQuery_self]

theorem W_cacheQuery_self (u : HashOutput) :
    W (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex x = W cache parameter leafIndex x := by
  have := W_cacheQuery_line (cache := cache) (parameter := parameter) (leafIndex := leafIndex) x u x.2
  rw [this, W_eq]
  exact Finset.sum_congr rfl fun r _ => reach_update_self _ _ _ _ _

/-- A landing at `x` does not raise the reach to any position. -/
theorem W_cacheQuery_le_of_hit {u : HashOutput} (hu : outcome u = .hit) (y : Position) :
    W (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex y ≤ W cache parameter leafIndex y := by
  by_cases hm : y.1 = x.1
  · obtain ⟨m, ρ⟩ := y
    simp only at hm
    subst hm
    rw [W_cacheQuery_line, hu, W_eq]
    exact Finset.sum_le_sum fun r _ => reach_update_hit_le _ _ _ _ _
  · rw [W_cacheQuery_of_ne x u hm]

variable {x} (hx : cache (input parameter leafIndex x) = none)
include hx

theorem line_fresh : line cache parameter leafIndex x.1 x.2 = .fresh := by
  simp [line, status, hx]

/-- **Martingale.** The mean reach to any position is unchanged by the query. -/
theorem ex_W (y : Position) :
    ex (fun u => W (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex y) =
      W cache parameter leafIndex y := by
  by_cases hm : y.1 = x.1
  · obtain ⟨m, ρ⟩ := y
    simp only at hm
    subst hm
    simp_rw [W_cacheQuery_line]
    rw [ex_outcome (fun s => ∑ r, reach nextRand landing (Function.update (line cache parameter leafIndex x.1) x.2 s)
      ρ signingAttemptLimit r), Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, W_eq]
    exact Finset.sum_congr rfl fun r _ => reach_probe landing_le_one _ (line_fresh hx) ρ _
      (fun j h0 hj => nextRand_no_return _ j h0 hj) r
  · simp_rw [W_cacheQuery_of_ne x _ hm]
    exact ex_const _

theorem not_isHit_x : ¬ IsHit cache parameter leafIndex x := by
  rw [isHit_iff]; simp [status, hx]

theorem isHit_cacheQuery (u : HashOutput) (y : Position) :
    IsHit (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex y ↔
      (y = x ∧ outcome u = .hit) ∨ IsHit cache parameter leafIndex y := by
  rw [isHit_iff, isHit_iff, status_cacheQuery]
  by_cases h : y = x
  · subst h
    have := not_isHit_x hx
    rw [isHit_iff] at this
    simp [this]
  · simp [h]

theorem V_cacheQuery (u : HashOutput) :
    (V (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex : ℝ≥0∞) =
      V cache parameter leafIndex + if outcome u = .hit then 1 else 0 := by
  rw [V, V, Finset.natCast_card_filter, Finset.natCast_card_filter]
  have h : ∀ y, (if IsHit (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex y then
      (1 : ℝ≥0∞) else 0) = (if IsHit cache parameter leafIndex y then 1 else 0) +
        if y = x then (if outcome u = .hit then 1 else 0) else 0 := fun y => by
    by_cases hy : y = x
    · subst hy; simp [isHit_cacheQuery hx, not_isHit_x hx]
    · simp [isHit_cacheQuery hx, hy]
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _)]

theorem H_cacheQuery (u : HashOutput) :
    H (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex =
      (∑ y, if IsHit cache parameter leafIndex y then
        W (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex y else 0) +
      if outcome u = .hit then W cache parameter leafIndex x else 0 := by
  rw [H]
  have h : ∀ y, (if IsHit (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex y then
      W (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex y else 0) =
      (if IsHit cache parameter leafIndex y then
        W (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex y else 0) +
        if y = x then (if outcome u = .hit then W cache parameter leafIndex x else 0) else 0 := fun y => by
    by_cases hy : y = x
    · subst hy; simp [isHit_cacheQuery hx, not_isHit_x hx, W_cacheQuery_self]
    · simp [isHit_cacheQuery hx, hy]
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _)]

/-- The mean hit mass grows by the landing mass at `x`. -/
theorem ex_H :
    ex (fun u => H (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex) =
      H cache parameter leafIndex + landing * W cache parameter leafIndex x := by
  simp_rw [H_cacheQuery hx]
  rw [ex_add, ex_sum]
  simp_rw [ex_ite, ex_W hx]
  rw [ex_outcome (fun s => if s = .hit then W cache parameter leafIndex x else 0), ite_eq_left rfl,
    ite_eq_right (by decide), mul_zero, add_zero, H]

omit hx in
/-- A landing at `x` never lowers the hit mass. -/
theorem H_le_cacheQuery_of_hit {u : HashOutput} (hu : outcome u = .hit) :
    H cache parameter leafIndex ≤ H (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex := by
  rw [H_eq_hitReach, H_eq_hitReach]
  refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun r _ => ?_
  by_cases hm : m = x.1
  · subst hm
    rw [line_cacheQuery_self, hu]
    exact hitReach_le_update landing_le_one _ _ _ _
  · rw [line_cacheQuery_of_ne x u hm]

/-- **The compensator step.** -/
theorem ex_V_mul_H :
    (V cache parameter leafIndex : ℝ≥0∞) * H cache parameter leafIndex +
        landing * (H cache parameter leafIndex + V cache parameter leafIndex * W cache parameter leafIndex x) ≤
      ex (fun u => (V (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex : ℝ≥0∞) *
        H (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex) := by
  simp_rw [V_cacheQuery hx, add_mul]
  rw [ex_add, ex_const_mul, ex_H hx]
  have hlow : ex (fun u => (if outcome u = .hit then (1 : ℝ≥0∞) else 0) * H cache parameter leafIndex) ≤
      ex (fun u => (if outcome u = .hit then (1 : ℝ≥0∞) else 0) *
        H (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex) :=
    ex_mono fun u => by
      split_ifs with hu
      · simpa using H_le_cacheQuery_of_hit (x := x) hu
      · simp
  rw [ex_outcome (fun s => (if s = .hit then (1 : ℝ≥0∞) else 0) * H cache parameter leafIndex)] at hlow
  simp only [ite_true, one_mul, reduceCtorEq, ite_false, zero_mul, mul_zero, add_zero] at hlow
  calc _ = (V cache parameter leafIndex : ℝ≥0∞) * (H cache parameter leafIndex + landing * W cache parameter leafIndex x) +
        landing * H cache parameter leafIndex := by ring
    _ ≤ _ := add_le_add le_rfl hlow

/-- A partnered position after the query was partnered before, or is `x` with the digest of a hit, or is a
hit whose digest the query repeats. -/
theorem Φ_cacheQuery_le (u : HashOutput) :
    Φ (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex ≤
      (∑ y, if IsPartnered cache parameter leafIndex y then
        W (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex y else 0) +
      (∑ y, if IsHit cache parameter leafIndex y then
        (if truncateHash u = dig cache parameter leafIndex y then 1 else 0) * W cache parameter leafIndex y else 0) +
      (∑ z, if IsHit cache parameter leafIndex z then
        (if truncateHash u = dig cache parameter leafIndex z then 1 else 0) else 0) * W cache parameter leafIndex x := by
  set K := ∑ z, if IsHit cache parameter leafIndex z then
    (if truncateHash u = dig cache parameter leafIndex z then (1 : ℝ≥0∞) else 0) else 0
  have hterm : ∀ y, (if IsPartnered (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex y then
      W (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex y else 0) ≤
      ((if IsPartnered cache parameter leafIndex y then
        W (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex y else 0) +
      (if IsHit cache parameter leafIndex y then
        (if truncateHash u = dig cache parameter leafIndex y then 1 else 0) * W cache parameter leafIndex y else 0)) +
      if y = x then K * W cache parameter leafIndex x else 0 := fun y => by
    by_cases hP : IsPartnered (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex y
    swap
    · rw [ite_eq_right hP]; exact bot_le
    rw [ite_eq_left hP]
    obtain ⟨o, ho, hv, z, hzy, other, hz, htr⟩ := hP
    by_cases hy : y = x
    · subst hy
      rw [QueryCache.cacheQuery_self, Option.some_inj] at ho
      subst ho
      have hz' : cache (input parameter leafIndex z) = some other := by
        rwa [cacheQuery_input_of_ne y z _ hzy] at hz
      have hzhit : IsHit cache parameter leafIndex z := ⟨other, hz', htr ▸ hv⟩
      have hdz : truncateHash u = dig cache parameter leafIndex z := by simp [dig, hz', htr]
      have hK : 1 ≤ K := by
        have h1 := Finset.single_le_sum (f := fun z => if IsHit cache parameter leafIndex z then
          (if truncateHash u = dig cache parameter leafIndex z then (1 : ℝ≥0∞) else 0) else 0)
          (fun _ _ => bot_le) (@Finset.mem_univ Position _ z)
        rw [ite_eq_left hzhit, ite_eq_left hdz] at h1
        exact h1
      rw [ite_eq_left rfl, W_cacheQuery_self]
      exact le_add_left (le_mul_of_one_le_left bot_le hK)
    · have ho' : cache (input parameter leafIndex y) = some o := by
        rwa [cacheQuery_input_of_ne x y u hy] at ho
      rw [ite_eq_right hy, add_zero]
      by_cases hzx : z = x
      · subst hzx
        rw [QueryCache.cacheQuery_self, Option.some_inj] at hz
        subst hz
        have hhit : IsHit cache parameter leafIndex y := ⟨o, ho', hv⟩
        have hd : truncateHash u = dig cache parameter leafIndex y := by simp [dig, ho', htr]
        have hu : outcome u = .hit := by simp [outcome, htr, hv]
        rw [ite_eq_left hhit, ite_eq_left hd, one_mul]
        exact le_add_left (W_cacheQuery_le_of_hit z hu y)
      · have hz' : cache (input parameter leafIndex z) = some other := by
          rwa [cacheQuery_input_of_ne x z _ hzx] at hz
        rw [ite_eq_left ⟨o, ho', hv, z, hzy, other, hz', htr⟩]
        exact le_self_add
  rw [Φ]
  refine (Finset.sum_le_sum fun y _ => hterm y).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _)]

/-- **The partner step.** -/
theorem ex_Φ_le :
    ex (fun u => Φ (cache.cacheQuery (input parameter leafIndex x) u) parameter leafIndex) ≤
      Φ cache parameter leafIndex +
        ((V cache parameter leafIndex : ℝ≥0∞) * W cache parameter leafIndex x + H cache parameter leafIndex) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  refine (ex_mono (Φ_cacheQuery_le hx)).trans_eq ?_
  rw [ex_add, ex_add, ex_mul_const, ex_sum, ex_sum, ex_sum]
  simp_rw [ex_ite, ex_W hx, ex_mul_const, ex_digest]
  have hV : (∑ z, if IsHit cache parameter leafIndex z then ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ else 0) =
      (V cache parameter leafIndex : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
    rw [V, Finset.natCast_card_filter, Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ => by split_ifs <;> simp
  have hH : (∑ y, if IsHit cache parameter leafIndex y then
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ * W cache parameter leafIndex y else 0) =
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ * H cache parameter leafIndex := by
    rw [H, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by split_ifs <;> simp
  rw [hV, hH, ← Φ]
  ring

end Query

end XmssSecurity.Partner
