module

public import Statement.LeanSphincs
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

/-!
# FORS coverage at the leanSPHINCS parameters

The FORS view of a full digest is `(idx, s) : View = Index × (ForsTreeIndex → ForsLeafIndex)`; the
disclosures `S : Disclosures` give, per instance and tree, the opened leaves. A view is `Covered`
when each selected leaf is opened. The price of `S` is the fraction of covered views,
`price S = 2^-266 Σ_idx Π_κ |S idx κ|` (`card_covered`).

* `HalfCov S (hi, s)`: some index with top 10 bits `hi` completes a covered view (`halfCov_iff`:
  some low 16 bits `lo` make `(hi · 2^16 + lo, s)` covered). A call-0 digest fixes `hi` and the 24
  leaves, with 6 ignored bits; for any map `f` with fibers of at most `2^6` outputs,
  `halfCov_frac_le` bounds the fraction of outputs `y` with `HalfCov S (f y)` by `2^16 · price S`
  (`card_halfCov_le`: half-covered pairs are at most the covered views).
* `revealed d`: the disclosures of a stream `d : Fin n → View` of signed views. For `n` independent
  uniform views, `expectedPrice_eq` is exact: the mean price is `E[c(M)]` with `M ~ Bin(n, 2^-26)`
  the load of one instance and `c(m) = (1 - (1 - 2^-10)^m)^24` its coverage probability.
  `expectedPrice_le`: at `n = signatureLimit` the mean price is at most `rhoCov / 2^128`,
  `rhoCov = 1.4726`, below the classical certificate's `ρ = 1.8586` (`expectedPrice_le_rhoClassical`).
  The binomial sum is cut at load 120 (`binomMean_le`): below it `(1 - p)^(n - 120)` is bounded by
  a partial binomial expansion of `(1 + p)^(n - 120)` (`one_sub_pow_le`), above it by a geometric
  tail; the finite sums are checked by the kernel (`coverCert`).
* `expectedPrice_comp`: a stream of uniform outputs whose views have equal fibers has the same mean
  price.
-/

open Finset Sphincs HashSig

namespace Quantum.Sphincs

-- Keep elaboration from unfolding `univ` of the large `Fin` types.
attribute [local irreducible] Fin.fintype

/-! ## Views, disclosures, price -/

/-- The 24 selected leaves of a digest. -/
abbrev ForsLeaves := ForsTreeIndex → ForsLeafIndex

/-- The FORS view of a full digest: the instance and its selected leaves. -/
abbrev View := Index × ForsLeaves

/-- The opened leaves, per instance and tree. -/
abbrev Disclosures := Index → ForsTreeIndex → Finset ForsLeafIndex

/-- Every selected leaf of the view is opened. -/
def Covered (S : Disclosures) (v : View) : Prop := ∀ κ, v.2 κ ∈ S v.1 κ

instance (S : Disclosures) : DecidablePred (Covered S) :=
  fun _ ↦ inferInstanceAs (Decidable (∀ _, _))

/-- `Σ_idx Π_κ |S idx κ|`, the number of covered views. -/
def coverMass (S : Disclosures) : ℕ := ∑ idx, ∏ κ, #(S idx κ)

/-- The fraction of covered views. -/
def price (S : Disclosures) : ℚ := coverMass S / 2 ^ 266

theorem card_index : Fintype.card Index = 2 ^ 26 := by simp [Sphincs.indexBits]

theorem card_forsLeaf : Fintype.card ForsLeafIndex = 2 ^ 10 := by simp [Sphincs.forsTreeHeight]

theorem card_forsTree : Fintype.card ForsTreeIndex = 24 := by simp [Sphincs.forsTreeCount]

theorem card_forsLeaves : Fintype.card ForsLeaves = (2 ^ 10) ^ 24 := by
  rw [Fintype.card_fun, card_forsLeaf, card_forsTree]

theorem card_view : Fintype.card View = 2 ^ 266 := by
  rw [Fintype.card_prod, card_forsLeaves, card_index, ← pow_mul, ← pow_add]

theorem card_covered (S : Disclosures) : #(univ.filter (Covered S)) = coverMass S := by
  rw [card_filter, Fintype.sum_prod_type, coverMass]
  refine sum_congr rfl fun idx _ ↦ ?_
  rw [sum_boole, Nat.cast_id, ← Fintype.card_piFinset]
  refine congrArg card (Finset.ext fun s ↦ ?_)
  rw [mem_filter_univ, Fintype.mem_piFinset]
  rfl

theorem price_eq_card (S : Disclosures) : price S = (#(univ.filter (Covered S)) : ℚ) / 2 ^ 266 := by
  rw [price, card_covered]

/-! ## Half coverage of a call-0 digest -/

/-- The top 10 bits of an index. -/
def hiOfIndex (idx : Index) : Fin (2 ^ 10) :=
  ⟨idx.val / 2 ^ 16, Nat.div_lt_of_lt_mul (lt_of_lt_of_eq idx.isLt (by norm_num [indexBits]))⟩

/-- Some index with top bits `h.1` makes `(idx, h.2)` covered: the call-0 part of a digest
(top index bits and leaves) completes to a covered view for some low index bits. -/
def HalfCov (S : Disclosures) (h : Fin (2 ^ 10) × ForsLeaves) : Prop :=
  ∃ idx : Index, idx.val / 2 ^ 16 = h.1.val ∧ Covered S (idx, h.2)

instance (S : Disclosures) : DecidablePred (HalfCov S) := fun _ ↦ by unfold HalfCov; infer_instance

theorem halfCov_iff (S : Disclosures) (hi : Fin (2 ^ 10)) (s : ForsLeaves) :
    HalfCov S (hi, s) ↔ ∃ (lo : Fin (2 ^ 16)) (h : hi.val * 2 ^ 16 + lo.val < 2 ^ indexBits),
      Covered S (⟨hi.val * 2 ^ 16 + lo.val, h⟩, s) := by
  constructor
  · rintro ⟨idx, hidx, hcov⟩
    have e : hi.val * 2 ^ 16 + idx.val % 2 ^ 16 = idx.val := by
      rw [← hidx, Nat.div_add_mod']
    refine ⟨⟨idx.val % 2 ^ 16, Nat.mod_lt _ (by norm_num)⟩, lt_of_eq_of_lt e idx.isLt, ?_⟩
    rwa [show (⟨hi.val * 2 ^ 16 + idx.val % 2 ^ 16, lt_of_eq_of_lt e idx.isLt⟩ : Index) = idx
      from Fin.ext e]
  · rintro ⟨lo, h, hcov⟩
    refine ⟨_, ?_, hcov⟩
    change (hi.val * 2 ^ 16 + lo.val) / 2 ^ 16 = hi.val
    rw [Nat.mul_comm, Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt lo.isLt, Nat.add_zero]

theorem card_halfCov_le (S : Disclosures) : #(univ.filter (HalfCov S)) ≤ coverMass S := by
  rw [← card_covered]
  refine card_le_card_of_surjOn (fun v : View ↦ (hiOfIndex v.1, v.2)) fun h hh ↦ ?_
  rw [mem_coe, mem_filter] at hh
  obtain ⟨idx, hidx, hcov⟩ := hh.2
  have hv : (idx, h.2) ∈ univ.filter (Covered S) := by
    rw [mem_filter]
    exact ⟨mem_univ _, hcov⟩
  refine ⟨(idx, h.2), mem_coe.mpr hv, ?_⟩
  change (hiOfIndex idx, h.2) = h
  rw [show hiOfIndex idx = h.1 from Fin.ext hidx]

/-- Outputs `y` whose part `f y` is half covered, when each part has at most `c` outputs. -/
theorem card_halfCov_comp_le {Y : Type*} [Fintype Y] (S : Disclosures)
    (f : Y → Fin (2 ^ 10) × ForsLeaves) (c : ℕ)
    (hf : ∀ z, #(univ.filter fun y ↦ f y = z) ≤ c) :
    #(univ.filter fun y ↦ HalfCov S (f y)) ≤ c * coverMass S := by
  have h1 : #(univ.filter fun y ↦ HalfCov S (f y)) ≤
      c * #((univ.filter fun y ↦ HalfCov S (f y)).image f) := by
    refine card_le_mul_card_image _ c fun z _ ↦ le_trans (card_le_card ?_) (hf z)
    intro y hy
    rw [mem_filter] at hy ⊢
    exact ⟨mem_univ _, hy.2⟩
  have h2 : (univ.filter fun y ↦ HalfCov S (f y)).image f ⊆ univ.filter (HalfCov S) := by
    intro z hz
    rw [mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [mem_filter] at hy ⊢
    exact ⟨mem_univ _, hy.2⟩
  exact h1.trans (Nat.mul_le_mul_left c ((card_le_card h2).trans (card_halfCov_le S)))

private theorem mul_div_mul_cancel_aux (a b c M : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a * c * (M / (a * b)) * b = c * M := by
  field_simp

/-- The flip fraction of half coverage: with `2^256` outputs and fibers of at most `2^6`, the
fraction of half-covered outputs is at most `2^16 · price S`. -/
theorem halfCov_frac_le {Y : Type*} [Fintype Y] (S : Disclosures)
    (f : Y → Fin (2 ^ 10) × ForsLeaves) (hf : ∀ z, #(univ.filter fun y ↦ f y = z) ≤ 2 ^ 6)
    (hY : Fintype.card Y = 2 ^ 256) :
    (#(univ.filter fun y ↦ HalfCov S (f y)) : ℚ) / Fintype.card Y ≤ 2 ^ 16 * price S := by
  have h : (#(univ.filter fun y ↦ HalfCov S (f y)) : ℚ) ≤ 2 ^ 6 * coverMass S := by
    exact_mod_cast card_halfCov_comp_le S f _ hf
  have e : (2 : ℚ) ^ 16 * ((coverMass S : ℚ) / 2 ^ 266) * 2 ^ 256 = 2 ^ 6 * coverMass S := by
    rw [show (2 : ℚ) ^ 266 = 2 ^ 10 * 2 ^ 256 by rw [← pow_add],
      show (2 : ℚ) ^ 16 = 2 ^ 10 * 2 ^ 6 by rw [← pow_add]]
    exact mul_div_mul_cancel_aux _ _ _ _ (by positivity) (by positivity)
  rw [hY, price, Nat.cast_pow, Nat.cast_ofNat, div_le_iff₀ (by positivity)]
  exact h.trans_eq e.symm

theorem card_hashOutput : Fintype.card HashOutput = 2 ^ 256 := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

/-- `halfCov_frac_le` for a call-0 output. -/
theorem halfCov_frac_hashOutput_le (S : Disclosures) (f : HashOutput → Fin (2 ^ 10) × ForsLeaves)
    (hf : ∀ z, #(univ.filter fun y ↦ f y = z) ≤ 2 ^ 6) :
    (#(univ.filter fun y ↦ HalfCov S (f y)) : ℚ) / 2 ^ 256 ≤ 2 ^ 16 * price S := by
  have h := halfCov_frac_le S f hf card_hashOutput
  rwa [card_hashOutput, Nat.cast_pow, Nat.cast_ofNat] at h

/-! ## Disclosures of a stream of views -/

/-- The disclosures of the views `d`: at `idx`, the leaves the views at `idx` select. -/
def revealed {n : ℕ} (d : Fin n → View) : Disclosures := fun idx κ ↦
  (univ.filter fun j ↦ (d j).1 = idx).image fun j ↦ (d j).2 κ

theorem covered_revealed_iff {n : ℕ} (d : Fin n → View) (i0 : Index) (ℓ : ForsLeaves) :
    Covered (revealed d) (i0, ℓ) ↔ ∀ κ, ∃ j, (d j).1 = i0 ∧ (d j).2 κ = ℓ κ := by
  simp [Covered, revealed]

/-- The mean price of the disclosures of `n` independent uniform views. -/
def expectedPrice (n : ℕ) : ℚ := (∑ d : Fin n → View, price (revealed d)) / (2 ^ 266) ^ n

/-! ## Counting streams -/

section Count

variable {I K F : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] [Fintype F]
  [DecidableEq F]

/-- Summing a function of the number of `i0` entries of a stream. -/
theorem sum_count_eq (n : ℕ) (i0 : I) (h : ℕ → ℚ) :
    ∑ x : Fin n → I, h #(univ.filter fun j ↦ x j = i0) =
      ∑ m ∈ range (n + 1), (n.choose m : ℚ) * ((Fintype.card I - 1 : ℕ) : ℚ) ^ (n - m) * h m := by
  have hfib : ∀ A : Finset (Fin n),
      #(univ.filter fun x : Fin n → I ↦ (univ.filter fun j ↦ x j = i0) = A) =
        (Fintype.card I - 1) ^ (n - #A) := by
    intro A
    have hA : (univ.filter fun x : Fin n → I ↦ (univ.filter fun j ↦ x j = i0) = A) =
        Fintype.piFinset fun j ↦ if j ∈ A then {i0} else univ.erase i0 := by
      ext x
      simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, Finset.ext_iff]
      refine forall_congr' fun j ↦ ?_
      by_cases hj : j ∈ A <;> simp [hj]
    rw [hA, Fintype.card_piFinset]
    calc ∏ j, #(if j ∈ A then {i0} else univ.erase i0)
        = ∏ j, (if j ∈ Aᶜ then Fintype.card I - 1 else 1) :=
          prod_congr rfl fun j _ ↦ by by_cases hj : j ∈ A <;> simp [hj, card_erase_of_mem]
      _ = (Fintype.card I - 1) ^ (n - #A) := by
          rw [prod_ite_mem, univ_inter, prod_const, card_compl, Fintype.card_fin]
  calc ∑ x : Fin n → I, h #(univ.filter fun j ↦ x j = i0)
      = ∑ A ∈ (univ : Finset (Fin n)).powerset,
          ∑ x ∈ univ.filter (fun x : Fin n → I ↦ (univ.filter fun j ↦ x j = i0) = A), h #A :=
        (sum_fiberwise_of_maps_to' (fun x _ ↦ mem_powerset.mpr (subset_univ _))
          fun A ↦ h #A).symm
    _ = ∑ A ∈ (univ : Finset (Fin n)).powerset, ((Fintype.card I - 1 : ℕ) : ℚ) ^ (n - #A) * h #A := by
        refine sum_congr rfl fun A _ ↦ ?_
        rw [sum_const, hfib, nsmul_eq_mul, Nat.cast_pow]
    _ = ∑ m ∈ range (#(univ : Finset (Fin n)) + 1), (#(univ : Finset (Fin n))).choose m •
          (((Fintype.card I - 1 : ℕ) : ℚ) ^ (n - m) * h m) :=
        sum_powerset_apply_card fun m ↦ ((Fintype.card I - 1 : ℕ) : ℚ) ^ (n - m) * h m
    _ = _ := by
        rw [card_univ, Fintype.card_fin]
        refine sum_congr rfl fun m _ ↦ ?_
        rw [nsmul_eq_mul, mul_assoc]

omit [Fintype I] in
/-- Leaf streams covering `ℓ` at the positions where the index stream hits `i0`. -/
theorem card_cover_leaves (n : ℕ) (x : Fin n → I) (i0 : I) (ℓ : K → F) :
    (#(univ.filter fun y : Fin n → K → F ↦ ∀ κ, ∃ j, x j = i0 ∧ y j κ = ℓ κ) : ℚ) =
      ((Fintype.card F : ℚ) ^ n - ((Fintype.card F - 1 : ℕ) : ℚ) ^ #(univ.filter fun j ↦ x j = i0) *
        (Fintype.card F : ℚ) ^ (n - #(univ.filter fun j ↦ x j = i0))) ^ Fintype.card K := by
  classical
  have hcnt : #(univ.filter fun j : Fin n ↦ ¬ x j = i0) = n - #(univ.filter fun j ↦ x j = i0) := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) fun j ↦ x j = i0
    rw [card_univ, Fintype.card_fin] at this
    omega
  have hT : ∀ c : F, (#(univ.filter fun f : Fin n → F ↦ ∃ j, x j = i0 ∧ f j = c) : ℚ) =
      (Fintype.card F : ℚ) ^ n - ((Fintype.card F - 1 : ℕ) : ℚ) ^ #(univ.filter fun j ↦ x j = i0) *
        (Fintype.card F : ℚ) ^ (n - #(univ.filter fun j ↦ x j = i0)) := by
    intro c
    have hU : (univ.filter fun f : Fin n → F ↦ ¬ ∃ j, x j = i0 ∧ f j = c) =
        Fintype.piFinset fun j ↦ if x j = i0 then univ.erase c else univ := by
      ext f
      simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, not_exists, not_and]
      refine forall_congr' fun j ↦ ?_
      by_cases hj : x j = i0 <;> simp [hj]
    have hUc : #(univ.filter fun f : Fin n → F ↦ ¬ ∃ j, x j = i0 ∧ f j = c) =
        (Fintype.card F - 1) ^ #(univ.filter fun j ↦ x j = i0) *
          Fintype.card F ^ (n - #(univ.filter fun j ↦ x j = i0)) := by
      rw [hU, Fintype.card_piFinset]
      have hc : ∀ j, #(if x j = i0 then univ.erase c else (univ : Finset F)) =
          if x j = i0 then Fintype.card F - 1 else Fintype.card F := by
        intro j
        split_ifs <;> simp [card_erase_of_mem]
      rw [prod_congr rfl fun j _ ↦ hc j, prod_ite, prod_const, prod_const, hcnt]
    have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin n → F)))
      fun f ↦ ∃ j, x j = i0 ∧ f j = c
    rw [hUc, card_univ, Fintype.card_fun, Fintype.card_fin] at hsplit
    rw [eq_sub_iff_add_eq]
    exact_mod_cast hsplit
  rw [card_equiv (Equiv.piComm fun (_ : Fin n) (_ : K) ↦ F)
      (t := Fintype.piFinset fun κ ↦ univ.filter fun f : Fin n → F ↦ ∃ j, x j = i0 ∧ f j = ℓ κ)
      fun y ↦ by simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]; exact Iff.rfl,
    Fintype.card_piFinset, Nat.cast_prod, prod_congr rfl fun κ _ ↦ hT (ℓ κ), prod_const, card_univ]

/-- Streams of `(index, leaves)` pairs covering `(i0, ℓ)`, by the number `m` of entries at `i0`. -/
theorem card_cover_stream (n : ℕ) (i0 : I) (ℓ : K → F) (P : (Fin n → I × (K → F)) → Prop)
    [DecidablePred P] (hP : ∀ d, P d ↔ ∀ κ, ∃ j, (d j).1 = i0 ∧ (d j).2 κ = ℓ κ) :
    (#(univ.filter P) : ℚ) =
      ∑ m ∈ range (n + 1), (n.choose m : ℚ) * ((Fintype.card I - 1 : ℕ) : ℚ) ^ (n - m) *
        ((Fintype.card F : ℚ) ^ n - ((Fintype.card F - 1 : ℕ) : ℚ) ^ m *
          (Fintype.card F : ℚ) ^ (n - m)) ^ Fintype.card K := by
  rw [filter_congr fun d _ ↦ hP d, natCast_card_filter,
    ← (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ ↦ I) (fun _ ↦ K → F)).symm.sum_comp,
    Fintype.sum_prod_type]
  simp only [Equiv.arrowProdEquivProdArrow_symm_apply, sum_boole]
  calc ∑ x : Fin n → I, (#(univ.filter fun y : Fin n → K → F ↦
        ∀ κ, ∃ j, x j = i0 ∧ y j κ = ℓ κ) : ℚ)
      = ∑ x : Fin n → I, ((Fintype.card F : ℚ) ^ n -
          ((Fintype.card F - 1 : ℕ) : ℚ) ^ #(univ.filter fun j ↦ x j = i0) *
          (Fintype.card F : ℚ) ^ (n - #(univ.filter fun j ↦ x j = i0))) ^ Fintype.card K :=
        sum_congr rfl fun x _ ↦ card_cover_leaves n x i0 ℓ
    _ = _ := sum_count_eq n i0 fun m ↦ ((Fintype.card F : ℚ) ^ n -
          ((Fintype.card F - 1 : ℕ) : ℚ) ^ m * (Fintype.card F : ℚ) ^ (n - m)) ^ Fintype.card K

end Count

/-- Streams of outputs with equal fibers over their views average as streams of views. -/
theorem sum_comp_eq_of_card_fiber {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (g : Ω → V) (c : ℕ) (hg : ∀ v, #(univ.filter fun ω ↦ g ω = v) = c) (n : ℕ)
    (Φ : (Fin n → V) → ℚ) :
    ∑ d : Fin n → Ω, Φ (fun j ↦ g (d j)) = (c : ℚ) ^ n * ∑ v : Fin n → V, Φ v := by
  calc ∑ d : Fin n → Ω, Φ (fun j ↦ g (d j))
      = ∑ v : Fin n → V, ∑ d ∈ univ.filter (fun d : Fin n → Ω ↦ (fun j ↦ g (d j)) = v), Φ v :=
        (sum_fiberwise_of_maps_to' (fun d _ ↦ mem_univ fun j ↦ g (d j)) Φ).symm
    _ = ∑ v : Fin n → V, (c : ℚ) ^ n * Φ v := by
        refine sum_congr rfl fun v _ ↦ ?_
        have hfib : (univ.filter fun d : Fin n → Ω ↦ (fun j ↦ g (d j)) = v) =
            Fintype.piFinset fun j ↦ univ.filter fun ω ↦ g ω = v j := by
          ext d
          simp [funext_iff]
        rw [sum_const, nsmul_eq_mul, hfib, Fintype.card_piFinset]
        simp [hg]
    _ = _ := (mul_sum _ _ _).symm

/-! ## The mean price as a binomial mean -/

/-- `E[c(M)]` for `M ~ Bin(n, p)`. -/
def binomMean (n : ℕ) (p : ℚ) (c : ℕ → ℚ) : ℚ :=
  ∑ m ∈ range (n + 1), (n.choose m : ℚ) * p ^ m * (1 - p) ^ (n - m) * c m

/-- The probability that `m` uniform views at one instance cover a fixed view there. -/
def coverProb (m : ℕ) : ℚ := (1 - (1 - 1 / 2 ^ 10) ^ m) ^ 24

theorem coverProb_nonneg (m : ℕ) : 0 ≤ coverProb m := by
  have h : ((1 : ℚ) - 1 / 2 ^ 10) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  exact pow_nonneg (by linarith) _

theorem coverProb_le_one (m : ℕ) : coverProb m ≤ 1 := by
  have h0 : 0 ≤ ((1 : ℚ) - 1 / 2 ^ 10) ^ m := pow_nonneg (by norm_num) _
  have h1 : ((1 : ℚ) - 1 / 2 ^ 10) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  exact pow_le_one₀ (by linarith) (by linarith)

/-- One term of the count, normalized. -/
theorem term_eq (a b C : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (k m j n : ℕ) (hn : m + j = n) :
    C * (a - 1) ^ j * (b ^ n - (b - 1) ^ m * b ^ j) ^ k / (a * b ^ k) ^ n =
      C * (1 / a) ^ m * (1 - 1 / a) ^ j * (1 - (1 - 1 / b) ^ m) ^ k := by
  subst hn
  obtain ⟨x, hx⟩ : ∃ x, b - 1 = x * b := ⟨(b - 1) / b, by field_simp⟩
  obtain ⟨y, hy⟩ : ∃ y, a - 1 = y * a := ⟨(a - 1) / a, by field_simp⟩
  have hx' : 1 - 1 / b = x := by field_simp; linarith
  have hy' : 1 - 1 / a = y := by field_simp; linarith
  have e : b ^ (m + j) - (x * b) ^ m * b ^ j = b ^ (m + j) * (1 - x ^ m) := by ring
  have ham : (1 / a) ^ m * a ^ m = 1 := by rw [← mul_pow, one_div_mul_cancel ha, one_pow]
  rw [hy, hx, e, mul_pow (b ^ (m + j)), hx', hy',
    div_eq_iff (pow_ne_zero _ (mul_ne_zero ha (pow_ne_zero _ hb)))]
  linear_combination (-(C * y ^ j * (1 - x ^ m) ^ k * a ^ j * (b ^ k) ^ (m + j))) * ham

theorem expectedPrice_eq (n : ℕ) : expectedPrice n = binomMean n (1 / 2 ^ 26) coverProb := by
  have hv : ∀ v : View, (#(univ.filter fun d : Fin n → View ↦ Covered (revealed d) v) : ℚ) =
      ∑ m ∈ range (n + 1), (n.choose m : ℚ) * (2 ^ 26 - 1) ^ (n - m) *
        ((2 ^ 10) ^ n - (2 ^ 10 - 1) ^ m * (2 ^ 10) ^ (n - m)) ^ 24 := by
    rintro ⟨i0, ℓ⟩
    have h := card_cover_stream n i0 ℓ (fun d ↦ Covered (revealed d) (i0, ℓ))
      fun d ↦ covered_revealed_iff d i0 ℓ
    rw [card_index, card_forsLeaf, card_forsTree, Nat.cast_sub Nat.one_le_two_pow,
      Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one] at h
    exact h
  have hsum : ∑ d : Fin n → View, price (revealed d) =
      (∑ v : View, (#(univ.filter fun d : Fin n → View ↦ Covered (revealed d) v) : ℚ)) /
        2 ^ 266 := by
    simp only [price_eq_card, natCast_card_filter, ← sum_div]
    rw [sum_comm]
  have htot : ∑ d : Fin n → View, price (revealed d) =
      ∑ m ∈ range (n + 1), (n.choose m : ℚ) * (2 ^ 26 - 1) ^ (n - m) *
        ((2 ^ 10) ^ n - (2 ^ 10 - 1) ^ m * (2 ^ 10) ^ (n - m)) ^ 24 := by
    rw [hsum, sum_congr rfl fun v _ ↦ hv v, sum_const, card_univ, card_view, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat, mul_div_cancel_left₀ _ (by positivity)]
  rw [expectedPrice, htot, binomMean, sum_div,
    show ((2 : ℚ) ^ 266) = 2 ^ 26 * (2 ^ 10) ^ 24 by rw [← pow_mul, ← pow_add]]
  refine sum_congr rfl fun m hm ↦ ?_
  exact term_eq _ _ _ (by norm_num) (by norm_num) 24 m (n - m) n
    (by have := mem_range.mp hm; omega)

/-- `expectedPrice` over streams of outputs `ω` (as `D_0, D_1` digest calls) whose views `g ω`
each have `c` outputs. -/
theorem expectedPrice_comp {Ω : Type*} [Fintype Ω] (g : Ω → View) (c : ℕ) (hc : c ≠ 0)
    (hg : ∀ v, #(univ.filter fun ω ↦ g ω = v) = c) (n : ℕ) :
    (∑ d : Fin n → Ω, price (revealed fun j ↦ g (d j))) / ((c : ℚ) * 2 ^ 266) ^ n =
      expectedPrice n := by
  rw [sum_comp_eq_of_card_fiber g c hg n fun v ↦ price (revealed v), expectedPrice, mul_pow,
    mul_div_mul_left _ _ (pow_ne_zero n (Nat.cast_ne_zero.mpr hc))]

/-! ## Bounding a binomial mean -/

theorem choose_mul_pow_le (n M0 : ℕ) {p r : ℚ} (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hpr : n * p ≤ r * (M0 + 1)) (i : ℕ) :
    (n.choose (M0 + i) : ℚ) * p ^ (M0 + i) ≤ n.choose M0 * p ^ M0 * r ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hrec : (n.choose (M0 + i + 1) : ℚ) * (((M0 + i : ℕ) : ℚ) + 1) =
        n.choose (M0 + i) * ((n - (M0 + i) : ℕ) : ℚ) := by
      exact_mod_cast Nat.choose_succ_right_eq n (M0 + i)
    have hsub : ((n - (M0 + i) : ℕ) : ℚ) * p ≤ r * (((M0 + i : ℕ) : ℚ) + 1) := by
      have h1 : ((n - (M0 + i) : ℕ) : ℚ) ≤ n := by exact_mod_cast Nat.sub_le n (M0 + i)
      have h2 : (M0 : ℚ) + 1 ≤ ((M0 + i : ℕ) : ℚ) + 1 := by
        push_cast
        linarith [(Nat.cast_nonneg i : (0 : ℚ) ≤ i)]
      calc ((n - (M0 + i) : ℕ) : ℚ) * p ≤ n * p := mul_le_mul_of_nonneg_right h1 hp
        _ ≤ r * (M0 + 1) := hpr
        _ ≤ r * (((M0 + i : ℕ) : ℚ) + 1) := mul_le_mul_of_nonneg_left h2 hr
    have hC : (0 : ℚ) ≤ n.choose (M0 + i) * p ^ (M0 + i) :=
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _)
    have hk : (0 : ℚ) < ((M0 + i : ℕ) : ℚ) + 1 := by positivity
    have step : (n.choose (M0 + i + 1) : ℚ) * p ^ (M0 + i + 1) ≤
        n.choose (M0 + i) * p ^ (M0 + i) * r := by
      refine le_of_mul_le_mul_right ?_ hk
      calc (n.choose (M0 + i + 1) : ℚ) * p ^ (M0 + i + 1) * (((M0 + i : ℕ) : ℚ) + 1)
          = n.choose (M0 + i) * p ^ (M0 + i) * (((n - (M0 + i) : ℕ) : ℚ) * p) := by
            rw [pow_succ]
            linear_combination p ^ (M0 + i) * p * hrec
        _ ≤ n.choose (M0 + i) * p ^ (M0 + i) * (r * (((M0 + i : ℕ) : ℚ) + 1)) :=
            mul_le_mul_of_nonneg_left hsub hC
        _ = n.choose (M0 + i) * p ^ (M0 + i) * r * (((M0 + i : ℕ) : ℚ) + 1) := by ring
    calc (n.choose (M0 + (i + 1)) : ℚ) * p ^ (M0 + (i + 1))
        = (n.choose (M0 + i + 1) : ℚ) * p ^ (M0 + i + 1) := by rw [add_assoc]
      _ ≤ n.choose (M0 + i) * p ^ (M0 + i) * r := step
      _ ≤ n.choose M0 * p ^ M0 * r ^ i * r := mul_le_mul_of_nonneg_right ih hr
      _ = n.choose M0 * p ^ M0 * r ^ (i + 1) := by rw [pow_succ, mul_assoc]

/-- Cut a binomial mean at load `M0`: exact terms below (with the `(1 - p)` factor at its largest
exponent left), a geometric tail of ratio `r ≥ n p / (M0 + 1)` above. -/
theorem binomMean_le (n M0 : ℕ) (hM0 : M0 ≤ n) {p r : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hpr : n * p ≤ r * (M0 + 1)) {c : ℕ → ℚ}
    (hc0 : ∀ m, 0 ≤ c m) (hc1 : ∀ m, c m ≤ 1) :
    binomMean n p c ≤ (1 - p) ^ (n - M0) * ∑ m ∈ range M0, (n.choose m : ℚ) * p ^ m * c m +
      n.choose M0 * p ^ M0 / (1 - r) := by
  have hq0 : 0 ≤ 1 - p := by linarith
  have hq1 : 1 - p ≤ 1 := by linarith
  rw [binomMean, ← sum_range_add_sum_Ico _ (Nat.le_succ_of_le hM0)]
  refine add_le_add ?_ ?_
  · rw [mul_sum]
    refine sum_le_sum fun m hm ↦ ?_
    have hm : m < M0 := mem_range.mp hm
    have h1 : (1 - p) ^ (n - m) ≤ (1 - p) ^ (n - M0) := pow_le_pow_of_le_one hq0 hq1 (by omega)
    have h2 : 0 ≤ (n.choose m : ℚ) * p ^ m * c m :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _)) (hc0 m)
    calc (n.choose m : ℚ) * p ^ m * (1 - p) ^ (n - m) * c m
        = (n.choose m * p ^ m * c m) * (1 - p) ^ (n - m) := by ring
      _ ≤ (n.choose m * p ^ m * c m) * (1 - p) ^ (n - M0) := mul_le_mul_of_nonneg_left h1 h2
      _ = _ := by ring
  · have hC : (0 : ℚ) ≤ n.choose M0 * p ^ M0 := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _)
    calc ∑ m ∈ Ico M0 (n + 1), (n.choose m : ℚ) * p ^ m * (1 - p) ^ (n - m) * c m
        ≤ ∑ m ∈ Ico M0 (n + 1), (n.choose m : ℚ) * p ^ m := sum_le_sum fun m _ ↦ by
          have hCm : 0 ≤ (n.choose m : ℚ) * p ^ m := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _)
          calc (n.choose m : ℚ) * p ^ m * (1 - p) ^ (n - m) * c m
              ≤ (n.choose m : ℚ) * p ^ m * 1 * 1 :=
                mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1) hCm) (hc1 m) (hc0 m)
                  (by rw [mul_one]; exact hCm)
            _ = _ := by ring
      _ = ∑ i ∈ range (n + 1 - M0), (n.choose (M0 + i) : ℚ) * p ^ (M0 + i) :=
          sum_Ico_eq_sum_range _ _ _
      _ ≤ ∑ i ∈ range (n + 1 - M0), (n.choose M0 : ℚ) * p ^ M0 * r ^ i :=
          sum_le_sum fun i _ ↦ choose_mul_pow_le n M0 hp0 hr0 hpr i
      _ = n.choose M0 * p ^ M0 * ∑ i ∈ range (n + 1 - M0), r ^ i := by rw [mul_sum]
      _ ≤ n.choose M0 * p ^ M0 * (1 / (1 - r)) := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n + 1 - M0) hr0 hr1
          rwa [← range_eq_Ico, pow_zero] at h
      _ = _ := by ring

/-- `(1 - p)^K ≤ 1 / Σ_{i < I} C(K, i) p^i`, the sum a partial expansion of `(1 + p)^K`. -/
theorem one_sub_pow_le (K I : ℕ) (hI0 : 0 < I) (hI : I ≤ K + 1) {p : ℚ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) : (1 - p) ^ K ≤ 1 / ∑ i ∈ range I, (K.choose i : ℚ) * p ^ i := by
  have hnn : ∀ i ∈ range (K + 1), 0 ≤ (K.choose i : ℚ) * p ^ i :=
    fun i _ ↦ mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _)
  have hB : 0 < ∑ i ∈ range I, (K.choose i : ℚ) * p ^ i := by
    have h := single_le_sum (f := fun i ↦ (K.choose i : ℚ) * p ^ i)
      (fun i hi ↦ mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _)) (mem_range.mpr hI0)
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one] at h
    linarith
  have hsum : ∑ i ∈ range I, (K.choose i : ℚ) * p ^ i ≤ (1 + p) ^ K := by
    rw [add_comm, add_pow]
    simp only [one_pow, mul_one]
    calc ∑ i ∈ range I, (K.choose i : ℚ) * p ^ i ≤ ∑ i ∈ range (K + 1), (K.choose i : ℚ) * p ^ i :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hI) fun i hi _ ↦ hnn i hi
      _ = ∑ i ∈ range (K + 1), p ^ i * (K.choose i : ℚ) := sum_congr rfl fun _ _ ↦ mul_comm _ _
  rw [le_div_iff₀ hB]
  calc (1 - p) ^ K * ∑ i ∈ range I, (K.choose i : ℚ) * p ^ i ≤ (1 - p) ^ K * (1 + p) ^ K :=
        mul_le_mul_of_nonneg_left hsum (pow_nonneg (by linarith) _)
    _ = (1 - p ^ 2) ^ K := by rw [← mul_pow]; ring
    _ ≤ 1 := pow_le_one₀ (by nlinarith) (by nlinarith)

theorem choose_cast_eq (n k : ℕ) : (n.choose k : ℚ) = n.descFactorial k / k.factorial := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul,
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr k.factorial_ne_zero)]

/-! ## The bound at `N = signatureLimit` -/

/-- The coverage rate: `E price ≤ rhoCov / 2^128`. -/
def rhoCov : ℚ := 7363 / 5000

/-- The classical FORS certificate's rate `ρ` at height 26 (`rho_h26_b26`, lean_sphincs
`FORS/Certificates/H26.lean`). -/
def rhoClassical : ℚ := 2043559331309 / 1099511627776

set_option maxRecDepth 100000 in
/-- The finite part of the bound, checked by the kernel: loads below 120 exactly, the factor
`(1 - 2^-26)^(N - 120)` through 60 terms of `(1 + 2^-26)^(N - 120)`, the tail at ratio `1/6`. -/
theorem coverCert :
    1 / (∑ i ∈ range 60, ((signatureLimit - 120).choose i : ℚ) * (1 / 2 ^ 26) ^ i) *
        ∑ m ∈ range 120, (signatureLimit.choose m : ℚ) * (1 / 2 ^ 26) ^ m * coverProb m +
      signatureLimit.choose 120 * (1 / 2 ^ 26) ^ 120 / (1 - 1 / 6) ≤ rhoCov / 2 ^ 128 := by
  simp only [choose_cast_eq]
  decide +kernel

/-- The mean price of `signatureLimit` uniform signed views is at most `1.4726 · 2^-128`. -/
theorem expectedPrice_le : expectedPrice signatureLimit ≤ rhoCov / 2 ^ 128 := by
  have hp0 : (0 : ℚ) ≤ 1 / 2 ^ 26 := by positivity
  have hp1 : (1 : ℚ) / 2 ^ 26 ≤ 1 := by norm_num
  have hlow : 0 ≤ ∑ m ∈ range 120, (signatureLimit.choose m : ℚ) * (1 / 2 ^ 26) ^ m * coverProb m :=
    sum_nonneg fun m _ ↦
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _)) (coverProb_nonneg m)
  rw [expectedPrice_eq]
  calc binomMean signatureLimit (1 / 2 ^ 26) coverProb
      ≤ (1 - 1 / 2 ^ 26) ^ (signatureLimit - 120) *
          ∑ m ∈ range 120, (signatureLimit.choose m : ℚ) * (1 / 2 ^ 26) ^ m * coverProb m +
        signatureLimit.choose 120 * (1 / 2 ^ 26) ^ 120 / (1 - 1 / 6) :=
        binomMean_le signatureLimit 120 (by norm_num [signatureLimit]) hp0 hp1 (by norm_num)
          (by norm_num) (by norm_num [signatureLimit]) coverProb_nonneg coverProb_le_one
    _ ≤ 1 / (∑ i ∈ range 60, ((signatureLimit - 120).choose i : ℚ) * (1 / 2 ^ 26) ^ i) *
          ∑ m ∈ range 120, (signatureLimit.choose m : ℚ) * (1 / 2 ^ 26) ^ m * coverProb m +
        signatureLimit.choose 120 * (1 / 2 ^ 26) ^ 120 / (1 - 1 / 6) :=
        add_le_add (mul_le_mul_of_nonneg_right
          (one_sub_pow_le _ 60 (by norm_num) (by norm_num [signatureLimit]) hp0 hp1) hlow) le_rfl
    _ ≤ rhoCov / 2 ^ 128 := coverCert

theorem rhoCov_le_rhoClassical : rhoCov ≤ rhoClassical := by norm_num [rhoCov, rhoClassical]

/-- The classical certificate's `ρ` bounds the mean price. -/
theorem expectedPrice_le_rhoClassical : expectedPrice signatureLimit ≤ rhoClassical / 2 ^ 128 :=
  expectedPrice_le.trans (div_le_div_of_nonneg_right rhoCov_le_rhoClassical (by positivity))

/-- The mean half-coverage rate of a call-0 digest: `2^16 · E price ≤ 2^16 · rhoCov / 2^128`. -/
theorem expectedHalfRate_le : 2 ^ 16 * expectedPrice signatureLimit ≤ 2 ^ 16 * rhoCov / 2 ^ 128 := by
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left expectedPrice_le (by positivity)

end Quantum.Sphincs

end
