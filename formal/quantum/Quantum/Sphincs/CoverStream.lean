module

public import Quantum.Sphincs.Coverage
public import Quantum.Sphincs.Keccak
public import Quantum.Xmss.Hybrid.Seed

@[expose] public section

/-!
# The FORS coverage of a stream of `H_msg` outputs

The event side discloses FORS leaves from a presampled stream: the `j`-th distinct signed message
gets the two `H_msg` outputs `d j : DigestCall → HashOutput`. This file instantiates
`Coverage.lean`'s mean price at that stream.

* `digestView o`: the FORS view `(idx, leaves)` the statement reads from the outputs `o`
  (`digestIndex`, `digestForsLeaves` of `truncateMessageDigest o`); `digestView_eq` gives it by
  `hiOf`, `loOf`, `leavesOf`, and `card_fiber_digestView`: each view has `2^246` output pairs.
* `streamCover d := revealed (digestView ∘ d)`, the static disclosures of the stream.
* `uavg_price_stream_eq`: the uniform average of `price (streamCover d)` over streams of length
  `n` is `expectedPrice n` (by `expectedPrice_comp`); `uavg_price_stream_le`: at
  `n = signatureLimit` it is at most `rhoCov / 2^128`, `rhoCov = 1.4726`. The `HalfCov` rate
  `2^16 · price` averages to at most `2^16 · rhoCov / 2^128` (`uavg_halfPrice_stream_le`).
  `uavg_price_streamPairs_le` is the same average over the uncurried coordinates
  `Fin n × DigestCall → HashOutput`.
* Monotonicity (`Disclosures` ordered pointwise): `Covered`, `HalfCov`, `coverMass` and `price`
  are monotone. `ofViews W` discloses a finite set of views; the disclosures of views drawn from
  the stream are below its static set (`ofViews_le_streamCover`), as are those of any re-indexed
  part of the stream (`streamCover_comp_le`).
-/

open Finset Sphincs HashSig
open Quantum.Xmss.Hybrid (uavg uavg_const_mul)
open scoped ENNReal

namespace Quantum.Sphincs

-- Keep elaboration from unfolding `univ` of the large `Fin` types.
attribute [local irreducible] Fin.fintype

/-! ## Monotonicity in the disclosures -/

theorem covered_mono {S T : Disclosures} (h : S ≤ T) {w : View} (hw : Covered S w) :
    Covered T w :=
  fun κ ↦ h w.1 κ (hw κ)

theorem halfCov_mono {S T : Disclosures} (h : S ≤ T) {y : Fin (2 ^ 10) × ForsLeaves}
    (hy : HalfCov S y) : HalfCov T y := by
  obtain ⟨idx, hidx, hcov⟩ := hy
  exact ⟨idx, hidx, covered_mono h hcov⟩

theorem coverMass_mono {S T : Disclosures} (h : S ≤ T) : coverMass S ≤ coverMass T := by
  unfold coverMass
  gcongr with idx _ κ _
  exact h idx κ

theorem price_nonneg (S : Disclosures) : 0 ≤ price S := by
  unfold price
  positivity

theorem price_mono {S T : Disclosures} (h : S ≤ T) : price S ≤ price T := by
  unfold price
  gcongr
  exact_mod_cast coverMass_mono h

/-- The disclosures of a finite set of views. -/
def ofViews (W : Finset View) : Disclosures := fun idx κ ↦
  (W.filter fun w ↦ w.1 = idx).image fun w ↦ w.2 κ

theorem mem_ofViews {W : Finset View} {idx : Index} {κ : ForsTreeIndex} {a : ForsLeafIndex} :
    a ∈ ofViews W idx κ ↔ ∃ w ∈ W, w.1 = idx ∧ w.2 κ = a := by
  simp only [ofViews, mem_image, mem_filter, and_assoc]

theorem ofViews_mono {W W' : Finset View} (h : W ⊆ W') : ofViews W ≤ ofViews W' :=
  fun _ _ _ ha ↦ by
    obtain ⟨w, hw, h1, h2⟩ := mem_ofViews.mp ha
    exact mem_ofViews.mpr ⟨w, h hw, h1, h2⟩

theorem covered_ofViews_iff (W : Finset View) (w : View) :
    Covered (ofViews W) w ↔ ∀ κ, ∃ u ∈ W, u.1 = w.1 ∧ u.2 κ = w.2 κ :=
  forall_congr' fun _ ↦ mem_ofViews

theorem ofViews_le_revealed {n : ℕ} (d : Fin n → View) {W : Finset View}
    (h : ∀ w ∈ W, ∃ j, d j = w) : ofViews W ≤ revealed d := fun idx κ a ha ↦ by
  obtain ⟨w, hw, h1, h2⟩ := mem_ofViews.mp ha
  obtain ⟨j, rfl⟩ := h w hw
  simp only [revealed, mem_image, mem_filter, mem_univ, true_and]
  exact ⟨j, h1, h2⟩

theorem revealed_comp_le {m n : ℕ} (d : Fin n → View) (σ : Fin m → Fin n) :
    revealed (d ∘ σ) ≤ revealed d := fun idx κ a ha ↦ by
  simp only [revealed, Function.comp_apply, mem_image, mem_filter, mem_univ, true_and] at ha ⊢
  obtain ⟨j, h1, h2⟩ := ha
  exact ⟨σ j, h1, h2⟩

/-! ## The view of an `H_msg` output pair -/

/-- The FORS view of the outputs `o` of the two `H_msg` calls, as the statement reads it. -/
def digestView (o : DigestCall → HashOutput) : View :=
  (digestIndex (truncateMessageDigest o), digestForsLeaves (truncateMessageDigest o))

theorem digestView_eq (o : DigestCall → HashOutput) :
    digestView o = (joinIndex (hiOf (o 0)) (loOf (o 1)), leavesOf (o 0)) := by
  rw [digestView, digestIndex_truncate, digestForsLeaves_truncate]

theorem joinIndex_eq_iff (hi : Fin (2 ^ 10)) (lo : Fin (2 ^ 16)) (idx : Index) :
    joinIndex hi lo = idx ↔ hi.val = idx.val / 2 ^ 16 ∧ lo.val = idx.val % 2 ^ 16 := by
  have h1 : hi.val < 1024 := hi.isLt
  have h2 : lo.val < 65536 := lo.isLt
  rw [Fin.ext_iff]
  change hi.val * 2 ^ 16 + lo.val = idx.val ↔ _
  simp only [Nat.reducePow]
  omega

theorem digestCall_cases (i : DigestCall) : i = 0 ∨ i = 1 := by
  obtain ⟨k, hk⟩ := i
  have hk' : k < 2 := hk
  match k, hk' with
  | 0, _ => exact Or.inl rfl
  | 1, _ => exact Or.inr rfl

theorem digestCall_one_ne_zero : (1 : DigestCall) ≠ 0 := by decide

theorem univ_digestCall : (univ : Finset DigestCall) = {0, 1} := by
  ext i
  simp only [mem_univ, mem_insert, mem_singleton, true_iff]
  exact digestCall_cases i

/-- **Each view has `2^246` output pairs**: `2^6` call-0 outputs per top index bits and leaves,
`2^240` call-1 outputs per low index bits. -/
theorem card_fiber_digestView (w : View) :
    #(univ.filter fun o : DigestCall → HashOutput ↦ digestView o = w) = 2 ^ 246 := by
  obtain ⟨idx, ℓ⟩ := w
  have hidx : idx.val < 2 ^ 26 := idx.isLt
  let hi : Fin (2 ^ 10) := ⟨idx.val / 2 ^ 16, by omega⟩
  let lo : Fin (2 ^ 16) := ⟨idx.val % 2 ^ 16, Nat.mod_lt _ (by norm_num)⟩
  let A : DigestCall → Finset HashOutput := fun i ↦
    if i = 0 then univ.filter fun y : HashOutput ↦ (hiOf y, leavesOf y) = (hi, ℓ)
    else univ.filter fun y : HashOutput ↦ loOf y = lo
  have hA0 : A 0 = univ.filter fun y : HashOutput ↦ (hiOf y, leavesOf y) = (hi, ℓ) :=
    ite_eq_left_iff.mpr fun h ↦ (h rfl).elim
  have hA1 : A 1 = univ.filter fun y : HashOutput ↦ loOf y = lo :=
    ite_eq_right_iff.mpr fun h ↦ (digestCall_one_ne_zero h).elim
  have hset : (univ.filter fun o : DigestCall → HashOutput ↦ digestView o = (idx, ℓ)) =
      Fintype.piFinset A := by
    ext o
    have hall : (∀ i, o i ∈ A i) ↔ o 0 ∈ A 0 ∧ o 1 ∈ A 1 :=
      ⟨fun h ↦ ⟨h 0, h 1⟩, fun h i ↦ (digestCall_cases i).elim (fun e ↦ e ▸ h.1)
        fun e ↦ e ▸ h.2⟩
    rw [mem_filter, Fintype.mem_piFinset, hall, hA0, hA1, digestView_eq]
    simp only [mem_univ, true_and, mem_filter, Prod.mk.injEq, joinIndex_eq_iff]
    have e1 : hiOf (o 0) = hi ↔ (hiOf (o 0)).val = idx.val / 2 ^ 16 := Fin.ext_iff
    have e2 : loOf (o 1) = lo ↔ (loOf (o 1)).val = idx.val % 2 ^ 16 := Fin.ext_iff
    rw [e1, e2]
    exact ⟨fun ⟨⟨a, b⟩, c⟩ ↦ ⟨⟨a, c⟩, b⟩, fun ⟨⟨a, c⟩, b⟩ ↦ ⟨⟨a, b⟩, c⟩⟩
  rw [hset, Fintype.card_piFinset, univ_digestCall, prod_pair digestCall_one_ne_zero.symm, hA0,
    hA1, card_fiber_hiLeaves, card_fiber_loOf, ← pow_add]

/-! ## The mean price of the stream -/

/-- The static disclosures of a stream of `H_msg` output pairs. -/
def streamCover {n : ℕ} (d : Fin n → DigestCall → HashOutput) : Disclosures :=
  revealed fun j ↦ digestView (d j)

/-- Disclosures of views drawn from the stream are below its static disclosures. -/
theorem ofViews_le_streamCover {n : ℕ} (d : Fin n → DigestCall → HashOutput) {W : Finset View}
    (h : ∀ w ∈ W, ∃ j, digestView (d j) = w) : ofViews W ≤ streamCover d :=
  ofViews_le_revealed _ h

/-- A re-indexed part of the stream discloses less. -/
theorem streamCover_comp_le {m n : ℕ} (d : Fin n → DigestCall → HashOutput) (σ : Fin m → Fin n) :
    streamCover (d ∘ σ) ≤ streamCover d :=
  revealed_comp_le (fun j ↦ digestView (d j)) σ

theorem card_digestPair :
    Fintype.card (DigestCall → HashOutput) = 2 ^ 246 * 2 ^ 266 := by
  rw [Fintype.card_fun, card_hashOutput, Fintype.card_fin, ← pow_add, ← pow_mul]
  simp only [digestCallCount, Nat.reduceMul, Nat.reduceAdd]

theorem card_stream (n : ℕ) :
    Fintype.card (Fin n → DigestCall → HashOutput) = (2 ^ 246 * 2 ^ 266) ^ n := by
  rw [Fintype.card_fun, card_digestPair, Fintype.card_fin]

/-- `expectedPrice` as the mean price of a uniform stream of output pairs. -/
theorem sum_price_stream_div (n : ℕ) :
    (∑ d : Fin n → DigestCall → HashOutput, price (streamCover d)) /
        (Fintype.card (Fin n → DigestCall → HashOutput) : ℚ) = expectedPrice n := by
  rw [← expectedPrice_comp digestView (2 ^ 246) (by positivity) card_fiber_digestView n,
    card_stream]
  simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, streamCover]

/-- **The mean price of a uniform stream** of length `n` is `expectedPrice n`. -/
theorem uavg_price_stream_eq (n : ℕ) :
    uavg (fun d : Fin n → DigestCall → HashOutput ↦ ENNReal.ofReal (price (streamCover d))) =
      ENNReal.ofReal (expectedPrice n) := by
  have hpos : (0 : ℝ) < (Fintype.card (Fin n → DigestCall → HashOutput) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  rw [uavg, ← ENNReal.ofReal_sum_of_nonneg fun d _ ↦ Rat.cast_nonneg.mpr (price_nonneg _),
    ← sum_price_stream_div, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast,
    ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_natCast, div_eq_mul_inv, mul_comm]

/-- **The mean price of a stream of `signatureLimit` output pairs** is at most
`rhoCov / 2^128`. -/
theorem uavg_price_stream_le :
    uavg (fun d : Fin signatureLimit → DigestCall → HashOutput ↦
        ENNReal.ofReal (price (streamCover d))) ≤ ENNReal.ofReal (rhoCov / 2 ^ 128) := by
  rw [uavg_price_stream_eq]
  exact ENNReal.ofReal_le_ofReal (by exact_mod_cast expectedPrice_le)

/-- The `HalfCov` rate `2^16 · price` of the stream, averaged. -/
theorem uavg_halfPrice_stream_le :
    uavg (fun d : Fin signatureLimit → DigestCall → HashOutput ↦
        2 ^ 16 * ENNReal.ofReal (price (streamCover d))) ≤
      2 ^ 16 * ENNReal.ofReal (rhoCov / 2 ^ 128) := by
  rw [uavg_const_mul]
  gcongr
  exact uavg_price_stream_le

/-! ## Uncurried stream coordinates -/

/-- The uniform average is invariant under an equivalence of the averaged types. -/
theorem uavg_comp_equiv {Θ Θ' : Type*} [Fintype Θ] [Fintype Θ'] (e : Θ ≃ Θ') (f : Θ' → ℝ≥0∞) :
    uavg (fun θ ↦ f (e θ)) = uavg f := by
  rw [uavg, uavg, Fintype.card_congr e, Equiv.sum_comp e f]

/-- The stream read from coordinates `(j, i) ↦ t (j, i)`. -/
def streamOfPairs {n : ℕ} (t : Fin n × DigestCall → HashOutput) : Fin n → DigestCall → HashOutput :=
  fun j i ↦ t (j, i)

/-- **The mean price over the uncurried stream coordinates.** -/
theorem uavg_price_streamPairs_le :
    uavg (fun t : Fin signatureLimit × DigestCall → HashOutput ↦
        ENNReal.ofReal (price (streamCover (streamOfPairs t)))) ≤
      ENNReal.ofReal (rhoCov / 2 ^ 128) := by
  have h := uavg_comp_equiv (Equiv.curry (Fin signatureLimit) DigestCall HashOutput)
    (fun d ↦ ENNReal.ofReal (price (streamCover d)))
  exact h.le.trans uavg_price_stream_le

end Quantum.Sphincs

end
