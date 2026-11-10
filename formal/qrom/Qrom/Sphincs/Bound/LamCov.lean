module

public import Qrom.Sphincs.Bound.Cover

@[expose] public section

/-!
# The cover probability

When the FORS leaves fit the first digest call (`mdBytes ≤ 32`), a coverable first call output has
leaves that the signatures at one index open, so `λ_cov` is at most the expected number of
`k`-tuples of signatures at one index over `2^(k a)`, which is at most
`2^h ∏_{j<k} (N / 2^h + j) / 2^(k a)` for `N` signatures (`Qrom.Sphincs.lamCov_le`).
-/

open OracleComp OracleSpec FORS FORS.Security Concrete Quantum
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

variable [Params]

/-! ## Counting digest views -/

/-- The digest calls, as the digest's view and the bits it drops. -/
def viewEquiv : DigV ≃ FullDigestView × (DroppedBit → Bool) :=
  (Equiv.ofBijective splitCalls splitCalls_bijective).trans
    (Equiv.prodCongr (Equiv.ofBijective fullDigestView fullDigestView_bijective)
      (Equiv.refl (DroppedBit → Bool)))

theorem viewEquiv_fst (v : DigV) : (viewEquiv v).1 = fullDigestView (truncateMessageDigest v) := rfl

/-- A property of the view holds on a fraction of the digest calls equal to its fraction of the
views. -/
theorem card_view_filter (R : FullDigestView → Prop) [DecidablePred R] :
    (Finset.univ.filter fun v : DigV ↦ R (fullDigestView (truncateMessageDigest v))).card *
      Fintype.card FullDigestView = Fintype.card DigV * (Finset.univ.filter R).card := by
  have h1 : (Finset.univ.filter fun v : DigV ↦ R (fullDigestView (truncateMessageDigest v))).card =
      (Finset.univ.filter R).card * Fintype.card (DroppedBit → Bool) := by
    rw [Finset.card_filter, Finset.card_filter,
      Fintype.sum_equiv viewEquiv _ (fun p : FullDigestView × (DroppedBit → Bool) ↦ if R p.1 then 1 else 0)
        (fun v ↦ by rw [viewEquiv_fst]),
      Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    show (∑ _y : DroppedBit → Bool, if R w then 1 else 0) = _
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  have h2 : Fintype.card DigV = Fintype.card FullDigestView * Fintype.card (DroppedBit → Bool) := by
    rw [Fintype.card_congr viewEquiv, Fintype.card_prod]
  rw [h1, h2]
  ring

/-- A digest lands at a given index for a fraction `2^-h` of the digest calls. -/
theorem card_index_eq (t : Index) :
    (Finset.univ.filter fun v : DigV ↦ digestIndex (truncateMessageDigest v) = t).card *
      Fintype.card Index = Fintype.card DigV := by
  have h := card_view_filter (fun w ↦ w.1 = t)
  have hc : (Finset.univ.filter fun w : FullDigestView ↦ w.1 = t).card =
      Fintype.card (FTree → FLeaf) := by
    rw [show (Finset.univ.filter fun w : FullDigestView ↦ w.1 = t) =
        ({t} : Finset Index) ×ˢ (Finset.univ : Finset (FTree → FLeaf)) from by
      ext w; simp; exact ⟨fun h ↦ ⟨w.2, by rw [← h]⟩, fun ⟨a, ha⟩ ↦ by rw [← ha]⟩, Finset.card_product, Finset.card_singleton, one_mul,
      Finset.card_univ]
  rw [hc, Fintype.card_prod] at h
  have hpos : 0 < Fintype.card (FTree → FLeaf) := Fintype.card_pos
  have h' : (Finset.univ.filter fun v : DigV ↦ digestIndex (truncateMessageDigest v) = t).card *
      Fintype.card Index * Fintype.card (FTree → FLeaf) =
      Fintype.card DigV * Fintype.card (FTree → FLeaf) := by
    rw [mul_assoc, ← h]
    rfl
  exact Nat.eq_of_mul_eq_mul_right hpos h'

/-! ## The leaves are read from the first call -/

/-- The digest calls with `y` first and zeros after. -/
def ext0 (y : HashOutput) : DigV := fun c ↦ if c = firstCall then y else 0

theorem ext0_first (y : HashOutput) : ext0 y firstCall = y := by simp [ext0]

theorem outputBit_call0 (ys : DigV) {g : ℕ} (hg : g < 256) : outputBit ys g = (ys firstCall).getLsbD g := by
  have h0 : g / 256 = 0 := Nat.div_eq_of_lt hg
  unfold outputBit
  rw [dite_eq_left (by rw [h0]; exact digestCalls_pos)]
  simp only [h0, Nat.mod_eq_of_lt hg]
  rfl

theorem digestSource_fors_lt (hmd : mdBytes ≤ 32) {q : ℕ} (hlow : totalHeight ≤ q)
    (hq : q < messageDigestBits) : digestSource q < 256 := by
  have hb := bottomHeight_le
  obtain ⟨-, -, hmd', -⟩ := field_bytes_le
  have hp := forsBit_lt hlow hq
  unfold digestSource
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  unfold msbPos
  omega

theorem leaves_call0 (hmd : mdBytes ≤ 32) {ys ys' : DigV} (h : ys firstCall = ys' firstCall) :
    digestLeaves (truncateMessageDigest ys) = digestLeaves (truncateMessageDigest ys') := by
  funext κ
  unfold digestLeaves
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
  have hκ := κ.isLt
  have hle : forsHeight * (κ.val + 1) ≤ forsHeight * forsTrees := Nat.mul_le_mul_left _ hκ
  have hq : leafOffset κ + i < messageDigestBits := by
    unfold leafOffset messageDigestBits
    rw [Nat.mul_succ] at hle
    rw [mul_comm forsTrees]
    omega
  have hlow : totalHeight ≤ leafOffset κ + i := by unfold leafOffset; omega
  rw [getLsbD_truncateMessageDigest _ hq, getLsbD_truncateMessageDigest _ hq,
    outputBit_call0 _ (digestSource_fors_lt hmd hlow hq), outputBit_call0 _ (digestSource_fors_lt hmd hlow hq), h]

/-- The fraction of first call outputs whose leaves lie in given sets is the product of the sets'
fractions. -/
theorem card_leaves (hmd : mdBytes ≤ 32) (L : FTree → Finset FLeaf) :
    (Finset.univ.filter fun y : HashOutput ↦
        ∀ κ, digestLeaves (truncateMessageDigest (ext0 y)) κ ∈ L κ).card *
      Fintype.card (FTree → FLeaf) = Fintype.card HashOutput * ∏ κ, (L κ).card := by
  set S := Finset.univ.filter fun y : HashOutput ↦
    ∀ κ, digestLeaves (truncateMessageDigest (ext0 y)) κ ∈ L κ
  let e := Equiv.piSplitAt firstCall fun _ : DigestCall ↦ HashOutput
  -- the digest calls whose leaves lie in `L` are those whose first call lies in `S`
  have ha : (Finset.univ.filter fun ys : DigV ↦
      ∀ κ, (fullDigestView (truncateMessageDigest ys)).2 κ ∈ L κ).card =
      S.card * Fintype.card ({j // j ≠ firstCall} → HashOutput) := by
    rw [Finset.card_filter, Finset.card_filter]
    have hf : ∀ ys : DigV, (if ∀ κ, (fullDigestView (truncateMessageDigest ys)).2 κ ∈ L κ then 1 else 0) =
        (fun p : HashOutput × ({j // j ≠ firstCall} → HashOutput) ↦
          if ∀ κ, digestLeaves (truncateMessageDigest (ext0 p.1)) κ ∈ L κ then 1 else 0) (e ys) := by
      intro ys
      have hl : digestLeaves (truncateMessageDigest ys) =
          digestLeaves (truncateMessageDigest (ext0 (ys firstCall))) :=
        leaves_call0 hmd (ext0_first _).symm
      have he : (e ys).1 = ys firstCall := rfl
      simp only [fullDigestView, hl, he]
    rw [Fintype.sum_equiv e _ (fun p : HashOutput × ({j // j ≠ firstCall} → HashOutput) ↦
          if ∀ κ, digestLeaves (truncateMessageDigest (ext0 p.1)) κ ∈ L κ then 1 else 0) hf,
      Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    show (∑ _r : {j // j ≠ firstCall} → HashOutput,
      if ∀ κ, digestLeaves (truncateMessageDigest (ext0 y)) κ ∈ L κ then 1 else 0) = _
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  have hb := card_view_filter (fun w ↦ ∀ κ, w.2 κ ∈ L κ)
  have hc : (Finset.univ.filter fun w : FullDigestView ↦ ∀ κ, w.2 κ ∈ L κ).card =
      Fintype.card Index * ∏ κ, (L κ).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    show ∑ _x : Index, ∑ y : FTree → FLeaf, (if ∀ κ, y κ ∈ L κ then 1 else 0) = _
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    congr 1
    rw [← Finset.card_filter, ← Fintype.card_piFinset]
    congr 1
    ext ℓ
    simp [Fintype.mem_piFinset]
  have hd : Fintype.card DigV = Fintype.card HashOutput * Fintype.card ({j // j ≠ firstCall} → HashOutput) := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  rw [ha, hc, hd, Fintype.card_prod] at hb
  have hpos : 0 < Fintype.card ({j // j ≠ firstCall} → HashOutput) * Fintype.card Index :=
    Nat.mul_pos Fintype.card_pos Fintype.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc S.card * Fintype.card (FTree → FLeaf) *
        (Fintype.card ({j // j ≠ firstCall} → HashOutput) * Fintype.card Index) =
      S.card * Fintype.card ({j // j ≠ firstCall} → HashOutput) *
        (Fintype.card Index * Fintype.card (FTree → FLeaf)) := by ring
    _ = _ := by rw [hb]; ring

/-! ## Tuples with few distinct entries -/

theorem sum_pow_card_image (q : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ∀ k : ℕ, ∑ f : Fin k → Fin q, x ^ (Finset.univ.image f).card ≤ ∏ j ∈ Finset.range k, (j + q * x)
  | 0 => by simp
  | k + 1 => by
    rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (k + 1) ↦ Fin q), Fintype.sum_prod_type,
      Finset.prod_range_succ]
    have himg : ∀ (v : Fin q) (f : Fin k → Fin q), Finset.univ.image (Fin.cons v f : Fin (k + 1) → Fin q) =
        insert v (Finset.univ.image f) := by
      intro v f
      ext w
      simp [Fin.exists_fin_succ, eq_comm]
    have hstep : ∀ f : Fin k → Fin q, ∑ v : Fin q,
        x ^ (insert v (Finset.univ.image f)).card ≤ (k + q * x) * x ^ (Finset.univ.image f).card := by
      intro f
      set S := Finset.univ.image f
      have hS : (S.card : ℝ) ≤ k := by
        have := Finset.card_image_le (s := Finset.univ) (f := f)
        rw [Finset.card_univ, Fintype.card_fin] at this
        exact_mod_cast this
      have hpt : ∀ v, x ^ (insert v S).card ≤ (if v ∈ S then 1 else 0) * x ^ S.card + x * x ^ S.card := by
        intro v
        have hp : 0 ≤ x ^ S.card := pow_nonneg hx _
        by_cases hv : v ∈ S
        · simp only [Finset.insert_eq_of_mem hv, hv, ite_true]
          nlinarith
        · simp only [Finset.card_insert_of_notMem hv, hv, ite_false, pow_succ]
          nlinarith
      refine (Finset.sum_le_sum fun v _ ↦ hpt v).trans ?_
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Finset.sum_boole]
      have hfS : (Finset.univ.filter fun v ↦ v ∈ S) = S := by ext; simp
      rw [hfS, nsmul_eq_mul]
      have hp : 0 ≤ x ^ S.card := pow_nonneg hx _
      nlinarith
    rw [Finset.sum_comm]
    have hc : ∀ v f, (Fin.consEquiv (fun _ : Fin (k + 1) ↦ Fin q)) (v, f) = Fin.cons v f := fun _ _ ↦ rfl
    simp only [hc, himg]
    calc ∑ f : Fin k → Fin q, ∑ v : Fin q, x ^ (insert v (Finset.univ.image f)).card
        ≤ ∑ f : Fin k → Fin q, (k + q * x) * x ^ (Finset.univ.image f).card :=
          Finset.sum_le_sum fun f _ ↦ hstep f
      _ = (k + q * x) * ∑ f : Fin k → Fin q, x ^ (Finset.univ.image f).card := by rw [Finset.mul_sum]
      _ ≤ (k + q * x) * ∏ j ∈ Finset.range k, (j + q * x) :=
          mul_le_mul_of_nonneg_left (sum_pow_card_image q hx k) (by positivity)
      _ = _ := by ring

/-! ## The bound -/

/-- The index of the digest of some digest call outputs. -/
abbrev idxD (v : DigV) : Index := digestIndex (truncateMessageDigest v)

/-- The number of presampled digests at the index `t`. -/
def cnt (δ : Fin signatureLimit → DigV) (t : Index) : ℕ :=
  (Finset.univ.filter fun i ↦ idxD (δ i) = t).card

/-- **The cover bound**: `2^h ∏_{j<k} (j + N / 2^h) / 2^(k a)`. -/
def lamB : ℝ := (Fintype.card Index : ℝ) *
  (∏ j ∈ Finset.range forsTrees, ((j : ℝ) + signatureLimit * (Fintype.card Index : ℝ)⁻¹)) /
    Fintype.card (FTree → FLeaf)

theorem card_leavesAll_le (δ : Fin signatureLimit → DigV) (t : Index) (κ : FTree) :
    (leavesAll δ t κ).card ≤ cnt δ t := by
  classical
  refine (Finset.card_le_card fun leaf hl ↦ ?_).trans
    (Finset.card_image_le (s := Finset.univ.filter fun i ↦ idxD (δ i) = t)
      (f := fun i ↦ digestLeaves (truncateMessageDigest (δ i)) κ))
  simp only [leavesAll, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  obtain ⟨i, hi, hk⟩ := hl
  exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hk⟩

open Classical in
/-- Per presampled digests: the coverable fraction is at most the `k`-th powers of the counts. -/
theorem sbC_le (hmd : mdBytes ≤ 32) (δ : Fin signatureLimit → DigV) :
    (sbC δ : ℝ) / Fintype.card HashOutput ≤
      ∑ t, (cnt δ t : ℝ) ^ forsTrees / Fintype.card (FTree → FLeaf) := by
  have hsub : Finset.univ.filter (Coverable δ) ⊆ Finset.univ.biUnion fun t ↦
      Finset.univ.filter fun y : HashOutput ↦
        ∀ κ, digestLeaves (truncateMessageDigest (ext0 y)) κ ∈ leavesAll δ t κ := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨ys, hys, hcov⟩ := hy
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    refine ⟨digestIndex (truncateMessageDigest ys), fun κ ↦ ?_⟩
    have hl := leaves_call0 hmd (ys := ys) (ys' := ext0 y) (by rw [hys, ext0_first])
    rw [← hl]
    exact hcov κ
  have hc := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hY : (0 : ℝ) < Fintype.card HashOutput := by exact_mod_cast Fintype.card_pos
  have hF : (0 : ℝ) < Fintype.card (FTree → FLeaf) := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hY, Finset.sum_mul]
  refine (Nat.cast_le.mpr hc).trans ?_
  push_cast
  refine Finset.sum_le_sum fun t _ ↦ ?_
  have hl := card_leaves hmd (leavesAll δ t)
  have hle : (∏ κ, (leavesAll δ t κ).card : ℝ) ≤ (cnt δ t : ℝ) ^ forsTrees := by
    calc (∏ κ, (leavesAll δ t κ).card : ℝ) ≤ ∏ _κ : FTree, (cnt δ t : ℝ) :=
          Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun κ _ ↦ by
            exact_mod_cast card_leavesAll_le δ t κ
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hl' : ((Finset.univ.filter fun y : HashOutput ↦
      ∀ κ, digestLeaves (truncateMessageDigest (ext0 y)) κ ∈ leavesAll δ t κ).card : ℝ) *
      Fintype.card (FTree → FLeaf) = Fintype.card HashOutput * ∏ κ, ((leavesAll δ t κ).card : ℝ) := by
    exact_mod_cast hl
  rw [div_mul_eq_mul_div, le_div_iff₀ hF, hl', mul_comm ((cnt δ t : ℝ) ^ forsTrees)]
  exact mul_le_mul_of_nonneg_left hle hY.le

/-- The presampled digests that put the digests of a tuple's signatures at `t`. -/
theorem card_tuple_at (f : FTree → Fin signatureLimit) (t : Index) :
    ((Finset.univ.filter fun δ : Fin signatureLimit → DigV ↦ ∀ κ, idxD (δ (f κ)) = t).card : ℝ) =
      (Fintype.card DigV : ℝ) ^ signatureLimit *
        ((Fintype.card Index : ℝ)⁻¹) ^ (Finset.univ.image f).card := by
  classical
  set S : Fin signatureLimit → Finset DigV := fun i ↦
    if i ∈ Finset.univ.image f then Finset.univ.filter fun v ↦ idxD v = t else Finset.univ
  have hset : (Finset.univ.filter fun δ : Fin signatureLimit → DigV ↦ ∀ κ, idxD (δ (f κ)) = t) =
      Fintype.piFinset S := by
    ext δ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, S]
    constructor
    · intro h i
      split_ifs with hi
      · obtain ⟨κ, -, rfl⟩ := Finset.mem_image.mp hi
        simpa using h κ
      · exact Finset.mem_univ _
    · intro h κ
      have := h (f κ)
      rw [ite_eq_left (Finset.mem_image_of_mem f (Finset.mem_univ κ))] at this
      simpa using this
  have hI : (0 : ℝ) < Fintype.card Index := by exact_mod_cast Fintype.card_pos
  have hn : ((Finset.univ.filter fun v : DigV ↦ idxD v = t).card : ℝ) =
      Fintype.card DigV * (Fintype.card Index : ℝ)⁻¹ := by
    have h := card_index_eq t
    rw [eq_mul_inv_iff_mul_eq₀ hI.ne']
    exact_mod_cast h
  rw [hset, Fintype.card_piFinset]
  push_cast
  have hS : ∀ i, ((S i).card : ℝ) = Fintype.card DigV *
      (if i ∈ Finset.univ.image f then (Fintype.card Index : ℝ)⁻¹ else 1) := by
    intro i
    simp only [S]
    split_ifs
    · exact hn
    · rw [Finset.card_univ, mul_one]
  rw [Finset.prod_congr rfl fun i _ ↦ hS i, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- **The cover probability is at most `lamB`.** -/
theorem lamCov_le (hmd : mdBytes ≤ 32) : lamCov ≤ ENNReal.ofReal lamB := by
  set cΔ := (Fintype.card (Fin signatureLimit → DigV) : ℝ)
  set r : (Fin signatureLimit → DigV) → ℝ := fun δ ↦ (sbC δ : ℝ) / Fintype.card HashOutput
  have hΔ : 0 < cΔ := Nat.cast_pos.mpr Fintype.card_pos
  have hcΔ : cΔ = (Fintype.card DigV : ℝ) ^ signatureLimit := by
    simp only [cΔ, Fintype.card_fun, Fintype.card_fin]; push_cast; ring
  have hr : ∀ δ, 0 ≤ r δ := fun δ ↦ by positivity
  have hlam : lamCov = ENNReal.ofReal (cΔ⁻¹ * ∑ δ, r δ) := by
    rw [lamCov, ENNReal.ofReal_mul (inv_nonneg.mpr hΔ.le), ENNReal.ofReal_inv_of_pos hΔ,
      ENNReal.ofReal_sum_of_nonneg fun δ _ ↦ hr δ]
    simp only [cΔ, ENNReal.ofReal_natCast, r]
  rw [hlam]
  refine ENNReal.ofReal_le_ofReal ?_
  set F := (Fintype.card (FTree → FLeaf) : ℝ)
  set I := (Fintype.card Index : ℝ)
  have hF : 0 < F := Nat.cast_pos.mpr Fintype.card_pos
  have hI : 0 < I := Nat.cast_pos.mpr Fintype.card_pos
  -- the `k`-th power of a count counts the tuples of signatures there
  have hpow : ∀ δ t, (cnt δ t : ℝ) ^ forsTrees =
      ((Finset.univ.filter fun f : FTree → Fin signatureLimit ↦ ∀ κ, idxD (δ (f κ)) = t).card : ℝ) := by
    intro δ t
    classical
    have : (Finset.univ.filter fun f : FTree → Fin signatureLimit ↦ ∀ κ, idxD (δ (f κ)) = t) =
        Fintype.piFinset fun _ : FTree ↦ Finset.univ.filter fun i ↦ idxD (δ i) = t := by
      ext f; simp [Fintype.mem_piFinset]
    rw [this, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, cnt]
    push_cast; ring
  have hswap : ∀ t, ∑ δ : Fin signatureLimit → DigV, (cnt δ t : ℝ) ^ forsTrees =
      ∑ f : FTree → Fin signatureLimit, cΔ * I⁻¹ ^ (Finset.univ.image f).card := by
    intro t
    simp only [hpow, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ ↦ ?_
    have h := card_tuple_at f t
    rw [Finset.card_filter] at h
    push_cast at h
    rw [h, hcΔ]
  calc cΔ⁻¹ * ∑ δ, r δ ≤ cΔ⁻¹ * ∑ δ, ∑ t, (cnt δ t : ℝ) ^ forsTrees / F :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun δ _ ↦ sbC_le hmd δ) (inv_nonneg.mpr hΔ.le)
    _ = F⁻¹ * ∑ t : Index, (cΔ⁻¹ * ∑ δ, (cnt δ t : ℝ) ^ forsTrees) := by
        rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ ↦ ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun δ _ ↦ ?_
        rw [div_eq_mul_inv]; ring
    _ = F⁻¹ * (I * ∑ f : FTree → Fin signatureLimit, I⁻¹ ^ (Finset.univ.image f).card) := by
        simp only [hswap]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, ← mul_assoc cΔ⁻¹,
          inv_mul_cancel₀ hΔ.ne', one_mul]
    _ ≤ F⁻¹ * (I * ∏ j ∈ Finset.range forsTrees, ((j : ℝ) + signatureLimit * I⁻¹)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hI.le) (inv_nonneg.mpr hF.le)
        exact sum_pow_card_image signatureLimit (inv_nonneg.mpr hI.le) forsTrees
    _ = lamB := by rw [lamB]; ring

end Qrom.Sphincs
