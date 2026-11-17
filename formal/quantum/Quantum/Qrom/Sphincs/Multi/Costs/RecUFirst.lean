module

public import Quantum.Qrom.Sphincs.Multi.Costs.RecUMove
public import Quantum.Qrom.Sphincs.Costs.RecUFirst
public import Quantum.Qrom.Xmss.Multi.Costs.RecUFirst

@[expose] public section

/-!
# The first reveals of the `n` users' keys' coordinates

The `n`-user analog of `Quantum.Qrom.Sphincs.Costs.RecUFirst`, at the owner of each cell. At a
first reveal of user `i`'s coordinate `(i, vcoord (msgPos K))` the run before it does not depend on
the pair there, so summed over the hidden values the recorded trial-`J` cells of `(i, K)` on the
value it signs count each recorded cell once: each digest has `2^384` of the `2^512` pairs, and a
cell at the encoding slot of `K` under user `i`'s `PK.seed` is trial `J` of at most one value.

* **Trial cells name their user, key and trial** (`IsBlkJSN`, `IsBlkSN`, `isBlkSN_unique`): under
  distinct `PK.seed`s `P` an encoding cell names the user (its `PK.seed`) and the key. Two users
  with one `PK.seed` share their trial cells, so the first-reveal sum is stated on distinct
  `PK.seed`s (`firstMaskSN`).
* **The potential `Ψ`** (`revPotSN P`): the recorded `h`-cells that are trial cells of a user's key
  whose coordinate is unrevealed. With distinct `PK.seed`s it is one-cell Lipschitz, the searches'
  reads and the programs do not raise it, and a first reveal of `(i, K)` lowers it by the recorded
  trial cells of `(i, K)` (`revDropSN`). Along the prefix the drops add up to at most the sponge
  calls `q` (`totalWeight_dropQWSN_le`).
* **The first reveals** (`sum_totalWeight_firstQWSN_le`): on distinct `PK.seed`s, summed over the
  hidden values, at most `q / 2^128` per hidden value (XMSS's view lemma with a weight per hidden
  value, `sum_queryWeight_view_le_wtN`, trial by trial).
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs.Multi

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Sphincs (Key keyOf msgPos)
open Quantum.Xmss.Hybrid (diagMass lazy_const suppAt_empty queryWeight_zero_weight
  totalWeight_le_totalWeight totalWeight_fintype_sum totalWeight_const_mul_weight
  totalWeight_chargeTrace_le)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT extCls ModedP recKraus initU
  forallQueries_of_modedP totalWeight_le_potential_of_forallQueries tsum_potential_sponge_le
  tsum_potential_le_of_keep potential_basis_init potential_diagPot_sqrt kWt
  viewBy_runtimeR_of_disc eq_of_recKraus_ne_zero querySupportedOn_traceRight
  card_filter_le_of_injective cw_clsKraus_ne_zero cw_readKrausH_ne_zero)
open Quantum.Qrom.Xmss.Multi (sum_queryWeight_view_le_wtN queryWeight_kWt_viewN
  sum_totalWeight_le_of_forallN)

attribute [local irreducible] sphincsRom Fin.fintype

/- Instance search for the register's decidable equality exceeds the default size. -/
set_option synthInstance.maxSize 2000

variable {n : ℕ}

/-! ## Trial cells name their user, key and trial -/

/-- **A trial-`J` cell of user `k.1`'s key `k.2`** under the `PK.seed`s `P`: `k.2` a key of the
signatures, the cell its encoding cell of trial `J` under `P k.1` and some value. -/
def IsBlkJSN (P : Fin n → PublicParameter) (k : Fin n × Key) (J : ℕ) (x : HashDomain) : Prop :=
  InRangeU k.2 ∧ ∃ m : Digest, x = trialCell (P k.1) k.2 m J

/-- **A trial cell of user `k.1`'s key `k.2`**, of a trial below `2^32`. -/
def IsBlkSN (P : Fin n → PublicParameter) (k : Fin n × Key) (x : HashDomain) : Prop :=
  ∃ J < encodingAttemptLimit, IsBlkJSN P k J x

variable {P : Fin n → PublicParameter}

/-- **A trial cell names its user and key**, under distinct `PK.seed`s. -/
theorem isBlkSN_unique (hP : Function.Injective P) {k k' : Fin n × Key} {x : HashDomain}
    (h : IsBlkSN P k x) (h' : IsBlkSN P k' x) : k = k' := by
  obtain ⟨J, -, -, m, rfl⟩ := h
  obtain ⟨J', -, -, m', he⟩ := h'
  obtain ⟨h1, h2⟩ := trialCell_seed_keyU he
  exact Prod.ext (hP h1) h2

/-- **A trial cell names its trial.** -/
theorem isBlkJSN_trial_unique {k : Fin n × Key} {J J' : ℕ} {x : HashDomain}
    (hJ : J < encodingAttemptLimit) (hJ' : J' < encodingAttemptLimit) (h : IsBlkJSN P k J x)
    (h' : IsBlkJSN P k J' x) : J = J' := by
  obtain ⟨-, m, rfl⟩ := h
  obtain ⟨-, m', he⟩ := h'
  exact (trialCell_injU hJ hJ' he).2

/-! ## The potential `Ψ` -/

variable (P) in
open scoped Classical in
/-- The users' keys with unrevealed coordinates (under the label `L`) of which `x` is a trial
cell. -/
noncomputable def blkCntSN (L : Finset (TPosN n)) (x : HashDomain) : ℝ :=
  ∑ k : Fin n × Key, if (k.1, vcoord (msgPos k.2)) ∉ L ∧ IsBlkSN P k x then 1 else 0

variable (P) in
open scoped Classical in
/-- **The potential `Ψ`**: the recorded `h`-cells that are trial cells of users' keys with
unrevealed coordinates. -/
noncomputable def revPotSN (s : RRegSN n (SelMemN n)) : ℝ :=
  ∑ x : HashDomain, if s.1.1 x ≠ none then blkCntSN P s.2.2.1 x else 0

variable (P) in
open scoped Classical in
/-- `Ψ` with the cell `z` counted as recorded. -/
noncomputable def revPotAtSN (z : HashDomain) (s : RRegSN n (SelMemN n)) : ℝ :=
  ∑ x : HashDomain, if x = z then blkCntSN P s.2.2.1 z else
    if s.1.1 x ≠ none then blkCntSN P s.2.2.1 x else 0

variable (P) in
open scoped Classical in
/-- The recorded trial cells of user `k.1`'s key `k.2`. -/
noncomputable def blkRecSN (k : Fin n × Key) (s : RRegSN n (SelMemN n)) : ℕ :=
  (Finset.univ.filter fun x : HashDomain ↦ s.1.1 x ≠ none ∧ IsBlkSN P k x).card

variable (P) in
open scoped Classical in
/-- The recorded trial-`J` cells of user `k.1`'s key `k.2`. -/
noncomputable def blkRecJSN (k : Fin n × Key) (J : ℕ) (s : RRegSN n (SelMemN n)) : ℕ :=
  (Finset.univ.filter fun x : HashDomain ↦ s.1.1 x ≠ none ∧ IsBlkJSN P k J x).card

variable (P) in
open scoped Classical in
/-- **The drop of `Ψ` at a first reveal of `(k.1, vcoord (msgPos k.2))`**: the recorded trial
cells of `k`. -/
noncomputable def revDropSN (k : Fin n × Key) (s : RRegSN n (SelMemN n)) : ℝ :=
  if (k.1, vcoord (msgPos k.2)) ∈ s.2.2.1 then 0 else (blkRecSN P k s : ℝ)

open scoped Classical in
/-- **The trials split the recorded trial cells.** -/
theorem sum_blkRecJSN_le (k : Fin n × Key) (s : RRegSN n (SelMemN n)) :
    ∑ J : Fin encodingAttemptLimit, blkRecJSN P k J.val s ≤ blkRecSN P k s := by
  unfold blkRecJSN blkRecSN
  rw [← Finset.card_biUnion]
  · refine Finset.card_le_card fun x hx ↦ ?_
    obtain ⟨J, -, hx⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨-, hr, hb⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hr, J.val, J.isLt, hb⟩
  · intro J _ J' _ hne
    refine Finset.disjoint_left.2 fun x hx hx' ↦ hne (Fin.ext ?_)
    exact isBlkJSN_trial_unique J.isLt J'.isLt (Finset.mem_filter.1 hx).2.2
      (Finset.mem_filter.1 hx').2.2

theorem blkCntSN_nonneg (L : Finset (TPosN n)) (x : HashDomain) : 0 ≤ blkCntSN P L x :=
  Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> norm_num

theorem blkCntSN_le_one (hP : Function.Injective P) (L : Finset (TPosN n)) (x : HashDomain) :
    blkCntSN P L x ≤ 1 := by
  classical
  unfold blkCntSN
  by_cases h : ∃ k, IsBlkSN P k x
  · obtain ⟨k₀, hk₀⟩ := h
    rw [Finset.sum_eq_single k₀ (fun k _ hne ↦ ite_eq_right fun hc ↦
      hne (isBlkSN_unique hP hc.2 hk₀)) (fun h ↦ absurd (Finset.mem_univ _) h)]
    split_ifs <;> norm_num
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun k _ ↦ ite_eq_right fun hc ↦ h ⟨k, hc.2⟩)
      zero_le_one

theorem blkCntSN_eq_zero (hP : Function.Injective P) {L : Finset (TPosN n)} {k : Fin n × Key}
    {x : HashDomain} (hx : IsBlkSN P k x) (hL : (k.1, vcoord (msgPos k.2)) ∈ L) :
    blkCntSN P L x = 0 := by
  classical
  exact Finset.sum_eq_zero fun _ _ ↦ ite_eq_right fun hc ↦
    hc.1 (isBlkSN_unique hP hx hc.2 ▸ hL)

theorem revPotSN_nonneg (s : RRegSN n (SelMemN n)) : 0 ≤ revPotSN P s :=
  Finset.sum_nonneg fun x _ ↦ by
    split_ifs
    · exact blkCntSN_nonneg _ x
    · exact le_rfl

theorem revPotSN_congr {s s' : RRegSN n (SelMemN n)} (hk : s'.1.1 = s.1.1)
    (hl : s'.2.2.1 = s.2.2.1) : revPotSN P s' = revPotSN P s := by
  unfold revPotSN
  rw [hk, hl]

theorem revPotSN_le_revPotAtSN (z : HashDomain) (s : RRegSN n (SelMemN n)) :
    revPotSN P s ≤ revPotAtSN P z s :=
  Finset.sum_le_sum fun x _ ↦ by
    by_cases hx : x = z
    · subst hx
      rw [ite_eq_left rfl]
      split_ifs
      · exact le_rfl
      · exact blkCntSN_nonneg _ x
    · rw [ite_eq_right hx]

theorem revPotAtSN_eq (hP : Function.Injective P) {z : HashDomain} {k : Fin n × Key}
    (hz : IsBlkSN P k z) {s : RRegSN n (SelMemN n)} (hs : (k.1, vcoord (msgPos k.2)) ∈ s.2.2.1) :
    revPotAtSN P z s = revPotSN P s :=
  Finset.sum_congr rfl fun x _ ↦ by
    by_cases hx : x = z
    · subst hx
      rw [ite_eq_left rfl, blkCntSN_eq_zero hP hz hs]
      split_ifs <;> rfl
    · rw [ite_eq_right hx]

theorem revPotAtSN_congr (z : HashDomain) {s s' : RRegSN n (SelMemN n)}
    (hk : ∀ x, x ≠ z → s'.1.1 x = s.1.1 x) (hl : s'.2.2.1 = s.2.2.1) :
    revPotAtSN P z s' = revPotAtSN P z s :=
  Finset.sum_congr rfl fun x _ ↦ by
    rw [hl]
    by_cases hx : x = z
    · rw [ite_eq_left hx, ite_eq_left hx]
    · rw [ite_eq_right hx, ite_eq_right hx, hk x hx]

/-- **`Ψ` is one-cell Lipschitz** under distinct `PK.seed`s. -/
theorem oneCellLipschitz_revPotSN (hP : Function.Injective P) :
    OneCellLipschitz (X := PairOut) (Z := HashDomain) (M := Finset (TPosN n) × SelMemN n)
      (revPotSN P) where
  h D b z v := by
    classical
    set f : HashDomain → ℝ := fun x ↦ if D.1 x ≠ none then blkCntSN P b.2.1 x else 0
    set f' : HashDomain → ℝ := fun x ↦
      if Function.update D.1 z v x ≠ none then blkCntSN P b.2.1 x else 0
    have hd : ∑ x, (f' x - f x) = f' z - f z :=
      Finset.sum_eq_single z (fun x _ hx ↦ by simp [f, f', Function.update_of_ne hx])
        (fun h ↦ absurd (Finset.mem_univ z) h)
    have hf' : f' z ≤ 1 := by
      simp only [f']
      split_ifs
      · exact blkCntSN_le_one hP _ z
      · exact zero_le_one
    have hf : 0 ≤ f z := by
      simp only [f]
      split_ifs
      · exact blkCntSN_nonneg _ z
      · exact le_rfl
    show ∑ x, f' x ≤ ∑ x, f x + 1
    rw [Finset.sum_sub_distrib] at hd
    linarith
  k _ _ _ _ := le_of_eq_of_le (revPotSN_congr rfl rfl) (le_add_of_nonneg_right zero_le_one)
  k' _ _ _ _ := le_of_eq_of_le (revPotSN_congr rfl rfl) (le_add_of_nonneg_right zero_le_one)

/-- **A program does not raise `Ψ`**: it discards its cell from the databases. -/
theorem revPotSN_progMap_le (c : HwProg PairOut HashDomain) (s : RRegSN n (SelMemN n)) :
    revPotSN P (progMap c s) ≤ revPotSN P s := by
  obtain ⟨⟨dh, dk, dk'⟩, W, ⟨L, m⟩⟩ := s
  rcases c with ⟨z, w⟩ | ⟨x, w⟩ | ⟨x, w⟩
  · refine Finset.sum_le_sum fun y _ ↦ ?_
    show (if Function.update dh z none y ≠ none then blkCntSN P L y else 0) ≤
      if dh y ≠ none then blkCntSN P L y else 0
    by_cases hy : y = z
    · subst hy
      rw [Function.update_self, ite_eq_right (fun h ↦ h rfl)]
      split_ifs
      · exact blkCntSN_nonneg _ y
      · exact le_rfl
    · rw [Function.update_of_ne hy]
  · exact le_of_eq (revPotSN_congr rfl rfl)
  · exact le_of_eq (revPotSN_congr rfl rfl)

theorem blkCntSN_union_le (T T' : Finset (TPosN n)) (x : HashDomain) :
    blkCntSN P (T ∪ T') x ≤ blkCntSN P T x :=
  Finset.sum_le_sum fun k _ ↦ by
    by_cases h : (k.1, vcoord (msgPos k.2)) ∉ T ∪ T' ∧ IsBlkSN P k x
    · rw [ite_eq_left h, ite_eq_left ⟨fun hl ↦ h.1 (Finset.mem_union_left _ hl), h.2⟩]
    · rw [ite_eq_right h]
      split_ifs <;> norm_num

open scoped Classical in
theorem ind_add_blkCntSN_le {T : Finset (TPosN n)} {k : Fin n × Key}
    (hl : (k.1, vcoord (msgPos k.2)) ∉ T) (x : HashDomain) :
    (if IsBlkSN P k x then (1 : ℝ) else 0) +
        blkCntSN P (T ∪ atU k.1 {vcoord (msgPos k.2)}) x ≤ blkCntSN P T x := by
  classical
  unfold blkCntSN
  have h1 : (if IsBlkSN P k x then (1 : ℝ) else 0) =
      ∑ r : Fin n × Key, if r = k then
        (if (r.1, vcoord (msgPos r.2)) ∉ T ∧ IsBlkSN P r x then 1 else 0) else 0 := by
    rw [Finset.sum_ite_eq' Finset.univ k, ite_eq_left (Finset.mem_univ _)]
    by_cases hb : IsBlkSN P k x
    · rw [ite_eq_left hb, ite_eq_left ⟨hl, hb⟩]
    · rw [ite_eq_right hb, ite_eq_right fun h ↦ hb h.2]
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun r _ ↦ ?_
  by_cases hr : r = k
  · subst hr
    have h0 : ¬((r.1, vcoord (msgPos r.2)) ∉ T ∪ atU r.1 {vcoord (msgPos r.2)} ∧
        IsBlkSN P r x) :=
      fun h ↦ h.1 (Finset.mem_union_right _ (mk_mem_atU _ (Finset.mem_singleton_self _)))
    rw [ite_eq_left rfl, ite_eq_right h0, add_zero]
  · rw [ite_eq_right hr, zero_add]
    by_cases h : (r.1, vcoord (msgPos r.2)) ∉ T ∪ atU k.1 {vcoord (msgPos k.2)} ∧ IsBlkSN P r x
    · rw [ite_eq_left h, ite_eq_left ⟨fun hl' ↦ h.1 (Finset.mem_union_left _ hl'), h.2⟩]
    · rw [ite_eq_right h]
      split_ifs <;> norm_num

variable (P) in
/-- The drop at a record of `T`: a first reveal's recorded trial cells, nothing otherwise. -/
noncomputable def revDropOSN (T : Finset (TPosN n)) (s : RRegSN n (SelMemN n)) : ℝ :=
  match keyOfTSN T with
  | some k => revDropSN P k s
  | none => 0

theorem revDropOSN_of_some {T : Finset (TPosN n)} {k : Fin n × Key} (hT : keyOfTSN T = some k)
    (s : RRegSN n (SelMemN n)) : revDropOSN P T s = revDropSN P k s := by
  unfold revDropOSN
  rw [hT]

theorem revDropOSN_of_none {T : Finset (TPosN n)} (hT : keyOfTSN T = none)
    (s : RRegSN n (SelMemN n)) : revDropOSN P T s = 0 := by
  unfold revDropOSN
  rw [hT]

theorem revDropOSN_nonneg (T : Finset (TPosN n)) (s : RRegSN n (SelMemN n)) :
    0 ≤ revDropOSN P T s := by
  rcases hT : keyOfTSN T with _ | k
  · exact (revDropOSN_of_none hT s).symm.le
  · rw [revDropOSN_of_some hT]
    unfold revDropSN
    split_ifs
    · exact le_rfl
    · exact Nat.cast_nonneg _

/-- **A record drops `Ψ` by at least the first-reveal drop.** -/
theorem revDropOSN_add_le (T : Finset (TPosN n)) (s : RRegSN n (SelMemN n)) :
    revDropOSN P T s + revPotSN P (recMapU T s) ≤ revPotSN P s := by
  classical
  obtain ⟨D, W, ⟨L, m⟩⟩ := s
  have hle : revPotSN P (recMapU T (D, W, (L, m))) ≤ revPotSN P (D, W, (L, m)) :=
    Finset.sum_le_sum fun y _ ↦ by
      show (if D.1 y ≠ none then blkCntSN P (L ∪ T) y else 0) ≤
        if D.1 y ≠ none then blkCntSN P L y else 0
      split_ifs
      · exact blkCntSN_union_le L T y
      · exact le_rfl
  rcases ho : keyOfTSN T with _ | ⟨i, K⟩
  · rw [revDropOSN_of_none ho, zero_add]
    exact hle
  · rw [revDropOSN_of_some ho]
    unfold revDropSN
    split_ifs with hl
    · rw [zero_add]
      exact hle
    · have hT : T = atU i {vcoord (msgPos K)} := (keyOfTSN_spec ho).2
      subst hT
      show ((Finset.univ.filter fun y : HashDomain ↦ D.1 y ≠ none ∧
          IsBlkSN P (i, K) y).card : ℝ) +
        ∑ y : HashDomain, (if D.1 y ≠ none then
          blkCntSN P (L ∪ atU i {vcoord (msgPos K)}) y else 0) ≤
          ∑ y : HashDomain, if D.1 y ≠ none then blkCntSN P L y else 0
      rw [Finset.card_filter, Nat.cast_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun y _ ↦ ?_
      by_cases hD : D.1 y ≠ none
      · rw [ite_eq_left hD, ite_eq_left hD]
        have h := ind_add_blkCntSN_le (P := P) (k := (i, K)) hl y
        by_cases hb : IsBlkSN P (i, K) y
        · rw [ite_eq_left hb] at h
          rw [ite_eq_left ⟨hD, hb⟩, Nat.cast_one]
          exact h
        · rw [ite_eq_right hb] at h
          rw [ite_eq_right fun h' ↦ hb h'.2, Nat.cast_zero]
          exact h
      · rw [ite_eq_right hD, ite_eq_right hD, ite_eq_right fun h ↦ hD h.1, Nat.cast_zero,
          zero_add]

variable (P) in
/-- **The drops of `Ψ` at the record ports.** -/
noncomputable def dropQWSN : ∀ i : (RSpecSN n (SelMemN n)).Port,
    Matrix ((RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n))
      ((RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n)) ℂ → ℝ≥0∞
  | .inr T, σ => ENNReal.ofReal
      (∑ q : Unit × RRegSN n (SelMemN n), revDropOSN P T q.2 * (σ q q).re)
  | _, _ => 0

/-- The traces at the sponge ports. -/
noncomputable def spongeTrSN (i : (RSpecSN n (SelMemN n)).Port)
    (σ : Matrix ((RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n))
      ((RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n)) ℂ) : ℝ≥0∞ :=
  ((if extCls PairOut HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n)) i then 0 else 1 :
    ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re

/-! ## `Ψ` along the prefix -/

/-- **The label invariant of the searches**: in the search of `(i, K)`, its coordinate is
revealed. -/
def labInvSN : ModeSN n → Set (RRegSN n (SelMemN n))
  | .rest _ => Set.univ
  | .grd _ i K _ _ => {s | (i, vcoord (msgPos K)) ∈ s.2.2.1}

/-- **The allowed calls keep the label invariant.** -/
theorem labInvSN_step (θ : TValsN n) (μ : ModeSN n) (i : (RSpecSN n (SelMemN n)).Port)
    (r : (RSpecSN n (SelMemN n)).Result i)
    (σ : Matrix ((RSpecSN n (SelMemN n)).In i × (runtimeR (m0SN (n := n))).D)
      ((RSpecSN n (SelMemN n)).In i × (runtimeR (m0SN (n := n))).D) ℂ)
    (hok : srchOkZSN P μ i)
    (hσ : QuerySupportedOn (fun m : (RSpecSN n (SelMemN n)).In i × (runtimeR (m0SN (n := n))).D ↦
      m.2) (labInvSN μ) σ) :
    QuerySupportedOn (fun m : (RSpecSN n (SelMemN n)).Out i × (runtimeR (m0SN (n := n))).D ↦ m.2)
      (labInvSN (srchNxZSN θ μ i r)) (((runtimeR (m0SN (n := n))).step i).branch r σ) := by
  rcases i with ((i | c) | c) | T
  · exact querySupportedOn_univ _ _
  · rcases μ with ks | ⟨ks, i', K, m, j⟩
    · exact hok.elim
    have hb : ((runtimeR (m0SN (n := n))).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty PairOut HashDomain)
        m0SN c r) σ
    rw [hb]
    obtain ⟨-, rfl⟩ := hok
    refine hσ.conj fun q' q hK hq ↦ ?_
    obtain ⟨-, hK'⟩ := one_kronecker_ne_zero (a := q.1) (a' := q'.1) (b := q.2) (b' := q'.2) hK
    obtain ⟨-, -, hm, hm'⟩ := cw_readKrausH_ne_zero (trialCell (P i') K m j)
      (trialUpdSN (trialCell (P i') K m j) (i', K)) r hK'
    have hl : q'.2.2.2.1 = q.2.2.2.1 := by rw [hm', hm]; rfl
    show q'.2 ∈ labInvSN (decNxSN ks i' K m j
      (TargetSum.decodeDigest (truncateHash (r.1.getD 0).1)))
    generalize TargetSum.decodeDigest (truncateHash (r.1.getD 0).1) = dd
    cases dd with
    | some _ => trivial
    | none =>
      show (i', vcoord (msgPos K)) ∈ q'.2.2.2.1
      rw [hl]
      exact hq
  · exact querySupportedOn_univ _ _
  · rcases ho : keyOfTSN T with _ | ⟨i', K⟩
    · have hn : srchNxZSN θ μ (.inr T) r = .rest μ.ks := revNxSN_none μ ho _
      rw [hn]
      exact querySupportedOn_univ _ _
    · have hn : srchNxZSN θ μ (.inr T) r =
          .grd (insert (i', K) μ.ks) i' K ((tabOf (userOf θ i')).valuePos (msgPos K)) 0 := by
        show revNxSN μ T _ = _
        unfold revNxSN
        rw [ho]
      have hT : T = atU i' {vcoord (msgPos K)} := (keyOfTSN_spec ho).2
      rw [hn]
      refine QuerySupportedOn.conj (K := recKraus (X := PairOut) (Z := HashDomain) T r) hσ
        fun q' q hK _ ↦ ?_
      rw [eq_of_recKraus_ne_zero (u := q.1) (u' := q'.1) (s := q.2) (s' := q'.2) hK]
      show (i', vcoord (msgPos K)) ∈ q.2.2.2.1 ∪ T
      rw [hT]
      exact Finset.mem_union_right _ (mk_mem_atU _ (Finset.mem_singleton_self _))

/-- **The step of `Ψ`**: a sponge call raises it by at most its trace; a search's read, a program
and a record do not raise it, a record lowering it by the first-reveal drop. -/
theorem revPotSN_step (hP : Function.Injective P) (i : (RSpecSN n (SelMemN n)).Port)
    (σ : Matrix ((RSpecSN n (SelMemN n)).In i × (runtimeR (m0SN (n := n))).D)
      ((RSpecSN n (SelMemN n)).In i × (runtimeR (m0SN (n := n))).D) ℂ) (hσ : σ.PosSemidef)
    (hI : ∃ μ, srchOkZSN P μ i ∧ QuerySupportedOn
      (fun m : (RSpecSN n (SelMemN n)).In i × (runtimeR (m0SN (n := n))).D ↦ m.2)
      (labInvSN μ) σ) :
    dropQWSN P i σ + ∑' r, potential (diagPot fun s ↦ √(revPotSN P s))
        (((runtimeR (m0SN (n := n))).step i).branch r σ) ≤
      potential (diagPot fun s ↦ √(revPotSN P s)) σ + spongeTrSN i σ := by
  have hφ0 : ∀ s, 0 ≤ revPotSN P s := revPotSN_nonneg
  rcases i with ((p | c) | c) | T
  · have hb : ∀ r : Unit, ((runtimeR (m0SN (n := n))).step (.inl (.inl (.inl p)))).branch r σ =
        MatrixMap.conj ((spongeHardwired PairOut HashDomain (hwEmpty PairOut HashDomain)
          (m0SN (n := n))).U p) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty PairOut HashDomain)
        m0SN p r) σ
    have hc : spongeTrSN (.inl (.inl (.inl p))) σ = ENNReal.ofReal σ.trace.re := by
      simp [spongeTrSN, extCls, hwCls]
      rfl
    rw [hc]
    show 0 + _ ≤ _
    rw [zero_add]
    exact (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans
      (tsum_potential_sponge_le hφ0 (oneCellLipschitz_revPotSN hP)
        (hwEmpty PairOut HashDomain) m0SN p hσ)
  · obtain ⟨μ, hok, hs⟩ := hI
    have hb : ∀ r, ((runtimeR (m0SN (n := n))).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty PairOut HashDomain)
        m0SN c r) σ
    have hc : spongeTrSN (.inl (.inl (.inr c))) σ = 0 := by
      simp [spongeTrSN, extCls, hwCls]
    rw [hc, add_zero]
    show 0 + _ ≤ _
    rw [zero_add]
    refine (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans ?_
    show ∑' r : c.Result, potential (diagPot fun s ↦ √(revPotSN P s))
      (MatrixMap.conj (hwReadKraus c r) σ) ≤ _
    rcases μ with ks | ⟨ks, i', K, m, j⟩
    · exact hok.elim
    obtain ⟨hj, rfl⟩ := hok
    set z := trialCell (P i') K m j
    refine tsum_potential_le_of_keep (fun r ↦ hwReadKraus (trialReadSN z (i', K)) r)
      (sum_hwReadKraus _) hφ0 (revPotSN_le_revPotAtSN z) (fun r a a' h ↦ ?_) hσ
      (fun q hq ↦ ?_)
    · obtain ⟨-, hK'⟩ := one_kronecker_ne_zero (a := a.1) (a' := a'.1) (b := a.2) (b' := a'.2) h
      obtain ⟨-, -, hm, hm'⟩ := cw_readKrausH_ne_zero z (trialUpdSN z (i', K)) r hK'
      obtain ⟨-, -, hR⟩ := cw_clsKraus_ne_zero hK'
      rw [kroneckerMap_apply] at hR
      exact revPotAtSN_congr _ (fun x hx ↦ cellRead_apply_ne_zero (left_ne_zero_of_mul hR) x hx)
        (by rw [hm', hm]; rfl)
    · by_cases hK : InRangeU K
      · exact (revPotAtSN_eq hP (show IsBlkSN P (i', K) z from ⟨j, hj, hK, m, rfl⟩)
          (hs q q hq).1).symm
      · refine Finset.sum_congr rfl fun x _ ↦ ?_
        by_cases hxz : x = z
        · subst hxz
          have h0 : blkCntSN P q.2.2.2.1 z = 0 := by
            classical
            refine Finset.sum_eq_zero fun k _ ↦ ite_eq_right fun hc ↦ ?_
            obtain ⟨J, -, hK'', m', he⟩ := hc.2
            exact hK ((trialCell_seed_keyU he).2 ▸ hK'')
          rw [ite_eq_left rfl, h0]
          split_ifs <;> rfl
        · rw [ite_eq_right hxz]
  · have hb : ∀ r, ((runtimeR (m0SN (n := n))).step (.inl (.inr c))).branch r σ =
        MatrixMap.conj (hwProgKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty PairOut HashDomain)
        m0SN c r) σ
    have hc : spongeTrSN (.inl (.inr c)) σ = 0 := by
      simp [spongeTrSN, extCls, hwCls]
    rw [hc, add_zero]
    show 0 + _ ≤ _
    rw [zero_add]
    refine (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans ?_
    refine (le_of_eq (tsum_potential_prog_eq hφ0 c hσ)).trans ?_
    refine le_of_le_of_eq ?_ (potential_diagPot_sqrt hφ0 σ).symm
    refine ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun q _ ↦ ?_)
    exact mul_le_mul_of_nonneg_right (revPotSN_progMap_le c q.2)
      (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  · have hc : spongeTrSN (.inr T) σ = 0 := by
      simp [spongeTrSN, extCls]
    rw [hc, add_zero]
    show ENNReal.ofReal (∑ q : Unit × RRegSN n (SelMemN n), revDropOSN P T q.2 * (σ q q).re) +
      ∑' m, potential (diagPot fun s ↦ √(revPotSN P s))
        (MatrixMap.conj (recKraus (X := PairOut) (Z := HashDomain) T m) σ) ≤ _
    rw [tsum_potential_rec_eqU hφ0 T hσ]
    refine le_of_le_of_eq ?_ (potential_diagPot_sqrt hφ0 σ).symm
    have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    have h1 : 0 ≤ ∑ q : Unit × RRegSN n (SelMemN n), revDropOSN P T q.2 * (σ q q).re :=
      Finset.sum_nonneg fun q _ ↦ mul_nonneg (revDropOSN_nonneg _ _) (hre q)
    have h2 : 0 ≤ ∑ q : Unit × RRegSN n (SelMemN n), revPotSN P (recMapU T q.2) * (σ q q).re :=
      Finset.sum_nonneg fun q _ ↦ mul_nonneg (hφ0 _) (hre q)
    refine (ENNReal.ofReal_add h1 h2).symm.trans_le (ENNReal.ofReal_le_ofReal ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (revDropOSN_add_le T q.2) (hre q)

/-- **The first-reveal drops of `Ψ` along a moded run**: at most the sponge charge, under distinct
`PK.seed`s (the potential starts at `0`). -/
theorem totalWeight_dropQWSN_le {Ω : QReg → Type} (hP : Function.Injective P) (θ : TValsN n)
    {fin : (Σ u, Ω u) → ModeSN n → Prop}
    (x : QuantumComp LocalSig.instruments.{0} (RSpecSN n (SelMemN n)) Ω (QReg.of Unit))
    (hx : ModedP (srchOkZSN P) (srchNxZSN θ) fin (.rest ∅) x) {q : ℕ}
    (hq : IFreeM.IsChargeBound x (portCharge fun i ↦
      if extCls PairOut HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n)) i then 0 else 1)
      q) :
    (runtimeR (m0SN (n := n))).totalWeight .instruments (dropQWSN P) x initQSN ≤ q := by
  have hφ0 : ∀ s, 0 ≤ revPotSN P s := revPotSN_nonneg
  have hfa := forallQueries_of_modedP (runtimeR (m0SN (n := n))) .instruments labInvSN
    (fun μ i r σ hok h ↦ labInvSN_step θ μ i r σ hok h) x (.rest ∅) hx (ρ := initQSN)
    (querySupportedOn_univ _ _)
  have h := totalWeight_le_potential_of_forallQueries (runtimeR (m0SN (n := n))) .instruments
    (diagPot fun s ↦ √(revPotSN P s)) _
    (fun i σ ↦ ∃ μ, srchOkZSN P μ i ∧ QuerySupportedOn
      (fun m : (RSpecSN n (SelMemN n)).In i × (runtimeR (m0SN (n := n))).D ↦ m.2)
      (labInvSN μ) σ)
    (fun i E σ hP' ↦ by
      obtain ⟨μ, hok, hs⟩ := hP'
      exact ⟨μ, hok, querySupportedOn_traceRight hs⟩)
    (dropQWSN P) spongeTrSN (fun i σ hσ hI ↦ revPotSN_step hP i σ hσ hI) x initQSN_posSemidef
    hfa
  have h0 : potential (diagPot fun s ↦ √(revPotSN P s)) (initQSN (n := n)) = 0 := by
    unfold initQSN initU
    rw [potential_basis_init m0SN hφ0 ()]
    refine (congrArg ENNReal.ofReal (Finset.sum_eq_zero fun y _ ↦ ite_eq_right fun h ↦
      h rfl)).trans ENNReal.ofReal_zero
  refine h.trans ((add_le_add (le_of_eq h0) le_rfl).trans ?_)
  rw [zero_add]
  refine (totalWeight_chargeTrace_le (runtimeR (m0SN (n := n))) .instruments _ x hq
    initQSN_posSemidef).trans ?_
  calc (q : ℝ≥0∞) * ENNReal.ofReal (initQSN (n := n)).trace.re ≤ q * 1 := by
        gcongr
        exact ofReal_trace_initQSN_le_one
    _ = q := mul_one _

/-! ## The first reveals, against `Ψ` -/

theorem pDistinct_iff_parQSN (θ : TValsN n) :
    PDistinct (tabOfN θ) ↔ Function.Injective (parQSN θ) :=
  Iff.rfl

/-- **A key's coordinate holds no `PK.seed`.** -/
theorem parQSN_update_msgPos (θ : TValsN n) (i : Fin n) {K : Key} (hK : InRangeU K)
    (d : TVal (vcoord (msgPos K))) :
    parQSN (Function.update θ (i, vcoord (msgPos K)) d) = parQSN θ :=
  funext fun j ↦ by
    by_cases hj : j = i
    · subst hj
      show (tabOf (userOf (Function.update θ (j, vcoord (msgPos K)) d) j)).publicSeed =
        (tabOf (userOf θ j)).publicSeed
      rw [userOf_update_self]
      exact publicSeed_tabOf_congr (pairAt_update_neU (fun h ↦ notMcU_seedC K hK h) d)
    · show (tabOf (userOf (Function.update θ (i, vcoord (msgPos K)) d) j)).publicSeed =
        (tabOf (userOf θ j)).publicSeed
      rw [userOf_update_of_ne θ hj]

/-- **The values of user `i`'s key coordinate whose trial-`J` cell is recorded** are at most
`2^-128` of the pairs per recorded trial-`J` cell of `(i, K)`. -/
theorem card_firstFSN_le {i : Fin n} {K : Key} (hK : InRangeU K) (J : Fin encodingAttemptLimit)
    (s : RRegSN n (SelMemN n)) (v : TValsN n) :
    ((Finset.univ.filter fun d : TVal (vcoord (msgPos K)) ↦
        s.1.1 (trialCell (parQSN v i) K ((tabOf (Function.update (userOf v i)
          (vcoord (msgPos K)) d)).valuePos (msgPos K)) J) ≠ none).card : ℝ≥0∞) *
        (Fintype.card (TVal (vcoord (msgPos K))) : ℝ≥0∞)⁻¹ ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * blkRecJSN (parQSN v) (i, K) J s := by
  have hval : ∀ d : TVal (vcoord (msgPos K)),
      (tabOf (Function.update (userOf v i) (vcoord (msgPos K)) d)).valuePos (msgPos K) =
        pairDigest (pairAt (Function.update (userOf v i) (vcoord (msgPos K)) d)
          (vcoord (msgPos K))) :=
    fun d ↦ valuePos_msgPosU hK _
  simp only [hval]
  set P₀ := parQSN v i
  set M := Finset.univ.filter fun m : Digest ↦ s.1.1 (trialCell P₀ K m J) ≠ none
  have hM : M.card ≤ blkRecJSN (parQSN v) (i, K) J s := by
    classical
    unfold blkRecJSN
    exact card_filter_le_of_injective (f := fun m : Digest ↦ trialCell P₀ K m J)
      (fun m m' h ↦ (trialCell_injU J.isLt J.isLt h).1) _ _ fun m hm ↦ ⟨hm, hK, m, rfl⟩
  obtain ⟨p, hp⟩ := msgPos_isValU hK
  generalize vcoord (msgPos K) = t at hp ⊢
  subst hp
  have hF : (Finset.univ.filter fun d : TVal (SPos.val p) ↦ s.1.1 (trialCell P₀ K
      (pairDigest (pairAt (Function.update (userOf v i) (SPos.val p) d) (SPos.val p))) J) ≠
        none).card ≤ M.card * (2 ^ 128 * 2 ^ 256) := by
    have hsub : (Finset.univ.filter fun d : TVal (SPos.val p) ↦ s.1.1 (trialCell P₀ K
        (pairDigest (pairAt (Function.update (userOf v i) (SPos.val p) d) (SPos.val p))) J) ≠
          none) ⊆
        M.biUnion fun m ↦ @Finset.filter PairOut (fun ω ↦ pairDigest ω = m)
          (fun ω ↦ instDecidableEqBitVec (pairDigest ω) m) Finset.univ := by
      intro d hd
      have hd' : s.1.1 (trialCell P₀ K (pairDigest d) J) ≠ none := by
        have h := (Finset.mem_filter.1 hd).2
        simpa only [pairAt, Function.update_self] using h
      refine Finset.mem_biUnion.2 ⟨pairDigest d, Finset.mem_filter.2 ⟨Finset.mem_univ _, hd'⟩,
        ?_⟩
      exact (@Finset.mem_filter _ (fun ω : PairOut ↦ pairDigest ω = pairDigest d)
        (fun ω ↦ instDecidableEqBitVec (pairDigest ω) (pairDigest d)) _ _).2
        ⟨Finset.mem_univ _, rfl⟩
    refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
    exact (Finset.sum_le_card_nsmul M _ (2 ^ 128 * 2 ^ 256) fun m _ ↦
      card_fiber_pairDigest_le m).trans_eq (smul_eq_mul _ _)
  have hc : (Fintype.card (TVal (SPos.val p)) : ℝ≥0∞) = Fintype.card PairOut := rfl
  rw [hc]
  calc _ ≤ ((M.card * (2 ^ 128 * 2 ^ 256) : ℕ) : ℝ≥0∞) * (Fintype.card PairOut : ℝ≥0∞)⁻¹ :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hF) zero_le
    _ = (M.card : ℝ≥0∞) * (((2 ^ 128 * 2 ^ 256 : ℕ) : ℝ≥0∞) / Fintype.card PairOut) := by
        rw [Nat.cast_mul, mul_assoc, ENNReal.div_eq_inv_mul, mul_comm (Fintype.card PairOut :
          ℝ≥0∞)⁻¹]
    _ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ * blkRecJSN (parQSN v) (i, K) J s := by
        rw [pairFiber_div_card, mul_comm]
        exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hM) zero_le

/-- The first-run states of trial `J` at the reveals, at the hidden values `θ`, on distinct
`PK.seed`s. -/
def firstSetSN (θ : TValsN n) (J : ℕ) :
    ∀ i : (RSpecSN n (SelMemN n)).Port,
      Set ((RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n))
  | .inr T => match keyOfTSN T with
    | some k => {q | PDistinct (tabOfN θ) ∧ (k.1, vcoord (msgPos k.2)) ∉ q.2.2.2.1 ∧
        q.2.1.1 (trialCell (parQSN θ k.1) k.2
          ((tabOf (userOf θ k.1)).valuePos (msgPos k.2)) J) ≠ none}
    | none => ∅
  | _ => ∅

/-- The source of a reveal: its key's coordinate, if unrevealed. -/
noncomputable def firstSrcSN : ∀ i : (RSpecSN n (SelMemN n)).Port,
    (RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n) → Finset (TPosN n)
  | .inr T, q => match keyOfTSN T with
    | some k => if (k.1, vcoord (msgPos k.2)) ∈ q.2.2.2.1 then ∅ else {(k.1, vcoord (msgPos k.2))}
    | none => ∅
  | _, _ => ∅

open scoped Classical in
/-- The source values of trial `J` at a reveal: the pairs at the key's coordinate whose trial-`J`
cell is recorded, on distinct `PK.seed`s (the other coordinates read off the hidden values). -/
noncomputable def firstFSN (J : ℕ) : ∀ i : (RSpecSN n (SelMemN n)).Port,
    (RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n) → (s : TPosN n) → TValsN n →
      Finset (TValN n s)
  | .inr T, q => fun s v ↦ match keyOfTSN T with
    | some k => Finset.univ.filter fun d : TValN n s ↦
        PDistinct (tabOfN (Function.update v s d)) ∧
          q.2.1.1 (trialCell (parQSN (Function.update v s d) k.1) k.2
            ((tabOf (userOf (Function.update v s d) k.1)).valuePos (msgPos k.2)) J) ≠ none
    | none => ∅
  | _, _ => fun _ _ ↦ ∅

/-- The states of a reveal at which the cell `x` is a recorded trial-`J` cell of the revealed
unrevealed key, on distinct `PK.seed`s. -/
def firstBSN (J : ℕ) (v : TValsN n) (x : HashDomain) :
    ∀ i : (RSpecSN n (SelMemN n)).Port,
      Set ((RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n))
  | .inr T => match keyOfTSN T with
    | some k => {q | PDistinct (tabOfN v) ∧ (k.1, vcoord (msgPos k.2)) ∉ q.2.2.2.1 ∧
        q.2.1.1 x ≠ none ∧ IsBlkJSN (parQSN v) k J x}
    | none => ∅
  | _ => ∅

/-- The weight per state of a reveal at trial `J`: its key's recorded trial-`J` cells over
`2^128`, if first, on distinct `PK.seed`s. -/
noncomputable def firstKSN (J : ℕ) (v : TValsN n) (i : (RSpecSN n (SelMemN n)).Port)
    (q : (RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n)) : ℝ≥0∞ :=
  (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑ x : HashDomain, (firstBSN J v x i).indicator 1 q

theorem firstBSN_of_some {T : Finset (TPosN n)} {k : Fin n × Key} (hT : keyOfTSN T = some k)
    (J : ℕ) (v : TValsN n) (x : HashDomain) :
    firstBSN J v x (.inr T) = {q : (RSpecSN n (SelMemN n)).In (.inr T) × RRegSN n (SelMemN n) |
      PDistinct (tabOfN v) ∧ (k.1, vcoord (msgPos k.2)) ∉ q.2.2.2.1 ∧ q.2.1.1 x ≠ none ∧
        IsBlkJSN (parQSN v) k J x} := by
  dsimp only [firstBSN]
  rw [hT]

theorem firstBSN_of_none {T : Finset (TPosN n)} (hT : keyOfTSN T = none) (J : ℕ)
    (v : TValsN n) (x : HashDomain) : firstBSN J v x (.inr T) = ∅ := by
  dsimp only [firstBSN]
  rw [hT]

open scoped Classical in
/-- **The count of a first reveal's states**: the recorded trial-`J` cells of the key. -/
theorem sum_indicator_firstBSN {T : Finset (TPosN n)} {k : Fin n × Key}
    (hT : keyOfTSN T = some k) (J : ℕ) (v : TValsN n)
    (q : (RSpecSN n (SelMemN n)).In (.inr T) × RRegSN n (SelMemN n)) :
    ∑ x : HashDomain, (firstBSN J v x (.inr T)).indicator 1 q =
      if PDistinct (tabOfN v) ∧ (k.1, vcoord (msgPos k.2)) ∉ q.2.2.2.1 then
        (blkRecJSN (parQSN v) k J q.2 : ℝ≥0∞) else 0 := by
  simp only [firstBSN_of_some hT]
  by_cases h : PDistinct (tabOfN v) ∧ (k.1, vcoord (msgPos k.2)) ∉ q.2.2.2.1
  · rw [ite_eq_left h]
    unfold blkRecJSN
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases hx : q.2.1.1 x ≠ none ∧ IsBlkJSN (parQSN v) k J x
    · rw [Set.indicator_of_mem (show q ∈ {q : (RSpecSN n (SelMemN n)).In (.inr T) ×
          RRegSN n (SelMemN n) | PDistinct (tabOfN v) ∧ (k.1, vcoord (msgPos k.2)) ∉ q.2.2.2.1 ∧
            q.2.1.1 x ≠ none ∧ IsBlkJSN (parQSN v) k J x} from ⟨h.1, h.2, hx⟩), ite_eq_left hx,
        Pi.one_apply, Nat.cast_one]
    · rw [Set.indicator_of_notMem fun hm ↦ hx hm.2.2, ite_eq_right hx, Nat.cast_zero]
  · rw [ite_eq_right h]
    exact Finset.sum_eq_zero fun x _ ↦
      Set.indicator_of_notMem (fun hm ↦ h ⟨hm.1, hm.2.1⟩) _

theorem firstKSN_eq_zero_of {J : ℕ} {v : TValsN n} {i : (RSpecSN n (SelMemN n)).Port}
    {q : (RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n)}
    (h : ∀ x, q ∉ firstBSN J v x i) : firstKSN J v i q = 0 := by
  unfold firstKSN
  rw [Finset.sum_eq_zero fun x _ ↦ Set.indicator_of_notMem (h x) _, mul_zero]

/-- **The trials' weights of a record port** are at most `2^-128` times its first-reveal drop. -/
theorem sum_kWt_firstKSN_le (v : TValsN n) (i : (RSpecSN n (SelMemN n)).Port)
    (σ : Matrix ((RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n))
      ((RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n)) ℂ) (hσ : σ.PosSemidef) :
    ∑ J : Fin encodingAttemptLimit, kWt (firstKSN J.val v i) σ ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * dropQWSN (parQSN v) i σ := by
  rcases i with ((p | c) | c) | T
  · refine le_of_eq_of_le (Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦ ?_) zero_le
    exact mul_eq_zero_of_left (firstKSN_eq_zero_of (i := .inl (.inl (.inl p))) fun _ h ↦ h) _
  · refine le_of_eq_of_le (Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦ ?_) zero_le
    exact mul_eq_zero_of_left (firstKSN_eq_zero_of (i := .inl (.inl (.inr c))) fun _ h ↦ h) _
  · refine le_of_eq_of_le (Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦ ?_) zero_le
    exact mul_eq_zero_of_left (firstKSN_eq_zero_of (i := .inl (.inr c)) fun _ h ↦ h) _
  · have hre : ∀ q : (RSpecSN n (SelMemN n)).In (.inr T) × RRegSN n (SelMemN n),
        0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    show ∑ J : Fin encodingAttemptLimit, ∑ q, firstKSN J.val v (.inr T) q *
        ENNReal.ofReal (σ q q).re ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ *
      ENNReal.ofReal (∑ q, revDropOSN (parQSN v) T q.2 * (σ q q).re)
    rw [ENNReal.ofReal_sum_of_nonneg fun q _ ↦ mul_nonneg (revDropOSN_nonneg _ _) (hre q),
      Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [← Finset.sum_mul, ENNReal.ofReal_mul (revDropOSN_nonneg _ _), ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    simp only [firstKSN, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    rcases hT : keyOfTSN T with _ | k
    · refine le_of_eq_of_le (Finset.sum_eq_zero fun J _ ↦ Finset.sum_eq_zero fun x _ ↦ ?_)
        zero_le
      rw [firstBSN_of_none hT]
      exact Set.indicator_of_notMem (Set.notMem_empty q) _
    · classical
      simp only [sum_indicator_firstBSN hT]
      rw [revDropOSN_of_some hT]
      by_cases h : PDistinct (tabOfN v) ∧ (k.1, vcoord (msgPos k.2)) ∉ q.2.2.2.1
      · simp only [ite_eq_left h]
        unfold revDropSN
        rw [ite_eq_right h.2, ENNReal.ofReal_natCast, ← Nat.cast_sum]
        exact Nat.cast_le.mpr (sum_blkRecJSN_le k q.2)
      · simp only [ite_eq_right h, Finset.sum_const_zero]
        exact zero_le

/-- **The source values of a first reveal** against its weight. -/
theorem card_firstFSN_le_firstKSN {T : Finset (TPosN n)} {i : Fin n} {K : Key}
    (hT : keyOfTSN T = some (i, K)) (J : Fin encodingAttemptLimit) (v : TValsN n)
    (p : (RSpecSN n (SelMemN n)).In (.inr T) × RRegSN n (SelMemN n))
    (hl : (i, vcoord (msgPos K)) ∉ p.2.2.2.1) :
    ((firstFSN J.val (.inr T) p (i, vcoord (msgPos K)) v).card : ℝ≥0∞) *
        (Fintype.card (TValN n (i, vcoord (msgPos K))) : ℝ≥0∞)⁻¹ ≤
      firstKSN J.val v (.inr T) p := by
  classical
  have hK : InRangeU K := (keyOfTSN_spec hT).1
  have hF : firstFSN J.val (.inr T) p (i, vcoord (msgPos K)) v =
      Finset.univ.filter fun d : TValN n (i, vcoord (msgPos K)) ↦
        PDistinct (tabOfN (Function.update v (i, vcoord (msgPos K)) d)) ∧
          p.2.1.1 (trialCell (parQSN (Function.update v (i, vcoord (msgPos K)) d) i) K
            ((tabOf (userOf (Function.update v (i, vcoord (msgPos K)) d) i)).valuePos
              (msgPos K)) J.val) ≠ none := by
    dsimp only [firstFSN]
    rw [hT]
  have hk : firstKSN J.val v (.inr T) p = (2 ^ 128 : ℝ≥0∞)⁻¹ *
      (if PDistinct (tabOfN v) ∧ (i, vcoord (msgPos K)) ∉ p.2.2.2.1 then
        (blkRecJSN (parQSN v) (i, K) J.val p.2 : ℝ≥0∞) else 0) := by
    unfold firstKSN
    rw [sum_indicator_firstBSN hT]
  rw [hk]
  by_cases hv : PDistinct (tabOfN v)
  · rw [ite_eq_left ⟨hv, hl⟩]
    refine le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card
      (t := Finset.univ.filter fun d : TVal (vcoord (msgPos K)) ↦
        p.2.1.1 (trialCell (parQSN v i) K ((tabOf (Function.update (userOf v i)
          (vcoord (msgPos K)) d)).valuePos (msgPos K)) J) ≠ none) fun d hd ↦ ?_)) zero_le)
      (card_firstFSN_le hK J p.2 v)
    rw [hF] at hd
    obtain ⟨-, -, h2⟩ := Finset.mem_filter.1 hd
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [parQSN_update_msgPos v i hK, userOf_update_self] at h2
    exact h2
  · have h0 : firstFSN J.val (.inr T) p (i, vcoord (msgPos K)) v = ∅ := by
      rw [hF]
      refine Finset.eq_empty_of_forall_notMem fun d hd ↦ hv ?_
      have h1 := (Finset.mem_filter.1 hd).2.1
      rw [pDistinct_iff_parQSN, parQSN_update_msgPos v i hK] at h1
      exact h1
    rw [h0, Finset.card_empty, Nat.cast_zero, zero_mul]
    exact zero_le

/-- **The view lemma at the first reveals, trial by trial.** -/
theorem sum_totalWeight_firstSetSN_le (A : MuAdversaryS n) (J : Fin encodingAttemptLimit) :
    ∑ θ : TValsN n, (runtimeR (m0SN (n := n))).totalWeight .instruments
        (fun i ↦ diagMass (firstSetSN θ J.val i)) (prefixQSN (strPolN n) A θ) initQSN ≤
      ∑ θ : TValsN n, (runtimeR (m0SN (n := n))).totalWeight .instruments
        (fun i ↦ kWt (firstKSN J.val θ i)) (prefixQSN (strPolN n) A θ) initQSN := by
  classical
  refine sum_totalWeight_le_of_forallN (runtimeR (m0SN (n := n))) LocalSig.Interp.instruments
    _ _ _ _ fun j ↦ ?_
  have hview := (viewBy_runtimeR_of_disc LocalSig.Interp.instruments (m0SN (n := n))
    (prefixTN (SelMemN n) cwUpdN (strPolN n) A) ∅
    (disc_prefixTN (SelMemN n) cwUpdN (strPolN n) A ∅) (fun _ ↦ initQSN)
    (lazy_const _ initQSN) (fun _ ↦ suppAt_empty _ initQSN) j).viewByOn fun _ ↦ True
  refine sum_queryWeight_view_le_wtN (runtimeR (m0SN (n := n))) LocalSig.Interp.instruments
    (fun r ↦ r.2.2.1) (fun θ ↦ prefixQSN (strPolN n) A θ) (fun _ ↦ initQSN)
    (fun _ ↦ initQSN_posSemidef) j (fun _ ↦ True) hview (fun θ ↦ firstSetSN θ J.val)
    (fun _ _ h ↦ absurd trivial h) firstSrcSN (firstFSN J.val) (fun i p s v d ↦ ?_)
    (fun v i p hp ↦ ?_) (firstKSN J.val) (fun i p v ↦ ?_) (fun T v u h ↦ ?_)
  · rcases i with ((i | c) | c) | T
    · rfl
    · rfl
    · rfl
    · dsimp only [firstFSN]
      rcases keyOfTSN T with _ | k
      · rfl
      · simp only [Function.update_idem]
  · rcases i with ((i | c) | c) | T
    · exact hp.elim
    · exact hp.elim
    · exact hp.elim
    · rcases hT : keyOfTSN T with _ | ⟨i, K⟩
      · have h0 : firstSetSN v J.val (.inr T) = ∅ := by
          dsimp only [firstSetSN]
          rw [hT]
        exact absurd (h0 ▸ hp) (Set.notMem_empty p)
      · have h0 : firstSetSN v J.val (.inr T) =
            {q : (RSpecSN n (SelMemN n)).In (.inr T) × RRegSN n (SelMemN n) |
              PDistinct (tabOfN v) ∧ (i, vcoord (msgPos K)) ∉ q.2.2.2.1 ∧
                q.2.1.1 (trialCell (parQSN v i) K
                  ((tabOf (userOf v i)).valuePos (msgPos K)) J.val) ≠ none} := by
          dsimp only [firstSetSN]
          rw [hT]
        have hp' : p ∈ {q : (RSpecSN n (SelMemN n)).In (.inr T) × RRegSN n (SelMemN n) |
            PDistinct (tabOfN v) ∧ (i, vcoord (msgPos K)) ∉ q.2.2.2.1 ∧
              q.2.1.1 (trialCell (parQSN v i) K
                ((tabOf (userOf v i)).valuePos (msgPos K)) J.val) ≠ none} := h0 ▸ hp
        refine ⟨(i, vcoord (msgPos K)), ?_, hp'.2.1, ?_⟩
        · have hs : firstSrcSN (.inr T) p = if (i, vcoord (msgPos K)) ∈ p.2.2.2.1 then ∅
              else {(i, vcoord (msgPos K))} := by
            dsimp only [firstSrcSN]
            rw [hT]
          rw [hs, ite_eq_right hp'.2.1]
          exact Finset.mem_singleton_self _
        · have hF : firstFSN J.val (.inr T) p (i, vcoord (msgPos K)) v =
              Finset.univ.filter fun d : TValN n (i, vcoord (msgPos K)) ↦
                PDistinct (tabOfN (Function.update v (i, vcoord (msgPos K)) d)) ∧
                  p.2.1.1 (trialCell (parQSN (Function.update v (i, vcoord (msgPos K)) d) i) K
                    ((tabOf (userOf (Function.update v (i, vcoord (msgPos K)) d) i)).valuePos
                      (msgPos K)) J.val) ≠ none := by
            dsimp only [firstFSN]
            rw [hT]
          rw [hF, Finset.mem_filter, Function.update_eq_self]
          exact ⟨Finset.mem_univ _, hp'.1, hp'.2.2⟩
  · rcases i with ((i | c) | c) | T
    · exact le_of_eq_of_le Finset.sum_empty zero_le
    · exact le_of_eq_of_le Finset.sum_empty zero_le
    · exact le_of_eq_of_le Finset.sum_empty zero_le
    · rcases hT : keyOfTSN T with _ | ⟨i, K⟩
      · have hs : firstSrcSN (.inr T) p = ∅ := by
          dsimp only [firstSrcSN]
          rw [hT]
        rw [hs, Finset.sum_empty]
        exact zero_le
      · have hs : firstSrcSN (.inr T) p = if (i, vcoord (msgPos K)) ∈ p.2.2.2.1 then ∅
            else {(i, vcoord (msgPos K))} := by
          dsimp only [firstSrcSN]
          rw [hT]
        by_cases hl : (i, vcoord (msgPos K)) ∈ p.2.2.2.1
        · rw [hs, ite_eq_left hl, Finset.sum_empty]
          exact zero_le
        · rw [hs, ite_eq_right hl, Finset.sum_singleton]
          exact card_firstFSN_le_firstKSN hT J v p hl
  · exact queryWeight_kWt_viewN (runtimeR (m0SN (n := n))) LocalSig.Interp.instruments
      (fun r ↦ r.2.2.1) (fun θ ↦ prefixQSN (strPolN n) A θ) (fun _ ↦ initQSN) j (fun _ ↦ True)
      hview (2 ^ 128 : ℝ≥0∞)⁻¹ (fun x ↦ firstBSN J.val u x) (fun _ _ h ↦ absurd trivial h)
      (firstKSN J.val u) (fun _ _ ↦ rfl) T h

theorem firstKSN_of_not {v : TValsN n} (hv : ¬ PDistinct (tabOfN v)) (J : ℕ)
    (i : (RSpecSN n (SelMemN n)).Port) (q : (RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n)) :
    firstKSN J v i q = 0 := by
  refine firstKSN_eq_zero_of fun x h ↦ hv ?_
  rcases i with ((p | c) | c) | T
  · exact (h : False).elim
  · exact (h : False).elim
  · exact (h : False).elim
  · rcases hT : keyOfTSN T with _ | k
    · rw [firstBSN_of_none hT] at h
      exact h.elim
    · rw [firstBSN_of_some hT] at h
      exact h.1

/-- **The first-reveal weights of one hidden value**: at most `q / 2^128`. -/
theorem totalWeight_firstKSN_le (A : MuAdversaryS n) (θ : TValsN n) {q : ℕ}
    (hq : IFreeM.IsChargeBound (prefixQSN (strPolN n) A θ) (portCharge fun i ↦
      if extCls PairOut HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n)) i then 0 else 1)
      q) :
    (runtimeR (m0SN (n := n))).totalWeight .instruments
      (fun i σ ↦ ∑ J : Fin encodingAttemptLimit, kWt (firstKSN J.val θ i) σ)
      (prefixQSN (strPolN n) A θ) initQSN ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ * q := by
  by_cases hθ : PDistinct (tabOfN θ)
  · refine (totalWeight_le_totalWeight (runtimeR (m0SN (n := n))) .instruments
      (fun i σ hσ ↦ sum_kWt_firstKSN_le θ i σ hσ) _ initQSN_posSemidef).trans ?_
    rw [totalWeight_const_mul_weight (runtimeR (m0SN (n := n))) .instruments
      (2 ^ 128 : ℝ≥0∞)⁻¹ (dropQWSN (parQSN θ)) (prefixQSN (strPolN n) A θ) initQSN]
    exact mul_le_mul_of_nonneg_left (totalWeight_dropQWSN_le ((pDistinct_iff_parQSN θ).1 hθ) θ
      _ (modedP_prefixQSN (fun _ ↦ noVal_strPol) A θ) hq) zero_le
  · refine (totalWeight_le_totalWeight (runtimeR (m0SN (n := n))) .instruments
      (w' := fun _ _ ↦ 0) (fun i σ _ ↦ le_of_eq ?_) _ initQSN_posSemidef).trans ?_
    · exact Finset.sum_eq_zero fun J _ ↦ Finset.sum_eq_zero fun p _ ↦
        mul_eq_zero_of_left (firstKSN_of_not hθ J.val i p) _
    · exact (ENNReal.tsum_eq_zero.mpr fun j ↦ queryWeight_zero_weight _ _ _ _ j).trans_le zero_le

theorem firstQWSN_eq_sumSN {θ : TValsN n} (hθ : PDistinct (tabOfN θ))
    (i : (RSpecSN n (SelMemN n)).Port)
    (σ : Matrix ((RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n))
      ((RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n)) ℂ) :
    firstQWSN θ i σ = ∑ J : Fin encodingAttemptLimit, diagMass (firstSetSN θ J.val i) σ := by
  rcases i with ((p | c) | c) | T
  · exact (Finset.sum_eq_zero fun _ _ ↦ diagMass_empty_setU σ).symm
  · exact (Finset.sum_eq_zero fun _ _ ↦ diagMass_empty_setU σ).symm
  · exact (Finset.sum_eq_zero fun _ _ ↦ diagMass_empty_setU σ).symm
  · rcases hT : keyOfTSN T with _ | ⟨i, K⟩
    · have h1 : firstQWSN θ (.inr T) σ = 0 := by
        dsimp only [firstQWSN]
        rw [hT]
      have h2 : ∀ J : ℕ, firstSetSN θ J (.inr T) = ∅ := fun J ↦ by
        dsimp only [firstSetSN]
        rw [hT]
      rw [h1]
      simp only [h2]
      exact (Finset.sum_eq_zero fun _ _ ↦ diagMass_empty_setU σ).symm
    · have h1 : firstQWSN θ (.inr T) σ = ∑ J : Fin encodingAttemptLimit,
          diagMass {q : (RSpecSN n (SelMemN n)).In (.inr T) × RRegSN n (SelMemN n) |
            (i, vcoord (msgPos K)) ∉ q.2.2.2.1 ∧ q.2.1.1 (trialCell (parQSN θ i) K
              ((tabOf (userOf θ i)).valuePos (msgPos K)) J) ≠ none} σ := by
        dsimp only [firstQWSN]
        rw [hT]
        rfl
      have h2 : ∀ J : ℕ, firstSetSN θ J (.inr T) =
          {q : (RSpecSN n (SelMemN n)).In (.inr T) × RRegSN n (SelMemN n) |
            PDistinct (tabOfN θ) ∧ (i, vcoord (msgPos K)) ∉ q.2.2.2.1 ∧
              q.2.1.1 (trialCell (parQSN θ i) K
                ((tabOf (userOf θ i)).valuePos (msgPos K)) J) ≠ none} := fun J ↦ by
        dsimp only [firstSetSN]
        rw [hT]
      rw [h1]
      simp only [h2]
      exact Finset.sum_congr rfl fun J _ ↦ congrArg (fun S ↦ diagMass S σ)
        (Set.ext fun q ↦ ⟨fun h ↦ ⟨hθ, h⟩, fun h ↦ h.2⟩)

open scoped Classical in
/-- **The first-reveal charges of the hidden values `θ`, on distinct `PK.seed`s.** -/
noncomputable def firstMaskSN (A : MuAdversaryS n) (θ : TValsN n) : ℝ≥0∞ :=
  if PDistinct (tabOfN θ) then
    (runtimeR (m0SN (n := n))).totalWeight .instruments (firstQWSN θ)
      (prefixQSN (strPolN n) A θ) initQSN
  else 0

/-- **The first-reveal charges, summed over the hidden values** (on distinct `PK.seed`s): at most
`q / 2^128` per hidden value. -/
theorem sum_totalWeight_firstQWSN_le (A : MuAdversaryS n) {q : ℕ}
    (hq : ∀ θ, IFreeM.IsChargeBound (prefixQSN (strPolN n) A θ) (portCharge fun i ↦
      if extCls PairOut HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n)) i then 0 else 1)
      q) :
    ∑ θ : TValsN n, firstMaskSN A θ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ * q * Fintype.card (TValsN n) := by
  calc ∑ θ : TValsN n, firstMaskSN A θ
      ≤ ∑ θ : TValsN n, ∑ J : Fin encodingAttemptLimit,
          (runtimeR (m0SN (n := n))).totalWeight .instruments
            (fun i ↦ diagMass (firstSetSN θ J.val i)) (prefixQSN (strPolN n) A θ) initQSN :=
        Finset.sum_le_sum fun θ _ ↦ by
          classical
          unfold firstMaskSN
          split_ifs with hθ
          · exact le_of_eq ((congrArg (fun w ↦ (runtimeR (m0SN (n := n))).totalWeight
              .instruments w (prefixQSN (strPolN n) A θ) initQSN)
              (funext fun i ↦ funext fun σ ↦ firstQWSN_eq_sumSN hθ i σ)).trans
              (totalWeight_fintype_sum (runtimeR (m0SN (n := n))) .instruments
                (fun (J : Fin encodingAttemptLimit) i ↦ diagMass (firstSetSN θ J.val i))
                (prefixQSN (strPolN n) A θ) initQSN))
          · exact zero_le
    _ = ∑ J : Fin encodingAttemptLimit, ∑ θ : TValsN n,
          (runtimeR (m0SN (n := n))).totalWeight .instruments
            (fun i ↦ diagMass (firstSetSN θ J.val i)) (prefixQSN (strPolN n) A θ) initQSN :=
        Finset.sum_comm
    _ ≤ ∑ J : Fin encodingAttemptLimit, ∑ θ : TValsN n,
          (runtimeR (m0SN (n := n))).totalWeight .instruments
            (fun i ↦ kWt (firstKSN J.val θ i)) (prefixQSN (strPolN n) A θ) initQSN :=
        Finset.sum_le_sum fun J _ ↦ sum_totalWeight_firstSetSN_le A J
    _ = ∑ θ : TValsN n, (runtimeR (m0SN (n := n))).totalWeight .instruments
          (fun i σ ↦ ∑ J : Fin encodingAttemptLimit, kWt (firstKSN J.val θ i) σ)
            (prefixQSN (strPolN n) A θ) initQSN := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun θ _ ↦ (totalWeight_fintype_sum (runtimeR (m0SN (n := n)))
          .instruments (fun (J : Fin encodingAttemptLimit) i ↦ kWt (firstKSN J.val θ i))
          (prefixQSN (strPolN n) A θ) initQSN).symm
    _ ≤ ∑ _θ : TValsN n, (2 ^ 128 : ℝ≥0∞)⁻¹ * q :=
        Finset.sum_le_sum fun θ _ ↦ totalWeight_firstKSN_le A θ (hq θ)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end Quantum.Qrom.Sphincs.Multi

end
