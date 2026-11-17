module

public import Quantum.Qrom.Sphincs.Costs.RecUMove

@[expose] public section

/-!
# The first reveals of the keys' coordinates

At a first reveal of a key's coordinate `vcoord (msgPos K)` (not yet in the memory label) the run
before it does not depend on the pair there (`viewBy_runtimeR_of_disc`), so summed over the hidden
values the recorded trial cells of `K` on the value it signs count each recorded cell once: each
digest has `2^384` of the `2^512` pairs, and a cell at the encoding slot of `K` is trial `J` of at
most one value (`trialCell_injU`). The first-reveal charges of trial `J` are at most `2^-128`
times the recorded trial-`J` cells of `K` (Disclose's view lemma with a weight per state,
`sum_queryWeight_view_le_wt`); over the trials, `2^-128` times the recorded trial cells of `K`,
which drop the potential `Ψ`.

* **Trial cells name their key and trial** (`IsBlkJU`, `IsBlkU`, `isBlkU_unique`,
  `isBlkJU_trial_unique`).
* **The potential `Ψ`** (`revPotU`): the recorded `h`-cells that are trial cells of a key whose
  coordinate is unrevealed. It is one-cell Lipschitz, the searches' reads (whose coordinate is
  revealed, `labInvU`) and the programs do not raise it, and a first reveal of `K` lowers it by
  `K`'s recorded trial cells (`revDropU`). Along the prefix the drops add up to at most the
  sponge calls `q` (`totalWeight_dropQW_le`).
* **The first reveals** (`sum_totalWeight_firstQW_le`): summed over the hidden values, at most
  `q / 2^128` per hidden value.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Sphincs (Key keyOf msgPos)
open Quantum.Xmss.Hybrid (diagMass setProj restrictTo lazy_const suppAt_empty
  totalWeight_le_totalWeight totalWeight_fintype_sum totalWeight_const_mul_weight
  totalWeight_chargeTrace_le sum_totalWeight_le_of_forall)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT extCls ModedP recKraus initU
  forallQueries_of_modedP totalWeight_le_potential_of_forallQueries tsum_potential_sponge_le
  tsum_potential_le_of_keep potential_basis_init potential_diagPot_sqrt kWt
  sum_queryWeight_view_le_wt viewBy_runtimeR_of_disc eq_of_recKraus_ne_zero
  querySupportedOn_traceRight)

attribute [local irreducible] sphincsRom Fin.fintype

/- Instance search for the register's decidable equality exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-! ## Trial cells name their key and trial -/

/-- **A trial-`J` cell of `K`**: `K` a key of the signatures, the cell its encoding cell of trial
`J` under some `PK.seed` and value. -/
def IsBlkJU (K : Key) (J : ℕ) (x : Qrom.HashDomain) : Prop :=
  InRangeU K ∧ ∃ (P : PublicParameter) (m : Digest), x = trialCell P K m J

/-- **A trial cell of `K`**, of a trial below `2^32`. -/
def IsBlkU (K : Key) (x : Qrom.HashDomain) : Prop :=
  ∃ J < encodingAttemptLimit, IsBlkJU K J x

/-- **An encoding cell names its `PK.seed` and its key.** -/
theorem trialCell_seed_keyU {P P' : PublicParameter} {K K' : Key} {m m' : Digest} {c c' : ℕ}
    (h : trialCell P K m c = trialCell P' K' m' c') : P = P' ∧ K = K' := by
  have hi := encodeInput_injective (encodeInput_slotInput ⟨0, 0, P⟩ 0 (.enc K.1 K.2.1 K.2.2)
    (m, BitVec.ofNat counterBits c)) ((encodeInput_slotInput ⟨0, 0, P'⟩ 0
      (.enc K'.1 K'.2.1 K'.2.2) (m', BitVec.ofNat counterBits c')).trans (congrArg some h.symm))
  simp only [slotInput, addressedHashInput, hasherInput] at hi
  obtain ⟨h1, -⟩ := List.append_inj hi (by
    simp [littleEndianBytes, Quantum.Sphincs.length_toBytes])
  obtain ⟨h2, -⟩ := List.append_inj h1 (by simp [littleEndianBytes])
  have hP : P = P' := Quantum.Sphincs.littleEndianBytes_injective 16 h2
  subst hP
  have hs := (slotOf_trialCell ⟨P, 0⟩ K m c).symm.trans
    ((congrArg (slotOf ⟨P, 0⟩) h).trans (slotOf_trialCell ⟨P, 0⟩ K' m' c'))
  injection Option.some.inj hs with h3 h4 h5
  exact ⟨rfl, Prod.ext h3 (Prod.ext h4 h5)⟩

/-- **A trial cell names its key.** -/
theorem isBlkU_unique {K K' : Key} {x : Qrom.HashDomain} (h : IsBlkU K x) (h' : IsBlkU K' x) :
    K = K' := by
  obtain ⟨J, -, -, P, m, rfl⟩ := h
  obtain ⟨J', -, -, P', m', he⟩ := h'
  exact (trialCell_seed_keyU he).2

/-- **A trial cell names its trial.** -/
theorem isBlkJU_trial_unique {K : Key} {J J' : ℕ} {x : Qrom.HashDomain}
    (hJ : J < encodingAttemptLimit) (hJ' : J' < encodingAttemptLimit) (h : IsBlkJU K J x)
    (h' : IsBlkJU K J' x) : J = J' := by
  obtain ⟨-, P, m, rfl⟩ := h
  obtain ⟨-, P', m', he⟩ := h'
  obtain ⟨rfl, -⟩ := trialCell_seed_keyU he
  exact (trialCell_injU hJ hJ' he).2

/-! ## The potential `Ψ` -/

open scoped Classical in
/-- The keys with unrevealed coordinates (under the label `T`) of which `x` is a trial cell. -/
noncomputable def blkCntU (T : Finset TPos) (x : Qrom.HashDomain) : ℝ :=
  ∑ K : Key, if vcoord (msgPos K) ∉ T ∧ IsBlkU K x then 1 else 0

open scoped Classical in
/-- **The potential `Ψ`**: the recorded `h`-cells that are trial cells of keys with unrevealed
coordinates. -/
noncomputable def revPotU (s : RegQ) : ℝ :=
  ∑ x : Qrom.HashDomain, if s.1.1 x ≠ none then blkCntU s.2.2.1 x else 0

open scoped Classical in
/-- `Ψ` with the cell `z` counted as recorded. -/
noncomputable def revPotAtU (z : Qrom.HashDomain) (s : RegQ) : ℝ :=
  ∑ x : Qrom.HashDomain, if x = z then blkCntU s.2.2.1 z else
    if s.1.1 x ≠ none then blkCntU s.2.2.1 x else 0

open scoped Classical in
/-- The recorded trial cells of `K`. -/
noncomputable def blkRecU (K : Key) (s : RegQ) : ℕ :=
  (Finset.univ.filter fun x : Qrom.HashDomain ↦ s.1.1 x ≠ none ∧ IsBlkU K x).card

open scoped Classical in
/-- The recorded trial-`J` cells of `K`. -/
noncomputable def blkRecJU (K : Key) (J : ℕ) (s : RegQ) : ℕ :=
  (Finset.univ.filter fun x : Qrom.HashDomain ↦ s.1.1 x ≠ none ∧ IsBlkJU K J x).card

open scoped Classical in
/-- **The drop of `Ψ` at a first reveal of `K`'s coordinate**: its recorded trial cells. -/
noncomputable def revDropU (K : Key) (s : RegQ) : ℝ :=
  if vcoord (msgPos K) ∈ s.2.2.1 then 0 else (blkRecU K s : ℝ)

open scoped Classical in
/-- **The trials split the recorded trial cells.** -/
theorem sum_blkRecJU_le (K : Key) (s : RegQ) :
    ∑ J : Fin encodingAttemptLimit, blkRecJU K J.val s ≤ blkRecU K s := by
  unfold blkRecJU blkRecU
  rw [← Finset.card_biUnion]
  · refine Finset.card_le_card fun x hx ↦ ?_
    obtain ⟨J, -, hx⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨-, hr, hb⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hr, J.val, J.isLt, hb⟩
  · intro J _ J' _ hne
    refine Finset.disjoint_left.2 fun x hx hx' ↦ hne (Fin.ext ?_)
    exact isBlkJU_trial_unique J.isLt J'.isLt (Finset.mem_filter.1 hx).2.2
      (Finset.mem_filter.1 hx').2.2

theorem blkCntU_nonneg (T : Finset TPos) (x : Qrom.HashDomain) : 0 ≤ blkCntU T x :=
  Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> norm_num

theorem blkCntU_le_one (T : Finset TPos) (x : Qrom.HashDomain) : blkCntU T x ≤ 1 := by
  classical
  unfold blkCntU
  by_cases h : ∃ K, IsBlkU K x
  · obtain ⟨K₀, hK₀⟩ := h
    rw [Finset.sum_eq_single K₀ (fun K _ hne ↦ ite_eq_right fun hc ↦
      hne (isBlkU_unique hc.2 hK₀)) (fun h ↦ absurd (Finset.mem_univ _) h)]
    split_ifs <;> norm_num
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun K _ ↦ ite_eq_right fun hc ↦ h ⟨K, hc.2⟩)
      zero_le_one

theorem blkCntU_eq_zero {T : Finset TPos} {K : Key} {x : Qrom.HashDomain} (hx : IsBlkU K x)
    (hT : vcoord (msgPos K) ∈ T) : blkCntU T x = 0 := by
  classical
  exact Finset.sum_eq_zero fun _ _ ↦ ite_eq_right fun hc ↦ hc.1 (isBlkU_unique hx hc.2 ▸ hT)

theorem revPotU_nonneg (s : RegQ) : 0 ≤ revPotU s :=
  Finset.sum_nonneg fun x _ ↦ by
    split_ifs
    · exact blkCntU_nonneg _ x
    · exact le_rfl

theorem revPotU_congr {s s' : RegQ} (hk : s'.1.1 = s.1.1) (hl : s'.2.2.1 = s.2.2.1) :
    revPotU s' = revPotU s := by
  unfold revPotU
  rw [hk, hl]

theorem revPotU_le_revPotAtU (z : Qrom.HashDomain) (s : RegQ) : revPotU s ≤ revPotAtU z s :=
  Finset.sum_le_sum fun x _ ↦ by
    by_cases hx : x = z
    · subst hx
      rw [ite_eq_left rfl]
      split_ifs
      · exact le_rfl
      · exact blkCntU_nonneg _ x
    · rw [ite_eq_right hx]

theorem revPotAtU_eq {z : Qrom.HashDomain} {K : Key} (hz : IsBlkU K z) {s : RegQ}
    (hs : vcoord (msgPos K) ∈ s.2.2.1) : revPotAtU z s = revPotU s :=
  Finset.sum_congr rfl fun x _ ↦ by
    by_cases hx : x = z
    · subst hx
      rw [ite_eq_left rfl, blkCntU_eq_zero hz hs]
      split_ifs <;> rfl
    · rw [ite_eq_right hx]

theorem revPotAtU_congr (z : Qrom.HashDomain) {s s' : RegQ}
    (hk : ∀ x, x ≠ z → s'.1.1 x = s.1.1 x) (hl : s'.2.2.1 = s.2.2.1) :
    revPotAtU z s' = revPotAtU z s :=
  Finset.sum_congr rfl fun x _ ↦ by
    rw [hl]
    by_cases hx : x = z
    · rw [ite_eq_left hx, ite_eq_left hx]
    · rw [ite_eq_right hx, ite_eq_right hx, hk x hx]

/-- **`Ψ` is one-cell Lipschitz.** -/
theorem oneCellLipschitz_revPotU : OneCellLipschitz (X := PairOut) (Z := Qrom.HashDomain)
    (M := QMem) revPotU where
  h D b z v := by
    classical
    set f : Qrom.HashDomain → ℝ := fun x ↦ if D.1 x ≠ none then blkCntU b.2.1 x else 0
    set f' : Qrom.HashDomain → ℝ := fun x ↦
      if Function.update D.1 z v x ≠ none then blkCntU b.2.1 x else 0
    have hd : ∑ x, (f' x - f x) = f' z - f z :=
      Finset.sum_eq_single z (fun x _ hx ↦ by simp [f, f', Function.update_of_ne hx])
        (fun h ↦ absurd (Finset.mem_univ z) h)
    have hf' : f' z ≤ 1 := by
      simp only [f']
      split_ifs
      · exact blkCntU_le_one _ z
      · exact zero_le_one
    have hf : 0 ≤ f z := by
      simp only [f]
      split_ifs
      · exact blkCntU_nonneg _ z
      · exact le_rfl
    show ∑ x, f' x ≤ ∑ x, f x + 1
    rw [Finset.sum_sub_distrib] at hd
    linarith
  k _ _ _ _ := le_of_eq_of_le (revPotU_congr rfl rfl) (le_add_of_nonneg_right zero_le_one)
  k' _ _ _ _ := le_of_eq_of_le (revPotU_congr rfl rfl) (le_add_of_nonneg_right zero_le_one)

/-- **A program does not raise `Ψ`**: it discards its cell from the databases. -/
theorem revPotU_progMap_le (c : HwProg PairOut Qrom.HashDomain) (s : RegQ) :
    revPotU (progMap c s) ≤ revPotU s := by
  obtain ⟨⟨dh, dk, dk'⟩, W, ⟨L, m⟩⟩ := s
  rcases c with ⟨z, w⟩ | ⟨x, w⟩ | ⟨x, w⟩
  · refine Finset.sum_le_sum fun y _ ↦ ?_
    show (if Function.update dh z none y ≠ none then blkCntU L y else 0) ≤
      if dh y ≠ none then blkCntU L y else 0
    by_cases hy : y = z
    · subst hy
      rw [Function.update_self, ite_eq_right (fun h ↦ h rfl)]
      split_ifs
      · exact blkCntU_nonneg _ y
      · exact le_rfl
    · rw [Function.update_of_ne hy]
  · exact le_of_eq (revPotU_congr rfl rfl)
  · exact le_of_eq (revPotU_congr rfl rfl)

/-- The register after a record of `T`. -/
def recMapU {X₁ Z₁ S₁ M₁ : Type} [DecidableEq S₁] (T : Finset S₁)
    (s : HwReg X₁ Z₁ (Finset S₁ × M₁)) : HwReg X₁ Z₁ (Finset S₁ × M₁) :=
  (s.1, s.2.1, (s.2.2.1 ∪ T, s.2.2.2))

theorem blkCntU_union_le (T T' : Finset TPos) (x : Qrom.HashDomain) :
    blkCntU (T ∪ T') x ≤ blkCntU T x :=
  Finset.sum_le_sum fun K _ ↦ by
    by_cases h : vcoord (msgPos K) ∉ T ∪ T' ∧ IsBlkU K x
    · rw [ite_eq_left h, ite_eq_left ⟨fun hl ↦ h.1 (Finset.mem_union_left _ hl), h.2⟩]
    · rw [ite_eq_right h]
      split_ifs <;> norm_num

open scoped Classical in
theorem ind_add_blkCntU_le {T : Finset TPos} {K : Key} (hl : vcoord (msgPos K) ∉ T)
    (x : Qrom.HashDomain) :
    (if IsBlkU K x then (1 : ℝ) else 0) + blkCntU (T ∪ {vcoord (msgPos K)}) x ≤
      blkCntU T x := by
  classical
  unfold blkCntU
  have h1 : (if IsBlkU K x then (1 : ℝ) else 0) =
      ∑ K' : Key, if K' = K then (if vcoord (msgPos K') ∉ T ∧ IsBlkU K' x then 1 else 0)
        else 0 := by
    rw [Finset.sum_ite_eq' Finset.univ K, ite_eq_left (Finset.mem_univ _)]
    by_cases hb : IsBlkU K x
    · rw [ite_eq_left hb, ite_eq_left ⟨hl, hb⟩]
    · rw [ite_eq_right hb, ite_eq_right fun h ↦ hb h.2]
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun K' _ ↦ ?_
  by_cases hr : K' = K
  · subst hr
    have h0 : ¬(vcoord (msgPos K') ∉ T ∪ {vcoord (msgPos K')} ∧ IsBlkU K' x) :=
      fun h ↦ h.1 (Finset.mem_union_right _ (Finset.mem_singleton_self _))
    rw [ite_eq_left rfl, ite_eq_right h0, add_zero]
  · rw [ite_eq_right hr, zero_add]
    by_cases h : vcoord (msgPos K') ∉ T ∪ {vcoord (msgPos K)} ∧ IsBlkU K' x
    · rw [ite_eq_left h, ite_eq_left ⟨fun hl' ↦ h.1 (Finset.mem_union_left _ hl'), h.2⟩]
    · rw [ite_eq_right h]
      split_ifs <;> norm_num

/-- The drop at a record of `T`: a first reveal's recorded trial cells, nothing otherwise. -/
noncomputable def revDropOU (T : Finset TPos) (s : RegQ) : ℝ :=
  match keyOfTU T with
  | some K => revDropU K s
  | none => 0

theorem revDropOU_nonneg (T : Finset TPos) (s : RegQ) : 0 ≤ revDropOU T s := by
  unfold revDropOU
  split
  · unfold revDropU
    split_ifs
    · exact le_rfl
    · exact Nat.cast_nonneg _
  · exact le_rfl

/-- **A record drops `Ψ` by at least the first-reveal drop.** -/
theorem revDropOU_add_le (T : Finset TPos) (s : RegQ) :
    revDropOU T s + revPotU (recMapU T s) ≤ revPotU s := by
  classical
  obtain ⟨D, W, ⟨L, m⟩⟩ := s
  have hle : revPotU (recMapU T (D, W, (L, m))) ≤ revPotU (D, W, (L, m)) :=
    Finset.sum_le_sum fun y _ ↦ by
      show (if D.1 y ≠ none then blkCntU (L ∪ T) y else 0) ≤
        if D.1 y ≠ none then blkCntU L y else 0
      split_ifs
      · exact blkCntU_union_le L T y
      · exact le_rfl
  unfold revDropOU
  rcases ho : keyOfTU T with _ | K
  · rw [zero_add]
    exact hle
  · show revDropU K (D, W, (L, m)) + _ ≤ _
    unfold revDropU
    split_ifs with hl
    · rw [zero_add]
      exact hle
    · have hT : T = {vcoord (msgPos K)} := (keyOfTU_spec ho).2
      subst hT
      show ((Finset.univ.filter fun y : Qrom.HashDomain ↦ D.1 y ≠ none ∧ IsBlkU K y).card : ℝ) +
        ∑ y : Qrom.HashDomain,
          (if D.1 y ≠ none then blkCntU (L ∪ {vcoord (msgPos K)}) y else 0) ≤
          ∑ y : Qrom.HashDomain, if D.1 y ≠ none then blkCntU L y else 0
      rw [Finset.card_filter, Nat.cast_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun y _ ↦ ?_
      by_cases hD : D.1 y ≠ none
      · rw [ite_eq_left hD, ite_eq_left hD]
        have h := ind_add_blkCntU_le hl y
        by_cases hb : IsBlkU K y
        · rw [ite_eq_left hb] at h
          rw [ite_eq_left ⟨hD, hb⟩, Nat.cast_one]
          exact h
        · rw [ite_eq_right hb] at h
          rw [ite_eq_right fun h' ↦ hb h'.2, Nat.cast_zero]
          exact h
      · rw [ite_eq_right hD, ite_eq_right hD, ite_eq_right fun h ↦ hD h.1, Nat.cast_zero,
          zero_add]

/-! ## Diagonal potentials along a record port -/

section recGen

variable {X₁ Z₁ S₁ M₁ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
  [Fintype S₁] [DecidableEq S₁] [Fintype M₁] [DecidableEq M₁]

omit [Fintype S₁] [Fintype M₁] in
theorem recKraus_apply_eqU (T : Finset S₁) (m : Finset S₁ × M₁)
    (t s : Unit × HwReg X₁ Z₁ (Finset S₁ × M₁)) :
    recKraus (X := X₁) (Z := Z₁) T m t s =
      if m = s.2.2.2 ∧ t = ((), recMapU T s.2) then 1 else 0 := by
  obtain ⟨⟨⟩, D', W', m'⟩ := t
  obtain ⟨⟨⟩, D, W, mm⟩ := s
  simp only [recKraus, kroneckerMap_apply, Matrix.one_apply_eq, one_mul, clsKraus_apply,
    Matrix.one_apply, recMapU, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- **A record port on a diagonal potential**: the weights after it are those of the recorded
states. -/
theorem tsum_potential_rec_eqU {φ : HwReg X₁ Z₁ (Finset S₁ × M₁) → ℝ} (hφ0 : ∀ s, 0 ≤ φ s)
    (T : Finset S₁)
    {σ : Matrix (Unit × HwReg X₁ Z₁ (Finset S₁ × M₁)) (Unit × HwReg X₁ Z₁ (Finset S₁ × M₁)) ℂ}
    (hσ : σ.PosSemidef) :
    ∑' m, potential (diagPot fun s ↦ √(φ s))
        (MatrixMap.conj (recKraus (X := X₁) (Z := Z₁) T m) σ) =
      ENNReal.ofReal (∑ q, φ (recMapU T q.2) * (σ q q).re) := by
  have hpost : ∀ m, 0 ≤ dW (fun q : Unit × HwReg X₁ Z₁ (Finset S₁ × M₁) ↦ φ q.2)
      (MatrixMap.conj (recKraus (X := X₁) (Z := Z₁) T m) σ) := fun m ↦
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (hφ0 q.2)
      (Complex.nonneg_iff.1 (posSemidef_conj _ hσ).diag_nonneg).1
  have hpot : ∀ τ : Matrix (Unit × HwReg X₁ Z₁ (Finset S₁ × M₁))
      (Unit × HwReg X₁ Z₁ (Finset S₁ × M₁)) ℂ,
      potential (diagPot fun s ↦ √(φ s)) τ = ENNReal.ofReal (dW (fun q ↦ φ q.2) τ) :=
    fun τ ↦ potential_diagPot_sqrt hφ0 τ
  have hinj : ∀ q q' : Unit × HwReg X₁ Z₁ (Finset S₁ × M₁), q.2.2.2 = q'.2.2.2 →
      ((), recMapU T q.2) = ((), recMapU T q'.2) → q = q' := fun q q' hi hf ↦
    Prod.ext (Subsingleton.elim _ _) (Prod.ext (congrArg (fun t ↦ t.2.1) hf)
      (Prod.ext (congrArg (fun t ↦ t.2.2.1) hf) hi))
  simp only [hpot]
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun m _ ↦ hpost m, sum_dW_conj,
    gram_classical_diag (recKraus (X := X₁) (Z := Z₁) T) (fun q ↦ q.2.2.2)
      (fun q ↦ ((), recMapU T q.2)) (recKraus_apply_eqU T) hinj, re_trace_diagonal_mul]

end recGen

/-! ## `Ψ` along the prefix -/

/-- **The label invariant of the searches**: in the search of `K`, its coordinate is revealed. -/
def labInvU : ModeU → Set RegQ
  | .rest _ => Set.univ
  | .grd _ K _ _ => {s | vcoord (msgPos K) ∈ s.2.2.1}

/-- **The allowed calls keep the label invariant.** -/
theorem labInvU_step (θ : TVals) (μ : ModeU)
    (i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port)
    (r : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Result i)
    (σ : Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × (runtimeR m0Q).D)
      ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × (runtimeR m0Q).D) ℂ)
    (hok : srchOkZ θ μ i)
    (hσ : QuerySupportedOn
      (fun m : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × (runtimeR m0Q).D ↦ m.2)
      (labInvU μ) σ) :
    QuerySupportedOn
      (fun m : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Out i × (runtimeR m0Q).D ↦ m.2)
      (labInvU (srchNxZ θ μ i r)) (((runtimeR m0Q).step i).branch r σ) := by
  rcases i with ((i | c) | c) | T
  · exact querySupportedOn_univ _ _
  · rcases μ with ks | ⟨ks, K, m, j⟩
    · exact hok.elim
    have hb : ((runtimeR m0Q).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty PairOut Qrom.HashDomain)
        m0Q c r) σ
    rw [hb]
    obtain ⟨-, rfl⟩ := hok
    refine hσ.conj fun q' q hK hq ↦ ?_
    obtain ⟨-, hK'⟩ := one_kronecker_ne_zero (a := q.1) (a' := q'.1) (b := q.2) (b' := q'.2) hK
    obtain ⟨hm, hm'⟩ := readKrausH_ne_zero_memU (trialCell (tabOf θ).publicSeed K m j)
      (trialUpdQ K (trialCell (tabOf θ).publicSeed K m j)) r hK'
    have hl : q'.2.2.2.1 = q.2.2.2.1 := by rw [hm', hm]; rfl
    show q'.2 ∈ labInvU (decNxU ks K m j (TargetSum.decodeDigest (truncateHash (r.1.getD 0).1)))
    generalize TargetSum.decodeDigest (truncateHash (r.1.getD 0).1) = dd
    cases dd with
    | some _ => trivial
    | none =>
      show vcoord (msgPos K) ∈ q'.2.2.2.1
      rw [hl]
      exact hq
  · exact querySupportedOn_univ _ _
  · rcases ho : keyOfTU T with _ | K
    · have hn : srchNxZ θ μ (.inr T) r = .rest μ.ks := revNxU_none μ ho _
      rw [hn]
      exact querySupportedOn_univ _ _
    · have hn : srchNxZ θ μ (.inr T) r =
          .grd (insert K μ.ks) K ((tabOf θ).valuePos (msgPos K)) 0 := by
        show revNxU μ T _ = _
        unfold revNxU
        rw [ho]
      have hT : T = {vcoord (msgPos K)} := (keyOfTU_spec ho).2
      rw [hn]
      refine QuerySupportedOn.conj (K := recKraus (X := PairOut) (Z := Qrom.HashDomain) T r) hσ
        fun q' q hK _ ↦ ?_
      rw [eq_of_recKraus_ne_zero (u := q.1) (u' := q'.1) (s := q.2) (s' := q'.2) hK]
      show vcoord (msgPos K) ∈ q.2.2.2.1 ∪ T
      rw [hT]
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- **The drops of `Ψ` at the record ports.** -/
noncomputable def dropQWU : ∀ i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port,
    Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD)
      ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD) ℂ → ℝ≥0∞
  | .inr T, σ => ENNReal.ofReal (∑ q : Unit × RegQ, revDropOU T q.2 * (σ q q).re)
  | _, _ => 0

/-- The traces at the sponge ports. -/
noncomputable def spongeTrU (i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port)
    (σ : Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD)
      ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD) ℂ) : ℝ≥0∞ :=
  ((if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 0 else 1 : ℕ) :
    ℝ≥0∞) * ENNReal.ofReal σ.trace.re

/-- **The step of `Ψ`**: a sponge call raises it by at most its trace; a search's read, a program
and a record do not raise it, a record lowering it by the first-reveal drop. -/
theorem revPotU_step (θ : TVals) (i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port)
    (σ : Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × (runtimeR m0Q).D)
      ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × (runtimeR m0Q).D) ℂ)
    (hσ : σ.PosSemidef)
    (hI : ∃ μ, srchOkZ θ μ i ∧ QuerySupportedOn
      (fun m : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × (runtimeR m0Q).D ↦ m.2)
      (labInvU μ) σ) :
    dropQWU i σ + ∑' r, potential (diagPot fun s ↦ √(revPotU s))
        (((runtimeR m0Q).step i).branch r σ) ≤
      potential (diagPot fun s ↦ √(revPotU s)) σ + spongeTrU i σ := by
  have hφ0 := revPotU_nonneg
  rcases i with ((p | c) | c) | T
  · have hb : ∀ r : Unit, ((runtimeR m0Q).step (.inl (.inl (.inl p)))).branch r σ =
        MatrixMap.conj ((spongeHardwired PairOut Qrom.HashDomain
          (hwEmpty PairOut Qrom.HashDomain) m0Q).U p) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty PairOut Qrom.HashDomain)
        m0Q p r) σ
    have hc : spongeTrU (.inl (.inl (.inl p))) σ = ENNReal.ofReal σ.trace.re := by
      simp [spongeTrU, extCls, hwCls]
      rfl
    rw [hc]
    show 0 + _ ≤ _
    rw [zero_add]
    exact (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans
      (tsum_potential_sponge_le hφ0 oneCellLipschitz_revPotU (hwEmpty PairOut Qrom.HashDomain)
        m0Q p hσ)
  · obtain ⟨μ, hok, hs⟩ := hI
    have hb : ∀ r, ((runtimeR m0Q).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty PairOut Qrom.HashDomain)
        m0Q c r) σ
    have hc : spongeTrU (.inl (.inl (.inr c))) σ = 0 := by
      simp [spongeTrU, extCls, hwCls]
    rw [hc, add_zero]
    show 0 + _ ≤ _
    rw [zero_add]
    refine (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans ?_
    show ∑' r : c.Result, potential (diagPot fun s ↦ √(revPotU s))
      (MatrixMap.conj (hwReadKraus c r) σ) ≤ _
    rcases μ with ks | ⟨ks, K, m, j⟩
    · exact hok.elim
    obtain ⟨hj, rfl⟩ := hok
    rw [trialRead_eq]
    have hK : InRangeU K ∨ ¬ InRangeU K := Classical.em _
    have hx : InRangeU K → IsBlkU K (trialCell (tabOf θ).publicSeed K m j) :=
      fun hK ↦ ⟨j, hj, hK, _, _, rfl⟩
    refine tsum_potential_le_of_keep _ (sum_hwReadKraus _) hφ0
      (revPotU_le_revPotAtU (trialCell (tabOf θ).publicSeed K m j)) (fun r a a' h ↦ ?_) hσ
      (fun q hq ↦ ?_)
    · obtain ⟨-, hK'⟩ := one_kronecker_ne_zero (a := a.1) (a' := a'.1) (b := a.2) (b' := a'.2) h
      obtain ⟨hm, hm'⟩ := readKrausH_ne_zero_memU _ _ r hK'
      exact revPotAtU_congr _ (readKrausH_ne_zero_cellsU _ _ r hK') (by rw [hm', hm]; rfl)
    · rcases hK with hK | hK
      · exact (revPotAtU_eq (hx hK) (hs q q hq).1).symm
      · refine Finset.sum_congr rfl fun x _ ↦ ?_
        by_cases hxz : x = trialCell (tabOf θ).publicSeed K m j
        · subst hxz
          have h0 : blkCntU q.2.2.2.1 (trialCell (tabOf θ).publicSeed K m j) = 0 := by
            classical
            refine Finset.sum_eq_zero fun K' _ ↦ ite_eq_right fun hc ↦ ?_
            obtain ⟨J, -, hK'', P', m', he⟩ := hc.2
            exact hK ((trialCell_seed_keyU he).2 ▸ hK'')
          rw [ite_eq_left rfl, h0]
          split_ifs <;> rfl
        · rw [ite_eq_right hxz]
  · have hb : ∀ r, ((runtimeR m0Q).step (.inl (.inr c))).branch r σ =
        MatrixMap.conj (hwProgKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty PairOut Qrom.HashDomain)
        m0Q c r) σ
    have hc : spongeTrU (.inl (.inr c)) σ = 0 := by
      simp [spongeTrU, extCls, hwCls]
    rw [hc, add_zero]
    show 0 + _ ≤ _
    rw [zero_add]
    refine (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans ?_
    refine (le_of_eq (tsum_potential_prog_eq hφ0 c hσ)).trans ?_
    refine le_of_le_of_eq ?_ (potential_diagPot_sqrt hφ0 σ).symm
    refine ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun q _ ↦ ?_)
    exact mul_le_mul_of_nonneg_right (revPotU_progMap_le c q.2)
      (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  · have hc : spongeTrU (.inr T) σ = 0 := by
      simp [spongeTrU, extCls]
    rw [hc, add_zero]
    show ENNReal.ofReal (∑ q : Unit × RegQ, revDropOU T q.2 * (σ q q).re) +
      ∑' m, potential (diagPot fun s ↦ √(revPotU s))
        (MatrixMap.conj (recKraus (X := PairOut) (Z := Qrom.HashDomain) T m) σ) ≤ _
    rw [tsum_potential_rec_eqU hφ0 T hσ]
    refine le_of_le_of_eq ?_ (potential_diagPot_sqrt hφ0 σ).symm
    have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    have h1 : 0 ≤ ∑ q : Unit × RegQ, revDropOU T q.2 * (σ q q).re :=
      Finset.sum_nonneg fun q _ ↦ mul_nonneg (revDropOU_nonneg _ _) (hre q)
    have h2 : 0 ≤ ∑ q : Unit × RegQ, revPotU (recMapU T q.2) * (σ q q).re :=
      Finset.sum_nonneg fun q _ ↦ mul_nonneg (hφ0 _) (hre q)
    refine (ENNReal.ofReal_add h1 h2).symm.trans_le (ENNReal.ofReal_le_ofReal ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (revDropOU_add_le T q.2) (hre q)

/-- **The first-reveal drops of `Ψ` along the prefix**: at most the sponge charge (the potential
starts at `0`). -/
theorem totalWeight_dropQW_le {pol : DigestPolicy} (hpol : pol.NoVal) (A : SAdversary)
    (θ : TVals) {q : ℕ}
    (hq : IFreeM.IsChargeBound (prefixQ pol A θ) (portCharge fun i ↦
      if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 0 else 1) q) :
    (runtimeR m0Q).totalWeight .instruments dropQWU (prefixQ pol A θ) initQ ≤ q := by
  have hφ0 := revPotU_nonneg
  have hfa := forallQueries_of_modedP (runtimeR m0Q) .instruments labInvU
    (fun μ i r σ hok h ↦ labInvU_step θ μ i r σ hok h) (prefixQ pol A θ) (.rest ∅)
    (modedP_prefixQ hpol A θ) (ρ := initQ) (querySupportedOn_univ _ _)
  have h := totalWeight_le_potential_of_forallQueries (runtimeR m0Q) .instruments
    (diagPot fun s ↦ √(revPotU s)) _
    (fun i σ ↦ ∃ μ, srchOkZ θ μ i ∧ QuerySupportedOn
      (fun m : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × (runtimeR m0Q).D ↦ m.2)
      (labInvU μ) σ)
    (fun i E σ hP ↦ by
      obtain ⟨μ, hok, hs⟩ := hP
      exact ⟨μ, hok, querySupportedOn_traceRight hs⟩)
    dropQWU spongeTrU (fun i σ hσ hI ↦ revPotU_step θ i σ hσ hI) (prefixQ pol A θ)
    initQ_posSemidef hfa
  have h0 : potential (diagPot fun s ↦ √(revPotU s)) initQ = 0 := by
    unfold initQ initU
    rw [potential_basis_init m0Q hφ0 ()]
    refine (congrArg ENNReal.ofReal (Finset.sum_eq_zero fun y _ ↦ ite_eq_right fun h ↦
      h rfl)).trans ENNReal.ofReal_zero
  refine h.trans ((add_le_add (le_of_eq h0) le_rfl).trans ?_)
  rw [zero_add]
  refine (totalWeight_chargeTrace_le (runtimeR m0Q) .instruments _ _ hq
    initQ_posSemidef).trans ?_
  calc (q : ℝ≥0∞) * ENNReal.ofReal initQ.trace.re ≤ q * 1 := by
        gcongr
        exact ofReal_trace_initQ_le_one
    _ = q := mul_one _

/-! ## The first reveals, against `Ψ` -/

theorem pairAt_update_neU {v : TVals} {s t : TPos} (h : t ≠ s) (d : TVal s) :
    pairAt (Function.update v s d) t = pairAt v t := by
  cases t with
  | val p => exact Function.update_of_ne h _ _
  | dig m => exact Function.update_of_ne h _ _
  | str j => exact Function.update_of_ne h _ _
  | asg m j => rfl

/-- **The values of a key's coordinate whose trial-`J` cell is recorded** are at most `2^-128` of
the pairs per recorded trial-`J` cell of the key. -/
theorem card_firstFU_le {K : Key} (hK : InRangeU K) (J : Fin encodingAttemptLimit) (s : RegQ)
    (v : TVals) :
    ((Finset.univ.filter fun d : TVal (vcoord (msgPos K)) ↦
        s.1.1 (trialCell (tabOf (Function.update v (vcoord (msgPos K)) d)).publicSeed K
          ((tabOf (Function.update v (vcoord (msgPos K)) d)).valuePos (msgPos K)) J) ≠
            none).card : ℝ≥0∞) * (Fintype.card (TVal (vcoord (msgPos K))) : ℝ≥0∞)⁻¹ ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * blkRecJU K J s := by
  have hseed : ∀ d : TVal (vcoord (msgPos K)),
      (tabOf (Function.update v (vcoord (msgPos K)) d)).publicSeed = (tabOf v).publicSeed :=
    fun d ↦ publicSeed_tabOf_congr (pairAt_update_neU (fun h ↦ notMcU_seedC K hK h) d)
  have hval : ∀ d : TVal (vcoord (msgPos K)),
      (tabOf (Function.update v (vcoord (msgPos K)) d)).valuePos (msgPos K) =
        pairDigest (pairAt (Function.update v (vcoord (msgPos K)) d) (vcoord (msgPos K))) :=
    fun d ↦ valuePos_msgPosU hK _
  simp only [hseed, hval]
  set P₀ := (tabOf v).publicSeed
  set M := Finset.univ.filter fun m : Digest ↦ s.1.1 (trialCell P₀ K m J) ≠ none
  have hM : M.card ≤ blkRecJU K J s := by
    classical
    unfold blkRecJU
    exact Quantum.Xmss.Assembly.card_filter_le_of_injective
      (f := fun m : Digest ↦ trialCell P₀ K m J)
      (fun m m' h ↦ (trialCell_injU J.isLt J.isLt h).1) _ _ fun m hm ↦ ⟨hm, hK, P₀, m, rfl⟩
  obtain ⟨p, hp⟩ := msgPos_isValU hK
  generalize vcoord (msgPos K) = t at hp ⊢
  subst hp
  have hF : (Finset.univ.filter fun d : TVal (SPos.val p) ↦ s.1.1 (trialCell P₀ K
      (pairDigest (pairAt (Function.update v (SPos.val p) d) (SPos.val p))) J) ≠ none).card ≤
        M.card * (2 ^ 128 * 2 ^ 256) := by
    have hsub : (Finset.univ.filter fun d : TVal (SPos.val p) ↦ s.1.1 (trialCell P₀ K
        (pairDigest (pairAt (Function.update v (SPos.val p) d) (SPos.val p))) J) ≠ none) ⊆
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
    _ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ * blkRecJU K J s := by
        rw [pairFiber_div_card, mul_comm]
        exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hM) zero_le

theorem diagMass_empty_setU {α : Type} [Fintype α] (σ : Matrix α α ℂ) :
    diagMass (∅ : Set α) σ = 0 := by
  simp [diagMass]

/-- The first-run states of trial `J` at the reveals, at the hidden values `θ`. -/
def firstSetU (θ : TVals) (J : ℕ) :
    ∀ i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port,
      Set ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD)
  | .inr T => match keyOfTU T with
    | some K => {q | vcoord (msgPos K) ∉ q.2.2.2.1 ∧ q.2.1.1 (trialCell (tabOf θ).publicSeed K
        ((tabOf θ).valuePos (msgPos K)) J) ≠ none}
    | none => ∅
  | _ => ∅

/-- The source of a reveal: its key's coordinate, if unrevealed. -/
noncomputable def firstSrcU : ∀ i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port,
    (recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD → Finset TPos
  | .inr T, q => match keyOfTU T with
    | some K => if vcoord (msgPos K) ∈ q.2.2.2.1 then ∅ else {vcoord (msgPos K)}
    | none => ∅
  | _, _ => ∅

/-- The source values of trial `J` at a reveal: the pairs at the key's coordinate whose trial-`J`
cell is recorded (the other coordinates read off the hidden values). -/
noncomputable def firstFU (J : ℕ) : ∀ i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port,
    (recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD → (s : TPos) → TVals →
      Finset (TVal s)
  | .inr T, q => fun s v ↦ match keyOfTU T with
    | some K => Finset.univ.filter fun d : TVal s ↦ q.2.1.1 (trialCell
        (tabOf (Function.update v s d)).publicSeed K
          ((tabOf (Function.update v s d)).valuePos (msgPos K)) J) ≠ none
    | none => ∅
  | _, _ => fun _ _ ↦ ∅

/-- The weight per state of a reveal at trial `J`: its key's recorded trial-`J` cells over
`2^128`, if first. -/
noncomputable def firstKU (J : ℕ) : ∀ i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port,
    (recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD → ℝ≥0∞
  | .inr T, q => match keyOfTU T with
    | some K => (2 ^ 128 : ℝ≥0∞)⁻¹ *
        (if vcoord (msgPos K) ∈ q.2.2.2.1 then 0 else (blkRecJU K J q.2 : ℝ≥0∞))
    | none => 0
  | _, _ => 0

/-- **The view lemma at the first reveals, trial by trial.** -/
theorem sum_totalWeight_firstSetU_le (pol : DigestPolicy) (A : SAdversary)
    (J : Fin encodingAttemptLimit) :
    ∑ θ : TVals, (runtimeR m0Q).totalWeight .instruments
        (fun i ↦ diagMass (firstSetU θ J i)) (prefixQ pol A θ) initQ ≤
      ∑ θ : TVals, (runtimeR m0Q).totalWeight .instruments
        (fun i ↦ kWt (firstKU J i)) (prefixQ pol A θ) initQ := by
  have h := sum_totalWeight_le_of_forall (runtimeR m0Q) LocalSig.Interp.instruments
    (fun θ i ↦ diagMass (firstSetU θ J i)) (fun i ↦ kWt (firstKU J i))
    (fun θ ↦ prefixQ pol A θ) (fun _ ↦ initQ) 1 fun n ↦ by
      rw [one_mul]
      refine sum_queryWeight_view_le_wt (runtimeR m0Q) LocalSig.Interp.instruments
        (fun r ↦ r.2.2.1) (fun θ ↦ prefixQ pol A θ) (fun _ ↦ initQ) (fun _ ↦ initQ_posSemidef) n
        (fun _ ↦ True)
        ((viewBy_runtimeR_of_disc LocalSig.Interp.instruments m0Q
          (prefixT SelMem cwUpd pol A) ∅ (disc_prefixT SelMem cwUpd pol A ∅) (fun _ ↦ initQ)
          (lazy_const _ initQ) (fun _ ↦ suppAt_empty _ initQ) n).viewByOn fun _ ↦ True)
        (fun θ ↦ firstSetU θ J) (fun _ _ h ↦ absurd trivial h) firstSrcU (firstFU J)
        (fun i p s v d ↦ ?_) (fun v i p hp ↦ ?_) (firstKU J) (fun i p v ↦ ?_)
      · rcases i with ((i | c) | c) | T
        · rfl
        · rfl
        · rfl
        · simp only [firstFU, Function.update_idem]
      · rcases i with ((i | c) | c) | T
        · exact hp.elim
        · exact hp.elim
        · exact hp.elim
        · rcases hT : keyOfTU T with _ | K
          · simp only [firstSetU, hT] at hp
            exact hp.elim
          · simp only [firstSetU, hT] at hp
            refine ⟨vcoord (msgPos K), ?_, hp.1, ?_⟩
            · simp only [firstSrcU, hT, ite_eq_right hp.1, Finset.mem_singleton]
            · simp only [firstFU, hT, Function.update_eq_self, Finset.mem_filter,
                Finset.mem_univ, true_and]
              exact hp.2
      · rcases i with ((i | c) | c) | T
        · exact le_of_eq_of_le Finset.sum_empty zero_le
        · exact le_of_eq_of_le Finset.sum_empty zero_le
        · exact le_of_eq_of_le Finset.sum_empty zero_le
        · rcases hT : keyOfTU T with _ | K
          · simp only [firstSrcU, hT, Finset.sum_empty]
            exact zero_le
          · by_cases hl : vcoord (msgPos K) ∈ p.2.2.2.1
            · simp only [firstSrcU, hT, ite_eq_left hl, Finset.sum_empty]
              exact zero_le
            · simp only [firstSrcU, firstFU, firstKU, hT, ite_eq_right hl, Finset.sum_singleton]
              exact card_firstFU_le (keyOfTU_spec hT).1 J p.2 v
  rwa [one_mul] at h

theorem firstQWU_eq_sum (θ : TVals) (i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port)
    (σ : Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD)
      ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD) ℂ) :
    firstQWU θ i σ = ∑ J : Fin encodingAttemptLimit, diagMass (firstSetU θ J.val i) σ := by
  rcases i with ((i | c) | c) | T
  · exact (Finset.sum_eq_zero fun _ _ ↦ diagMass_empty_setU σ).symm
  · exact (Finset.sum_eq_zero fun _ _ ↦ diagMass_empty_setU σ).symm
  · exact (Finset.sum_eq_zero fun _ _ ↦ diagMass_empty_setU σ).symm
  · rcases hT : keyOfTU T with _ | K
    · simp only [firstQWU, firstSetU, hT]
      exact (Finset.sum_eq_zero fun _ _ ↦ diagMass_empty_setU σ).symm
    · simp only [firstQWU, firstSetU, hT]
      rfl

theorem sum_kWt_firstKU_inr (T : Finset TPos) (σ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ)
    (hσ : σ.PosSemidef) :
    ∑ J : Fin encodingAttemptLimit, ∑ q : Unit × RegQ, firstKU J.val (.inr T) q *
        ENNReal.ofReal (σ q q).re ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (∑ q : Unit × RegQ, revDropOU T q.2 * (σ q q).re) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  rw [ENNReal.ofReal_sum_of_nonneg fun q _ ↦ mul_nonneg (revDropOU_nonneg _ _) (hre q),
    Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  rw [← Finset.sum_mul, ENNReal.ofReal_mul (revDropOU_nonneg _ _), ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ zero_le
  rcases hT : keyOfTU T with _ | K
  · simp only [firstKU, revDropOU, hT, Finset.sum_const_zero]
    exact zero_le
  · simp only [firstKU, revDropOU, hT, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    unfold revDropU
    by_cases hl : vcoord (msgPos K) ∈ q.2.2.2.1
    · simp only [ite_eq_left hl, Finset.sum_const_zero]
      exact zero_le
    · simp only [ite_eq_right hl]
      rw [ENNReal.ofReal_natCast, ← Nat.cast_sum]
      exact Nat.cast_le.mpr (sum_blkRecJU_le K q.2)

theorem sum_kWt_firstKU_le (i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port)
    (σ : Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD)
      ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD) ℂ) (hσ : σ.PosSemidef) :
    ∑ J : Fin encodingAttemptLimit, kWt (firstKU J.val i) σ ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * dropQWU i σ := by
  rcases i with ((i | c) | c) | T
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦
      zero_mul _) zero_le
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦
      zero_mul _) zero_le
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦
      zero_mul _) zero_le
  · exact sum_kWt_firstKU_inr T σ hσ

/-- **The first-reveal charges, summed over the hidden values**: at most `q / 2^128` per hidden
value. -/
theorem sum_totalWeight_firstQW_le {pol : DigestPolicy} (hpol : pol.NoVal) (A : SAdversary)
    {q : ℕ}
    (hq : ∀ θ, IFreeM.IsChargeBound (prefixQ pol A θ) (portCharge fun i ↦
      if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 0 else 1) q) :
    ∑ θ : TVals, (runtimeR m0Q).totalWeight .instruments (firstQWU θ) (prefixQ pol A θ) initQ ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * q * Fintype.card TVals := by
  calc ∑ θ : TVals, (runtimeR m0Q).totalWeight .instruments (firstQWU θ) (prefixQ pol A θ) initQ
      = ∑ θ : TVals, ∑ J : Fin encodingAttemptLimit,
          (runtimeR m0Q).totalWeight .instruments (fun i ↦ diagMass (firstSetU θ J.val i))
            (prefixQ pol A θ) initQ := Finset.sum_congr rfl fun θ _ ↦
        (congrArg (fun w ↦ (runtimeR m0Q).totalWeight .instruments w (prefixQ pol A θ) initQ)
          (funext fun i ↦ funext fun σ ↦ firstQWU_eq_sum θ i σ)).trans
          (totalWeight_fintype_sum (runtimeR m0Q) .instruments
            (fun (J : Fin encodingAttemptLimit) i ↦ diagMass (firstSetU θ J.val i))
            (prefixQ pol A θ) initQ)
    _ = ∑ J : Fin encodingAttemptLimit, ∑ θ : TVals,
          (runtimeR m0Q).totalWeight .instruments (fun i ↦ diagMass (firstSetU θ J.val i))
            (prefixQ pol A θ) initQ := Finset.sum_comm
    _ ≤ ∑ J : Fin encodingAttemptLimit, ∑ θ : TVals,
          (runtimeR m0Q).totalWeight .instruments (fun i ↦ kWt (firstKU J.val i))
            (prefixQ pol A θ) initQ :=
        Finset.sum_le_sum fun J _ ↦ sum_totalWeight_firstSetU_le pol A J
    _ = ∑ θ : TVals, (runtimeR m0Q).totalWeight .instruments
          (fun i σ ↦ ∑ J : Fin encodingAttemptLimit, kWt (firstKU J.val i) σ)
            (prefixQ pol A θ) initQ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun θ _ ↦ (totalWeight_fintype_sum (runtimeR m0Q)
          .instruments (fun (J : Fin encodingAttemptLimit) i ↦ kWt (firstKU J.val i))
          (prefixQ pol A θ) initQ).symm
    _ ≤ ∑ _θ : TVals, (2 ^ 128 : ℝ≥0∞)⁻¹ * q := Finset.sum_le_sum fun θ _ ↦ by
        refine (totalWeight_le_totalWeight (runtimeR m0Q) .instruments
          (fun i σ hσ ↦ sum_kWt_firstKU_le i σ hσ) _ initQ_posSemidef).trans ?_
        rw [totalWeight_const_mul_weight (runtimeR m0Q) .instruments (2 ^ 128 : ℝ≥0∞)⁻¹ dropQWU
          (prefixQ pol A θ) initQ]
        exact mul_le_mul_of_nonneg_left (totalWeight_dropQW_le hpol A θ (hq θ)) zero_le
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end Quantum.Qrom.Sphincs

end
