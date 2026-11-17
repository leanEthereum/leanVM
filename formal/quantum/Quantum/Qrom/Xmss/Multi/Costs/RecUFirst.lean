module

public import Quantum.Qrom.Xmss.Multi.Costs.RecUMove
public import Quantum.Qrom.Xmss.Costs.RecUFirst

@[expose] public section

/-!
# The first reveals of the `n` users' randomizer bases

The `n`-user analog of `Quantum.Qrom.Xmss.Costs.RecUFirst`. At a first reveal of user `i`'s base
`(i, loC rnd)` the run before it does not depend on `θ (i, loC rnd)`, so summed over the hidden
values the recorded trial cells of `(i, rnd)`'s search count each recorded cell once per trial.

* **Trial cells name their search and user** (`IsBlkQN`, `isBlkQN_unique`): under distinct
  parameters `P`, a message-digest cell names the user (its parameter) and the position `rnd`.
  Two users with one parameter share their trial cells (and a search of one records cells the
  other's first reveal hits), so the first-reveal sum is stated on distinct parameters.
* **The potential `Ψ`** (`revPotQN P`): the recorded `h`-cells that are trial cells of a search
  `(i, rnd)` whose base is unrevealed; with distinct parameters it is one-cell Lipschitz, the
  searches' reads and the programs do not raise it, and a first reveal of `(i, rnd)` lowers it by
  the recorded trial cells of `(i, rnd)` (`revDropQN`). Along the prefix the drops add up to at
  most the sponge calls `q` (`totalWeight_dropQWN_le`).
* **The view lemma with a weight per hidden value** (`sum_queryWeight_view_le_wtN`): Disclose's
  count where the bound `κ v` may depend on the hidden values (here through the parameters).
* **The first reveals** (`sum_firstMaskN_le`): on distinct parameters, summed over the hidden
  values, at most `2^32 · q / 2^128` per hidden value.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

universe u v w u₁ v₁

namespace Quantum.Qrom.Xmss.Multi

open Quantum QuantumRuntime Quantum.Sponge HashSig LeanXmss
open Quantum.Xmss.Hybrid (diagMass Agree ViewByOn lazy_const suppAt_empty sum_agree_eq
  card_mul_sum_agree_mem diagMass_eq_sum_label queryWeight_fintype_sum queryWeight_zero_weight
  totalWeight_le_totalWeight totalWeight_fintype_sum totalWeight_const_mul_weight
  totalWeight_chargeTrace_le)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT extCls ModedP recKraus initU
  forallQueries_of_modedP totalWeight_le_potential_of_forallQueries tsum_potential_sponge_le
  tsum_potential_le_of_keep potential_basis_init potential_diagPot_sqrt kWt
  viewBy_runtimeR_of_disc eq_of_recKraus_ne_zero querySupportedOn_traceRight cw_clsKraus_ne_zero
  cw_readKrausH_ne_zero card_filter_le_of_injective)

attribute [local irreducible] xmssRom

/- Instance search for the register's decidable equality exceeds the default size. -/
set_option synthInstance.maxSize 2000

variable {n : ℕ}

/-! ## Trial cells name their search and user -/

/-- **A trial cell of user `k.1`'s search of `k.2`** under the parameters `P`: a message-digest
cell of the search's key and message under `P k.1`, at any randomizer. -/
def IsBlkQN (P : Fin n → PublicParameter) (k : Fin n × Pos) (x : HashDomain) : Prop :=
  ∃ l e msg, rndLab k.2 = some (l, e, msg) ∧
    ∃ r : Randomizer, x = cell (P k.1) (.msg l e) (msg, r)

theorem isBlkQ_of_isBlkQN {P : Fin n → PublicParameter} {k : Fin n × Pos} {x : HashDomain}
    (h : IsBlkQN P k x) : IsBlkQ k.2 x := by
  obtain ⟨l, e, msg, hr, r, rfl⟩ := h
  exact ⟨l, e, msg, hr, P k.1, r, rfl⟩

/-- **A trial cell names its search and user**, under distinct parameters. -/
theorem isBlkQN_unique {P : Fin n → PublicParameter} (hP : Function.Injective P)
    {k k' : Fin n × Pos} {x : HashDomain} (h : IsBlkQN P k x) (h' : IsBlkQN P k' x) : k = k' := by
  have hr := isBlkQ_unique (isBlkQ_of_isBlkQN h) (isBlkQ_of_isBlkQN h')
  obtain ⟨l, e, msg, -, r, rfl⟩ := h
  obtain ⟨l', e', msg', -, r', he⟩ := h'
  exact Prod.ext (hP (param_eq_of_cell_msg he)) hr

theorem isBlkQN_rndCell {P : Fin n → PublicParameter} {rnd : Pos} {l : Layer} {e : KeyIndex}
    {msg : MsgBytes} (hr : rndLab rnd = some (l, e, msg)) (i : Fin n) (b : Randomizer) (j : ℕ) :
    IsBlkQN P (i, rnd) (rndCell (P i) rnd b j) := by
  rw [rndCell_eq hr]
  exact ⟨l, e, msg, hr, _, rfl⟩

/-! ## The potential `Ψ` -/

open scoped Classical in
/-- The unrevealed searches (under the label `L`) of which `x` is a trial cell. -/
noncomputable def blkCntQN (P : Fin n → PublicParameter) (L : Finset (HPosN n))
    (x : HashDomain) : ℝ :=
  ∑ k : Fin n × Pos, if (k.1, loC k.2) ∉ L ∧ IsBlkQN P k x then 1 else 0

open scoped Classical in
/-- **The potential `Ψ`**: the recorded `h`-cells that are trial cells of unrevealed searches. -/
noncomputable def revPotQN (P : Fin n → PublicParameter) (s : RRegN n (SelMemN n)) : ℝ :=
  ∑ x : HashDomain, if s.1.1 x ≠ none then blkCntQN P s.2.2.1 x else 0

open scoped Classical in
/-- `Ψ` with the cell `z` counted as recorded. -/
noncomputable def revPotAtQN (P : Fin n → PublicParameter) (z : HashDomain)
    (s : RRegN n (SelMemN n)) : ℝ :=
  ∑ x : HashDomain, if x = z then blkCntQN P s.2.2.1 z else
    if s.1.1 x ≠ none then blkCntQN P s.2.2.1 x else 0

open scoped Classical in
/-- The recorded trial cells of the search `k`. -/
noncomputable def blkRecQN (P : Fin n → PublicParameter) (k : Fin n × Pos)
    (s : RRegN n (SelMemN n)) : ℕ :=
  (Finset.univ.filter fun x : HashDomain ↦ s.1.1 x ≠ none ∧ IsBlkQN P k x).card

open scoped Classical in
/-- **The drop of `Ψ` at a first reveal of the search `k`**: its recorded trial cells. -/
noncomputable def revDropQN (P : Fin n → PublicParameter) (k : Fin n × Pos)
    (s : RRegN n (SelMemN n)) : ℝ :=
  if (k.1, loC k.2) ∈ s.2.2.1 then 0 else (blkRecQN P k s : ℝ)

variable {P : Fin n → PublicParameter}

theorem blkCntQN_nonneg (L : Finset (HPosN n)) (x : HashDomain) : 0 ≤ blkCntQN P L x :=
  Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> norm_num

theorem blkCntQN_le_one (hP : Function.Injective P) (L : Finset (HPosN n)) (x : HashDomain) :
    blkCntQN P L x ≤ 1 := by
  classical
  unfold blkCntQN
  by_cases h : ∃ k, IsBlkQN P k x
  · obtain ⟨k₀, hk₀⟩ := h
    rw [Finset.sum_eq_single k₀ (fun k _ hne ↦ ite_eq_right fun hc ↦
      hne (isBlkQN_unique hP hc.2 hk₀)) (fun h ↦ absurd (Finset.mem_univ _) h)]
    split_ifs <;> norm_num
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun k _ ↦ ite_eq_right fun hc ↦ h ⟨k, hc.2⟩)
      zero_le_one

theorem blkCntQN_eq_zero (hP : Function.Injective P) {L : Finset (HPosN n)} {k : Fin n × Pos}
    {x : HashDomain} (hx : IsBlkQN P k x) (hL : (k.1, loC k.2) ∈ L) : blkCntQN P L x = 0 := by
  classical
  exact Finset.sum_eq_zero fun _ _ ↦ ite_eq_right fun hc ↦
    hc.1 (isBlkQN_unique hP hx hc.2 ▸ hL)

theorem revPotQN_nonneg (s : RRegN n (SelMemN n)) : 0 ≤ revPotQN P s :=
  Finset.sum_nonneg fun x _ ↦ by
    split_ifs
    · exact blkCntQN_nonneg _ x
    · exact le_rfl

theorem revPotQN_congr {s s' : RRegN n (SelMemN n)} (hk : s'.1.1 = s.1.1)
    (hl : s'.2.2.1 = s.2.2.1) : revPotQN P s' = revPotQN P s := by
  unfold revPotQN
  rw [hk, hl]

theorem revPotQN_le_revPotAtQN (z : HashDomain) (s : RRegN n (SelMemN n)) :
    revPotQN P s ≤ revPotAtQN P z s :=
  Finset.sum_le_sum fun x _ ↦ by
    by_cases hx : x = z
    · subst hx
      rw [ite_eq_left rfl]
      split_ifs
      · exact le_rfl
      · exact blkCntQN_nonneg _ x
    · rw [ite_eq_right hx]

theorem revPotAtQN_eq (hP : Function.Injective P) {z : HashDomain} {k : Fin n × Pos}
    (hz : IsBlkQN P k z) {s : RRegN n (SelMemN n)} (hs : (k.1, loC k.2) ∈ s.2.2.1) :
    revPotAtQN P z s = revPotQN P s :=
  Finset.sum_congr rfl fun x _ ↦ by
    by_cases hx : x = z
    · subst hx
      rw [ite_eq_left rfl, blkCntQN_eq_zero hP hz hs]
      split_ifs <;> rfl
    · rw [ite_eq_right hx]

theorem revPotAtQN_congr (z : HashDomain) {s s' : RRegN n (SelMemN n)}
    (hk : ∀ x, x ≠ z → s'.1.1 x = s.1.1 x) (hl : s'.2.2.1 = s.2.2.1) :
    revPotAtQN P z s' = revPotAtQN P z s :=
  Finset.sum_congr rfl fun x _ ↦ by
    rw [hl]
    by_cases hx : x = z
    · rw [ite_eq_left hx, ite_eq_left hx]
    · rw [ite_eq_right hx, ite_eq_right hx, hk x hx]

/-- **`Ψ` is one-cell Lipschitz** under distinct parameters. -/
theorem oneCellLipschitz_revPotQN (hP : Function.Injective P) :
    OneCellLipschitz (X := HashOutput) (Z := HashDomain) (M := QMemN n) (revPotQN P) where
  h D b z v := by
    classical
    set f : HashDomain → ℝ := fun x ↦ if D.1 x ≠ none then blkCntQN P b.2.1 x else 0
    set f' : HashDomain → ℝ := fun x ↦
      if Function.update D.1 z v x ≠ none then blkCntQN P b.2.1 x else 0
    have hd : ∑ x, (f' x - f x) = f' z - f z :=
      Finset.sum_eq_single z (fun x _ hx ↦ by simp [f, f', Function.update_of_ne hx])
        (fun h ↦ absurd (Finset.mem_univ z) h)
    have hf' : f' z ≤ 1 := by
      simp only [f']
      split_ifs
      · exact blkCntQN_le_one hP _ z
      · exact zero_le_one
    have hf : 0 ≤ f z := by
      simp only [f]
      split_ifs
      · exact blkCntQN_nonneg _ z
      · exact le_rfl
    show ∑ x, f' x ≤ ∑ x, f x + 1
    rw [Finset.sum_sub_distrib] at hd
    linarith
  k _ _ _ _ := le_of_eq_of_le (revPotQN_congr rfl rfl) (le_add_of_nonneg_right zero_le_one)
  k' _ _ _ _ := le_of_eq_of_le (revPotQN_congr rfl rfl) (le_add_of_nonneg_right zero_le_one)

/-- **A program does not raise `Ψ`**: it discards its cell from the databases. -/
theorem revPotQN_progMap_le (c : HwProg HashOutput HashDomain) (s : RRegN n (SelMemN n)) :
    revPotQN P (progMap c s) ≤ revPotQN P s := by
  obtain ⟨⟨dh, dk, dk'⟩, W, ⟨L, m⟩⟩ := s
  rcases c with ⟨z, w⟩ | ⟨x, w⟩ | ⟨x, w⟩
  · refine Finset.sum_le_sum fun y _ ↦ ?_
    show (if Function.update dh z none y ≠ none then blkCntQN P L y else 0) ≤
      if dh y ≠ none then blkCntQN P L y else 0
    by_cases hy : y = z
    · subst hy
      rw [Function.update_self, ite_eq_right (fun h ↦ h rfl)]
      split_ifs
      · exact blkCntQN_nonneg _ y
      · exact le_rfl
    · rw [Function.update_of_ne hy]
  · exact le_of_eq (revPotQN_congr rfl rfl)
  · exact le_of_eq (revPotQN_congr rfl rfl)

theorem blkCntQN_union_le (T T' : Finset (HPosN n)) (x : HashDomain) :
    blkCntQN P (T ∪ T') x ≤ blkCntQN P T x :=
  Finset.sum_le_sum fun k _ ↦ by
    by_cases h : (k.1, loC k.2) ∉ T ∪ T' ∧ IsBlkQN P k x
    · rw [ite_eq_left h, ite_eq_left ⟨fun hl ↦ h.1 (Finset.mem_union_left _ hl), h.2⟩]
    · rw [ite_eq_right h]
      split_ifs <;> norm_num

open scoped Classical in
theorem ind_add_blkCntQN_le {T : Finset (HPosN n)} {k : Fin n × Pos} (hl : (k.1, loC k.2) ∉ T)
    (x : HashDomain) :
    (if IsBlkQN P k x then (1 : ℝ) else 0) + blkCntQN P (T ∪ atU k.1 {loC k.2}) x ≤
      blkCntQN P T x := by
  classical
  unfold blkCntQN
  have h1 : (if IsBlkQN P k x then (1 : ℝ) else 0) =
      ∑ r : Fin n × Pos, if r = k then (if (r.1, loC r.2) ∉ T ∧ IsBlkQN P r x then 1 else 0)
        else 0 := by
    rw [Finset.sum_ite_eq' Finset.univ k, ite_eq_left (Finset.mem_univ _)]
    by_cases hb : IsBlkQN P k x
    · rw [ite_eq_left hb, ite_eq_left ⟨hl, hb⟩]
    · rw [ite_eq_right hb, ite_eq_right fun h ↦ hb h.2]
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun r _ ↦ ?_
  by_cases hr : r = k
  · subst hr
    have h0 : ¬((r.1, loC r.2) ∉ T ∪ atU r.1 {loC r.2} ∧ IsBlkQN P r x) :=
      fun h ↦ h.1 (Finset.mem_union_right _ (mk_mem_atU _ (Finset.mem_singleton_self _)))
    rw [ite_eq_left rfl, ite_eq_right h0, add_zero]
  · rw [ite_eq_right hr, zero_add]
    by_cases h : (r.1, loC r.2) ∉ T ∪ atU k.1 {loC k.2} ∧ IsBlkQN P r x
    · rw [ite_eq_left h, ite_eq_left ⟨fun hl' ↦ h.1 (Finset.mem_union_left _ hl'), h.2⟩]
    · rw [ite_eq_right h]
      split_ifs <;> norm_num

variable (P) in
/-- The drop at a record of `T`: a first reveal's recorded trial cells, nothing otherwise. -/
noncomputable def revDropOQN (T : Finset (HPosN n)) (s : RRegN n (SelMemN n)) : ℝ :=
  match rndOfTN T with
  | some k => revDropQN P k s
  | none => 0

theorem revDropOQN_nonneg (T : Finset (HPosN n)) (s : RRegN n (SelMemN n)) :
    0 ≤ revDropOQN P T s := by
  unfold revDropOQN
  split
  · unfold revDropQN
    split_ifs
    · exact le_rfl
    · exact Nat.cast_nonneg _
  · exact le_rfl

theorem revDropOQN_of_some {T : Finset (HPosN n)} {k : Fin n × Pos} (hT : rndOfTN T = some k)
    (s : RRegN n (SelMemN n)) : revDropOQN P T s = revDropQN P k s := by
  unfold revDropOQN
  rw [hT]

theorem revDropOQN_of_none {T : Finset (HPosN n)} (hT : rndOfTN T = none)
    (s : RRegN n (SelMemN n)) : revDropOQN P T s = 0 := by
  unfold revDropOQN
  rw [hT]

/-- **A record drops `Ψ` by at least the first-reveal drop.** -/
theorem revDropOQN_add_le (T : Finset (HPosN n)) (s : RRegN n (SelMemN n)) :
    revDropOQN P T s + revPotQN P (recMapQ T s) ≤ revPotQN P s := by
  classical
  obtain ⟨D, W, ⟨L, m⟩⟩ := s
  have hle : revPotQN P (recMapQ T (D, W, (L, m))) ≤ revPotQN P (D, W, (L, m)) :=
    Finset.sum_le_sum fun y _ ↦ by
      show (if D.1 y ≠ none then blkCntQN P (L ∪ T) y else 0) ≤
        if D.1 y ≠ none then blkCntQN P L y else 0
      split_ifs
      · exact blkCntQN_union_le L T y
      · exact le_rfl
  rcases ho : rndOfTN T with _ | ⟨i, rnd⟩
  · rw [revDropOQN_of_none ho, zero_add]
    exact hle
  · rw [revDropOQN_of_some ho]
    unfold revDropQN
    split_ifs with hl
    · rw [zero_add]
      exact hle
    · have hT : T = atU i {loC rnd} := (rndOfTN_spec ho).2
      subst hT
      show ((Finset.univ.filter fun y : HashDomain ↦ D.1 y ≠ none ∧
          IsBlkQN P (i, rnd) y).card : ℝ) +
        ∑ y : HashDomain, (if D.1 y ≠ none then blkCntQN P (L ∪ atU i {loC rnd}) y else 0) ≤
          ∑ y : HashDomain, if D.1 y ≠ none then blkCntQN P L y else 0
      rw [Finset.card_filter, Nat.cast_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun y _ ↦ ?_
      by_cases hD : D.1 y ≠ none
      · rw [ite_eq_left hD, ite_eq_left hD]
        have h := ind_add_blkCntQN_le (P := P) (k := (i, rnd)) hl y
        by_cases hb : IsBlkQN P (i, rnd) y
        · rw [ite_eq_left hb] at h
          rw [ite_eq_left ⟨hD, hb⟩, Nat.cast_one]
          exact h
        · rw [ite_eq_right hb] at h
          rw [ite_eq_right fun h' ↦ hb h'.2, Nat.cast_zero]
          exact h
      · rw [ite_eq_right hD, ite_eq_right hD, ite_eq_right fun h ↦ hD h.1, Nat.cast_zero,
          zero_add]

/-! ## `Ψ` along the prefix -/

/-- **The label invariant of the searches**: in the search of `(i, rnd)`, its base is
revealed. -/
def labInvQN : SrchModeN n → Set (RRegN n (SelMemN n))
  | .free => Set.univ
  | .grd i rnd _ _ => {s | (i, loC rnd) ∈ s.2.2.1}

/-- **The allowed calls keep the label invariant.** -/
theorem labInvQN_step (θ : HPosN n → Digest) (μ : SrchModeN n)
    (i : (RSpecN n (SelMemN n)).Port) (r : (RSpecN n (SelMemN n)).Result i)
    (σ : Matrix ((RSpecN n (SelMemN n)).In i × (runtimeR (m0N (n := n))).D)
      ((RSpecN n (SelMemN n)).In i × (runtimeR (m0N (n := n))).D) ℂ)
    (hok : srchOkZN P μ i)
    (hσ : QuerySupportedOn (fun m : (RSpecN n (SelMemN n)).In i × (runtimeR (m0N (n := n))).D ↦
      m.2) (labInvQN μ) σ) :
    QuerySupportedOn (fun m : (RSpecN n (SelMemN n)).Out i × (runtimeR (m0N (n := n))).D ↦ m.2)
      (labInvQN (srchNxZN θ μ i r)) (((runtimeR (m0N (n := n))).step i).branch r σ) := by
  rcases i with ((i | c) | c) | T
  · exact querySupportedOn_univ _ _
  · rcases μ with _ | ⟨i', rnd, b, j⟩
    · exact hok.elim
    have hb : ((runtimeR (m0N (n := n))).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty HashOutput HashDomain)
        m0N c r) σ
    rw [hb]
    obtain ⟨-, l, e, msg, -, rfl⟩ := hok
    refine hσ.conj fun q' q hK hq ↦ ?_
    obtain ⟨-, hK'⟩ := one_kronecker_ne_zero (a := q.1) (a' := q'.1) (b := q.2) (b' := q'.2) hK
    obtain ⟨hm, hm'⟩ := readKrausH_ne_zero_memN _ _ r hK'
    have hl : q'.2.2.2.1 = q.2.2.2.1 := by rw [hm', hm]; rfl
    show q'.2 ∈ labInvQN (match Codeword.decode (truncateHash (r.1.getD 0)) with
      | some _ => SrchModeN.free
      | none => SrchModeN.grd i' rnd b (j + 1))
    split
    · trivial
    · show (i', loC rnd) ∈ q'.2.2.2.1
      rw [hl]
      exact hq
  · exact querySupportedOn_univ _ _
  · rcases ho : rndOfTN T with _ | ⟨i', rnd⟩
    · have hn : srchNxZN θ μ (.inr T) r = .free := by
        show revNxQN T _ = _
        unfold revNxQN
        rw [ho]
      rw [hn]
      exact querySupportedOn_univ _ _
    · have hn : srchNxZN θ μ (.inr T) r = .grd i' rnd (θ (i', loC rnd)) 0 := by
        show revNxQN T _ = _
        unfold revNxQN
        rw [ho]
      have hT : T = atU i' {loC rnd} := (rndOfTN_spec ho).2
      rw [hn]
      refine QuerySupportedOn.conj (K := recKraus (X := HashOutput) (Z := HashDomain) T r) hσ
        fun q' q hK _ ↦ ?_
      rw [eq_of_recKraus_ne_zero (u := q.1) (u' := q'.1) (s := q.2) (s' := q'.2) hK]
      show (i', loC rnd) ∈ q.2.2.2.1 ∪ T
      rw [hT]
      exact Finset.mem_union_right _ (mk_mem_atU _ (Finset.mem_singleton_self _))

variable (P) in
/-- **The drops of `Ψ` at the record ports.** -/
noncomputable def dropQWN : ∀ i : (RSpecN n (SelMemN n)).Port,
    Matrix ((RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n))
      ((RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n)) ℂ → ℝ≥0∞
  | .inr T, σ => ENNReal.ofReal
      (∑ q : Unit × RRegN n (SelMemN n), revDropOQN P T q.2 * (σ q q).re)
  | _, _ => 0

/-- The traces at the sponge ports. -/
noncomputable def spongeTrQN (i : (RSpecN n (SelMemN n)).Port)
    (σ : Matrix ((RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n))
      ((RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n)) ℂ) : ℝ≥0∞ :=
  ((if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i then 0 else 1 :
    ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re

/-- **The step of `Ψ`**: a sponge call raises it by at most its trace; a search's read, a program
and a record do not raise it, a record lowering it by the first-reveal drop. -/
theorem revPotQN_step (hP : Function.Injective P) (i : (RSpecN n (SelMemN n)).Port)
    (σ : Matrix ((RSpecN n (SelMemN n)).In i × (runtimeR (m0N (n := n))).D)
      ((RSpecN n (SelMemN n)).In i × (runtimeR (m0N (n := n))).D) ℂ) (hσ : σ.PosSemidef)
    (hI : ∃ μ, srchOkZN P μ i ∧ QuerySupportedOn
      (fun m : (RSpecN n (SelMemN n)).In i × (runtimeR (m0N (n := n))).D ↦ m.2) (labInvQN μ) σ) :
    dropQWN P i σ + ∑' r, potential (diagPot fun s ↦ √(revPotQN P s))
        (((runtimeR (m0N (n := n))).step i).branch r σ) ≤
      potential (diagPot fun s ↦ √(revPotQN P s)) σ + spongeTrQN i σ := by
  have hφ0 : ∀ s, 0 ≤ revPotQN P s := revPotQN_nonneg
  rcases i with ((p | c) | c) | T
  · have hb : ∀ r : Unit, ((runtimeR (m0N (n := n))).step (.inl (.inl (.inl p)))).branch r σ =
        MatrixMap.conj ((spongeHardwired HashOutput HashDomain (hwEmpty HashOutput HashDomain)
          (m0N (n := n))).U p) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty HashOutput HashDomain)
        m0N p r) σ
    have hc : spongeTrQN (.inl (.inl (.inl p))) σ = ENNReal.ofReal σ.trace.re := by
      simp [spongeTrQN, extCls, hwCls]
      rfl
    rw [hc]
    show 0 + _ ≤ _
    rw [zero_add]
    exact (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans
      (tsum_potential_sponge_le hφ0 (oneCellLipschitz_revPotQN hP)
        (hwEmpty HashOutput HashDomain) m0N p hσ)
  · obtain ⟨μ, hok, hs⟩ := hI
    have hb : ∀ r, ((runtimeR (m0N (n := n))).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty HashOutput HashDomain)
        m0N c r) σ
    have hc : spongeTrQN (.inl (.inl (.inr c))) σ = 0 := by
      simp [spongeTrQN, extCls, hwCls]
    rw [hc, add_zero]
    show 0 + _ ≤ _
    rw [zero_add]
    refine (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans ?_
    show ∑' r : c.Result, potential (diagPot fun s ↦ √(revPotQN P s))
      (MatrixMap.conj (hwReadKraus c r) σ) ≤ _
    rcases μ with _ | ⟨i', rnd, b, j⟩
    · exact hok.elim
    obtain ⟨-, l, e, msg, hr, rfl⟩ := hok
    have hx : IsBlkQN P (i', rnd) (trialCell (P i') l e msg b j) := by
      have := isBlkQN_rndCell (P := P) hr i' b j
      rwa [rndCell_eq hr] at this
    refine tsum_potential_le_of_keep (fun r ↦ hwReadKraus (.readH (trialCell (P i') l e msg b j)
        (trialUpdN (trialCell (P i') l e msg b j) (i', l, e))) r) (sum_hwReadKraus _) hφ0
      (revPotQN_le_revPotAtQN (trialCell (P i') l e msg b j)) (fun r a a' h ↦ ?_) hσ
      (fun q hq ↦ (revPotAtQN_eq hP hx (hs q q hq).1).symm)
    obtain ⟨-, hK'⟩ := one_kronecker_ne_zero (a := a.1) (a' := a'.1) (b := a.2) (b' := a'.2) h
    obtain ⟨hm, hm'⟩ := readKrausH_ne_zero_memN _ _ r hK'
    exact revPotAtQN_congr _ (readKrausH_ne_zero_cellsN _ _ r hK') (by rw [hm', hm]; rfl)
  · have hb : ∀ r, ((runtimeR (m0N (n := n))).step (.inl (.inr c))).branch r σ =
        MatrixMap.conj (hwProgKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty HashOutput HashDomain)
        m0N c r) σ
    have hc : spongeTrQN (.inl (.inr c)) σ = 0 := by
      simp [spongeTrQN, extCls, hwCls]
    rw [hc, add_zero]
    show 0 + _ ≤ _
    rw [zero_add]
    refine (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans ?_
    refine (le_of_eq (tsum_potential_prog_eq hφ0 c hσ)).trans ?_
    refine le_of_le_of_eq ?_ (potential_diagPot_sqrt hφ0 σ).symm
    refine ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun q _ ↦ ?_)
    exact mul_le_mul_of_nonneg_right (revPotQN_progMap_le c q.2)
      (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  · have hc : spongeTrQN (.inr T) σ = 0 := by
      simp [spongeTrQN, extCls]
    rw [hc, add_zero]
    show ENNReal.ofReal (∑ q : Unit × RRegN n (SelMemN n), revDropOQN P T q.2 * (σ q q).re) +
      ∑' m, potential (diagPot fun s ↦ √(revPotQN P s))
        (MatrixMap.conj (recKraus (X := HashOutput) (Z := HashDomain) T m) σ) ≤ _
    rw [tsum_potential_rec_eqQ hφ0 T hσ]
    refine le_of_le_of_eq ?_ (potential_diagPot_sqrt hφ0 σ).symm
    have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    have h1 : 0 ≤ ∑ q : Unit × RRegN n (SelMemN n), revDropOQN P T q.2 * (σ q q).re :=
      Finset.sum_nonneg fun q _ ↦ mul_nonneg (revDropOQN_nonneg _ _) (hre q)
    have h2 : 0 ≤ ∑ q : Unit × RRegN n (SelMemN n), revPotQN P (recMapQ T q.2) * (σ q q).re :=
      Finset.sum_nonneg fun q _ ↦ mul_nonneg (hφ0 _) (hre q)
    refine (ENNReal.ofReal_add h1 h2).symm.trans_le (ENNReal.ofReal_le_ofReal ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (revDropOQN_add_le T q.2) (hre q)

/-- **The first-reveal drops of `Ψ` along a moded run**: at most the sponge charge, under distinct
parameters (the potential starts at `0`). -/
theorem totalWeight_dropQWN_le {Ω : QReg → Type} (hP : Function.Injective P)
    (θ : HPosN n → Digest) {fin : (Σ u, Ω u) → SrchModeN n → Prop}
    (x : QuantumComp LocalSig.instruments.{0} (RSpecN n (SelMemN n)) Ω (QReg.of Unit))
    (hx : ModedP (srchOkZN P) (srchNxZN θ) fin .free x) {q : ℕ}
    (hq : IFreeM.IsChargeBound x (portCharge fun i ↦
      if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i then 0 else 1)
      q) :
    (runtimeR (m0N (n := n))).totalWeight .instruments (dropQWN P) x initQN ≤ q := by
  have hφ0 : ∀ s, 0 ≤ revPotQN P s := revPotQN_nonneg
  have hfa := forallQueries_of_modedP (runtimeR (m0N (n := n))) .instruments labInvQN
    (fun μ i r σ hok h ↦ labInvQN_step θ μ i r σ hok h) x .free hx (ρ := initQN)
    (querySupportedOn_univ _ _)
  have h := totalWeight_le_potential_of_forallQueries (runtimeR (m0N (n := n))) .instruments
    (diagPot fun s ↦ √(revPotQN P s)) _
    (fun i σ ↦ ∃ μ, srchOkZN P μ i ∧ QuerySupportedOn
      (fun m : (RSpecN n (SelMemN n)).In i × (runtimeR (m0N (n := n))).D ↦ m.2) (labInvQN μ) σ)
    (fun i E σ hP' ↦ by
      obtain ⟨μ, hok, hs⟩ := hP'
      exact ⟨μ, hok, querySupportedOn_traceRight hs⟩)
    (dropQWN P) spongeTrQN (fun i σ hσ hI ↦ revPotQN_step hP i σ hσ hI) x initQN_posSemidef hfa
  have h0 : potential (diagPot fun s ↦ √(revPotQN P s)) (initQN (n := n)) = 0 := by
    unfold initQN initU
    rw [potential_basis_init m0N hφ0 ()]
    refine (congrArg ENNReal.ofReal (Finset.sum_eq_zero fun y _ ↦ ite_eq_right fun h ↦
      h rfl)).trans ENNReal.ofReal_zero
  refine h.trans ((add_le_add (le_of_eq h0) le_rfl).trans ?_)
  rw [zero_add]
  refine (totalWeight_chargeTrace_le (runtimeR (m0N (n := n))) .instruments _ x hq
    initQN_posSemidef).trans ?_
  calc (q : ℝ≥0∞) * ENNReal.ofReal (initQN (n := n)).trace.re ≤ q * 1 := by
        gcongr
        exact ofReal_trace_initQN_le_one
    _ = q := mul_one _

/-! ## Disclose's view lemma with a weight per hidden value -/

section viewV

variable {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)]

/-- **The count of a family of sources with a bound per family** (`sum_agree_and_le` with `κ`
depending on the family). -/
theorem sum_agree_and_le_wtN [∀ s, Nonempty (D s)] (T : Finset S) (v : (s : S) → D s)
    (Q : ((s : S) → D s) → Prop) [DecidablePred Q] (srcs : Finset S)
    (F : (s : S) → ((s : S) → D s) → Finset (D s))
    (hF : ∀ s u d, F s (Function.update u s d) = F s u)
    (hQ : ∀ u, Q u → ∃ s ∈ srcs, s ∉ T ∧ u s ∈ F s u) (κ : ((s : S) → D s) → ℝ≥0∞)
    (hκ : ∀ u, ∑ s ∈ srcs, ((F s u).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ u) :
    ∑ u, (if Agree T v u ∧ Q u then (1 : ℝ≥0∞) else 0) ≤
      ∑ u, if Agree T v u then κ u else 0 := by
  calc ∑ u, (if Agree T v u ∧ Q u then (1 : ℝ≥0∞) else 0)
      ≤ ∑ u, ∑ s ∈ srcs.filter (· ∉ T), (if Agree T v u ∧ u s ∈ F s u then 1 else 0) := by
        refine Finset.sum_le_sum fun u _ ↦ ?_
        split_ifs with h
        · obtain ⟨s, hs, hsT, hsF⟩ := hQ u h.2
          refine le_trans ?_ (Finset.single_le_sum
            (f := fun s ↦ if Agree T v u ∧ u s ∈ F s u then (1 : ℝ≥0∞) else 0)
            (fun _ _ ↦ by simp) (Finset.mem_filter.mpr ⟨hs, hsT⟩))
          simp [h.1, hsF]
        · simp
    _ = ∑ s ∈ srcs.filter (· ∉ T), ∑ u, (if Agree T v u ∧ u s ∈ F s u then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ s ∈ srcs.filter (· ∉ T), (Fintype.card (D s) : ℝ≥0∞)⁻¹ *
          ∑ u, (if Agree T v u then ((F s u).card : ℝ≥0∞) else 0) := by
        refine Finset.sum_congr rfl fun s hs ↦ ?_
        rw [← card_mul_sum_agree_mem T v (Finset.mem_filter.mp hs).2 (F s) (hF s), ← mul_assoc,
          ENNReal.inv_mul_cancel (by simp) (ENNReal.natCast_ne_top _), one_mul]
    _ = ∑ u, ∑ s ∈ srcs.filter (· ∉ T), (Fintype.card (D s) : ℝ≥0∞)⁻¹ *
          (if Agree T v u then ((F s u).card : ℝ≥0∞) else 0) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ u, if Agree T v u then ∑ s ∈ srcs.filter (· ∉ T),
          ((F s u).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ else 0 := by
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        by_cases h : Agree T v u
        · simp only [h, ↓reduceIte]
          exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
        · simp [h]
    _ ≤ ∑ u, if Agree T v u then κ u else 0 := by
        refine Finset.sum_le_sum fun u _ ↦ ?_
        split_ifs
        · exact (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans (hκ u)
        · exact le_rfl

/-- **The pointwise count with a weight per family.** -/
theorem sum_agree_diagMass_le_wtN [∀ s, Nonempty (D s)] {α : Type} [Fintype α]
    (lab : α → Finset S) (T : Finset S) (v : (s : S) → D s) (C : ((s : S) → D s) → Set α)
    (srcs : α → Finset S) (F : α → (s : S) → ((s : S) → D s) → Finset (D s))
    (hF : ∀ a s u d, F a s (Function.update u s d) = F a s u)
    (hsrc : ∀ u a, a ∈ C u → ∃ s ∈ srcs a, s ∉ lab a ∧ u s ∈ F a s u)
    (κ : ((s : S) → D s) → α → ℝ≥0∞)
    (hκ : ∀ a u, ∑ s ∈ srcs a,
      ((F a s u).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ u a) (σ : Matrix α α ℂ) :
    ∑ u, (if Agree T v u then diagMass (C u ∩ {a | lab a = T}) σ else 0) ≤
      ∑ u, if Agree T v u then kWt (fun a ↦ if lab a = T then κ u a else 0) σ else 0 := by
  classical
  simp only [diagMass, kWt]
  calc ∑ u, (if Agree T v u then
          ∑ a, (C u ∩ {a | lab a = T}).indicator (fun a ↦ ENNReal.ofReal (σ a a).re) a else 0)
      = ∑ a, ∑ u, (if Agree T v u then
          (C u ∩ {a | lab a = T}).indicator (fun a ↦ ENNReal.ofReal (σ a a).re) a else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        split_ifs <;> simp
    _ ≤ ∑ a, ∑ u, (if Agree T v u then
          (if lab a = T then κ u a else 0) * ENNReal.ofReal (σ a a).re else 0) := by
        refine Finset.sum_le_sum fun a _ ↦ ?_
        by_cases ha : lab a = T
        · calc ∑ u, (if Agree T v u then
                  (C u ∩ {a | lab a = T}).indicator (fun a ↦ ENNReal.ofReal (σ a a).re) a else 0)
              = ENNReal.ofReal (σ a a).re *
                  ∑ u, (if Agree T v u ∧ a ∈ C u then (1 : ℝ≥0∞) else 0) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun u _ ↦ ?_
                by_cases h1 : Agree T v u <;> by_cases h2 : a ∈ C u <;>
                  simp [h1, h2, ha]
            _ ≤ ENNReal.ofReal (σ a a).re * ∑ u, (if Agree T v u then κ u a else 0) :=
                mul_le_mul_of_nonneg_left (sum_agree_and_le_wtN T v (fun u ↦ a ∈ C u) (srcs a)
                  (F a) (hF a) (fun u hu ↦ by
                    obtain ⟨s, hs, hsl, hsF⟩ := hsrc u a hu
                    exact ⟨s, hs, ha ▸ hsl, hsF⟩) (fun u ↦ κ u a) (fun u ↦ hκ a u)) zero_le
            _ = _ := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun u _ ↦ ?_
                by_cases h1 : Agree T v u <;> simp [h1, ha, mul_comm]
        · refine le_of_eq_of_le (Finset.sum_eq_zero fun u _ ↦ ?_) zero_le
          split_ifs
          · exact Set.indicator_of_notMem (fun h ↦ ha h.2) _
          · rfl
    _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        split_ifs <;> simp

/-- Summing a function of the families agreeing with each family on `T`. -/
theorem mul_sum_eq_sum_agreeN (T : Finset S) (v₀ : (s : S) → D s)
    (f : ((s : S) → D s) → ℝ≥0∞) :
    (∑ u, if Agree T v₀ u then (1 : ℝ≥0∞) else 0) * ∑ u, f u =
      ∑ v, ∑ u, if Agree T v u then f u else 0 := by
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [← sum_agree_eq T u v₀, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have hs : Agree T u w ↔ Agree T w u := ⟨Agree.symm, Agree.symm⟩
  by_cases h : Agree T w u <;> simp [h, hs]

/-- The `κ`-weighted diagonal of a count of sets. -/
theorem kWt_mul_sum_indicatorN {α Y : Type} [Fintype α] [Fintype Y] (c : ℝ≥0∞)
    (B : Y → Set α) (σ : Matrix α α ℂ) :
    kWt (fun a ↦ c * ∑ y, (B y).indicator 1 a) σ = c * ∑ y, diagMass (B y) σ := by
  simp only [kWt, diagMass, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases ha : a ∈ B y
  · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha, Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha, mul_zero, zero_mul]

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {Ω : QReg → Type w} {A : QReg}

omit [Fintype S] [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
/-- **The lazy-sampling property for a count of sets** of states labelled `T`. -/
theorem queryWeight_kWt_viewN (lab : R.D → Finset S)
    (x : ((s : S) → D s) → QuantumComp L spec Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × R.D) (A × R.D) ℂ) (j : ℕ)
    (P : spec.Port → Prop) (hview : ViewByOn R I P lab x ρ j) {Y : Type} [Fintype Y]
    (c : ℝ≥0∞) (B : Y → ∀ i, Set (spec.In i × R.D)) (hBP : ∀ y i, ¬ P i → B y i = ∅)
    (κ : ∀ i, spec.In i × R.D → ℝ≥0∞) (hκB : ∀ i p, κ i p = c * ∑ y, (B y i).indicator 1 p)
    (T : Finset S) {v u : (s : S) → D s} (h : Agree T v u) :
    R.queryWeight I (fun i ↦ kWt (fun p ↦ if lab p.2 = T then κ i p else 0)) (x u) (ρ u) j =
      R.queryWeight I (fun i ↦ kWt (fun p ↦ if lab p.2 = T then κ i p else 0)) (x v) (ρ v) j := by
  have hw : (fun i ↦ kWt (fun p : spec.In i × R.D ↦ if lab p.2 = T then κ i p else 0)) =
      fun i σ ↦ c * ∑ y, diagMass (B y i ∩ {p | lab p.2 = T}) σ := by
    funext i σ
    rw [← kWt_mul_sum_indicatorN]
    refine congrArg (fun κ ↦ kWt κ σ) (funext fun p ↦ ?_)
    by_cases hp : lab p.2 = T
    · rw [ite_eq_left hp, hκB]
      refine congrArg (c * ·) (Finset.sum_congr rfl fun y _ ↦ ?_)
      by_cases hb : p ∈ B y i
      · rw [Set.indicator_of_mem hb,
          Set.indicator_of_mem (show p ∈ B y i ∩ {p | lab p.2 = T} from ⟨hb, hp⟩)]
      · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem fun h ↦ hb h.1]
    · rw [ite_eq_right hp]
      exact (mul_eq_zero_of_right c (Finset.sum_eq_zero fun y _ ↦
        Set.indicator_of_notMem (fun h ↦ hp h.2) _)).symm
  rw [hw, R.queryWeight_const_mul I c, R.queryWeight_const_mul I c, queryWeight_fintype_sum,
    queryWeight_fintype_sum]
  refine congrArg (c * ·) (Finset.sum_congr rfl fun y _ ↦ ?_)
  exact hview T u v h.symm (fun i ↦ B y i ∩ {p | lab p.2 = T}) (fun i p hp ↦ hp.2)
    fun i hi ↦ by rw [hBP y i hi, Set.empty_inter]

/-- **The view lemma at one label with a weight per hidden value.** -/
theorem sum_queryWeight_cut_le_wtN [∀ s, Nonempty (D s)] (lab : R.D → Finset S)
    (x : ((s : S) → D s) → QuantumComp L spec Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × R.D) (A × R.D) ℂ) (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ)
    (P : spec.Port → Prop) (hview : ViewByOn R I P lab x ρ j)
    (C : ((s : S) → D s) → ∀ i, Set (spec.In i × R.D)) (hCP : ∀ v i, ¬ P i → C v i = ∅)
    (srcs : ∀ i, spec.In i × R.D → Finset S)
    (F : ∀ i, spec.In i × R.D → (s : S) → ((s : S) → D s) → Finset (D s))
    (hF : ∀ i p s v d, F i p s (Function.update v s d) = F i p s v)
    (hsrc : ∀ v i p, p ∈ C v i → ∃ s ∈ srcs i p, s ∉ lab p.2 ∧ v s ∈ F i p s v)
    (κ : ((s : S) → D s) → ∀ i, spec.In i × R.D → ℝ≥0∞)
    (hκ : ∀ i p v, ∑ s ∈ srcs i p,
      ((F i p s v).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ v i p)
    (hκv : ∀ T v u, Agree T v u →
      R.queryWeight I (fun i ↦ kWt (fun p ↦ if lab p.2 = T then κ u i p else 0)) (x u) (ρ u) j =
        R.queryWeight I (fun i ↦ kWt (fun p ↦ if lab p.2 = T then κ u i p else 0)) (x v)
          (ρ v) j)
    (T : Finset S) :
    ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i ∩ {p | lab p.2 = T})) (x v) (ρ v) j ≤
      ∑ v, R.queryWeight I (fun i ↦ kWt (fun p ↦ if lab p.2 = T then κ v i p else 0))
        (x v) (ρ v) j := by
  classical
  obtain ⟨v₀⟩ : Nonempty ((s : S) → D s) := inferInstance
  have hN1 : 1 ≤ ∑ u, (if Agree T v₀ u then (1 : ℝ≥0∞) else 0) := by
    have h := Finset.single_le_sum (f := fun u ↦ if Agree T v₀ u then (1 : ℝ≥0∞) else 0)
      (fun _ _ ↦ by simp) (Finset.mem_univ v₀)
    simp only [show Agree T v₀ v₀ from fun _ _ ↦ rfl, ↓reduceIte] at h
    exact h
  have hN0 : (∑ u, if Agree T v₀ u then (1 : ℝ≥0∞) else 0) ≠ 0 :=
    (zero_lt_one.trans_le hN1).ne'
  have hNtop : (∑ u, if Agree T v₀ u then (1 : ℝ≥0∞) else 0) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun u _ ↦ by split_ifs <;> simp
  have hv : ∀ v, ∑ u, (if Agree T v u then
      R.queryWeight I (fun i ↦ diagMass (C u i ∩ {p | lab p.2 = T})) (x u) (ρ u) j else 0) ≤
        ∑ u, (if Agree T v u then R.queryWeight I
          (fun i ↦ kWt (fun p ↦ if lab p.2 = T then κ u i p else 0)) (x u) (ρ u) j else 0) := by
    intro v
    have hstep : ∀ u, (if Agree T v u then
        R.queryWeight I (fun i ↦ diagMass (C u i ∩ {p | lab p.2 = T})) (x u) (ρ u) j else 0) =
          R.queryWeight I (fun i σ ↦ if Agree T v u then
            diagMass (C u i ∩ {p | lab p.2 = T}) σ else 0) (x v) (ρ v) j := by
      intro u
      by_cases h : Agree T v u
      · simp only [h, ↓reduceIte]
        exact (hview T v u h (fun i ↦ C u i ∩ {p | lab p.2 = T}) (fun i p hp ↦ hp.2)
          fun i hi ↦ by rw [hCP u i hi, Set.empty_inter]).symm
      · simp only [h, ↓reduceIte]
        exact (queryWeight_zero_weight R I (x v) (ρ v) j).symm
    have hstep' : ∀ u, (if Agree T v u then R.queryWeight I
        (fun i ↦ kWt (fun p ↦ if lab p.2 = T then κ u i p else 0)) (x u) (ρ u) j else 0) =
          R.queryWeight I (fun i σ ↦ if Agree T v u then
            kWt (fun p ↦ if lab p.2 = T then κ u i p else 0) σ else 0) (x v) (ρ v) j := by
      intro u
      by_cases h : Agree T v u
      · simp only [h, ↓reduceIte]
        exact hκv T v u h
      · simp only [h, ↓reduceIte]
        exact (queryWeight_zero_weight R I (x v) (ρ v) j).symm
    simp only [hstep, hstep']
    rw [← queryWeight_fintype_sum, ← queryWeight_fintype_sum]
    refine R.queryWeight_mono I (fun i σ _ ↦ ?_) (x v) (hρ v) j
    exact sum_agree_diagMass_le_wtN (fun p : spec.In i × R.D ↦ lab p.2) T v (fun u ↦ C u i)
      (srcs i) (F i) (hF i) (fun u p hp ↦ hsrc u i p hp) (fun u ↦ κ u i) (fun p u ↦ hκ i p u) σ
  refine (ENNReal.mul_le_mul_iff_right hN0 hNtop).mp ?_
  rw [mul_sum_eq_sum_agreeN T v₀, mul_sum_eq_sum_agreeN T v₀]
  exact Finset.sum_le_sum fun v _ ↦ hv v

/-- **The adaptive view lemma with a weight per hidden value**: as Assembly's
`sum_queryWeight_view_le_wt`, with the bound `κ v` depending on the hidden values `v`, its
weights at the states labelled `T` seen alike by families agreeing on `T` (`hκv`). -/
theorem sum_queryWeight_view_le_wtN [∀ s, Nonempty (D s)] (lab : R.D → Finset S)
    (x : ((s : S) → D s) → QuantumComp L spec Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × R.D) (A × R.D) ℂ) (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ)
    (P : spec.Port → Prop) (hview : ViewByOn R I P lab x ρ j)
    (C : ((s : S) → D s) → ∀ i, Set (spec.In i × R.D)) (hCP : ∀ v i, ¬ P i → C v i = ∅)
    (srcs : ∀ i, spec.In i × R.D → Finset S)
    (F : ∀ i, spec.In i × R.D → (s : S) → ((s : S) → D s) → Finset (D s))
    (hF : ∀ i p s v d, F i p s (Function.update v s d) = F i p s v)
    (hsrc : ∀ v i p, p ∈ C v i → ∃ s ∈ srcs i p, s ∉ lab p.2 ∧ v s ∈ F i p s v)
    (κ : ((s : S) → D s) → ∀ i, spec.In i × R.D → ℝ≥0∞)
    (hκ : ∀ i p v, ∑ s ∈ srcs i p,
      ((F i p s v).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ v i p)
    (hκv : ∀ T v u, Agree T v u →
      R.queryWeight I (fun i ↦ kWt (fun p ↦ if lab p.2 = T then κ u i p else 0)) (x u) (ρ u) j =
        R.queryWeight I (fun i ↦ kWt (fun p ↦ if lab p.2 = T then κ u i p else 0)) (x v)
          (ρ v) j) :
    ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i)) (x v) (ρ v) j ≤
      ∑ v, R.queryWeight I (fun i ↦ kWt (κ v i)) (x v) (ρ v) j := by
  classical
  have hpart : ∀ v, R.queryWeight I (fun i ↦ diagMass (C v i)) (x v) (ρ v) j =
      ∑ T, R.queryWeight I (fun i ↦ diagMass (C v i ∩ {p | lab p.2 = T})) (x v) (ρ v) j :=
    fun v ↦ by
      rw [← queryWeight_fintype_sum]
      refine congrArg (fun w ↦ R.queryWeight I w (x v) (ρ v) j)
        (funext fun i ↦ funext fun σ ↦ ?_)
      exact diagMass_eq_sum_label (fun p ↦ lab p.2) (C v i) σ
  have hκpart : ∀ v, R.queryWeight I (fun i ↦ kWt (κ v i)) (x v) (ρ v) j =
      ∑ T, R.queryWeight I (fun i ↦ kWt (fun p ↦ if lab p.2 = T then κ v i p else 0))
        (x v) (ρ v) j :=
    fun v ↦ by
      rw [← queryWeight_fintype_sum]
      refine congrArg (fun w ↦ R.queryWeight I w (x v) (ρ v) j)
        (funext fun i ↦ funext fun σ ↦ ?_)
      simp only [kWt]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  calc ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i)) (x v) (ρ v) j
      = ∑ T, ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i ∩ {p | lab p.2 = T})) (x v)
          (ρ v) j := by
        simp only [hpart]
        exact Finset.sum_comm
    _ ≤ ∑ T, ∑ v, R.queryWeight I (fun i ↦ kWt (fun p ↦ if lab p.2 = T then κ v i p else 0))
          (x v) (ρ v) j :=
        Finset.sum_le_sum fun T _ ↦ sum_queryWeight_cut_le_wtN R I lab x ρ hρ j P hview C hCP
          srcs F hF hsrc κ hκ hκv T
    _ = _ := by
        rw [Finset.sum_comm]
        simp only [hκpart]

/-- **Summed weights per hidden value along runs**, call by call. -/
theorem sum_totalWeight_le_of_forallN {V : Type*} [Fintype V]
    (w c : V → ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (x : V → QuantumComp L spec Ω A) (ρ : V → Matrix (A × R.D) (A × R.D) ℂ)
    (h : ∀ j, ∑ v, R.queryWeight I (w v) (x v) (ρ v) j ≤
      ∑ v, R.queryWeight I (c v) (x v) (ρ v) j) :
    ∑ v, R.totalWeight I (w v) (x v) (ρ v) ≤ ∑ v, R.totalWeight I (c v) (x v) (ρ v) := by
  simp only [QuantumRuntime.totalWeight]
  rw [← Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable,
    ← Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
  exact ENNReal.tsum_le_tsum h

end viewV

/-! ## The first reveals, against `Ψ` -/

/-- User `i`'s parameter is the value of its parameter coordinate. -/
theorem parQN_apply (θ : HPosN n → Digest) (i : Fin n) : parQN θ i = θ (i, paramC) :=
  param_tabOf (userOf θ i)

theorem parQN_update (θ : HPosN n → Digest) {s : HPosN n} (hs : s.2 ≠ paramC) (d : Digest) :
    parQN (Function.update θ s d) = parQN θ :=
  funext fun i ↦ by
    rw [parQN_apply, parQN_apply, Function.update_of_ne]
    rintro rfl
    exact hs rfl

/-- The first-run states of trial `J` at the reveals, at the hidden values `θ`, on distinct
parameters. -/
def firstSetQN (θ : HPosN n → Digest) (J : ℕ) :
    ∀ i : (RSpecN n (SelMemN n)).Port,
      Set ((RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n))
  | .inr T => match rndOfTN T with
    | some k => {q | Function.Injective (parQN θ) ∧ (k.1, loC k.2) ∉ q.2.2.2.1 ∧
        q.2.1.1 (rndCell (parQN θ k.1) k.2 (θ (k.1, loC k.2)) J) ≠ none}
    | none => ∅
  | _ => ∅

/-- The source of a reveal: its base, if unrevealed. -/
noncomputable def firstSrcQN : ∀ i : (RSpecN n (SelMemN n)).Port,
    (RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n) → Finset (HPosN n)
  | .inr T, q => match rndOfTN T with
    | some k => if (k.1, loC k.2) ∈ q.2.2.2.1 then ∅ else {(k.1, loC k.2)}
    | none => ∅
  | _, _ => ∅

open scoped Classical in
/-- The source values of trial `J` at a reveal: the bases whose trial-`J` cell is recorded (the
parameters read off the hidden values with the source coordinate erased, if distinct). -/
noncomputable def firstFQN (J : ℕ) : ∀ i : (RSpecN n (SelMemN n)).Port,
    (RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n) → (s : HPosN n) →
      ((s : HPosN n) → Digest) → Finset Digest
  | .inr T, q => fun s v ↦ match rndOfTN T with
    | some k => if Function.Injective (parQN (Function.update v s 0)) then
        Finset.univ.filter fun b : Digest ↦
          q.2.1.1 (rndCell (parQN (Function.update v s 0) k.1) k.2 b J) ≠ none
      else ∅
    | none => ∅
  | _, _ => fun _ _ ↦ ∅

/-- The states of a reveal at which the cell `x` is a recorded trial cell of the revealed
unrevealed search, on distinct parameters. -/
def firstBN (v : HPosN n → Digest) (x : HashDomain) :
    ∀ i : (RSpecN n (SelMemN n)).Port,
      Set ((RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n))
  | .inr T => match rndOfTN T with
    | some k => {q | Function.Injective (parQN v) ∧ (k.1, loC k.2) ∉ q.2.2.2.1 ∧
        q.2.1.1 x ≠ none ∧ IsBlkQN (parQN v) k x}
    | none => ∅
  | _ => ∅

open scoped Classical in
/-- The weight per state of a reveal: its first-reveal drop over `|Digest|`, on distinct
parameters. -/
noncomputable def firstKQN (v : HPosN n → Digest) : ∀ i : (RSpecN n (SelMemN n)).Port,
    (RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n) → ℝ≥0∞
  | .inr T, q => if Function.Injective (parQN v) then
      (Fintype.card Digest : ℝ≥0∞)⁻¹ * ENNReal.ofReal (revDropOQN (parQN v) T q.2) else 0
  | _, _ => 0

theorem firstBN_of_some {T : Finset (HPosN n)} {k : Fin n × Pos} (hT : rndOfTN T = some k)
    (v : HPosN n → Digest) (x : HashDomain) :
    firstBN v x (.inr T) = {q : (RSpecN n (SelMemN n)).In (.inr T) × RRegN n (SelMemN n) |
      Function.Injective (parQN v) ∧ (k.1, loC k.2) ∉ q.2.2.2.1 ∧ q.2.1.1 x ≠ none ∧
        IsBlkQN (parQN v) k x} := by
  dsimp only [firstBN]
  rw [hT]

theorem firstBN_of_none {T : Finset (HPosN n)} (hT : rndOfTN T = none) (v : HPosN n → Digest)
    (x : HashDomain) : firstBN v x (.inr T) = ∅ := by
  dsimp only [firstBN]
  rw [hT]

theorem mem_firstBN {T : Finset (HPosN n)} {k : Fin n × Pos} (hT : rndOfTN T = some k)
    {v : HPosN n → Digest} {x : HashDomain}
    {q : (RSpecN n (SelMemN n)).In (.inr T) × RRegN n (SelMemN n)} :
    q ∈ firstBN v x (.inr T) ↔ Function.Injective (parQN v) ∧ (k.1, loC k.2) ∉ q.2.2.2.1 ∧
      q.2.1.1 x ≠ none ∧ IsBlkQN (parQN v) k x := by
  simp only [firstBN_of_some hT, Set.mem_ofPred_eq]

theorem injective_of_mem_firstBN {T : Finset (HPosN n)} {v : HPosN n → Digest}
    {x : HashDomain} {q : (RSpecN n (SelMemN n)).In (.inr T) × RRegN n (SelMemN n)}
    (h : q ∈ firstBN v x (.inr T)) : Function.Injective (parQN v) := by
  rcases hT : rndOfTN T with _ | k
  · rw [firstBN_of_none hT] at h
    exact absurd h (Set.notMem_empty q)
  · exact ((mem_firstBN hT).1 h).1

open scoped Classical in
theorem blkRecQN_eq_sum (P : Fin n → PublicParameter) (k : Fin n × Pos)
    (s : RRegN n (SelMemN n)) :
    ((blkRecQN P k s : ℕ) : ℝ≥0∞) =
      ∑ x : HashDomain, (if s.1.1 x ≠ none ∧ IsBlkQN P k x then (1 : ℝ≥0∞) else 0) := by
  unfold blkRecQN
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  split_ifs <;> simp

/-- **The weight per state as a count of sets.** -/
theorem firstKQN_eq (v : HPosN n → Digest) (i : (RSpecN n (SelMemN n)).Port)
    (q : (RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n)) :
    firstKQN v i q = (Fintype.card Digest : ℝ≥0∞)⁻¹ *
      ∑ x : HashDomain, (firstBN v x i).indicator 1 q := by
  classical
  rcases i with ((p | c) | c) | T
  · exact (mul_eq_zero_of_right _ (Finset.sum_eq_zero fun x _ ↦
      Set.indicator_of_notMem (Set.notMem_empty q) _)).symm
  · exact (mul_eq_zero_of_right _ (Finset.sum_eq_zero fun x _ ↦
      Set.indicator_of_notMem (Set.notMem_empty q) _)).symm
  · exact (mul_eq_zero_of_right _ (Finset.sum_eq_zero fun x _ ↦
      Set.indicator_of_notMem (Set.notMem_empty q) _)).symm
  · have hK : firstKQN v (.inr T) q = if Function.Injective (parQN v) then
        (Fintype.card Digest : ℝ≥0∞)⁻¹ * ENNReal.ofReal (revDropOQN (parQN v) T q.2) else 0 :=
      rfl
    rw [hK]
    by_cases hv : Function.Injective (parQN v)
    · rw [ite_eq_left hv]
      refine congrArg (fun t ↦ (Fintype.card Digest : ℝ≥0∞)⁻¹ * t) ?_
      rcases hT : rndOfTN T with _ | k
      · rw [revDropOQN_of_none hT, ENNReal.ofReal_zero]
        exact (Finset.sum_eq_zero fun x _ ↦ by
          rw [firstBN_of_none hT]
          exact Set.indicator_of_notMem (Set.notMem_empty q) _).symm
      · rw [revDropOQN_of_some hT]
        unfold revDropQN
        by_cases hl : (k.1, loC k.2) ∈ q.2.2.2.1
        · rw [ite_eq_left hl, ENNReal.ofReal_zero]
          exact (Finset.sum_eq_zero fun x _ ↦
            Set.indicator_of_notMem (fun h ↦ ((mem_firstBN hT).1 h).2.1 hl) _).symm
        · rw [ite_eq_right hl, ENNReal.ofReal_natCast, blkRecQN_eq_sum]
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          by_cases hx : q.2.1.1 x ≠ none ∧ IsBlkQN (parQN v) k x
          · rw [ite_eq_left hx, Set.indicator_of_mem ((mem_firstBN hT).2 ⟨hv, hl, hx⟩),
              Pi.one_apply]
          · rw [ite_eq_right hx,
              Set.indicator_of_notMem fun h ↦ hx ((mem_firstBN hT).1 h).2.2]
    · rw [ite_eq_right hv]
      exact (mul_eq_zero_of_right _ (Finset.sum_eq_zero fun x _ ↦
        Set.indicator_of_notMem (fun h ↦ hv (injective_of_mem_firstBN h)) _)).symm

theorem firstKQN_le (v : HPosN n → Digest) (T : Finset (HPosN n))
    (q : (RSpecN n (SelMemN n)).In (.inr T) × RRegN n (SelMemN n)) :
    firstKQN v (.inr T) q ≤
      (Fintype.card Digest : ℝ≥0∞)⁻¹ * ENNReal.ofReal (revDropOQN (parQN v) T q.2) := by
  classical
  show (if Function.Injective (parQN v) then
    (Fintype.card Digest : ℝ≥0∞)⁻¹ * ENNReal.ofReal (revDropOQN (parQN v) T q.2) else 0) ≤ _
  split_ifs
  · exact le_rfl
  · exact zero_le

theorem kWt_firstKQN_le (v : HPosN n → Digest) (i : (RSpecN n (SelMemN n)).Port)
    (σ : Matrix ((RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n))
      ((RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n)) ℂ) (hσ : σ.PosSemidef) :
    kWt (firstKQN v i) σ ≤ (Fintype.card Digest : ℝ≥0∞)⁻¹ * dropQWN (parQN v) i σ := by
  rcases i with ((p | c) | c) | T
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun _ _ ↦ zero_mul _) zero_le
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun _ _ ↦ zero_mul _) zero_le
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun _ _ ↦ zero_mul _) zero_le
  · have hre : ∀ q : (RSpecN n (SelMemN n)).In (.inr T) × RRegN n (SelMemN n),
        0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    have hR : (Fintype.card Digest : ℝ≥0∞)⁻¹ * ENNReal.ofReal
        (∑ q : (RSpecN n (SelMemN n)).In (.inr T) × RRegN n (SelMemN n),
          revDropOQN (parQN v) T q.2 * (σ q q).re) =
        ∑ q : (RSpecN n (SelMemN n)).In (.inr T) × RRegN n (SelMemN n),
          (Fintype.card Digest : ℝ≥0∞)⁻¹ * ENNReal.ofReal (revDropOQN (parQN v) T q.2) *
            ENNReal.ofReal (σ q q).re := by
      rw [ENNReal.ofReal_sum_of_nonneg fun q _ ↦ mul_nonneg (revDropOQN_nonneg _ _) (hre q),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [ENNReal.ofReal_mul (revDropOQN_nonneg _ _), mul_assoc]
    exact le_of_le_of_eq (Finset.sum_le_sum fun q _ ↦
      mul_le_mul_of_nonneg_right (firstKQN_le v T q) zero_le) hR.symm

theorem firstKQN_of_not (v : HPosN n → Digest) (hv : ¬ Function.Injective (parQN v))
    (i : (RSpecN n (SelMemN n)).Port) (q : (RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n)) :
    firstKQN v i q = 0 := by
  classical
  rcases i with ((p | c) | c) | T
  · rfl
  · rfl
  · rfl
  · show (if Function.Injective (parQN v) then
      (Fintype.card Digest : ℝ≥0∞)⁻¹ * ENNReal.ofReal (revDropOQN (parQN v) T q.2) else 0) = 0
    rw [ite_eq_right hv]

theorem card_firstFQN_le {T : Finset (HPosN n)} {i : Fin n} {rnd : Pos}
    (hT : rndOfTN T = some (i, rnd)) (J : ℕ) (s : RRegN n (SelMemN n)) (v : HPosN n → Digest)
    (hl : (i, loC rnd) ∉ s.2.2.1) :
    ((Finset.univ.filter fun b : Digest ↦
      s.1.1 (rndCell (parQN v i) rnd b J) ≠ none).card : ℝ≥0∞) ≤
        ENNReal.ofReal (revDropOQN (parQN v) T s) := by
  classical
  obtain ⟨⟨l, e, msg⟩, hr⟩ := Option.isSome_iff_exists.mp (rndOfTN_spec hT).1
  have hd : revDropQN (parQN v) (i, rnd) s = (blkRecQN (parQN v) (i, rnd) s : ℝ) :=
    ite_eq_right hl
  rw [revDropOQN_of_some hT, hd, ENNReal.ofReal_natCast]
  exact Nat.cast_le.mpr (card_filter_le_of_injective (rndCell_base_inj hr _ J) _ _
    fun b hb ↦ ⟨hb, isBlkQN_rndCell hr i b J⟩)

/-- **The view lemma at the first reveals, trial by trial.** -/
theorem sum_totalWeight_firstSetQN_le (A : MuAdversary n) (J : ℕ) :
    ∑ θ : HPosN n → Digest, (runtimeR (m0N (n := n))).totalWeight .instruments
        (fun i ↦ diagMass (firstSetQN θ J i)) (prefixQN A θ) initQN ≤
      ∑ θ : HPosN n → Digest, (runtimeR (m0N (n := n))).totalWeight .instruments
        (fun i ↦ kWt (firstKQN θ i)) (prefixQN A θ) initQN := by
  classical
  refine sum_totalWeight_le_of_forallN (runtimeR (m0N (n := n))) LocalSig.Interp.instruments
    _ _ _ _ fun j ↦ ?_
  have hview := (viewBy_runtimeR_of_disc LocalSig.Interp.instruments (m0N (n := n))
    (prefixTN (SelMemN n) cwUpdN A) ∅ (disc_prefixTN (SelMemN n) cwUpdN A ∅) (fun _ ↦ initQN)
    (lazy_const _ initQN) (fun _ ↦ suppAt_empty _ initQN) j).viewByOn fun _ ↦ True
  refine sum_queryWeight_view_le_wtN (runtimeR (m0N (n := n))) LocalSig.Interp.instruments
    (fun r ↦ r.2.2.1) (fun θ ↦ prefixQN A θ) (fun _ ↦ initQN) (fun _ ↦ initQN_posSemidef) j
    (fun _ ↦ True) hview (fun θ ↦ firstSetQN θ J) (fun _ _ h ↦ absurd trivial h) firstSrcQN
    (firstFQN J) (fun i p s v d ↦ ?_) (fun v i p hp ↦ ?_) firstKQN (fun i p v ↦ ?_)
    (fun T v u h ↦ ?_)
  · rcases i with ((i | c) | c) | T
    · rfl
    · rfl
    · rfl
    · dsimp only [firstFQN]
      rw [Function.update_idem]
  · rcases i with ((i | c) | c) | T
    · exact hp.elim
    · exact hp.elim
    · exact hp.elim
    · rcases hT : rndOfTN T with _ | ⟨i, rnd⟩
      · have hp' : p ∈ (∅ : Set ((RSpecN n (SelMemN n)).In (.inr T) × RRegN n (SelMemN n))) := by
          have h0 : firstSetQN v J (.inr T) = ∅ := by
            dsimp only [firstSetQN]
            rw [hT]
          rw [← h0]
          exact hp
        exact hp'.elim
      · have h0 : firstSetQN v J (.inr T) = {q | Function.Injective (parQN v) ∧
            (i, loC rnd) ∉ q.2.2.2.1 ∧
            q.2.1.1 (rndCell (parQN v i) rnd (v (i, loC rnd)) J) ≠ none} := by
          dsimp only [firstSetQN]
          rw [hT]
        have hp' : p ∈ {q : (RSpecN n (SelMemN n)).In (.inr T) × RRegN n (SelMemN n) |
            Function.Injective (parQN v) ∧ (i, loC rnd) ∉ q.2.2.2.1 ∧
            q.2.1.1 (rndCell (parQN v i) rnd (v (i, loC rnd)) J) ≠ none} := h0 ▸ hp
        have hne : (i, loC rnd).2 ≠ paramC := (paramC_ne_loC (rndOfTN_spec hT).1).symm
        refine ⟨(i, loC rnd), ?_, hp'.2.1, ?_⟩
        · have hs : firstSrcQN (.inr T) p =
              if (i, loC rnd) ∈ p.2.2.2.1 then ∅ else {(i, loC rnd)} := by
            dsimp only [firstSrcQN]
            rw [hT]
          rw [hs, ite_eq_right hp'.2.1]
          exact Finset.mem_singleton_self _
        · have hF : firstFQN J (.inr T) p (i, loC rnd) v =
              if Function.Injective (parQN (Function.update v (i, loC rnd) 0)) then
                Finset.univ.filter fun b : Digest ↦ p.2.1.1 (rndCell
                  (parQN (Function.update v (i, loC rnd) 0) i) rnd b J) ≠ none
              else ∅ := by
            dsimp only [firstFQN]
            rw [hT]
          rw [hF, parQN_update v hne, ite_eq_left hp'.1]
          exact mem_filter_univ_of' hp'.2.2
  · rcases i with ((i | c) | c) | T
    · exact le_of_eq_of_le Finset.sum_empty zero_le
    · exact le_of_eq_of_le Finset.sum_empty zero_le
    · exact le_of_eq_of_le Finset.sum_empty zero_le
    · rcases hT : rndOfTN T with _ | ⟨i, rnd⟩
      · have hs : firstSrcQN (.inr T) p = ∅ := by
          dsimp only [firstSrcQN]
          rw [hT]
        rw [hs, Finset.sum_empty]
        exact zero_le
      · have hs : firstSrcQN (.inr T) p =
            if (i, loC rnd) ∈ p.2.2.2.1 then ∅ else {(i, loC rnd)} := by
          dsimp only [firstSrcQN]
          rw [hT]
        by_cases hl : (i, loC rnd) ∈ p.2.2.2.1
        · rw [hs, ite_eq_left hl, Finset.sum_empty]
          exact zero_le
        · have hne : (i, loC rnd).2 ≠ paramC := (paramC_ne_loC (rndOfTN_spec hT).1).symm
          have hF : firstFQN J (.inr T) p (i, loC rnd) v =
              if Function.Injective (parQN (Function.update v (i, loC rnd) 0)) then
                Finset.univ.filter fun b : Digest ↦ p.2.1.1 (rndCell
                  (parQN (Function.update v (i, loC rnd) 0) i) rnd b J) ≠ none
              else ∅ := by
            dsimp only [firstFQN]
            rw [hT]
          have hK : firstKQN v (.inr T) p = if Function.Injective (parQN v) then
              (Fintype.card Digest : ℝ≥0∞)⁻¹ *
                ENNReal.ofReal (revDropOQN (parQN v) T p.2) else 0 := rfl
          rw [hs, ite_eq_right hl, Finset.sum_singleton, hF, parQN_update v hne, hK]
          by_cases hv : Function.Injective (parQN v)
          · rw [ite_eq_left hv, ite_eq_left hv, mul_comm]
            exact mul_le_mul_of_nonneg_left (card_firstFQN_le hT J p.2 v hl) zero_le
          · rw [ite_eq_right hv, ite_eq_right hv, Finset.card_empty, Nat.cast_zero, zero_mul]
  · exact queryWeight_kWt_viewN (runtimeR (m0N (n := n))) LocalSig.Interp.instruments
      (fun r ↦ r.2.2.1) (fun θ ↦ prefixQN A θ) (fun _ ↦ initQN) j (fun _ ↦ True) hview
      (Fintype.card Digest : ℝ≥0∞)⁻¹ (fun x ↦ firstBN u x) (fun _ _ h ↦ absurd trivial h)
      (firstKQN u) (firstKQN_eq u) T h

/-- **The first-reveal weights of one hidden value**: at most `q / 2^128`. -/
theorem totalWeight_kWt_firstKQN_le (A : MuAdversary n) (θ : HPosN n → Digest) {q : ℕ}
    (hq : IFreeM.IsChargeBound (prefixQN A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i then 0 else 1)
      q) :
    (runtimeR (m0N (n := n))).totalWeight .instruments (fun i ↦ kWt (firstKQN θ i))
      (prefixQN A θ) initQN ≤ (Fintype.card Digest : ℝ≥0∞)⁻¹ * q := by
  by_cases hθ : Function.Injective (parQN θ)
  · refine (totalWeight_le_totalWeight (runtimeR (m0N (n := n))) .instruments
      (fun i σ hσ ↦ kWt_firstKQN_le θ i σ hσ) _ initQN_posSemidef).trans ?_
    refine (le_of_eq (totalWeight_const_mul_weight (runtimeR (m0N (n := n))) .instruments
      (Fintype.card Digest : ℝ≥0∞)⁻¹ (dropQWN (parQN θ)) (prefixQN A θ) initQN)).trans ?_
    exact mul_le_mul_of_nonneg_left (totalWeight_dropQWN_le hθ θ (prefixQN A θ)
      (modedP_prefixQN A θ) hq) zero_le
  · refine (totalWeight_le_totalWeight (runtimeR (m0N (n := n))) .instruments
      (w' := fun _ _ ↦ 0) (fun i σ _ ↦ le_of_eq ?_) _ initQN_posSemidef).trans ?_
    · exact Finset.sum_eq_zero fun p _ ↦ mul_eq_zero_of_left (firstKQN_of_not θ hθ i p) _
    · exact (ENNReal.tsum_eq_zero.mpr fun j ↦ queryWeight_zero_weight _ _ _ _ j).trans_le zero_le

theorem firstQWN_eq_sumN {θ : HPosN n → Digest} (hθ : Function.Injective (parQN θ))
    (i : (RSpecN n (SelMemN n)).Port)
    (σ : Matrix ((RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n))
      ((RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n)) ℂ) :
    firstQWN θ i σ = ∑ J : Fin randomizerAttemptLimit, diagMass (firstSetQN θ J.val i) σ := by
  rcases i with ((p | c) | c) | T
  · exact (Finset.sum_eq_zero fun _ _ ↦ diagMass_zero_set σ).symm
  · exact (Finset.sum_eq_zero fun _ _ ↦ diagMass_zero_set σ).symm
  · exact (Finset.sum_eq_zero fun _ _ ↦ diagMass_zero_set σ).symm
  · rcases hT : rndOfTN T with _ | ⟨i, rnd⟩
    · have h1 : firstQWN θ (.inr T) σ = 0 := by
        dsimp only [firstQWN]
        rw [hT]
      have h2 : ∀ J : ℕ, firstSetQN θ J (.inr T) = ∅ := fun J ↦ by
        dsimp only [firstSetQN]
        rw [hT]
      rw [h1]
      simp only [h2]
      exact (Finset.sum_eq_zero fun _ _ ↦ diagMass_zero_set σ).symm
    · have h1 : firstQWN θ (.inr T) σ = ∑ J : Fin randomizerAttemptLimit,
          diagMass {q : (RSpecN n (SelMemN n)).In (.inr T) × RRegN n (SelMemN n) |
            (i, loC rnd) ∉ q.2.2.2.1 ∧
              q.2.1.1 (rndCell (parQN θ i) rnd (θ (i, loC rnd)) J) ≠ none} σ := by
        dsimp only [firstQWN]
        rw [hT]
        rfl
      have h2 : ∀ J : ℕ, firstSetQN θ J (.inr T) =
          {q : (RSpecN n (SelMemN n)).In (.inr T) × RRegN n (SelMemN n) |
            Function.Injective (parQN θ) ∧ (i, loC rnd) ∉ q.2.2.2.1 ∧
              q.2.1.1 (rndCell (parQN θ i) rnd (θ (i, loC rnd)) J) ≠ none} := fun J ↦ by
        dsimp only [firstSetQN]
        rw [hT]
      rw [h1]
      simp only [h2]
      exact Finset.sum_congr rfl fun J _ ↦ congrArg (fun S ↦ diagMass S σ)
        (Set.ext fun q ↦ ⟨fun h ↦ ⟨hθ, h⟩, fun h ↦ h.2⟩)

open scoped Classical in
/-- **The first-reveal charges of the hidden values `θ`, on distinct parameters.** -/
noncomputable def firstMaskN (A : MuAdversary n) (θ : HPosN n → Digest) : ℝ≥0∞ :=
  if PDistinct (tabOfN θ) then
    (runtimeR (m0N (n := n))).totalWeight .instruments (firstQWN θ) (prefixQN A θ) initQN
  else 0

/-- **The first-reveal charges, summed over the hidden values** (on distinct parameters): at most
`2^32 / 2^128` times the sponge charge per hidden value. -/
theorem sum_totalWeight_firstQWN_le (A : MuAdversary n) {q : ℕ}
    (hq : ∀ θ, IFreeM.IsChargeBound (prefixQN A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i then 0 else 1)
      q) :
    ∑ θ : HPosN n → Digest, firstMaskN A θ ≤
      (randomizerAttemptLimit : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ * q *
        Fintype.card (HPosN n → Digest) := by
  have hcard : (Fintype.card Digest : ℝ≥0∞)⁻¹ = (2 ^ 128 : ℝ≥0∞)⁻¹ := by
    rw [card_digest_recU]
    norm_num
  calc ∑ θ : HPosN n → Digest, firstMaskN A θ
      ≤ ∑ θ : HPosN n → Digest, ∑ J : Fin randomizerAttemptLimit,
          (runtimeR (m0N (n := n))).totalWeight .instruments
            (fun i ↦ diagMass (firstSetQN θ J.val i)) (prefixQN A θ) initQN :=
        Finset.sum_le_sum fun θ _ ↦ by
          classical
          unfold firstMaskN
          split_ifs with hθ
          · exact le_of_eq ((congrArg (fun w ↦ (runtimeR (m0N (n := n))).totalWeight
              .instruments w (prefixQN A θ) initQN)
              (funext fun i ↦ funext fun σ ↦ firstQWN_eq_sumN hθ i σ)).trans
              (totalWeight_fintype_sum (runtimeR (m0N (n := n))) .instruments
                (fun (J : Fin randomizerAttemptLimit) i ↦ diagMass (firstSetQN θ J.val i))
                (prefixQN A θ) initQN))
          · exact zero_le
    _ = ∑ J : Fin randomizerAttemptLimit, ∑ θ : HPosN n → Digest,
          (runtimeR (m0N (n := n))).totalWeight .instruments
            (fun i ↦ diagMass (firstSetQN θ J.val i)) (prefixQN A θ) initQN := Finset.sum_comm
    _ ≤ ∑ _J : Fin randomizerAttemptLimit, ∑ θ : HPosN n → Digest,
          (runtimeR (m0N (n := n))).totalWeight .instruments (fun i ↦ kWt (firstKQN θ i))
            (prefixQN A θ) initQN :=
        Finset.sum_le_sum fun J _ ↦ sum_totalWeight_firstSetQN_le A J.val
    _ ≤ ∑ _J : Fin randomizerAttemptLimit, ∑ _θ : HPosN n → Digest,
          (2 ^ 128 : ℝ≥0∞)⁻¹ * q :=
        Finset.sum_le_sum fun J _ ↦ Finset.sum_le_sum fun θ _ ↦ by
          rw [← hcard]
          exact totalWeight_kWt_firstKQN_le A θ (hq θ)
    _ = _ := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
        ring

end Quantum.Qrom.Xmss.Multi

end
