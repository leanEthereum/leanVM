module

public import Quantum.Qrom.Sphincs.Costs.Bound
public import Quantum.Qrom.Sphincs.Costs.EncRead

@[expose] public section

/-!
# The Enc weights of leanSPHINCS's challenge prefix

The Enc weights `encPre` (the codeword cells of the key's encoding slot at the empty read cells of
an unselected key, summed over the trial reads of the challenge prefix) are bounded by the joint
potential `encPotQ` (EncRead), CostJoint's telescoping on the calls of an invariant
(`totalWeight_le_potential_of_forallQueries`) with the invariant `PreInvQ` and the database grade
at most `q + K` (every port raises it by at most one: `querySupportedOn_runtimeR_stepE`,
`querySupportedOn_initQ_gradeE`). The leanSPHINCS counterpart of `Quantum.Qrom.Xmss` `Costs/Enc`.

* **`encPre_le_chargesE`**: at any public key `pk`, on calls satisfying `PreInvQ pk hon`,
  `2^-15 encPre ≤ q + 4 (q + K) recUPre + 2^-510 K` (sponge calls raise the potential by their
  trace, trial reads drop it by `2^-15 encWt` up to their charge, programs and records keep it).
* **`encPre_le`**: `encPre ≤ encCap encC encEps q K recUPre` with `encC = 2^15` (from
  `ρ_c ≥ 2^-14`) and `encEps = 2^-510` (re-compression of a cell of `2^512` pairs).
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Sphincs (Key)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR extWeight sumWeight extCls portCh
  PotLabelFree potential_diagPot_sqrt tsum_potential_recStep_diag tsum_potential_sponge_le
  totalWeight_le_potential_of_forallQueries potential_basis_init isChargeBound_mono_charge
  isChargeBound_zero forallQueries_of_charge_step forallQueries_and querySupportedOn_traceRight
  totalWeight_le_lin)
open Quantum.Xmss.Hybrid (totalWeight_le_totalWeight totalWeight_const_mul_weight
  totalWeight_trace_le_of_isChargeBound)

attribute [local irreducible] sphincsRom

-- Keep elaboration from unfolding `univ` of the large `Fin` types.
attribute [local irreducible] Fin.fintype

/- Instance search for the register with its trivial public register exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-! ## The constants -/

/-- **The Enc factor**: `2^15`, from the codeword fraction `ρ_c ≥ 2^-14`. -/
noncomputable def encC : ℝ≥0∞ :=
  2 ^ 15

/-- **The Enc re-compression fraction**: `2^-510 ≥ 2/|Y × Y| + 4/|Y × Y|²`. -/
noncomputable def encEps : ℝ≥0∞ :=
  (2 ^ 510)⁻¹

theorem encC_le : encC ≤ 2 ^ 15 :=
  le_rfl

theorem encEps_le : encEps ≤ (2 ^ 510)⁻¹ :=
  le_rfl

/-! ## The database grade at the calls -/

/-- **Every port of runtime 2 raises the database grade by at most one.** -/
theorem querySupportedOn_runtimeR_stepE
    (i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port)
    (r : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Result i) (t : ℕ)
    (σ : Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i ×
      (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D)
      ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i ×
        (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D) ℂ)
    (hσ : QuerySupportedOn (fun q : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i ×
      (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D ↦ dbGrade q.2.1) (Set.Iic t) σ) :
    QuerySupportedOn (fun q : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Out i ×
      (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D ↦ dbGrade q.2.1) (Set.Iic (t + 1))
        (((runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).step i).branch r σ) := by
  rcases i with i | j
  · exact querySupportedOn_spongeHardwiredRuntime_step (hwEmpty PairOut Qrom.HashDomain) m0Q i r
      t σ hσ
  · exact Quantum.Xmss.Assembly.querySupportedOn_recStep j r t σ hσ

/-- The initial state has empty databases. -/
theorem querySupportedOn_initQ_gradeE :
    QuerySupportedOn (fun m : QReg.of Unit ×
      (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D ↦ dbGrade m.2.1) (Set.Iic 0)
        initQ := by
  intro m m' hm
  change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty PairOut Qrom.HashDomain, m0Q) : RegQ)).matrix) m m' ≠ 0 at hm
  simp only [SubState.matrix_basis] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · constructor <;> simp [← he.1, ← he.2, dbGrade, Database.size_empty]
  · exact False.elim (h rfl)

/-! ## The potential at the start -/

theorem encPotQ_empty (pk : PublicKey) (m : QMem) :
    encPotQ pk (((Database.empty, Database.empty, Database.empty),
      hwEmpty PairOut Qrom.HashDomain, m) : RegQ) = 0 := by
  unfold encPotQ
  refine Finset.sum_eq_zero fun K _ ↦ ?_
  have h0 : encCwCount pk (unionH (((Database.empty, Database.empty, Database.empty),
      hwEmpty PairOut Qrom.HashDomain, m) : RegQ)) K = 0 := by
    have h := Quantum.Qrom.Xmss.cellOutCount_le_card (U := unionH (((Database.empty,
      Database.empty, Database.empty), hwEmpty PairOut Qrom.HashDomain, m) : RegQ))
      (P := fun x ↦ slotOf pk x = some (.enc K.1 K.2.1 K.2.2))
      (Qo := fun y ↦ Quantum.Sphincs.Codeword.Valid (pairDigest y)) (fun _ ↦ False)
      fun _ _ _ hy ↦ by cases hy
    rw [Finset.filter_false, Finset.card_empty] at h
    exact Nat.le_zero.mp h
  rw [h0]
  split_ifs <;> simp

/-! ## The Enc weights along the prefix -/

variable {pk : PublicKey} {hon : HonestCells}

variable (pk) in
/-- **The charges of the Enc potential**: the trace at the sponge ports; at a read port
`4 G recUWt` plus `2^-510` per unit of trace; nothing at the program and record ports. -/
noncomputable def encChgE (G : ℕ) :=
  portCh PairOut Qrom.HashDomain TPos SelMem (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
    (fun c σ ↦ 4 * (G : ℝ≥0∞) * trialW pk recUWt c σ +
      encEps * ENNReal.ofReal σ.trace.re) fun _ _ ↦ 0

/-- **The port conditions of the Enc potential**: on an input satisfying `PreInvQ pk hon` with
database grade at most `G`, the scaled Enc weight plus the potential after the call is at most the
potential before plus the charge `encChgE pk G`. -/
theorem encPotQ_port_leE {G : ℕ} (i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port)
    (σ : Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i ×
      (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D)
      ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i ×
        (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D) ℂ) (hσ : σ.PosSemidef)
    (hI : PreInvQ pk hon i σ ∧ QuerySupportedOn
      (fun m : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RegQ ↦ dbGrade m.2.1)
        (Set.Iic G) σ) :
    extWeight (hwCost (fun c σ ↦ (2 ^ 15 : ℝ≥0∞)⁻¹ * trialW pk (encWt pk) c σ)
        fun _ _ ↦ 0) i σ +
        ∑' r, potential (diagPot fun s ↦ √(encPotQ pk s))
          (((runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).step i).branch r σ) ≤
      potential (diagPot fun s ↦ √(encPotQ pk s)) σ + encChgE pk G i σ := by
  rcases i with ((p | c) | c) | T
  · have hbr : ∀ r : Unit, ((runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).step
        (.inl (.inl (.inl p)))).branch r σ =
        MatrixMap.conj ((spongeHardwired PairOut Qrom.HashDomain
          (hwEmpty PairOut Qrom.HashDomain) m0Q).U p) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty PairOut Qrom.HashDomain)
        m0Q p r) σ
    simp only [encChgE, portCh, extWeight, sumWeight, hwCost, zero_add]
    exact (le_of_eq (tsum_congr fun r ↦ congrArg _ (hbr r))).trans
      (tsum_potential_sponge_le encPotQ_nonneg oneCellLipschitz_encPotQ _ _ p hσ)
  · obtain ⟨⟨⟨z, K, hz, rfl⟩, hMF, hnb⟩, hgr⟩ := hI
    have hbr : ∀ r, ((runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).step
        (.inl (.inl (.inr (trialRead z K))))).branch r σ =
        MatrixMap.conj (hwReadKraus (trialRead z K) r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty PairOut Qrom.HashDomain)
        m0Q (trialRead z K) r) σ
    have hnb' : ReadNoBot (.readH z (trialUpdQ K z)) σ := readNoBot_of_noBot _ hnb
    have hsupp : ∀ a, σ a a ≠ 0 → EncFree pk a.2 ∧ dbGrade a.2.1 ≤ G := fun a ha ↦
      ⟨(hMF a a ha).1, Set.mem_Iic.mp (hgr a a ha).1⟩
    simp only [encChgE, portCh, extWeight, sumWeight, hwCost]
    exact (le_of_eq (congrArg (_ + ·) (tsum_congr fun r ↦ congrArg _ (hbr r)))).trans
      (trialRead_potential_leE hz hσ hnb' hsupp)
  · obtain ⟨⟨z, v, rfl, hz⟩, -, -⟩ := hI.1
    have hbr : ∀ r, ((runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).step
        (.inl (.inr (.programH z v)))).branch r σ =
        MatrixMap.conj (hwProgKraus (.programH z v) r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty PairOut Qrom.HashDomain)
        m0Q (.programH z v) r) σ
    simp only [encChgE, portCh, extWeight, sumWeight, hwCost, zero_add, add_zero]
    have hprog := tsum_potential_prog_eq (encPotQ_nonneg (pk := pk)) (.programH z v) hσ
    refine (le_of_eq ((tsum_congr fun r ↦ congrArg _ (hbr r)).trans hprog)).trans
      (le_of_eq ?_)
    refine Eq.trans ?_ (potential_diagPot_sqrt encPotQ_nonneg σ).symm
    exact congrArg ENNReal.ofReal (Finset.sum_congr rfl fun a _ ↦ by
      rw [encPotQ_progMap (not_enc_of_exemptCellE hz) v])
  · have hlab : PotLabelFree (X := PairOut) (Z := Qrom.HashDomain) (S := TPos) (M' := SelMem)
        (encPotQ pk) := fun _ _ _ _ _ ↦ encPotQ_congr rfl rfl
    simp only [encChgE, portCh, extWeight, sumWeight, zero_add, add_zero]
    exact tsum_potential_recStep_diag encPotQ_nonneg hlab T hσ

variable (pk) in
/-- **The Enc weights of the prefix, by the joint potential**: at the public key `pk`, with at
most `q` sponge and `K` classical calls, on calls satisfying `PreInvQ pk hon`,
`2^-15 encPre ≤ q + 4 (q + K) recUPre + 2^-510 K`. -/
theorem encPre_le_chargesE (pol : DigestPolicy) (A : SAdversary) (θ : TVals) {q K : ℕ}
    (hinv : PrefixInvQ pk hon pol A θ)
    (hq : IFreeM.IsChargeBound (prefixQ pol A θ) (portCharge fun i ↦
      if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 0 else 1) q)
    (hK : IFreeM.IsChargeBound (prefixQ pol A θ) (portCharge fun i ↦
      if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1 else 0) K) :
    (2 ^ 15 : ℝ≥0∞)⁻¹ * preTot pol A θ (trialW pk (encWt pk)) ≤
      q + 4 * ((q + K : ℕ) : ℝ≥0∞) * preTot pol A θ (trialW pk recUWt) +
        encEps * K := by
  obtain ⟨P, hP, hx⟩ := hinv
  -- The database grade at the calls.
  set κ : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port → ℕ := fun i ↦
    (if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 0 else 1) +
      (if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1 else 0) with hκ
  have hκ1 : ∀ i, κ i = 1 := fun i ↦ by
    rw [hκ]
    by_cases h : extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i = true <;> simp [h]
  have hxκ : IFreeM.IsChargeBound (prefixQ pol A θ) (portCharge κ) (q + K) :=
    isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl) (hq.add hK)
  have hb : IFreeM.IsChargeBound (prefixQ pol A θ)
      (portCharge fun _ : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port ↦ 0) 0 :=
    isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl)
      (isChargeBound_zero (prefixQ pol A θ))
  have hg := forallQueries_of_charge_step (runtimeR m0Q) (fun s ↦ dbGrade s.1) κ (fun _ ↦ 0)
    (fun i r t σ hσ ↦ (querySupportedOn_runtimeR_stepE i r t σ hσ).mono
      (Set.Iic_subset_Iic.2 (by rw [hκ1]))) .instruments (prefixQ pol A θ) hxκ hb
    querySupportedOn_initQ_gradeE
  -- The potential argument.
  have h0 : potential (diagPot fun s ↦ √(encPotQ pk s)) initQ = 0 :=
    (potential_basis_init (X := PairOut) (Z := Qrom.HashDomain) m0Q encPotQ_nonneg ()).trans
      (by rw [encPotQ_empty, ENNReal.ofReal_zero])
  have hmain := totalWeight_le_potential_of_forallQueries (runtimeR m0Q) .instruments
    (diagPot fun s ↦ √(encPotQ pk s)) _
    (fun i σ ↦ PreInvQ pk hon i σ ∧ QuerySupportedOn
      (fun m : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RegQ ↦ dbGrade m.2.1)
        (Set.Iic (q + K)) σ)
    (fun i E σ h ↦ ⟨hP i E σ h.1, (querySupportedOn_traceRight
      (q := fun a : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RegQ ↦
        dbGrade a.2.1) h.2.2).mono (Set.Iic_subset_Iic.2 (by omega))⟩)
    (extWeight (hwCost (fun c σ ↦ (2 ^ 15 : ℝ≥0∞)⁻¹ * trialW pk (encWt pk) c σ)
      fun _ _ ↦ 0))
    (encChgE pk (q + K)) (fun i σ hσ hI ↦ encPotQ_port_leE i σ hσ hI) (prefixQ pol A θ)
    initQ_posSemidef (forallQueries_and hx hg)
  -- The drops are the scaled Enc weights.
  have hlow : (2 ^ 15 : ℝ≥0∞)⁻¹ * preTot pol A θ (trialW pk (encWt pk)) ≤
      (runtimeR m0Q).totalWeight .instruments
        (extWeight (hwCost (fun c σ ↦ (2 ^ 15 : ℝ≥0∞)⁻¹ * trialW pk (encWt pk) c σ)
          fun _ _ ↦ 0)) (prefixQ pol A θ) initQ := by
    refine (le_of_eq (totalWeight_const_mul_weight (runtimeR m0Q) .instruments _
      (extWeight (hwCost (trialW pk (encWt pk)) fun _ _ ↦ 0)) (prefixQ pol A θ) initQ).symm).trans
      (totalWeight_le_totalWeight (runtimeR m0Q) .instruments (fun i σ _ ↦ ?_) (prefixQ pol A θ)
        initQ_posSemidef)
    rcases i with ((_ | _) | _) | _
    · exact le_of_eq (mul_zero _)
    · exact le_rfl
    · exact le_of_eq (mul_zero _)
    · exact le_of_eq (mul_zero _)
  -- The charges along the prefix.
  have hchg : (runtimeR m0Q).totalWeight .instruments (encChgE pk (q + K)) (prefixQ pol A θ)
      initQ ≤ q + 4 * ((q + K : ℕ) : ℝ≥0∞) * preTot pol A θ (trialW pk recUWt) +
        encEps * K := by
    refine (totalWeight_le_lin (runtimeR m0Q) .instruments _
      (fun i σ ↦ if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 0
        else ENNReal.ofReal σ.trace.re)
      (extWeight (hwCost (trialW pk recUWt) fun _ _ ↦ 0))
      (fun i σ ↦ encEps * trW i σ) 1 (4 * ((q + K : ℕ) : ℝ≥0∞))
      (fun i σ _ ↦ ?_) (prefixQ pol A θ) initQ_posSemidef).trans ?_
    · rcases i with ((p | c) | c) | T
      · simp [encChgE, portCh, extWeight, sumWeight, hwCost, extCls, hwCls, trW]
        exact le_of_eq rfl
      · simp [encChgE, portCh, extWeight, sumWeight, hwCost, extCls, hwCls, trW]
      · exact zero_le
      · exact zero_le
    · have h1 := (totalWeight_trace_le_of_isChargeBound (runtimeR m0Q) .instruments _
        (prefixQ pol A θ) hq initQ_posSemidef).trans
        ((mul_le_mul_of_nonneg_left ofReal_trace_initQ_le_one zero_le).trans_eq (mul_one _))
      have h3 : (runtimeR m0Q).totalWeight .instruments
          (fun i σ ↦ encEps * trW i σ) (prefixQ pol A θ) initQ ≤
          encEps * K :=
        (le_of_eq (totalWeight_const_mul_weight (runtimeR m0Q) .instruments _ trW
          (prefixQ pol A θ) initQ)).trans
          (mul_le_mul_of_nonneg_left (totalWeight_trW_le _ hK) zero_le)
      rw [one_mul]
      exact add_le_add (add_le_add h1 le_rfl) h3
  calc (2 ^ 15 : ℝ≥0∞)⁻¹ * preTot pol A θ (trialW pk (encWt pk)) ≤
        potential (diagPot fun s ↦ √(encPotQ pk s)) initQ +
          (runtimeR m0Q).totalWeight .instruments (encChgE pk (q + K)) (prefixQ pol A θ)
            initQ :=
        hlow.trans hmain
    _ ≤ _ := by
        rw [h0, zero_add]
        exact hchg

/-- **The Enc weights of the challenge prefix**: with at most `q` sponge and `K` classical calls,
on calls satisfying `PreInvQ (pkQ θ) hon`,
`encPre ≤ 2^15 (q + 4 (q + K) recUPre + (q + K) K 2^-510)`. -/
theorem encPre_le {hon : HonestCells} (pol : DigestPolicy) (A : SAdversary) (θ : TVals)
    {q K : ℕ} (hinv : PrefixInvQ (pkQ θ) hon pol A θ)
    (hq : IFreeM.IsChargeBound (prefixQ pol A θ) (portCharge fun i ↦
      if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 0 else 1) q)
    (hK : IFreeM.IsChargeBound (prefixQ pol A θ) (portCharge fun i ↦
      if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1 else 0) K) :
    encPre pol A θ ≤ encCap encC encEps q K (recUPre pol A θ) := by
  have h := encPre_le_chargesE (pkQ θ) pol A θ hinv hq hK
  have hK' : encEps * K ≤ ((q + K : ℕ) : ℝ≥0∞) * K * encEps := by
    rcases Nat.eq_zero_or_pos K with hK0 | hK0
    · subst hK0
      simp
    · have h1 : (1 : ℝ≥0∞) ≤ ((q + K : ℕ) : ℝ≥0∞) := by
        exact_mod_cast (show 1 ≤ q + K by omega)
      calc encEps * K = 1 * K * encEps := by rw [one_mul, mul_comm]
        _ ≤ _ := by gcongr
  have h2 : (2 ^ 15 : ℝ≥0∞) ≠ 0 := by positivity
  have h2' : (2 ^ 15 : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  unfold encCap encC
  calc encPre pol A θ = 2 ^ 15 * ((2 ^ 15 : ℝ≥0∞)⁻¹ * encPre pol A θ) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel h2 h2', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (h.trans (add_le_add le_rfl hK')) zero_le

end Quantum.Qrom.Sphincs

end
