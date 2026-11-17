module

public import Quantum.Qrom.Xmss.Costs.EncRead

@[expose] public section

/-!
# The Enc weights of the challenge prefix

The Enc weights `encPre` (the codeword cells of the key's message slot at the empty read cells of
an unselected key, summed over the trial reads of the challenge prefix) are bounded by the joint
potential `encPotQ` (EncRead), CostJoint's telescoping on the calls of an invariant
(`totalWeight_le_potential_of_forallQueries`) with the invariant `PreInvQ` and the database grade
at most `q + K` (every port raises it by at most one: `querySupportedOn_runtimeR_stepQ`,
`querySupportedOn_initQ_grade`).

* **`encPre_le_charges`**: `2^-22 encPre ≤ q + 4 (q + K) recUPre + 2^-250 K` (sponge calls raise
  the potential by their trace, trial reads drop it by `2^-22 encWt` up to their charge, programs
  and records keep it).
* **`encPre_le`**: `encPre ≤ 2^22 (q + 4 (q + K) recUPre + (q + K) K 2^-250)`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Sponge HashSig LeanXmss
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR extWeight sumWeight extCls portCh
  PotLabelFree potential_diagPot_sqrt tsum_potential_recStep_diag tsum_potential_sponge_le
  totalWeight_le_potential_of_forallQueries potential_basis_init isChargeBound_mono_charge
  isChargeBound_zero forallQueries_of_charge_step forallQueries_and querySupportedOn_traceRight
  totalWeight_le_lin)
open Quantum.Xmss.Hybrid (totalWeight_le_totalWeight totalWeight_const_mul_weight
  totalWeight_trace_le_of_isChargeBound)

attribute [local irreducible] xmssRom

/- Instance search for the register with its trivial public register exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-! ## The database grade at the calls -/

/-- **Every port of runtime 2 raises the database grade by at most one.** -/
theorem querySupportedOn_runtimeR_stepQ (i : (recHwSpec HashOutput HashDomain HPos SelMem).Port)
    (r : (recHwSpec HashOutput HashDomain HPos SelMem).Result i) (t : ℕ)
    (σ : Matrix ((recHwSpec HashOutput HashDomain HPos SelMem).In i ×
      (runtimeR (X := HashOutput) (Z := HashDomain) m0Q).D)
      ((recHwSpec HashOutput HashDomain HPos SelMem).In i ×
        (runtimeR (X := HashOutput) (Z := HashDomain) m0Q).D) ℂ)
    (hσ : QuerySupportedOn (fun q : (recHwSpec HashOutput HashDomain HPos SelMem).In i ×
      (runtimeR (X := HashOutput) (Z := HashDomain) m0Q).D ↦ dbGrade q.2.1) (Set.Iic t) σ) :
    QuerySupportedOn (fun q : (recHwSpec HashOutput HashDomain HPos SelMem).Out i ×
      (runtimeR (X := HashOutput) (Z := HashDomain) m0Q).D ↦ dbGrade q.2.1) (Set.Iic (t + 1))
        (((runtimeR (X := HashOutput) (Z := HashDomain) m0Q).step i).branch r σ) := by
  rcases i with i | j
  · exact querySupportedOn_spongeHardwiredRuntime_step (hwEmpty HashOutput HashDomain) m0Q i r t
      σ hσ
  · exact Quantum.Xmss.Assembly.querySupportedOn_recStep j r t σ hσ

/-- The initial state has empty databases. -/
theorem querySupportedOn_initQ_grade :
    QuerySupportedOn (fun m : QReg.of Unit × (runtimeR (X := HashOutput) (Z := HashDomain) m0Q).D ↦
      dbGrade m.2.1) (Set.Iic 0) initQ := by
  intro m m' hm
  change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty HashOutput HashDomain, m0Q) : RReg SelMem)).matrix) m m' ≠ 0 at hm
  simp only [SubState.matrix_basis] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · constructor <;> simp [← he.1, ← he.2, dbGrade, Database.size_empty]
  · exact False.elim (h rfl)

/-! ## The potential at the start -/

theorem encPotQ_empty (m : QMem) :
    encPotQ (((Database.empty, Database.empty, Database.empty), hwEmpty HashOutput HashDomain, m) :
      RReg SelMem) = 0 := by
  unfold encPotQ
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  have h0 : msgCwCount (unionH (((Database.empty, Database.empty, Database.empty),
      hwEmpty HashOutput HashDomain, m) : RReg SelMem)) k.1 k.2 = 0 := by
    have h := cellOutCount_le_card (U := unionH (((Database.empty, Database.empty,
      Database.empty), hwEmpty HashOutput HashDomain, m) : RReg SelMem))
      (P := fun x ↦ slotOf x = some (.msg k.1 k.2))
      (Qo := fun y ↦ Codeword.Valid (truncateHash y)) (fun _ ↦ False) fun _ _ _ hy ↦ by
        cases hy
    rw [Finset.filter_false, Finset.card_empty] at h
    exact Nat.le_zero.mp h
  rw [h0]
  split_ifs <;> simp

/-! ## The Enc weights along the prefix -/

variable {hon : HonestCells}

/-- **The charges of the Enc potential**: the trace at the sponge ports; at a read port
`4 G recUWt` plus `2^-250` per unit of trace; nothing at the program and record ports. -/
noncomputable def encChg (G : ℕ) :=
  portCh HashOutput HashDomain HPos SelMem (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
    (fun c σ ↦ 4 * (G : ℝ≥0∞) * trialW recUWt c σ +
      (2 ^ 250 : ℝ≥0∞)⁻¹ * ENNReal.ofReal σ.trace.re) fun _ _ ↦ 0

/-- **The port conditions of the Enc potential**: on an input satisfying `PreInvQ` with database
grade at most `G`, the scaled Enc weight plus the potential after the call is at most the
potential before plus the charge `encChg G`. -/
theorem encPotQ_port_le {G : ℕ} (i : (recHwSpec HashOutput HashDomain HPos SelMem).Port)
    (σ : Matrix ((recHwSpec HashOutput HashDomain HPos SelMem).In i ×
      (runtimeR (X := HashOutput) (Z := HashDomain) m0Q).D)
      ((recHwSpec HashOutput HashDomain HPos SelMem).In i ×
        (runtimeR (X := HashOutput) (Z := HashDomain) m0Q).D) ℂ) (hσ : σ.PosSemidef)
    (hI : PreInvQ hon i σ ∧ QuerySupportedOn
      (fun m : (recHwSpec HashOutput HashDomain HPos SelMem).In i × RReg SelMem ↦ dbGrade m.2.1)
        (Set.Iic G) σ) :
    extWeight (hwCost (fun c σ ↦ (2 ^ 22 : ℝ≥0∞)⁻¹ * trialW encWt c σ) fun _ _ ↦ 0) i σ +
        ∑' r, potential (diagPot fun s ↦ √(encPotQ s))
          (((runtimeR (X := HashOutput) (Z := HashDomain) m0Q).step i).branch r σ) ≤
      potential (diagPot fun s ↦ √(encPotQ s)) σ + encChg G i σ := by
  rcases i with ((p | c) | c) | T
  · have hbr : ∀ r : Unit, ((runtimeR (X := HashOutput) (Z := HashDomain) m0Q).step
        (.inl (.inl (.inl p)))).branch r σ =
        MatrixMap.conj ((spongeHardwired HashOutput HashDomain (hwEmpty HashOutput HashDomain)
          m0Q).U p) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty HashOutput HashDomain)
        m0Q p r) σ
    simp only [encChg, portCh, extWeight, sumWeight, hwCost, zero_add]
    exact (le_of_eq (tsum_congr fun r ↦ congrArg _ (hbr r))).trans
      (tsum_potential_sponge_le encPotQ_nonneg oneCellLipschitz_encPotQ _ _ p hσ)
  · obtain ⟨⟨⟨z, l, e, hz, rfl⟩, hMF, hnb⟩, hgr⟩ := hI
    have hbr : ∀ r, ((runtimeR (X := HashOutput) (Z := HashDomain) m0Q).step
        (.inl (.inl (.inr (trialRead z l e))))).branch r σ =
        MatrixMap.conj (hwReadKraus (trialRead z l e) r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty HashOutput HashDomain)
        m0Q (trialRead z l e) r) σ
    have hnb' : ReadNoBot (.readH z (trialUpdQ l e z)) σ := readNoBot_of_noBot _ hnb
    have hsupp : ∀ a, σ a a ≠ 0 → MsgFree a.2 ∧ dbGrade a.2.1 ≤ G := fun a ha ↦
      ⟨(hMF a a ha).1, Set.mem_Iic.mp (hgr a a ha).1⟩
    simp only [encChg, portCh, extWeight, sumWeight, hwCost]
    exact (le_of_eq (congrArg (_ + ·) (tsum_congr fun r ↦ congrArg _ (hbr r)))).trans
      (trialRead_potential_le hz hσ hnb' hsupp)
  · obtain ⟨⟨z, v, rfl, hz⟩, -, -⟩ := hI.1
    have hbr : ∀ r, ((runtimeR (X := HashOutput) (Z := HashDomain) m0Q).step
        (.inl (.inr (.programH z v)))).branch r σ =
        MatrixMap.conj (hwProgKraus (.programH z v) r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty HashOutput HashDomain)
        m0Q (.programH z v) r) σ
    simp only [encChg, portCh, extWeight, sumWeight, hwCost, zero_add, add_zero]
    have hprog := tsum_potential_prog_eq encPotQ_nonneg (.programH z v) hσ
    refine (le_of_eq ((tsum_congr fun r ↦ congrArg _ (hbr r)).trans hprog)).trans
      (le_of_eq ?_)
    refine Eq.trans ?_ (potential_diagPot_sqrt encPotQ_nonneg σ).symm
    exact congrArg ENNReal.ofReal (Finset.sum_congr rfl fun a _ ↦ by
      rw [encPotQ_progMap (not_msg_of_exemptCell hz) v])
  · have hlab : PotLabelFree (X := HashOutput) (Z := HashDomain) (S := HPos) (M' := SelMem)
        encPotQ := fun _ _ _ _ _ ↦ encPotQ_congr rfl rfl
    simp only [encChg, portCh, extWeight, sumWeight, zero_add, add_zero]
    exact tsum_potential_recStep_diag encPotQ_nonneg hlab T hσ

/-- **The Enc weights of the prefix, by the joint potential**: with at most `q` sponge and `K`
classical calls, on calls satisfying `PreInvQ`,
`2^-22 encPre ≤ q + 4 (q + K) recUPre + 2^-250 K`. -/
theorem encPre_le_charges (A : Adversary) (θ : HPos → Digest) {q K : ℕ}
    (hinv : PrefixInvQ hon A θ)
    (hq : IFreeM.IsChargeBound (prefixQ A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 0 else 1) q)
    (hK : IFreeM.IsChargeBound (prefixQ A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 1 else 0) K) :
    (2 ^ 22 : ℝ≥0∞)⁻¹ * encPre A θ ≤
      q + 4 * ((q + K : ℕ) : ℝ≥0∞) * recUPre A θ + (2 ^ 250 : ℝ≥0∞)⁻¹ * K := by
  obtain ⟨P, hP, hx⟩ := hinv
  -- The database grade at the calls.
  set κ : (recHwSpec HashOutput HashDomain HPos SelMem).Port → ℕ := fun i ↦
    (if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 0 else 1) +
      (if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 1 else 0) with hκ
  have hκ1 : ∀ i, κ i = 1 := fun i ↦ by
    rw [hκ]
    by_cases h : extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i = true <;> simp [h]
  have hxκ : IFreeM.IsChargeBound (prefixQ A θ) (portCharge κ) (q + K) :=
    isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl) (hq.add hK)
  have hb : IFreeM.IsChargeBound (prefixQ A θ)
      (portCharge fun _ : (recHwSpec HashOutput HashDomain HPos SelMem).Port ↦ 0) 0 :=
    isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl)
      (isChargeBound_zero (prefixQ A θ))
  have hg := forallQueries_of_charge_step (runtimeR m0Q) (fun s ↦ dbGrade s.1) κ (fun _ ↦ 0)
    (fun i r t σ hσ ↦ (querySupportedOn_runtimeR_stepQ i r t σ hσ).mono
      (Set.Iic_subset_Iic.2 (by rw [hκ1]))) .instruments (prefixQ A θ) hxκ hb
    querySupportedOn_initQ_grade
  -- The potential argument.
  have h0 : potential (diagPot fun s ↦ √(encPotQ s)) initQ = 0 :=
    (potential_basis_init (X := HashOutput) (Z := HashDomain) m0Q encPotQ_nonneg ()).trans
      (by rw [encPotQ_empty, ENNReal.ofReal_zero])
  have hmain := totalWeight_le_potential_of_forallQueries (runtimeR m0Q) .instruments
    (diagPot fun s ↦ √(encPotQ s)) _
    (fun i σ ↦ PreInvQ hon i σ ∧ QuerySupportedOn
      (fun m : (recHwSpec HashOutput HashDomain HPos SelMem).In i × RReg SelMem ↦ dbGrade m.2.1)
        (Set.Iic (q + K)) σ)
    (fun i E σ h ↦ ⟨hP i E σ h.1, (querySupportedOn_traceRight
      (q := fun a : (recHwSpec HashOutput HashDomain HPos SelMem).In i × RReg SelMem ↦
        dbGrade a.2.1) h.2.2).mono (Set.Iic_subset_Iic.2 (by omega))⟩)
    (extWeight (hwCost (fun c σ ↦ (2 ^ 22 : ℝ≥0∞)⁻¹ * trialW encWt c σ) fun _ _ ↦ 0))
    (encChg (q + K)) (fun i σ hσ hI ↦ encPotQ_port_le i σ hσ hI) (prefixQ A θ)
    initQ_posSemidef (forallQueries_and hx hg)
  -- The drops are the scaled Enc weights.
  have hlow : (2 ^ 22 : ℝ≥0∞)⁻¹ * encPre A θ ≤ (runtimeR m0Q).totalWeight .instruments
      (extWeight (hwCost (fun c σ ↦ (2 ^ 22 : ℝ≥0∞)⁻¹ * trialW encWt c σ) fun _ _ ↦ 0))
        (prefixQ A θ) initQ := by
    refine (le_of_eq (totalWeight_const_mul_weight (runtimeR m0Q) .instruments _
      (extWeight (hwCost (trialW encWt) fun _ _ ↦ 0)) (prefixQ A θ) initQ).symm).trans
      (totalWeight_le_totalWeight (runtimeR m0Q) .instruments (fun i σ _ ↦ ?_) (prefixQ A θ)
        initQ_posSemidef)
    rcases i with ((_ | _) | _) | _
    · exact le_of_eq (mul_zero _)
    · exact le_rfl
    · exact le_of_eq (mul_zero _)
    · exact le_of_eq (mul_zero _)
  -- The charges along the prefix.
  have hchg : (runtimeR m0Q).totalWeight .instruments (encChg (q + K)) (prefixQ A θ) initQ ≤
      q + 4 * ((q + K : ℕ) : ℝ≥0∞) * recUPre A θ + (2 ^ 250 : ℝ≥0∞)⁻¹ * K := by
    refine (totalWeight_le_lin (runtimeR m0Q) .instruments _
      (fun i σ ↦ if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 0
        else ENNReal.ofReal σ.trace.re)
      (extWeight (hwCost (trialW recUWt) fun _ _ ↦ 0))
      (fun i σ ↦ (2 ^ 250 : ℝ≥0∞)⁻¹ * trW i σ) 1 (4 * ((q + K : ℕ) : ℝ≥0∞))
      (fun i σ _ ↦ ?_) (prefixQ A θ) initQ_posSemidef).trans ?_
    · rcases i with ((p | c) | c) | T
      · simp [encChg, portCh, extWeight, sumWeight, hwCost, extCls, hwCls, trW]
        exact le_of_eq rfl
      · simp [encChg, portCh, extWeight, sumWeight, hwCost, extCls, hwCls, trW]
      · exact zero_le
      · exact zero_le
    · have h1 := (totalWeight_trace_le_of_isChargeBound (runtimeR m0Q) .instruments _
        (prefixQ A θ) hq initQ_posSemidef).trans
        ((mul_le_mul_of_nonneg_left ofReal_trace_initQ_le_one zero_le).trans_eq (mul_one _))
      have h3 : (runtimeR m0Q).totalWeight .instruments
          (fun i σ ↦ (2 ^ 250 : ℝ≥0∞)⁻¹ * trW i σ) (prefixQ A θ) initQ ≤
          (2 ^ 250 : ℝ≥0∞)⁻¹ * K :=
        (le_of_eq (totalWeight_const_mul_weight (runtimeR m0Q) .instruments _ trW (prefixQ A θ)
          initQ)).trans (mul_le_mul_of_nonneg_left (totalWeight_trW_le _ hK) zero_le)
      rw [one_mul]
      exact add_le_add (add_le_add h1 le_rfl) h3
  calc (2 ^ 22 : ℝ≥0∞)⁻¹ * encPre A θ ≤ potential (diagPot fun s ↦ √(encPotQ s)) initQ +
        (runtimeR m0Q).totalWeight .instruments (encChg (q + K)) (prefixQ A θ) initQ :=
        hlow.trans hmain
    _ ≤ _ := by
        rw [h0, zero_add]
        exact hchg

/-- **The Enc weights of the challenge prefix**: with at most `q` sponge and `K` classical calls,
on calls satisfying `PreInvQ`,
`encPre ≤ 2^22 (q + 4 (q + K) recUPre + (q + K) K 2^-250)`. -/
theorem encPre_le {hon : HonestCells} (A : Adversary) (θ : HPos → Digest) {q K : ℕ}
    (hinv : PrefixInvQ hon A θ)
    (hq : IFreeM.IsChargeBound (prefixQ A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 0 else 1) q)
    (hK : IFreeM.IsChargeBound (prefixQ A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 1 else 0) K) :
    encPre A θ ≤ 2 ^ 22 * ((q : ℝ≥0∞) + 4 * ((q + K : ℕ) : ℝ≥0∞) * recUPre A θ +
      ((q + K : ℕ) : ℝ≥0∞) * K * (2 ^ 250 : ℝ≥0∞)⁻¹) := by
  have h := encPre_le_charges A θ hinv hq hK
  have hK' : (2 ^ 250 : ℝ≥0∞)⁻¹ * K ≤ ((q + K : ℕ) : ℝ≥0∞) * K * (2 ^ 250 : ℝ≥0∞)⁻¹ := by
    rcases Nat.eq_zero_or_pos K with hK0 | hK0
    · subst hK0
      simp
    · have h1 : (1 : ℝ≥0∞) ≤ ((q + K : ℕ) : ℝ≥0∞) := by
        exact_mod_cast (show 1 ≤ q + K by omega)
      calc (2 ^ 250 : ℝ≥0∞)⁻¹ * K = 1 * K * (2 ^ 250 : ℝ≥0∞)⁻¹ := by rw [one_mul, mul_comm]
        _ ≤ _ := by gcongr
  have h2 : (2 ^ 22 : ℝ≥0∞) ≠ 0 := by positivity
  have h2' : (2 ^ 22 : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  calc encPre A θ = 2 ^ 22 * ((2 ^ 22 : ℝ≥0∞)⁻¹ * encPre A θ) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel h2 h2', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (h.trans (add_le_add le_rfl hK')) zero_le

end Quantum.Qrom.Xmss

end
