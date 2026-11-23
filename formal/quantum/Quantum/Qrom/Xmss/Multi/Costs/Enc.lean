module

public import Quantum.Qrom.Xmss.Multi.Costs.EncRead

@[expose] public section

/-!
# The Enc weights of the `n`-user challenge prefix

The `n`-user analog of `Quantum.Qrom.Xmss.Costs.Enc`. The Enc weights `encPreN P` (the codeword
cells of the owner's key at the empty read cells of an unselected key, summed over the trial reads
of the challenge prefix) are bounded by the joint potential `encPotQN P` (EncRead), CostJoint's
telescoping on the calls of an invariant (`totalWeight_le_potential_of_forallQueries`) with the
invariant `PreInvQN` and the database grade at most `q + K` (every port raises it by at most one:
`querySupportedOn_runtimeR_stepQN`, `querySupportedOn_initQN_grade`).

* **`encPreN_le_charges`**: `2^-22 encPreN ≤ q + 4 (q + K) recUPreN + 2^-250 K`.
* **`encPreN_le`**: `encPreN ≤ 2^22 (q + 4 (q + K) recUPreN + (q + K) K 2^-250)`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Qrom.Xmss.Multi

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

variable {n : ℕ}

/-! ## The database grade at the calls -/

/-- **Every port of runtime 2 raises the database grade by at most one.** -/
theorem querySupportedOn_runtimeR_stepQN (i : (RSpecN n (SelMemN n)).Port)
    (r : (RSpecN n (SelMemN n)).Result i) (t : ℕ)
    (σ : Matrix ((RSpecN n (SelMemN n)).In i ×
      (runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).D)
      ((RSpecN n (SelMemN n)).In i ×
        (runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).D) ℂ)
    (hσ : QuerySupportedOn (fun q : (RSpecN n (SelMemN n)).In i ×
      (runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).D ↦ dbGrade q.2.1)
        (Set.Iic t) σ) :
    QuerySupportedOn (fun q : (RSpecN n (SelMemN n)).Out i ×
      (runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).D ↦ dbGrade q.2.1)
        (Set.Iic (t + 1))
        (((runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).step i).branch r σ) := by
  rcases i with i | j
  · exact querySupportedOn_spongeHardwiredRuntime_step (hwEmpty HashOutput HashDomain) m0N i r t
      σ hσ
  · exact Quantum.Xmss.Assembly.querySupportedOn_recStep j r t σ hσ

/-- The initial state has empty databases. -/
theorem querySupportedOn_initQN_grade :
    QuerySupportedOn (fun m : QReg.of Unit ×
      (runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).D ↦ dbGrade m.2.1)
        (Set.Iic 0) initQN := by
  intro m m' hm
  change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty HashOutput HashDomain, m0N) : RRegN n (SelMemN n))).matrix)
      m m' ≠ 0 at hm
  simp only [SubState.matrix_basis] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · constructor <;> simp [← he.1, ← he.2, dbGrade, Database.size_empty]
  · exact False.elim (h rfl)

/-! ## The potential at the start -/

theorem encPotQN_empty (P : Fin n → PublicParameter) (m : QMemN n) :
    encPotQN P (((Database.empty, Database.empty, Database.empty),
      hwEmpty HashOutput HashDomain, m) : RRegN n (SelMemN n)) = 0 := by
  unfold encPotQN
  refine Finset.sum_eq_zero fun κ _ ↦ ?_
  have h0 : msgCwCountN P (unionH (((Database.empty, Database.empty, Database.empty),
      hwEmpty HashOutput HashDomain, m) : RRegN n (SelMemN n))) κ.1 κ.2.1 κ.2.2 = 0 := by
    have h := cellOutCount_le_card (D := HashDomain) (Y := HashOutput)
      (U := unionH (((Database.empty, Database.empty, Database.empty),
        hwEmpty HashOutput HashDomain, m) : RRegN n (SelMemN n)))
      (P := fun x ↦ Quantum.Qrom.MultiUser.ownerOf P prefixOf x = some κ.1 ∧
        slotOf x = some (.msg κ.2.1 κ.2.2))
      (Qo := fun y ↦ Codeword.Valid (truncateHash y)) (fun _ ↦ False) fun _ _ _ hy ↦ by
        cases hy
    rw [Finset.filter_false, Finset.card_empty] at h
    exact Nat.le_zero.mp h
  rw [h0]
  split_ifs <;> simp

/-! ## The Enc weights along the prefix -/

variable {hon : Fin n → HonestCells} {P : Fin n → PublicParameter}

/-- **The charges of the Enc potential**: the trace at the sponge ports; at a read port
`4 G recUWtN` plus `2^-250` per unit of trace; nothing at the program and record ports. -/
noncomputable def encChgN (G : ℕ) :=
  portCh HashOutput HashDomain (HPosN n) (SelMemN n) (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
    (fun c σ ↦ 4 * (G : ℝ≥0∞) * trialWN recUWtN c σ +
      (2 ^ 250 : ℝ≥0∞)⁻¹ * ENNReal.ofReal σ.trace.re) fun _ _ ↦ 0

/-- **The port conditions of the Enc potential**: on an input satisfying `PreInvQN` with database
grade at most `G`, the scaled Enc weight plus the potential after the call is at most the
potential before plus the charge `encChgN G`. -/
theorem encPotQN_port_le {G : ℕ} (i : (RSpecN n (SelMemN n)).Port)
    (σ : Matrix ((RSpecN n (SelMemN n)).In i ×
      (runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).D)
      ((RSpecN n (SelMemN n)).In i ×
        (runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).D) ℂ)
    (hσ : σ.PosSemidef)
    (hI : PreInvQN hon P i σ ∧ QuerySupportedOn
      (fun m : (RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n) ↦ dbGrade m.2.1)
        (Set.Iic G) σ) :
    extWeight (hwCost (fun c σ ↦ (2 ^ 22 : ℝ≥0∞)⁻¹ * trialWN (encWtN P) c σ) fun _ _ ↦ 0) i σ +
        ∑' r, potential (diagPot fun s ↦ √(encPotQN P s))
          (((runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).step i).branch r σ) ≤
      potential (diagPot fun s ↦ √(encPotQN P s)) σ + encChgN G i σ := by
  rcases i with ((p | c) | c) | T
  · have hbr : ∀ r : Unit, ((runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).step
        (.inl (.inl (.inl p)))).branch r σ =
        MatrixMap.conj ((spongeHardwired HashOutput HashDomain (hwEmpty HashOutput HashDomain)
          (m0N (n := n))).U p) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty HashOutput HashDomain)
        m0N p r) σ
    simp only [encChgN, portCh, extWeight, sumWeight, hwCost, zero_add]
    exact (le_of_eq (tsum_congr fun r ↦ congrArg _ (hbr r))).trans
      (tsum_potential_sponge_le (encPotQN_nonneg P) (oneCellLipschitz_encPotQN P) _ _ p hσ)
  · obtain ⟨⟨⟨z, j, l, e, hz, ho, rfl⟩, hMF, -, hnb⟩, hgr⟩ := hI
    have hbr : ∀ r, ((runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).step
        (.inl (.inl (.inr (trialReadN z (j, l, e)))))).branch r σ =
        MatrixMap.conj (hwReadKraus (trialReadN z (j, l, e)) r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty HashOutput HashDomain)
        m0N (trialReadN z (j, l, e)) r) σ
    have hnb' : ReadNoBot (.readH z (trialUpdN z (j, l, e))) σ := readNoBot_of_noBot _ hnb
    have hsupp : ∀ a, σ a a ≠ 0 → MsgFreeN a.2 ∧ dbGrade a.2.1 ≤ G := fun a ha ↦
      ⟨(hMF a a ha).1, Set.mem_Iic.mp (hgr a a ha).1⟩
    simp only [encChgN, portCh, extWeight, sumWeight, hwCost]
    exact (le_of_eq (congrArg (_ + ·) (tsum_congr fun r ↦ congrArg _ (hbr r)))).trans
      (trialReadN_potential_le hz ho hσ hnb' hsupp)
  · obtain ⟨⟨z, v, rfl, -, hz⟩, -⟩ := hI.1
    have hbr : ∀ r, ((runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).step
        (.inl (.inr (.programH z v)))).branch r σ =
        MatrixMap.conj (hwProgKraus (.programH z v) r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty HashOutput HashDomain)
        m0N (.programH z v) r) σ
    simp only [encChgN, portCh, extWeight, sumWeight, hwCost, zero_add, add_zero]
    have hprog := tsum_potential_prog_eq (encPotQN_nonneg P) (.programH z v) hσ
    refine (le_of_eq ((tsum_congr fun r ↦ congrArg _ (hbr r)).trans hprog)).trans
      (le_of_eq ?_)
    refine Eq.trans ?_ (potential_diagPot_sqrt (encPotQN_nonneg P) σ).symm
    exact congrArg ENNReal.ofReal (Finset.sum_congr rfl fun a _ ↦ by
      rw [encPotQN_progMap hz v])
  · have hlab : PotLabelFree (X := HashOutput) (Z := HashDomain) (S := HPosN n)
        (M' := SelMemN n) (encPotQN P) := fun _ _ _ _ _ ↦ encPotQN_congr rfl rfl
    simp only [encChgN, portCh, extWeight, sumWeight, zero_add, add_zero]
    exact tsum_potential_recStep_diag (encPotQN_nonneg P) hlab T hσ

/-- **The Enc weights of the prefix, by the joint potential**: with at most `q` sponge and `K`
classical calls, on calls satisfying `PreInvQN`,
`2^-22 encPreN ≤ q + 4 (q + K) recUPreN + 2^-250 K`. -/
theorem encPreN_le_charges (A : MuAdversary n) (θ : HPosN n → Digest) {q K : ℕ}
    (hinv : PrefixInvQN hon P A θ)
    (hq : IFreeM.IsChargeBound (prefixQN A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i then 0 else 1) q)
    (hK : IFreeM.IsChargeBound (prefixQN A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i then 1 else 0)
        K) :
    (2 ^ 22 : ℝ≥0∞)⁻¹ * encPreN P A θ ≤
      q + 4 * ((q + K : ℕ) : ℝ≥0∞) * recUPreN A θ + (2 ^ 250 : ℝ≥0∞)⁻¹ * K := by
  obtain ⟨Q, hQ, hx⟩ := hinv
  -- The database grade at the calls.
  set ch : (RSpecN n (SelMemN n)).Port → ℕ := fun i ↦
    (if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i then 0 else 1) +
      (if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i then 1
        else 0) with hch
  have hch1 : ∀ i, ch i = 1 := fun i ↦ by
    rw [hch]
    by_cases h : extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i = true
      <;> simp [h]
  have hxch : IFreeM.IsChargeBound (prefixQN A θ) (portCharge ch) (q + K) :=
    isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl) (hq.add hK)
  have hb : IFreeM.IsChargeBound (prefixQN A θ)
      (portCharge fun _ : (RSpecN n (SelMemN n)).Port ↦ 0) 0 :=
    isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl)
      (isChargeBound_zero (prefixQN A θ))
  have hg := forallQueries_of_charge_step (runtimeR (m0N (n := n))) (fun s ↦ dbGrade s.1) ch
    (fun _ ↦ 0) (fun i r t σ hσ ↦ (querySupportedOn_runtimeR_stepQN i r t σ hσ).mono
      (Set.Iic_subset_Iic.2 (by rw [hch1]))) .instruments (prefixQN A θ) hxch hb
    querySupportedOn_initQN_grade
  -- The potential argument.
  have h0 : potential (diagPot fun s ↦ √(encPotQN P s)) initQN = 0 :=
    (potential_basis_init (X := HashOutput) (Z := HashDomain) (m0N (n := n))
      (encPotQN_nonneg P) ()).trans (by rw [encPotQN_empty, ENNReal.ofReal_zero])
  have hmain := totalWeight_le_potential_of_forallQueries (runtimeR (m0N (n := n))) .instruments
    (diagPot fun s ↦ √(encPotQN P s)) _
    (fun i σ ↦ PreInvQN hon P i σ ∧ QuerySupportedOn
      (fun m : (RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n) ↦ dbGrade m.2.1)
        (Set.Iic (q + K)) σ)
    (fun i E σ h ↦ ⟨hQ i E σ h.1, (querySupportedOn_traceRight
      (q := fun a : (RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n) ↦
        dbGrade a.2.1) h.2.2).mono (Set.Iic_subset_Iic.2 (by omega))⟩)
    (extWeight (hwCost (fun c σ ↦ (2 ^ 22 : ℝ≥0∞)⁻¹ * trialWN (encWtN P) c σ) fun _ _ ↦ 0))
    (encChgN (q + K)) (fun i σ hσ hI ↦ encPotQN_port_le i σ hσ hI) (prefixQN A θ)
    initQN_posSemidef (forallQueries_and hx hg)
  -- The drops are the scaled Enc weights.
  have hlow : (2 ^ 22 : ℝ≥0∞)⁻¹ * encPreN P A θ ≤
      (runtimeR (m0N (n := n))).totalWeight .instruments
        (extWeight (hwCost (fun c σ ↦ (2 ^ 22 : ℝ≥0∞)⁻¹ * trialWN (encWtN P) c σ)
          fun _ _ ↦ 0)) (prefixQN A θ) initQN := by
    refine (le_of_eq (totalWeight_const_mul_weight (runtimeR (m0N (n := n))) .instruments _
      (extWeight (hwCost (trialWN (encWtN P)) fun _ _ ↦ 0)) (prefixQN A θ) initQN).symm).trans
      (totalWeight_le_totalWeight (runtimeR (m0N (n := n))) .instruments (fun i σ _ ↦ ?_)
        (prefixQN A θ) initQN_posSemidef)
    rcases i with ((_ | _) | _) | _
    · exact le_of_eq (mul_zero _)
    · exact le_rfl
    · exact le_of_eq (mul_zero _)
    · exact le_of_eq (mul_zero _)
  -- The charges along the prefix.
  have hchg : (runtimeR (m0N (n := n))).totalWeight .instruments (encChgN (q + K))
      (prefixQN A θ) initQN ≤
      q + 4 * ((q + K : ℕ) : ℝ≥0∞) * recUPreN A θ + (2 ^ 250 : ℝ≥0∞)⁻¹ * K := by
    refine (totalWeight_le_lin (runtimeR (m0N (n := n))) .instruments _
      (fun i σ ↦ if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i
        then 0 else ENNReal.ofReal σ.trace.re)
      (extWeight (hwCost (trialWN recUWtN) fun _ _ ↦ 0))
      (fun i σ ↦ (2 ^ 250 : ℝ≥0∞)⁻¹ * trWN i σ) 1 (4 * ((q + K : ℕ) : ℝ≥0∞))
      (fun i σ _ ↦ ?_) (prefixQN A θ) initQN_posSemidef).trans ?_
    · rcases i with ((p | c) | c) | T
      · simp [encChgN, portCh, extWeight, sumWeight, hwCost, extCls, hwCls, trWN]
        exact le_of_eq rfl
      · simp [encChgN, portCh, extWeight, sumWeight, hwCost, extCls, hwCls, trWN]
      · exact zero_le
      · exact zero_le
    · have h1 := (totalWeight_trace_le_of_isChargeBound (runtimeR (m0N (n := n))) .instruments _
        (prefixQN A θ) hq initQN_posSemidef).trans
        ((mul_le_mul_of_nonneg_left ofReal_trace_initQN_le_one zero_le).trans_eq (mul_one _))
      have h3 : (runtimeR (m0N (n := n))).totalWeight .instruments
          (fun i σ ↦ (2 ^ 250 : ℝ≥0∞)⁻¹ * trWN i σ) (prefixQN A θ) initQN ≤
          (2 ^ 250 : ℝ≥0∞)⁻¹ * K :=
        (le_of_eq (totalWeight_const_mul_weight (runtimeR (m0N (n := n))) .instruments _ trWN
          (prefixQN A θ) initQN)).trans
            (mul_le_mul_of_nonneg_left (totalWeight_trWN_le _ hK) zero_le)
      rw [one_mul]
      exact add_le_add (add_le_add h1 le_rfl) h3
  calc (2 ^ 22 : ℝ≥0∞)⁻¹ * encPreN P A θ ≤ potential (diagPot fun s ↦ √(encPotQN P s)) initQN +
        (runtimeR (m0N (n := n))).totalWeight .instruments (encChgN (q + K)) (prefixQN A θ)
          initQN :=
        hlow.trans hmain
    _ ≤ _ := by
        rw [h0, zero_add]
        exact hchg

/-- **The Enc weights of the challenge prefix**: with at most `q` sponge and `K` classical calls,
on calls satisfying `PreInvQN`,
`encPreN ≤ 2^22 (q + 4 (q + K) recUPreN + (q + K) K 2^-250)`. -/
theorem encPreN_le {hon : Fin n → HonestCells} {P : Fin n → PublicParameter} (A : MuAdversary n)
    (θ : HPosN n → Digest) {q K : ℕ} (hinv : PrefixInvQN hon P A θ)
    (hq : IFreeM.IsChargeBound (prefixQN A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i then 0 else 1) q)
    (hK : IFreeM.IsChargeBound (prefixQN A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i then 1 else 0)
        K) :
    encPreN P A θ ≤ 2 ^ 22 * ((q : ℝ≥0∞) + 4 * ((q + K : ℕ) : ℝ≥0∞) * recUPreN A θ +
      ((q + K : ℕ) : ℝ≥0∞) * K * (2 ^ 250 : ℝ≥0∞)⁻¹) := by
  have h := encPreN_le_charges A θ hinv hq hK
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
  calc encPreN P A θ = 2 ^ 22 * ((2 ^ 22 : ℝ≥0∞)⁻¹ * encPreN P A θ) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel h2 h2', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (h.trans (add_le_add le_rfl hK')) zero_le

end Quantum.Qrom.Xmss.Multi

end
