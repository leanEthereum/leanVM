module

public import Quantum.Qrom.Sphincs.Multi.Costs.EncRead
public import Quantum.Qrom.Sphincs.Costs.Enc

@[expose] public section

/-!
# The Enc weights of the `n`-user challenge prefix

The `n`-user analog of `Quantum.Qrom.Sphincs` `Costs/Enc`. The Enc weights `encPreSN` (the
codeword cells of the owner's key at the empty read cells of an unselected key, summed over the
trial reads of the challenge prefix) are bounded by the joint potential `encPotQSN pk` (EncRead),
CostJoint's telescoping on the calls of an invariant (`totalWeight_le_potential_of_forallQueries`)
with the invariant `PreInvQSN` and the database grade at most `q + K` (every port raises it by at
most one: `querySupportedOn_runtimeR_stepQSN`, `querySupportedOn_initQSN_grade`).

* **`encPreSN_le_charges`**: at any public keys `pk`, on calls satisfying `PreInvQSN pk hon`,
  `2^-15 preTotSN (encWtSN pk) ≤ q + 4 (q + K) recUPreSN + 2^-510 K`.
* **`encPreSN_le`**: `encPreSN ≤ encCap encC encEps q K recUPreSN`, the single-user constants
  `encC = 2^15`, `encEps = 2^-510`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs.Multi

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

variable {n : ℕ}

/-! ## The database grade at the calls -/

/-- **Every port of the `n`-user runtime 2 raises the database grade by at most one.** -/
theorem querySupportedOn_runtimeR_stepQSN (i : (RSpecSN n (SelMemN n)).Port)
    (r : (RSpecSN n (SelMemN n)).Result i) (t : ℕ)
    (σ : Matrix ((RSpecSN n (SelMemN n)).In i ×
      (runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).D)
      ((RSpecSN n (SelMemN n)).In i ×
        (runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).D) ℂ)
    (hσ : QuerySupportedOn (fun q : (RSpecSN n (SelMemN n)).In i ×
      (runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).D ↦ dbGrade q.2.1)
        (Set.Iic t) σ) :
    QuerySupportedOn (fun q : (RSpecSN n (SelMemN n)).Out i ×
      (runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).D ↦ dbGrade q.2.1)
        (Set.Iic (t + 1))
        (((runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).step i).branch r σ) := by
  rcases i with i | j
  · exact querySupportedOn_spongeHardwiredRuntime_step (hwEmpty PairOut HashDomain) m0SN i r t
      σ hσ
  · exact Quantum.Xmss.Assembly.querySupportedOn_recStep j r t σ hσ

/-- The initial state has empty databases. -/
theorem querySupportedOn_initQSN_grade :
    QuerySupportedOn (fun m : QReg.of Unit ×
      (runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).D ↦ dbGrade m.2.1)
        (Set.Iic 0) initQSN := by
  intro m m' hm
  change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty PairOut HashDomain, m0SN) : RRegSN n (SelMemN n))).matrix)
      m m' ≠ 0 at hm
  simp only [SubState.matrix_basis] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · constructor <;> simp [← he.1, ← he.2, dbGrade, Database.size_empty]
  · exact False.elim (h rfl)

/-! ## The potential at the start -/

theorem encPotQSN_empty (pk : Fin n → PublicKey) (m : QMemSN n) :
    encPotQSN pk (((Database.empty, Database.empty, Database.empty),
      hwEmpty PairOut HashDomain, m) : RRegSN n (SelMemN n)) = 0 := by
  unfold encPotQSN
  refine Finset.sum_eq_zero fun κ _ ↦ ?_
  have h0 : encCwCountN pk (unionH (((Database.empty, Database.empty, Database.empty),
      hwEmpty PairOut HashDomain, m) : RRegSN n (SelMemN n))) κ.1 κ.2 = 0 := by
    have h := Quantum.Qrom.Xmss.cellOutCount_le_card (D := HashDomain) (Y := PairOut)
      (U := unionH (((Database.empty, Database.empty, Database.empty),
        hwEmpty PairOut HashDomain, m) : RRegSN n (SelMemN n)))
      (P := fun x ↦ ownerS pk x = some κ.1 ∧
        slotOf (pk κ.1) x = some (.enc κ.2.1 κ.2.2.1 κ.2.2.2))
      (Qo := fun y ↦ Quantum.Sphincs.Codeword.Valid (pairDigest y)) (fun _ ↦ False)
      fun _ _ _ hy ↦ by cases hy
    rw [Finset.filter_false, Finset.card_empty] at h
    exact Nat.le_zero.mp h
  rw [h0]
  split_ifs <;> simp

/-! ## The Enc weights along the prefix -/

variable {pk : Fin n → PublicKey} {hon : Fin n → HonestCells}

/-- **The charges of the Enc potential**: the trace at the sponge ports; at a read port
`4 G recUWtSN` plus `2^-510` per unit of trace; nothing at the program and record ports. -/
noncomputable def encChgSN (G : ℕ) :=
  portCh PairOut HashDomain (TPosN n) (SelMemN n) (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
    (fun c σ ↦ 4 * (G : ℝ≥0∞) * trialWSN recUWtSN c σ +
      encEps * ENNReal.ofReal σ.trace.re) fun _ _ ↦ 0

/-- **The port conditions of the Enc potential**: on an input satisfying `PreInvQSN pk hon` with
database grade at most `G`, the scaled Enc weight plus the potential after the call is at most the
potential before plus the charge `encChgSN G`. -/
theorem encPotQSN_port_le {G : ℕ} (i : (RSpecSN n (SelMemN n)).Port)
    (σ : Matrix ((RSpecSN n (SelMemN n)).In i ×
      (runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).D)
      ((RSpecSN n (SelMemN n)).In i ×
        (runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).D) ℂ)
    (hσ : σ.PosSemidef)
    (hI : PreInvQSN pk hon i σ ∧ QuerySupportedOn
      (fun m : (RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n) ↦ dbGrade m.2.1)
        (Set.Iic G) σ) :
    extWeight (hwCost (fun c σ ↦ (2 ^ 15 : ℝ≥0∞)⁻¹ * trialWSN (encWtSN pk) c σ)
        fun _ _ ↦ 0) i σ +
        ∑' r, potential (diagPot fun s ↦ √(encPotQSN pk s))
          (((runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).step i).branch r σ) ≤
      potential (diagPot fun s ↦ √(encPotQSN pk s)) σ + encChgSN G i σ := by
  rcases i with ((p | c) | c) | T
  · have hbr : ∀ r : Unit, ((runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).step
        (.inl (.inl (.inl p)))).branch r σ =
        MatrixMap.conj ((spongeHardwired PairOut HashDomain
          (hwEmpty PairOut HashDomain) (m0SN (n := n))).U p) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty PairOut HashDomain)
        m0SN p r) σ
    simp only [encChgSN, portCh, extWeight, sumWeight, hwCost, zero_add]
    exact (le_of_eq (tsum_congr fun r ↦ congrArg _ (hbr r))).trans
      (tsum_potential_sponge_le encPotQSN_nonneg (oneCellLipschitz_encPotQSN pk) _ _ p hσ)
  · obtain ⟨⟨⟨z, j, K, hz, ho, rfl⟩, hMF, -, hnb⟩, hgr⟩ := hI
    have hbr : ∀ r, ((runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).step
        (.inl (.inl (.inr (trialReadSN z (j, K)))))).branch r σ =
        MatrixMap.conj (hwReadKraus (trialReadSN z (j, K)) r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty PairOut HashDomain)
        m0SN (trialReadSN z (j, K)) r) σ
    have hnb' : ReadNoBot (.readH z (trialUpdSN z (j, K))) σ := readNoBot_of_noBot _ hnb
    have hsupp : ∀ a, σ a a ≠ 0 → EncFreeSN pk a.2 ∧ dbGrade a.2.1 ≤ G := fun a ha ↦
      ⟨(hMF a a ha).1, Set.mem_Iic.mp (hgr a a ha).1⟩
    simp only [encChgSN, portCh, extWeight, sumWeight, hwCost]
    exact (le_of_eq (congrArg (_ + ·) (tsum_congr fun r ↦ congrArg _ (hbr r)))).trans
      (trialReadSN_potential_le hz ho hσ hnb' hsupp)
  · obtain ⟨⟨z, v, rfl, hz⟩, -⟩ := hI.1
    have hbr : ∀ r, ((runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).step
        (.inl (.inr (.programH z v)))).branch r σ =
        MatrixMap.conj (hwProgKraus (.programH z v) r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty PairOut HashDomain)
        m0SN (.programH z v) r) σ
    simp only [encChgSN, portCh, extWeight, sumWeight, hwCost, zero_add, add_zero]
    have hprog := tsum_potential_prog_eq (encPotQSN_nonneg (pk := pk)) (.programH z v) hσ
    refine (le_of_eq ((tsum_congr fun r ↦ congrArg _ (hbr r)).trans hprog)).trans
      (le_of_eq ?_)
    refine Eq.trans ?_ (potential_diagPot_sqrt encPotQSN_nonneg σ).symm
    exact congrArg ENNReal.ofReal (Finset.sum_congr rfl fun a _ ↦ by
      rw [encPotQSN_progMap (not_enc_of_exemptCellSN hz) v])
  · have hlab : PotLabelFree (X := PairOut) (Z := HashDomain) (S := TPosN n) (M' := SelMemN n)
        (encPotQSN pk) := fun _ _ _ _ _ ↦ encPotQSN_congr rfl rfl
    simp only [encChgSN, portCh, extWeight, sumWeight, zero_add, add_zero]
    exact tsum_potential_recStep_diag encPotQSN_nonneg hlab T hσ

variable (pk) in
/-- **The Enc weights of the prefix, by the joint potential**: with at most `q` sponge and `K`
classical calls, on calls satisfying `PreInvQSN pk hon`,
`2^-15 preTotSN (encWtSN pk) ≤ q + 4 (q + K) recUPreSN + 2^-510 K`. -/
theorem encPreSN_le_charges (A : MuAdversaryS n) (θ : TValsN n) {q K : ℕ}
    (hinv : PrefixInvQSN pk hon A θ)
    (hq : IFreeM.IsChargeBound (prefixQSN (strPolN n) A θ) (portCharge fun i ↦
      if extCls PairOut HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n)) i then 0 else 1) q)
    (hK : IFreeM.IsChargeBound (prefixQSN (strPolN n) A θ) (portCharge fun i ↦
      if extCls PairOut HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n)) i then 1 else 0)
        K) :
    (2 ^ 15 : ℝ≥0∞)⁻¹ * preTotSN A θ (trialWSN (encWtSN pk)) ≤
      q + 4 * ((q + K : ℕ) : ℝ≥0∞) * recUPreSN A θ + encEps * K := by
  obtain ⟨Q, hQ, hx⟩ := hinv
  -- The database grade at the calls.
  set ch : (RSpecSN n (SelMemN n)).Port → ℕ := fun i ↦
    (if extCls PairOut HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n)) i then 0 else 1) +
      (if extCls PairOut HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n)) i then 1
        else 0) with hch
  have hch1 : ∀ i, ch i = 1 := fun i ↦ by
    rw [hch]
    by_cases h : extCls PairOut HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n)) i = true
      <;> simp [h]
  have hxch : IFreeM.IsChargeBound (prefixQSN (strPolN n) A θ) (portCharge ch) (q + K) :=
    isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl) (hq.add hK)
  have hb : IFreeM.IsChargeBound (prefixQSN (strPolN n) A θ)
      (portCharge fun _ : (RSpecSN n (SelMemN n)).Port ↦ 0) 0 :=
    isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl)
      (isChargeBound_zero (prefixQSN (strPolN n) A θ))
  have hg := forallQueries_of_charge_step (runtimeR (m0SN (n := n))) (fun s ↦ dbGrade s.1) ch
    (fun _ ↦ 0) (fun i r t σ hσ ↦ (querySupportedOn_runtimeR_stepQSN i r t σ hσ).mono
      (Set.Iic_subset_Iic.2 (by rw [hch1]))) .instruments (prefixQSN (strPolN n) A θ) hxch hb
    querySupportedOn_initQSN_grade
  -- The potential argument.
  have h0 : potential (diagPot fun s ↦ √(encPotQSN pk s)) initQSN = 0 :=
    (potential_basis_init (X := PairOut) (Z := HashDomain) (m0SN (n := n))
      encPotQSN_nonneg ()).trans (by rw [encPotQSN_empty, ENNReal.ofReal_zero])
  have hmain := totalWeight_le_potential_of_forallQueries (runtimeR (m0SN (n := n)))
    .instruments (diagPot fun s ↦ √(encPotQSN pk s)) _
    (fun i σ ↦ PreInvQSN pk hon i σ ∧ QuerySupportedOn
      (fun m : (RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n) ↦ dbGrade m.2.1)
        (Set.Iic (q + K)) σ)
    (fun i E σ h ↦ ⟨hQ i E σ h.1, (querySupportedOn_traceRight
      (q := fun a : (RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n) ↦
        dbGrade a.2.1) h.2.2).mono (Set.Iic_subset_Iic.2 (by omega))⟩)
    (extWeight (hwCost (fun c σ ↦ (2 ^ 15 : ℝ≥0∞)⁻¹ * trialWSN (encWtSN pk) c σ)
      fun _ _ ↦ 0))
    (encChgSN (q + K)) (fun i σ hσ hI ↦ encPotQSN_port_le i σ hσ hI)
    (prefixQSN (strPolN n) A θ) initQSN_posSemidef (forallQueries_and hx hg)
  -- The drops are the scaled Enc weights.
  have hlow : (2 ^ 15 : ℝ≥0∞)⁻¹ * preTotSN A θ (trialWSN (encWtSN pk)) ≤
      (runtimeR (m0SN (n := n))).totalWeight .instruments
        (extWeight (hwCost (fun c σ ↦ (2 ^ 15 : ℝ≥0∞)⁻¹ * trialWSN (encWtSN pk) c σ)
          fun _ _ ↦ 0)) (prefixQSN (strPolN n) A θ) initQSN := by
    refine (le_of_eq (totalWeight_const_mul_weight (runtimeR (m0SN (n := n))) .instruments _
      (extWeight (hwCost (trialWSN (encWtSN pk)) fun _ _ ↦ 0)) (prefixQSN (strPolN n) A θ)
        initQSN).symm).trans
      (totalWeight_le_totalWeight (runtimeR (m0SN (n := n))) .instruments (fun i σ _ ↦ ?_)
        (prefixQSN (strPolN n) A θ) initQSN_posSemidef)
    rcases i with ((_ | _) | _) | _
    · exact le_of_eq (mul_zero _)
    · exact le_rfl
    · exact le_of_eq (mul_zero _)
    · exact le_of_eq (mul_zero _)
  -- The charges along the prefix.
  have hchg : (runtimeR (m0SN (n := n))).totalWeight .instruments (encChgSN (q + K))
      (prefixQSN (strPolN n) A θ) initQSN ≤
      q + 4 * ((q + K : ℕ) : ℝ≥0∞) * recUPreSN A θ + encEps * K := by
    refine (totalWeight_le_lin (runtimeR (m0SN (n := n))) .instruments _
      (fun i σ ↦ if extCls PairOut HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n)) i
        then 0 else ENNReal.ofReal σ.trace.re)
      (extWeight (hwCost (trialWSN recUWtSN) fun _ _ ↦ 0))
      (fun i σ ↦ encEps * trWSN i σ) 1 (4 * ((q + K : ℕ) : ℝ≥0∞))
      (fun i σ _ ↦ ?_) (prefixQSN (strPolN n) A θ) initQSN_posSemidef).trans ?_
    · rcases i with ((p | c) | c) | T
      · simp [encChgSN, portCh, extWeight, sumWeight, hwCost, extCls, hwCls, trWSN]
        exact le_of_eq rfl
      · simp [encChgSN, portCh, extWeight, sumWeight, hwCost, extCls, hwCls, trWSN]
      · exact zero_le
      · exact zero_le
    · have h1 := (totalWeight_trace_le_of_isChargeBound (runtimeR (m0SN (n := n)))
        .instruments _ (prefixQSN (strPolN n) A θ) hq initQSN_posSemidef).trans
        ((mul_le_mul_of_nonneg_left ofReal_trace_initQSN_le_one zero_le).trans_eq (mul_one _))
      have h3 : (runtimeR (m0SN (n := n))).totalWeight .instruments
          (fun i σ ↦ encEps * trWSN i σ) (prefixQSN (strPolN n) A θ) initQSN ≤
          encEps * K :=
        (le_of_eq (totalWeight_const_mul_weight (runtimeR (m0SN (n := n))) .instruments _ trWSN
          (prefixQSN (strPolN n) A θ) initQSN)).trans
            (mul_le_mul_of_nonneg_left (totalWeight_trWSN_le _ hK) zero_le)
      rw [one_mul]
      exact add_le_add (add_le_add h1 le_rfl) h3
  calc (2 ^ 15 : ℝ≥0∞)⁻¹ * preTotSN A θ (trialWSN (encWtSN pk)) ≤
        potential (diagPot fun s ↦ √(encPotQSN pk s)) initQSN +
          (runtimeR (m0SN (n := n))).totalWeight .instruments (encChgSN (q + K))
            (prefixQSN (strPolN n) A θ) initQSN :=
        hlow.trans hmain
    _ ≤ _ := by
        rw [h0, zero_add]
        exact hchg

/-- **The Enc weights of the `n`-user challenge prefix**: with at most `q` sponge and `K` classical
calls, on calls satisfying `PreInvQSN (pkQN θ) hon`,
`encPreSN ≤ 2^15 (q + 4 (q + K) recUPreSN + (q + K) K 2^-510)`. -/
theorem encPreSN_le {hon : Fin n → HonestCells} (A : MuAdversaryS n) (θ : TValsN n) {q K : ℕ}
    (hinv : PrefixInvQSN (pkQN θ) hon A θ)
    (hq : IFreeM.IsChargeBound (prefixQSN (strPolN n) A θ) (portCharge fun i ↦
      if extCls PairOut HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n)) i then 0 else 1) q)
    (hK : IFreeM.IsChargeBound (prefixQSN (strPolN n) A θ) (portCharge fun i ↦
      if extCls PairOut HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n)) i then 1 else 0)
        K) :
    encPreSN A θ ≤ encCap encC encEps q K (recUPreSN A θ) := by
  have h := encPreSN_le_charges (pkQN θ) A θ hinv hq hK
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
  calc encPreSN A θ = 2 ^ 15 * ((2 ^ 15 : ℝ≥0∞)⁻¹ * encPreSN A θ) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel h2 h2', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (h.trans (add_le_add le_rfl hK')) zero_le

end Quantum.Qrom.Sphincs.Multi

end
