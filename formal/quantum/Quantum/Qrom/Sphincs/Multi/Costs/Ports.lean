module

public import Quantum.Qrom.Sphincs.Multi.Costs.Defs

@[expose] public section

/-!
# The classical costs of the `n`-user leanSPHINCS runtime 2: the ports of the challenge prefix

The `n`-user analog of `Quantum.Qrom.Sphincs.Costs.Ports`, for the event `BadRQN pk hon S`:

* **A trial read** of user `i`'s key `κ = (i, K)` at a cell `z` of `K`'s encoding slot owned by
  `i` (`card_hFlip_trialReadSN_le`, `readCost_trialReadSN_le`): the key is unselected at every
  trial read (`selOkS`), so on an empty cell the flipping pairs are the codeword pairs hitting a
  codeword cell of `i`'s key (Events' `card_flip_readCwN_le`), and a recorded cell flips only with
  the key unselected. For every `s > 0` the refined cost is at most `(1 + s) aQSN + (1 + 1/s) pQSN`,
  `aQSN = 2^-127 encWtSN + 2/|Y × Y|` per unit of trace, `pQSN = recUWtSN`.
* **A program of an exempt cell** costs nothing (`flipCost_programH_badRQN_eq_zero`).
* **The prefix** (`twPQSN_le_pk`, `twPQSN_le`): on calls satisfying `PreInvQSN` (`PrefixInvQSN`),
  with at most `K` classical calls, `twPQSN ≤ (√(2^-127 encPreSN + (2/|Y × Y|) K) + √recUPreSN)²`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Quantum.Sphincs (Key keyOf msgPos Disclosures)

namespace Quantum.Qrom.Sphincs.Multi

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR liftRead extWeight sumWeight extCls
  NoBot le_sq_add_of_forall_lin totalWeight_le_lin totalWeight_le_add
  totalWeight_le_of_forallQueries)
open Quantum.Xmss.Hybrid (totalWeight_le_totalWeight totalWeight_const_mul_weight
  totalWeight_chargeTrace_le)

attribute [local irreducible] sphincsRom

-- Keep elaboration from unfolding `univ` of the large `Fin` types.
attribute [local irreducible] Fin.fintype

/- Instance search for the registers over `Finset (TPosN n)` exceeds the default size. -/
set_option synthInstance.maxSize 2000

variable {n : ℕ} {pk : Fin n → PublicKey} {hon : Fin n → HonestCells} {S : Fin n → Disclosures}

/-! ## A trial read -/

/-- A read cell at the encoding slot of its owner's unselected key has no target. -/
theorem tgtRSN_enc_none {W : Hw PairOut Qrom.HashDomain} {m : QMemSN n} {z : Qrom.HashDomain}
    {i : Fin n} {K : Key} (hz : slotOf (pk i) z = some (.enc K.1 K.2.1 K.2.2))
    (ho : ownerS pk z = some i) (hm : m.2 i K = none) :
    tgtRSN pk hon S W m z = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun y hy ↦ by
    rcases hy with h | h
    · have h' : tgtDigestN pk hon W.1 m.2 z = some (pairDigest y) := h
      rw [tgtDigestN_of_owner _ _ ho, tgtDigest_enc_none _ hz hm] at h'
      cases h'
    · exact hmsgCall_ne_zero_of_enc hz h.1

open scoped Classical in
/-- **The flipping pairs of a trial read** at an empty, not hardwired cell of an unselected key:
at most `2^384 · encCwCountN`. -/
theorem card_hFlip_trialReadSN_le {z : Qrom.HashDomain} {i : Fin n} {K : Key}
    (hz : slotOf (pk i) z = some (.enc K.1 K.2.1 K.2.2)) (ho : ownerS pk z = some i)
    (q : Unit × RRegSN n (SelMemN n)) (hW : q.2.2.1.1 z = none) (hD : q.2.1.1 z = none)
    (hm : memAtS q.2 (i, K) = none) :
    (Finset.univ.filter (hFlip (BadRQN pk hon S) z (trialUpdSN z (i, K)) q)).card ≤
      encCwCountN pk (unionH q.2) i K * (2 ^ 128 * 2 ^ 256) := by
  obtain ⟨u₀, s⟩ := q
  have hm' : s.2.2.2 i K = none := hm
  have hsel : ∀ v, trialUpdSN z (i, K) s.2.2 (some v) = (s.2.2.1, cwSelN s.2.2.2 i K z v) :=
    fun v ↦ congrArg (Prod.mk s.2.2.1) (cwUpdN_some_of_none i K z hm' v)
  by_cases hb : s ∈ BadRQN pk hon S
  · -- Inside the event, a read of an empty cell keeps it.
    refine (Nat.le_zero.mpr (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr
      fun v _ hv ↦ ?_))).trans (Nat.zero_le _)
    have hfill : ∀ (u : Option PairOut) (m' : QMemSN n),
        (∀ x, ∀ y ∈ tgtRSN pk hon S s.2.1 s.2.2 x, y ∈ tgtRSN pk hon S s.2.1 m' x) →
        ((Function.update s.1.1 z u, s.1.2), s.2.1, m') ∈ BadRQN pk hon S :=
      fun u m' hm ↦ mem_cellTargetBad_fill hb hD u m' hm
    have hmono : ∀ x, ∀ y ∈ tgtRSN pk hon S s.2.1 s.2.2 x,
        y ∈ tgtRSN pk hon S s.2.1 (trialUpdSN z (i, K) s.2.2 (some v)) x := by
      intro x y hy
      rw [hsel]
      rcases hy with h | h
      · exact .inl (tgtDigestN_cwSelN_mono hm' z v h)
      · exact .inr (mem_covTgtN_memory h)
    rcases hv with hv | ⟨u, hu⟩
    · exact hv (iff_of_true (hfill (some v) s.2.2 fun _ _ h ↦ h) hb)
    · exact hu (iff_of_true (hfill u _ hmono) (hfill u s.2.2 fun _ _ h ↦ h))
  · -- An unselected key: the codeword flips of Events' `card_flip_readCwN_le`.
    have hsr : SelectReadN pk (s.1, s.2.1, s.2.2.2) z i K := ⟨hW, hD, hm', hz, ho⟩
    have hnb : (s.1, s.2.1, s.2.2.2) ∉ BadQN pk hon S := hb
    have hnot : ∀ u : Option PairOut,
        ((Function.update s.1.1 z u, s.1.2), s.2.1, s.2.2) ∉ BadRQN pk hon S :=
      fun u ↦ not_mem_cellTargetBad_readH hb s.2.2 (tgtRSN_enc_none hz ho hm')
        (fun _ _ _ h ↦ h) u
    refine le_trans (Finset.card_le_card fun v hv ↦ ?_) (card_flip_readCwN_le hnb hsr)
    rw [Finset.mem_filter] at hv ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hv.2 with hv | ⟨u, hu⟩
    · exact absurd (iff_of_false (hnot (some v)) hb) hv
    · refine ⟨u, ?_⟩
      have h1 : ((Function.update s.1.1 z u, s.1.2), s.2.1,
          trialUpdSN z (i, K) s.2.2 (some v)) ∈ BadRQN pk hon S := by
        by_contra h2
        exact hu (iff_of_false h2 (hnot u))
      rw [hsel] at h1
      exact h1

/-- **A recorded flip of a trial read** is recorded at an unselected key, given the key is
unselected. -/
theorem recFlip_trialReadSN {z : Qrom.HashDomain} {κ : UKeyS n}
    {q : Unit × RRegSN n (SelMemN n)} (hm : memAtS q.2 κ = none)
    (h : RecFlip (BadRQN pk hon S) z (trialUpdSN z κ) q) :
    q.2.1.1 z ≠ none ∧ memAtS q.2 κ = none := by
  obtain ⟨y, hy, -⟩ := h
  exact ⟨by rw [hy]; exact Option.some_ne_none y, hm⟩

/-- **The linear charge of a trial read**: `2^-127 encWtSN` plus `2/|Y × Y|` per unit of trace. -/
noncomputable def aQSN (pk : Fin n → PublicKey) (c : HwRead PairOut Qrom.HashDomain (QMemSN n))
    (σ : Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ) : ℝ≥0∞ :=
  (2 ^ 127 : ℝ≥0∞)⁻¹ * trialWSN (encWtSN pk) c σ +
    ENNReal.ofReal (2 / Fintype.card PairOut * σ.trace.re)

/-- **The recorded flip mass of a trial read**: `recUWtSN`. -/
noncomputable def pQSN (c : HwRead PairOut Qrom.HashDomain (QMemSN n))
    (σ : Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ) : ℝ≥0∞ :=
  trialWSN recUWtSN c σ

/-- **A trial read, linearized**: on an input with the read cell not hardwired and the key
unselected, for every `s > 0`, the refined cost is at most `(1 + s) aQSN + (1 + 1/s) pQSN`. -/
theorem readCost_trialReadSN_le {z : Qrom.HashDomain} {i : Fin n} {K : Key}
    (hz : slotOf (pk i) z = some (.enc K.1 K.2.1 K.2.2)) (ho : ownerS pk z = some i)
    {σ : Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ}
    (hσ : σ.PosSemidef) (hW : ∀ q, σ q q ≠ 0 → q.2.2.1.1 z = none)
    (hm : ∀ q, σ q q ≠ 0 → memAtS q.2 (i, K) = none) {s : ℝ} (hs : 0 < s) :
    readCost (BadRQN pk hon S) (trialReadSN z (i, K)) σ ≤
      ENNReal.ofReal (1 + s) * aQSN pk (trialReadSN z (i, K)) σ +
        ENNReal.ofReal (1 + s⁻¹) * pQSN (trialReadSN z (i, K)) σ := by
  classical
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have htr : σ.trace.re = ∑ q, (σ q q).re := by rw [Matrix.trace, Complex.re_sum]; rfl
  have hN : (0 : ℝ) < Fintype.card PairOut := Nat.cast_pos.mpr Fintype.card_pos
  refine (readCost_readH_le_lin (BadRQN pk hon S) z (trialUpdSN z (i, K)) hσ hs).trans
    (add_le_add (mul_le_mul_of_nonneg_left ?_ zero_le) (mul_le_mul_of_nonneg_left ?_ zero_le))
  · -- The linear part.
    set E : ℝ := ∑ q, encWtSN pk z (i, K) q.2 * (σ q q).re
    have h2 : (2 : ℝ) * (2 ^ 128)⁻¹ = (2 ^ 127)⁻¹ := by norm_num
    have hE0 : 0 ≤ E := Finset.sum_nonneg fun q _ ↦ mul_nonneg (by
      unfold encWtSN; split_ifs <;> positivity) (hre q)
    have hkey : readHA (BadRQN pk hon S) z (trialUpdSN z (i, K)) σ ≤
        (2 ^ 127 : ℝ)⁻¹ * E + 2 / Fintype.card PairOut * σ.trace.re := by
      rw [htr, ← h2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      unfold readHA
      refine Finset.sum_le_sum fun q _ ↦ ?_
      by_cases h0 : σ q q = 0
      · simp only [h0, Complex.zero_re, mul_zero, add_zero, le_refl]
      have hWq := hW q h0
      have hmq := hm q h0
      rw [ite_eq_left hWq]
      have hc : (2 : ℝ) * (2 ^ 128)⁻¹ * (encWtSN pk z (i, K) q.2 * (σ q q).re) +
          2 / Fintype.card PairOut * (σ q q).re =
          (2 * (2 ^ 128)⁻¹ * encWtSN pk z (i, K) q.2 + 2 / Fintype.card PairOut) *
            (σ q q).re := by ring
      rw [hc]
      refine mul_le_mul_of_nonneg_right ?_ (hre q)
      have he0 : 0 ≤ encWtSN pk z (i, K) q.2 := by unfold encWtSN; split_ifs <;> positivity
      by_cases hD : q.2.1.1 z = none
      · rw [ite_eq_left hD]
        have hf := card_hFlip_trialReadSN_le (hon := hon) (S := S) hz ho q hWq hD hmq
        have hw : encWtSN pk z (i, K) q.2 = encCwCountN pk (unionH q.2) i K := by
          unfold encWtSN
          rw [ite_eq_left ⟨hD, hmq⟩]
        have hf' : ((Finset.univ.filter (hFlip (BadRQN pk hon S) z (trialUpdSN z (i, K)) q)).card :
            ℝ) / Fintype.card PairOut ≤ (2 ^ 128)⁻¹ * encWtSN pk z (i, K) q.2 := by
          calc ((Finset.univ.filter (hFlip (BadRQN pk hon S) z (trialUpdSN z (i, K)) q)).card :
                ℝ) / Fintype.card PairOut ≤
                ((encCwCountN pk (unionH q.2) i K * (2 ^ 128 * 2 ^ 256) : ℕ) : ℝ) /
                  Fintype.card PairOut :=
                div_le_div_of_nonneg_right (Nat.cast_le.mpr hf) hN.le
            _ = (2 ^ 128)⁻¹ * encWtSN pk z (i, K) q.2 := by
                rw [Nat.cast_mul, mul_div_assoc, pairFiber_div_card_real, hw, mul_comm]
        rw [add_div, mul_div_assoc]
        linarith
      · rw [ite_eq_right hD]
        have : 0 ≤ 2 * (2 ^ 128 : ℝ)⁻¹ * encWtSN pk z (i, K) q.2 :=
          mul_nonneg (by positivity) he0
        linarith
    refine (ENNReal.ofReal_le_ofReal hkey).trans ?_
    unfold aQSN
    rw [trialWSN_trialReadSN _ z (i, K),
      ENNReal.ofReal_add (mul_nonneg (by positivity) hE0)
        (mul_nonneg (by positivity) (Complex.nonneg_iff.1 hσ.trace_nonneg).1),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  · -- The recorded part.
    rw [pQSN, trialWSN_trialReadSN _ z (i, K)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold readHP
    refine Finset.sum_le_sum fun q _ ↦ ?_
    by_cases h0 : σ q q = 0
    · simp only [h0, Complex.zero_re, mul_zero, le_refl]
    refine mul_le_mul_of_nonneg_right ?_ (hre q)
    by_cases hp : q.2.2.1.1 z = none ∧ RecFlip (BadRQN pk hon S) z (trialUpdSN z (i, K)) q
    · rw [ite_eq_left hp]
      unfold recUWtSN
      rw [ite_eq_left (recFlip_trialReadSN (hm q h0) hp.2)]
    · rw [ite_eq_right hp]
      unfold recUWtSN
      split_ifs <;> norm_num

/-! ## Programs of exempt cells -/

/-- **A program of an exempt cell costs nothing.** -/
theorem flipCost_programH_badRQN_eq_zero {z : Qrom.HashDomain} (hz : ExemptCellN pk hon z)
    (a : PairOut)
    {σ : Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ}
    (hσ : σ.PosSemidef) :
    flipCost (BadRQN pk hon S) (hwProgKraus (.programH z a)) 0 σ = 0 :=
  flipCost_programH_cellTargetBad_eq_zero z a hσ fun q _ _ ↦
    programH_badQN_conds (S := S) (W := q.2.2.1) (m := q.2.2.2.2) hz a

/-! ## The prefix -/

/-- The trace weight of the read and program ports. -/
noncomputable def trWSN : ∀ i : (RSpecSN n (SelMemN n)).Port,
    Matrix ((RSpecSN n (SelMemN n)).In i × RDSN n)
      ((RSpecSN n (SelMemN n)).In i × RDSN n) ℂ → ℝ≥0∞ :=
  extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re)

/-- **The trace-weighted classical calls**: with at most `K` classical calls on every path, the
traces of the inputs of the read and program calls of a program from `initQSN` add up to at most
`K`. -/
theorem totalWeight_trWSN_le {Ω : QReg → Type}
    (x : QuantumComp LocalSig.instruments.{0} (RSpecSN n (SelMemN n)) Ω (QReg.of Unit)) {K : ℕ}
    (hK : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls PairOut Qrom.HashDomain (QMemSN n) (recSpec (TPosN n)
        (SelMemN n)) i then 1 else 0) K) :
    (runtimeR (m0SN (n := n))).totalWeight .instruments trWSN x initQSN ≤ K := by
  refine (totalWeight_le_totalWeight (runtimeR (m0SN (n := n))) .instruments
    (w' := fun i σ ↦ ((if extCls PairOut Qrom.HashDomain (QMemSN n) (recSpec (TPosN n)
      (SelMemN n)) i then 1 else 0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re)
    (fun i σ _ ↦ ?_) x initQSN_posSemidef).trans ?_
  · rcases i with ((p | c) | c) | T <;> simp [trWSN, extWeight, sumWeight, hwCost, extCls, hwCls]
    all_goals exact le_of_eq rfl
  · refine (totalWeight_chargeTrace_le (runtimeR (m0SN (n := n))) .instruments _ x hK
      initQSN_posSemidef).trans ?_
    calc (K : ℝ≥0∞) * ENNReal.ofReal (initQSN (n := n)).trace.re ≤ K * 1 := by
          gcongr
          exact ofReal_trace_initQSN_le_one
      _ = K := mul_one _

variable (pk hon S) in
/-- **The prefix's classical costs at the public keys `pk`**: on prefix calls satisfying
`PreInvQSN`, with at most `K` classical calls,
`twPQSN ≤ (√(2^-127 encPre + (2/|Y × Y|) K) + √recUPreSN)²`, the Enc weights at `pk`. -/
theorem twPQSN_le_pk (A : MuAdversaryS n) (θ : TValsN n) (hinv : PrefixInvQSN pk hon A θ)
    {K : ℕ} (hK : IFreeM.IsChargeBound (prefixQSN (strPolN n) A θ)
      (portCharge fun i ↦ if extCls PairOut Qrom.HashDomain (QMemSN n) (recSpec (TPosN n)
        (SelMemN n)) i then 1 else 0) K) :
    twPQSN pk hon S A θ ≤ (((2 ^ 127 : ℝ≥0∞)⁻¹ * preTotSN A θ (trialWSN (encWtSN pk)) +
      ENNReal.ofReal (2 / Fintype.card PairOut) * K) ^ (2⁻¹ : ℝ) +
        recUPreSN A θ ^ (2⁻¹ : ℝ)) ^ 2 := by
  obtain ⟨Q, hQ, hx⟩ := hinv
  set wa : ∀ i : (RSpecSN n (SelMemN n)).Port,
      Matrix ((RSpecSN n (SelMemN n)).In i × RDSN n)
        ((RSpecSN n (SelMemN n)).In i × RDSN n) ℂ → ℝ≥0∞ :=
    extWeight (hwCost (aQSN pk) fun _ _ ↦ 0)
  set wp : ∀ i : (RSpecSN n (SelMemN n)).Port,
      Matrix ((RSpecSN n (SelMemN n)).In i × RDSN n)
        ((RSpecSN n (SelMemN n)).In i × RDSN n) ℂ → ℝ≥0∞ :=
    extWeight (hwCost pQSN fun _ _ ↦ 0)
  -- The linear charge along the prefix.
  have ha : (runtimeR (m0SN (n := n))).totalWeight .instruments wa (prefixQSN (strPolN n) A θ)
      initQSN ≤ (2 ^ 127 : ℝ≥0∞)⁻¹ * preTotSN A θ (trialWSN (encWtSN pk)) +
        ENNReal.ofReal (2 / Fintype.card PairOut) * K := by
    refine (totalWeight_le_add (runtimeR (m0SN (n := n))) .instruments wa
      (extWeight (hwCost (trialWSN (encWtSN pk)) fun _ _ ↦ 0))
      (fun i σ ↦ ENNReal.ofReal (2 / Fintype.card PairOut) * trWSN i σ)
      (2 ^ 127 : ℝ≥0∞)⁻¹ 1 (fun i σ _ ↦ ?_) (prefixQSN (strPolN n) A θ)
        initQSN_posSemidef).trans ?_
    · rcases i with ((p | c) | c) | T
      · exact zero_le
      · show aQSN pk c σ ≤ (2 ^ 127 : ℝ≥0∞)⁻¹ * trialWSN (encWtSN pk) c σ +
          1 * (ENNReal.ofReal (2 / Fintype.card PairOut) * ENNReal.ofReal σ.trace.re)
        unfold aQSN
        rw [one_mul, ← ENNReal.ofReal_mul (by positivity)]
        exact le_rfl
      · exact zero_le
      · exact zero_le
    · rw [one_mul]
      refine add_le_add le_rfl ((le_of_eq (totalWeight_const_mul_weight
        (runtimeR (m0SN (n := n))) .instruments (ENNReal.ofReal (2 / Fintype.card PairOut))
          trWSN (prefixQSN (strPolN n) A θ) initQSN)).trans ?_)
      exact mul_le_mul_of_nonneg_left (totalWeight_trWSN_le _ hK) zero_le
  refine (le_sq_add_of_forall_lin (c := 0) fun s hs ↦ ?_).trans_eq (add_zero _)
  rw [add_zero]
  refine (totalWeight_le_of_forallQueries (runtimeR (m0SN (n := n))) .instruments
    (PreInvQSN pk hon) hQ
    (w' := fun i σ ↦ ENNReal.ofReal (1 + s) * wa i σ + ENNReal.ofReal (1 + s⁻¹) * wp i σ)
    (fun i σ hσ hI ↦ ?_) (prefixQSN (strPolN n) A θ) initQSN_posSemidef hx).trans ?_
  · rcases i with ((p | c) | c) | T
    · exact zero_le
    · obtain ⟨⟨z, i, K, hz, ho, rfl⟩, hEF, hSel, hnb⟩ := hI
      show readCostT (BadRQN pk hon S) (trialReadSN z (i, K)) σ ≤
        ENNReal.ofReal (1 + s) * aQSN pk (trialReadSN z (i, K)) σ +
          ENNReal.ofReal (1 + s⁻¹) * pQSN (trialReadSN z (i, K)) σ
      have hnb' : ReadNoBot (trialReadSN z (i, K)) σ := readNoBot_of_noBot _ hnb
      unfold readCostT
      rw [ite_eq_left hnb']
      refine readCost_trialReadSN_le hz ho hσ (fun q hq ↦ ?_) (fun q hq ↦ ?_) hs
      · have hq' := (hEF q q hq).1
        by_contra hw
        exact hq' z (Option.ne_none_iff_isSome.mp hw) i K hz
      · exact (hSel q q hq).1 (i, K) rfl
    · obtain ⟨⟨z, a, rfl, hz⟩, -, -, -⟩ := hI
      show flipCost (BadRQN pk hon S) (hwProgKraus (.programH z a)) 0 σ ≤
        ENNReal.ofReal (1 + s) * 0 + ENNReal.ofReal (1 + s⁻¹) * 0
      rw [flipCost_programH_badRQN_eq_zero hz a hσ]
      exact zero_le
    · exact zero_le
  · refine (totalWeight_le_add (runtimeR (m0SN (n := n))) .instruments _ wa wp
      (ENNReal.ofReal (1 + s)) (ENNReal.ofReal (1 + s⁻¹)) (fun _ _ _ ↦ le_rfl)
        (prefixQSN (strPolN n) A θ) initQSN_posSemidef).trans ?_
    exact add_le_add (mul_le_mul_of_nonneg_left ha zero_le)
      (mul_le_mul_of_nonneg_left le_rfl zero_le)

variable (hon S) in
/-- **The prefix's classical costs at the canonical public keys**:
`twPQSN ≤ (√(2^-127 encPreSN + (2/|Y × Y|) K) + √recUPreSN)²`. -/
theorem twPQSN_le (A : MuAdversaryS n) (θ : TValsN n) (hinv : PrefixInvQSN (pkQN θ) hon A θ)
    {K : ℕ} (hK : IFreeM.IsChargeBound (prefixQSN (strPolN n) A θ)
      (portCharge fun i ↦ if extCls PairOut Qrom.HashDomain (QMemSN n) (recSpec (TPosN n)
        (SelMemN n)) i then 1 else 0) K) :
    twPQSN (pkQN θ) hon S A θ ≤ (((2 ^ 127 : ℝ≥0∞)⁻¹ * encPreSN A θ +
      ENNReal.ofReal (2 / Fintype.card PairOut) * K) ^ (2⁻¹ : ℝ) +
        recUPreSN A θ ^ (2⁻¹ : ℝ)) ^ 2 :=
  twPQSN_le_pk (pkQN θ) hon S A θ hinv hK

end Quantum.Qrom.Sphincs.Multi

end
