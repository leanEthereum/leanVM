module

public import Quantum.Qrom.Xmss.Multi.Costs.Defs

@[expose] public section

/-!
# The classical costs of the `n`-user runtime 2: the ports of the challenge prefix

The `n`-user analog of `Quantum.Qrom.Xmss.Costs.Ports`, for the event `BadRQN hon P`:

* **A trial read** of user `i`'s key `κ = (i, l, e)` at a cell `z` owned by `i`
  (`card_hFlip_trialReadN_le`, `readCost_trialReadN_le`): the key is unselected at every trial
  read (`selOk`), so on an empty cell the flipping values are the codeword outputs hitting a
  codeword cell of `i`'s key (Events' `card_flip_readCwN_le`), and a recorded cell flips only with
  the key unselected. For every `s > 0` the refined cost is at most `(1 + s) aQN + (1 + 1/s) pQN`,
  `aQN = 2^-127 encWtN + 2/|Y|` per unit of trace, `pQN = recUWtN`.
* **A program of an exempt cell** costs nothing (`flipCost_programH_badRQN_eq_zero`).
* **The prefix** (`twPQN_le`): on calls satisfying `PreInvQN` (`PrefixInvQN`), with at most `K`
  classical calls, `twPQN ≤ (√(2^-127 encPreN + (2/|Y|) K) + √recUPreN)²`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Qrom.Xmss.Multi

open Quantum QuantumRuntime Quantum.Sponge HashSig LeanXmss
open Quantum.Xmss (Slot)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR liftRead extWeight sumWeight extCls
  NoBot le_sq_add_of_forall_lin totalWeight_le_lin totalWeight_le_add
  totalWeight_le_of_forallQueries)
open Quantum.Xmss.Hybrid (totalWeight_le_totalWeight totalWeight_const_mul_weight
  totalWeight_chargeTrace_le)
open Quantum.Qrom.MultiUser (ownerOf)

attribute [local irreducible] xmssRom

variable {n : ℕ} {hon : Fin n → HonestCells} {P : Fin n → PublicParameter}

/-! ## A trial read -/

theorem trialReadN_eq (z : HashDomain) (κ : UKey n) :
    trialReadN z κ = .readH z (trialUpdN z κ) :=
  rfl

/-- A read cell at the message slot of its owner's unselected key has no target. -/
theorem tgtRN_msg_none {W : Hw HashOutput HashDomain} {m : QMemN n} {z : HashDomain} {i : Fin n}
    {l : Layer} {e : KeyIndex} (hz : slotOf z = some (.msg l e))
    (ho : ownerOf P prefixOf z = some i) (hm : m.2 i l e = none) :
    tgtRN hon P W m z = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun y hy ↦ by
    have h : tgtDigestN hon P W.1 m.2 z = some (truncateHash y) := hy
    rw [tgtDigestN_of_owner _ _ ho, tgtDigest_msg_none _ hz hm] at h
    cases h

open scoped Classical in
/-- **The flipping values of a trial read** at an empty, not hardwired cell of an unselected key:
at most `2^128 · msgCwCountN`. -/
theorem card_hFlip_trialReadN_le {z : HashDomain} {i : Fin n} {l : Layer} {e : KeyIndex}
    (hz : slotOf z = some (.msg l e)) (ho : ownerOf P prefixOf z = some i)
    (q : Unit × RRegN n (SelMemN n)) (hW : q.2.2.1.1 z = none) (hD : q.2.1.1 z = none)
    (hm : memAt q.2 (i, l, e) = none) :
    (Finset.univ.filter (hFlip (BadRQN hon P) z (trialUpdN z (i, l, e)) q)).card ≤
      msgCwCountN P (unionH q.2) i l e * 2 ^ 128 := by
  obtain ⟨u₀, s⟩ := q
  have hm' : s.2.2.2 i l e = none := hm
  have hsel : ∀ v, trialUpdN z (i, l, e) s.2.2 (some v) = (s.2.2.1, cwSelN s.2.2.2 i l e z v) :=
    fun v ↦ by
      show (s.2.2.1, cwUpdN i l e z s.2.2.2 (some v)) = _
      rw [cwUpdN_some_of_none i l e z hm' v]
  by_cases hb : s ∈ BadRQN hon P
  · -- Inside the event, a read of an empty cell keeps it.
    refine (Nat.le_zero.mpr (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr
      fun v _ hv ↦ ?_))).trans (Nat.zero_le _)
    have hfill : ∀ (u : Option HashOutput) (m' : QMemN n),
        (∀ x, ∀ y ∈ tgtRN hon P s.2.1 s.2.2 x, y ∈ tgtRN hon P s.2.1 m' x) →
        ((Function.update s.1.1 z u, s.1.2), s.2.1, m') ∈ BadRQN hon P :=
      fun u m' hm ↦ mem_cellTargetBad_fill hb hD u m' hm
    have hmono : ∀ x, ∀ y ∈ tgtRN hon P s.2.1 s.2.2 x,
        y ∈ tgtRN hon P s.2.1 (trialUpdN z (i, l, e) s.2.2 (some v)) x := by
      intro x y hy
      rw [hsel]
      exact tgtDigestN_cwSelN_mono hm' z v hy
    rcases hv with hv | ⟨u, hu⟩
    · exact hv (iff_of_true (hfill (some v) s.2.2 fun _ _ h ↦ h) hb)
    · exact hu (iff_of_true (hfill u _ hmono) (hfill u s.2.2 fun _ _ h ↦ h))
  · -- An unselected key: the codeword flips of Events' `card_flip_readCwN_le`.
    have hsr : SelectReadN P (s.1, s.2.1, s.2.2.2) z i l e := ⟨hW, hD, hm', hz, ho⟩
    have hnb : (s.1, s.2.1, s.2.2.2) ∉ BadQN hon P := hb
    have hnot : ∀ u : Option HashOutput,
        ((Function.update s.1.1 z u, s.1.2), s.2.1, s.2.2) ∉ BadRQN hon P :=
      fun u ↦ not_mem_cellTargetBad_readH hb s.2.2 (tgtRN_msg_none hz ho hm')
        (fun _ _ _ h ↦ h) u
    refine le_trans (Finset.card_le_card fun v hv ↦ ?_) (card_flip_readCwN_le hnb hsr)
    rw [Finset.mem_filter] at hv ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hv.2 with hv | ⟨u, hu⟩
    · exact absurd (iff_of_false (hnot (some v)) hb) hv
    · refine ⟨u, ?_⟩
      have h1 : ((Function.update s.1.1 z u, s.1.2), s.2.1,
          trialUpdN z (i, l, e) s.2.2 (some v)) ∈ BadRQN hon P := by
        by_contra h2
        exact hu (iff_of_false h2 (hnot u))
      rw [hsel] at h1
      exact h1

/-- **A recorded flip of a trial read** is recorded at an unselected key, given the key is
unselected. -/
theorem recFlip_trialReadN {z : HashDomain} {κ : UKey n} {q : Unit × RRegN n (SelMemN n)}
    (hm : memAt q.2 κ = none) (h : RecFlip (BadRQN hon P) z (trialUpdN z κ) q) :
    q.2.1.1 z ≠ none ∧ memAt q.2 κ = none := by
  obtain ⟨y, hy, -⟩ := h
  exact ⟨by rw [hy]; exact Option.some_ne_none y, hm⟩

/-- **The linear charge of a trial read**: `2^-127 encWtN` plus `2/|Y|` per unit of trace. -/
noncomputable def aQN (P : Fin n → PublicParameter) (c : HwRead HashOutput HashDomain (QMemN n))
    (σ : Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ) : ℝ≥0∞ :=
  (2 ^ 127 : ℝ≥0∞)⁻¹ * trialWN (encWtN P) c σ +
    ENNReal.ofReal (2 / Fintype.card HashOutput * σ.trace.re)

/-- **The recorded flip mass of a trial read**: `recUWtN`. -/
noncomputable def pQN (c : HwRead HashOutput HashDomain (QMemN n))
    (σ : Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ) : ℝ≥0∞ :=
  trialWN recUWtN c σ

/-- **A trial read, linearized**: on an input with the read cell not hardwired and the key
unselected, for every `s > 0`, the refined cost is at most `(1 + s) aQN + (1 + 1/s) pQN`. -/
theorem readCost_trialReadN_le {z : HashDomain} {i : Fin n} {l : Layer} {e : KeyIndex}
    (hz : slotOf z = some (.msg l e)) (ho : ownerOf P prefixOf z = some i)
    {σ : Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ} (hσ : σ.PosSemidef)
    (hW : ∀ q, σ q q ≠ 0 → q.2.2.1.1 z = none)
    (hm : ∀ q, σ q q ≠ 0 → memAt q.2 (i, l, e) = none) {s : ℝ} (hs : 0 < s) :
    readCost (BadRQN hon P) (trialReadN z (i, l, e)) σ ≤
      ENNReal.ofReal (1 + s) * aQN P (trialReadN z (i, l, e)) σ +
        ENNReal.ofReal (1 + s⁻¹) * pQN (trialReadN z (i, l, e)) σ := by
  classical
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have htr : σ.trace.re = ∑ q, (σ q q).re := by rw [Matrix.trace, Complex.re_sum]; rfl
  have hN : (0 : ℝ) < Fintype.card HashOutput := Nat.cast_pos.mpr Fintype.card_pos
  have h2N : (2 : ℝ) ^ 128 / Fintype.card HashOutput = (2 ^ 128)⁻¹ := two_pow_div_card_hashOutput
  rw [trialReadN_eq]
  refine (readCost_readH_le_lin (BadRQN hon P) z (trialUpdN z (i, l, e)) hσ hs).trans
    (add_le_add (mul_le_mul_of_nonneg_left ?_ zero_le) (mul_le_mul_of_nonneg_left ?_ zero_le))
  · -- The linear part.
    set E : ℝ := ∑ q, encWtN P z (i, l, e) q.2 * (σ q q).re
    have hE0 : 0 ≤ E := Finset.sum_nonneg fun q _ ↦ mul_nonneg (by
      unfold encWtN; split_ifs <;> positivity) (hre q)
    have hkey : readHA (BadRQN hon P) z (trialUpdN z (i, l, e)) σ ≤
        (2 ^ 127 : ℝ)⁻¹ * E + 2 / Fintype.card HashOutput * σ.trace.re := by
      rw [htr, ← two_inv_two_pow_128, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      unfold readHA
      refine Finset.sum_le_sum fun q _ ↦ ?_
      by_cases h0 : σ q q = 0
      · simp only [h0, Complex.zero_re, mul_zero, add_zero, le_refl]
      have hWq := hW q h0
      have hmq := hm q h0
      rw [ite_eq_left hWq]
      have hc : (2 : ℝ) * (2 ^ 128)⁻¹ * (encWtN P z (i, l, e) q.2 * (σ q q).re) +
          2 / Fintype.card HashOutput * (σ q q).re =
          (2 * (2 ^ 128)⁻¹ * encWtN P z (i, l, e) q.2 + 2 / Fintype.card HashOutput) *
            (σ q q).re := by ring
      rw [hc]
      refine mul_le_mul_of_nonneg_right ?_ (hre q)
      have he0 : 0 ≤ encWtN P z (i, l, e) q.2 := by unfold encWtN; split_ifs <;> positivity
      by_cases hD : q.2.1.1 z = none
      · rw [ite_eq_left hD]
        have hf := card_hFlip_trialReadN_le (hon := hon) hz ho q hWq hD hmq
        have hw : encWtN P z (i, l, e) q.2 = msgCwCountN P (unionH q.2) i l e := by
          unfold encWtN
          rw [ite_eq_left ⟨hD, hmq⟩]
        have hf' : ((Finset.univ.filter (hFlip (BadRQN hon P) z (trialUpdN z (i, l, e)) q)).card :
            ℝ) / Fintype.card HashOutput ≤ (2 ^ 128)⁻¹ * encWtN P z (i, l, e) q.2 := by
          rw [div_le_iff₀ hN, hw]
          refine (Nat.cast_le.mpr hf).trans ?_
          rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← h2N, mul_comm (2 ^ 128 /
            (Fintype.card HashOutput : ℝ)), mul_assoc, div_mul_cancel₀ _ hN.ne']
        rw [add_div, mul_div_assoc]
        linarith
      · rw [ite_eq_right hD]
        have : 0 ≤ 2 * (2 ^ 128 : ℝ)⁻¹ * encWtN P z (i, l, e) q.2 :=
          mul_nonneg (by positivity) he0
        linarith
    refine (ENNReal.ofReal_le_ofReal hkey).trans ?_
    unfold aQN
    rw [← trialReadN_eq, trialWN_trialReadN _ z (i, l, e),
      ENNReal.ofReal_add (mul_nonneg (by positivity) hE0)
        (mul_nonneg (by positivity) (Complex.nonneg_iff.1 hσ.trace_nonneg).1),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  · -- The recorded part.
    rw [← trialReadN_eq, pQN, trialWN_trialReadN _ z (i, l, e)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold readHP
    refine Finset.sum_le_sum fun q _ ↦ ?_
    by_cases h0 : σ q q = 0
    · simp only [h0, Complex.zero_re, mul_zero, le_refl]
    refine mul_le_mul_of_nonneg_right ?_ (hre q)
    by_cases hp : q.2.2.1.1 z = none ∧ RecFlip (BadRQN hon P) z (trialUpdN z (i, l, e)) q
    · rw [ite_eq_left hp]
      unfold recUWtN
      rw [ite_eq_left (recFlip_trialReadN (hm q h0) hp.2)]
    · rw [ite_eq_right hp]
      unfold recUWtN
      split_ifs <;> norm_num

/-! ## Programs of exempt cells -/

/-- **A program of an exempt cell costs nothing.** -/
theorem flipCost_programH_badRQN_eq_zero {z : HashDomain} (hz : ExemptCellN hon P z)
    (a : HashOutput) {σ : Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ}
    (hσ : σ.PosSemidef) :
    flipCost (BadRQN hon P) (hwProgKraus (.programH z a)) 0 σ = 0 :=
  flipCost_programH_cellTargetBad_eq_zero z a hσ fun q _ _ ↦
    ⟨fun _ hx _ hy ↦ (tgtDigestN_update_of_ne q.2.2.1.1 q.2.2.2.2 hx (some a)).symm.trans hy,
      fun hv ↦ Option.some_ne_none _
        ((hz.tgtDigestN_update q.2.2.1.1 q.2.2.2.2 a).symm.trans hv).symm⟩

/-! ## The prefix -/

/-- The trace weight of the read and program ports. -/
noncomputable def trWN : ∀ i : (RSpecN n (SelMemN n)).Port,
    Matrix ((RSpecN n (SelMemN n)).In i × RDN n)
      ((RSpecN n (SelMemN n)).In i × RDN n) ℂ → ℝ≥0∞ :=
  extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re)

/-- **The trace-weighted classical calls**: with at most `K` classical calls on every path, the
traces of the inputs of the read and program calls of a program from `initQN` add up to at most
`K`. -/
theorem totalWeight_trWN_le {Ω : QReg → Type}
    (x : QuantumComp LocalSig.instruments.{0} (RSpecN n (SelMemN n)) Ω (QReg.of Unit)) {K : ℕ}
    (hK : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n)
        (SelMemN n)) i then 1 else 0) K) :
    (runtimeR (m0N (n := n))).totalWeight .instruments trWN x initQN ≤ K := by
  refine (totalWeight_le_totalWeight (runtimeR (m0N (n := n))) .instruments
    (w' := fun i σ ↦ ((if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n)
      (SelMemN n)) i then 1 else 0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re)
    (fun i σ _ ↦ ?_) x initQN_posSemidef).trans ?_
  · rcases i with ((p | c) | c) | T <;> simp [trWN, extWeight, sumWeight, hwCost, extCls, hwCls]
    all_goals exact le_of_eq rfl
  · refine (totalWeight_chargeTrace_le (runtimeR (m0N (n := n))) .instruments _ x hK
      initQN_posSemidef).trans ?_
    calc (K : ℝ≥0∞) * ENNReal.ofReal (initQN (n := n)).trace.re ≤ K * 1 := by
          gcongr
          exact ofReal_trace_initQN_le_one
      _ = K := mul_one _

variable (hon P) in
/-- **The prefix's classical costs**: on prefix calls satisfying `PreInvQN`, with at most `K`
classical calls, `twPQN ≤ (√(2^-127 encPreN + (2/|Y|) K) + √recUPreN)²`. -/
theorem twPQN_le (A : MuAdversary n) (θ : HPosN n → Digest) (hinv : PrefixInvQN hon P A θ)
    {K : ℕ} (hK : IFreeM.IsChargeBound (prefixQN A θ)
      (portCharge fun i ↦ if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n)
        (SelMemN n)) i then 1 else 0) K) :
    twPQN hon P A θ ≤ (((2 ^ 127 : ℝ≥0∞)⁻¹ * encPreN P A θ +
      ENNReal.ofReal (2 / Fintype.card HashOutput) * K) ^ (2⁻¹ : ℝ) +
        recUPreN A θ ^ (2⁻¹ : ℝ)) ^ 2 := by
  obtain ⟨Q, hQ, hx⟩ := hinv
  set wa : ∀ i : (RSpecN n (SelMemN n)).Port,
      Matrix ((RSpecN n (SelMemN n)).In i × RDN n)
        ((RSpecN n (SelMemN n)).In i × RDN n) ℂ → ℝ≥0∞ :=
    extWeight (hwCost (aQN P) fun _ _ ↦ 0)
  set wp : ∀ i : (RSpecN n (SelMemN n)).Port,
      Matrix ((RSpecN n (SelMemN n)).In i × RDN n)
        ((RSpecN n (SelMemN n)).In i × RDN n) ℂ → ℝ≥0∞ :=
    extWeight (hwCost pQN fun _ _ ↦ 0)
  -- The linear charge along the prefix.
  have ha : (runtimeR (m0N (n := n))).totalWeight .instruments wa (prefixQN A θ) initQN ≤
      (2 ^ 127 : ℝ≥0∞)⁻¹ * encPreN P A θ +
        ENNReal.ofReal (2 / Fintype.card HashOutput) * K := by
    refine (totalWeight_le_add (runtimeR (m0N (n := n))) .instruments wa
      (extWeight (hwCost (trialWN (encWtN P)) fun _ _ ↦ 0))
      (fun i σ ↦ ENNReal.ofReal (2 / Fintype.card HashOutput) * trWN i σ)
      (2 ^ 127 : ℝ≥0∞)⁻¹ 1 (fun i σ _ ↦ ?_) (prefixQN A θ) initQN_posSemidef).trans ?_
    · rcases i with ((p | c) | c) | T
      · exact zero_le
      · show aQN P c σ ≤ (2 ^ 127 : ℝ≥0∞)⁻¹ * trialWN (encWtN P) c σ +
          1 * (ENNReal.ofReal (2 / Fintype.card HashOutput) * ENNReal.ofReal σ.trace.re)
        unfold aQN
        rw [one_mul, ← ENNReal.ofReal_mul (by positivity)]
        exact le_rfl
      · exact zero_le
      · exact zero_le
    · rw [one_mul]
      refine add_le_add le_rfl ((le_of_eq (totalWeight_const_mul_weight
        (runtimeR (m0N (n := n))) .instruments (ENNReal.ofReal (2 / Fintype.card HashOutput))
          trWN (prefixQN A θ) initQN)).trans ?_)
      exact mul_le_mul_of_nonneg_left (totalWeight_trWN_le _ hK) zero_le
  refine (le_sq_add_of_forall_lin (c := 0) fun s hs ↦ ?_).trans_eq (add_zero _)
  rw [add_zero]
  refine (totalWeight_le_of_forallQueries (runtimeR (m0N (n := n))) .instruments
    (PreInvQN hon P) hQ
    (w' := fun i σ ↦ ENNReal.ofReal (1 + s) * wa i σ + ENNReal.ofReal (1 + s⁻¹) * wp i σ)
    (fun i σ hσ hI ↦ ?_) (prefixQN A θ) initQN_posSemidef hx).trans ?_
  · rcases i with ((p | c) | c) | T
    · exact zero_le
    · obtain ⟨⟨z, i, l, e, hz, ho, rfl⟩, hMF, hSel, hnb⟩ := hI
      show readCostT (BadRQN hon P) (trialReadN z (i, l, e)) σ ≤
        ENNReal.ofReal (1 + s) * aQN P (trialReadN z (i, l, e)) σ +
          ENNReal.ofReal (1 + s⁻¹) * pQN (trialReadN z (i, l, e)) σ
      have hnb' : ReadNoBot (trialReadN z (i, l, e)) σ := readNoBot_of_noBot _ hnb
      unfold readCostT
      rw [ite_eq_left hnb']
      refine readCost_trialReadN_le hz ho hσ (fun q hq ↦ ?_) (fun q hq ↦ ?_) hs
      · have hq' := (hMF q q hq).1
        by_contra hw
        exact hq' z (Option.ne_none_iff_isSome.mp hw) l e hz
      · exact (hSel q q hq).1 (i, l, e) rfl
    · obtain ⟨⟨z, a, rfl, hz, -⟩, -, -, -⟩ := hI
      show flipCost (BadRQN hon P) (hwProgKraus (.programH z a)) 0 σ ≤
        ENNReal.ofReal (1 + s) * 0 + ENNReal.ofReal (1 + s⁻¹) * 0
      rw [flipCost_programH_badRQN_eq_zero hz a hσ]
      exact zero_le
    · exact zero_le
  · refine (totalWeight_le_add (runtimeR (m0N (n := n))) .instruments _ wa wp
      (ENNReal.ofReal (1 + s)) (ENNReal.ofReal (1 + s⁻¹)) (fun _ _ _ ↦ le_rfl) (prefixQN A θ)
        initQN_posSemidef).trans ?_
    exact add_le_add (mul_le_mul_of_nonneg_left ha zero_le)
      (mul_le_mul_of_nonneg_left le_rfl zero_le)

end Quantum.Qrom.Xmss.Multi

end
