module

public import Quantum.Qrom.Sphincs.Costs.Defs

@[expose] public section

/-!
# The classical costs of leanSPHINCS's runtime 2: the ports of the challenge prefix

The refined cost of each classical port of the prefix, for the event `BadRQ pk hon S`:

* **A trial read** (`card_hFlip_trialRead_le`, `recFlip_trialRead`, `readCost_trialRead_le`):
  for every `s > 0`, at most `(1 + s) aQ + (1 + 1/s) pQ` (CostRefined's
  `readCost_readH_le_lin`). On an empty read cell the pairs that flip the event are the codeword
  pairs hitting a codeword cell of the key's encoding slot (unselected key, Events'
  `card_flip_readCw_le`) or the one target digest of the cell (selected key): `aQ` pays
  `2^-127 (encWt + selWt)` plus `2/|Y × Y|` per unit of trace. A recorded read cell flips only if
  its key is unselected or its pair hits the selected digest (`recUWt + recSWt`, `pQ`). The read
  cell has no Cov target (an encoding cell is no `H_msg` call).
* **A program of an exempt cell** costs nothing (`flipCost_programH_badRQ_eq_zero`).
* **The prefix** (`twPQ_le`): on calls satisfying `PreInvQ` (`PrefixInvQ`), with at most `K`
  classical calls,
  `twPQ ≤ (√(2^-127 (encPre + selPre) + (2/|Y × Y|) K) + √(recUPre + recSPre))²`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Sphincs (Key keyOf msgPos)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR liftRead extWeight sumWeight extCls
  NoBot le_sq_add_of_forall_lin totalWeight_le_lin totalWeight_le_add
  totalWeight_le_of_forallQueries)
open Quantum.Xmss.Hybrid (totalWeight_le_totalWeight totalWeight_const_mul_weight
  totalWeight_chargeTrace_le)

attribute [local irreducible] sphincsRom

-- Keep elaboration from unfolding `univ` of the large `Fin` types.
attribute [local irreducible] Fin.fintype

variable {pk : PublicKey} {hon : HonestCells} {S : Quantum.Sphincs.Disclosures}

/-! ## A trial read -/

/-- A read cell at the encoding slot of an unselected key has no target. -/
theorem tgtR_enc_none {W : Hw PairOut Qrom.HashDomain} {m : QMem} {z : Qrom.HashDomain} {K : Key}
    (hz : slotOf pk z = some (.enc K.1 K.2.1 K.2.2)) (hm : m.2 K = none) :
    tgtR pk hon S W m z = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun y hy ↦ by
    rcases hy with h | h
    · have h' : tgtDigest pk hon W.1 m.2 z = some (pairDigest y) := h
      rw [tgtDigest_enc_none _ hz hm] at h'
      cases h'
    · exact hmsgCall_ne_zero_of_enc hz h.1

/-- **A trial read keeps or grows every target.** -/
theorem tgtR_trialUpdQ_mono {W : Hw PairOut Qrom.HashDomain} {m : QMem} {z : Qrom.HashDomain}
    {K : Key} (v : PairOut) (x : Qrom.HashDomain) (y : PairOut)
    (hy : y ∈ tgtR pk hon S W m x) : y ∈ tgtR pk hon S W (trialUpdQ K z m (some v)) x := by
  rcases hy with h | h
  · left
    show tgtDigest pk hon W.1 (cwUpd K z m.2 (some v)) x = some (pairDigest y)
    by_cases hm : m.2 K = none
    · rw [cwUpd_some_of_none K z hm v]
      exact tgtDigest_cwSel_mono hm z v h
    · rw [cwUpd_of_ne_none hm]
      exact h
  · exact .inr (mem_covTgt_memory h)

open scoped Classical in
/-- **The flipping pairs of a trial read** at an empty, not hardwired cell: at most
`2^384 · encCwCount` for an unselected key, `2^384` for a selected one. -/
theorem card_hFlip_trialRead_le {z : Qrom.HashDomain} {K : Key}
    (hz : slotOf pk z = some (.enc K.1 K.2.1 K.2.2)) (q : Unit × RegQ) (hW : q.2.2.1.1 z = none)
    (hD : q.2.1.1 z = none) :
    (Finset.univ.filter (hFlip (BadRQ pk hon S) z (trialUpdQ K z) q)).card ≤
      (if q.2.2.2.2 K = none then encCwCount pk (unionH q.2) K else 1) * (2 ^ 128 * 2 ^ 256) := by
  obtain ⟨u₀, s⟩ := q
  by_cases hb : s ∈ BadRQ pk hon S
  · -- Inside the event, a read of an empty cell keeps it.
    refine (Nat.le_zero.mpr (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr
      fun v _ hv ↦ ?_))).trans (Nat.zero_le _)
    have hfill : ∀ (u : Option PairOut) (m' : QMem),
        (∀ x, ∀ y ∈ tgtR pk hon S s.2.1 s.2.2 x, y ∈ tgtR pk hon S s.2.1 m' x) →
        ((Function.update s.1.1 z u, s.1.2), s.2.1, m') ∈ BadRQ pk hon S :=
      fun u m' hm ↦ mem_cellTargetBad_fill hb hD u m' hm
    rcases hv with hv | ⟨u, hu⟩
    · exact hv (iff_of_true (hfill (some v) s.2.2 fun _ _ h ↦ h) hb)
    · exact hu (iff_of_true (hfill u _ fun x y hy ↦ tgtR_trialUpdQ_mono v x y hy)
        (hfill u s.2.2 fun _ _ h ↦ h))
  · by_cases hm : s.2.2.2 K = none
    · -- An unselected key: the codeword flips of Events' `card_flip_readCw_le`.
      rw [ite_eq_left hm]
      have hsr : SelectRead pk (projQ s) z K := ⟨hW, hD, hm, hz⟩
      have hnb : projQ s ∉ BadQ pk hon S := hb
      have hnot : ∀ u : Option PairOut,
          ((Function.update s.1.1 z u, s.1.2), s.2.1, s.2.2) ∉ BadRQ pk hon S :=
        fun u ↦ not_mem_cellTargetBad_readH hb s.2.2 (tgtR_enc_none hz hm) (fun _ _ _ h ↦ h) u
      refine le_trans (Finset.card_le_card fun v hv ↦ ?_) (card_flip_readCw_le hnb hsr)
      rw [Finset.mem_filter] at hv ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hv.2 with hv | ⟨u, hu⟩
      · exact absurd (iff_of_false (hnot (some v)) hb) hv
      · refine ⟨u, ?_⟩
        have h1 : ((Function.update s.1.1 z u, s.1.2), s.2.1,
            trialUpdQ K z s.2.2 (some v)) ∈ BadRQ pk hon S := by
          by_contra h2
          exact hu (iff_of_false h2 (hnot u))
        have he : trialUpdQ K z s.2.2 (some v) = (s.2.2.1, cwSel s.2.2.2 K z v) := by
          show (s.2.2.1, cwUpd K z s.2.2.2 (some v)) = _
          rw [cwUpd_some_of_none K z hm v]
        rw [he] at h1
        exact h1
    · -- A selected key: the memory is kept, the cell's one target digest.
      rw [ite_eq_right hm, one_mul]
      have hkeep : ∀ v, trialUpdQ K z s.2.2 (some v) = s.2.2 := fun v ↦ by
        show (s.2.2.1, cwUpd K z s.2.2.2 (some v)) = s.2.2
        rw [cwUpd_of_ne_none hm]
      have hsub : Finset.univ.filter (hFlip (BadRQ pk hon S) z (trialUpdQ K z) ((), s)) ⊆
          Finset.univ.filter fun v : PairOut ↦
            tgtDigest pk hon s.2.1.1 s.2.2.2 z = some (pairDigest v) := by
        intro v hv
        rw [Finset.mem_filter] at hv ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        rcases hv.2 with hv | ⟨u, hu⟩
        · have h1 : ((Function.update s.1.1 z (some v), s.1.2), s.2) ∈ BadRQ pk hon S := by
            by_contra h2
            exact hv (iff_of_false h2 hb)
          obtain ⟨y, hy, hyt⟩ := exists_of_mem_cellTargetBad_updateH (o := some v) hb
            (fun _ _ _ h ↦ h) h1
          change (s.2.1.1 z).or (some v) = some y at hy
          rw [hW] at hy
          cases hy
          rcases hyt with h | h
          · exact h
          · exact absurd h.1 (hmsgCall_ne_zero_of_enc hz)
        · exact absurd (by rw [hkeep]) hu
      refine (Finset.card_le_card hsub).trans ?_
      rcases hd : tgtDigest pk hon s.2.1.1 s.2.2.2 z with _ | d
      · rw [Finset.filter_false_of_mem fun v _ h ↦ by cases h]
        simp
      · refine le_trans (Finset.card_le_card fun v hv ↦ ?_) (card_fiber_pairDigest_le d)
        rw [Finset.mem_filter] at hv ⊢
        exact ⟨Finset.mem_univ _, (Option.some.inj hv.2).symm⟩

/-- **A recorded flip of a trial read** is recorded at an unselected key or hits the selected
digest (`RecHitQ`). -/
theorem recFlip_trialRead {z : Qrom.HashDomain} {K : Key}
    (hz : slotOf pk z = some (.enc K.1 K.2.1 K.2.2)) {q : Unit × RegQ} (hW : q.2.2.1.1 z = none)
    (h : RecFlip (BadRQ pk hon S) z (trialUpdQ K z) q) :
    (q.2.1.1 z ≠ none ∧ q.2.2.2.2 K = none) ∨ RecHitQ z K q.2 := by
  obtain ⟨u₀, s⟩ := q
  obtain ⟨y, hy, h⟩ := h
  by_cases hm : s.2.2.2 K = none
  · exact .inl ⟨by rw [hy]; exact Option.some_ne_none y, hm⟩
  right
  obtain ⟨sel, hsel⟩ := Option.ne_none_iff_exists'.mp hm
  rcases h with h | ⟨u, hu⟩
  · -- The emptied register is outside, so the cell `z` alone puts the register inside.
    have hfill : ((Function.update s.1.1 z none, s.1.2), s.2) ∈ BadRQ pk hon S →
        s ∈ BadRQ pk hon S := by
      intro hb
      have h2 := mem_cellTargetBad_fill (z := z) hb (by simp) (some y) s.2.2 fun _ _ h ↦ h
      have h3 : Function.update (Function.update s.1.1 z none) z (some y) = s.1.1 := by
        rw [Function.update_idem, ← hy, Function.update_eq_self]
      simp only [h3] at h2
      exact h2
    have hs : s ∈ BadRQ pk hon S := by
      by_contra hs
      exact h (iff_of_false hs fun hb ↦ hs (hfill hb))
    have hne : ((Function.update s.1.1 z none, s.1.2), s.2) ∉ BadRQ pk hon S := fun hb ↦ h
      (iff_of_true hs hb)
    obtain ⟨x, y', hxy, hyt⟩ := hs
    by_cases hx : x = z
    · subst hx
      change (s.2.1.1 x).or (s.1.1 x) = some y' at hxy
      rw [hW, hy] at hxy
      cases hxy
      rcases hyt with ht | ht
      · have ht' : tgtDigest pk hon s.2.1.1 s.2.2.2 x = some (pairDigest y) := ht
        rw [tgtDigest, hz, Option.bind_some, slotDigest_enc] at ht'
        change (s.2.2.2 K).bind _ = _ at ht'
        rw [hsel, Option.bind_some] at ht'
        by_cases hc : sel.1 = x
        · rw [ite_eq_left hc] at ht'
          cases ht'
        · rw [ite_eq_right hc] at ht'
          exact ⟨y, sel, hy, hsel, hc, (Option.some.inj ht').symm⟩
      · exact absurd ht.1 (hmsgCall_ne_zero_of_enc hz)
    · refine absurd ⟨x, y', ?_, hyt⟩ hne
      change (s.2.1.1 x).or (Function.update s.1.1 z none x) = some y'
      rw [Function.update_of_ne hx]
      exact hxy
  · refine absurd ?_ hu
    show _ ↔ _
    have hk : trialUpdQ K z s.2.2 (s.1.1 z) = s.2.2 := by
      show (s.2.2.1, cwUpd K z s.2.2.2 (s.1.1 z)) = s.2.2
      rw [cwUpd_of_ne_none hm]
    rw [hy] at hk
    rw [hk]

/-- **The linear charge of a trial read**: `2^-127 (encWt + selWt)` plus `2/|Y × Y|` per unit of
trace. -/
noncomputable def aQ (pk : PublicKey) (c : HwRead PairOut Qrom.HashDomain QMem)
    (σ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ) : ℝ≥0∞ :=
  (2 ^ 127 : ℝ≥0∞)⁻¹ * (trialW pk (encWt pk) c σ + trialW pk selWt c σ) +
    ENNReal.ofReal (2 / Fintype.card PairOut * σ.trace.re)

/-- **The recorded flip mass of a trial read**: `recUWt + recSWt`. -/
noncomputable def pQ (pk : PublicKey) (c : HwRead PairOut Qrom.HashDomain QMem)
    (σ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ) : ℝ≥0∞ :=
  trialW pk recUWt c σ + trialW pk recSWt c σ

theorem two_inv_two_pow_128 : (2 : ℝ) * (2 ^ 128)⁻¹ = (2 ^ 127)⁻¹ := by
  norm_num

/-- **A trial read, linearized**: on an input with the read cell not hardwired, for every
`s > 0`, the refined cost is at most `(1 + s) aQ + (1 + 1/s) pQ`. -/
theorem readCost_trialRead_le {z : Qrom.HashDomain} {K : Key}
    (hz : slotOf pk z = some (.enc K.1 K.2.1 K.2.2))
    {σ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ} (hσ : σ.PosSemidef)
    (hW : ∀ q, σ q q ≠ 0 → q.2.2.1.1 z = none) {s : ℝ} (hs : 0 < s) :
    readCost (BadRQ pk hon S) (trialRead z K) σ ≤
      ENNReal.ofReal (1 + s) * aQ pk (trialRead z K) σ +
        ENNReal.ofReal (1 + s⁻¹) * pQ pk (trialRead z K) σ := by
  classical
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have htr : σ.trace.re = ∑ q, (σ q q).re := by rw [Matrix.trace, Complex.re_sum]; rfl
  have hN : (0 : ℝ) < Fintype.card PairOut := Nat.cast_pos.mpr Fintype.card_pos
  rw [trialRead_eq]
  refine (readCost_readH_le_lin (BadRQ pk hon S) z (trialUpdQ K z) hσ hs).trans
    (add_le_add (mul_le_mul_of_nonneg_left ?_ zero_le) (mul_le_mul_of_nonneg_left ?_ zero_le))
  · -- The linear part.
    set E : ℝ := ∑ q, encWt pk z K q.2 * (σ q q).re
    set Sl : ℝ := ∑ q, selWt z K q.2 * (σ q q).re
    have hE0 : 0 ≤ E := Finset.sum_nonneg fun q _ ↦ mul_nonneg (by
      unfold encWt; split_ifs <;> positivity) (hre q)
    have hS0 : 0 ≤ Sl := Finset.sum_nonneg fun q _ ↦ mul_nonneg (by
      unfold selWt; split_ifs <;> positivity) (hre q)
    have hkey : readHA (BadRQ pk hon S) z (trialUpdQ K z) σ ≤
        (2 ^ 127 : ℝ)⁻¹ * (E + Sl) + 2 / Fintype.card PairOut * σ.trace.re := by
      rw [htr, ← two_inv_two_pow_128, Finset.mul_sum, mul_add, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      unfold readHA
      refine Finset.sum_le_sum fun q _ ↦ ?_
      by_cases h0 : σ q q = 0
      · simp only [h0, Complex.zero_re, mul_zero, add_zero, le_refl]
      have hWq := hW q h0
      rw [ite_eq_left hWq]
      have hc : (2 : ℝ) * (2 ^ 128)⁻¹ * (encWt pk z K q.2 * (σ q q).re) +
          2 * (2 ^ 128)⁻¹ * (selWt z K q.2 * (σ q q).re) +
            2 / Fintype.card PairOut * (σ q q).re =
          (2 * (2 ^ 128)⁻¹ * (encWt pk z K q.2 + selWt z K q.2) +
            2 / Fintype.card PairOut) * (σ q q).re := by ring
      rw [hc]
      refine mul_le_mul_of_nonneg_right ?_ (hre q)
      have hes : 0 ≤ encWt pk z K q.2 + selWt z K q.2 := by
        unfold encWt selWt; split_ifs <;> positivity
      by_cases hD : q.2.1.1 z = none
      · rw [ite_eq_left hD]
        have hf := card_hFlip_trialRead_le (hon := hon) (S := S) hz q hWq hD
        have hf' : ((Finset.univ.filter (hFlip (BadRQ pk hon S) z (trialUpdQ K z) q)).card :
            ℝ) / Fintype.card PairOut ≤ (2 ^ 128)⁻¹ * (encWt pk z K q.2 + selWt z K q.2) := by
          have hk : ((if q.2.2.2.2 K = none then encCwCount pk (unionH q.2) K else 1 : ℕ) : ℝ) ≤
              encWt pk z K q.2 + selWt z K q.2 := by
            unfold encWt selWt
            by_cases hm : q.2.2.2.2 K = none
            · rw [ite_eq_left hm, ite_eq_left ⟨hD, hm⟩, ite_eq_right fun h ↦ h.2 hm, add_zero]
            · rw [ite_eq_right hm, ite_eq_right fun h ↦ hm h.2, ite_eq_left ⟨hD, hm⟩, zero_add,
                Nat.cast_one]
          calc ((Finset.univ.filter (hFlip (BadRQ pk hon S) z (trialUpdQ K z) q)).card : ℝ) /
                Fintype.card PairOut ≤
                (((if q.2.2.2.2 K = none then encCwCount pk (unionH q.2) K else 1) *
                  (2 ^ 128 * 2 ^ 256) : ℕ) : ℝ) / Fintype.card PairOut :=
                div_le_div_of_nonneg_right (Nat.cast_le.mpr hf) hN.le
            _ = ((if q.2.2.2.2 K = none then encCwCount pk (unionH q.2) K else 1 : ℕ) : ℝ) *
                (2 ^ 128)⁻¹ := by
                rw [Nat.cast_mul, mul_div_assoc, pairFiber_div_card_real]
            _ ≤ (2 ^ 128)⁻¹ * (encWt pk z K q.2 + selWt z K q.2) := by
                rw [mul_comm]
                exact mul_le_mul_of_nonneg_left hk (by positivity)
        rw [add_div, mul_div_assoc]
        linarith
      · rw [ite_eq_right hD]
        have : 0 ≤ 2 * (2 ^ 128 : ℝ)⁻¹ * (encWt pk z K q.2 + selWt z K q.2) :=
          mul_nonneg (by positivity) hes
        linarith
    refine (ENNReal.ofReal_le_ofReal hkey).trans ?_
    unfold aQ
    rw [← trialRead_eq, trialW_trialRead _ hz, trialW_trialRead _ hz,
      ENNReal.ofReal_add (mul_nonneg (by positivity) (add_nonneg hE0 hS0))
        (mul_nonneg (by positivity) (Complex.nonneg_iff.1 hσ.trace_nonneg).1),
      ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_add hE0 hS0, ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  · -- The recorded part.
    have hU0 : 0 ≤ ∑ q, recUWt z K q.2 * (σ q q).re := Finset.sum_nonneg fun q _ ↦
      mul_nonneg (by unfold recUWt; split_ifs <;> norm_num) (hre q)
    have hS0 : 0 ≤ ∑ q, recSWt z K q.2 * (σ q q).re := Finset.sum_nonneg fun q _ ↦
      mul_nonneg (by unfold recSWt; split_ifs <;> norm_num) (hre q)
    rw [← trialRead_eq, pQ, trialW_trialRead _ hz, trialW_trialRead _ hz,
      ← ENNReal.ofReal_add hU0 hS0]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold readHP
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ (hre q)
    by_cases hp : q.2.2.1.1 z = none ∧ RecFlip (BadRQ pk hon S) z (trialUpdQ K z) q
    · rw [ite_eq_left hp]
      rcases recFlip_trialRead hz hp.1 hp.2 with h | h
      · have : recUWt z K q.2 = 1 := ite_eq_left h
        have : 0 ≤ recSWt z K q.2 := by unfold recSWt; split_ifs <;> norm_num
        linarith
      · have : recSWt z K q.2 = 1 := ite_eq_left h
        have : 0 ≤ recUWt z K q.2 := by unfold recUWt; split_ifs <;> norm_num
        linarith
    · rw [ite_eq_right hp]
      unfold recUWt recSWt
      split_ifs <;> norm_num

/-! ## Programs of exempt cells -/

/-- **A program of an exempt cell costs nothing.** -/
theorem flipCost_programH_badRQ_eq_zero {z : Qrom.HashDomain} (hz : ExemptCell pk hon z)
    (a : PairOut) {σ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ} (hσ : σ.PosSemidef) :
    flipCost (BadRQ pk hon S) (hwProgKraus (.programH z a)) 0 σ = 0 :=
  flipCost_programH_cellTargetBad_eq_zero z a hσ fun q _ _ ↦
    programH_badQ_conds (S := S) (W := q.2.2.1) (m := q.2.2.2.2) hz a

/-! ## The prefix -/

/-- The trace weight of the read and program ports. -/
noncomputable def trW : ∀ i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port,
    Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD)
      ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD) ℂ → ℝ≥0∞ :=
  extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re)

/-- **The trace-weighted classical calls**: with at most `K` classical calls on every path, the
traces of the inputs of the read and program calls of a program from `initQ` add up to at most
`K`. -/
theorem totalWeight_trW_le {Ω : QReg → Type}
    (x : QuantumComp LocalSig.instruments.{0} (recHwSpec PairOut Qrom.HashDomain TPos SelMem) Ω
      (QReg.of Unit)) {K : ℕ}
    (hK : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1
        else 0) K) :
    (runtimeR m0Q).totalWeight .instruments trW x initQ ≤ K := by
  refine (totalWeight_le_totalWeight (runtimeR m0Q) .instruments
    (w' := fun i σ ↦ ((if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1
      else 0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) (fun i σ _ ↦ ?_) x initQ_posSemidef).trans ?_
  · rcases i with ((p | c) | c) | T <;> simp [trW, extWeight, sumWeight, hwCost, extCls, hwCls]
    all_goals exact le_of_eq rfl
  · refine (totalWeight_chargeTrace_le (runtimeR m0Q) .instruments _ x hK initQ_posSemidef).trans ?_
    calc (K : ℝ≥0∞) * ENNReal.ofReal initQ.trace.re ≤ K * 1 := by
          gcongr
          exact ofReal_trace_initQ_le_one
      _ = K := mul_one _

variable (pk hon S) in
/-- **The prefix's classical costs**: on prefix calls satisfying `PreInvQ`, with at most `K`
classical calls, `twPQ ≤ (√(2^-127 (encPre + selPre) + (2/|Y × Y|) K) + √(recUPre + recSPre))²`,
the weights at the public key `pk`. -/
theorem twPQ_le_pk (pol : DigestPolicy) (A : SAdversary) (θ : TVals)
    (hinv : PrefixInvQ pk hon pol A θ) {K : ℕ}
    (hK : IFreeM.IsChargeBound (prefixQ pol A θ)
      (portCharge fun i ↦ if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1
        else 0) K) :
    twPQ pk hon S pol A θ ≤ (((2 ^ 127 : ℝ≥0∞)⁻¹ *
      (preTot pol A θ (trialW pk (encWt pk)) + preTot pol A θ (trialW pk selWt)) +
      ENNReal.ofReal (2 / Fintype.card PairOut) * K) ^ (2⁻¹ : ℝ) +
        (preTot pol A θ (trialW pk recUWt) + preTot pol A θ (trialW pk recSWt)) ^ (2⁻¹ : ℝ)) ^
          2 := by
  obtain ⟨P, hP, hx⟩ := hinv
  set wa : ∀ i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port,
      Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD)
        ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD) ℂ → ℝ≥0∞ :=
    extWeight (hwCost (aQ pk) fun _ _ ↦ 0)
  set wp : ∀ i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port,
      Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD)
        ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD) ℂ → ℝ≥0∞ :=
    extWeight (hwCost (pQ pk) fun _ _ ↦ 0)
  -- The linear charge along the prefix.
  have ha : (runtimeR m0Q).totalWeight .instruments wa (prefixQ pol A θ) initQ ≤
      (2 ^ 127 : ℝ≥0∞)⁻¹ *
        (preTot pol A θ (trialW pk (encWt pk)) + preTot pol A θ (trialW pk selWt)) +
        ENNReal.ofReal (2 / Fintype.card PairOut) * K := by
    refine (totalWeight_le_lin (runtimeR m0Q) .instruments wa
      (extWeight (hwCost (trialW pk (encWt pk)) fun _ _ ↦ 0))
      (extWeight (hwCost (trialW pk selWt) fun _ _ ↦ 0))
      (fun i σ ↦ ENNReal.ofReal (2 / Fintype.card PairOut) * trW i σ)
      (2 ^ 127 : ℝ≥0∞)⁻¹ (2 ^ 127 : ℝ≥0∞)⁻¹ (fun i σ _ ↦ ?_) (prefixQ pol A θ)
      initQ_posSemidef).trans ?_
    · rcases i with ((p | c) | c) | T
      · exact zero_le
      · show aQ pk c σ ≤ (2 ^ 127 : ℝ≥0∞)⁻¹ * trialW pk (encWt pk) c σ +
          (2 ^ 127 : ℝ≥0∞)⁻¹ * trialW pk selWt c σ +
            ENNReal.ofReal (2 / Fintype.card PairOut) * ENNReal.ofReal σ.trace.re
        unfold aQ
        rw [mul_add, ← ENNReal.ofReal_mul (by positivity)]
        exact le_rfl
      · exact zero_le
      · exact zero_le
    · rw [← mul_add]
      refine add_le_add le_rfl ((le_of_eq (totalWeight_const_mul_weight (runtimeR m0Q)
        .instruments (ENNReal.ofReal (2 / Fintype.card PairOut)) trW (prefixQ pol A θ)
          initQ)).trans ?_)
      exact mul_le_mul_of_nonneg_left (totalWeight_trW_le _ hK) zero_le
  -- The recorded flip mass along the prefix.
  have hp : (runtimeR m0Q).totalWeight .instruments wp (prefixQ pol A θ) initQ ≤
      preTot pol A θ (trialW pk recUWt) + preTot pol A θ (trialW pk recSWt) := by
    refine (totalWeight_le_add (runtimeR m0Q) .instruments wp
      (extWeight (hwCost (trialW pk recUWt) fun _ _ ↦ 0))
      (extWeight (hwCost (trialW pk recSWt) fun _ _ ↦ 0)) 1 1 (fun i σ _ ↦ ?_)
      (prefixQ pol A θ) initQ_posSemidef).trans_eq ?_
    · rcases i with ((p | c) | c) | T
      · exact zero_le
      · show pQ pk c σ ≤ 1 * trialW pk recUWt c σ + 1 * trialW pk recSWt c σ
        rw [one_mul, one_mul]
        rfl
      · exact zero_le
      · exact zero_le
    · rw [one_mul, one_mul]
      rfl
  refine (le_sq_add_of_forall_lin (c := 0) fun s hs ↦ ?_).trans_eq (add_zero _)
  rw [add_zero]
  refine (totalWeight_le_of_forallQueries (runtimeR m0Q) .instruments (PreInvQ pk hon) hP
    (w' := fun i σ ↦ ENNReal.ofReal (1 + s) * wa i σ + ENNReal.ofReal (1 + s⁻¹) * wp i σ)
    (fun i σ hσ hI ↦ ?_) (prefixQ pol A θ) initQ_posSemidef hx).trans ?_
  · rcases i with ((p | c) | c) | T
    · exact zero_le
    · obtain ⟨⟨z, K, hz, rfl⟩, hMF, hnb⟩ := hI
      show readCostT (BadRQ pk hon S) (trialRead z K) σ ≤
        ENNReal.ofReal (1 + s) * aQ pk (trialRead z K) σ +
          ENNReal.ofReal (1 + s⁻¹) * pQ pk (trialRead z K) σ
      have hnb' : ReadNoBot (trialRead z K) σ := readNoBot_of_noBot _ hnb
      unfold readCostT
      rw [ite_eq_left hnb']
      refine readCost_trialRead_le hz hσ (fun q hq ↦ ?_) hs
      have hq' := (hMF q q hq).1
      by_contra hw
      exact hq' z (Option.ne_none_iff_isSome.mp hw) K hz
    · obtain ⟨⟨z, a, rfl, hz⟩, -, -⟩ := hI
      show flipCost (BadRQ pk hon S) (hwProgKraus (.programH z a)) 0 σ ≤
        ENNReal.ofReal (1 + s) * 0 + ENNReal.ofReal (1 + s⁻¹) * 0
      rw [flipCost_programH_badRQ_eq_zero hz a hσ]
      exact zero_le
    · exact zero_le
  · refine (totalWeight_le_add (runtimeR m0Q) .instruments _ wa wp (ENNReal.ofReal (1 + s))
      (ENNReal.ofReal (1 + s⁻¹)) (fun _ _ _ ↦ le_rfl) (prefixQ pol A θ)
      initQ_posSemidef).trans ?_
    exact add_le_add (mul_le_mul_of_nonneg_left ha zero_le) (mul_le_mul_of_nonneg_left hp zero_le)

variable (hon S) in
/-- **The prefix's classical costs at the canonical public key**:
`twPQ ≤ (√(2^-127 (encPre + selPre) + (2/|Y × Y|) K) + √(recUPre + recSPre))²`. -/
theorem twPQ_le (pol : DigestPolicy) (A : SAdversary) (θ : TVals)
    (hinv : PrefixInvQ (pkQ θ) hon pol A θ) {K : ℕ}
    (hK : IFreeM.IsChargeBound (prefixQ pol A θ)
      (portCharge fun i ↦ if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1
        else 0) K) :
    twPQ (pkQ θ) hon S pol A θ ≤ (((2 ^ 127 : ℝ≥0∞)⁻¹ * (encPre pol A θ + selPre pol A θ) +
      ENNReal.ofReal (2 / Fintype.card PairOut) * K) ^ (2⁻¹ : ℝ) +
        (recUPre pol A θ + recSPre pol A θ) ^ (2⁻¹ : ℝ)) ^ 2 :=
  twPQ_le_pk (pkQ θ) hon S pol A θ hinv hK

end Quantum.Qrom.Sphincs

end
