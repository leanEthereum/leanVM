module

public import Quantum.Xmss.Hybrid.GradedMasked
public import Quantum.Sponge.Oracle.Hardwired.ReadCost

@[expose] public section

/-!
# The randomizer trials' hidden reads

GradedMasked's `uavg_mask_readMass_le_xmssR0` leaves the hidden mass of the challenge prefix's
reads (the randomizer trials) as the hypothesis `htrial`.

* **Good public data only** (`uavg_mask_readMass_le_split_good`,
  `uavg_mask_readMass_le_xmssR0_good`): the masked read-mass bound with `htrial` asked only on a
  good set `TG` of public data and hidden values that the good tables reach.
* **Moded programs** (`ModedE`, `totalWeight_le_moded`): a program whose calls follow a mode
  machine (`ok`, `nx`), with a potential per mode, moves the weight of a call onto an earlier call.
* **The trial modes** (`TMode`, `TrialBlock`, `rdOk`, `rdNx`, `tFree_prefixT`,
  `modedE_realizeT`): every read of the challenge prefix is a trial's `k`-read at a trial block
  keeping the memory, followed by the `k'`-read at `π (x, a)` and the `h`-read at `π (x, a).2 + c`.
* **Moving the trials' hidden mass** (`kpot`, `trialW`, `trial_step`,
  `totalWeight_prefixT_le_trialW`): when no trial block is a hidden `k`-cell, the prefix's hidden
  read mass is at most the trial charge `trialW`, which charges each `k`-read the hidden weights of
  its `k'`- and `h`-reads through all outcomes.
* **One cell read with outcome-dependent weights** (`gramQ_apply`, `gramQ_off`, `cellV_some`,
  `re_trace_gramQ_le`): on a state with no decompressed `⊥` at the cell, the weights after the read
  are at most `2 q(y)` on a recorded value `y` and `2/N · Σ_y q(y)` on an empty cell (`cB`).
-/

open IPFunctor Matrix MeasureTheory
open scoped ENNReal ComplexOrder Kronecker

universe u v w w'

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid

/-! ## The masked read mass with the trial term on good data -/

section good

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

variable {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M)

/-- **`uavg_mask_readMass_le_split` with the trial term on good data**: the challenge prefix's
hidden read mass is asked only on the public data and hidden values of `TG`, which the good tables
reach (`hTG`). -/
theorem uavg_mask_readMass_le_split_good (A : Adversary (X × Z)) (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) {∅} ρ)
    (Hh : HonestTable → Set Z) (Hk Hk' : HonestTable → Set X)
    {E P K : Type} [Fintype E] [Fintype P] [Fintype K]
    (e : HonestTable × E → P × ((HPos → Digest) × K)) (G : HonestTable × E → Prop)
    [DecidablePred G] (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card P * Fintype.card ((HPos → Digest) × K) ≤
      Fintype.card (HonestTable × E))
    (pubP : P → Pub) (B : P → K → Finset HPos)
    (hgame : ∀ t, G t → ∃ v : HPos → Digest,
      Agree (Finset.univ \ B (e t).1 (e t).2.2) v (e t).2.1 ∧
      realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A) = realizeT v (gameT M upd (pubP (e t).1) A))
    (Hhk : P → K → Set Z) (Hkk Hk'k : P → K → Set X)
    (hsub : ∀ t, G t →
      Hh t.1 ⊆ hidH (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)) ∪ Hhk (e t).1 (e t).2.2 ∧
      Hk t.1 ⊆ hidK (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)) ∪ Hkk (e t).1 (e t).2.2 ∧
      Hk' t.1 ⊆ hidK' (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)) ∪ Hk'k (e t).1 (e t).2.2)
    (εK : ℝ≥0∞)
    (hcH : ∀ p z, ∑ k, (Hhk p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤ εK * Fintype.card K)
    (hcK : ∀ p y, ∑ k, (Hkk p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤ εK * Fintype.card K)
    (hcK' : ∀ p y, ∑ k, (Hk'k p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤ εK * Fintype.card K)
    (J : Finset HPos) (hBJ : ∀ p k, B p k ⊆ J) (εB : ℝ≥0∞)
    (hεB : ∀ p, ∀ s ∈ J,
      ((Finset.univ.filter fun k ↦ s ∈ B p k).card : ℝ≥0∞) ≤ εB * Fintype.card K)
    {R : ℕ} (hR : ∀ (pub : Pub) (v : HPos → Digest),
      IFreeM.IsChargeBound (realizeT v (gameT M upd pub A)) (portCharge (candCharge X Z M J)) R)
    {N : ℕ} (hN : ∀ (pub : Pub) (v : HPos → Digest),
      IFreeM.IsChargeBound (realizeT v (gameT M upd pub A))
        (portCharge fun i ↦ if readRecPort M i = true then 1 else 0) N)
    (TG : P → (HPos → Digest) → Prop) [∀ p, DecidablePred (TG p)]
    (hTG : ∀ t, G t → TG (e t).1 (e t).2.1)
    (τ : ℝ≥0∞)
    (htrial : ∀ p, ∑ v : HPos → Digest, (if TG p v then (runtimeR m₀).totalWeight
      LocalSig.Interp.instruments
      (portMass (fun i ↦ readRecPort M i = true) (hidH (pubP p) fun q ↦ v (.inl q))
        (hidK (pubP p) fun q ↦ v (.inl q)) (hidK' (pubP p) fun q ↦ v (.inl q)))
      (realizeT v (prefixT M upd (pubP p) A)) ρ else 0) ≤ τ * Fintype.card (HPos → Digest)) :
    uavg (fun t : HonestTable × E ↦ if G t then (runtimeR m₀).totalWeight
      LocalSig.Interp.instruments (readMass (Hh t.1) (Hk t.1) (Hk' t.1))
        (realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A)) ρ else 0) ≤
      τ + (2 ^ 128 : ℝ≥0∞)⁻¹ * ((3 * verifyBlocks : ℕ) : ℝ≥0∞) + N * (εK + R * εB) := by
  simp only [readMass_eq_portMass]
  refine uavg_mask_le_of_injOn e G hinj hcard _
    (fun p w ↦ (if TG p w.1 then (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (portMass (fun i ↦ readRecPort M i = true) (hidH (pubP p) fun q ↦ w.1 (.inl q))
          (hidK (pubP p) fun q ↦ w.1 (.inl q)) (hidK' (pubP p) fun q ↦ w.1 (.inl q)))
        (realizeT w.1 (prefixT M upd (pubP p) A)) ρ else 0) +
      ∑' a, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (portMass (fun i ↦ readRecPort M i = true) (hidH (pubP p) fun q ↦ w.1 (.inl q))
          (hidK (pubP p) fun q ↦ w.1 (.inl q)) (hidK' (pubP p) fun q ↦ w.1 (.inl q)))
        (realizeT w.1 (verifyT M (pubP p) a))
        (((runtimeR m₀).run₂ LocalSig.Interp.instruments
          (realizeT w.1 (prefixT M upd (pubP p) A))).branch a ρ) +
      (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (portMass (fun i ↦ readRecPort M i = true) (Hhk p w.2) (Hkk p w.2) (Hk'k p w.2))
        (realizeT w.1 (gameT M upd (pubP p) A)) ρ +
      N * revW m₀ LocalSig.Interp.instruments (B p w.2) (realizeT w.1 (gameT M upd (pubP p) A)) ρ)
    (fun t ht ↦ ?_) _ fun p ↦ ?_
  · obtain ⟨v, hv, hgeq⟩ := hgame t ht
    obtain ⟨h1, h2, h3⟩ := hsub t ht
    dsimp only
    rw [hgeq]
    simp only [hTG t ht, ↓reduceIte]
    refine (totalWeight_portMass_le_mismatch m₀ LocalSig.Interp.instruments
      (gameT M upd (pubP (e t).1) A) (disc_gameT M upd _ A ∅) (keepsLab_gameT upd _ A) ρ hρ hs
      (B (e t).1 (e t).2.2) (Finset.disjoint_empty_left _) _ (Hh t.1) (Hk t.1) (Hk' t.1) hv
      (hN _ v)).trans (add_le_add ?_ le_rfl)
    exact (totalWeight_portMass_mono _ _ m₀ h1 h2 h3 _ hρ).trans
      ((totalWeight_portMass_union_le _ _ m₀ _ _ _ _ _ _ _ hρ).trans (add_le_add
        (le_of_eq (totalWeight_portMass_gameT_split upd _ m₀ _ A _ _ _ _ ρ hρ)) le_rfl))
  · have hver := sum_verifyMass_le upd (pubP p) A m₀ ρ hρ hρ1 hs
    rw [card_digest_inv] at hver
    have hK : ∀ v : HPos → Digest, ∑ k, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (portMass (fun i ↦ readRecPort M i = true) (Hhk p k) (Hkk p k) (Hk'k p k))
        (realizeT v (gameT M upd (pubP p) A)) ρ ≤ εK * N * Fintype.card K := fun v ↦
      (sum_totalWeight_portMass_le_count LocalSig.Interp.instruments _ m₀ _ hρ (Hhk p) (Hkk p)
        (Hk'k p) εK (hcH p) (hcK p) (hcK' p) (hN _ v)).trans
        (by calc (εK * Fintype.card K) * (N * ENNReal.ofReal ρ.trace.re)
              ≤ (εK * Fintype.card K) * (N * 1) := by gcongr
            _ = εK * N * Fintype.card K := by ring)
    have hrev : ∀ v : HPos → Digest, ∑ k, revW m₀ LocalSig.Interp.instruments (B p k)
        (realizeT v (gameT M upd (pubP p) A)) ρ ≤ R * εB * Fintype.card K := fun v ↦
      (sum_revW_le m₀ LocalSig.Interp.instruments _ hρ (B p) J (hBJ p) εB (hεB p) (hR _ v)).trans
        (by calc (Fintype.card K : ℝ≥0∞) * (R * εB * ENNReal.ofReal ρ.trace.re)
              ≤ Fintype.card K * (R * εB * 1) := by gcongr
            _ = R * εB * Fintype.card K := by ring)
    set pre : (HPos → Digest) → ℝ≥0∞ := fun v ↦ if TG p v then (runtimeR m₀).totalWeight
      LocalSig.Interp.instruments
      (portMass (fun i ↦ readRecPort M i = true) (hidH (pubP p) fun q ↦ v (.inl q))
        (hidK (pubP p) fun q ↦ v (.inl q)) (hidK' (pubP p) fun q ↦ v (.inl q)))
      (realizeT v (prefixT M upd (pubP p) A)) ρ else 0 with hpre
    set ver : (HPos → Digest) → ℝ≥0∞ := fun v ↦ ∑' a, (runtimeR m₀).totalWeight
      LocalSig.Interp.instruments
      (portMass (fun i ↦ readRecPort M i = true) (hidH (pubP p) fun q ↦ v (.inl q))
        (hidK (pubP p) fun q ↦ v (.inl q)) (hidK' (pubP p) fun q ↦ v (.inl q)))
      (realizeT v (verifyT M (pubP p) a))
      (((runtimeR m₀).run₂ LocalSig.Interp.instruments
        (realizeT v (prefixT M upd (pubP p) A))).branch a ρ) with hver'
    rw [Fintype.sum_prod_type]
    calc ∑ v : HPos → Digest, ∑ k : K,
          (pre (v, k).1 + ver (v, k).1 +
          (runtimeR m₀).totalWeight LocalSig.Interp.instruments
            (portMass (fun i ↦ readRecPort M i = true) (Hhk p (v, k).2) (Hkk p (v, k).2)
              (Hk'k p (v, k).2))
            (realizeT (v, k).1 (gameT M upd (pubP p) A)) ρ +
          N * revW m₀ LocalSig.Interp.instruments (B p (v, k).2)
            (realizeT (v, k).1 (gameT M upd (pubP p) A)) ρ)
        ≤ ∑ v : HPos → Digest, (Fintype.card K * (pre v + ver v) +
          (εK * N * Fintype.card K + N * (R * εB * Fintype.card K))) := by
          refine Finset.sum_le_sum fun v _ ↦ ?_
          dsimp only
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul, add_assoc]
          exact add_le_add le_rfl (add_le_add (hK v) (mul_le_mul_of_nonneg_left (hrev v) zero_le))
      _ = Fintype.card K * (∑ v : HPos → Digest, pre v + ∑ v : HPos → Digest, ver v) +
          Fintype.card (HPos → Digest) * (εK * N * Fintype.card K + N * (R * εB * Fintype.card K))
          := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul]
      _ ≤ Fintype.card K * (τ * Fintype.card (HPos → Digest) +
            (2 ^ 128 : ℝ≥0∞)⁻¹ * (((3 * verifyBlocks : ℕ) : ℝ≥0∞) * Fintype.card (HPos → Digest))) +
          Fintype.card (HPos → Digest) * (εK * N * Fintype.card K + N * (R * εB * Fintype.card K))
          := add_le_add (mul_le_mul_of_nonneg_left (add_le_add (htrial p) hver) zero_le) le_rfl
      _ = (τ + (2 ^ 128 : ℝ≥0∞)⁻¹ * ((3 * verifyBlocks : ℕ) : ℝ≥0∞) + N * (εK + R * εB)) *
          Fintype.card ((HPos → Digest) × K) := by
          rw [Fintype.card_prod, Nat.cast_mul (Fintype.card (HPos → Digest)) (Fintype.card K)]
          ring

/-- **`uavg_mask_readMass_le_xmssR0` with the trial term on good data**: as GradedMasked's bound,
the randomizer trials' hidden read mass `τ` asked only on the public data and hidden values of
`TG`, which the good tables reach. -/
theorem uavg_mask_readMass_le_xmssR0_good (A : Adversary (X × Z)) {q : ℕ}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
    (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) {∅} ρ)
    {E P W : Type} [Fintype E] [Fintype P] [Fintype W]
    (e : HonestTable × E → P × ((HPos → Digest) × (RK × W))) (G : HonestTable × E → Prop)
    [DecidablePred G] (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card P * Fintype.card ((HPos → Digest) × (RK × W)) ≤
      Fintype.card (HonestTable × E))
    (pubP : P → Pub) (parP : P → PublicParameter) (permP : P → Equiv.Perm (X × Z)) (Gπ : ℕ)
    (hgame : ∀ t, G t → ∃ v : HPos → Digest,
      Agree (Finset.univ \ r0Bk (permP (e t).1) (parP (e t).1) (e t).2.2.1) v (e t).2.1 ∧
      realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A) = realizeT v (gameT M upd (pubP (e t).1) A))
    (hpath : ∀ t, G t →
      pathH t.1 ⊆ hidH (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)) ∧
      pathK t.1 ⊆ hidK (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)) ∧
      pathK' t.1 ⊆ hidK' (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)))
    (hr0 : ∀ t, G t →
      r0H t.1 ⊆ r0Hk (permP (e t).1) (parP (e t).1) (e t).2.2.1 ∧
      r0K t.1 ⊆ r0Kk (parP (e t).1) (e t).2.2.1 ∧
      r0K' t.1 ⊆ r0K'k Gπ (permP (e t).1) (parP (e t).1) (e t).2.2.1 ∧
      seedK t.1 ⊆ seedKk (parP (e t).1) (e t).2.2.1)
    (seedHk : P → RK × W → Set Z) (seedK'k : P → RK × W → Set X) (εA : ℝ≥0∞)
    (hseed : ∀ t, G t → seedH t.1 ⊆ seedHk (e t).1 (e t).2.2 ∧
      seedK' t.1 ⊆ seedK'k (e t).1 (e t).2.2)
    (hA : ∀ p z, ∑ k, (seedHk p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤
      εA * Fintype.card (RK × W))
    (hA' : ∀ p y, ∑ k, (seedK'k p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤
      εA * Fintype.card (RK × W))
    (TG : P → (HPos → Digest) → Prop) [∀ p, DecidablePred (TG p)]
    (hTG : ∀ t, G t → TG (e t).1 (e t).2.1)
    (τ : ℝ≥0∞)
    (htrial : ∀ p, ∑ v : HPos → Digest, (if TG p v then (runtimeR m₀).totalWeight
      LocalSig.Interp.instruments
      (portMass (fun i ↦ readRecPort M i = true) (hidH (pubP p) fun q ↦ v (.inl q))
        (hidK (pubP p) fun q ↦ v (.inl q)) (hidK' (pubP p) fun q ↦ v (.inl q)))
      (realizeT v (prefixT M upd (pubP p) A)) ρ else 0) ≤ τ * Fintype.card (HPos → Digest)) :
    uavg (fun t : HonestTable × E ↦ if G t then (runtimeR m₀).totalWeight
      LocalSig.Interp.instruments
      (readMass (pathH t.1 ∪ seedH t.1 ∪ r0H t.1) (pathK t.1 ∪ seedK t.1 ∪ r0K t.1)
        (pathK' t.1 ∪ seedK' t.1 ∪ r0K' t.1))
      (realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A)) ρ else 0) ≤
      τ + (2 ^ 128 : ℝ≥0∞)⁻¹ * ((3 * verifyBlocks : ℕ) : ℝ≥0∞) +
        ((3 * (signBlocks * lifetime + verifyBlocks) + 2 * progCap : ℕ) : ℝ≥0∞) *
          ((εA + r0Eps Gπ) +
            ((2 * lifetime : ℕ) : ℝ≥0∞) * ((Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z)) := by
  have e1 : (Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z ≤ r0Eps Gπ := le_add_self
  have e2 : 2 * (Fintype.card MasterSeed : ℝ≥0∞)⁻¹ ≤ εA + r0Eps Gπ :=
    (le_self_add.trans le_self_add).trans le_add_self
  have e3 : (Fintype.card RLabel : ℝ≥0∞) * Gπ / Fintype.card Z ≤ r0Eps Gπ :=
    le_add_self.trans le_self_add
  exact uavg_mask_readMass_le_split_good upd A m₀ ρ hρ hρ1 hs
    (fun L ↦ pathH L ∪ seedH L ∪ r0H L) (fun L ↦ pathK L ∪ seedK L ∪ r0K L)
    (fun L ↦ pathK' L ∪ seedK' L ∪ r0K' L) e G hinj hcard pubP
    (fun p k ↦ r0Bk (permP p) (parP p) k.1) hgame
    (fun p k ↦ r0Hk (permP p) (parP p) k.1 ∪ seedHk p k)
    (fun p k ↦ r0Kk (parP p) k.1 ∪ seedKk (parP p) k.1)
    (fun p k ↦ r0K'k Gπ (permP p) (parP p) k.1 ∪ seedK'k p k)
    (fun t ht ↦ by
      obtain ⟨p1, p2, p3⟩ := hpath t ht
      obtain ⟨r1, r2, r3, r4⟩ := hr0 t ht
      obtain ⟨s1, s2⟩ := hseed t ht
      refine ⟨?_, ?_, ?_⟩
      · rintro z ((hz | hz) | hz)
        exacts [Or.inl (p1 hz), Or.inr (Or.inr (s1 hz)), Or.inr (Or.inl (r1 hz))]
      · rintro x ((hx | hx) | hx)
        exacts [Or.inl (p2 hx), Or.inr (Or.inr (r4 hx)), Or.inr (Or.inl (r2 hx))]
      · rintro x ((hx | hx) | hx)
        exacts [Or.inl (p3 hx), Or.inr (Or.inr (s2 hx)), Or.inr (Or.inl (r3 hx))])
    (εA + r0Eps Gπ)
    (fun p z ↦ (sum_indicator_union_le _ _ z).trans <| (add_le_add (sum_indicator_pad_le
      (fun k : RK ↦ r0Hk (permP p) (parP p) k) z _ (sum_indicator_r0Hk_le _ _ z)) (hA p z)).trans
      (add_mul_le_add_mul e1 le_rfl))
    (fun p y ↦ (sum_indicator_pad_le (fun k : RK ↦ r0Kk (parP p) k ∪ seedKk (parP p) k) y _
      (sum_indicator_kCells_le _ y)).trans (mul_le_mul_of_nonneg_right e2 zero_le))
    (fun p y ↦ (sum_indicator_union_le _ _ y).trans <| (add_le_add (sum_indicator_pad_le
      (fun k : RK ↦ r0K'k Gπ (permP p) (parP p) k) y _ (sum_indicator_r0K'k_le _ _ _ y))
      (hA' p y)).trans (add_mul_le_add_mul e3 le_rfl))
    rJ (fun p k ↦ r0Bk_subset _ _ _) ((Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z)
    (fun p s _ ↦ le_of_eq_of_le (card_filter_pad (W := W)
      (fun k : RK ↦ s ∈ r0Bk (permP p) (parP p) k))
      ((mul_le_mul_of_nonneg_right (card_filter_r0Bk_le _ _ s) zero_le).trans_eq
        (by rw [mul_assoc, ← Nat.cast_mul, ← Fintype.card_prod])))
    (hR_gameT upd A hperm hsign) (hN_readRec upd A hperm hsign) TG hTG τ htrial

end good

/-! ## Moded programs -/

section moded

variable {spec : QuantumOracleSpec.{0, 0}} {L : LocalSig.{u, v}} {Ω : QReg → Type w}
  {Mode : Type} (ok : Mode → spec.Port → Prop) (nx : Mode → (i : spec.Port) → spec.Result i → Mode)

/-- The condition of a mode on a command: a call must be allowed by the mode. -/
def modeCmdOk {A : QReg} : QuantumComp.Cmd L spec A → Mode → Prop
  | .prim _, _ => True
  | .query i _ _, μ => ok μ i

/-- The mode after a command: a local operation keeps it, a call moves it by its result. -/
def modeCmdNx {A : QReg} : (c : QuantumComp.Cmd L spec A) → Mode → c.Resp → Mode
  | .prim _, μ, _ => μ
  | .query i _ _, μ, b => nx μ i b.down

/-- **A moded program**: from the mode `μ`, every call is allowed by the current mode, which moves
by the call's result; every leaf `a` is reached in the mode `fin a`. -/
def ModedE (fin : (Σ u, Ω u) → Mode) :
    Mode → {A : QReg} → IFreeM (QuantumComp.toIPFunctor L spec) Ω A → Prop
  | μ, _, .pure a => μ = fin ⟨_, a⟩
  | μ, _, .liftBind c next => modeCmdOk ok c μ ∧ ∀ b, ModedE fin (modeCmdNx nx c μ b) (next b)

variable {ok nx}

theorem modedE_bind {Y : QReg → Type w'} {fin : (Σ u, Ω u) → Mode} {fin' : (Σ u, Y u) → Mode}
    {A : QReg} (x : IFreeM (QuantumComp.toIPFunctor L spec) Ω A)
    (g : ∀ u, Ω u → IFreeM (QuantumComp.toIPFunctor L spec) Y u) {μ : Mode}
    (hx : ModedE ok nx fin μ x) (hg : ∀ u a, ModedE ok nx fin' (fin ⟨u, a⟩) (g u a)) :
    ModedE ok nx fin' μ (x.bind g) := by
  induction x using IFreeM.inductionOn generalizing μ with
  | pure _ a =>
    change μ = fin ⟨_, a⟩ at hx
    subst hx
    exact hg _ a
  | liftBind _ c next ih => exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩

theorem modedE₂_bind {A B B' : QReg} {α β : Type} {fin : α → Mode} {fin' : β → Mode}
    (x : QuantumComp₂ L spec A B α) (g : α → QuantumComp₂ L spec B B' β) {μ : Mode}
    (hx : ModedE ok nx (fun p ↦ fin p.2.2) μ x)
    (hg : ∀ a, ModedE ok nx (fun p ↦ fin' p.2.2) (fin a) (g a)) :
    ModedE ok nx (fun p ↦ fin' p.2.2) μ (x.bind g) := by
  refine modedE_bind x _ hx fun u p ↦ ?_
  obtain ⟨e, a⟩ := p
  subst e
  exact hg a

theorem modedE_pure₂ {A : QReg} {α : Type} {fin : α → Mode} (a : α) :
    ModedE ok nx (fun p ↦ fin p.2.2) (fin a)
      (QuantumComp₂.pure (L := L) (spec := spec) (A := A) a) :=
  rfl

theorem modedE_act {A B : QReg} {α : Type} {fin : α → Mode} (p : SubInstrument A B α)
    (μ : Mode) (hμ : ∀ a, fin a = μ) :
    ModedE (L := LocalSig.instruments) ok nx (fun q ↦ fin q.2.2) μ (QComp.act (spec := spec) p) :=
  ⟨trivial, fun b ↦ (hμ b.down).symm⟩

variable (R : QuantumRuntime spec) (I : L.Interp)

/-- **Moving the weight along a moded program.** Let every mode `μ` carry the potentials
`Kp μ j`, and on every positive semidefinite input `σ` of an allowed call let the weight `w` plus
the potentials after the call in the next modes be at most the potentials before plus the charge
`c`. Then the weight of a moded program is at most the initial potential plus the charges. -/
theorem totalWeight_le_moded {Zp J : Type*} [Fintype Zp] [Fintype J]
    (Kp : Mode → J → Matrix Zp R.D ℂ)
    (w c : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (h : ∀ μ i σ, σ.PosSemidef → ok μ i →
      w i σ + ∑' r, ∑ j, potential (Kp (nx μ i r) j) ((R.step i).branch r σ) ≤
        ∑ j, potential (Kp μ j) σ + c i σ)
    {fin : (Σ u, Ω u) → Mode} {A : QReg} (x : QuantumComp L spec Ω A) :
    ∀ μ, ModedE ok nx fin μ x → ∀ {ρ : Matrix (A × R.D) (A × R.D) ℂ}, ρ.PosSemidef →
      R.totalWeight I w x ρ ≤ ∑ j, potential (Kp μ j) ρ + R.totalWeight I c x ρ := by
  classical
  induction x using QuantumComp.inductionOn with
  | pure _ y =>
    intro μ _ ρ _
    rw [totalWeight_pure]
    exact zero_le
  | primBind _ o k ih =>
    intro μ hx ρ hρ
    have hb := fun b ↦ ((I o).frame R.D).posSemidef_branch_apply b hρ
    rw [totalWeight_primBind, totalWeight_primBind]
    calc ∑' b, R.totalWeight I w (k b) (((I o).frame R.D).branch b ρ)
        ≤ ∑' b, (∑ j, potential (Kp μ j) (((I o).frame R.D).branch b ρ) +
            R.totalWeight I c (k b) (((I o).frame R.D).branch b ρ)) :=
          ENNReal.tsum_le_tsum fun b ↦ ih b μ (hx.2 (ULift.up b)) (hb b)
      _ = ∑ j, ∑' b, potential (Kp μ j) (((I o).frame R.D).branch b ρ) +
            ∑' b, R.totalWeight I c (k b) (((I o).frame R.D).branch b ρ) := by
          rw [ENNReal.tsum_add, Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
      _ ≤ _ := by
          gcongr with j
          exact tsum_potential_frame_le (Kp μ j) (I o) hρ
  | queryBind _ i E ℓ k ih =>
    intro μ hx ρ hρ
    have hσ := posSemidef_callInput ℓ hρ
    have hb := fun r ↦ (R.queryStep i E ℓ).posSemidef_branch_apply r hρ
    rw [totalWeight_queryBind, totalWeight_queryBind]
    have hk : ∀ r, R.totalWeight I w (k r) ((R.queryStep i E ℓ).branch r ρ) ≤
        ∑ j, potential (Kp (nx μ i r) j) ((R.step i).branch r (callInput ℓ R.D ρ)) +
          R.totalWeight I c (k r) ((R.queryStep i E ℓ).branch r ρ) := fun r ↦ by
      simp only [← potential_queryStep]
      exact ih r _ (hx.2 (ULift.up r)) (hb r)
    calc w i (callInput ℓ R.D ρ) + ∑' r, R.totalWeight I w (k r) ((R.queryStep i E ℓ).branch r ρ)
        ≤ w i (callInput ℓ R.D ρ) + ∑' r, (∑ j, potential (Kp (nx μ i r) j)
            ((R.step i).branch r (callInput ℓ R.D ρ)) +
            R.totalWeight I c (k r) ((R.queryStep i E ℓ).branch r ρ)) := by
          gcongr with r
          exact hk r
      _ = (w i (callInput ℓ R.D ρ) + ∑' r, ∑ j, potential (Kp (nx μ i r) j)
            ((R.step i).branch r (callInput ℓ R.D ρ))) +
            ∑' r, R.totalWeight I c (k r) ((R.queryStep i E ℓ).branch r ρ) := by
          rw [ENNReal.tsum_add, add_assoc]
      _ ≤ (∑ j, potential (Kp μ j) (callInput ℓ R.D ρ) + c i (callInput ℓ R.D ρ)) +
            ∑' r, R.totalWeight I c (k r) ((R.queryStep i E ℓ).branch r ρ) := by
          exact add_le_add (h μ i _ hσ hx.1) le_rfl
      _ = _ := by
          simp only [potential_callInput]
          rw [add_assoc]

/-- `totalWeight_le_moded` from a mode with no potential. -/
theorem totalWeight_le_moded_of_zero {Zp J : Type*} [Fintype Zp] [Fintype J]
    (Kp : Mode → J → Matrix Zp R.D ℂ)
    (w c : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (h : ∀ μ i σ, σ.PosSemidef → ok μ i →
      w i σ + ∑' r, ∑ j, potential (Kp (nx μ i r) j) ((R.step i).branch r σ) ≤
        ∑ j, potential (Kp μ j) σ + c i σ)
    {fin : (Σ u, Ω u) → Mode} {A : QReg} (x : QuantumComp L spec Ω A) (μ : Mode)
    (hμ : ∀ j, Kp μ j = 0) (hx : ModedE ok nx fin μ x)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    R.totalWeight I w x ρ ≤ R.totalWeight I c x ρ := by
  classical
  refine (totalWeight_le_moded R I Kp w c h x μ hx hρ).trans (le_of_eq ?_)
  have h0 : ∑ j, potential (Kp μ j) ρ = 0 := Finset.sum_eq_zero fun j _ ↦ by
    rw [hμ j, potential_eq, Matrix.mul_zero, Matrix.kronecker_zero, Matrix.zero_mul,
      Matrix.trace_zero, Complex.zero_re, ENNReal.ofReal_zero]
  rw [h0, zero_add]

end moded

/-! ## The modes of the randomizer trials -/

section modes

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

/-- The modes of a randomizer trial's reads: free; after the `k`-read at the block `x` with the
outcome `a` (the `k'`-read at `π (x, a)` is next); after the `k'`-read, with the `h`-cell `z`
next. -/
inductive TMode
  | free
  | afK (x : X) (a : Z)
  | afK' (z : Z)

/-- A one-block message-digest input's block: a randomizer trial's `k`-cell. -/
def TrialBlock (P : PublicParameter) (x : X) : Prop :=
  ∃ (l : Layer) (e : KeyIndex) (msg : HashInput) (ρ : Randomizer), msg.length ≤ 32 ∧
    blocks (thInput P (hashDomainFields (.message l e)) (msg ++ littleEndianBytes 16 ρ)) = [x]

variable (π : Equiv.Perm (X × Z)) (P : PublicParameter)

/-- The reads a mode allows: a free read is a `k`-read at a trial block; after the `k`-read at `x`
with outcome `a` the `k'`-read at `π (x, a)` keeping the memory; then the `h`-read at `z`. -/
def rdOk {M' : Type} : TMode → HwRead X Z M' → Prop
  | .free, .readK x u => TrialBlock P x ∧ u = fun m _ ↦ m
  | .afK x a, .readK' y u => y = (π (x, a)).1 ∧ u = fun m _ ↦ m
  | .afK' z, .readH z' _ => z' = z
  | _, _ => False

/-- The mode after a read. -/
def rdNx {M' : Type} : TMode → (c : HwRead X Z M') → c.Result → TMode
  | .free, .readK x _, r => .afK x (r.1.getD 0)
  | .afK x a, .readK' _ _, r => .afK' ((π (x, a)).2 + r.1.getD 0)
  | _, _, _ => .free

/-- The calls the modes allow, on runtime 1's ports. -/
def okR {M : Type} : TMode → (hwReadSpec X Z M).Port → Prop
  | μ, .inl _ => μ = .free
  | μ, .inr c => rdOk π P μ c

/-- The mode after a call of runtime 1. -/
def nxR {M : Type} : TMode → (i : (hwReadSpec X Z M).Port) → (hwReadSpec X Z M).Result i → TMode
  | _, .inl _, _ => .free
  | μ, .inr c, r => rdNx π μ c r

/-- The calls the modes allow, on the template's ports. -/
def okT {M : Type} : TMode → (XSpec M).Port → Prop
  | μ, .inl (.inl (.inr c)) => rdOk π P μ c.1
  | μ, _ => μ = .free

/-- The mode after a call of the template. -/
def nxT {M : Type} : TMode → (i : (XSpec M).Port) → (XSpec M).Result i → TMode
  | μ, .inl (.inl (.inr c)), r => rdNx π μ c.1 r
  | _, _, _ => .free

/-- The calls the modes allow, on runtime 2's ports with record ports. -/
def okZ {M : Type} : TMode → (recHwSpec X Z HPos M).Port → Prop
  | μ, .inl (.inl (.inr c)) => rdOk π P μ c
  | μ, _ => μ = .free

/-- The mode after a call of runtime 2 with record ports. -/
def nxZ {M : Type} : TMode → (i : (recHwSpec X Z HPos M).Port) →
    (recHwSpec X Z HPos M).Result i → TMode
  | μ, .inl (.inl (.inr c)), r => rdNx π μ c r
  | _, _, _ => .free

variable {M : Type} [Fintype M] [DecidableEq M]

/-! ### Runtime 1's trial reads -/

variable {π P}

omit [Fintype M] [DecidableEq M] in
theorem modedE_readCall {μ : TMode} {c : HwRead X Z M} (h : rdOk π P μ c) (B : QReg) :
    ModedE (L := LocalSig.instruments) (okR π P) (nxR π) (fun p ↦ rdNx π μ c p.2.2) μ
      (readCall c B) :=
  ⟨h, fun _ ↦ ⟨trivial, fun _ ↦ rfl⟩⟩

variable (π P) in
/-- A stateful program of runtime 1 that is moded from every state. -/
def SMod {B : QReg} {σ α : Type} (μ : TMode) (fin : α → TMode)
    (x : StateT σ (QComp (hwReadSpec X Z M) B B) α) : Prop :=
  ∀ s, ModedE (L := LocalSig.instruments) (okR π P) (nxR π) (fun p ↦ fin p.2.2.1) μ (x.run s)

section smod

variable {B : QReg} {σ α β : Type}

omit [Fintype M] [DecidableEq M] in
theorem sMod_bind {x : StateT σ (QComp (hwReadSpec X Z M) B B) α}
    {k : α → StateT σ (QComp (hwReadSpec X Z M) B B) β} {μ : TMode} {f : α → TMode}
    {g : β → TMode} (hx : SMod π P μ f x) (hk : ∀ a, SMod π P (f a) g (k a)) :
    SMod π P μ g (x >>= k) := by
  intro s
  rw [StateT.run_bind]
  exact modedE₂_bind (fin := fun q : α × σ ↦ f q.1) (fin' := fun q : β × σ ↦ g q.1) _ _ (hx s)
    fun p ↦ hk p.1 p.2

omit [Fintype M] [DecidableEq M] in
theorem sMod_pure (a : α) (f : α → TMode) :
    SMod π P (f a) f (pure a : StateT σ (QComp (hwReadSpec X Z M) B B) α) := by
  intro s
  rw [StateT.run_pure]
  rfl

omit [Fintype M] [DecidableEq M] in
theorem modedE_map {spec : QuantumOracleSpec.{0, 0}} {ok : TMode → spec.Port → Prop}
    {nx : TMode → (i : spec.Port) → spec.Result i → TMode} {A B' : QReg} {γ δ : Type}
    {x : QComp spec A B' γ} (g : γ → δ) {f : δ → TMode} {μ : TMode}
    (hx : ModedE (L := LocalSig.instruments) ok nx (fun p ↦ f (g p.2.2)) μ x) :
    ModedE (L := LocalSig.instruments) ok nx (fun p ↦ f p.2.2) μ (x.map g) := by
  rw [QuantumComp₂.map_eq_bind_pure]
  exact modedE₂_bind (fin := fun a ↦ f (g a)) _ _ hx fun _ ↦ rfl

omit [Fintype M] [DecidableEq M] in
theorem sMod_map {x : StateT σ (QComp (hwReadSpec X Z M) B B) α} (g : α → β) {μ : TMode}
    {f : β → TMode} (hx : SMod π P μ (fun a ↦ f (g a)) x) : SMod π P μ f (g <$> x) := by
  intro s
  rw [StateT.run_map]
  exact modedE_map (f := fun q : β × σ ↦ f q.1) (fun p : α × σ ↦ (g p.1, p.2)) (hx s)

omit [Fintype M] [DecidableEq M] in
theorem sMod_rdK {x : X} (hx : TrialBlock P x) :
    SMod π P .free (fun a ↦ .afK x a) (rdK (M := M) B x) :=
  fun s ↦ modedE₂_bind (fin := fun r : Option Z × M ↦ TMode.afK x (r.1.getD 0))
    (fin' := fun q : Z × List (SpongeRead X Z) ↦ TMode.afK x q.1) (readCall (.readK x keepMem) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.k x (r.1.getD 0)]))
    (modedE_readCall (π := π) (μ := .free) (c := .readK x keepMem) ⟨hx, rfl⟩ B) fun _ ↦ rfl

omit [Fintype M] [DecidableEq M] in
theorem sMod_rdK' {x : X} {a : Z} {y : X} (hy : y = (π (x, a)).1) :
    SMod π P (.afK x a) (fun c ↦ .afK' ((π (x, a)).2 + c)) (rdK' (M := M) B y) :=
  fun s ↦ modedE₂_bind (fin := fun r : Option Z × M ↦ TMode.afK' ((π (x, a)).2 + r.1.getD 0))
    (fin' := fun q : Z × List (SpongeRead X Z) ↦ TMode.afK' ((π (x, a)).2 + q.1))
    (readCall (.readK' y keepMem) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.k' y (r.1.getD 0)]))
    (modedE_readCall (π := π) (μ := .afK x a) (c := .readK' y keepMem) ⟨hy, rfl⟩ B) fun _ ↦ rfl

omit [Fintype M] [DecidableEq M] in
theorem sMod_rdHU {z z' : Z} (hz : z' = z) (u : M → Option X → M) :
    SMod π P (.afK' z) (fun _ ↦ .free) (rdHU M B z' u) :=
  fun s ↦ modedE₂_bind (fin := fun _ : Option X × M ↦ TMode.free)
    (fin' := fun _ : X × List (SpongeRead X Z) ↦ TMode.free) (readCall (.readH z' u) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.h z' (r.1.getD 0)]))
    (modedE_readCall (π := π) (μ := .afK' z) (c := .readH z' u) hz B) fun _ ↦ rfl

omit [Fintype M] [DecidableEq M] in
/-- **A trial's round of reads**, from a state with zero capacity and a trial block. -/
theorem sMod_rdRoundU (u : X → X → M → Option X → M) (s : X × Z) (b : X) (hs : s.2 = 0)
    (hb : TrialBlock P (s.1 + b)) :
    SMod π P .free (fun _ ↦ .free) (rdRoundU M u π B s b) := by
  unfold rdRoundU
  refine sMod_bind (sMod_rdK hb) fun a ↦ ?_
  refine sMod_bind (sMod_rdK' (a := a) (by rw [hs, zero_add])) fun c ↦ ?_
  refine sMod_bind (sMod_rdHU (by rw [hs, zero_add]) _) fun w ↦ ?_
  exact sMod_pure (f := fun _ ↦ TMode.free) _

omit [Fintype M] [DecidableEq M] in
/-- **A randomizer trial's hash** of a one-block input whose block is a trial block. -/
theorem modedE_hashTrial (u : X → X → M → Option X → M) (input : HashInput) (b : X)
    (hb : blocks input = [b]) (hT : TrialBlock P b) :
    ModedE (L := LocalSig.instruments) (okR π P) (nxR π) (fun _ ↦ .free) .free
      (hashTrial M u π B input) := by
  have hfold : SMod π P (B := B) .free (fun _ ↦ .free)
      ((blocks input).foldlM (rdRoundU M u π B) (0, 0)) := by
    rw [hb]
    exact sMod_bind (sMod_rdRoundU u (0, 0) b rfl (by rw [zero_add]; exact hT))
      fun s' ↦ sMod_pure (f := fun _ ↦ TMode.free) s'
  exact modedE_map (f := fun _ ↦ TMode.free) Prod.fst
    (sMod_map (f := fun _ ↦ TMode.free) (out256 : X → HashOutput)
      (sMod_map (f := fun _ ↦ TMode.free) (fun s : X × Z ↦ s.1) hfold) [])

omit [Fintype M] [DecidableEq M] in
/-- **The randomizer search** of a label's message is moded. -/
theorem modedE_grindR (upd : TrialUpd M) (pub : Pub) (l : Layer) (e : KeyIndex)
    {message : HashInput} (hm : message.length ≤ 32) (base : Randomizer) :
    ∀ n trial, ModedE (L := LocalSig.instruments) (okR pub.perm pub.param) (nxR pub.perm)
      (fun _ ↦ .free) .free (grindR M upd pub B l e message base n trial)
  | 0, _ => rfl
  | n + 1, trial => by
    rw [grindR]
    obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp (length_blocks_trial pub.param
      (hashDomainFields (.message l e)) hm base trial)
    refine modedE₂_bind (fin := fun _ ↦ TMode.free) (fin' := fun _ ↦ TMode.free) _ _
      (modedE_hashTrial (upd l e) _ b hb ⟨l, e, message, _, hm, hb⟩) fun out ↦ ?_
    show ModedE _ _ _ _ (match Codeword.decode (truncateHash out) with
      | some x => QuantumComp₂.pure (some (base + BitVec.ofNat digestBits trial, x))
      | none => grindR M upd pub B l e message base n (trial + 1))
    split
    · rfl
    · exact modedE_grindR upd pub l e hm base n (trial + 1)

end smod

/-! ### Lifting the modes to the template and to runtime 2 -/

omit [Fintype M] [DecidableEq M] in
theorem rdOk_liftRead {μ : TMode} {c : HwRead X Z M} (h : rdOk π P μ c) :
    rdOk π P μ (liftRead (S := HPos) c) := by
  rcases μ with _ | ⟨x, a⟩ | z <;> rcases c with ⟨z', u⟩ | ⟨x', u⟩ | ⟨y, u⟩
  all_goals first
    | exact h
    | exact ⟨h.1, by rw [h.2]⟩

omit [Fintype M] [DecidableEq M] in
/-- **Lifting runtime 1's moded programs to templates.** -/
theorem modedE_readLift {Ω : QReg → Type} {A : QReg} {fin : (Σ u, Ω u) → TMode}
    (y : QuantumComp LocalSig.instruments (hwReadSpec X Z M) Ω A) {μ : TMode}
    (hy : ModedE (okR π P) (nxR π) fin μ y) :
    ModedE (okT π P) (nxT π) fin μ (readLift goodAll y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedE _ _ _ μ (IFreeM.mapLens (readLens goodAll) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · refine ⟨rdOk_liftRead hy.1, fun b ↦ ?_⟩
      rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;> rcases μ with _ | ⟨x', a⟩ | z' <;>
        exact ih _ (hy.2 (ULift.up (b.down.1, b.down.2.2)))

omit [Fintype M] [DecidableEq M] in
/-- A sponge program of runtime 1 is moded, free throughout. -/
theorem modedE_liftOrdinary {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments (spongeSpec X Z) Ω A) :
    ModedE (okR π P) (nxR π) (fun _ ↦ .free) .free
      (y.liftOrdinary (t := hwReadCmdSpec X Z M)) := by
  induction y using IFreeM.inductionOn with
  | pure _ a => rfl
  | liftBind _ c next ih =>
    show ModedE _ _ _ _ (IFreeM.mapLens QuantumComp.ordinaryLens (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _⟩
    · exact ⟨rfl, fun b ↦ ih _⟩

omit [Fintype M] [DecidableEq M] in
/-- **Realizing keeps the modes.** -/
theorem modedE_realizeT (v : HPos → Digest) {L : LocalSig.{u, v}} {Ω : QReg → Type w}
    {A : QReg} {fin : (Σ u, Ω u) → TMode} (y : QuantumComp L (XSpec M) Ω A) {μ : TMode}
    (hy : ModedE (okT π P) (nxT π) fin μ y) :
    ModedE (okZ π P) (nxZ π) fin μ (realizeT v y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedE _ _ _ μ (IFreeM.mapLens (tmplLens v) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨((i | c) | ⟨p, hp⟩) | T, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · cases p <;> exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩

/-! ### The challenge prefix is moded -/

section trialPrefix

variable (π P) in
/-- A template moded from the free mode back to it. -/
abbrev TFree {Ω : QReg → Type} {A : QReg} (y : QuantumComp LocalSig.instruments (XSpec M) Ω A) :
    Prop :=
  ModedE (okT π P) (nxT π) (fun _ ↦ .free) .free y

omit [Fintype M] [DecidableEq M] in
theorem tFree_bind {A B B' : QReg} {α β : Type} (x : QComp (XSpec M) A B α)
    (g : α → QComp (XSpec M) B B' β) (hx : TFree π P x) (hg : ∀ a, TFree π P (g a)) :
    TFree π P (x.bind g) :=
  modedE₂_bind (fin := fun _ ↦ TMode.free) (fin' := fun _ ↦ TMode.free) x g hx hg

omit [Fintype M] [DecidableEq M] in
theorem tFree_act {A B : QReg} {α : Type} (p : SubInstrument A B α) :
    TFree π P (QComp.act (spec := XSpec M) p) :=
  ⟨trivial, fun _ ↦ rfl⟩

omit [Fintype M] [DecidableEq M] in
theorem tFree_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (XSpec M) B B' α)
    (hk : ∀ r, TFree π P (k r)) : TFree π P (revealThen goodAll T k) :=
  ⟨rfl, fun b ↦ tFree_bind _ _ (tFree_act _) fun _ ↦ hk b.down⟩

omit [Fintype M] [DecidableEq M] in
theorem tFree_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (XSpec M) B B' α) (hk : TFree π P k) : TFree π P (progThen p hp k) :=
  ⟨rfl, fun _ ↦ tFree_bind _ _ (tFree_act _) fun _ ↦ hk⟩

omit [Fintype M] [DecidableEq M] in
theorem tFree_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) :
    TFree π P (progPorts M B ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => exact tFree_progThen p trivial _ ih

omit [Fintype M] [DecidableEq M] in
theorem tFree_progSlots (pub : Pub) (B : QReg) (ss : List Slot) :
    TFree π P (progSlots M pub B ss) := by
  induction ss with
  | nil => rfl
  | cons s ss ih => exact tFree_bind _ _ (tFree_progPorts B _) fun _ ↦ ih

variable (upd : TrialUpd M)

omit [Fintype M] [DecidableEq M] in
theorem tFree_signLayerT (pub : Pub) (B : QReg) (lab : RLabel) :
    TFree pub.perm pub.param (signLayerT M upd pub B lab) := by
  refine tFree_revealThen _ _ fun r₀ ↦ tFree_bind _ _
    (modedE_readLift _ (modedE_grindR upd pub lab.layer lab.key (RLabel.length_msg_le lab) _ _ _))
    fun g ↦ ?_
  rcases g with _ | ⟨ρ, x⟩
  · rfl
  · exact tFree_revealThen _ _ fun r ↦ tFree_bind _ _ (tFree_progSlots pub B _) fun _ ↦ rfl

omit [Fintype M] [DecidableEq M] in
theorem tFree_signT (pub : Pub) (B : QReg) (r : SigningRequest) :
    TFree pub.perm pub.param (signT M upd pub B r) := by
  refine tFree_bind _ _ (tFree_signLayerT upd pub B _) fun b ↦ ?_
  rcases b with _ | ⟨bottom, f⟩
  · rfl
  · refine tFree_bind _ _ (tFree_signLayerT upd pub B _) fun t ↦ ?_
    rcases t with _ | ⟨top, _⟩ <;> rfl

omit [Fintype M] [DecidableEq M] in
theorem tFree_challengeT (pub : Pub) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (advSpec (X × Z)) A) :
    ModedE (okT pub.perm pub.param) (nxT pub.perm) (fun _ ↦ .free) .free
      (challengeT M upd pub A c) := by
  rcases c with o | ⟨p | r, E, ℓ⟩
  · exact modedE_readLift _ (modedE_liftOrdinary _)
  · exact modedE_readLift _ (modedE_liftOrdinary _)
  · exact modedE_bind _ _ (tFree_bind _ _ (tFree_act _) fun _ ↦ tFree_signT upd pub _ r)
      fun _ _ ↦ rfl

omit [Fintype M] [DecidableEq M] in
theorem modedE_cast {spec : QuantumOracleSpec.{0, 0}} {ok : TMode → spec.Port → Prop}
    {nx : TMode → (i : spec.Port) → spec.Result i → TMode} {Ω : QReg → Type w}
    {fin : (Σ u, Ω u) → TMode} {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) (μ : TMode) :
    ModedE ok nx fin μ (e ▸ y) ↔ ModedE ok nx fin μ y := by
  subst e
  rfl

omit [Fintype M] [DecidableEq M] in
/-- Substituting moded trees that start and end free. -/
theorem modedE_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments spec)
      (QuantumComp.toIPFunctor LocalSig.instruments (XSpec M)))
    (hσ : ∀ A c, ModedE (okT π P) (nxT π) (fun _ ↦ .free) .free (σ A c)) {Ω : QReg → Type}
    {A : QReg} (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) :
    ModedE (okT π P) (nxT π) (fun _ ↦ .free) .free (x.substitute σ) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind s c next ih =>
    rw [IFreeM.substitute_liftBind]
    exact modedE_bind _ _ (hσ s c) fun u ans ↦ (modedE_cast ans.2 _ _).mpr (ih ans.1)

omit [Fintype M] [DecidableEq M] in
/-- **The challenge prefix is moded**: its reads are randomizer trials. -/
theorem tFree_prefixT (pub : Pub) (A : Adversary (X × Z)) :
    TFree pub.perm pub.param (prefixT M upd pub A) :=
  tFree_revealThen _ _ fun _ ↦ tFree_bind _ _
    (modedE_substitute _ (tFree_challengeT upd pub) _) fun _ ↦ rfl

end trialPrefix

end modes

/-! ## Potentials -/

section pot

variable {A Zp D : Type} [Fintype A] [DecidableEq A] [Fintype Zp] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
theorem potential_zero (σ : Matrix (A × D) (A × D) ℂ) :
    potential (0 : Matrix Zp D ℂ) σ = 0 := by
  rw [potential_eq, Matrix.mul_zero, Matrix.kronecker_zero, Matrix.zero_mul, Matrix.trace_zero,
    Complex.zero_re, ENNReal.ofReal_zero]

omit [Fintype A] [Fintype D] in
theorem one_kronecker_setProj (S : Set D) :
    (1 : Matrix A A ℂ) ⊗ₖ setProj S = setProj {q : A × D | q.2 ∈ S} := by
  ext ⟨a, d⟩ ⟨a', d'⟩
  simp only [kroneckerMap_apply, setProj, diagonal_apply, Matrix.one_apply, Prod.mk.injEq,
    Set.indicator, Pi.one_apply]
  by_cases ha : a = a' <;> by_cases hd : d = d' <;> simp [ha, hd]

/-- The potential of a projector on basis states is their diagonal mass. -/
theorem potential_setProj (S : Set D) {σ : Matrix (A × D) (A × D) ℂ} (hσ : σ.PosSemidef) :
    potential (setProj S) σ = diagMass {q : A × D | q.2 ∈ S} σ := by
  rw [potential_eq, conjTranspose_setProj, setProj_mul_self, one_kronecker_setProj]
  exact ofReal_trace_setProj_mul _ hσ

omit [DecidableEq D] in
/-- The potential after a Kraus operator acting on the register only. -/
theorem potential_conj_kron (K : Matrix Zp D ℂ) (N : Matrix D D ℂ)
    (σ : Matrix (A × D) (A × D) ℂ) :
    potential K (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ N) σ) = potential (K * N) σ := by
  simp only [potential, MatrixMap.amplifyLeft_conj, MatrixMap.conj_apply]
  congr 3
  have h1 : (1 : Matrix A A ℂ) ⊗ₖ (K * N) =
      ((1 : Matrix A A ℂ) ⊗ₖ K) * ((1 : Matrix A A ℂ) ⊗ₖ N) := by
    rw [← mul_kronecker_mul, Matrix.one_mul]
  have h2 : (1 : Matrix A A ℂ) ⊗ₖ (Nᴴ * Kᴴ) =
      ((1 : Matrix A A ℂ) ⊗ₖ Nᴴ) * ((1 : Matrix A A ℂ) ⊗ₖ Kᴴ) := by
    rw [← mul_kronecker_mul, Matrix.one_mul]
  simp only [conjTranspose_kronecker, conjTranspose_one, conjTranspose_mul]
  rw [h1, h2]
  simp only [Matrix.mul_assoc]

end pot

/-! ## The read of one cell, with outcome-dependent diagonal weights -/

section cellBound

open Quantum.Sponge

variable {n Y R M0 : Type} [Fintype n] [DecidableEq n] [Fintype Y] [DecidableEq Y]
  [Fintype R] [DecidableEq R] [Fintype M0] [DecidableEq M0]
  {e : n ≃ Option Y × R} {act : R → Prop} [DecidablePred act] {μ : R → M0}
  {τ : Option Y → R → R} {K : Option Y × M0 → Matrix n n ℂ} {idx : n → Option Y × M0}
  {φ : n → n}

variable (e) in
/-- The diagonal weight `q o` of the rests, for the outcome `o`. -/
noncomputable def wDiag (q : Option Y → R → ℝ) (o : Option Y) : Matrix n n ℂ :=
  diagonal fun t ↦ ((q o (e t).2 : ℝ) : ℂ)

omit [Fintype Y] [DecidableEq Y] [Fintype R] [DecidableEq R] [Fintype M0] [DecidableEq M0]
  [DecidablePred act] in
theorem gramQ_term (q : Option Y → R → ℝ) (i : Option Y × M0) (t s : n) :
    ((K i)ᴴ * wDiag e q i.1 * K i) t s =
      ∑ u, star (K i u t) * ((q i.1 (e u).2 : ℝ) : ℂ) * K i u s := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [wDiag, mul_diagonal, conjTranspose_apply]

omit [DecidablePred act] in
/-- **The Gram operator of a cell read with outcome-dependent weights**, on an active column. -/
theorem gramQ_apply (h : CellRead e act μ τ K) (q : Option Y → R → ℝ) {s : n}
    (hs : act (e s).2) (t : n) :
    (∑ i, (K i)ᴴ * wDiag e q i.1 * K i) t s =
      if (e t).2 = (e s).2 then
        ((∑ o, cr (e t).1 o * (∑ a, cr a o ^ 2 * q o (τ o (e s).2)) * cr o (e s).1 : ℝ) : ℂ)
      else 0 := by
  simp only [Matrix.sum_apply, gramQ_term]
  split_ifs with hts
  · have ht : act (e t).2 := hts ▸ hs
    rw [Fintype.sum_prod_type]
    push_cast
    refine Finset.sum_congr rfl fun o _ ↦ ?_
    rw [Finset.sum_eq_single (μ (e s).2)]
    · rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm,
        Finset.sum_eq_single (τ o (e s).2)]
      · rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [h.entry _ _ _ _ ht, h.entry _ _ _ _ hs]
        simp only [Equiv.apply_symm_apply, hts, and_self, ↓reduceIte, Complex.star_def,
          Complex.conj_ofReal]
        push_cast
        rw [cr_comm o (e t).1]
        ring
      · intro r _ hr
        refine Finset.sum_eq_zero fun a _ ↦ ?_
        rw [h.entry _ _ _ _ hs]
        simp [hr]
      · simp
    · intro m0 _ hm
      refine Finset.sum_eq_zero fun u _ ↦ ?_
      rw [h.entry _ _ _ _ hs]
      simp [Ne.symm hm]
    · simp
  · refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun u _ ↦ ?_
    by_cases hKs : K i u s = 0
    · simp [hKs]
    obtain ⟨hμ, hτ⟩ := Quantum.Sponge.cellRead_ne_zero h hs hKs
    have hKt : K i u t = 0 := by
      by_contra hKt
      by_cases ht : act (e t).2
      · obtain ⟨hμ', hτ'⟩ := Quantum.Sponge.cellRead_ne_zero h ht hKt
        exact hts (h.inj i.1 _ _ (hμ'.trans hμ.symm) (hτ'.symm.trans hτ))
      · exact h.off i u t ht hKt (hτ ▸ h.act_τ _ _ hs)
    simp [hKt]

omit [Fintype R] [DecidablePred act] in
/-- The Gram operator of a cell read with outcome-dependent weights, on a hardwired column. -/
theorem gramQ_off (h : CellRead e act μ τ K) (hc : ClsOff e act K idx φ)
    (q : Option Y → R → ℝ) {s : n} (hs : ¬ act (e s).2) (t : n) :
    (∑ i, (K i)ᴴ * wDiag e q i.1 * K i) t s =
      if t = s then ((q (idx s).1 (e (φ s)).2 : ℝ) : ℂ) else 0 := by
  simp only [Matrix.sum_apply, gramQ_term]
  rw [Finset.sum_eq_single (idx s)]
  · rw [Finset.sum_eq_single (φ s)]
    · have hφ : ¬ act (e (φ s)).2 := h.off (idx s) (φ s) s hs (by rw [hc.entry _ _ _ hs]; simp)
      rw [hc.entry _ _ _ hs, ite_eq_left ⟨rfl, rfl⟩, mul_one]
      by_cases ht : act (e t).2
      · have h0 : K (idx s) (φ s) t = 0 := by
          by_contra h0
          exact hφ ((Quantum.Sponge.cellRead_ne_zero h ht h0).2 ▸ h.act_τ _ _ ht)
        rw [h0, star_zero, zero_mul, ite_eq_right]
        rintro rfl
        exact hs ht
      · rw [hc.entry _ _ _ ht]
        by_cases hts : t = s
        · subst hts
          simp
        · rw [ite_eq_right, ite_eq_right hts]
          · simp
          · rintro ⟨h1, h2⟩
            exact hts (hc.inj t s ht hs h1.symm h2.symm)
    · intro u _ hu
      rw [hc.entry _ _ _ hs, ite_eq_right fun h' ↦ hu h'.2, mul_zero]
    · simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun u _ ↦ ?_
    rw [hc.entry _ _ _ hs, ite_eq_right fun h' ↦ hi h'.1, mul_zero]
  · simp

omit [Fintype n] [DecidableEq n] [DecidableEq Y] in
/-- A positive semidefinite matrix bounds its cross terms: `c (σᵢⱼ + σⱼᵢ) ≤ σᵢᵢ + c² σⱼⱼ`. -/
theorem re_cross_le {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (i j : n) (c : ℝ) :
    c * (σ i j + σ j i).re ≤ (σ i i).re + c ^ 2 * (σ j j).re := by
  have h2 := (hσ.submatrix ![i, j]).dotProduct_mulVec_nonneg ![1, -(c : ℂ)]
  simp only [dotProduct, mulVec, Fin.sum_univ_two, submatrix_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.star_apply, mul_one] at h2
  have e1 : star (1 : ℂ) = 1 := star_one _
  have e2 : star (-(c : ℂ)) = -(c : ℂ) := by rw [star_neg, Complex.star_def, Complex.conj_ofReal]
  rw [e1, e2, one_mul] at h2
  have h3 := (Complex.le_def.1 h2).1
  simp only [Complex.zero_re, Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.neg_im] at h3
  rw [Complex.add_re]
  nlinarith [h3]

variable [Nonempty Y]

omit [Fintype n] [DecidableEq n] [Nonempty Y] in
/-- With no recorded amplitude along the rows, the empty outcome has no weight. -/
theorem cellV_none {S : Matrix (Option Y) (Option Y) ℂ} (hrow : ∀ a, ∑ y, S (some y) a = 0) :
    ∑ a', ∑ a, ((cr none a' * cr a none : ℝ) : ℂ) * S a' a = 0 := by
  rw [Fintype.sum_option]
  simp only [cr, zero_mul, Complex.ofReal_zero, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  rcases a with _ | y
  · simp
  · simp only [Complex.ofReal_mul]
    rw [← Finset.mul_sum, hrow, mul_zero]

omit [Fintype n] [DecidableEq n] [Nonempty Y] in
/-- **The weight of a recorded outcome** with no recorded amplitude along the rows and columns:
`σ_yy + (σ_y⊥ + σ_⊥y)/√N + σ_⊥⊥/N`. -/
theorem cellV_some {S : Matrix (Option Y) (Option Y) ℂ} (hrow : ∀ a, ∑ y, S (some y) a = 0)
    (hcol : ∀ a, ∑ y, S a (some y) = 0) (y : Y) :
    ∑ a', ∑ a, ((cr (some y) a' * cr a (some y) : ℝ) : ℂ) * S a' a =
      S (some y) (some y) + (((Real.sqrt (Fintype.card Y))⁻¹ : ℝ) : ℂ) *
        (S (some y) none + S none (some y)) +
        (((Fintype.card Y : ℝ)⁻¹ : ℝ) : ℂ) * S none none := by
  set c : ℂ := (((Real.sqrt (Fintype.card Y))⁻¹ : ℝ) : ℂ)
  set N : ℂ := (((Fintype.card Y : ℝ)⁻¹ : ℝ) : ℂ)
  have hcc : c * c = N := by
    simp only [c, N, ← Complex.ofReal_mul, inv_sqrt_mul_inv_sqrt_card]
  have hX : ∀ a', ∑ a, ((cr (some y) a' * cr a (some y) : ℝ) : ℂ) * S a' a =
      (cr (some y) a' : ℂ) * (c * S a' none + S a' (some y)) := fun a' ↦ by
    have hs : ∑ y', ((cr (some y') (some y) : ℝ) : ℂ) * S a' (some y') =
        S a' (some y) - N * ∑ y', S a' (some y') := by
      simp only [cr, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp [N, apply_ite (fun x : ℝ ↦ (x : ℂ)), ite_mul]
    rw [Fintype.sum_option]
    simp only [Complex.ofReal_mul, mul_assoc, ← Finset.mul_sum]
    rw [hs, hcol a', mul_zero, sub_zero]
    simp only [cr, c]
    ring
  simp only [hX]
  rw [Fintype.sum_option]
  have hs : ∑ y', ((cr (some y) (some y') : ℝ) : ℂ) *
      (c * S (some y') none + S (some y') (some y)) =
      (c * S (some y) none + S (some y) (some y)) -
        N * ∑ y', (c * S (some y') none + S (some y') (some y)) := by
    simp only [cr, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [N, apply_ite (fun x : ℝ ↦ (x : ℂ)), ite_mul]
  rw [hs, Finset.sum_add_distrib, ← Finset.mul_sum, hrow, hrow, mul_zero, add_zero, mul_zero,
    sub_zero]
  simp only [cr, c]
  rw [← hcc]
  ring

variable (e act τ idx φ) in
/-- **The diagonal bound of a read with outcome-dependent weights**: on an active rest, twice the
recorded outcome's weight on a recorded cell, `2/N` times the summed weights on an empty cell; on a
hardwired cell, the weight of its classical move. -/
noncomputable def cB (q : Option Y → R → ℝ) (s : n) : ℝ :=
  if act (e s).2 then
    (e s).1.elim (2 / Fintype.card Y * ∑ y, q (some y) (τ (some y) (e s).2))
      fun y ↦ 2 * q (some y) (τ (some y) (e s).2)
  else q (idx s).1 (e (φ s)).2

/-- **The read of one cell with outcome-dependent weights**: for a state with no decompressed `⊥`
at the cell, the weights after the read are at most the diagonal bound `cB` of the state. -/
theorem re_trace_gramQ_le (h : CellRead e act μ τ K) (hc : ClsOff e act K idx φ)
    (q : Option Y → R → ℝ) (hq : ∀ o r, 0 ≤ q o r) {σ : Matrix n n ℂ} (hσ : σ.PosSemidef)
    (hnb : CellNoBot e act σ) :
    ((∑ i, (K i)ᴴ * wDiag e q i.1 * K i) * σ).trace.re ≤
      ∑ s, cB e act τ idx φ q s * (σ s s).re := by
  obtain ⟨G, hG⟩ : ∃ G : Matrix n n ℂ, G = ∑ i, (K i)ᴴ * wDiag e q i.1 * K i := ⟨_, rfl⟩
  rw [← hG]
  have hGa : ∀ s, act (e s).2 → ∀ t, G t s = if (e t).2 = (e s).2 then
      ((∑ o, cr (e t).1 o * (∑ a, cr a o ^ 2 * q o (τ o (e s).2)) * cr o (e s).1 : ℝ) : ℂ)
      else 0 := fun s hs t ↦ by rw [hG]; exact gramQ_apply h q hs t
  have hGo : ∀ s, ¬ act (e s).2 → ∀ t,
      G t s = if t = s then ((q (idx s).1 (e (φ s)).2 : ℝ) : ℂ) else 0 :=
    fun s hs t ↦ by rw [hG]; exact gramQ_off h hc q hs t
  have htr : (G * σ).trace = ∑ s, ∑ t, G t s * σ s t := by
    rw [Matrix.trace]
    simp only [diag_apply, Matrix.mul_apply]
    exact Finset.sum_comm
  have hsplit : ∀ f : n → ℝ, ∑ s, f s = ∑ r, ∑ a, f (e.symm (a, r)) := fun f ↦ by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rw [htr, Complex.re_sum, hsplit, hsplit]
  refine Finset.sum_le_sum fun r _ ↦ ?_
  by_cases hr : act r
  · -- an active rest
    obtain ⟨S, hS⟩ : ∃ S : Matrix (Option Y) (Option Y) ℂ,
        ∀ a' a, σ (e.symm (a', r)) (e.symm (a, r)) = S a' a := ⟨fun a' a ↦ _, fun _ _ ↦ rfl⟩
    obtain ⟨g, hg⟩ : ∃ g : Option Y → ℝ, ∀ o, ∑ b, cr b o ^ 2 * q o (τ o r) = g o :=
      ⟨_, fun _ ↦ rfl⟩
    have hrow : ∀ a, ∑ y, S (some y) a = 0 := fun a ↦ by
      simp only [← hS]
      exact hnb r hr _
    have hcol : ∀ a, ∑ y, S a (some y) = 0 := fun a ↦ by
      simp only [← hS]
      exact cellNoBot_col hσ.isHermitian hnb hr _
    have hF : ∀ a', ∑ t, G t (e.symm (a', r)) * σ (e.symm (a', r)) t =
        ∑ a, ((∑ o, cr a o * g o * cr o a' : ℝ) : ℂ) * S a' a := fun a' ↦ by
      have hs : act (e (e.symm (a', r))).2 := by rw [Equiv.apply_symm_apply]; exact hr
      rw [sum_rest_eq (e := e) r fun t ht ↦ by
        rw [hGa _ hs, Equiv.apply_symm_apply, ite_eq_right ht, zero_mul]]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [hGa _ hs]
      simp only [Equiv.apply_symm_apply, ↓reduceIte, hg, hS]
    have hVc : ∑ a', ∑ a, ((∑ o, cr a o * g o * cr o a' : ℝ) : ℂ) * S a' a =
        ∑ o, (g o : ℂ) * ∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a := by
      simp only [Complex.ofReal_sum, Finset.sum_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a' _ ↦ ?_
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun o _ ↦ ?_
      push_cast
      ring
    simp only [hF]
    rw [← Complex.re_sum, hVc, Complex.re_sum]
    simp only [Complex.re_ofReal_mul]
    rw [Fintype.sum_option, cellV_none hrow, Complex.zero_re, mul_zero, zero_add,
      Fintype.sum_option]
    simp only [cB, Equiv.apply_symm_apply, hr, ↓reduceIte, Option.elim_none, Option.elim_some, hS]
    have hle : ∀ y : Y, g (some y) *
        (∑ a', ∑ a, ((cr (some y) a' * cr a (some y) : ℝ) : ℂ) * S a' a).re ≤
        2 * q (some y) (τ (some y) r) * (S (some y) (some y)).re +
          2 / Fintype.card Y * q (some y) (τ (some y) r) * (S none none).re := fun y ↦ by
      rw [← hg, ← Finset.sum_mul, sum_cr_sq, one_mul, cellV_some hrow hcol y]
      have hcross : (Real.sqrt (Fintype.card Y))⁻¹ * (S (some y) none + S none (some y)).re ≤
          (S (some y) (some y)).re + (Fintype.card Y : ℝ)⁻¹ * (S none none).re := by
        have h0 := re_cross_le hσ (e.symm (some y, r)) (e.symm (none, r))
          (Real.sqrt (Fintype.card Y))⁻¹
        rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at h0
        simpa only [hS, Complex.add_re] using h0
      simp only [Complex.add_re, Complex.re_ofReal_mul] at hcross ⊢
      have hq0 := hq (some y) (τ (some y) r)
      have hd : 0 ≤ (S none none).re := by
        rw [← hS]
        exact (Complex.nonneg_iff.1 hσ.diag_nonneg).1
      have hd' : 0 ≤ (S (some y) (some y)).re := by
        rw [← hS]
        exact (Complex.nonneg_iff.1 hσ.diag_nonneg).1
      have hN : 0 ≤ (Fintype.card Y : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
      rw [div_eq_mul_inv]
      nlinarith [mul_le_mul_of_nonneg_left hcross hq0, mul_nonneg hq0 (mul_nonneg hN hd)]
    calc ∑ y, g (some y) *
          (∑ a', ∑ a, ((cr (some y) a' * cr a (some y) : ℝ) : ℂ) * S a' a).re
        ≤ ∑ y, (2 * q (some y) (τ (some y) r) * (S (some y) (some y)).re +
            2 / Fintype.card Y * q (some y) (τ (some y) r) * (S none none).re) :=
          Finset.sum_le_sum fun y _ ↦ hle y
      _ = _ := by
          rw [Finset.sum_add_distrib, add_comm, ← Finset.sum_mul, ← Finset.mul_sum]
  · -- a hardwired rest
    refine le_of_eq (Finset.sum_congr rfl fun a _ ↦ ?_)
    have hs : ¬ act (e (e.symm (a, r))).2 := by rw [Equiv.apply_symm_apply]; exact hr
    rw [Finset.sum_eq_single (e.symm (a, r))]
    · rw [hGo _ hs, ite_eq_left rfl, cB, ite_eq_right hs, Complex.re_ofReal_mul]
    · intro t _ ht
      rw [hGo _ hs, ite_eq_right ht, zero_mul]
    · simp

end cellBound

/-! ## Moving the trials' hidden mass onto their `k`-reads -/

section trialW

open HashSig LeanXmss

/-- The register states whose `h`-cell `z` is hidden and not hardwired. -/
def hSet {Mem : Type} (Hh : Set Z) (z : Z) : Set (HwReg X Z Mem) :=
  {d | z ∈ Hh ∧ d.2.1.1 z = none}

/-- The register states whose `k'`-cell `y` is hidden and not hardwired. -/
def k'Set {Mem : Type} (Hk' : Set X) (y : X) : Set (HwReg X Z Mem) :=
  {d | y ∈ Hk' ∧ d.2.1.2.2 y = none}

variable {Mem : Type} [Fintype Mem] [DecidableEq Mem] (π : Equiv.Perm (X × Z)) (Hh : Set Z)
  (Hk' : Set X)

/-- **The potentials of the trial modes**: after the `k`-read at `x` with outcome `a`, the hidden
mass of the coming `k'`-read at `π (x, a)` and, through each of its outcomes, of the `h`-read at
`π (x, a) + c`; after the `k'`-read, that of the `h`-read. -/
noncomputable def kpot : TMode → Option (Option Z × Mem) → Matrix (HwReg X Z Mem) (HwReg X Z Mem) ℂ
  | .free, _ => 0
  | .afK x a, none => setProj (k'Set Hk' (π (x, a)).1)
  | .afK x a, some r =>
      setProj (hSet Hh ((π (x, a)).2 + r.1.getD 0)) * readKrausK' (π (x, a)).1 (fun m _ ↦ m) r
  | .afK' z, none => setProj (hSet Hh z)
  | .afK' _, some _ => 0

variable {S M : Type} [Fintype S] [DecidableEq S] [Fintype M] [DecidableEq M]

/-- **The trial charge**: at a `k`-read at `x`, the potentials of the coming `k'`- and `h`-reads
through each outcome; nothing elsewhere. -/
noncomputable def trialW :
    ∀ i : (recHwSpec X Z S M).Port, Matrix ((recHwSpec X Z S M).In i ×
      QReg.of (HwReg X Z (Finset S × M))) ((recHwSpec X Z S M).In i ×
        QReg.of (HwReg X Z (Finset S × M))) ℂ → ℝ≥0∞
  | .inl (.inl (.inr (.readK x _))), σ => ∑ r, ∑ j,
      potential (kpot π Hh Hk' (.afK x (r.1.getD 0)) j)
        (MatrixMap.conj (hwReadKraus (.readK x (fun m _ ↦ m)) r) σ)
  | _, _ => 0

theorem kpot_free (j : Option (Option Z × Mem)) : kpot π Hh Hk' .free j = 0 :=
  rfl

theorem sum_potential_kpot_free {A : Type} [Fintype A] [DecidableEq A]
    (σ : Matrix (A × HwReg X Z Mem)
    (A × HwReg X Z Mem) ℂ) : ∑ j, potential (kpot π Hh Hk' .free j) σ = 0 :=
  Finset.sum_eq_zero fun _ _ ↦ potential_zero σ

variable {π Hh Hk'}

theorem portMass_readRec_read (Hk : Set X) (c : HwRead X Z (Finset HPos × M))
    (σ : Matrix (Unit × HwReg X Z (Finset HPos × M)) (Unit × HwReg X Z (Finset HPos × M)) ℂ) :
    portMass (S := HPos) (M' := M) (fun i ↦ readRecPort M i = true) Hh Hk Hk'
      (.inl (.inl (.inr c))) σ = diagMass (hidSet Hh Hk Hk' (.inl (.inr c))) σ := by
  have hQ : readRecPort M (.inl (.inl (.inr c))) = true := rfl
  simp only [portMass, hQ, ↓reduceIte]
  exact congrFun (congrFun (extWeight_hiddenMass_eq (t := recSpec HPos M)
    (M := Finset HPos × M) Hh Hk Hk') (.inl (.inl (.inr c)))) σ

theorem portMass_readRec_eq_zero (Hk : Set X) {i : (recHwSpec X Z HPos M).Port}
    (hi : ∀ c, i ≠ .inl (.inl (.inr c)))
    (σ : Matrix ((recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M)))
      ((recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) :
    portMass (fun i ↦ readRecPort M i = true) Hh Hk Hk' i σ = 0 := by
  rcases i with ((i | c) | c) | T
  · rfl
  · exact absurd rfl (hi c)
  · rfl
  · have hQ : readRecPort M (.inr T) = true := rfl
    simp only [portMass, hQ, ↓reduceIte]
    rw [congrFun (congrFun (extWeight_hiddenMass_eq (t := recSpec HPos M) Hh Hk Hk') _) σ]
    exact Finset.sum_eq_zero fun a _ ↦ Set.indicator_of_notMem (Set.notMem_empty a) _

theorem step_readH (Hk : Set X) (z : Z) (u : Finset HPos × M → Option X → Finset HPos × M)
    {σ : Matrix (Unit × HwReg X Z (Finset HPos × M)) (Unit × HwReg X Z (Finset HPos × M)) ℂ}
    (hσ : σ.PosSemidef) :
    portMass (fun i ↦ readRecPort M i = true) Hh Hk Hk' (.inl (.inl (.inr (.readH z u)))) σ +
        ∑' r : Option X × (Finset HPos × M), ∑ j, potential (kpot π Hh Hk' TMode.free j)
          (MatrixMap.conj (hwReadKraus (.readH z u) r) σ) ≤
      ∑ j, potential (kpot π Hh Hk' (.afK' z) j) σ + 0 := by
  rw [portMass_readRec_read]
  simp only [sum_potential_kpot_free, tsum_zero, add_zero]
  rw [Fintype.sum_option]
  simp only [kpot, potential_zero, Finset.sum_const_zero, add_zero]
  rw [potential_setProj _ hσ]
  exact le_rfl

theorem step_readK (Hk : Set X) (x : X) (hx : x ∉ Hk)
    (σ : Matrix (Unit × HwReg X Z (Finset HPos × M)) (Unit × HwReg X Z (Finset HPos × M)) ℂ) :
    portMass (fun i ↦ readRecPort M i = true) Hh Hk Hk'
        (.inl (.inl (.inr (.readK x (fun m _ ↦ m))))) σ +
        ∑' r : Option Z × (Finset HPos × M), ∑ j,
          potential (kpot π Hh Hk' (.afK x (r.1.getD 0)) j)
            (MatrixMap.conj (hwReadKraus (.readK x (fun m _ ↦ m)) r) σ) ≤
      ∑ j, potential (kpot π Hh Hk' TMode.free j) σ +
        trialW π Hh Hk' (S := HPos) (M := M) (.inl (.inl (.inr (.readK x (fun m _ ↦ m))))) σ := by
  have h0 : diagMass (hidSet Hh Hk Hk' (.inl (.inr (.readK x (fun m _ ↦ m)))) :
      Set (Unit × HwReg X Z (Finset HPos × M))) σ = 0 :=
    Finset.sum_eq_zero fun p _ ↦ Set.indicator_of_notMem (fun hp ↦ hx hp.1) _
  rw [portMass_readRec_read, h0, zero_add, sum_potential_kpot_free, zero_add, tsum_fintype]
  exact le_rfl

theorem step_readK' (Hk : Set X) (x : X) (a : Z)
    {σ : Matrix (Unit × HwReg X Z (Finset HPos × M)) (Unit × HwReg X Z (Finset HPos × M)) ℂ}
    (hσ : σ.PosSemidef) :
    portMass (fun i ↦ readRecPort M i = true) Hh Hk Hk'
        (.inl (.inl (.inr (.readK' (π (x, a)).1 (fun m _ ↦ m))))) σ +
        ∑' r : Option Z × (Finset HPos × M), ∑ j,
          potential (kpot π Hh Hk' (.afK' ((π (x, a)).2 + r.1.getD 0)) j)
            (MatrixMap.conj (hwReadKraus (.readK' (π (x, a)).1 (fun m _ ↦ m)) r) σ) ≤
      ∑ j, potential (kpot π Hh Hk' (.afK x a) j) σ + 0 := by
  rw [portMass_readRec_read, Fintype.sum_option, tsum_fintype, add_zero]
  simp only [kpot]
  rw [potential_setProj _ hσ]
  refine add_le_add le_rfl (le_of_eq (Finset.sum_congr rfl fun r _ ↦ ?_))
  rw [Fintype.sum_option]
  simp only [potential_zero, Finset.sum_const_zero, add_zero]
  exact potential_conj_kron _ _ σ

/-- **The step condition of the trial modes**: in runtime 2 with record ports, the hidden mass of
every allowed call plus the potentials after it is at most the potentials before plus the trial
charge, when no trial block is a hidden `k`-cell. -/
theorem trial_step (m₀ : Finset HPos × M) (P : PublicParameter) (Hk : Set X)
    (hk : ∀ x, TrialBlock P x → x ∉ Hk) (μ : TMode) (i : (recHwSpec X Z HPos M).Port)
    (σ : Matrix ((recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M)))
      ((recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M))) ℂ)
    (hσ : σ.PosSemidef) (hok : okZ π P μ i) :
    portMass (fun i ↦ readRecPort M i = true) Hh Hk Hk' i σ +
        ∑' r, ∑ j, potential (kpot π Hh Hk' (nxZ π μ i r) j)
          (((runtimeR m₀).step i).branch r σ) ≤
      ∑ j, potential (kpot π Hh Hk' μ j) σ + trialW π Hh Hk' i σ := by
  rcases i with ((i | c) | c) | T
  · obtain rfl : μ = .free := hok
    rw [portMass_readRec_eq_zero Hk (fun _ h ↦ by cases h), zero_add, sum_potential_kpot_free]
    exact (ENNReal.tsum_le_tsum fun r ↦ (sum_potential_kpot_free π Hh Hk' _).le).trans
      (by simp)
  · have hb : ∀ r, ((runtimeR m₀).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m₀ c r) σ
    simp only [hb]
    rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;> rcases μ with _ | ⟨x₀, a⟩ | z₀
    all_goals try exact False.elim hok
    · obtain rfl : z = z₀ := hok
      exact step_readH Hk z u hσ
    · obtain ⟨hT, rfl⟩ := hok
      exact step_readK Hk x (hk x hT) σ
    · obtain ⟨rfl, rfl⟩ := hok
      exact step_readK' Hk x₀ a hσ
  · obtain rfl : μ = .free := hok
    rw [portMass_readRec_eq_zero Hk (fun _ h ↦ by simp at h), zero_add, sum_potential_kpot_free]
    exact (ENNReal.tsum_le_tsum fun r ↦ (sum_potential_kpot_free π Hh Hk' _).le).trans
      (by simp)
  · obtain rfl : μ = .free := hok
    rw [portMass_readRec_eq_zero Hk (fun _ h ↦ by simp at h), zero_add, sum_potential_kpot_free]
    exact (ENNReal.tsum_le_tsum fun r ↦ (sum_potential_kpot_free π Hh Hk' _).le).trans
      (by simp)

/-- **The trials' hidden mass moves onto their `k`-reads**: the hidden mass of the challenge
prefix's reads is at most its trial charge, when no trial block is a hidden `k`-cell. -/
theorem totalWeight_prefixT_le_trialW (upd : TrialUpd M) (m₀ : Finset HPos × M) (pub : Pub)
    (A : Adversary (X × Z)) (v : HPos → Digest) (Hk : Set X)
    (hk : ∀ x, TrialBlock pub.param x → x ∉ Hk)
    {ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ} (hρ : ρ.PosSemidef) :
    (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (portMass (fun i ↦ readRecPort M i = true) Hh Hk Hk') (realizeT v (prefixT M upd pub A)) ρ ≤
      (runtimeR m₀).totalWeight LocalSig.Interp.instruments (trialW pub.perm Hh Hk')
        (realizeT v (prefixT M upd pub A)) ρ := by
  exact totalWeight_le_moded_of_zero (runtimeR m₀) LocalSig.Interp.instruments
    (kpot pub.perm Hh Hk') _ _ (fun μ i σ hσ hok ↦ trial_step m₀ pub.param Hk hk μ i σ hσ hok)
    (realizeT v (prefixT M upd pub A)) .free (fun _ ↦ rfl)
    (modedE_realizeT v _ (tFree_prefixT upd pub A)) hρ

end trialW

/-! ## The trial charge by the read of one cell, twice -/

section trialBound

open Quantum.Sponge

variable {Mem : Type} [Fintype Mem] [DecidableEq Mem]

omit [DecidableEq Mem] in
theorem potential_eq_kron (K : Matrix (HwReg X Z Mem) (HwReg X Z Mem) ℂ)
    (ρ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) :
    potential K ρ = ENNReal.ofReal
      ((((1 : Matrix Unit Unit ℂ) ⊗ₖ K)ᴴ * ((1 : Matrix Unit Unit ℂ) ⊗ₖ K) * ρ).trace.re) := by
  rw [potential_eq, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
    Matrix.one_mul]

omit [Fintype Mem] in
theorem kron_setProj_eq (S : Set (HwReg X Z Mem)) :
    (1 : Matrix Unit Unit ℂ) ⊗ₖ setProj S =
      diagonal fun t : Unit × HwReg X Z Mem ↦ (((Set.indicator S 1 t.2 : ℝ)) : ℂ) := by
  rw [one_kronecker_setProj]
  ext t t'
  simp only [setProj, diagonal_apply, Set.indicator, Pi.one_apply]
  split_ifs <;> simp_all

theorem potential_setProj_mul_eq (S : Set (HwReg X Z Mem))
    (N : Matrix (HwReg X Z Mem) (HwReg X Z Mem) ℂ)
    (ρ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) :
    potential (setProj S * N) ρ = ENNReal.ofReal
      ((((1 : Matrix Unit Unit ℂ) ⊗ₖ N)ᴴ * ((1 : Matrix Unit Unit ℂ) ⊗ₖ setProj S) *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ N) * ρ).trace.re) := by
  have h1 : (1 : Matrix Unit Unit ℂ) ⊗ₖ (setProj S * N) =
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ setProj S) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ N) := by
    rw [← mul_kronecker_mul, Matrix.one_mul]
  have hP : ((1 : Matrix Unit Unit ℂ) ⊗ₖ setProj S)ᴴ = (1 : Matrix Unit Unit ℂ) ⊗ₖ setProj S := by
    rw [conjTranspose_kronecker, conjTranspose_one, conjTranspose_setProj]
  have hPP : ((1 : Matrix Unit Unit ℂ) ⊗ₖ setProj S) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ setProj S) =
      (1 : Matrix Unit Unit ℂ) ⊗ₖ setProj S := by
    rw [← mul_kronecker_mul, Matrix.one_mul, setProj_mul_self]
  have key : ((1 : Matrix Unit Unit ℂ) ⊗ₖ (setProj S * N))ᴴ *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ (setProj S * N)) =
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ N)ᴴ * ((1 : Matrix Unit Unit ℂ) ⊗ₖ setProj S) *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ N) := by
    rw [h1, conjTranspose_mul, hP, Matrix.mul_assoc, ← Matrix.mul_assoc (1 ⊗ₖ setProj S), hPP,
      Matrix.mul_assoc]
  rw [potential_eq_kron, key]

theorem re_trace_kraus_setProj_nonneg (S : Set (HwReg X Z Mem))
    (N : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ)
    {ρ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hρ : ρ.PosSemidef) :
    0 ≤ (Nᴴ * ((1 : Matrix Unit Unit ℂ) ⊗ₖ setProj S) * N * ρ).trace.re := by
  have hP : ((1 : Matrix Unit Unit ℂ) ⊗ₖ setProj S).PosSemidef := by
    rw [kron_setProj_eq]
    refine PosSemidef.diagonal fun t ↦ ?_
    simp only [Set.indicator, Pi.one_apply]
    split_ifs <;> simp
  exact (hP.conjTranspose_mul_mul_same N).trace_mul_re_nonneg hρ

end trialBound

end Quantum.Xmss.Assembly

end
