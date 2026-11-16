module

public import Quantum.Sphincs.Assembly.CoversFull
public import Quantum.Sphincs.Assembly.HTrial
public import Quantum.Sphincs.Assembly.TrialHit
public import Quantum.Sphincs.Assembly.CostRun

@[expose] public section

/-!
# The masked hidden masses of leanSPHINCS's graded hybrid

The hidden mass at the ports `Q` (no program ports) of the canonical game at a padded table, for
the hidden sets of runtime 1's full table (`fullCovH`, CoversFull), averaged over the padded tables
of the good set `MassG S` (`0` elsewhere, so the bad fraction is paid once by the masked hybrid).

* **The generic masked bound** (`uavg_mask_portMass_le_sph`): on the good set the table's hidden
  sets lie in the template's (`hidH`, MassSources' sources, `2^-128` per call), in sets of the
  never-revealed part `KK` (each cell in them for at most `εK` of `KK`) and in further sets of the
  public data and the hidden values whose summed mass is a hypothesis `hX` (`κX` per call). The
  game at the table is the game at the reparametrized data up to the first-meeting record mass of
  the charged coordinates (MassSources' `mass_le_chgRev`), paid by `N · chgRevAvg`.
* **The never-revealed part's cells** (`kkH`, `kkK`, `kkK'`): the `SK.seed`-keyed derivations'
  (SeedStage's slots, `seedHK`, `seedK'K`; `seedKK`), the `PRF_msg` calls' (`prfKKH`, `prfKKK`,
  `prfKKK'`: `SK.prf` and the randomizer coins) and the non-first messages' `H_msg` cells
  (HmsgCovers' `rbCellsH`). Each cell is in them for at most `kkEps` of `KK`
  (`sum_indicator_kkH_le`, ...), `kkEps = seedEps 18 + |MasterSeed|⁻¹ + |HashOutput|⁻¹ +
  24 |Message| / |Z|`: a non-first message `M` (fixed by the cell: by the block, the rate's
  injectivity or the capacity's load `≤ 5`) for `|Message| / |Z|` each.
* **`hsub`** (`fullCov_subset`): on `MassG S` with `S` implying HmsgCovers' `HStatic`, the full
  table's hidden sets lie in `hidH ∪ kk ∪ tmCells`.
* **The bounds**: `uavg_mask_spongeMass_le_sph` (`6q` sponge calls) and
  `uavg_mask_readMass_le_sph` (TrialSource's read bound with HTrial's trials), with the template's
  `H_msg` cells' mass `hX` (`κX` per call) a hypothesis.
-/

open IPFunctor Matrix
open scoped ENNReal ComplexOrder Kronecker

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message MasterSeed PublicParameter Randomizer)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (uavg uavg_mono uavg_add uavg_const_mul portMass capOf rateOf
  CoinSlots spongeMass readMass)
open Quantum.Xmss.Assembly (Sources recHwSpec recSpec runtimeR realizeT invSupp extCls
  sum_totalWeight_portMass_le_count totalWeight_portMass_mono totalWeight_portMass_union_le
  sum_indicator_union_le card_filter_eq_sum_indicator le_div_mul_of_mul_le card_mul_sum_slot_le
  sum_indicator_range_gCap_le sum_indicator_notFirst_le gCap)
open Quantum.Sphincs.Hybrid (DLab dLabCell dLabCell_injective rCell rOrd rCell_injective skCell
  skCell_injective SkIdx Secret SeedKS seedEps)

namespace Quantum.Sphincs.Assembly

/-! ## The generic masked bound -/

section generic

variable (Q : (recHwSpec X Z HPos Selections).Port → Prop) [DecidablePred Q] (A : SAdversary)
  (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Mem HPos)))
    (QReg.of Unit × QReg.of (HwReg X Z (Mem HPos))) ℂ)

/-- The arithmetic of the per-public-datum sum, over abstract quantities. -/
theorem mask_sum_arith (N κ εK κX cV cK a x : ℝ≥0∞) (ha : a ≤ N * κ * cV)
    (hx : x ≤ N * κX * cV) :
    cK * a + cV * (εK * N * cK) + cK * x ≤ N * (κ + εK + κX) * (cV * cK) :=
  calc cK * a + cV * (εK * N * cK) + cK * x
      ≤ cK * (N * κ * cV) + cV * (εK * N * cK) + cK * (N * κX * cV) := by gcongr
    _ = N * (κ + εK + κX) * (cV * cK) := by ring

/-- A sum of three terms, over an abstract type. -/
theorem sum_three_eq {V : Type*} [Fintype V] (c d : ℝ≥0∞) (a x : V → ℝ≥0∞) :
    ∑ v, (c * a v + d + c * x v) = c * ∑ v, a v + Fintype.card V * d + c * ∑ v, x v := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

open scoped Classical in
/-- **The masked hidden mass at the ports `Q`** of the canonical game at the padded tables. On the
good set the table's hidden sets lie in the template's (`hidH`), in cells of the never-revealed part
(`Hhk`, each cell for at most `εK` of `KK`) and in further cells of the public data and the hidden
values (`Hhx`, mass `hX`). -/
theorem uavg_mask_portMass_le_sph (hQ : ∀ c, ¬Q (.inl (.inr c))) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Mem HPos)) ↦ p.2.2.2.1)
      {∅} ρ)
    (S : PP → ((s : HPos) → XD s) → Prop)
    (Hh : FT → Set Z) (Hk Hk' : FT → Set X)
    (Hhk : PP → ((s : HPos) → XD s) × KK → Set Z)
    (Hkk Hk'k : PP → ((s : HPos) → XD s) × KK → Set X)
    (Hhx : PP → ((s : HPos) → XD s) → Set Z) (Hkx Hk'x : PP → ((s : HPos) → XD s) → Set X)
    (hsub : ∀ t, MassG S t →
      Hh t ⊆ hidH (pubP (fullE t).1) (fullE t).2.1 ∪ Hhk (fullE t).1 (fullE t).2 ∪
        Hhx (fullE t).1 (fullE t).2.1 ∧
      Hk t ⊆ hidK (pubP (fullE t).1) (fullE t).2.1 ∪ Hkk (fullE t).1 (fullE t).2 ∪
        Hkx (fullE t).1 (fullE t).2.1 ∧
      Hk' t ⊆ hidK' (pubP (fullE t).1) (fullE t).2.1 ∪ Hk'k (fullE t).1 (fullE t).2 ∪
        Hk'x (fullE t).1 (fullE t).2.1)
    (εK : ℝ≥0∞)
    (hcH : ∀ p v z, ∑ k, (Hhk p (v, k)).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤
      εK * Fintype.card KK)
    (hcK : ∀ p v y, ∑ k, (Hkk p (v, k)).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤
      εK * Fintype.card KK)
    (hcK' : ∀ p v y, ∑ k, (Hk'k p (v, k)).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤
      εK * Fintype.card KK)
    {N : ℕ} (hN : ∀ (pub : Pub) (v : (s : HPos) → XD s),
      IFreeM.IsChargeBound (gameR msgPol A pub v) (portCharge fun i ↦ if Q i then 1 else 0) N)
    (κX : ℝ≥0∞)
    (hX : ∀ p, ∑ v, (runtimeR m0R).totalWeight LocalSig.Interp.instruments
      (portMass Q (Hhx p v) (Hkx p v) (Hk'x p v)) (gameR msgPol A (pubP p) v) ρ ≤
        N * κX * Fintype.card ((s : HPos) → XD s))
    (r : FT → ℝ≥0∞)
    (hmis : ∀ t, MassG S t → ∀ (Hh₀ : Set Z) (Hk₀ Hk'₀ : Set X),
      (runtimeR m0R).totalWeight LocalSig.Interp.instruments (portMass Q Hh₀ Hk₀ Hk'₀)
          (gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t))) ρ ≤
        (runtimeR m0R).totalWeight LocalSig.Interp.instruments (portMass Q Hh₀ Hk₀ Hk'₀)
          (gameR msgPol A (pubP (fullE t).1) (fullE t).2.1) ρ + N * r t)
    (μ : ℝ≥0∞) (hr : uavg (fun t : FT ↦ if MassG S t then r t else 0) ≤ μ) :
    uavg (fun t : FT ↦ if MassG S t then (runtimeR m0R).totalWeight LocalSig.Interp.instruments
      (portMass Q (Hh t) (Hk t) (Hk' t)) (gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t))) ρ
        else 0) ≤
      N * ((2 ^ 128 : ℝ≥0∞)⁻¹ + εK + κX) + N * μ := by
  set mK : PP → ((s : HPos) → XD s) × KK → ℝ≥0∞ := fun p w ↦
    (runtimeR m0R).totalWeight LocalSig.Interp.instruments
      (portMass Q (Hhk p w) (Hkk p w) (Hk'k p w)) (gameR msgPol A (pubP p) w.1) ρ with hmK
  set mX : PP → ((s : HPos) → XD s) → ℝ≥0∞ := fun p v ↦
    (runtimeR m0R).totalWeight LocalSig.Interp.instruments
      (portMass Q (Hhx p v) (Hkx p v) (Hk'x p v)) (gameR msgPol A (pubP p) v) ρ with hmX
  set g : PP → ((s : HPos) → XD s) × KK → ℝ≥0∞ := fun p w ↦
    massA Q A ρ p w.1 + mK p w + mX p w.1 with hg
  have hle : ∀ t, (if MassG S t then (runtimeR m0R).totalWeight LocalSig.Interp.instruments
      (portMass Q (Hh t) (Hk t) (Hk' t)) (gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t))) ρ
        else 0) ≤
      (if MassG S t then g (fullE t).1 (fullE t).2 else 0) +
        (N : ℝ≥0∞) * (if MassG S t then r t else 0) := by
    intro t
    by_cases ht : MassG S t
    · simp only [ht, ↓reduceIte]
      obtain ⟨h1, h2, h3⟩ := hsub t ht
      refine (hmis t ht _ _ _).trans (add_le_add ?_ le_rfl)
      refine (totalWeight_portMass_mono _ Q m0R h1 h2 h3 _ hρ).trans
        ((totalWeight_portMass_union_le _ Q m0R _ _ _ _ _ _ _ hρ).trans (add_le_add
          (totalWeight_portMass_union_le _ Q m0R _ _ _ _ _ _ _ hρ) le_rfl))
    · simp only [ht, ↓reduceIte, mul_zero, add_zero, le_refl]
  have hgsum : ∀ p, ∑ w, g p w ≤
      N * ((Fintype.card Digest : ℝ≥0∞)⁻¹ + εK + κX) *
        Fintype.card (((s : HPos) → XD s) × KK) := by
    intro p
    have hK : ∀ v : (s : HPos) → XD s, ∑ k, mK p (v, k) ≤ εK * N * Fintype.card KK := fun v ↦
      (sum_totalWeight_portMass_le_count LocalSig.Interp.instruments Q m0R _ hρ
        (fun k ↦ Hhk p (v, k)) (fun k ↦ Hkk p (v, k)) (fun k ↦ Hk'k p (v, k)) εK (hcH p v)
        (hcK p v) (hcK' p v) (hN _ v)).trans
        (by calc (εK * Fintype.card KK) * (N * ENNReal.ofReal ρ.trace.re)
              ≤ (εK * Fintype.card KK) * (N * 1) := by gcongr
            _ = εK * N * Fintype.card KK := by ring)
    refine sum_prod_le_of_sph (g p) _ ?_
    calc ∑ v, ∑ k, g p (v, k)
        ≤ ∑ v, ((Fintype.card KK : ℝ≥0∞) * massA Q A ρ p v + εK * N * Fintype.card KK +
            (Fintype.card KK : ℝ≥0∞) * mX p v) := by
          refine Finset.sum_le_sum fun v _ ↦ ?_
          simp only [hg]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
          exact add_le_add (add_le_add le_rfl (hK v)) le_rfl
      _ = (Fintype.card KK : ℝ≥0∞) * ∑ v, massA Q A ρ p v +
            Fintype.card ((s : HPos) → XD s) * (εK * N * Fintype.card KK) +
            (Fintype.card KK : ℝ≥0∞) * ∑ v, mX p v := by
          exact sum_three_eq _ _ _ _
      _ ≤ _ := mask_sum_arith N _ εK κX _ _ _ _ (sum_massA_le Q A ρ hQ hρ hρ1 hs hN p) (hX p)
  calc uavg (fun t : FT ↦ if MassG S t then (runtimeR m0R).totalWeight
        LocalSig.Interp.instruments (portMass Q (Hh t) (Hk t) (Hk' t))
        (gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t))) ρ else 0)
      ≤ uavg (fun t : FT ↦ (if MassG S t then g (fullE t).1 (fullE t).2 else 0) +
          (N : ℝ≥0∞) * (if MassG S t then r t else 0)) := uavg_mono hle
    _ = uavg (fun t : FT ↦ if MassG S t then g (fullE t).1 (fullE t).2 else 0) +
          (N : ℝ≥0∞) * uavg (fun t : FT ↦ if MassG S t then r t else 0) := by
        rw [uavg_add, uavg_const_mul]
    _ ≤ N * ((Fintype.card Digest : ℝ≥0∞)⁻¹ + εK + κX) + N * μ :=
        add_le_add (uavg_mask_le_of_injOn_sph fullE (MassG S) (fullE_spec (SrcS S) A).1
          (le_card_mul_of_eq_inst _ _ _ _ _ _ card_coords) (fun t ↦ g (fullE t).1 (fullE t).2)
          g (fun _ _ ↦ le_rfl) _ hgsum) (mul_le_mul_of_nonneg_left hr zero_le)
    _ = N * ((2 ^ 128 : ℝ≥0∞)⁻¹ + εK + κX) + N * μ := by
        rw [card_digest_inv]

end generic

/-! ## The never-revealed part's cells and their multiplicities -/

section kk

/-! ### Counting over abstract types -/

/-- A middle factor cancelled by its inverse. -/
theorem inv_mul_cancel_mid (a b c : ℝ≥0∞) (hb0 : b ≠ 0) (hbt : b ≠ ⊤) :
    b⁻¹ * (a * b * c) = a * c := by
  rw [show a * b * c = b * (a * c) by ring, ← mul_assoc, ENNReal.inv_mul_cancel hb0 hbt, one_mul]

/-- The count of a fixed first seed, over abstract types. -/
theorem sum_ite_fst_eq {A B W : Type*} [Fintype A] [DecidableEq A] [Fintype B] [Fintype W]
    (a₀ : A) :
    ∑ k : (A × B) × W, (if k.1.1 = a₀ then (1 : ℝ≥0∞) else 0) =
      Fintype.card B * Fintype.card W := by
  have h : ∀ a : A, (∑ b : B, ∑ _w : W, if a = a₀ then (1 : ℝ≥0∞) else 0) =
      if a = a₀ then (Fintype.card B * Fintype.card W : ℝ≥0∞) else 0 := fun a ↦ by
    by_cases ha : a = a₀
    · simp only [ha, ↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    · simp only [ha, ↓reduceIte, Finset.sum_const_zero]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_congr rfl fun a _ ↦ h a]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- The count of a fixed second seed, over abstract types. -/
theorem sum_ite_snd_eq {A B W : Type*} [Fintype A] [Fintype B] [DecidableEq B] [Fintype W]
    (b₀ : B) :
    ∑ k : (A × B) × W, (if k.1.2 = b₀ then (1 : ℝ≥0∞) else 0) =
      Fintype.card A * Fintype.card W := by
  have h' : ∀ b : B, (∑ _w : W, if b = b₀ then (1 : ℝ≥0∞) else 0) =
      if b = b₀ then (Fintype.card W : ℝ≥0∞) else 0 := fun b ↦ by
    by_cases hb : b = b₀
    · simp only [hb, ↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    · simp only [hb, ↓reduceIte, Finset.sum_const_zero]
  have h : ∀ a : A, (∑ b : B, ∑ _w : W, if b = b₀ then (1 : ℝ≥0∞) else 0) =
      Fintype.card W := fun a ↦ by
    rw [Finset.sum_congr rfl fun b _ ↦ h' b]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_congr rfl fun a _ ↦ h a,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **A point naming the first seed**: when the sets `T k` holding `x` agree on `k.1.1`, the point
weighs at most `1 / |A|`. -/
theorem sum_indicator_key_fst_le {A B W α : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    [Fintype B] [Fintype W] (T : (A × B) × W → Set α) (x : α)
    (hT : ∀ k k', x ∈ T k → x ∈ T k' → k.1.1 = k'.1.1) :
    ∑ k, (T k).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤
      (Fintype.card A : ℝ≥0∞)⁻¹ * Fintype.card ((A × B) × W) := by
  by_cases h : ∃ k₀, x ∈ T k₀
  · obtain ⟨k₀, hk₀⟩ := h
    calc ∑ k, (T k).indicator (fun _ ↦ (1 : ℝ≥0∞)) x
        ≤ ∑ k : (A × B) × W, if k.1.1 = k₀.1.1 then (1 : ℝ≥0∞) else 0 :=
          Finset.sum_le_sum fun k _ ↦ by
            by_cases hk : x ∈ T k
            · rw [Set.indicator_of_mem hk]
              simp [hT k k₀ hk hk₀]
            · rw [Set.indicator_of_notMem hk]
              exact zero_le
      _ = Fintype.card B * Fintype.card W := sum_ite_fst_eq _
      _ = (Fintype.card A : ℝ≥0∞)⁻¹ * Fintype.card ((A × B) × W) := by
          rw [Fintype.card_prod, Fintype.card_prod, Nat.cast_mul, Nat.cast_mul, ← mul_assoc,
            ← mul_assoc, ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
              (ENNReal.natCast_ne_top _), one_mul]
  · rw [Finset.sum_eq_zero fun k _ ↦ Set.indicator_of_notMem (fun hk ↦ h ⟨k, hk⟩) _]
    exact zero_le

/-- **A point naming the second seed**: when the sets `T k` holding `x` agree on `k.1.2`, the point
weighs at most `1 / |B|`. -/
theorem sum_indicator_key_snd_le {A B W α : Type*} [Fintype A] [Fintype B] [Nonempty B]
    [DecidableEq B] [Fintype W] (T : (A × B) × W → Set α) (x : α)
    (hT : ∀ k k', x ∈ T k → x ∈ T k' → k.1.2 = k'.1.2) :
    ∑ k, (T k).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤
      (Fintype.card B : ℝ≥0∞)⁻¹ * Fintype.card ((A × B) × W) := by
  by_cases h : ∃ k₀, x ∈ T k₀
  · obtain ⟨k₀, hk₀⟩ := h
    calc ∑ k, (T k).indicator (fun _ ↦ (1 : ℝ≥0∞)) x
        ≤ ∑ k : (A × B) × W, if k.1.2 = k₀.1.2 then (1 : ℝ≥0∞) else 0 :=
          Finset.sum_le_sum fun k _ ↦ by
            by_cases hk : x ∈ T k
            · rw [Set.indicator_of_mem hk]
              simp [hT k k₀ hk hk₀]
            · rw [Set.indicator_of_notMem hk]
              exact zero_le
      _ = Fintype.card A * Fintype.card W := sum_ite_snd_eq _
      _ = (Fintype.card B : ℝ≥0∞)⁻¹ * Fintype.card ((A × B) × W) := by
          rw [Fintype.card_prod, Fintype.card_prod, Nat.cast_mul, Nat.cast_mul]
          exact (inv_mul_cancel_mid _ _ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
            (ENNReal.natCast_ne_top _)).symm
  · rw [Finset.sum_eq_zero fun k _ ↦ Set.indicator_of_notMem (fun hk ↦ h ⟨k, hk⟩) _]
    exact zero_le

/-- **A point covered by a few events**: when `x ∈ T k` only if one of the events `P M k` of a set
`Ms` holds, each of weight at most `ε`, the point weighs at most `|Ms| ε`. -/
theorem sum_indicator_le_finset {K J α : Type*} [Fintype K] (T : K → Set α) (x : α)
    (Ms : Finset J) (P : J → K → Prop) (hT : ∀ k, x ∈ T k → ∃ M ∈ Ms, P M k) (ε : ℝ≥0∞)
    (hP : ∀ M ∈ Ms, ∑ k, ({k | P M k} : Set K).indicator (fun _ ↦ (1 : ℝ≥0∞)) k ≤ ε) :
    ∑ k, (T k).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤ Ms.card * ε :=
  calc ∑ k, (T k).indicator (fun _ ↦ (1 : ℝ≥0∞)) x
      ≤ ∑ k, ∑ M ∈ Ms, ({k | P M k} : Set K).indicator (fun _ ↦ (1 : ℝ≥0∞)) k :=
        Finset.sum_le_sum fun k _ ↦ by
          by_cases hk : x ∈ T k
          · obtain ⟨M, hM, hP⟩ := hT k hk
            rw [Set.indicator_of_mem hk]
            refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun M ↦
              ({k | P M k} : Set K).indicator (fun _ ↦ (1 : ℝ≥0∞)) k) (fun _ _ ↦ zero_le) hM)
            rw [Set.indicator_of_mem (show k ∈ {k | P M k} from hP)]
          · rw [Set.indicator_of_notMem hk]
            exact zero_le
    _ = ∑ M ∈ Ms, ∑ k, ({k | P M k} : Set K).indicator (fun _ ↦ (1 : ℝ≥0∞)) k :=
        Finset.sum_comm
    _ ≤ ∑ _M ∈ Ms, ε := Finset.sum_le_sum hP
    _ = Ms.card * ε := by rw [Finset.sum_const, nsmul_eq_mul]

/-- A sum moved along a bijection, with the count of the domain. -/
theorem sum_equiv_le {K K' : Type*} [Fintype K] [Fintype K'] (e : K ≃ K') (f : K → ℝ≥0∞)
    (c : ℝ≥0∞) (h : ∑ y, f (e.symm y) ≤ c * Fintype.card K') :
    ∑ k, f k ≤ c * Fintype.card K := by
  rw [Fintype.card_congr e, ← Equiv.sum_comp e.symm]
  exact h

/-- **A sum against a count, across `Fintype` instances** (over an abstract type: comparing the
concrete instances of the never-revealed part unfolds them). -/
theorem sum_inst_le {K : Type*} (i i' : Fintype K) (f : K → ℝ≥0∞) (c : ℝ≥0∞)
    (h : @Finset.sum _ _ _ (@Finset.univ K i') f ≤ c * @Fintype.card K i') :
    @Finset.sum _ _ _ (@Finset.univ K i) f ≤ c * @Fintype.card K i := by
  rw [Subsingleton.elim i i']
  exact h

/-! ### The coordinates of the randomizer coins -/

/-- The never-revealed part beside `(SK.seed, SK.prf)`, SeedStage's slots and the randomizer coins'
`k`- and `k'`-parts. -/
abbrev KR : Type :=
  (Message → Fin 960 → ZMod 2) × (DLab → Z) × (DLab → Z) × (DLab → Fin 832 → ZMod 2)

/-- The never-revealed part with the randomizer coins last (gCap's coordinates). -/
abbrev KKR : Type := Secret × (SeedKS × KR) × (Message → Z) × (Message → Z)

/-- **The never-revealed part, the randomizer coins last.** -/
def kkE : KK ≃ KKR where
  toFun k := (k.1, (k.2.1, k.2.2.2.2), k.2.2.1, k.2.2.2.1)
  invFun y := (y.1, y.2.1.1, y.2.2.1, y.2.2.2, y.2.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The randomizer capacity at the coordinates is gCap's. -/
theorem rCapKK_kkE (p : PP) (y : KKR) (M : Message) :
    rCapKK p (kkE.symm y) M = gCap (pubP p).perm (fun M s ↦ rCell M (pubP p).seed s.2) y M :=
  rfl

/-! ### The cells -/

/-- The `SK.seed`-keyed derivations' `k`-cells at the never-revealed part. -/
def seedKK (p : PP) (k : KK) : Set X :=
  Set.range (skCell (pubP p).seed k.1.1)

/-- The `PRF_msg` calls' `h`-cells at the never-revealed part. -/
def prfKKH (p : PP) (k : KK) : Set Z :=
  Set.range (rCapKK p k)

/-- The `PRF_msg` calls' `k`-cells at the never-revealed part. -/
def prfKKK (p : PP) (k : KK) : Set X :=
  Set.range (rcK p k)

/-- The `PRF_msg` calls' `k'`-cells at the never-revealed part, on a good permutation. -/
def prfKKK' (p : PP) (k : KK) : Set X :=
  {x | PermGood (pubP p).perm 18 ∧ ∃ M, rRateK p k M = x}

/-- **The never-revealed part's `h`-cells.** -/
def kkH (p : PP) (w : ((s : HPos) → XD s) × KK) : Set Z :=
  seedHK p w.2 ∪ prfKKH p w.2 ∪ rbCellsH p w

/-- **The never-revealed part's `k`-cells.** -/
def kkK (p : PP) (w : ((s : HPos) → XD s) × KK) : Set X :=
  seedKK p w.2 ∪ prfKKK p w.2 ∪ rbCellsK p w

/-- **The never-revealed part's `k'`-cells.** -/
def kkK' (p : PP) (w : ((s : HPos) → XD s) × KK) : Set X :=
  seedK'K p w.2 ∪ prfKKK' p w.2 ∪ rbCellsK' p w

/-- **The multiplicity of the never-revealed part's cells**: `seedEps 18` for SeedStage's slots,
`|MasterSeed|⁻¹` and `|HashOutput|⁻¹` for the `SK.seed`- and `SK.prf`-keyed blocks, and
`24 |Message| / |Z|` for the randomizer coins (`18` per rate on a `PermGood π 18`, `1` per
capacity) and the non-first messages (`1` per block or rate, `5` per capacity). -/
noncomputable def kkEps : ℝ≥0∞ :=
  seedEps 18 + (Fintype.card MasterSeed : ℝ≥0∞)⁻¹ + (Fintype.card HashOutput : ℝ≥0∞)⁻¹ +
    24 * ((Fintype.card Message : ℝ≥0∞) / Fintype.card Z)

/-! ### The multiplicities -/

/-- A point's indicator below another's when membership implies membership. -/
theorem indicator_le_of_imp {α β : Type*} (s : Set α) (t : Set β) (a : α) (b : β)
    (h : a ∈ s → b ∈ t) :
    s.indicator (fun _ ↦ (1 : ℝ≥0∞)) a ≤ t.indicator (fun _ ↦ (1 : ℝ≥0∞)) b := by
  by_cases ha : a ∈ s
  · rw [Set.indicator_of_mem ha, Set.indicator_of_mem (h ha)]
  · rw [Set.indicator_of_notMem ha]
    exact zero_le

/-- **A message is non-first** for at most `|Message| / |Z|` of the never-revealed part. -/
theorem sum_indicator_rBK_le (p : PP) (M : Message) :
    ∑ k, ({k | M ∈ rBK p k} : Set KK).indicator (fun _ ↦ (1 : ℝ≥0∞)) k ≤
      (Fintype.card Message : ℝ≥0∞) / Fintype.card Z * Fintype.card KK := by
  have h0 := sum_indicator_notFirst_le (S := Secret) (S₀ := SeedKS × KR) (pubP p).perm
    (fun M s ↦ rCell M (pubP p).seed s.2) rOrd M
  refine sum_equiv_le kkE (fun k ↦ ({k | M ∈ rBK p k} : Set KK).indicator (fun _ ↦ 1) k) _
    (sum_inst_le _ _ _ _ (le_trans ?_ h0))
  refine Finset.sum_le_sum fun y _ ↦ indicator_le_of_imp _ _ _ _ ?_
  rintro ⟨b, hb, he⟩
  exact ⟨b, hb, (rCapKK_kkE p y b).symm.trans (he.trans (rCapKK_kkE p y M))⟩

/-- **The `SK.seed`-keyed blocks** name the seed. -/
theorem sum_indicator_seedKK_le (p : PP) (x : X) :
    ∑ k, (seedKK p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤
      (Fintype.card MasterSeed : ℝ≥0∞)⁻¹ * Fintype.card KK :=
  sum_inst_le _ _ _ _ (sum_indicator_key_fst_le (fun k : KK ↦ seedKK p k) x
    fun k k' ⟨b, hb⟩ ⟨b', hb'⟩ ↦ (Prod.mk.inj
      (skCell_injective (pubP p).seed (a₁ := (k.1.1, b)) (a₂ := (k'.1.1, b'))
        (hb.trans hb'.symm))).1)

/-- **The `PRF_msg` blocks** name `SK.prf`. -/
theorem sum_indicator_prfKKK_le (p : PP) (x : X) :
    ∑ k, (prfKKK p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ * Fintype.card KK :=
  sum_inst_le _ _ _ _ (sum_indicator_key_snd_le (fun k : KK ↦ prfKKK p k) x
    fun k k' ⟨M, hM⟩ ⟨M', hM'⟩ ↦ (Prod.mk.inj
      (rCell_injective (pubP p).seed (a₁ := (k.1.2, M)) (a₂ := (k'.1.2, M'))
        (hM.trans hM'.symm))).1)

/-- **The `PRF_msg` rates**: on a `PermGood π 18`, a rate is a message's for at most
`18 |Message| / |Z|` of the never-revealed part (its `k`-coin is uniform). -/
theorem sum_indicator_prfKKK'_le (p : PP) (x : X) :
    ∑ k, (prfKKK' p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤
      18 * ((Fintype.card Message : ℝ≥0∞) / Fintype.card Z) * Fintype.card KK := by
  have h : ∑ y : KKR, (prfKKK' p (kkE.symm y)).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤
      18 * ((Fintype.card Message : ℝ≥0∞) / Fintype.card Z) * Fintype.card KKR := by
    by_cases hG : PermGood (pubP p).perm 18
    · refine (le_div_mul_of_mul_le (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _) (card_mul_sum_slot_le (fun y : KKR ↦ prfKKK' p (kkE.symm y))
          x (fun M s ↦ {w | ((pubP p).perm (rCell M (pubP p).seed s.2, w)).1 = x}) 18
          (fun _ hk ↦ hk.2) fun M s ↦ ?_)).trans_eq ?_
      · rw [← card_filter_eq_sum_indicator]
        exact_mod_cast hG.rate _ x
      · rw [mul_comm (Fintype.card Message : ℝ≥0∞), mul_div_assoc]
    · exact le_of_eq_of_le (Finset.sum_eq_zero fun y _ ↦ Set.indicator_of_notMem
        (fun h ↦ hG h.1) _) zero_le
  exact sum_equiv_le kkE _ _ h

/-- **The `PRF_msg` capacities**: a capacity is a message's for at most `|Message| / |Z|` of the
never-revealed part (its `k'`-coin is uniform). -/
theorem sum_indicator_prfKKH_le (p : PP) (z : Z) :
    ∑ k, (prfKKH p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤
      (Fintype.card Message : ℝ≥0∞) / Fintype.card Z * Fintype.card KK := by
  have h0 := sum_indicator_range_gCap_le (S := Secret) (S₀ := SeedKS × KR) (pubP p).perm
    (fun M s ↦ rCell M (pubP p).seed s.2) z
  refine sum_equiv_le kkE (fun k ↦ (prfKKH p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) z) _
    (sum_inst_le _ _ _ _ (le_trans ?_ h0))
  refine Finset.sum_le_sum fun y _ ↦ indicator_le_of_imp _ _ _ _ ?_
  rintro ⟨M, rfl⟩
  exact ⟨M, (rCapKK_kkE p y M).symm⟩

open scoped Classical in
/-- The message whose `H_msg` cell `x` is, if any. -/
noncomputable def cellMsgs {α : Type} (c : Randomizer × DLab → α) (x : α) : Finset Message :=
  @dite _ (∃ q, c q = x) (Classical.propDecidable _) (fun h ↦ {h.choose.2.1}) fun _ ↦ ∅

theorem card_cellMsgs_le {α : Type} (c : Randomizer × DLab → α) (x : α) :
    (cellMsgs c x).card ≤ 1 := by
  unfold cellMsgs
  split
  · exact (Finset.card_singleton _).le
  · exact Finset.card_empty.le.trans zero_le_one

theorem mem_cellMsgs {α : Type} {c : Randomizer × DLab → α} (hc : Function.Injective c) {x : α}
    {q : Randomizer × DLab} (hq : c q = x) : q.2.1 ∈ cellMsgs c x := by
  have h : ∃ q, c q = x := ⟨q, hq⟩
  unfold cellMsgs
  rw [dite_eq_left_of_eq_true (eq_true h), Finset.mem_singleton,
    hc (h.choose_spec.trans hq.symm)]

/-- **The non-first messages' `H_msg` blocks**: a block names its message. -/
theorem sum_indicator_rbCellsK_le (p : PP) (v : (s : HPos) → XD s) (x : X) :
    ∑ k, (rbCellsK p (v, k)).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤
      (Fintype.card Message : ℝ≥0∞) / Fintype.card Z * Fintype.card KK := by
  refine (sum_indicator_le_finset (fun k ↦ rbCellsK p (v, k)) x
    (cellMsgs (fun q ↦ hmCellK (pubP p) (rootV v) q.1 q.2) x) (fun M k ↦ M ∈ rBK p k)
    (fun k ⟨_, M, hM, i, R, he⟩ ↦ ⟨M, mem_cellMsgs (q := (R, (M, i)))
      (dLabCell_injective (pubP p).seed (rootV v)) he, hM⟩) _
    fun M _ ↦ sum_indicator_rBK_le p M).trans ?_
  calc ((cellMsgs (fun q ↦ hmCellK (pubP p) (rootV v) q.1 q.2) x).card : ℝ≥0∞) *
        ((Fintype.card Message : ℝ≥0∞) / Fintype.card Z * Fintype.card KK)
      ≤ 1 * ((Fintype.card Message : ℝ≥0∞) / Fintype.card Z * Fintype.card KK) := by
        gcongr
        exact_mod_cast card_cellMsgs_le _ x
    _ = _ := one_mul _

/-- **The non-first messages' `H_msg` rates**: on the static condition, a rate names its input. -/
theorem sum_indicator_rbCellsK'_le (p : PP) (v : (s : HPos) → XD s) (x : X) :
    ∑ k, (rbCellsK' p (v, k)).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤
      (Fintype.card Message : ℝ≥0∞) / Fintype.card Z * Fintype.card KK := by
  by_cases hS : HStatic (pubP p) (rootV v)
  · refine (sum_indicator_le_finset (fun k ↦ rbCellsK' p (v, k)) x
      (cellMsgs (fun q ↦ hmCellR (pubP p) (rootV v) q.1 q.2) x) (fun M k ↦ M ∈ rBK p k)
      (fun k ⟨_, M, hM, i, R, he⟩ ↦ ⟨M, mem_cellMsgs (q := (R, (M, i))) hS.1 he, hM⟩) _
      fun M _ ↦ sum_indicator_rBK_le p M).trans ?_
    calc ((cellMsgs (fun q ↦ hmCellR (pubP p) (rootV v) q.1 q.2) x).card : ℝ≥0∞) *
          ((Fintype.card Message : ℝ≥0∞) / Fintype.card Z * Fintype.card KK)
        ≤ 1 * ((Fintype.card Message : ℝ≥0∞) / Fintype.card Z * Fintype.card KK) := by
          gcongr
          exact_mod_cast card_cellMsgs_le _ x
      _ = _ := one_mul _
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun k _ ↦ Set.indicator_of_notMem
      (fun h ↦ hS h.1) _) zero_le

/-- **The non-first messages' `H_msg` capacities**: on the static condition, a capacity is at most
five inputs'. -/
theorem sum_indicator_rbCellsH_le (p : PP) (v : (s : HPos) → XD s) (z : Z) :
    ∑ k, (rbCellsH p (v, k)).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤
      5 * ((Fintype.card Message : ℝ≥0∞) / Fintype.card Z) * Fintype.card KK := by
  by_cases hS : HStatic (pubP p) (rootV v)
  · classical
    obtain ⟨T, hT, hmem⟩ := hS.2 z
    refine (sum_indicator_le_finset (fun k ↦ rbCellsH p (v, k)) z (T.image fun q ↦ q.2.1)
      (fun M k ↦ M ∈ rBK p k)
      (fun k ⟨_, M, hM, i, R, he⟩ ↦ ⟨M, Finset.mem_image.mpr ⟨(R, (M, i)), hmem R _ he, rfl⟩, hM⟩)
      _ fun M _ ↦ sum_indicator_rBK_le p M).trans ?_
    rw [mul_assoc]
    gcongr
    exact_mod_cast Finset.card_image_le.trans hT
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun k _ ↦ Set.indicator_of_notMem
      (fun h ↦ hS h.1) _) zero_le

/-- Three indicator sums against a common factor. -/
theorem sum_indicator_union3_le {K α : Type*} [Fintype K] (S T U : K → Set α) (a : α)
    (C x y w : ℝ≥0∞) (hS : ∑ k, (S k).indicator (fun _ ↦ (1 : ℝ≥0∞)) a ≤ x * C)
    (hT : ∑ k, (T k).indicator (fun _ ↦ (1 : ℝ≥0∞)) a ≤ y * C)
    (hU : ∑ k, (U k).indicator (fun _ ↦ (1 : ℝ≥0∞)) a ≤ w * C) :
    ∑ k, (S k ∪ T k ∪ U k).indicator (fun _ ↦ (1 : ℝ≥0∞)) a ≤ (x + y + w) * C :=
  ((sum_indicator_union_le _ _ a).trans (add_le_add (sum_indicator_union_le _ _ a) le_rfl)).trans
    ((add_le_add (add_le_add hS hT) hU).trans_eq (by rw [add_mul, add_mul]))

theorem arith_kkH (s a b m : ℝ≥0∞) : s + m + 5 * m ≤ s + a + b + 24 * m := by
  calc s + m + 5 * m = s + 6 * m := by ring
    _ ≤ s + a + b + 24 * m := add_le_add (le_self_add.trans le_self_add)
        (mul_le_mul_of_nonneg_right (by norm_num) zero_le)

theorem arith_kkK (s a b m : ℝ≥0∞) : a + b + 1 * m ≤ s + a + b + 24 * m := by
  rw [add_assoc s a b]
  exact add_le_add le_add_self (mul_le_mul_of_nonneg_right (by norm_num) zero_le)

theorem arith_kkK' (s a b m : ℝ≥0∞) : s + 18 * m + m ≤ s + a + b + 24 * m := by
  calc s + 18 * m + m = s + 19 * m := by ring
    _ ≤ s + a + b + 24 * m := add_le_add (le_self_add.trans le_self_add)
        (mul_le_mul_of_nonneg_right (by norm_num) zero_le)

/-- **The never-revealed part's `h`-cells** weigh at most `kkEps`. -/
theorem sum_indicator_kkH_le (p : PP) (v : (s : HPos) → XD s) (z : Z) :
    ∑ k, (kkH p (v, k)).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤ kkEps * Fintype.card KK :=
  (sum_indicator_union3_le (fun k ↦ seedHK p k) (fun k ↦ prfKKH p k) (fun k ↦ rbCellsH p (v, k))
    z _ _ _ _ (sum_inst_le _ _ _ _ (sum_indicator_seedHK_le p z)) (sum_indicator_prfKKH_le p z)
    (sum_indicator_rbCellsH_le p v z)).trans
    (mul_le_mul_of_nonneg_right (arith_kkH _ _ _ _) zero_le)

/-- **The never-revealed part's `k`-cells** weigh at most `kkEps`. -/
theorem sum_indicator_kkK_le (p : PP) (v : (s : HPos) → XD s) (x : X) :
    ∑ k, (kkK p (v, k)).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤ kkEps * Fintype.card KK :=
  (sum_indicator_union3_le (fun k ↦ seedKK p k) (fun k ↦ prfKKK p k) (fun k ↦ rbCellsK p (v, k))
    x _ _ _ _ (sum_indicator_seedKK_le p x) (sum_indicator_prfKKK_le p x)
    ((sum_indicator_rbCellsK_le p v x).trans_eq (by rw [one_mul]))).trans
    (mul_le_mul_of_nonneg_right (arith_kkK _ _ _ _) zero_le)

/-- **The never-revealed part's `k'`-cells** weigh at most `kkEps`. -/
theorem sum_indicator_kkK'_le (p : PP) (v : (s : HPos) → XD s) (x : X) :
    ∑ k, (kkK' p (v, k)).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤ kkEps * Fintype.card KK :=
  (sum_indicator_union3_le (fun k ↦ seedK'K p k) (fun k ↦ prfKKK' p k)
    (fun k ↦ rbCellsK' p (v, k)) x _ _ _ _ (sum_inst_le _ _ _ _ (sum_indicator_seedK'K_le p x))
    (sum_indicator_prfKKK'_le p x) (sum_indicator_rbCellsK'_le p v x)).trans
    (mul_le_mul_of_nonneg_right (arith_kkK' _ _ _ _) zero_le)

end kk

/-! ## `hsub`: the full table's hidden sets on the good set -/

section hsub

theorem fullE_seedKS (t : FT) : (fullE t).2.2.2.1 = (phiE t).2.2.2.2.2.1 := by
  obtain ⟨h₃, hc₃, e⟩ := dLast_eq (yOf t)
  show (psiE (dLast (yOf t))).2.2.2.1 = _
  rw [e]
  rfl

theorem fullE_secret (t : FT) :
    (fullE t).2.2.1 = ((tabOf t).secretSeed, (tabOf t).prfKey) := by
  rw [(fullE_kk t).1, (phiE_rest t).2]
  exact dFull_secret

variable {S : PP → ((s : HPos) → XD s) → Prop} {t : FT}

/-- **The full table's hidden sets on the good set**, with the static condition at the
reparametrized data: in the template's (`hidH`), the never-revealed part's (`kkH`) and the
template's `H_msg` cells at the hidden randomizers (`tmCellsH`). -/
theorem fullCov_subset (ht : MassG S t) (hS : HStatic (pubP (fullE t).1) (rootV (fullE t).2.1)) :
    fullCovH (tabOf t) ⊆ hidH (pubP (fullE t).1) (fullE t).2.1 ∪ kkH (fullE t).1 (fullE t).2 ∪
        tmCellsH (fullE t).1 (fullE t).2.1 ∧
      fullCovK (tabOf t) ⊆ hidK (pubP (fullE t).1) (fullE t).2.1 ∪ kkK (fullE t).1 (fullE t).2 ∪
        tmCellsK (fullE t).1 (fullE t).2.1 ∧
      fullCovK' (tabOf t) ⊆ hidK' (pubP (fullE t).1) (fullE t).2.1 ∪
        kkK' (fullE t).1 (fullE t).2 ∪ tmCellsK' (fullE t).1 (fullE t).2.1 := by
  have hc := ht.1
  have hst := hc.1.1
  obtain ⟨p1, p2, p3⟩ := tabPaths_subset_hid ht
  have hsec := fullE_secret t
  have hS₀ : (fullE t).2.2.1.1 = (tabOf t).secretSeed := by rw [hsec]
  have hsk := fullE_seedKS t
  have hπ := pubP_perm (t := t)
  have hP := pubP_seed hst
  have hG : PermGood (pubP (fullE t).1).perm 18 := by
    rw [hπ]
    exact hc.2.1
  refine ⟨?_, ?_, ?_⟩
  · rintro z (((hz | ⟨b, rfl⟩) | ⟨M, rfl⟩) | ⟨M, i, rfl⟩)
    · exact Or.inl (Or.inl (p1 hz))
    · refine Or.inl (Or.inr (Or.inl (Or.inl ⟨b, ?_⟩)))
      obtain ⟨s1, s2⟩ := seedSlots_table hst b
      show capOf (fun _ ↦ ((fullE t).2.2.2.1).1 b) (fun _ ↦ ((fullE t).2.2.2.1).2 b)
        (pubP (fullE t).1).perm (skCell (pubP (fullE t).1).seed (fullE t).2.2.1.1 b) = _
      rw [hsk, s1, s2, hπ, hP, hS₀]
      rfl
    · exact Or.inl (Or.inr (Or.inl (Or.inr ⟨M, ((rCells_fullE hc M).2.2).symm⟩)))
    · rcases (hmCells_subset hc hS M i).1 with h | h
      · exact Or.inr h
      · exact Or.inl (Or.inr (Or.inr h))
  · rintro x (((hx | ⟨b, rfl⟩) | ⟨M, rfl⟩) | ⟨M, i, rfl⟩)
    · exact Or.inl (Or.inl (p2 hx))
    · refine Or.inl (Or.inr (Or.inl (Or.inl ⟨b, ?_⟩)))
      show skCell (pubP (fullE t).1).seed (fullE t).2.2.1.1 b = _
      rw [hP, hS₀]
    · exact Or.inl (Or.inr (Or.inl (Or.inr ⟨M, ((rCells_fullE hc M).1).symm⟩)))
    · rcases (hmCells_subset hc hS M i).2.1 with h | h
      · exact Or.inr h
      · exact Or.inl (Or.inr (Or.inr h))
  · rintro x (((hx | ⟨b, rfl⟩) | ⟨M, rfl⟩) | ⟨M, i, rfl⟩)
    · exact Or.inl (Or.inl (p3 hx))
    · refine Or.inl (Or.inr (Or.inl (Or.inl ⟨hG, b, ?_⟩)))
      obtain ⟨s1, -⟩ := seedSlots_table hst b
      show ((pubP (fullE t).1).perm (skCell (pubP (fullE t).1).seed (fullE t).2.2.1.1 b,
        ((fullE t).2.2.2.1).1 b)).1 = _
      rw [hsk, s1, hπ, hP, hS₀]
      rfl
    · exact Or.inl (Or.inr (Or.inl (Or.inr ⟨hG, M, ((rCells_fullE hc M).2.1).symm⟩)))
    · rcases (hmCells_subset hc hS M i).2.2 with h | h
      · exact Or.inr h
      · exact Or.inl (Or.inr (Or.inr h))

end hsub

/-! ## The masked sponge mass -/

section sponge

variable (A : SAdversary) {q : ℕ}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- The sponge ports' charge as a port-set charge. -/
theorem advCalls_gameR_Q (p : Pub) (v : (s : HPos) → XD s) :
    IFreeM.IsChargeBound (gameR msgPol A p v)
      (portCharge fun i ↦
        if extCls X Z (Mem HPos) (recSpec HPos Selections) i = false then 1 else 0) (6 * q) := by
  have hc : (fun i ↦ if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 0 else 1) =
      fun i ↦ if extCls X Z (Mem HPos) (recSpec HPos Selections) i = false then 1 else 0 :=
    funext fun i ↦ by cases extCls X Z (Mem HPos) (recSpec HPos Selections) i <;> rfl
  rw [← hc]
  exact advCalls_gameR hperm hsign msgPol p v

open scoped Classical in
/-- **The masked sponge mass of runtime 1's full table** (`hS` of the masked hybrid, with the mask
`MassG S = FullG (SrcS S)`): at most `6q (2^-128 + kkEps + κX) + 6q chgRevAvg`, where the static
condition `S` implies HmsgCovers' `HStatic` and `κX` is the per-call weight of the template's
`H_msg` cells at the hidden randomizers (`hX`). -/
theorem uavg_mask_spongeMass_le_sph (S : PP → ((s : HPos) → XD s) → Prop)
    (hSt : ∀ p v, S p v → HStatic (pubP p) (rootV v)) (κX : ℝ≥0∞)
    (hX : ∀ p, ∑ v, (runtimeR m0R).totalWeight LocalSig.Interp.instruments
      (spongeMass (tmCellsH p v) (tmCellsK p v) (tmCellsK' p v)) (gameR msgPol A (pubP p) v)
        initR ≤ ((6 * q : ℕ) : ℝ≥0∞) * κX * Fintype.card ((s : HPos) → XD s)) :
    uavg (fun t : FT ↦ if MassG S t then (runtimeR m0R).totalWeight LocalSig.Interp.instruments
      (spongeMass (fullCovH (tabOf t)) (fullCovK (tabOf t)) (fullCovK' (tabOf t)))
        (gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t))) initR else 0) ≤
      ((6 * q : ℕ) : ℝ≥0∞) * ((2 ^ 128 : ℝ≥0∞)⁻¹ + kkEps + κX) +
        ((6 * q : ℕ) : ℝ≥0∞) * chgRevAvg A initR S :=
  uavg_mask_portMass_le_sph (fun i ↦ extCls X Z (Mem HPos) (recSpec HPos Selections) i = false)
    A initR (fun _ h ↦ Bool.noConfusion h) initR_posSemidef ofReal_trace_initR_le_one
    (Quantum.Xmss.Hybrid.querySupportedOn_initR m0R _) S
    (fun t ↦ fullCovH (tabOf t)) (fun t ↦ fullCovK (tabOf t)) (fun t ↦ fullCovK' (tabOf t))
    kkH kkK kkK' tmCellsH tmCellsK tmCellsK'
    (fun _ ht ↦ fullCov_subset ht (hSt _ _ ht.2.2.2)) kkEps sum_indicator_kkH_le
    sum_indicator_kkK_le sum_indicator_kkK'_le (advCalls_gameR_Q A hperm hsign) κX hX
    (chgRev A initR) (fun t ht _ _ _ ↦ mass_le_chgRev _ A initR initR_posSemidef
      (Quantum.Xmss.Hybrid.querySupportedOn_initR m0R _) S (advCalls_gameR_Q A hperm hsign) t ht
      _ _ _) _ le_rfl

end sponge

/-! ## The masked read mass -/

section read

/-- The template's hidden rates lie in TrialHit's `k'`-cells (`2^50 + 2^257` of them). -/
theorem hidK'_subset_k'CellsP (pub : Pub) (v : (s : HPos) → XD s) :
    ∀ y ∈ hidK' pub v, y ∈ k'CellsP pub v := by
  rintro _ ⟨-, s, hs, j, hj, rfl⟩
  have hm := mem_k'CellsP_slot pub v (slotOutPos s, ⟨j, hj.trans_le (nBlk_le _ _)⟩)
  rw [outSlot_slotOutPos hs] at hm
  exact hm

/-- The template's hidden capacities lie in TrialHit's `h`-cells (`2^50 + 2^257` of them). -/
theorem hidH_subset_hCellsP (pub : Pub) (v : (s : HPos) → XD s) :
    ∀ z ∈ hidH pub v, z ∈ hCellsP pub v := by
  rintro _ ⟨-, s, hs, j, hj, rfl⟩
  have hm := mem_hCellsP_slot pub v (slotOutPos s, ⟨j, hj.trans_le (nBlk_le _ _)⟩)
  rw [outSlot_slotOutPos hs] at hm
  exact hm

set_option exponentiation.threshold 1024 in
theorem card_cells_le_trialCellCap {n : ℕ} (h : n ≤ 2 ^ 50 + 2 ^ 257) : n ≤ trialCellCap :=
  h.trans (by unfold trialCellCap; norm_num)

variable (A : SAdversary) {q : ℕ}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

open scoped Classical in
/-- **The masked read mass of runtime 1's full table** (`hRd` of the masked hybrid, with the mask
`MassG S = FullG (SrcS S)`): at most `trialTau (2 clsCap) + 2^-128 · 3 verifyBlocks +
clsCap (kkEps + κX) + clsCap chgRevAvg`, where the static condition `S` implies HmsgCovers'
`HStatic` and TrialsOff's event's complement, and `κX` is the per-call read weight of the
template's `H_msg` cells at the hidden randomizers (`hX`). -/
theorem uavg_mask_readMass_le_sph (S : PP → ((s : HPos) → XD s) → Prop)
    (hSt : ∀ p v, S p v → HStatic (pubP p) (rootV v))
    (hOff : ∀ p v, S p v → TrialsOff (pubP p).xw (pubP p).keys.1 (valsOf v)) (κX : ℝ≥0∞)
    (hX : ∀ p, ∑ v, (runtimeR m0R).totalWeight LocalSig.Interp.instruments
      (readMass (tmCellsH p v) (tmCellsK p v) (tmCellsK' p v)) (gameR msgPol A (pubP p) v)
        initR ≤ clsCap * κX * Fintype.card ((s : HPos) → XD s)) :
    uavg (fun t : FT ↦ if MassG S t then (runtimeR m0R).totalWeight LocalSig.Interp.instruments
      (readMass (fullCovH (tabOf t)) (fullCovK (tabOf t)) (fullCovK' (tabOf t)))
        (gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t))) initR else 0) ≤
      trialTau (2 * clsCap) + (2 ^ 128 : ℝ≥0∞)⁻¹ * ((3 * verifyBlocks : ℕ) : ℝ≥0∞) +
        clsCap * kkEps + clsCap * κX + clsCap * chgRevAvg A initR S := by
  have h := uavg_mask_readMass_le_sph_good A hperm hsign S initR initR_posSemidef
    ofReal_trace_initR_le_one (Quantum.Xmss.Hybrid.querySupportedOn_initR m0R _)
    (fun t ↦ fullCovH (tabOf t)) (fun t ↦ fullCovK (tabOf t)) (fun t ↦ fullCovK' (tabOf t))
    (fun p ↦ hidH (pubP p)) (fun p ↦ hidK (pubP p)) (fun p ↦ hidK' (pubP p)) _
    (fun p ↦ sourcesSlotInv Selections (pubP p)) kkH kkK kkK' tmCellsH tmCellsK tmCellsK'
    (fun _ ht ↦ fullCov_subset ht (hSt _ _ ht.2.2.2)) kkEps sum_indicator_kkH_le
    sum_indicator_kkK_le sum_indicator_kkK'_le κX hX
    (fun p v ↦ TrialHidGood (pubP p) (hidK (pubP p) v))
    (fun t ht ↦ trialHidGood_of_trialsOff (by rw [pubP_perm]; exact ht.1.2.1)
      (hOff _ _ ht.2.2.2) fun x ⟨_, s, hs, j, hj, e⟩ ↦ ⟨s, hs, j, hj, e⟩)
    (trialTau (2 * clsCap)) fun p ↦ sum_trialMass_le_clsCap cwUpd msgPol A hperm hsign
      valFree_msgPol m0R (pubP p) initR initR_posSemidef ofReal_trace_initR_le_one
      (Quantum.Xmss.Hybrid.querySupportedOn_initR m0R _)
      (Quantum.Xmss.Assembly.noBot_init m0R (SubState.basis ()).matrix)
      (hidH (pubP p)) (hidK (pubP p)) (hidK' (pubP p)) _ card_digest_inv.le
      (sourcesSlotInv Selections (pubP p))
      (fun v ↦ ⟨k'CellsP (pubP p) v, hidK'_subset_k'CellsP _ v,
        card_cells_le_trialCellCap (card_k'CellsP_le _ v)⟩)
      (fun v ↦ ⟨hCellsP (pubP p) v, hidH_subset_hCellsP _ v,
        card_cells_le_trialCellCap (card_hCellsP_le _ v)⟩)
  rwa [card_digest_inv] at h

end read

/-! ## The masked hybrid's hypotheses (`Quantum.Sphincs.Hybrid.Masked`) -/

section hybrid

/-- **`hcov`**: runtime 1's full table is covered by the hidden sets `fullCovH`. -/
theorem hcov_sph (t : FT) :
    Quantum.Xmss.Hybrid.Covers (fullHw (tabOf t)) (fullCovH (tabOf t)) (fullCovK (tabOf t))
      (fullCovK' (tabOf t)) :=
  covers_fullHw (tabOf t)

variable (A : SAdversary) {q : ℕ}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

open scoped Classical in
/-- **`hS`** of the masked hybrid at the good set `FullG (SrcS S)`:
`κ = 2^-128 + kkEps + κX + chgRevAvg`. -/
theorem hS_sph (S : PP → ((s : HPos) → XD s) → Prop)
    (hSt : ∀ p v, S p v → HStatic (pubP p) (rootV v)) (κX : ℝ≥0∞)
    (hX : ∀ p, ∑ v, (runtimeR m0R).totalWeight LocalSig.Interp.instruments
      (spongeMass (tmCellsH p v) (tmCellsK p v) (tmCellsK' p v)) (gameR msgPol A (pubP p) v)
        initR ≤ ((6 * q : ℕ) : ℝ≥0∞) * κX * Fintype.card ((s : HPos) → XD s)) :
    uavg (fun t : FT ↦ if FullG (SrcS S) t then (runtimeR m0R).totalWeight
      LocalSig.Interp.instruments
      (spongeMass (fullCovH (tabOf t)) (fullCovK (tabOf t)) (fullCovK' (tabOf t)))
        (gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t))) initR else 0) ≤
      ((6 * q : ℕ) : ℝ≥0∞) * ((2 ^ 128 : ℝ≥0∞)⁻¹ + kkEps + κX + chgRevAvg A initR S) :=
  (uavg_mask_spongeMass_le_sph A hperm hsign S hSt κX hX).trans_eq (mul_add _ _ _).symm

open scoped Classical in
/-- **`hRd`** of the masked hybrid at the good set `FullG (SrcS S)`:
`ν = trialTau (2 clsCap) + 2^-128 · 3 verifyBlocks + clsCap (kkEps + κX) + clsCap chgRevAvg`. -/
theorem hRd_sph (S : PP → ((s : HPos) → XD s) → Prop)
    (hSt : ∀ p v, S p v → HStatic (pubP p) (rootV v))
    (hOff : ∀ p v, S p v → TrialsOff (pubP p).xw (pubP p).keys.1 (valsOf v)) (κX : ℝ≥0∞)
    (hX : ∀ p, ∑ v, (runtimeR m0R).totalWeight LocalSig.Interp.instruments
      (readMass (tmCellsH p v) (tmCellsK p v) (tmCellsK' p v)) (gameR msgPol A (pubP p) v)
        initR ≤ clsCap * κX * Fintype.card ((s : HPos) → XD s)) :
    uavg (fun t : FT ↦ if FullG (SrcS S) t then (runtimeR m0R).totalWeight
      LocalSig.Interp.instruments
      (readMass (fullCovH (tabOf t)) (fullCovK (tabOf t)) (fullCovK' (tabOf t)))
        (gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t))) initR else 0) ≤
      trialTau (2 * clsCap) + (2 ^ 128 : ℝ≥0∞)⁻¹ * ((3 * verifyBlocks : ℕ) : ℝ≥0∞) +
        clsCap * kkEps + clsCap * κX + clsCap * chgRevAvg A initR S :=
  uavg_mask_readMass_le_sph A hperm hsign S hSt hOff κX hX

end hybrid

end Quantum.Sphincs.Assembly

end
