module

public import Quantum.Xmss.Assembly.GameR
public import Quantum.Xmss.Assembly.CostRun
public import Quantum.Xmss.Assembly.ProgView
public import Quantum.Xmss.Assembly.ProgSafe
public import Quantum.Xmss.Assembly.EventSqrt
public import Quantum.Xmss.Assembly.KeyLazy
public import Quantum.Xmss.Assembly.KeysReparam
public import Quantum.Xmss.Assembly.PrefixFacts
public import Quantum.Xmss.Assembly.TrialsOff
public import Quantum.Xmss.Assembly.PathsDisjoint
public import Quantum.Xmss.Assembly.CostJoint
public import Quantum.Xmss.Assembly.TrialHitUniform
public import Quantum.Xmss.Assembly.EncPorts
public import Quantum.Xmss.Assembly.HTrial
public import Quantum.Xmss.Assembly.RecJ
public import Quantum.Xmss.Assembly.HwHeads
public import Quantum.Xmss.Assembly.RecBadMass
public import Quantum.Xmss.Assembly.RecHitB
public import Quantum.Xmss.Assembly.CwRev
public import Quantum.Xmss.Assembly.RecOffDecHit
public import Quantum.Xmss.Hybrid.GradedMasked

@[expose] public section

/-!
# leanXMSS is quantum SUF-CMA secure in the QRPM, from its open debts

The assembly of the chain of games (design, sections 2 and 9). Every step is a committed theorem;
every link that the committed theorems do not provide is a field of `XmssQrpmDebts q A`, stated as
exactly the missing link. The averages are over the uniform honest table `L : HonestTable`
(keys, `π`, master seed). The canonical runtime-2 game is GameR's
`gameR A L = realizeT (valueAt L) (gameT Selections cwUpd (pubOf L) A)` against `runtimeR m0R`, its
challenge prefix `prefixR A L` followed by the verification (`gameR_eq`).

1. **G0 to runtime 1 with the full table** (FullTable's `winProb_eq_uavg_full`), **program ports**
   (`p1T_eq_p1K`) and **record ports** (`p1K_eq_p1R`, RecordDrop).
2. **The masked graded hybrid** (GradedMasked's `uavg_win_runtime1R_le_graded_total_masked_pad`
   with `covers_fullHw`): `runtime1R` against `runtimeR` on the canonical game, the masses averaged
   over the good set `maskG` (ReparamR0's `r0G treeQ 18` of the padded table with HTrial's
   `TrialHidGood` at its public datum and hidden values) and its bad fraction `2^-174 + 2^-400`
   paid once (`r0G_frac_le_keccak`, `trialHidGood_r0G_frac_le_keccak`). Sponge ports:
   `uavg_mask_spongeMass_le_xmssR0` at `r0E`, `6q κ` with `κ = kappaS = 2^-128 + 2^-189`
   (`spongeConst_le_keccak`). Read ports: TrialSource's `uavg_mask_readMass_le_xmssR0_good` at
   `r0E`, `htrialTau (2 clsCap) + 2^-117` (`readConst_le_keccak`), the randomizer trials' term
   HTrial's `sum_trialMass_le` with the recorded trial cells `trialRecW` at most `2` per read call
   (`sum_trialRecW_le`).
3. **End** (PrefixFacts' `endReads_wGame_trialHit`, on the good tables `GoodL = TableGood ∧
   TrialsOff`): the win is at most the event `BadR L progCap` at the end of the game, the read
   error `readTerm` and the trial-hit mass, averaged at most `trialCap = 2^-399` (TrialHit's
   `uavg_trialHitMass_le` with TrialHitUniform's `decUniformHyp`).
4. **The event bound** (CostRefined's `ewR_le_sqrt_ref`, `PermGood`): `(advTerm q + verTerm q +
   √(twPR + verLin q))²`, the verification's reads graded like sponge calls and the challenge
   prefix's classical costs `twPR` (ReadCost's refined read cost) linear.
5. **The prefix's classical costs** (CostRefined's `twPR_le`, `PermGood`, `q ≤ 2^64`):
   `twPR ≤ (√E + √m)² + progPreR` with `E = 2 encRPre + hwMovePre + kapRR clsCap` and the
   flip-value recorded mass `m = cwRecPre + recBadPre`. EncRefined's `encE_le`:
   `E ≤ encEC q + 2 encBeta q · m + 2 encGamma q (kfPre + recJPre) + hwHeadPre`, where
   `hwHeadPre = 0` (HwHeads' `hwHeadPre_eq_zero_all`), `kfPre ≤ kfGame` averaged by KeyLazy on
   KeysReparam's `keyE` (`uavg_kfTot_le_r0`, `progBound`) and the `RecJ` weight by RecJ's
   `uavg_recJPre_le_two_pow` (`recJCap = 2^-35`). The mass `m` averaged over `GoodL`:
   `cwRecPre` by CwRev's `uavg_cwRecPre_all_le_rev` (debt `cwReFail`), `recBadPre` by RecBadMass's
   `recBadAvg_of_parts` from RecOffDecHit's `decHitAvg_goodL` (`2^-74`), RecHitB's
   `recHitBAvg_of_dec` (debt `decHitB`) and RecOffDecHit's `recOffAvg`: `flipMassCap q`. All
   averaged by `uavg_ite_cost_le_add`. The programs: `progPreR ≤ progTot` and ProgSafe's
   `uavg_progTot_le_kTot` with KeyLazy's `uavg_kTot_le` on a reparametrization exposing the keys
   (`uavg_kTot_le_r0`, KeysReparam): `progBound`.
6. **Good tables**: `PermGood` (`prob_not_permGood_keccak`, `2^-777`), `TrialsOff`
   (`trialsOff_frac_le_keccak`, `2^-173`) and `HonestPathsDisjoint` (`uavg_not_pathsDisjoint_le`,
   `2^-170`, PathsDisjoint).

`qrpmBound q = (√eventTerm + hybTerm)² + 2^-174 + 2^-400` with
`eventTerm = (advTerm + verTerm + √(clsBound + verLin))² + readTerm + trialCap + goodTerm` and
`hybTerm = √(4 · 6q · 6q κ) + √(htrialTau (2 clsCap) + 2^-117)`. For `q > 2^64` the bound is at
least `1` (`one_le_qrpmBound`), so the debts are needed only for `q ≤ 2^64`.

| Debt | Statement | Target | Owner |
|---|---|---|---|
| `cwReFail` | `CwReView A`: reveals of a label whose earlier search failed | `cwReEps q` | CwReFail |
| `decHitB` | `DecHitBAvg A GoodL`: decompressed other-label digest hits | `2^-60` | RecHitB's route |
-/

open MeasureTheory Matrix
open scoped ENNReal Kronecker

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

/-! ## Averages over a table split into three coordinates -/

section avg

variable {Θ S P K : Type*} [Fintype Θ] [Fintype S] [Fintype P] [Fintype K]

theorem card_inv_of_equiv (e : Θ ≃ S × P × K) :
    (Fintype.card Θ : ℝ≥0∞)⁻¹ =
      (Fintype.card S : ℝ≥0∞)⁻¹ * ((Fintype.card P : ℝ≥0∞)⁻¹ * (Fintype.card K : ℝ≥0∞)⁻¹) := by
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_prod, Nat.cast_mul, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.natCast_ne_top _))) (Or.inl (ENNReal.natCast_ne_top _)),
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]

theorem sum_of_equiv (e : Θ ≃ S × P × K) (F : Θ → ℝ≥0∞) :
    ∑ θ, F θ = ∑ s, ∑ p, ∑ k, F (e.symm (s, p, k)) := by
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]

/-- The average of a function of the middle coordinate. -/
theorem uavg_comp_snd_fst [Nonempty S] [Nonempty K] (e : Θ ≃ S × P × K) (h : P → ℝ≥0∞) :
    uavg (fun θ ↦ h (e θ).2.1) = (Fintype.card P : ℝ≥0∞)⁻¹ * ∑ p, h p := by
  have hS : (Fintype.card S : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hK : (Fintype.card K : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [uavg, card_inv_of_equiv e, sum_of_equiv e, Equiv.apply_symm_apply,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  calc (Fintype.card S : ℝ≥0∞)⁻¹ * ((Fintype.card P : ℝ≥0∞)⁻¹ * (Fintype.card K : ℝ≥0∞)⁻¹) *
        ((Fintype.card S : ℝ≥0∞) * ((Fintype.card K : ℝ≥0∞) * ∑ p, h p))
      = ((Fintype.card S : ℝ≥0∞)⁻¹ * Fintype.card S) *
          (((Fintype.card K : ℝ≥0∞)⁻¹ * Fintype.card K) *
            ((Fintype.card P : ℝ≥0∞)⁻¹ * ∑ p, h p)) := by ring
    _ = (Fintype.card P : ℝ≥0∞)⁻¹ * ∑ p, h p := by
      rw [ENNReal.inv_mul_cancel hS (ENNReal.natCast_ne_top _),
        ENNReal.inv_mul_cancel hK (ENNReal.natCast_ne_top _), one_mul, one_mul]

/-- **Jensen for `(√g + √f)²`**: the average is at most `(√(E g) + √(E f))²`. -/
theorem uavg_sqrt_add_sqrt_sq_le [Nonempty Θ] (g f : Θ → ℝ≥0∞) :
    uavg (fun θ ↦ (g θ ^ (2⁻¹ : ℝ) + f θ ^ (2⁻¹ : ℝ)) ^ 2) ≤
      (uavg g ^ (2⁻¹ : ℝ) + uavg f ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h4 : ∀ y : ℝ≥0∞, 4 * (4⁻¹ * y) = y := fun y ↦ by
    rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hsingle : ∀ y : ℝ≥0∞, ∑' j : ℕ, (4 * (if j = 0 then 4⁻¹ * y else 0)) ^ (2⁻¹ : ℝ) =
      y ^ (2⁻¹ : ℝ) := fun y ↦ by
    rw [tsum_eq_single 0 fun j hj ↦ by
      simp only [hj, ↓reduceIte, mul_zero,
        ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]]
    simp only [↓reduceIte, h4]
  have h := uavg_le_of_hybrid (fun θ ↦ (g θ ^ (2⁻¹ : ℝ) + f θ ^ (2⁻¹ : ℝ)) ^ 2) g
    (fun θ j ↦ if j = 0 then 4⁻¹ * f θ else 0) fun θ ↦ by
      rw [pow_two_rpow_inv_two, hsingle]
  refine h.trans_eq ?_
  have hμ : ∀ j : ℕ, uavg (fun θ ↦ if j = 0 then 4⁻¹ * f θ else 0) =
      if j = 0 then 4⁻¹ * uavg f else 0 := fun j ↦ by
    by_cases hj : j = 0
    · simp only [hj, ↓reduceIte, uavg_const_mul]
    · simp only [hj, ↓reduceIte, uavg_const]
  simp only [hμ, hsingle]

/-- **Jensen for `(a + √f)²`**: the average is at most `(a + √(E f))²`. -/
theorem uavg_sq_add_sqrt_le [Nonempty Θ] (a : ℝ≥0∞) (f : Θ → ℝ≥0∞) :
    uavg (fun θ ↦ (a + f θ ^ (2⁻¹ : ℝ)) ^ 2) ≤ (a + uavg f ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := uavg_sqrt_add_sqrt_sq_le (fun _ : Θ ↦ a ^ 2) f
  rwa [uavg_const, pow_two_rpow_inv_two] at h

/-- **The classical costs averaged over the good parameters**, CostJoint's `uavg_ite_cost_le`
with a further term: if on `good` the total `tw ≤ (√E + √m)² + p` and `E ≤ E₀ + β m + γ r`, and
the averages over `good` of `m`, `r` and `p` are at most `mc`, `rc` and `pc`, then the average over
`good` of `tw` is at most `(√(E₀ + β mc + γ rc) + √mc)² + pc`. -/
theorem uavg_ite_cost_le_add {good : Θ → Prop} [DecidablePred good] {tw E m p r : Θ → ℝ≥0∞}
    {E₀ β γ mc pc rc : ℝ≥0∞}
    (htw : ∀ θ, good θ → tw θ ≤ (E θ ^ (2⁻¹ : ℝ) + m θ ^ (2⁻¹ : ℝ)) ^ 2 + p θ)
    (hE : ∀ θ, good θ → E θ ≤ E₀ + β * m θ + γ * r θ)
    (hm : uavg (fun θ ↦ if good θ then m θ else 0) ≤ mc)
    (hr : uavg (fun θ ↦ if good θ then r θ else 0) ≤ rc)
    (hp : uavg (fun θ ↦ if good θ then p θ else 0) ≤ pc) :
    uavg (fun θ ↦ if good θ then tw θ else 0) ≤
      ((E₀ + β * mc + γ * rc) ^ (2⁻¹ : ℝ) + mc ^ (2⁻¹ : ℝ)) ^ 2 + pc := by
  refine (uavg_mono (g := fun θ ↦ ((if good θ then E θ else 0) ^ (2⁻¹ : ℝ) +
    (if good θ then m θ else 0) ^ (2⁻¹ : ℝ)) ^ 2 + if good θ then p θ else 0) fun θ ↦ ?_).trans ?_
  · by_cases hθ : good θ
    · simp only [ite_eq_left hθ]
      exact htw θ hθ
    · simp only [ite_eq_right hθ]
      exact zero_le
  have hE' : uavg (fun θ ↦ if good θ then E θ else 0) ≤ E₀ + β * mc + γ * rc := by
    refine (uavg_mono (g := fun θ ↦ E₀ + β * (if good θ then m θ else 0) +
      γ * (if good θ then r θ else 0)) fun θ ↦ ?_).trans ?_
    · by_cases hθ : good θ
      · rw [ite_eq_left hθ, ite_eq_left hθ, ite_eq_left hθ]
        exact hE θ hθ
      · rw [ite_eq_right hθ]
        exact zero_le
    · rw [uavg_add, uavg_add, uavg_const_mul, uavg_const_mul]
      exact add_le_add (add_le_add (uavg_const_le E₀) (mul_le_mul_of_nonneg_left hm zero_le))
        (mul_le_mul_of_nonneg_left hr zero_le)
  rw [uavg_add]
  exact add_le_add ((uavg_sq_rpow_add_le _ _).trans (pow_le_pow_left₀ zero_le (add_le_add
    (ENNReal.rpow_le_rpow hE' (by norm_num)) (ENNReal.rpow_le_rpow hm (by norm_num))) 2)) hp

end avg

/-! ## The table and the win probabilities of the chain -/

section quantities

/-- The honest table as master seed, permutation and keys. -/
def tableSplit : HonestTable ≃ MasterSeed × Equiv.Perm (X × Z) × SpongeKeys X Z :=
  tableEquiv.trans ((Equiv.prodComm _ _).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)))

/-- S5's runtime 1 with the cells `Lt L` hardwired, running the grind-only game. -/
noncomputable def p1T (A : Adversary (X × Z)) (Lt : HonestTable → Hw X Z) (L : HonestTable) :
    ℝ≥0∞ :=
  (spongeHardwiredReadRuntime X Z (Lt L) ()).evalDistMap .instruments
    (gameReadsT Unit (pubOf L) (valueAt L) A) (SubState.basis ()) winObs {true}

/-- Kraus's runtime 1 (`Lt L` hardwired, program ports) running the canonical game with its record
ports dropped. -/
noncomputable def p1K (A : Adversary (X × Z)) (Lt : HonestTable → Hw X Z) (L : HonestTable) :
    ℝ≥0∞ :=
  (runtime1 X Z (Lt L) ()).evalDistMap .instruments (gameD Unit (pubOf L) (valueAt L) A)
    (SubState.basis ()) winObs {true}

/-- Runtime 1 with record ports running the canonical game. -/
noncomputable def p1R (A : Adversary (X × Z)) (Lt : HonestTable → Hw X Z) (L : HonestTable) :
    ℝ≥0∞ :=
  (runtime1R X Z (Lt L) m0R).evalDistMap .instruments (gameR A L) (SubState.basis ()) winObs
    {true}

/-- Runtime 2 with the coin table `Lc L` and record ports, running the canonical game. -/
noncomputable def p2CR (A : Adversary (X × Z)) (Lc : HonestTable → Hw X Z) (L : HonestTable) :
    ℝ≥0∞ :=
  (runtime2CoinsR X Z (Lc L) m0R).evalDistMap .instruments (gameR A L) (SubState.basis ())
    winObs {true}

/-- `runtimeR` running `x2 L`. -/
noncomputable def p2R
    (x2 : HonestTable → QComp (recHwSpec X Z HPos Selections) (QReg.of Unit) (QReg.of Unit)
      Bool)
    (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).evalDistMap .instruments (x2 L) (SubState.basis ()) winObs {true}

end quantities

/-! ## Runtime 2 with record ports, for a general label and memory -/

section generic

variable {S M' : Type} [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M']

/-- **Hidden `k`-cells naming one 128-bit value, for `runtimeR`, averaged over a reparametrized
table** (`sum_queryWeight_hiddenK_digest_extend_le`, `avg_le_of_sum_le`). -/
theorem uavg_hiddenK_digest_runtimeR_le {Θ P : Type} [Fintype Θ] [Fintype P]
    (e : Θ ≃ P × (S → Digest)) (m₀ : Finset S × M') (lab : HwReg X Z (Finset S × M') → Finset S)
    (x : P → (S → Digest) → QComp (recHwSpec X Z S M') (QReg.of Unit) (QReg.of Unit) Bool)
    (ρ : SubState (QReg.of Unit)) (j : ℕ)
    (hview : ∀ p, ViewByOn (D := fun _ : S ↦ Digest) (runtimeR m₀) .instruments
      (fun i ↦ i.isLeft = true) lab (x p)
      (fun _ ↦ ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) j)
    (Hk : P → (S → Digest) → Set X) (src : P → X → HwReg X Z (Finset S × M') → S)
    (val : P → X → HwReg X Z (Finset S × M') → Digest)
    (hk : ∀ p v y r, y ∈ Hk p v → r.2.1.2.1 y = none →
      src p y r ∉ lab r ∧ v (src p y r) = val p y r) :
    uavg (fun θ ↦ (runtimeR m₀).queryWeight .instruments
      (extWeight (hiddenMass ∅ (Hk (e θ).1 (e θ).2) ∅)) (x (e θ).1 (e θ).2)
      (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) j) ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  refine avg_le_of_sum_le e _ _ fun p ↦ ?_
  simp only [Equiv.apply_symm_apply]
  have hρ : ENNReal.ofReal (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix).trace.re ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (ρ.prod (runtimeR (X := X) (Z := Z) m₀).init).trace_re_le_one
  refine (sum_queryWeight_hiddenK_digest_extend_le .instruments m₀ recStep lab (x p)
    (fun _ ↦ ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix)
    (fun _ ↦ (ρ.prod (runtimeR (X := X) (Z := Z) m₀).init).posSemidef) j
    (fun i ↦ i.isLeft = true) (fun _ ↦ rfl) (hview p) (Hk p) (src p) (val p) (hk p)).trans ?_
  gcongr
  calc ∑ _v : S → Digest,
        ENNReal.ofReal (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix).trace.re
      ≤ ∑ _v : S → Digest, (1 : ℝ≥0∞) := Finset.sum_le_sum fun _ _ ↦ hρ
    _ = Fintype.card (S → Digest) := by simp

end generic

/-! ## The game's fresh key flips -/

/-- The target-free fresh `k`, `k'` program flips of the whole game (KeyLazy's `kfW`). -/
noncomputable def kfGame (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (fun _ _ ↦ 0) (kfW L.perm)))
    (gameR A L) initR

/-! ## The bound -/

/-- The bad fraction of the keys' reparametrization (`keyE_bad_le`): `2^-170`. -/
noncomputable def keyBadCap : ℝ≥0∞ := (2 ^ 170 : ℝ≥0∞)⁻¹

/-- **The programs** (ProgSafe, KeyLazy): `progCap (2^-301 + keyBadCap)`. Also the averaged fresh
`k`, `k'` flips of the game (`uavg_kfTot_le_r0`). -/
noncomputable def progBound : ℝ≥0∞ :=
  (2 ^ 301 : ℝ≥0∞)⁻¹ * progCap + progCap * keyBadCap

/-- The averaged `RecJ` weight of the prefix's program calls over the good tables
(`uavg_recJPre_le_two_pow`, `q ≤ 2^64`): `2^-35`. -/
noncomputable def recJCap : ℝ≥0∞ := (2 ^ 35 : ℝ≥0∞)⁻¹

/-- **The target of `CwReView`** (debt `cwReFail`): `2^-100 + 12q · 2^-128` per hidden value for
the reveals of a label whose earlier search ran all its trials without a codeword while the key
stayed unselected. A failed search needs nearly all of its `2^32` trials to fail: the fresh ones
fail with `(1 - ρ)` each, and the bases with many recorded trial blocks cost their share of the
recorded blocks of unrevealed labels, at most `6q` in total. -/
noncomputable def cwReEps (q : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / 2 ^ 100) + ((12 * q : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 2 ^ 128)

/-- **The codeword-recorded mass of the prefix, averaged over all tables** (CwRev's
`uavg_cwRecPre_all_le_rev` at `cwReEps q`): the first runs `2^-94 · 6q`, the failed searches
`4 · 2^32 · cwReEps q`, the fresh trial reads `cwFreshEps (6q + clsCap) · clsCap`, `cwJunk` and the
static `clsCap · 2^-400`. -/
noncomputable def cwRecCap (q : ℕ) : ℝ≥0∞ :=
  cwRevTau q (cwReEps q) + cwJunk + clsCap * ENNReal.ofReal (1 / 2 ^ 400)

/-- **The decompressed re-grind hits** (RecOffDecHit's `decHitAvg_goodL`): `2^-74`. -/
noncomputable def decHitTau : ℝ≥0∞ := ENNReal.ofReal (1 / 2 ^ 74)

/-- **The target of `DecHitBAvg`** (debt `decHitB`): `2^-60`, a clean power of two above the
estimate `2 lifetime · 2^-107` (one possible hit of the selected codeword digest per label run,
over at least `2^107` codeword digests). -/
noncomputable def decHitBTau : ℝ≥0∞ := ENNReal.ofReal (1 / 2 ^ 60)

/-- **The recorded trial cells off the trial's path** (RecOffDecHit's `recOffAvg`): `2/|Z|` per
trial read, `2^-511 clsCap`. -/
noncomputable def recOffTau : ℝ≥0∞ := ENNReal.ofReal (2 / Fintype.card Z) * (clsCap : ℝ≥0∞)

/-- **The `RecBad` mass of the prefix, averaged over the good tables** (`recBadAvg_of_parts` with
`recHitBAvg_of_dec`): `2 decHitTau + recConv + (2 decHitBTau + recConv) + recOffTau`. -/
noncomputable def recBadCap : ℝ≥0∞ :=
  2 * decHitTau + recConv + (2 * decHitBTau + recConv) + recOffTau

/-- **The flip-value recorded mass** `cwRecPre + recBadPre`, averaged over the good tables. -/
noncomputable def flipMassCap (q : ℕ) : ℝ≥0∞ := cwRecCap q + recBadCap

/-- **The prefix's classical costs** (`twPR_le`, `encE_le`, averaged): `(√(encEC q +
2 encBeta q · flipMassCap q + 2 encGamma q (progBound + recJCap)) + √flipMassCap q)² +
progBound`. -/
noncomputable def clsBound (q : ℕ) : ℝ≥0∞ :=
  ((encEC q + 2 * encBeta q * flipMassCap q + 2 * encGamma q * (progBound + recJCap)) ^
    (2⁻¹ : ℝ) + flipMassCap q ^ (2⁻¹ : ℝ)) ^ 2 + progBound

/-- The read error of verification's final reads (`verifyBlocks` reads of each function). -/
noncomputable def readTerm : ℝ≥0∞ :=
  ENNReal.ofReal (readError X Z verifyBlocks verifyBlocks verifyBlocks)

/-- The weight of the permutations that are not `PermGood π 18`. -/
noncomputable def permTerm : ℝ≥0∞ := ENNReal.ofReal (1 / 2 ^ 777)

/-- The target of the fraction of the tables whose honest paths share a cell: `2^-170`. -/
noncomputable def disjCap : ℝ≥0∞ := (2 ^ 170 : ℝ≥0∞)⁻¹

/-- The fraction of the tables off `GoodL`: `2^-777 + disjCap + 2^-173`. -/
noncomputable def goodTerm : ℝ≥0∞ :=
  permTerm + disjCap + ENNReal.ofReal (1 / 2 ^ 173)

/-- The bound on the averaged trial-hit mass (`uavg_trialHitMass_le_of_good`): `2^-399`. -/
noncomputable def trialCap : ℝ≥0∞ := ENNReal.ofReal (1 / 2 ^ 399)

/-- The bound on runtime 2's win probability. -/
noncomputable def eventTerm (q : ℕ) : ℝ≥0∞ :=
  (advTerm q + verTerm q + (clsBound q + verLin q) ^ (2⁻¹ : ℝ)) ^ 2 + readTerm + trialCap +
    goodTerm

/-- The masked hidden mass per sponge call: `2^-128 + 2^-189` (`spongeConst_le_keccak`). -/
noncomputable def kappaS : ℝ≥0∞ :=
  (2 ^ 128 : ℝ≥0∞)⁻¹ + (2 ^ 189 : ℝ≥0∞)⁻¹

/-- The masked hidden mass at the read ports: the randomizer trials' `htrialTau (2 clsCap)`
(HTrial: the recorded trial cells weigh at most `2` per read call) plus `2^-117`
(`readConst_le_keccak`). -/
noncomputable def readCap : ℝ≥0∞ :=
  htrialTau (2 * clsCap) + ENNReal.ofReal (1 / 2 ^ 117)

/-- The target of the masked graded hybrid: `√(4 · 6q · μ) + √ν` with the sponge-port mass
`μ = 6q κ` over at most `6q` sponge calls and the read-port mass `ν = readCap`. -/
noncomputable def hybTerm (q : ℕ) : ℝ≥0∞ :=
  (4 * (((6 * q : ℕ) : ℝ≥0∞) * (((6 * q : ℕ) : ℝ≥0∞) * kappaS))) ^ (2⁻¹ : ℝ) +
    readCap ^ (2⁻¹ : ℝ)

/-- The bad fraction of the masked hybrid's good set `maskG`, paid once: ReparamR0's `2^-174` and
HTrial's `2^-400`. -/
noncomputable def r0Term : ℝ≥0∞ := ENNReal.ofReal (1 / 2 ^ 174) + ENNReal.ofReal (1 / 2 ^ 400)

/-- **The leanXMSS QRPM bound**: `(√eventTerm + hybTerm)² + 2^-174 + 2^-400`. -/
noncomputable def qrpmBound (q : ℕ) : ℝ≥0∞ :=
  (eventTerm q ^ (2⁻¹ : ℝ) + hybTerm q) ^ 2 + r0Term

/-! ## The debts -/

section debts

/-- **The open debts of the leanXMSS QRPM proof**, for an adversary `A` making at most `q`
permutation calls and at most `lifetime` signing requests (needed for `q ≤ 2^64` only: above,
`qrpmBound q ≥ 1`). Every other link is a committed theorem (see the module docstring). -/
structure XmssQrpmDebts (q : ℕ) (A : Adversary (X × Z)) where
  /-- **Failed searches at the reveals** (CwRev): the mass at a reveal of a label already revealed
  whose key is still unselected, summed over the hidden values, is at most `cwReEps q` per
  value. -/
  cwReFail : CwReView A (cwReEps q)
  /-- **The decompressed other-label digest hits** (RecHitB), averaged over the good tables. -/
  decHitB : DecHitBAvg A GoodL decHitBTau

end debts

/-! ## The proof -/

section proof

attribute [local instance] badRDec

/-- The permutations that are not `PermGood π 18` weigh at most `2^-777` among the tables. -/
theorem uavg_not_permGood_le :
    uavg (fun L : HonestTable ↦ if PermGood L.perm 18 then 0 else 1) ≤ permTerm := by
  refine (uavg_comp_snd_fst tableSplit
    (fun π : Equiv.Perm (X × Z) ↦ if PermGood π 18 then (0 : ℝ≥0∞) else 1)).trans_le ?_
  have h := ENNReal.ofReal_le_ofReal (prob_not_permGood_keccak (X := X) (Z := Z) card_X card_Z)
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast] at h
  have hs : ∑ π : Equiv.Perm (X × Z), (if PermGood π 18 then (0 : ℝ≥0∞) else 1) =
      ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π 18).card : ℝ≥0∞) := by
    rw [← Finset.sum_boole]
    exact Finset.sum_congr rfl fun π _ ↦ by by_cases hπ : PermGood π 18 <;> simp [hπ]
  rw [hs, mul_comm, ← div_eq_mul_inv]
  exact h

open scoped Classical in
/-- The tables violating `TrialsOff` weigh at most `2^-173` (`trialsOff_frac_le_keccak`). -/
theorem uavg_not_trialsOff_le :
    uavg (fun L : HonestTable ↦ if TrialsOff L then (0 : ℝ≥0∞) else 1) ≤
      ENNReal.ofReal (1 / 2 ^ 173) := by
  rw [uavg_ite_zero_one]
  exact trialsOff_frac_le_keccak

/-- **The program ports drop** (`dropsTo_gameD`): Kraus's runtime 1 on `gameD` is S5's runtime 1
on the grind-only game. -/
theorem p1T_eq_p1K (A : Adversary (X × Z)) {Lt : HonestTable → Hw X Z}
    (hLt : ∀ L, HwLe (tableHw L) (Lt L)) (L : HonestTable) : p1T A Lt L = p1K A Lt L :=
  (congrArg (fun μ : Measure Bool ↦ μ {true})
    (evalDistMap_runtime1_eq_spongeHardwiredReadRuntime (Lt L) ()
      (dropsTo_gameD (M := Unit) ((progsOf_tableHw L).mono (hLt L)) A) (SubState.basis ())
      winObs)).symm

/-- **The record ports drop** (`dropRec_gameT`, `evalDistMap_runtime1R_eq`): runtime 1 with record
ports on the canonical game is Kraus's runtime 1 on `gameD`. -/
theorem p1K_eq_p1R (A : Adversary (X × Z)) (Lt : HonestTable → Hw X Z) (L : HonestTable) :
    p1K A Lt L = p1R A Lt L :=
  (congrArg (fun μ : Measure Bool ↦ μ {true})
    (evalDistMap_runtime1R_eq (Lt L) m0R (dropRec_gameT cwUpd (valueAt L) (pubOf L) A)
      (SubState.basis ()) winObs)).symm

/-- The prefix's program flips are among the game's: `progPreR ≤ progTot`. -/
theorem progPreR_le_progTot (A : Adversary (X × Z)) (L : HonestTable) :
    progPreR A L ≤ progTot A L := by
  unfold progPreR progTot costTot
  rw [gameR_eq]
  exact totalWeight_le_bind₂ (runtimeR m0R) .instruments _ (prefixR A L) _ initR

/-- **The fraction of the tables off `GoodL`**: at most `goodTerm`. -/
theorem uavg_not_goodL_le :
    uavg (fun L ↦ if GoodL L then (0 : ℝ≥0∞) else 1) ≤ goodTerm := by
  classical
  have hpt : ∀ L : HonestTable, (if GoodL L then (0 : ℝ≥0∞) else 1) ≤
      ((if PermGood L.perm 18 then 0 else 1) + (if HonestPathsDisjoint L then 0 else 1)) +
        (if TrialsOff L then 0 else 1) := fun L ↦ by
    by_cases hG : GoodL L
    · rw [ite_eq_left hG]
      exact zero_le
    · rw [ite_eq_right hG]
      have h : ¬PermGood L.perm 18 ∨ ¬HonestPathsDisjoint L ∨ ¬TrialsOff L := by
        by_cases h1 : PermGood L.perm 18
        · by_cases h2 : HonestPathsDisjoint L
          · exact Or.inr (Or.inr fun h3 ↦ hG ⟨⟨h1, h2⟩, h3⟩)
          · exact Or.inr (Or.inl h2)
        · exact Or.inl h1
      rcases h with h | h | h
      · rw [ite_eq_right h]
        exact le_self_add.trans le_self_add
      · rw [ite_eq_right h]
        exact le_add_self.trans le_self_add
      · rw [ite_eq_right h]
        exact le_add_self
  refine (uavg_mono hpt).trans ?_
  rw [uavg_add, uavg_add]
  exact add_le_add (add_le_add uavg_not_permGood_le uavg_not_pathsDisjoint_le)
    uavg_not_trialsOff_le

/-- **The good set of the masked hybrid**: ReparamR0's `r0G treeQ 18` and HTrial's
`TrialHidGood` at the public datum and hidden values of `r0E`. -/
def maskG (t : HonestTable × RE) : Prop :=
  r0G treeQ 18 t ∧ TrialHidGood (pubR (r0E t).1) (r0E t).2.1

/-- `maskG`, decided classically. -/
noncomputable instance instDecidablePredMaskG : DecidablePred maskG :=
  Classical.decPred _

/-- A filter covered by two filters has at most their total card. -/
theorem card_filter_le_add {α : Type*} [Fintype α] (P Q R : α → Prop) [DecidablePred P]
    [DecidablePred Q] [DecidablePred R] (h : ∀ a, P a → Q a ∨ R a) :
    (Finset.univ.filter P).card ≤ (Finset.univ.filter Q).card + (Finset.univ.filter R).card := by
  classical
  refine (Finset.card_le_card fun a ha ↦ ?_).trans (Finset.card_union_le _ _)
  rw [Finset.mem_filter] at ha
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
  rcases h a ha.2 with h | h
  · exact Or.inl ⟨ha.1, h⟩
  · exact Or.inr ⟨ha.1, h⟩

/-- **The bad fraction of `maskG`**: at most `2^-174 + 2^-400` (`r0G_frac_le_keccak`,
`trialHidGood_r0G_frac_le_keccak`). -/
theorem maskG_frac_le :
    (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ ¬maskG t).card ≤
      r0Term := by
  refine le_trans ?_ (add_le_add r0G_frac_le_keccak trialHidGood_r0G_frac_le_keccak)
  rw [← mul_add, ← Nat.cast_add]
  refine mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_filter_le_add _ _ _ fun t h ↦ ?_))
    zero_le
  by_cases h0 : r0G treeQ 18 t
  · exact Or.inr ⟨h0, fun h' ↦ h ⟨h0, h'⟩⟩
  · exact Or.inl h0

/-- A value plus an average of values, each at most `D`, is at most `2 D`. -/
theorem add_sum_avg_le {Y : Type} [Fintype Y] [Nonempty Y] {a D : ℝ≥0∞} {f : Y → ℝ≥0∞}
    (ha : a ≤ D) (hf : ∀ y, f y ≤ D) :
    a + ∑ y, (Fintype.card Y : ℝ≥0∞)⁻¹ * f y ≤ 2 * D := by
  calc a + ∑ y, (Fintype.card Y : ℝ≥0∞)⁻¹ * f y ≤ D + ∑ _y : Y, (Fintype.card Y : ℝ≥0∞)⁻¹ * D :=
        add_le_add ha (Finset.sum_le_sum fun y _ ↦ mul_le_mul_of_nonneg_left (hf y) zero_le)
    _ = 2 * D := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
        ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
          (ENNReal.natCast_ne_top _), one_mul, two_mul]

open scoped ComplexOrder in
/-- The diagonal mass of a `k`-read port's input set is at most the trace at the read and record
ports, and `0` elsewhere. -/
theorem diagMass_readKSet_le (G : X → Set (HwReg X Z Mem)) (Inv : HwReg X Z Mem → Prop)
    (i : (recHwSpec X Z HPos Selections).Port)
    {σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem)) ℂ}
    (hσ : σ.PosSemidef) :
    diagMass (readKSet G Inv i) σ ≤
      if readRecPort Selections i = true then ENNReal.ofReal σ.trace.re else 0 := by
  rcases i with ((p | c) | c) | T
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun a _ ↦
      Set.indicator_of_notMem (Set.notMem_empty a) _) zero_le
  · exact (diagMass_le_trace _ hσ).trans_eq (ite_eq_left rfl).symm
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun a _ ↦
      Set.indicator_of_notMem (Set.notMem_empty a) _) zero_le
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun a _ ↦
      Set.indicator_of_notMem (Set.notMem_empty a) _) zero_le

open scoped ComplexOrder in
/-- **The recorded trial cells per call** (HTrial's `trialRecW`): a diagonal mass plus an average
of diagonal masses, at most `2` times the trace at the read and record ports. -/
theorem trialRecW_le (π : Equiv.Perm (X × Z)) (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem)) ℂ)
    (hσ : σ.PosSemidef) :
    trialRecW (M := Selections) π i σ ≤
      2 * if readRecPort Selections i = true then ENNReal.ofReal σ.trace.re else 0 :=
  add_sum_avg_le (diagMass_readKSet_le _ _ i hσ) fun _ ↦ diagMass_readKSet_le _ _ i hσ

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **HTrial's `hrec` with `R = 2 clsCap`**: the recorded trial cells along the challenge prefix
weigh at most `2` per read call (`trialRecW_le`), at most `clsCap` read calls. -/
theorem sum_trialRecW_le (pub : Pub) :
    ∑ v : HPos → Digest, (runtimeR m0R).totalWeight .instruments
      (trialRecW (M := Selections) pub.perm) (realizeT v (prefixT Selections cwUpd pub A)) initR ≤
        2 * (clsCap : ℝ≥0∞) * Fintype.card (HPos → Digest) := by
  have hv : ∀ v : HPos → Digest, (runtimeR m0R).totalWeight .instruments
      (trialRecW (M := Selections) pub.perm) (realizeT v (prefixT Selections cwUpd pub A)) initR ≤
        2 * (clsCap : ℝ≥0∞) := fun v ↦ by
    have hN : IPFunctor.IFreeM.IsChargeBound (realizeT v (prefixT Selections cwUpd pub A))
        (portCharge fun i ↦ if readRecPort Selections i = true then 1 else 0) clsCap := by
      have h := hN_readRec cwUpd A hperm hsign pub v
      rw [gameT_eq_prefixT_bind, realizeT_bind₂] at h
      exact isChargeBound_of_bind₂ h
    refine ((totalWeight_le_totalWeight (runtimeR m0R) .instruments
      (w' := fun i σ ↦ 2 * if readRecPort Selections i = true then ENNReal.ofReal σ.trace.re
        else 0) (fun i σ hσ ↦ trialRecW_le _ i σ hσ) _ initR_posSemidef).trans_eq
      (totalWeight_const_mul_weight (runtimeR m0R) .instruments 2
        (fun i σ ↦ if readRecPort Selections i = true then ENNReal.ofReal σ.trace.re else 0) _
        initR)).trans (mul_le_mul_of_nonneg_left ?_ zero_le)
    exact (totalWeight_trace_le_of_isChargeBound' (runtimeR m0R) .instruments
      (fun i ↦ readRecPort Selections i = true) _ hN initR_posSemidef).trans
      ((mul_le_mul_of_nonneg_left ofReal_trace_initR_le_one zero_le).trans_eq (mul_one _))
  calc ∑ v : HPos → Digest, (runtimeR m0R).totalWeight .instruments
        (trialRecW (M := Selections) pub.perm) (realizeT v (prefixT Selections cwUpd pub A)) initR
      ≤ ∑ _v : HPos → Digest, 2 * (clsCap : ℝ≥0∞) := Finset.sum_le_sum fun v _ ↦ hv v
    _ = 2 * (clsCap : ℝ≥0∞) * Fintype.card (HPos → Digest) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

set_option exponentiation.threshold 1024 in
/-- **The masked sponge-port mass** (`uavg_mask_spongeMass_le_xmssR0` at ReparamR0's `r0E`,
`maskG`, SeedStage's seed families): at most `6q · kappaS` over the good set. -/
theorem uavg_mask_spongeMass_le :
    uavg (fun t : HonestTable × RE ↦ if maskG t then (runtimeR m0R).totalWeight
      .instruments (spongeMass (coverH t.1) (coverK t.1) (coverK' t.1)) (gameR A t.1) initR
        else 0) ≤ ((6 * q : ℕ) : ℝ≥0∞) * kappaS :=
  (uavg_mask_spongeMass_le_xmssR0 cwUpd A hperm hsign m0R initR initR_posSemidef
    ofReal_trace_initR_le_one (Hybrid.querySupportedOn_initR m0R _) r0E maskG
    ((r0E_injOn treeQ 18).mono fun _ ht ↦ ht.1) card_r0E_le pubR parR permR 18
    (fun _ ht ↦ hgame_r0E cwUpd A hashesSlots_treeQ ht.1)
    (fun _ ht ↦ r0E_hpath hashesSlots_treeQ ht.1)
    (fun _ ht ↦ r0E_hr0 ht.1) (fun p k ↦ seedHSlots (permR p) (parR p) k.1 k.2.1)
    (fun p k ↦ seedK'Slots 18 (permR p) (parR p) k.1 k.2.1) (seedEps 18)
    (fun _ ht ↦ r0E_hseed ht.1) (fun p z ↦ sum_indicator_seedHSlots_le 18 (permR p) (parR p) z)
    (fun p y ↦ sum_indicator_seedK'Slots_le 18 (permR p) (parR p) y)).trans
    (mul_le_mul_of_nonneg_left (spongeConst_le_keccak
      (seedEps_le_keccak.trans (ENNReal.ofReal_le_ofReal (by norm_num)))) zero_le)

set_option exponentiation.threshold 1024 in
/-- **The masked read-port mass** (TrialSource's `uavg_mask_readMass_le_xmssR0_good` at
ReparamR0's `r0E` on `maskG`, the trials' term HTrial's `sum_trialMass_le` with
`sum_trialRecW_le`): at most `readCap` over the good set. -/
theorem uavg_mask_readMass_le :
    uavg (fun t : HonestTable × RE ↦ if maskG t then (runtimeR m0R).totalWeight
      .instruments (readMass (coverH t.1) (coverK t.1) (coverK' t.1)) (gameR A t.1) initR
        else 0) ≤ readCap := by
  refine (uavg_mask_readMass_le_xmssR0_good cwUpd A hperm hsign m0R initR initR_posSemidef
    ofReal_trace_initR_le_one (Hybrid.querySupportedOn_initR m0R _) r0E maskG
    ((r0E_injOn treeQ 18).mono fun _ ht ↦ ht.1) card_r0E_le pubR parR permR 18
    (fun _ ht ↦ hgame_r0E cwUpd A hashesSlots_treeQ ht.1)
    (fun _ ht ↦ r0E_hpath hashesSlots_treeQ ht.1)
    (fun _ ht ↦ r0E_hr0 ht.1) (fun p k ↦ seedHSlots (permR p) (parR p) k.1 k.2.1)
    (fun p k ↦ seedK'Slots 18 (permR p) (parR p) k.1 k.2.1) (seedEps 18)
    (fun _ ht ↦ r0E_hseed ht.1) (fun p z ↦ sum_indicator_seedHSlots_le 18 (permR p) (parR p) z)
    (fun p y ↦ sum_indicator_seedK'Slots_le 18 (permR p) (parR p) y)
    (fun p v ↦ TrialHidGood (pubR p) v) (fun _ ht ↦ ht.2) (htrialTau (2 * clsCap))
    fun p ↦ sum_trialMass_le cwUpd A hperm hsign m0R (pubR p) initR initR_posSemidef
      ofReal_trace_initR_le_one (Hybrid.querySupportedOn_initR m0R _)
      (noBot_init m0R (SubState.basis ()).matrix) (2 * clsCap)
      (sum_trialRecW_le hperm hsign (pubR p))).trans ?_
  rw [add_assoc]
  exact add_le_add le_rfl (readConst_le_keccak
    (seedEps_le_keccak.trans (ENNReal.ofReal_le_ofReal (by norm_num))))

/-- **The masked graded hybrid with record ports**, averaged over the table. -/
theorem uavg_p1R_le :
    uavg (p1R A fullHw) ≤ (uavg (p2R (gameR A)) ^ (2⁻¹ : ℝ) + hybTerm q) ^ 2 + r0Term := by
  refine (uavg_win_runtime1R_le_graded_total_masked_pad .instruments fullHw coverH coverK coverK'
    covers_fullHw m0R (gameR A) (fun _ ↦ SubState.basis ()) (fun _ ↦ winObs)
    (measurableSet_singleton true) (6 * q) (advCalls_gameR hperm hsign) maskG _ _
    (uavg_mask_spongeMass_le hperm hsign) (uavg_mask_readMass_le hperm hsign)).trans ?_
  refine add_le_add (le_of_eq ?_) maskG_frac_le
  rw [hybTerm, add_assoc]
  rfl

/-- **The programs**, averaged over the good tables: ProgSafe's `uavg_progTot_le_kTot` with
KeysReparam's `uavg_kTot_le_r0` (KeyLazy on ReparamR0's reparametrization, keys split off). -/
theorem uavg_progPreR_le (hq : q ≤ 2 ^ 64) :
    uavg (fun L ↦ if GoodL L then progPreR A L else 0) ≤ progBound := by
  have hk := uavg_kTot_le_r0 hperm hsign hq
  refine (uavg_mono fun L ↦ ?_).trans ((uavg_progTot_le_kTot hk).trans ?_)
  · by_cases hg : GoodL L
    · rw [ite_eq_left hg, ite_eq_left hg.1.1]
      exact progPreR_le_progTot A L
    · rw [ite_eq_right hg]
      exact zero_le
  · unfold progBound keyBadCap
    exact le_rfl

/-- **The averaged fresh `k`, `k'` flips of the game** (EncPorts' `uavg_kfTot_le` with the hidden
values `val p x` reading the public datum `p`, as KeysReparam's `uavg_kTot_le_dep`). -/
theorem uavg_kfTot_le_dep {E Q V : Type} [Fintype E] [Nonempty E] [Fintype Q] [Fintype V]
    (e : HonestTable × E → Q × (((X → Z) × (X → Z)) × V)) (G : HonestTable × E → Prop)
    [DecidablePred G] (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card Q * Fintype.card (((X → Z) × (X → Z)) × V) ≤
      Fintype.card (HonestTable × E))
    (par : Q → PublicParameter) (perm : Q → Equiv.Perm (X × Z)) (hk : Q → Z → X)
    (val : Q → V → HPos → Digest)
    (hgame : ∀ t, G t → gameR A t.1 = gameKK A (par (e t).1) (perm (e t).1) (hk (e t).1)
      (val (e t).1 (e t).2.2) (e t).2.1.1 (e t).2.1.2)
    (hπ : ∀ t, G t → perm (e t).1 = t.1.perm) :
    uavg (fun L ↦ if PermGood L.perm 18 then (runtimeR m0R).totalWeight .instruments
        (extWeight (hwCost (fun _ _ ↦ 0) (kfW L.perm))) (gameR A L) initR else 0) ≤
      (2 ^ 301)⁻¹ * progCap + progCap * ((Fintype.card (HonestTable × E) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t ↦ ¬G t).card) := by
  refine uavg_le_of_injOn e G hinj hcard _
    (fun p x ↦ if PermGood (perm p) 18 then (runtimeR m0R).totalWeight .instruments
      (extWeight (hwCost (fun _ _ ↦ 0) (kfW (perm p))))
        (gameKK A (par p) (perm p) (hk p) (val p x.2) x.1.1 x.1.2) initR else 0)
    (fun t ht ↦ ?_) progCap (fun t _ ↦ ?_) ((2 ^ 301)⁻¹ * progCap) (fun p ↦ ?_)
  · by_cases hL : PermGood t.1.perm 18
    · have hp : PermGood (perm (e t).1) 18 := (hπ t ht).symm ▸ hL
      rw [ite_eq_left hL, ite_eq_left hp, hgame t ht, hπ t ht]
    · rw [ite_eq_right hL]
      exact zero_le
  · by_cases hL : PermGood t.1.perm 18
    · rw [ite_eq_left hL]
      refine (totalWeight_le_totalWeight (runtimeR m0R) .instruments
        (w' := extWeight (hwCost (fun _ _ ↦ 0) fun _ σ ↦ ENNReal.ofReal σ.trace.re))
        (fun i σ hσ ↦ ?_) (gameR A t.1) initR_posSemidef).trans
        (totalWeight_progs_le (gameR A t.1) (progCalls_gameR hperm hsign t.1))
      rcases i with ((p | c) | c) | T
      · exact le_rfl
      · exact le_rfl
      · dsimp only [extWeight, sumWeight, hwCost]
        cases c with
        | programH z u => exact zero_le
        | programK y a => exact diagMass_le_trace _ hσ
        | programK' y a => exact diagMass_le_trace _ hσ
      · exact le_rfl
    · rw [ite_eq_right hL]
      exact zero_le
  · by_cases hp : PermGood (perm p) 18
    · refine (Finset.sum_congr rfl fun x _ ↦ ite_eq_left hp).trans_le ?_
      exact sum_pair_le (fun k k' w ↦ (runtimeR m0R).totalWeight .instruments
        (extWeight (hwCost (fun _ _ ↦ 0) (kfW (perm p))))
          (gameKK A (par p) (perm p) (hk p) (val p w) k k') initR) _ _
        fun w ↦ sum_kfTot_le A (par p) (perm p) (hk p) (val p w) hperm hsign hp
    · rw [Finset.sum_eq_zero fun x _ ↦ ite_eq_right hp]
      exact zero_le

/-- **The averaged fresh `k`, `k'` flips of the game on KeysReparam's `keyE`**: over the
`PermGood` tables at most `progBound`. -/
theorem uavg_kfTot_le_r0 :
    uavg (fun L ↦ if PermGood L.perm 18 then kfGame A L else 0) ≤ progBound := by
  refine (uavg_kfTot_le_dep hperm hsign (E := RE) (Q := KQ) (V := KV) keyE (r0G treeQ 18)
    keyE_injOn card_keyE_le parK permK hkK valK (fun _ ht ↦ hgame_keyE A ht)
    fun t _ ↦ permK_keyE t).trans ?_
  unfold progBound keyBadCap
  gcongr
  exact keyE_bad_le

/-- **The flip-value recorded mass**, averaged over the good tables: CwRev's
`uavg_cwRecPre_all_le_rev` (debt `cwReFail`) and RecBadMass's `recBadAvg_of_parts` with
RecOffDecHit's `decHitAvg_goodL`, `recOffAvg` and RecHitB's `recHitBAvg_of_dec` (debt `decHitB`). -/
theorem uavg_flipMass_le (d : XmssQrpmDebts q A) :
    uavg (fun L ↦ if GoodL L then cwRecPre A L + recBadPre A L else 0) ≤ flipMassCap q := by
  have hc : uavg (cwRecPre A) ≤ cwRecCap q := uavg_cwRecPre_all_le_rev hperm hsign d.cwReFail
  have hb : RecBadAvg A GoodL recBadCap := recBadAvg_of_parts hperm hsign GoodL
    (decHitAvg_goodL hperm hsign) (recHitBAvg_of_dec hperm hsign GoodL d.decHitB)
    (recOffAvg hperm hsign GoodL)
  refine (uavg_mono (g := fun L ↦ cwRecPre A L + if GoodL L then recBadPre A L else 0)
    fun L ↦ ?_).trans ?_
  · by_cases hg : GoodL L
    · rw [ite_eq_left hg, ite_eq_left hg]
    · rw [ite_eq_right hg]
      exact zero_le
  · rw [uavg_add]
    exact add_le_add hc hb

/-- **The prefix's linear charge at a good table** (EncRefined's `encE_le` with
`hwHeadPre_eq_zero_all` and `kfPre_le`): `E ≤ encEC q + 2 encBeta q · m + 2 encGamma q (kfGame +
recJPre)` with `m = cwRecPre + recBadPre`. -/
theorem encE_le_good (hq : q ≤ 2 ^ 64) (L : HonestTable) (hg : GoodL L) :
    2 * encRPre A L + hwMovePre A L + ENNReal.ofReal kapRR * (clsCap : ℝ≥0∞) ≤
      encEC q + 2 * encBeta q * (cwRecPre A L + recBadPre A L) +
        2 * encGamma q * (kfGame A L + recJPre A L) := by
  have h := encE_le hperm hsign hq L hg.1.1
  rw [hwHeadPre_eq_zero_all hperm hsign L, add_zero] at h
  exact h.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (add_le_add (kfPre_le A L) le_rfl) zero_le))

/-- **The prefix's refined classical costs**, averaged over the good tables (`twPR_le`,
`encE_le_good`, `uavg_ite_cost_le_add`): at most `clsBound q`. -/
theorem uavg_twPR_le (hq : q ≤ 2 ^ 64) (d : XmssQrpmDebts q A) :
    uavg (fun L ↦ if GoodL L then twPR A L else 0) ≤ clsBound q := by
  have hr : uavg (fun L ↦ if GoodL L then kfGame A L + recJPre A L else 0) ≤
      progBound + recJCap := by
    refine (uavg_mono (g := fun L ↦ (if PermGood L.perm 18 then kfGame A L else 0) +
      if GoodL L then recJPre A L else 0) fun L ↦ ?_).trans ?_
    · by_cases hg : GoodL L
      · rw [ite_eq_left hg, ite_eq_left hg.1.1, ite_eq_left hg]
      · rw [ite_eq_right hg]
        exact zero_le
    · rw [uavg_add]
      exact add_le_add (uavg_kfTot_le_r0 hperm hsign) (uavg_recJPre_le_two_pow hperm hsign hq)
  exact uavg_ite_cost_le_add (fun L hg ↦ twPR_le hperm hsign hq L hg.1.1)
    (encE_le_good hperm hsign hq) (uavg_flipMass_le hperm hsign d) hr
    (uavg_progPreR_le hperm hsign hq)

/-- **Runtime 2's win at a good table** (PrefixFacts' `endReads_wGame_trialHit`, CostRefined's
`ewR_le_sqrt_ref`). -/
theorem p2R_le_good (L : HonestTable) (hg : GoodL L) :
    p2R (gameR A) L ≤ (advTerm q + verTerm q + (twPR A L + verLin q) ^ (2⁻¹ : ℝ)) ^ 2 + readTerm +
      trialHitMass m0R A L := by
  let : DecidablePred (· ∈ BadRS (S := HPos) L progCap) := badRDec L progCap
  have h := endReads_wGame_trialHit (m₀ := m0R) (A := A) hg.1 rfl (progCalls_gameR hperm hsign L)
  refine h.trans (add_le_add (add_le_add ?_ le_rfl) le_rfl)
  exact ewR_le_sqrt_ref hperm hsign L hg.1.1

/-- **Runtime 2's win probability**, averaged over the table. -/
theorem uavg_p2R_le (hq : q ≤ 2 ^ 64) (d : XmssQrpmDebts q A) :
    uavg (p2R (gameR A)) ≤ eventTerm q := by
  set twg : HonestTable → ℝ≥0∞ := fun L ↦ if GoodL L then twPR A L else 0
  set hitg : HonestTable → ℝ≥0∞ := fun L ↦ if GoodL L then trialHitMass m0R A L else 0
  set bad : HonestTable → ℝ≥0∞ := fun L ↦ if GoodL L then 0 else 1
  have hpt : ∀ L, p2R (gameR A) L ≤
      (advTerm q + verTerm q + (twg L + verLin q) ^ (2⁻¹ : ℝ)) ^ 2 + readTerm + hitg L + bad L := by
    intro L
    by_cases hg : GoodL L
    · simp only [twg, hitg, bad, hg, ↓reduceIte, add_zero]
      exact p2R_le_good hperm hsign L hg
    · simp only [bad, hg, ↓reduceIte]
      exact (QuantumRuntime.outcomeLawWith_le_one _ _ _ _ _ _).trans le_add_self
  have htw : uavg twg ≤ clsBound q := uavg_twPR_le hperm hsign hq d
  have hJ : uavg (fun L ↦ (advTerm q + verTerm q + (twg L + verLin q) ^ (2⁻¹ : ℝ)) ^ 2) ≤
      (advTerm q + verTerm q + (uavg twg + verLin q) ^ (2⁻¹ : ℝ)) ^ 2 := by
    have h := uavg_sq_add_sqrt_le (advTerm q + verTerm q) (fun L ↦ twg L + verLin q)
    rwa [uavg_add, uavg_const] at h
  calc uavg (p2R (gameR A))
      ≤ uavg (fun L ↦ (advTerm q + verTerm q + (twg L + verLin q) ^ (2⁻¹ : ℝ)) ^ 2 + readTerm +
          hitg L + bad L) := uavg_mono hpt
    _ = uavg (fun L ↦ (advTerm q + verTerm q + (twg L + verLin q) ^ (2⁻¹ : ℝ)) ^ 2) + readTerm +
          uavg hitg + uavg bad := by
      rw [uavg_add, uavg_add, uavg_add, uavg_const]
    _ ≤ (advTerm q + verTerm q + (uavg twg + verLin q) ^ (2⁻¹ : ℝ)) ^ 2 + readTerm + trialCap +
          goodTerm :=
      add_le_add (add_le_add (add_le_add hJ le_rfl)
        (uavg_trialHitMass_le_of_good m0R A GoodL fun _ h ↦ ⟨h.2, h.1.1⟩)) uavg_not_goodL_le
    _ ≤ eventTerm q := by
      unfold eventTerm
      gcongr

/-- **The leanXMSS bound for one adversary**, from its debts. -/
theorem winProb_le_qrpmBound (d : XmssQrpmDebts q A) (hq : q ≤ 2 ^ 64) :
    winProb keccakStateEquiv A ≤ qrpmBound q := by
  have hK : uavg (p1T A fullHw) = uavg (p1R A fullHw) :=
    congrArg uavg (funext fun L ↦ (p1T_eq_p1K A tableLe_fullHw L).trans (p1K_eq_p1R A fullHw L))
  calc winProb keccakStateEquiv A = uavg (p1T A fullHw) := winProb_eq_uavg_full A
    _ = uavg (p1R A fullHw) := hK
    _ ≤ (uavg (p2R (gameR A)) ^ (2⁻¹ : ℝ) + hybTerm q) ^ 2 + r0Term := uavg_p1R_le hperm hsign
    _ ≤ (eventTerm q ^ (2⁻¹ : ℝ) + hybTerm q) ^ 2 + r0Term := by
      gcongr
      exact uavg_p2R_le hperm hsign hq d

omit hperm hsign in
/-- The win probability is at most `1`. -/
theorem winProb_le_one (A : Adversary (X × Z)) : winProb keccakStateEquiv A ≤ 1 := by
  rw [winProb_eq_uavg_full A]
  refine (uavg_mono (g := fun _ ↦ (1 : ℝ≥0∞)) fun _ ↦ ?_).trans (uavg_const 1).le
  exact QuantumRuntime.outcomeLawWith_le_one _ _ _ _ _ _

omit hperm hsign in
/-- **Above `2^64` permutation calls the bound is trivial**: the sponge-port hybrid term alone is
`√(4 · 6q · 6q κ) ≥ 12 q 2^-64 ≥ 1`. -/
theorem one_le_qrpmBound (hq : 2 ^ 64 < q) : 1 ≤ qrpmBound q := by
  have h6 : (2 : ℝ≥0∞) ^ 64 ≤ ((6 * q : ℕ) : ℝ≥0∞) := by
    have h : 2 ^ 64 ≤ 6 * q := hq.le.trans (by omega)
    exact_mod_cast h
  have hk : (2 ^ 128 : ℝ≥0∞)⁻¹ ≤ kappaS := by
    unfold kappaS
    exact le_self_add
  have h1 : (1 : ℝ≥0∞) ≤ ((6 * q : ℕ) : ℝ≥0∞) * (((6 * q : ℕ) : ℝ≥0∞) * kappaS) :=
    calc (1 : ℝ≥0∞) = 2 ^ 64 * (2 ^ 64 * (2 ^ 128)⁻¹) := by
          rw [← mul_assoc, ← pow_add, show 64 + 64 = 128 from rfl,
            ENNReal.mul_inv_cancel (by simp) (by simp)]
      _ ≤ _ := by gcongr
  have h2 : 1 ≤ hybTerm q := by
    unfold hybTerm
    refine le_trans ?_ le_self_add
    calc (1 : ℝ≥0∞) = 1 ^ (2⁻¹ : ℝ) := (ENNReal.one_rpow _).symm
      _ ≤ _ := ENNReal.rpow_le_rpow (h1.trans (le_mul_of_one_le_left zero_le (by norm_num)))
          (by norm_num)
  unfold qrpmBound
  exact (one_le_pow₀ (h2.trans le_add_self)).trans le_self_add

omit hperm hsign in
/-- **leanXMSS is quantum SUF-CMA secure in the QRPM** with bound `qrpmBound`, given the open
debts of every adversary within the budgets making at most `2^64` permutation calls (above, the
bound is at least `1`). Conditional: the unconditional theorem constructs the debts. -/
theorem leanXmss_qrpm_security_of_debts
    (hd : ∀ q (A : Adversary (X × Z)),
      (∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q) →
      (∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime) →
      q ≤ 2 ^ 64 → XmssQrpmDebts q A) :
    QuantumStronglyUnforgeable keccakStateEquiv qrpmBound := fun q A hq hs ↦
  if hle : q ≤ 2 ^ 64 then winProb_le_qrpmBound hq hs (hd q A hq hs hle) hle
  else (winProb_le_one A).trans (one_le_qrpmBound (not_le.mp hle))

end proof

/-! ## The Disclose part of the hybrid sum -/

section disclose

/-- **The 128-bit hidden `k`-cells of the canonical game, per call** (Disclose with
`viewByOn_gameT`, through `uavg_hiddenK_digest_runtimeR_le`). For a reparametrization
`e : HonestTable ≃ P × (HPos → Digest)` of the table into public data and the hidden values,
and hidden `k`-cells `HkV p v` each naming an undisclosed position whose value it carries,
the hidden mass of the `j`-th call of the realized template game against `runtimeR`, averaged over
the table, is at most `2^-128`. -/
theorem uavg_hiddenK_digest_le {P : Type} [Fintype P] (A : Adversary (X × Z))
    (e : HonestTable ≃ P × (HPos → Digest)) (pubP : P → Pub)
    (HkV : P → (HPos → Digest) → Set X) (src : P → X → HwReg X Z Mem → HPos)
    (val : P → X → HwReg X Z Mem → Digest)
    (hk : ∀ p v y r, y ∈ HkV p v → r.2.1.2.1 y = none →
      src p y r ∉ r.2.2.1 ∧ v (src p y r) = val p y r) (j : ℕ) :
    uavg (fun L ↦ (runtimeR m0R).queryWeight .instruments
      (extWeight (hiddenMass ∅ (HkV (e L).1 (e L).2) ∅))
      (realizeT (e L).2 (gameT Selections cwUpd (pubP (e L).1) A)) initR j) ≤
        (2 ^ 128 : ℝ≥0∞)⁻¹ :=
  uavg_hiddenK_digest_runtimeR_le e m0R (fun r ↦ r.2.2.1)
    (fun p v ↦ realizeT v (gameT Selections cwUpd (pubP p) A)) (SubState.basis ()) j
    (fun p ↦ viewByOn_gameT Selections cwUpd (pubP p) A m0R initR j) HkV src val hk

end disclose

end Quantum.Xmss.Assembly

end
