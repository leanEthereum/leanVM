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
public import Quantum.Xmss.Assembly.CostJoint
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
   over ReparamR0's good set `r0G treeQ 18` of the padded table and its bad fraction `2^-174` paid
   once (`r0G_frac_le_keccak`). Sponge ports: `uavg_mask_spongeMass_le_xmssR0` at `r0E`,
   `6q κ` with `κ = kappaS = 2^-128 + 2^-189` (`spongeConst_le_keccak`). Read ports:
   `uavg_mask_readMass_le_xmssR0` at `r0E`, `trialTau q + 2^-117` (`readConst_le_keccak`), the
   randomizer trials' term the debt `htrial`.
3. **End** (PrefixFacts' `endReads_wGame_trialHit`, on the good tables `GoodL = TableGood ∧
   TrialsOff`): the win is at most the event `BadR L progCap` at the end of the game, the read
   error `readTerm` and the trial-hit mass (debt `trialHit`, averaged: `trialCap`).
4. **The event bound** (EventSqrt's `ewR_le_sqrt`, `PermGood`): `(advTerm q + verTerm q +
   √(twP + verLin q))²`, the verification's reads graded like sponge calls and the challenge
   prefix's classical costs `twP` linear.
5. **The prefix's classical costs** (CostLift's `flipCost_le_ports` split, `twP_le`):
   `twP ≤ (√encEpsPre + √massPre)² + progPre`; the prefix calls only `ReadOk` reads
   (`chgB_prefixR`), so its `ε, ε'` flip terms are at most `2^-300` per unit of call weight
   (`epsW_prefixR_le`), at most `clsCap` units (`totalWeight_calls_le`, `clsCalls_prefixR`): `epsCap`.
   The codeword flips are `2^-128 cntPre` (`encW_le_cntW`) with the joint count (debt `encJoint`)
   linear in the recorded mass (debt `restMass`), averaged by CostJoint's `uavg_ite_cost_le`.
   The programs: `progPre ≤ progTot` and ProgSafe's `uavg_progTot_le_kTot` with KeyLazy's
   `uavg_kTot_le` on a reparametrization exposing the keys (debt `keys`): `progBound`.
6. **Good tables**: `PermGood` (`prob_not_permGood_keccak`, `2^-777`), `TrialsOff`
   (`trialsOff_frac_le_keccak`, `2^-173`) and `HonestPathsDisjoint` (debt `pathsDisjoint`).

`qrpmBound q = (√eventTerm + hybTerm)² + 2^-174` with
`eventTerm = (advTerm + verTerm + √(clsBound + verLin))² + readTerm + trialCap + goodTerm` and
`hybTerm = √(4 · 6q · 6q κ) + √(trialTau q + 2^-117)`. For `q > 2^64` the bound is at least `1`
(`one_le_qrpmBound`), so the debts are needed only for `q ≤ 2^64`.

| Debt | Statement | Target | Owner |
|---|---|---|---|
| `htrial` | trials' hidden read mass per public datum (GradedMasked's form) | `trialTau q` | TrialSource |
| `trialHit` | averaged trial-hit mass on `GoodL` | `trialCap = 2^-380` | TrialSource |
| `pathsDisjoint` | fraction of tables without `HonestPathsDisjoint` | `disjCap = 2^-170` | open |
| `encJoint` | `cntPre ≤ encCapA q + encCapB q · massPre` on `GoodL` | | EncPotential |
| `restMass` | averaged `massPre` on `GoodL` | `massCap q` | EncPotential |
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

/-! ## The challenge prefix's costs and the good tables -/

section prefixCosts

attribute [local instance] badRDec

/-- A cost summed along the run of the challenge prefix `prefixR A L` in `runtimeR` (record ports:
`0`). -/
noncomputable def prefixCost (A : Adversary (X × Z))
    (dR : HwRead X Z Mem → Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ → ℝ≥0∞)
    (dP : HwProg X Z → Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ → ℝ≥0∞)
    (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost dR dP)) (prefixR A L) initR

/-- The codeword flips of the selecting reads with the flip terms `ε, ε'` of the other reads,
summed along the prefix. -/
noncomputable def encEpsPre (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  prefixCost A (fun c σ ↦ encW Prod.snd trialUpd (BadR L progCap) L c σ +
    epsW Prod.snd trialUpd (BadR L progCap) L c σ) (fun _ _ ↦ 0) L

/-- The recorded mass of the reads (`massW`), summed along the prefix. -/
noncomputable def massPre (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  prefixCost A (massW Prod.snd trialUpd L) (fun _ _ ↦ 0) L

/-- The state-weighted counts of the selecting reads of all trials of all keys (`cntW`), summed
along the prefix. -/
noncomputable def cntPre (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  prefixCost A (cntW Prod.snd trialUpd L) (fun _ _ ↦ 0) L

/-- The flip costs of the program ports, summed along the prefix. -/
noncomputable def progPre (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  prefixCost A (fun _ _ ↦ 0) (dPof L) L

end prefixCosts

/-- **The good tables of the event side**: EndReads' `TableGood` (`PermGood π 18`, honest paths
sharing no cell) and no top-layer trial block a programmable `k`-cell (`TrialsOff`). -/
def GoodL (L : HonestTable) : Prop :=
  TableGood L ∧ TrialsOff L

/-- The good tables, decided classically. -/
noncomputable instance instDecidablePredGoodL : DecidablePred GoodL :=
  Classical.decPred _

/-! ## The bound -/

/-- The constant part of the joint count of the selecting reads: `2^22 (6q + progCap)`, the
cross-key potential (one per adversary call and per program call) over the codeword rate
`ρ_c ≥ 2^-21`, with a factor `2`. -/
def encCapA (q : ℕ) : ℕ := 2 ^ 22 * (6 * q + progCap)

/-- The recorded-mass factor of the joint count: `3 · 2^22 (6q + progCap)`. -/
def encCapB (q : ℕ) : ℕ := 3 * 2 ^ 22 * (6 * q + progCap)

/-- The codeword flip per unit of the selecting reads' count: `2^-128` (`encW_le_cntW`). -/
noncomputable def encK : ℝ≥0∞ := ENNReal.ofReal (2 ^ 128)⁻¹

/-- The target of the recorded mass of the prefix's reads: `3 · 6q · 2^21 · 2^-128 = 18q · 2^-107`.
A trial's cells are recorded only if the adversary queried the trial's block, which carries the
hidden 128-bit randomizer base plus the trial counter: each adversary entry at a key's message
prefix matches a given trial with probability `2^-128`, the trials of a key weigh at most
`1 / ρ_c ≤ 2^21` (survival), and the `6q` adversary entries are shared among the keys. -/
noncomputable def massCap (q : ℕ) : ℝ≥0∞ :=
  ((18 * q * 2 ^ 21 : ℕ) : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹

/-- The bad fraction of the keys' reparametrization (`keyE_bad_le`): `2^-170`. -/
noncomputable def keyBadCap : ℝ≥0∞ := (2 ^ 170 : ℝ≥0∞)⁻¹

/-- **The programs** (ProgSafe, KeyLazy): `progCap (2^-301 + keyBadCap)`. -/
noncomputable def progBound : ℝ≥0∞ :=
  (2 ^ 301 : ℝ≥0∞)⁻¹ * progCap + progCap * keyBadCap

/-- **The prefix's classical costs**: `(√(2^-128 (encCapA + encCapB massCap) + epsCap) +
√massCap)² + progBound`. -/
noncomputable def clsBound (q : ℕ) : ℝ≥0∞ :=
  ((encK * encCapA q + epsCap + encK * encCapB q * massCap q) ^ (2⁻¹ : ℝ) +
    massCap q ^ (2⁻¹ : ℝ)) ^ 2 + progBound

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

/-- The target of the averaged trial-hit mass (debt `trialHit`): `2^-380`. -/
noncomputable def trialCap : ℝ≥0∞ := (2 ^ 380 : ℝ≥0∞)⁻¹

/-- The bound on runtime 2's win probability. -/
noncomputable def eventTerm (q : ℕ) : ℝ≥0∞ :=
  (advTerm q + verTerm q + (clsBound q + verLin q) ^ (2⁻¹ : ℝ)) ^ 2 + readTerm + trialCap +
    goodTerm

/-- The masked hidden mass per sponge call: `2^-128 + 2^-189` (`spongeConst_le_keccak`). -/
noncomputable def kappaS : ℝ≥0∞ :=
  (2 ^ 128 : ℝ≥0∞)⁻¹ + (2 ^ 189 : ℝ≥0∞)⁻¹

/-- The target of the randomizer trials' hidden read mass per public datum (debt `htrial`):
`clsCap · 2^-460` for fresh trial cells plus `2^-128 massCap q` for trial cells the adversary
recorded (their hidden positions still carry 128-bit hidden digests). -/
noncomputable def trialTau (q : ℕ) : ℝ≥0∞ :=
  (clsCap : ℝ≥0∞) * (2 ^ 460 : ℝ≥0∞)⁻¹ + (2 ^ 128 : ℝ≥0∞)⁻¹ * massCap q

/-- The masked hidden mass at the read ports: `trialTau q + 2^-117` (`readConst_le_keccak`). -/
noncomputable def readCap (q : ℕ) : ℝ≥0∞ :=
  trialTau q + ENNReal.ofReal (1 / 2 ^ 117)

/-- The target of the masked graded hybrid: `√(4 · 6q · μ) + √ν` with the sponge-port mass
`μ = 6q κ` over at most `6q` sponge calls and the read-port mass `ν = readCap q`. -/
noncomputable def hybTerm (q : ℕ) : ℝ≥0∞ :=
  (4 * (((6 * q : ℕ) : ℝ≥0∞) * (((6 * q : ℕ) : ℝ≥0∞) * kappaS))) ^ (2⁻¹ : ℝ) +
    readCap q ^ (2⁻¹ : ℝ)

/-- The bad fraction of ReparamR0's good set, paid once by the masked hybrid: `2^-174`. -/
noncomputable def r0Term : ℝ≥0∞ := ENNReal.ofReal (1 / 2 ^ 174)

/-- **The leanXMSS QRPM bound**: `(√eventTerm + hybTerm)² + 2^-174`. -/
noncomputable def qrpmBound (q : ℕ) : ℝ≥0∞ :=
  (eventTerm q ^ (2⁻¹ : ℝ) + hybTerm q) ^ 2 + r0Term

/-! ## The debts -/

section debts

open scoped Classical in
/-- **The open debts of the leanXMSS QRPM proof**, for an adversary `A` making at most `q`
permutation calls and at most `lifetime` signing requests (needed for `q ≤ 2^64` only: above,
`qrpmBound q ≥ 1`). Every other link is a committed theorem (see the module docstring). -/
structure XmssQrpmDebts (q : ℕ) (A : Adversary (X × Z)) where
  /-- **The randomizer trials' hidden read mass** (GradedMasked's `htrial` at ReparamR0's public
  data): per public datum, summed over the hidden values, the hidden mass of the challenge
  prefix's reads is at most `trialTau q` per hidden value. -/
  htrial : ∀ p : RP, ∑ v : HPos → Digest, (runtimeR m0R).totalWeight .instruments
    (portMass (fun i ↦ readRecPort Selections i = true) (hidH (pubR p) fun s ↦ v (.inl s))
      (hidK (pubR p) fun s ↦ v (.inl s)) (hidK' (pubR p) fun s ↦ v (.inl s)))
    (realizeT v (prefixT Selections cwUpd (pubR p) A)) initR ≤
      trialTau q * Fintype.card (HPos → Digest)
  /-- **The trial-hit mass** (PrefixFacts' `trialHitMass`), averaged over the good tables. -/
  trialHit : uavg (fun L ↦ if GoodL L then trialHitMass m0R A L else 0) ≤ trialCap
  /-- **Honest paths share no cell** except on a fraction `disjCap` of the tables. -/
  pathsDisjoint : uavg (fun L : HonestTable ↦ if HonestPathsDisjoint L then 0 else 1) ≤ disjCap
  /-- **The cross-key potential** on the prefix: the joint count of the selecting reads is at
  most `encCapA q` plus `encCapB q` per unit of recorded mass. -/
  encJoint : ∀ L, GoodL L → cntPre A L ≤ (encCapA q : ℝ≥0∞) + (encCapB q : ℝ≥0∞) * massPre A L
  /-- **The recorded mass** of the prefix's reads, averaged over the good tables. -/
  restMass : uavg (fun L ↦ if GoodL L then massPre A L else 0) ≤ massCap q

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

/-- **The prefix's classical costs** at a table: `(√encEpsPre + √massPre)² + progPre` (CostLift's
per-port split `flipCost_le_ports`, linear along the run, optimized over the split). -/
theorem twP_le (A : Adversary (X × Z)) (L : HonestTable) :
    twP A L ≤ (encEpsPre A L ^ (2⁻¹ : ℝ) + massPre A L ^ (2⁻¹ : ℝ)) ^ 2 + progPre A L :=
  le_sq_add_of_forall_lin fun _ hs ↦ totalWeight_le_lin (runtimeR m0R) .instruments _ _ _ _ _ _
    (extWeight_hwCost_le_lin _ _ _ (fun _ _ ↦ 0) _ _ _ fun c _ hσ ↦ (flipCost_le_ports Prod.snd
      trialUpd (fun m s ↦ (m.1, s)) (fun _ _ ↦ rfl) (BadR L progCap) (N := progCap)
      (fun _ ↦ Iff.rfl) (fun t m v ↦ liftUpd_cases (sel := fun s ↦ cwSel s t.l t.e t.x t.xi v)
        (cwUpd_some t.l t.e t.x t.xi m.2 v)) c hs hσ).trans_eq (add_zero _).symm)
    (prefixR A L) initR_posSemidef

/-- The prefix's program flips are among the game's: `progPre ≤ progTot`. -/
theorem progPre_le_progTot (A : Adversary (X × Z)) (L : HonestTable) :
    progPre A L ≤ progTot A L := by
  unfold progPre progTot prefixCost costTot
  rw [gameR_eq]
  exact totalWeight_le_bind₂ (runtimeR m0R) .instruments _ (prefixR A L) _ initR

/-- **The fraction of the tables off `GoodL`**: at most `goodTerm`. -/
theorem uavg_not_goodL_le {q : ℕ} {A : Adversary (X × Z)} (d : XmssQrpmDebts q A) :
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
  exact add_le_add (add_le_add uavg_not_permGood_le d.pathsDisjoint) uavg_not_trialsOff_le

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

set_option exponentiation.threshold 1024 in
/-- **The masked sponge-port mass** (`uavg_mask_spongeMass_le_xmssR0` at ReparamR0's `r0E`,
`r0G treeQ 18`, SeedStage's seed families): at most `6q · kappaS` over the good set. -/
theorem uavg_mask_spongeMass_le :
    uavg (fun t : HonestTable × RE ↦ if r0G treeQ 18 t then (runtimeR m0R).totalWeight
      .instruments (spongeMass (coverH t.1) (coverK t.1) (coverK' t.1)) (gameR A t.1) initR
        else 0) ≤ ((6 * q : ℕ) : ℝ≥0∞) * kappaS :=
  (uavg_mask_spongeMass_le_xmssR0 cwUpd A hperm hsign m0R initR initR_posSemidef
    ofReal_trace_initR_le_one (Hybrid.querySupportedOn_initR m0R _) r0E (r0G treeQ 18)
    (r0E_injOn treeQ 18) card_r0E_le pubR parR permR 18
    (fun _ ht ↦ hgame_r0E cwUpd A hashesSlots_treeQ ht) (fun _ ht ↦ r0E_hpath hashesSlots_treeQ ht)
    (fun _ ht ↦ r0E_hr0 ht) (fun p k ↦ seedHSlots (permR p) (parR p) k.1 k.2.1)
    (fun p k ↦ seedK'Slots 18 (permR p) (parR p) k.1 k.2.1) (seedEps 18)
    (fun _ ht ↦ r0E_hseed ht) (fun p z ↦ sum_indicator_seedHSlots_le 18 (permR p) (parR p) z)
    (fun p y ↦ sum_indicator_seedK'Slots_le 18 (permR p) (parR p) y)).trans
    (mul_le_mul_of_nonneg_left (spongeConst_le_keccak
      (seedEps_le_keccak.trans (ENNReal.ofReal_le_ofReal (by norm_num)))) zero_le)

set_option exponentiation.threshold 1024 in
/-- **The masked read-port mass** (`uavg_mask_readMass_le_xmssR0` at ReparamR0's `r0E`, with the
trials' term `htrial`): at most `readCap q` over the good set. -/
theorem uavg_mask_readMass_le (d : XmssQrpmDebts q A) :
    uavg (fun t : HonestTable × RE ↦ if r0G treeQ 18 t then (runtimeR m0R).totalWeight
      .instruments (readMass (coverH t.1) (coverK t.1) (coverK' t.1)) (gameR A t.1) initR
        else 0) ≤ readCap q := by
  refine (uavg_mask_readMass_le_xmssR0 cwUpd A hperm hsign m0R initR initR_posSemidef
    ofReal_trace_initR_le_one (Hybrid.querySupportedOn_initR m0R _) r0E (r0G treeQ 18)
    (r0E_injOn treeQ 18) card_r0E_le pubR parR permR 18
    (fun _ ht ↦ hgame_r0E cwUpd A hashesSlots_treeQ ht) (fun _ ht ↦ r0E_hpath hashesSlots_treeQ ht)
    (fun _ ht ↦ r0E_hr0 ht) (fun p k ↦ seedHSlots (permR p) (parR p) k.1 k.2.1)
    (fun p k ↦ seedK'Slots 18 (permR p) (parR p) k.1 k.2.1) (seedEps 18)
    (fun _ ht ↦ r0E_hseed ht) (fun p z ↦ sum_indicator_seedHSlots_le 18 (permR p) (parR p) z)
    (fun p y ↦ sum_indicator_seedK'Slots_le 18 (permR p) (parR p) y) (trialTau q)
    d.htrial).trans ?_
  rw [add_assoc]
  exact add_le_add le_rfl (readConst_le_keccak
    (seedEps_le_keccak.trans (ENNReal.ofReal_le_ofReal (by norm_num))))

/-- **The masked graded hybrid with record ports**, averaged over the table. -/
theorem uavg_p1R_le (d : XmssQrpmDebts q A) :
    uavg (p1R A fullHw) ≤ (uavg (p2R (gameR A)) ^ (2⁻¹ : ℝ) + hybTerm q) ^ 2 + r0Term := by
  refine (uavg_win_runtime1R_le_graded_total_masked_pad .instruments fullHw coverH coverK coverK'
    covers_fullHw m0R (gameR A) (fun _ ↦ SubState.basis ()) (fun _ ↦ winObs)
    (measurableSet_singleton true) (6 * q) (advCalls_gameR hperm hsign) (r0G treeQ 18) _ _
    (uavg_mask_spongeMass_le hperm hsign) (uavg_mask_readMass_le hperm hsign d)).trans ?_
  refine add_le_add (le_of_eq ?_) r0G_frac_le_keccak
  rw [hybTerm, add_assoc]
  rfl

/-- **The codeword flips and the other reads' flip terms of the prefix** at a `PermGood` table, for
`q ≤ 2^64`: at most `2^-128 cntPre + epsCap` (`encW_le_cntW`; `epsW_prefixR_le`: the prefix calls
only `ReadOk` reads; at most `clsCap` classical calls). -/
theorem encEpsPre_le (hq : q ≤ 2 ^ 64) (L : HonestTable) (hπ : PermGood L.perm 18) :
    encEpsPre A L ≤ encK * cntPre A L + epsCap := by
  refine (totalWeight_le_add (runtimeR m0R) .instruments _ _ _ _ 1
    (extWeight_hwCost_le_add _ _ _ _ _ fun c _ hσ ↦ add_le_add
      (encW_le_cntW Prod.snd trialUpd (BadR L progCap) L c hσ) (one_mul _).ge)
    (prefixR A L) initR_posSemidef).trans ?_
  rw [one_mul]
  refine add_le_add le_rfl ((epsW_prefixR_le hperm hsign hq L hπ).trans ?_)
  unfold epsCap
  rw [mul_comm]
  gcongr
  exact totalWeight_calls_le (prefixR A L) (clsCalls_prefixR hperm hsign L)

/-- **The programs**, averaged over the good tables: ProgSafe's `uavg_progTot_le_kTot` with
KeysReparam's `uavg_kTot_le_r0` (KeyLazy on ReparamR0's reparametrization, keys split off). -/
theorem uavg_progPre_le (hq : q ≤ 2 ^ 64) :
    uavg (fun L ↦ if GoodL L then progPre A L else 0) ≤ progBound := by
  have hk := uavg_kTot_le_r0 hperm hsign hq
  refine (uavg_mono fun L ↦ ?_).trans ((uavg_progTot_le_kTot hk).trans ?_)
  · by_cases hg : GoodL L
    · rw [ite_eq_left hg, ite_eq_left hg.1.1]
      exact progPre_le_progTot A L
    · rw [ite_eq_right hg]
      exact zero_le
  · unfold progBound keyBadCap
    exact le_rfl

/-- **The prefix's classical costs**, averaged over the good tables (CostJoint's
`uavg_ite_cost_le`): at most `clsBound q`. -/
theorem uavg_twP_le (hq : q ≤ 2 ^ 64) (d : XmssQrpmDebts q A) :
    uavg (fun L ↦ if GoodL L then twP A L else 0) ≤ clsBound q := by
  have htw : ∀ L, GoodL L → twP A L ≤ ((encK * cntPre A L + epsCap) ^ (2⁻¹ : ℝ) +
      massPre A L ^ (2⁻¹ : ℝ)) ^ 2 + progPre A L := fun L hg ↦
    (twP_le A L).trans (add_le_add (pow_le_pow_left₀ zero_le (add_le_add
      (ENNReal.rpow_le_rpow (encEpsPre_le hperm hsign hq L hg.1.1) (by norm_num)) le_rfl) 2)
      le_rfl)
  have hE : ∀ L, GoodL L → encK * cntPre A L + epsCap ≤
      (encK * encCapA q + epsCap) + encK * encCapB q * massPre A L := fun L hg ↦
    calc encK * cntPre A L + epsCap
        ≤ encK * ((encCapA q : ℝ≥0∞) + (encCapB q : ℝ≥0∞) * massPre A L) + epsCap := by
          gcongr
          exact d.encJoint L hg
      _ = (encK * encCapA q + epsCap) + encK * encCapB q * massPre A L := by ring
  exact uavg_ite_cost_le htw hE d.restMass (uavg_progPre_le hperm hsign hq)

/-- **Runtime 2's win at a good table** (PrefixFacts' `endReads_wGame_trialHit`, EventSqrt's
`ewR_le_sqrt`). -/
theorem p2R_le_good (L : HonestTable) (hg : GoodL L) :
    p2R (gameR A) L ≤ (advTerm q + verTerm q + (twP A L + verLin q) ^ (2⁻¹ : ℝ)) ^ 2 + readTerm +
      trialHitMass m0R A L := by
  let : DecidablePred (· ∈ BadRS (S := HPos) L progCap) := badRDec L progCap
  have h := endReads_wGame_trialHit (m₀ := m0R) (A := A) hg.1 rfl (progCalls_gameR hperm hsign L)
  refine h.trans (add_le_add (add_le_add ?_ le_rfl) le_rfl)
  exact ewR_le_sqrt hperm hsign L hg.1.1

/-- **Runtime 2's win probability**, averaged over the table. -/
theorem uavg_p2R_le (hq : q ≤ 2 ^ 64) (d : XmssQrpmDebts q A) :
    uavg (p2R (gameR A)) ≤ eventTerm q := by
  set twg : HonestTable → ℝ≥0∞ := fun L ↦ if GoodL L then twP A L else 0
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
  have htw : uavg twg ≤ clsBound q := uavg_twP_le hperm hsign hq d
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
      add_le_add (add_le_add (add_le_add hJ le_rfl) d.trialHit) (uavg_not_goodL_le d)
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
    _ ≤ (uavg (p2R (gameR A)) ^ (2⁻¹ : ℝ) + hybTerm q) ^ 2 + r0Term := uavg_p1R_le hperm hsign d
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
