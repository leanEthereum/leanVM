module

public import Quantum.Sphincs.Assembly.Stream
public import Quantum.Sphincs.Assembly.WinDecomp
public import Quantum.Sphincs.Assembly.EventRef
public import Quantum.Sphincs.Assembly.EncRefined
public import Quantum.Sphincs.Assembly.RecOffDecHit
public import Quantum.Sphincs.Assembly.CwReFail
public import Quantum.Sphincs.Assembly.KeyLazy
public import Quantum.Sphincs.Assembly.TrialHitUniform
public import Quantum.Sphincs.Assembly.HConflict
public import Quantum.Sphincs.CoverStream

@[expose] public section

/-!
# leanSPHINCS's event side, averaged

leanXMSS's `uavg_p2R_le` (`Quantum.Xmss.Assembly.Security`) for leanSPHINCS's event-side game
`gameR strPol A p v` at template data `(p, v)`: for fixed `PK.seed`, `π` with `PermGood π 18` and
`h`, averaged over the keys `(k, k')` and the hidden values `v` (the keys are averaged because
KeyLazy's fresh `k`, `k'` flips are), the win probability `p2R strPol` is at most an explicit
`eventTermS q ε` plus twice the fraction of the data off the good set `GoodES`.

* **Jensen and averages over products** (`uavg_sq_add_sqrt_add_sqrt_le`, `uavg_prod_iter`,
  `uavg_fst_marg`, `uavg_snd_marg`).
* **The coverage price** (`strSplit`, `uavg_price_coverOf_le`): the hidden values split into the
  stream coordinates and the rest, so the averaged price of `S★(v)` is CoverStream's
  `rhoCov / 2^128`.
* **The fresh bounds linearized in the price** (`advTerm_add_verTerm_le`, `verLin_le_es`):
  `advTerm + verTerm ≤ advA q + √(advB q² · covRate v)` and `verLin ≤ verLinS + 3 verifyBlocks ·
  covRate v`, with `covRate v = 2^16 price S★(v)`.
* **The win at good data** (`p2R_le_goodES`): WinDecomp's `endReads_wGame_trialHit` with
  EventRef's `ewR_le_sqrt_ref_sph`.
* **The classical costs averaged** (`uavg_twPR_le_es`): CostRefined's `twPR_le`, EncRefined's
  `encE_le`, CwRev's `uavg_cwRecPre_le_rev` (given `CwReView`), RecBadMass's
  `recBadAvg_of_parts` with RecOffDecHit's `decHitAvg`, `recOffAvg`, RecJ's `uavg_recJPre_le`,
  KeyLazy's `uavg_kfPre_le`, `uavg_kW_le` and ProgSafe's `progW_le_kW_gameT`.
* **The bound** (`uavg_p2R_le_es`), with TrialHitUniform's trial-hit mass and HConflict's
  `uavg_hConflictMassP_le`; with CwReFail's `cwReView_cf` (`ε = cfEps = 2^-157`) without
  hypothesis on the failed searches (`uavg_p2R_le_es'`, `uavg_p2R_msgPol_le_es'`).
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message PublicParameter)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (uavg uavg_mono uavg_add uavg_const_mul)
open Quantum.Xmss.Assembly (runtimeR realizeT keepCost extWeight kapRR uavg_sq_rpow_add_le
  uavg_const_le uavg_const pow_two_rpow_inv_two totalWeight_le_bind₂)

namespace Quantum.Sphincs.Assembly

/-! ## Averages -/

section avg

/-- **Jensen for `(a + √g + √f)²`**: the average is at most `(a + √(E g) + √(E f))²`. -/
theorem uavg_sq_add_sqrt_add_sqrt_le {Θ : Type*} [Fintype Θ] (a : ℝ≥0∞) (g f : Θ → ℝ≥0∞) :
    uavg (fun θ ↦ (a + g θ ^ (2⁻¹ : ℝ) + f θ ^ (2⁻¹ : ℝ)) ^ 2) ≤
      (a + uavg g ^ (2⁻¹ : ℝ) + uavg f ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hc : uavg (fun _ : Θ ↦ a ^ 2) ^ (2⁻¹ : ℝ) ≤ a :=
    (ENNReal.rpow_le_rpow (uavg_const_le _) (by norm_num)).trans_eq (pow_two_rpow_inv_two a)
  have hs : uavg (fun θ ↦ (g θ ^ (2⁻¹ : ℝ) + f θ ^ (2⁻¹ : ℝ)) ^ 2) ^ (2⁻¹ : ℝ) ≤
      uavg g ^ (2⁻¹ : ℝ) + uavg f ^ (2⁻¹ : ℝ) :=
    (ENNReal.rpow_le_rpow (uavg_sq_rpow_add_le g f) (by norm_num)).trans_eq
      (pow_two_rpow_inv_two _)
  calc uavg (fun θ ↦ (a + g θ ^ (2⁻¹ : ℝ) + f θ ^ (2⁻¹ : ℝ)) ^ 2)
      = uavg (fun θ ↦ ((a ^ 2) ^ (2⁻¹ : ℝ) +
          ((g θ ^ (2⁻¹ : ℝ) + f θ ^ (2⁻¹ : ℝ)) ^ 2) ^ (2⁻¹ : ℝ)) ^ 2) :=
        congrArg uavg (funext fun θ ↦ by
          rw [pow_two_rpow_inv_two, pow_two_rpow_inv_two, add_assoc])
    _ ≤ (uavg (fun _ : Θ ↦ a ^ 2) ^ (2⁻¹ : ℝ) +
          uavg (fun θ ↦ (g θ ^ (2⁻¹ : ℝ) + f θ ^ (2⁻¹ : ℝ)) ^ 2) ^ (2⁻¹ : ℝ)) ^ 2 :=
        uavg_sq_rpow_add_le (fun _ ↦ a ^ 2) fun θ ↦ (g θ ^ (2⁻¹ : ℝ) + f θ ^ (2⁻¹ : ℝ)) ^ 2
    _ ≤ (a + (uavg g ^ (2⁻¹ : ℝ) + uavg f ^ (2⁻¹ : ℝ))) ^ 2 :=
        pow_le_pow_left₀ zero_le (add_le_add hc hs) 2
    _ = _ := by rw [add_assoc]

/-- **The average over a product is the iterated average.** -/
theorem uavg_prod_iter {K V : Type*} [Fintype K] [Fintype V] (g : K × V → ℝ≥0∞) :
    uavg g = uavg (fun k ↦ uavg (fun v ↦ g (k, v))) := by
  unfold uavg
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
    mul_assoc, Finset.mul_sum]

/-- The average of a function of the first coordinate. -/
theorem uavg_fst_marg {K V : Type*} [Fintype K] [Fintype V] [Nonempty V] (F : K → ℝ≥0∞) :
    uavg (fun θ : K × V ↦ F θ.1) = uavg F := by
  rw [uavg_prod_iter]
  exact congrArg uavg (funext fun k ↦ uavg_const (F k))

/-- The average of a function of the second coordinate. -/
theorem uavg_snd_marg {K V : Type*} [Fintype K] [Nonempty K] [Fintype V] (F : V → ℝ≥0∞) :
    uavg (fun θ : K × V ↦ F θ.2) = uavg F := by
  rw [uavg_prod_iter]
  exact uavg_const (uavg F)

/-- **The averaged guarded classical costs** (leanXMSS's `uavg_ite_cost_le_add`): if on `good`
the total `tw ≤ (√E + √m)² + p` and `E ≤ E₀ + β m + γ r`, and the averages over `good` of `m`, `r`
and `p` are at most `mc`, `rc` and `pc`, the average over `good` of `tw` is at most
`(√(E₀ + β mc + γ rc) + √mc)² + pc`. -/
theorem uavg_ite_cost_le_add_sph {Θ : Type*} [Fintype Θ] {good : Θ → Prop} [DecidablePred good]
    {tw E m p r : Θ → ℝ≥0∞} {E₀ β γ mc pc rc : ℝ≥0∞}
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

/-- A guarded sum averaged is at most the sum of the guarded averages. -/
theorem uavg_ite_add_le {Θ : Type*} [Fintype Θ] {good : Θ → Prop} [DecidablePred good]
    {f g : Θ → ℝ≥0∞} {a b : ℝ≥0∞} (hf : uavg (fun θ ↦ if good θ then f θ else 0) ≤ a)
    (hg : uavg (fun θ ↦ if good θ then g θ else 0) ≤ b) :
    uavg (fun θ ↦ if good θ then f θ + g θ else 0) ≤ a + b := by
  refine (uavg_mono (g := fun θ ↦ (if good θ then f θ else 0) + if good θ then g θ else 0)
    fun θ ↦ ?_).trans ?_
  · by_cases hθ : good θ
    · rw [ite_eq_left hθ, ite_eq_left hθ, ite_eq_left hθ]
    · rw [ite_eq_right hθ, ite_eq_right hθ, ite_eq_right hθ, add_zero]
  · rw [uavg_add]
    exact add_le_add hf hg

end avg

/-! ## The coverage price over the hidden values -/

section cover

/-- The stream coordinates. -/
def isStr : HPos → Bool
  | .str _ _ => true
  | _ => false

/-- Hidden values from stream entries and the other coordinates. -/
def strJoin (t : Fin signatureLimit × DigestCall → HashOutput)
    (r : (s : {s : HPos // isStr s = false}) → XD s.1) : (s : HPos) → XD s
  | .val p => r ⟨.val p, rfl⟩
  | .rnd M => r ⟨.rnd M, rfl⟩
  | .dig M i => r ⟨.dig M i, rfl⟩
  | .str j i => t (j, i)
  | .asg M j => r ⟨.asg M j, rfl⟩

/-- **The hidden values as the stream and the rest.** -/
def strSplit : ((s : HPos) → XD s) ≃
    (Fin signatureLimit × DigestCall → HashOutput) ×
      ((s : {s : HPos // isStr s = false}) → XD s.1) where
  toFun v := (fun ji ↦ v (.str ji.1 ji.2), fun s ↦ v s.1)
  invFun w := strJoin w.1 w.2
  left_inv v := funext fun s ↦ by cases s <;> rfl
  right_inv w := by
    refine Prod.ext (funext fun _ ↦ rfl) (funext fun s ↦ ?_)
    obtain ⟨s, hs⟩ := s
    cases s with
    | val p => rfl
    | rnd M => rfl
    | dig M i => rfl
    | str j i => simp [isStr] at hs
    | asg M j => rfl

/-- **The averaged price of the static coverage set** `S★(v)` over the hidden values: at most
`rhoCov / 2^128` (CoverStream's `uavg_price_streamPairs_le`). -/
theorem uavg_price_coverOf_le :
    uavg (fun v : (s : HPos) → XD s ↦ ENNReal.ofReal (price (coverOf v))) ≤
      ENNReal.ofReal (rhoCov / 2 ^ 128) := by
  have h := uavg_comp_equiv strSplit
    (fun w ↦ ENNReal.ofReal (price (streamCover (streamOfPairs w.1))))
  rw [uavg_fst_marg (fun t ↦ ENNReal.ofReal (price (streamCover (streamOfPairs t))))] at h
  exact (le_of_eq h).trans uavg_price_streamPairs_le

end cover

/-! ## The fresh bounds linearized in the price -/

section fresh

/-- The fresh rate's constant part at Keccak sizes: `2^-128 + 2 · 2^-302`. -/
noncomputable def freshK : ℝ≥0∞ :=
  (2 ^ 128)⁻¹ + 2 * (2 ^ 302 : ℝ≥0∞)⁻¹

/-- The coverage part of the fresh rates: `2^16 price S★(v)`. -/
noncomputable def covRate (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 ^ 16 * price (coverOf v) : ℚ) : ℝ)

/-- The averaged coverage part: `2^16 rhoCov / 2^128`. -/
noncomputable def covPS : ℝ≥0∞ :=
  2 ^ 16 * ENNReal.ofReal (rhoCov / 2 ^ 128)

/-- The price-free part of `advTerm + verTerm`: `6q √(6 freshK) + 3 verifyBlocks √freshK`. -/
noncomputable def advA (q : ℕ) : ℝ≥0∞ :=
  ((6 * q : ℕ) : ℝ≥0∞) * (6 * freshK) ^ (2⁻¹ : ℝ) +
    ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * freshK ^ (2⁻¹ : ℝ)

/-- The factor of `√covRate` in `advTerm + verTerm`: `6q √6 + 3 verifyBlocks`. -/
noncomputable def advB (q : ℕ) : ℝ≥0∞ :=
  ((6 * q : ℕ) : ℝ≥0∞) * 6 ^ (2⁻¹ : ℝ) + ((3 * verifyBlocks : ℕ) : ℝ≥0∞)

/-- The price-free part of `verLin`: `3 verifyBlocks (freshK + 2/|X| + 2/|Z|)`. -/
noncomputable def verLinS : ℝ≥0∞ :=
  ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * keepCost X Z freshK

theorem covRate_eq_price (v : (s : HPos) → XD s) :
    covRate v = 2 ^ 16 * ENNReal.ofReal (price (coverOf v)) := by
  unfold covRate
  push_cast
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

/-- **The averaged coverage part**, over the keys and the hidden values: at most `covPS`. -/
theorem uavg_covRate_le :
    uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦ covRate θ.2) ≤ covPS := by
  rw [uavg_snd_marg covRate, show covRate = fun v ↦ 2 ^ 16 * ENNReal.ofReal (price (coverOf v))
    from funext covRate_eq_price, uavg_const_mul]
  exact mul_le_mul_of_nonneg_left uavg_price_coverOf_le zero_le

theorem keepCost_add (a b : ℝ≥0∞) : keepCost X Z (a + b) = keepCost X Z a + b := by
  unfold keepCost
  rw [add_right_comm a b, add_right_comm (a + _) b]

theorem keepCost_mono {a b : ℝ≥0∞} (h : a ≤ b) : keepCost X Z a ≤ keepCost X Z b := by
  unfold keepCost
  gcongr

variable {q : ℕ}

/-- **`advTerm + verTerm` linearized in the price**: for `q ≤ 2^64`,
`advTerm v q + verTerm v q ≤ advA q + √(advB q² · covRate v)`. -/
theorem advTerm_add_verTerm_le (hq : q ≤ 2 ^ 64) (v : (s : HPos) → XD s) :
    advTerm v q + verTerm v q ≤ advA q + (advB q ^ 2 * covRate v) ^ (2⁻¹ : ℝ) := by
  have hh : (0 : ℝ) ≤ 2⁻¹ := by norm_num
  have h1 : ∀ n ∈ Finset.range (6 * q), (6 * advEps v n) ^ (2⁻¹ : ℝ) ≤
      (6 * freshK) ^ (2⁻¹ : ℝ) + 6 ^ (2⁻¹ : ℝ) * covRate v ^ (2⁻¹ : ℝ) := fun n hn ↦ by
    have he : advEps v n ≤ freshK + covRate v :=
      advEps_le_keccak v hq (Finset.mem_range.mp hn)
    calc (6 * advEps v n) ^ (2⁻¹ : ℝ) ≤ (6 * freshK + 6 * covRate v) ^ (2⁻¹ : ℝ) := by
          rw [← mul_add]
          exact ENNReal.rpow_le_rpow (mul_le_mul_of_nonneg_left he zero_le) hh
      _ ≤ (6 * freshK) ^ (2⁻¹ : ℝ) + (6 * covRate v) ^ (2⁻¹ : ℝ) :=
          ENNReal.rpow_add_le_add_rpow _ _ hh (by norm_num)
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg (6 : ℝ≥0∞) (covRate v) hh]
  have hadv : advTerm v q ≤ ((6 * q : ℕ) : ℝ≥0∞) *
      ((6 * freshK) ^ (2⁻¹ : ℝ) + 6 ^ (2⁻¹ : ℝ) * covRate v ^ (2⁻¹ : ℝ)) := by
    unfold advTerm
    refine (Finset.sum_le_sum h1).trans_eq ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hver : verTerm v q ≤ ((3 * verifyBlocks : ℕ) : ℝ≥0∞) *
      (freshK ^ (2⁻¹ : ℝ) + covRate v ^ (2⁻¹ : ℝ)) := by
    unfold verTerm
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    exact (ENNReal.rpow_le_rpow (verEps_le_keccak v hq) hh).trans
      (ENNReal.rpow_add_le_add_rpow _ _ hh (by norm_num))
  rw [ENNReal.mul_rpow_of_nonneg _ _ hh, pow_two_rpow_inv_two]
  refine (add_le_add hadv hver).trans_eq ?_
  unfold advA advB
  ring

/-- **`verLin` linearized in the price**: for `q ≤ 2^64`,
`verLin v q ≤ verLinS + 3 verifyBlocks · covRate v`. -/
theorem verLin_le_es (hq : q ≤ 2 ^ 64) (v : (s : HPos) → XD s) :
    verLin v q ≤ verLinS + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * covRate v := by
  unfold verLin verLinS
  rw [← mul_add, ← keepCost_add]
  exact mul_le_mul_of_nonneg_left (keepCost_mono (verEps_le_keccak v hq)) zero_le

end fresh

/-! ## The good data and the constants -/

section good

/-- The public data at `PK.seed`, `π`, `h` and the keys `(k, k')`. -/
def pubES (par : PublicParameter) (perm : Equiv.Perm (X × Z)) (hk : Z → X)
    (kk : (X → Z) × (X → Z)) : Pub :=
  ⟨par, perm, (hk, kk.1, kk.2)⟩

/-- **The good data of the event side** at keys and hidden values `θ = ((k, k'), v)`: HConflict's
`HZLoad` (a property of the keys), PrefixFacts' `PathsDisjoint`, `HmsgSep`, `HmsgHSep`,
HConflict's `HSelfSep`, `TrialsOff` and ProgSafe's `NoHmsgHead` (static: no adversary; the
prefix's calls stay inside RecJ's `keyHw` for every adversary, `staysInR_keyHw`). -/
structure GoodES (par : PublicParameter) (perm : Equiv.Perm (X × Z)) (hk : Z → X)
    (θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s)) : Prop where
  load : HZLoad (pubES par perm hk θ.1)
  disj : PathsDisjoint (pubES par perm hk θ.1).xw (pubES par perm hk θ.1).keys.1 (valsOf θ.2)
  sep : HmsgSep (pubES par perm hk θ.1) θ.2
  hsep : HmsgHSep (pubES par perm hk θ.1) θ.2
  self : HSelfSep (pubES par perm hk θ.1) θ.2
  off : TrialsOff (pubES par perm hk θ.1).xw (pubES par perm hk θ.1).keys.1 (valsOf θ.2)
  head : NoHmsgHead (pubES par perm hk θ.1) θ.2

/-- `GoodES`, decided classically. -/
noncomputable instance instDecidablePredGoodES (par : PublicParameter)
    (perm : Equiv.Perm (X × Z)) (hk : Z → X) :
    DecidablePred (GoodES par perm hk) :=
  Classical.decPred _

/-- `Bad (evData p v) N`, decided as CostRun's `BadR`. -/
@[instance_reducible]
noncomputable def badDecES (p : Pub) (v : (s : HPos) → XD s) (N : ℕ) :
    DecidablePred (· ∈ Bad (S := HPos) (evData p v) N) :=
  badRDec p v N

/-- **The averaged fresh `k`, `k'` flips** (KeyLazy): `2^-301 progCap`. -/
noncomputable def kfCapS : ℝ≥0∞ :=
  (2 ^ 301)⁻¹ * progCap

/-- **The averaged `RecBad` mass** (`recBadAvg_of_parts` with `decHitAvg` and `recOffAvg`):
`2 · 2^-121 + recConv + 2/|Z| · clsCap`. -/
noncomputable def recBadCapS : ℝ≥0∞ :=
  2 * ENNReal.ofReal (1 / 2 ^ 121) + recConv + ENNReal.ofReal (2 / Fintype.card Z) * clsCap

/-- **The averaged flip-value recorded mass** `cwRecPre + recBadPre`, with the failed-search bound
`ε` of `CwReView`. -/
noncomputable def flipCapS (q : ℕ) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  cwRevTau q ε + recBadCapS

/-- **The averaged prefix costs** (`twPR_le`, `encE_le`): `(√(encEC q + 2 encBeta q · flipCapS +
2 encGamma q (kfCapS + recCapS q kfCapS)) + √flipCapS)² + kfCapS`. -/
noncomputable def clsBoundS (q : ℕ) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  ((encEC q + 2 * encBeta q * flipCapS q ε + 2 * encGamma q * (kfCapS + recCapS q kfCapS)) ^
    (2⁻¹ : ℝ) + flipCapS q ε ^ (2⁻¹ : ℝ)) ^ 2 + kfCapS

/-- **leanSPHINCS's event term**: `(advA q + √(advB q² covPS) + √(clsBoundS q ε + verLinS +
3 verifyBlocks covPS))²`, the verification's read error, the trial-hit mass `2^-189` and the
conflict cap `hConflictCap N`. -/
noncomputable def eventTermS (q : ℕ) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  (advA q + (advB q ^ 2 * covPS) ^ (2⁻¹ : ℝ) +
    (clsBoundS q ε + (verLinS + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * covPS)) ^ (2⁻¹ : ℝ)) ^ 2 +
    ENNReal.ofReal (readError X Z verifyBlocks verifyBlocks verifyBlocks) +
      ENNReal.ofReal (1 / 2 ^ 189) + ENNReal.ofReal (hConflictCap signatureLimit)

end good

/-! ## The bound -/

section proof

attribute [local instance] badDecES

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

set_option synthInstance.maxSize 2000 in
/-- **The win at good data** (WinDecomp's `endReads_wGame_trialHit`, EventRef's
`ewR_le_sqrt_ref_sph`): at `PermGood π 18`, with disjoint honest paths, `HmsgSep`, `HmsgHSep`,
`p2R strPol ≤ (advTerm + verTerm + √(twPR + verLin))² + readError + trialHitMass +
hConflictMass`. -/
theorem p2R_le_goodES (p : Pub) (v : (s : HPos) → XD s) (hπ : PermGood p.perm 18)
    (hpd : PathsDisjoint p.xw p.keys.1 (valsOf v)) (hsepK : HmsgSep p v)
    (hsepH : HmsgHSep p v) :
    p2R strPol A p v ≤ (advTerm v q + verTerm v q +
      (twPR strPol A p v + verLin v q) ^ (2⁻¹ : ℝ)) ^ 2 +
        ENNReal.ofReal (readError X Z verifyBlocks verifyBlocks verifyBlocks) +
          trialHitMass m0R A p v + hConflictMass m0R A p v := by
  have h := @endReads_wGame_trialHit m0R A p v (badRDec p v progCap) hpd hsepK hsepH
    (fun _ _ h ↦ Finset.notMem_empty _ h) rfl (progCalls_gameR hperm hsign strPol p v)
  exact h.trans (add_le_add (add_le_add (add_le_add
    (ewR_le_sqrt_ref_sph hperm hsign strPol p v hπ) le_rfl) le_rfl) le_rfl)

omit hperm hsign in
/-- The prefix's program flips are among the game's. -/
theorem progPreR_le_progW_es (p : Pub) (v : (s : HPos) → XD s) :
    progPreR strPol A p v ≤ progW (Bad (S := HPos) (evData p v) progCap) m0R
      (realizeT v (gameT Selections cwUpd strPol p A)) initR := by
  have h := totalWeight_le_bind₂ (runtimeR m0R) .instruments
    (extWeight (hwCost (fun _ _ ↦ 0) (dPof p v))) (prefixR strPol A p v)
    (fun x ↦ realizeT v (verifyT Selections p x)) initR
  rw [← gameR_eq] at h
  exact h

variable (par : PublicParameter) (perm : Equiv.Perm (X × Z)) (hk : Z → X)
  (hπ : PermGood perm 18)
include hπ

set_option synthInstance.maxSize 2000 in
/-- **The averaged fresh flips of the game** (KeyLazy's `uavg_kW_le`), over the keys and the
hidden values, on the good data: at most `kfCapS`. -/
theorem uavg_kW_goodES (hq : q ≤ 2 ^ 64) :
    uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦ if GoodES par perm hk θ then
      kW (Bad (S := HPos) (evData (pubES par perm hk θ.1) θ.2) progCap) m0R
        (realizeT θ.2 (gameT Selections cwUpd strPol (pubES par perm hk θ.1) A)) initR
      else 0) ≤ kfCapS := by
  have h := uavg_kW_le hperm hsign (Q := Unit) (fun _ ↦ par) (fun _ ↦ perm) (fun _ ↦ hk)
    (fun _ w ↦ w) (fun θ ↦ GoodES par perm hk θ.2) (fun _ _ ↦ hπ) (progCap_add_le hq) cwUpd
    strPol
  exact (uavg_snd_marg (K := Unit) _).symm.trans_le h

set_option synthInstance.maxSize 2000 in
/-- **The averaged target-free fresh flips of the prefix** (KeyLazy's `uavg_kfPre_le`), on the
good data: at most `kfCapS`. -/
theorem uavg_kfPre_goodES :
    uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦ if GoodES par perm hk θ then
      kfPre strPol A (pubES par perm hk θ.1) θ.2 else 0) ≤ kfCapS := by
  have h := uavg_kfPre_le hperm hsign (Q := Unit) (fun _ ↦ par) (fun _ ↦ perm) (fun _ ↦ hk)
    (fun _ w ↦ w) (fun θ ↦ GoodES par perm hk θ.2) (fun _ _ ↦ hπ) strPol
  exact (uavg_snd_marg (K := Unit) _).symm.trans_le h

set_option synthInstance.maxSize 2000 in
/-- **The averaged program flips of the prefix** (ProgSafe's `progW_le_kW_gameT` with
`uavg_kW_goodES`): at most `kfCapS`. -/
theorem uavg_progPreR_goodES (hq : q ≤ 2 ^ 64) :
    uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦ if GoodES par perm hk θ then
      progPreR strPol A (pubES par perm hk θ.1) θ.2 else 0) ≤ kfCapS := by
  refine uavg_ite_le_of_le _ (fun θ hθ ↦ ?_) (uavg_kW_goodES hperm hsign par perm hk hπ hq)
  refine (progPreR_le_progW_es (A := A) (pubES par perm hk θ.1) θ.2).trans ?_
  have hρ := querySupportedOn_init_keyHeld (pubES par perm hk θ.1) m0R (A := QReg.of Unit)
    (SubState.basis ()).matrix
  exact progW_le_kW_gameT progCap cwUpd strPol (pubES par perm hk θ.1) θ.2 A m0R hθ.head
    initR_posSemidef hρ

omit hπ in
open scoped Classical in
set_option synthInstance.maxSize 2000 in
/-- **The averaged codeword-recorded mass** (CwRev's `uavg_cwRecPre_le_rev`), given the failed
searches `CwReView` at every pair of keys: at most `cwRevTau q ε`. -/
theorem uavg_cwRecPre_goodES {ε : ℝ≥0∞}
    (hre : ∀ kk, CwReView strPol A (pubES par perm hk kk) ε) :
    uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦ if GoodES par perm hk θ then
      cwRecPre strPol A (pubES par perm hk θ.1) θ.2 else 0) ≤ cwRevTau q ε := by
  refine (uavg_mono (g := fun θ ↦ if TrialsOff (pubES par perm hk θ.1).xw
    (pubES par perm hk θ.1).keys.1 (valsOf θ.2) then cwRecPre strPol A (pubES par perm hk θ.1) θ.2
      else 0) fun θ ↦ ?_).trans ?_
  · by_cases hg : GoodES par perm hk θ
    · rw [ite_eq_left hg, ite_eq_left hg.off]
    · rw [ite_eq_right hg]
      exact zero_le
  rw [uavg_prod_iter]
  exact (uavg_mono fun kk ↦ uavg_cwRecPre_le_rev hperm hsign strPol _ (hre kk)).trans
    (uavg_const_le _)

set_option synthInstance.maxSize 2000 in
/-- **The averaged flip-value recorded mass** on the good data: at most `flipCapS q ε`. -/
theorem uavg_flipMass_goodES {ε : ℝ≥0∞}
    (hre : ∀ kk, CwReView strPol A (pubES par perm hk kk) ε) :
    uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦ if GoodES par perm hk θ then
      cwRecPre strPol A (pubES par perm hk θ.1) θ.2 + recBadPre strPol A (pubES par perm hk θ.1) θ.2
      else 0) ≤ flipCapS q ε := by
  have hb : RecBadAvg strPol A (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦
      pubES par perm hk θ.1) (fun θ ↦ θ.2) (GoodES par perm hk) recBadCapS :=
    recBadAvg_of_parts hperm hsign strPol _ _ _
      (decHitAvg hperm hsign strPol _ _ _ fun _ hθ ↦ ⟨hθ.off, hπ⟩)
      (recOffAvg hperm hsign strPol _ _ _)
  exact uavg_ite_add_le (uavg_cwRecPre_goodES hperm hsign par perm hk hre) hb

set_option synthInstance.maxSize 2000 in
/-- **The prefix's refined classical costs averaged** over the good data (`twPR_le`, `encE_le`,
`uavg_ite_cost_le_add_sph`): at most `clsBoundS q ε`. -/
theorem uavg_twPR_le_es (hq : q ≤ 2 ^ 64) {ε : ℝ≥0∞}
    (hre : ∀ kk, CwReView strPol A (pubES par perm hk kk) ε) :
    uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦ if GoodES par perm hk θ then
      twPR strPol A (pubES par perm hk θ.1) θ.2 else 0) ≤ clsBoundS q ε := by
  have hkf := uavg_kfPre_goodES hperm hsign par perm hk hπ
  have hrj := uavg_recJPre_le hperm hsign hq strPol
    (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦ pubES par perm hk θ.1) (fun θ ↦ θ.2)
    (GoodES par perm hk) (fun _ _ ↦ hπ) hkf
  have htw : ∀ θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s), GoodES par perm hk θ →
      twPR strPol A (pubES par perm hk θ.1) θ.2 ≤
        ((2 * encRPre strPol A (pubES par perm hk θ.1) θ.2 +
          hwMovePre strPol A (pubES par perm hk θ.1) θ.2 +
            ENNReal.ofReal kapRR * (clsCap : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
          (cwRecPre strPol A (pubES par perm hk θ.1) θ.2 +
            recBadPre strPol A (pubES par perm hk θ.1) θ.2) ^ (2⁻¹ : ℝ)) ^ 2 +
          progPreR strPol A (pubES par perm hk θ.1) θ.2 := fun θ _ ↦
    twPR_le hperm hsign hq strPol (pubES par perm hk θ.1) θ.2 hπ
  have hE : ∀ θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s), GoodES par perm hk θ →
      2 * encRPre strPol A (pubES par perm hk θ.1) θ.2 +
          hwMovePre strPol A (pubES par perm hk θ.1) θ.2 +
            ENNReal.ofReal kapRR * (clsCap : ℝ≥0∞) ≤
        encEC q + 2 * encBeta q * (cwRecPre strPol A (pubES par perm hk θ.1) θ.2 +
            recBadPre strPol A (pubES par perm hk θ.1) θ.2) +
          2 * encGamma q * (kfPre strPol A (pubES par perm hk θ.1) θ.2 +
            recJPre strPol A (pubES par perm hk θ.1) θ.2) := fun θ _ ↦
    encE_le (pubES par perm hk θ.1) θ.2 hperm hsign hq strPol hπ
  exact uavg_ite_cost_le_add_sph htw hE (uavg_flipMass_goodES hperm hsign par perm hk hπ hre)
    (uavg_ite_add_le hkf hrj) (uavg_progPreR_goodES hperm hsign par perm hk hπ hq)

omit hperm hπ in
open scoped Classical in
set_option synthInstance.maxSize 2000 in
/-- **The averaged conflict mass** (HConflict's `uavg_hConflictMassP_le` at every pair of keys
with `HZLoad`): at most `hConflictCap N` plus the fraction of the data off `GoodES`. -/
theorem uavg_hConflict_goodES :
    uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦ if GoodES par perm hk θ then
      hConflictMass m0R A (pubES par perm hk θ.1) θ.2 else 0) ≤
      ENNReal.ofReal (hConflictCap signatureLimit) +
        uavg (fun θ ↦ if GoodES par perm hk θ then (0 : ℝ≥0∞) else 1) := by
  refine (uavg_mono (g := fun θ ↦ if HZLoad (pubES par perm hk θ.1) then
    hConflictMassP ((∅ : Finset HPos), m0) A (pubES par perm hk θ.1) θ.2 else 0)
    fun θ ↦ ?_).trans ?_
  · by_cases hg : GoodES par perm hk θ
    · rw [ite_eq_left hg, ite_eq_left hg.load]
      rfl
    · rw [ite_eq_right hg]
      exact zero_le
  rw [uavg_prod_iter, uavg_prod_iter (fun θ ↦ if GoodES par perm hk θ then (0 : ℝ≥0∞) else 1),
    ← uavg_const (Θ := (X → Z) × (X → Z)) (ENNReal.ofReal (hConflictCap signatureLimit)),
    ← uavg_add]
  refine uavg_mono fun kk ↦ ?_
  by_cases hl : HZLoad (pubES par perm hk kk)
  · simp only [ite_eq_left hl]
    refine (uavg_hConflictMassP_le hl m0 A hsign).trans (add_le_add le_rfl (uavg_mono fun v ↦ ?_))
    by_cases hs : HmsgSep (pubES par perm hk kk) v ∧ HSelfSep (pubES par perm hk kk) v
    · rw [ite_eq_left hs]
      exact zero_le
    · rw [ite_eq_right hs, ite_eq_right fun hg ↦ hs ⟨hg.sep, hg.self⟩]
  · simp only [ite_eq_right hl]
    exact (uavg_const_le 0).trans zero_le

set_option synthInstance.maxSize 2000 in
/-- **leanSPHINCS's event side, averaged** (leanXMSS's `uavg_p2R_le`): for an adversary with at
most `q ≤ 2^64` permutation and `signatureLimit` signing queries, for every `PK.seed`, every `π`
with `PermGood π 18` and every `h`, given the failed searches `CwReView ε` at every pair of keys,
the win probability of the event-side game `p2R strPol`, averaged over the keys `(k, k')` and the
hidden values `v`, is at most `eventTermS q ε` plus twice the fraction of the data off `GoodES`. -/
theorem uavg_p2R_le_es (hq : q ≤ 2 ^ 64) {ε : ℝ≥0∞}
    (hre : ∀ kk, CwReView strPol A (pubES par perm hk kk) ε) :
    uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦
      p2R strPol A (pubES par perm hk θ.1) θ.2) ≤
      eventTermS q ε + 2 * uavg (fun θ ↦ if GoodES par perm hk θ then (0 : ℝ≥0∞) else 1) := by
  set G := GoodES par perm hk
  set twg : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) → ℝ≥0∞ := fun θ ↦
    if G θ then twPR strPol A (pubES par perm hk θ.1) θ.2 else 0
  set hitg : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) → ℝ≥0∞ := fun θ ↦
    if G θ then trialHitMass m0R A (pubES par perm hk θ.1) θ.2 else 0
  set hcg : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) → ℝ≥0∞ := fun θ ↦
    if G θ then hConflictMass m0R A (pubES par perm hk θ.1) θ.2 else 0
  set bad : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) → ℝ≥0∞ := fun θ ↦ if G θ then 0 else 1
  set gg : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) → ℝ≥0∞ := fun θ ↦ advB q ^ 2 * covRate θ.2
  set ff : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) → ℝ≥0∞ := fun θ ↦
    twg θ + (verLinS + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * covRate θ.2)
  set rdT : ℝ≥0∞ := ENNReal.ofReal (readError X Z verifyBlocks verifyBlocks verifyBlocks)
  have hpt : ∀ θ, p2R strPol A (pubES par perm hk θ.1) θ.2 ≤
      (advA q + gg θ ^ (2⁻¹ : ℝ) + ff θ ^ (2⁻¹ : ℝ)) ^ 2 + rdT + hitg θ + hcg θ + bad θ := by
    intro θ
    by_cases hg : G θ
    · simp only [twg, hitg, hcg, bad, ff, gg, ite_eq_left hg, add_zero]
      refine (p2R_le_goodES hperm hsign _ θ.2 hπ hg.disj hg.sep hg.hsep).trans
        (add_le_add (add_le_add (add_le_add (pow_le_pow_left₀ zero_le (add_le_add
          (advTerm_add_verTerm_le hq θ.2) (ENNReal.rpow_le_rpow (add_le_add le_rfl
            (verLin_le_es hq θ.2)) (by norm_num))) 2) le_rfl) le_rfl) le_rfl)
    · simp only [bad, ite_eq_right hg]
      exact (QuantumRuntime.outcomeLawWith_le_one _ _ _ _ _ _).trans le_add_self
  have hJ := uavg_sq_add_sqrt_add_sqrt_le (advA q) gg ff
  have hgg : uavg gg ≤ advB q ^ 2 * covPS := by
    simp only [gg]
    rw [uavg_const_mul]
    exact mul_le_mul_of_nonneg_left uavg_covRate_le zero_le
  have hff : uavg ff ≤ clsBoundS q ε + (verLinS + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * covPS) := by
    simp only [ff]
    rw [uavg_add, uavg_add, uavg_const, uavg_const_mul]
    exact add_le_add (uavg_twPR_le_es hperm hsign par perm hk hπ hq hre)
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left uavg_covRate_le zero_le))
  have hhit : uavg hitg ≤ ENNReal.ofReal (1 / 2 ^ 189) := by
    refine (uavg_mono fun θ ↦ ?_).trans (uavg_const_le (ENNReal.ofReal (1 / 2 ^ 189)))
    by_cases hg : G θ
    · simp only [hitg, ite_eq_left hg]
      exact trialHitMassAt_le_keccak strPol m0R A hg.off hπ
    · simp only [hitg, ite_eq_right hg]
      exact zero_le
  have hhc : uavg hcg ≤ ENNReal.ofReal (hConflictCap signatureLimit) + uavg bad :=
    uavg_hConflict_goodES hsign par perm hk
  calc uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦
        p2R strPol A (pubES par perm hk θ.1) θ.2)
      ≤ uavg (fun θ ↦ (advA q + gg θ ^ (2⁻¹ : ℝ) + ff θ ^ (2⁻¹ : ℝ)) ^ 2 + rdT + hitg θ +
          hcg θ + bad θ) := uavg_mono hpt
    _ = uavg (fun θ ↦ (advA q + gg θ ^ (2⁻¹ : ℝ) + ff θ ^ (2⁻¹ : ℝ)) ^ 2) + rdT + uavg hitg +
          uavg hcg + uavg bad := by
        rw [uavg_add, uavg_add, uavg_add, uavg_add, uavg_const]
    _ ≤ (advA q + (advB q ^ 2 * covPS) ^ (2⁻¹ : ℝ) + (clsBoundS q ε +
          (verLinS + ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * covPS)) ^ (2⁻¹ : ℝ)) ^ 2 + rdT +
          ENNReal.ofReal (1 / 2 ^ 189) +
          (ENNReal.ofReal (hConflictCap signatureLimit) + uavg bad) + uavg bad := by
        refine add_le_add (add_le_add (add_le_add (add_le_add (hJ.trans ?_) le_rfl) hhit) hhc)
          le_rfl
        exact pow_le_pow_left₀ zero_le (add_le_add (add_le_add le_rfl
          (ENNReal.rpow_le_rpow hgg (by norm_num))) (ENNReal.rpow_le_rpow hff (by norm_num))) 2
    _ = eventTermS q ε + 2 * uavg bad := by
        unfold eventTermS
        ring

set_option synthInstance.maxSize 2000 in
/-- **The event side at `msgPol`** (Stream's `uavg_p2R_msgPol_eq_strPol` at every pair of keys,
then `uavg_p2R_le_es`). -/
theorem uavg_p2R_msgPol_le_es (hq : q ≤ 2 ^ 64) {ε : ℝ≥0∞}
    (hre : ∀ kk, CwReView strPol A (pubES par perm hk kk) ε) :
    uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦
      p2R msgPol A (pubES par perm hk θ.1) θ.2) ≤
      eventTermS q ε + 2 * uavg (fun θ ↦ if GoodES par perm hk θ then (0 : ℝ≥0∞) else 1) := by
  have e : ∀ kk : (X → Z) × (X → Z), uavg (p2R msgPol A (pubES par perm hk kk)) =
      uavg (p2R strPol A (pubES par perm hk kk)) := fun kk ↦ uavg_p2R_msgPol_eq_strPol A _
  have h := uavg_p2R_le_es hperm hsign par perm hk hπ hq hre
  rw [uavg_prod_iter] at h ⊢
  exact (congrArg uavg (funext e)).trans_le h

set_option synthInstance.maxSize 2000 in
/-- **leanSPHINCS's event side, averaged, without hypothesis on the failed searches**
(`uavg_p2R_le_es` with CwReFail's `cwReView_cf`, `ε = cfEps = 2^-157`). -/
theorem uavg_p2R_le_es' (hq : q ≤ 2 ^ 64) :
    uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦
      p2R strPol A (pubES par perm hk θ.1) θ.2) ≤
      eventTermS q cfEps +
        2 * uavg (fun θ ↦ if GoodES par perm hk θ then (0 : ℝ≥0∞) else 1) :=
  uavg_p2R_le_es hperm hsign par perm hk hπ hq fun _ ↦
    cwReView_cf hperm hsign strPol valFree_strPol _ hπ

set_option synthInstance.maxSize 2000 in
/-- **The event side at `msgPol`, without hypothesis on the failed searches**
(`uavg_p2R_msgPol_le_es` with `cwReView_cf`). -/
theorem uavg_p2R_msgPol_le_es' (hq : q ≤ 2 ^ 64) :
    uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦
      p2R msgPol A (pubES par perm hk θ.1) θ.2) ≤
      eventTermS q cfEps +
        2 * uavg (fun θ ↦ if GoodES par perm hk θ then (0 : ℝ≥0∞) else 1) :=
  uavg_p2R_msgPol_le_es hperm hsign par perm hk hπ hq fun _ ↦
    cwReView_cf hperm hsign strPol valFree_strPol _ hπ

end proof

end Quantum.Sphincs.Assembly

end
