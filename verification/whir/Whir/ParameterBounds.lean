import Whir.GroupedChallenges
import Whir.CodingBounds
import Whir.FieldCardinality
import Whir.JohnsonListNumerics
import Whir.JohnsonNumerics

/-! Exact, unground production-profile accounting. These deliberately conservative
bounds do not assert the source tests' floating-point 128-bit target. All 56
profiles are read from `Protocol.productionConfig`; no table is copied here.

The exact rational envelope gives query miss probability at most 2^-80, a
Johnson list cap 2^32, and the exact BCHKS25 numerator cap 2^108. The actual
`GroupedChallenges` ledger then gives grouped-message loss at most 2^-79 and
interactive loss at most 2^-73 for at most 2^64 initial claims. Ring switching,
authentication, Fiat–Shamir, and proof of work are not included in these totals. -/
namespace Whir.ParameterBounds
open Whir.Protocol Whir.CausalGame Whir.GroupedChallenges
open scoped BigOperators

/-- All 56 supported production configurations, without a copied source table. -/
abbrev Profile := Fin 14 × Fin 4

def config (p : Profile) : Config :=
  (productionConfig (p.1.val + 15) (p.2.val + 1)).getD default

/-- Rational upper envelope of the square root of the nominal rate. -/
def upper (r : Nat) : ℚ :=
  (if r % 2 = 0 then 1 else 3 / 4) / 2 ^ (r / 2)

def alpha (r : Nat) : ℚ := (129 / 128) * upper r

def dimension (c : Config) (i : Nat) : Nat := 2 ^ remaining c i

def length (c : Config) (i : Nat) : Nat := 2 ^ (remaining c i + c.rates[i]!)

def rho (c : Config) (i : Nat) : ℚ :=
  (dimension c i - 1 : Nat) / (length c i : ℚ)

/-- Arithmetic certificate; every conjunct is checked on the actual integer ladder. -/
def LevelFacts (c : Config) (i : Nat) : Prop :=
  0 < dimension c i - 1 ∧ dimension c i - 1 < length c i ∧
  length c i ≤ 2^26 ∧ (1 / 2^26 : ℚ) ≤ rho c i ∧
  rho c i ≤ (upper c.rates[i]!)^2 ∧
  0 < upper c.rates[i]! ∧ 0 < alpha c.rates[i]! ∧ alpha c.rates[i]! < 1 ∧
  rho c i / 64 ≤ (alpha c.rates[i]!)^2 - rho c i ∧
  (alpha c.rates[i]!) ^ c.queries[i]! ≤ (1 / 2^80 : ℚ)

instance (c : Config) (i : Nat) : Decidable (LevelFacts c i) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel computation, not native evaluation or the floating-point source test. -/
theorem production_level_facts :
    ∀ p : Profile, ∀ i : Fin (config p).folds.size, LevelFacts (config p) i := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem production_config_valid : ∀ p : Profile,
    (config p).valid = true ∧ 0 < (config p).folds.size ∧
    (config p).folds.size ≤ 6 ∧
    (productionConfig (p.1.val + 15) (p.2.val + 1)).isSome = true := by
  decide +kernel

/-- Conservatively relaxed analytic estimates, attached to the actual rate array. -/
def estimates (c : Config) : Estimates c := fun i =>
  ⟨2^32, 2^108, alpha c.rates[i.val]!⟩

/-- The challenge field cardinality is exact, not a security assumption. -/
theorem field_cardinality : (Fintype.card Concrete.E : ℚ) = fieldSize := by
  rw [FieldModel.card_E]
  norm_num [fieldSize]

/-- The initial powers-batch loss remains explicit in the number of claims. -/
theorem initialBatch_le_claims (c : Config) (claims : Nat) :
    initialBatch c (estimates c) claims ≤ (claims : ℚ) / 2^160 := by
  unfold initialBatch
  split_ifs
  · simp only [estimates, fieldSize]
    calc
      _ ≤ (claims : ℚ) * (2^32 : Nat) / (2:ℚ)^192 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast Nat.sub_le claims 1
      _ = _ := by norm_num; ring
  · positivity

theorem initialBatch_le (c : Config) (claims : Nat) (hclaims : claims ≤ 2^64) :
    initialBatch c (estimates c) claims ≤ (1 / 2^96 : ℚ) := by
  calc
    _ ≤ (claims : ℚ) / 2^160 := initialBatch_le_claims c claims
    _ ≤ (2^64 : ℚ) / 2^160 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hclaims
    _ = _ := by norm_num

def LevelLedgerFacts (c : Config) (i : Fin c.folds.size) : Prop :=
  foldError c (estimates c) i ≤ (1 / 2^83 : ℚ) ∧
  oodError c (estimates c) i ≤ (1 / 2^123 : ℚ) ∧
  queryBatchError c (estimates c) i ≤ (1 / 2^79 : ℚ)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem production_level_ledger :
    ∀ p : Profile, ∀ i : Fin (config p).folds.size, LevelLedgerFacts (config p) i := by
  unfold LevelLedgerFacts oodError
  simp only [estimates, Nat.choose_two_right]
  decide +kernel

theorem initialBatch_mono (c : Config) {a b : Nat} (h : a ≤ b) :
    initialBatch c (estimates c) a ≤ initialBatch c (estimates c) b := by
  unfold initialBatch
  split_ifs
  · apply div_le_div_of_nonneg_right _ (by norm_num [fieldSize])
    apply mul_le_mul_of_nonneg_right _ (by norm_num [estimates])
    exact_mod_cast Nat.sub_le_sub_right h 1
  · exact le_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Whole interactive and grouped-message ledgers, before ring switching and
without subtracting any grinding budget. -/
theorem production_ledger_at_claim_cap : ∀ p : Profile,
    interactiveError (config p) (estimates (config p)) (2^64) ≤ (1 / 2^73 : ℚ) ∧
    groupedMaximum (config p) (estimates (config p)) (2^64) ≤ (1 / 2^79 : ℚ) := by
  unfold interactiveError groupedMaximum oodError
  simp only [estimates, Nat.choose_two_right]
  decide +kernel

theorem production_interactive (p : Profile) (claims : Nat) (hclaims : claims ≤ 2^64) :
    interactiveError (config p) (estimates (config p)) claims ≤ (1 / 2^73 : ℚ) := by
  apply le_trans _ (production_ledger_at_claim_cap p).1
  unfold interactiveError
  exact add_le_add (add_le_add (initialBatch_mono _ hclaims) le_rfl) le_rfl

theorem production_grouped (p : Profile) (claims : Nat) (hclaims : claims ≤ 2^64) :
    groupedMaximum (config p) (estimates (config p)) claims ≤ (1 / 2^79 : ℚ) := by
  apply le_trans _ (production_ledger_at_claim_cap p).2
  unfold groupedMaximum
  exact max_le_max (initialBatch_mono _ hclaims) le_rfl

/-- Each supplied in-range size/rate is represented in the finite family. -/
theorem supported_config {logN rate : Nat} (hn : 15 ≤ logN ∧ logN ≤ 28)
    (hr : 1 ≤ rate ∧ rate ≤ 4) :
    ∃ p : Profile, p.1.val + 15 = logN ∧ p.2.val + 1 = rate ∧
      productionConfig logN rate = some (config p) := by
  let p : Profile := (⟨logN - 15, by omega⟩, ⟨rate - 1, by omega⟩)
  have hp : p.1.val + 15 = logN := by dsimp [p]; omega
  have hq : p.2.val + 1 = rate := by dsimp [p]; omega
  refine ⟨p, hp, hq, ?_⟩
  have h := (production_config_valid p).2.2.2
  rw [hp, hq] at h
  cases hc : productionConfig logN rate with
  | none => simp [hc] at h
  | some c => simp [config, hp, hq, hc]

/-- Rational envelope transfer: positive Johnson slack with multiplicity budget 128. -/
theorem production_sqrt_envelope (p : Profile) (i : Fin (config p).folds.size) :
    0 < (rho (config p) i : ℝ) ∧
    (1 / 2^26 : ℝ) ≤ (rho (config p) i : ℝ) ∧
    (rho (config p) i : ℝ) < 1 ∧
    0 < (alpha (config p).rates[i.val]! : ℝ) ∧
    (alpha (config p).rates[i.val]! : ℝ) < 1 ∧
    Real.sqrt (rho (config p) i : ℝ) ≤
      (128 / 129 : ℝ) * (alpha (config p).rates[i.val]! : ℝ) := by
  obtain ⟨hd, hdn, hn, hr, hu, hup, ha, ha1, hgap, hq⟩ := production_level_facts p i
  have hr' : (1 / 2^26 : ℝ) ≤ (rho (config p) i : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr hr
  have hrp : 0 < (rho (config p) i : ℝ) := lt_of_lt_of_le (by norm_num) hr'
  have hu' : (rho (config p) i : ℝ) ≤ (upper (config p).rates[i.val]! : ℝ)^2 := by
    exact_mod_cast hu
  have hup' : 0 < (upper (config p).rates[i.val]! : ℝ) := by exact_mod_cast hup
  have ha' : 0 < (alpha (config p).rates[i.val]! : ℝ) := by exact_mod_cast ha
  have ha1' : (alpha (config p).rates[i.val]! : ℝ) < 1 := by exact_mod_cast ha1
  have hscale : (alpha (config p).rates[i.val]! : ℝ) =
      (129 / 128 : ℝ) * (upper (config p).rates[i.val]! : ℝ) := by
    simp [alpha]
  have hs : Real.sqrt (rho (config p) i : ℝ) ≤
      (upper (config p).rates[i.val]! : ℝ) := by
    nlinarith [Real.sq_sqrt hrp.le, Real.sqrt_nonneg (rho (config p) i : ℝ)]
  refine ⟨hrp, hr', ?_, ha', ha1', ?_⟩
  · nlinarith
  · nlinarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The adjacent powers-batch charge is inside, not outside, its grouped query
message. Subtracting the query miss term isolates the actual ledger summand. -/
theorem production_adjacent_batch : ∀ p : Profile, ∀ i : Fin (config p).folds.size,
    0 ≤ queryBatchError (config p) (estimates (config p)) i -
      (alpha (config p).rates[i.val]!) ^ (config p).queries[i.val]! ∧
    queryBatchError (config p) (estimates (config p)) i -
      (alpha (config p).rates[i.val]!) ^ (config p).queries[i.val]! ≤
        (1 / 2^152 : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem production_tail : ∀ p : Profile,
    ((config p).logN - (config p).folds.toList.sum : Nat) *
      (2 / fieldSize) ≤ (1 / 2^188 : ℚ) := by
  decide +kernel

def threshold (c : Config) (i : Nat) : Nat :=
  ⌈(length c i : ℚ) * alpha c.rates[i]!⌉₊

/-- Actual interleaved candidate lists on every production-sized domain obey the
relaxed list cap. The only domain premise identifies the encoder's block length. -/
theorem production_candidates_card
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {lanes : Nat}
    (p : Profile) (i : Fin (config p).folds.size)
    (domain : Finset F) (hdom : domain.card = length (config p) i)
    (oracle : ↥domain → Fin lanes → F) :
    (CodingBounds.candidates
      (fun v : Fin lanes → Fin (dimension (config p) i) → F =>
        fun x : ↥domain => CodingBounds.interleavedEncode v x)
      oracle (threshold (config p) i)).card ≤ 2^32 := by
  obtain ⟨hd, hdn, hn, hr, hu, hup, ha, ha1, hgap, hq⟩ := production_level_facts p i
  apply JohnsonListNumerics.interleaved_candidates_card_le_two_pow32 domain oracle
    (threshold (config p) i) (by omega) (by omega) (by omega)
    (rho (config p) i) (alpha (config p).rates[i.val]!)
  · simp [rho, hdom]
  · exact hr
  · exact ha.le
  · exact hgap
  · rw [hdom]
    exact Nat.le_ceil _

@[simp] theorem rho_cast (c : Config) (i : Nat) :
    (rho c i : ℝ) = ((dimension c i - 1 : Nat) : ℝ) / length c i := by
  simp [rho]

def radius (c : Config) (i : Nat) : ℝ := 1 - (alpha c.rates[i]! : ℝ)

/-- Positive radius strictly below the reduced-rate Johnson radius. -/
theorem production_radius (p : Profile) (i : Fin (config p).folds.size) :
    0 < radius (config p) i ∧
      radius (config p) i < 1 - Real.sqrt (rho (config p) i : ℝ) := by
  obtain ⟨hr, hrl, hru, ha, ha1, hgap⟩ := production_sqrt_envelope p i
  unfold radius
  constructor <;> nlinarith

theorem production_multiplicity (p : Profile) (i : Fin (config p).folds.size) :
    max ⌈Real.sqrt (rho (config p) i : ℝ) /
      (1 - Real.sqrt (rho (config p) i : ℝ) - radius (config p) i)⌉₊ 3 ≤ 128 := by
  obtain ⟨hr, hrl, hru, ha, ha1, hgap⟩ := production_sqrt_envelope p i
  exact MutualAgreement.johnson_multiplicity_le_128 _ _ ha hgap

/-- Instantiation of the exact, square-root/ceiling BCHKS25 expression. -/
theorem production_johnsonNumerator (p : Profile) (i : Fin (config p).folds.size) :
    MutualAgreement.johnsonNumerator (length (config p) i) (dimension (config p) i)
      (radius (config p) i) ≤ (2 : ℝ)^108 := by
  obtain ⟨hr, hrl, hru, ha, ha1, hgap⟩ := production_sqrt_envelope p i
  simp only [rho_cast] at hr hrl hru hgap
  exact MutualAgreement.johnsonNumerator_le_two_pow_108 _ _ _ hr hrl hru.le
    (production_level_facts p i).2.2.1 ha ha1 hgap

/-- The ledger result stated directly for the actual production constructor,
with only supported input ranges and the caller's claim-count limit. -/
theorem supported_ledger {logN rate : Nat} {c : Config}
    (hn : 15 ≤ logN ∧ logN ≤ 28) (hr : 1 ≤ rate ∧ rate ≤ 4)
    (hc : productionConfig logN rate = some c) (claims : Nat)
    (hclaims : claims ≤ 2^64) :
    interactiveError c (estimates c) claims ≤ (1 / 2^73 : ℚ) ∧
    groupedMaximum c (estimates c) claims ≤ (1 / 2^79 : ℚ) := by
  obtain ⟨p, hp, hq, hconfig⟩ := supported_config hn hr
  have h : c = config p := Option.some.inj (hc.symm.trans hconfig)
  subst c
  exact ⟨production_interactive p claims hclaims, production_grouped p claims hclaims⟩

end Whir.ParameterBounds
