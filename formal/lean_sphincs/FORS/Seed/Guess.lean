import FORS.Scheme.Domains

/-!
Exact derivation-input parsing and hidden-seed guessing. An input names at most one seed, so it
names a uniform seed with probability at most `2^-256`. In the adaptive guessing experiment the
seed is sampled independently of the strategy's initial state and private randomness, and the
strategy learns only whether each selected input names that seed.
-/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SeedGuess

variable [Params]

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 10000

/-- This complete byte input is a candidate derivation query naming the given master seed. -/
def SeedHit (input : HashInput) (seed : MasterSeed) : Prop :=
  ∃ parameter domain, keygenHashInput parameter domain seed = input

/-- Whatever derivation address an input uses, it can name at most one 256-bit seed. -/
theorem seedHit_unique {input : HashInput} {seed seed' : MasterSeed}
    (h : SeedHit input seed) (h' : SeedHit input seed') : seed = seed' := by
  obtain ⟨parameter, domain, heq⟩ := h
  obtain ⟨parameter', domain', heq'⟩ := h'
  exact (keygenInput_injective (heq.trans heq'.symm)).2.2

/-- Exact logical parser for derivation inputs. Invalid inputs produce `none`; valid inputs
produce the unique seed whose actual 32-byte little-endian serialization occupies the payload. -/
noncomputable def parseSeed (input : HashInput) : Option MasterSeed :=
  if h : ∃ seed, SeedHit input seed then some (Classical.choose h) else none

theorem parseSeed_eq_some_iff (input : HashInput) (seed : MasterSeed) :
    parseSeed input = some seed ↔ SeedHit input seed := by
  classical
  unfold parseSeed
  split
  next h =>
    constructor
    · intro heq
      cases Option.some.inj heq
      exact Classical.choose_spec h
    · intro hseed
      exact congrArg some (seedHit_unique (Classical.choose_spec h) hseed)
  next h =>
    constructor
    · simp
    · intro hseed
      exact False.elim (h ⟨seed, hseed⟩)

/-- Each fixed byte input contributes at most one equality guess against a uniform hidden seed. -/
theorem seedHit_probability_le (input : HashInput) :
    Pr[SeedHit input | sampleMasterSeed] ≤ 1 / (2 : ℝ≥0∞) ^ 256 := by
  classical
  letI := SampleableType.ofFintype MasterSeed
  rw [show sampleMasterSeed = ($ᵗ MasterSeed : ProbComp MasterSeed) from rfl,
    probEvent_uniformSample]
  have hcard : (Finset.univ.filter (SeedHit input)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro seed hseed seed' hseed'
    exact seedHit_unique (Finset.mem_filter.mp hseed).2 (Finset.mem_filter.mp hseed').2
  rw [show Fintype.card MasterSeed = 2 ^ 256 by simp, Nat.cast_pow, Nat.cast_ofNat]
  exact ENNReal.div_le_div_right (by exact_mod_cast hcard) _

/-- An adaptive query choice and its state transition after an equality-oracle reply. -/
structure Trial (σ : Type) where
  input : HashInput
  next : Bool → σ

end FORS.Security.SeedGuess
