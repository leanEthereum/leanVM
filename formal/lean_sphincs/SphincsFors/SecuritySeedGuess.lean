import SphincsFors.SecurityDomains
import SphincsFors.Uniform

/-!
Exact derivation-input parsing and hidden-seed guessing. An input names at most one seed, so it
names a uniform seed with probability at most `2^-256`. In the adaptive guessing experiment the
seed is sampled independently of the strategy's initial state and private randomness, and the
strategy learns only whether each selected input names that seed.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsFors.Security.SeedGuess

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

theorem parseSeed_keygen (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    parseSeed (keygenHashInput parameter domain seed) = some seed :=
  (parseSeed_eq_some_iff _ _).2 ⟨parameter, domain, rfl⟩

/-- Verifier inputs can never be mistaken for derivation inputs, even across public parameters. -/
theorem parseSeed_verifier (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    parseSeed (tweakableHashInput parameter domain payload) = none := by
  cases h : parseSeed (tweakableHashInput parameter domain payload) with
  | none => rfl
  | some seed =>
      obtain ⟨parameter', domain', heq⟩ := (parseSeed_eq_some_iff _ _).1 h
      exact False.elim (keygenInput_ne_hashInput parameter' parameter domain' domain seed payload heq)

/-- Each fixed byte input contributes at most one equality guess against a uniform hidden seed. -/
theorem seedHit_probability_le (input : HashInput) :
    Pr{let x ← sampleMasterSeed}[(SeedHit input) x] ≤ 1 / (2 : ℝ≥0∞) ^ 256 := by
  classical
  letI := SampleableType.ofFintype MasterSeed
  rw [show sampleMasterSeed = ($ᵗ MasterSeed : ProbComp MasterSeed) from rfl,
    SampleableType.prEvent_uniformSample]
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

/-- Private random choices depend on prior state, never directly on the hidden seed. -/
abbrev Strategy (σ : Type) := σ → ProbComp (Option (Trial σ))

/-- At most `q` adaptive equality guesses. The strategy sees each failed guess, and stops on the
first success. The input is parsed using the actual candidate derivation layouts. -/
noncomputable def monitor {σ : Type} (choose : Strategy σ) (seed : MasterSeed) :
    Nat → σ → ProbComp Bool
  | 0, _ => pure false
  | q + 1, state => do
      let some trial ← choose state | return false
      if parseSeed trial.input = some seed then return true
      else monitor choose seed q (trial.next false)

/-- The hidden seed is sampled once and retained for every adaptive guess. -/
noncomputable def experiment {σ : Type} (choose : Strategy σ) (q : Nat) (state : σ) : ProbComp Bool :=
  sampleMasterSeed >>= fun seed => monitor choose seed q state

end SphincsFors.Security.SeedGuess
