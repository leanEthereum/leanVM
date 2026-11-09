module

public import FORS.Scheme.Domains

@[expose] public section

/-!
Exact seed-input parsing and hidden-seed guessing. An input names at most one seed, so it
names a uniform seed with probability at most `2^-256`. In the adaptive guessing experiment the
seed is sampled independently of the strategy's initial state and private randomness, and the
strategy learns only whether each selected input names that seed.
-/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SeedGuess

variable [Params]

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 10000

/-- This complete byte input names the given master seed: a derivation of it, or a hash of
`leanSPHINCS || seed || d` (`PK.seed` at `d = 0`, `SK.prf` at `d = 1`). -/
def SeedHit (input : HashInput) (seed : MasterSeed) : Prop :=
  (∃ parameter domain, keygenHashInput parameter domain seed = input) ∨ ∃ domain, keySeedInput seed domain = input

/-- An input names at most one 256-bit seed. -/
theorem seedHit_unique {input : HashInput} {seed seed' : MasterSeed}
    (h : SeedHit input seed) (h' : SeedHit input seed') : seed = seed' := by
  rcases h with ⟨parameter, domain, rfl⟩ | ⟨domain, rfl⟩ <;>
    rcases h' with ⟨parameter', domain', heq⟩ | ⟨domain', heq⟩
  · exact (keygenInput_injective heq.symm).2.2
  · exact absurd heq (keySeedInput_ne_keygenHashInput _ _ _ _ _)
  · exact absurd heq.symm (keySeedInput_ne_keygenHashInput _ _ _ _ _)
  · exact (bytesLE_injective (List.append_cancel_left (List.append_inj' heq rfl).1)).symm

/-- Exact logical parser for seed inputs. Invalid inputs produce `none`; valid inputs produce the
unique seed whose 32-byte little-endian serialization they carry. -/
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
    Pr{let x ← sampleMasterSeed}[(SeedHit input) x] ≤ 1 / (2 : ℝ≥0∞) ^ 256 := by
  classical
  let := SampleableType.ofFintype MasterSeed
  rw [show sampleMasterSeed = ($ᵗ MasterSeed : ProbComp MasterSeed) from rfl,
    SampleableType.prEvent_uniformSample]
  have hcard : (Finset.univ.filter (SeedHit input)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro seed hseed seed' hseed'
    exact seedHit_unique (Finset.mem_filter.mp hseed).2 (Finset.mem_filter.mp hseed').2
  rw [show Fintype.card MasterSeed = 2 ^ 256 by simp, Nat.cast_pow, Nat.cast_ofNat]
  exact ENNReal.div_le_div_right (by exact_mod_cast hcard) _

end FORS.Security.SeedGuess
