module

public import FORS.Reduction.InternalizeGame

@[expose] public section

/-! The graph-view cost program of the deterministic-randomizer game. The randomizer base
`R0` of a message is read from a table `rnd` of full hash outputs indexed by message; its one
derivation hash call is charged as a one-unit tick, so the cost program preserves the joint law of output and original
hash cost whenever `rnd` holds the answers at `SK.prf`'s randomizer-derivation inputs. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.Det

variable [Params]

open Concrete Completeness Prefix HiddenGraph SeedCoupling GraphView

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Randomizer-base derivation outputs (`R0`), by message. -/
abbrev RTable := Message → HashOutput

/-- One half of every randomizer derivation output, by message: the base randomizers, or the step
halves. -/
abbrev LTable := Message → Randomness

/-- The hash output whose low half is `low` and whose high half is `high`. -/
def joinHalves (low high : Digest) : HashOutput :=
  BitVec.ofNat hashOutputBits (high.toNat * 2 ^ digestBits + low.toNat)

theorem joinHalves_toNat (low high : Digest) :
    (joinHalves low high).toNat = high.toNat * 2 ^ 128 + low.toNat := by
  have hl : low.toNat < 2 ^ 128 := low.isLt
  have hh : high.toNat < 2 ^ 128 := high.isLt
  rw [joinHalves, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by simp only [hashOutputBits, digestBits]; omega)

theorem truncateHash_joinHalves (low high : Digest) : truncateHash (joinHalves low high) = low := by
  apply BitVec.eq_of_toNat_eq
  rw [truncateHash, BitVec.extractLsb'_toNat, joinHalves_toNat, Nat.shiftRight_zero]
  show (high.toNat * 2 ^ 128 + low.toNat) % 2 ^ 128 = low.toNat
  have hl : low.toNat < 2 ^ 128 := low.isLt
  omega

theorem upperHash_joinHalves (low high : Digest) : upperHash (joinHalves low high) = high := by
  apply BitVec.eq_of_toNat_eq
  rw [upperHash, BitVec.extractLsb'_toNat, joinHalves_toNat, Nat.shiftRight_eq_div_pow]
  show (high.toNat * 2 ^ 128 + low.toNat) / 2 ^ 128 % 2 ^ 128 = high.toNat
  have hl : low.toNat < 2 ^ 128 := low.isLt
  have hh : high.toNat < 2 ^ 128 := high.isLt
  omega

theorem joinHalves_truncate (x : HashOutput) : joinHalves (truncateHash x) (upperHash x) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [joinHalves_toNat, truncateHash, upperHash, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, Nat.shiftRight_eq_div_pow]
  have hx : x.toNat < 2 ^ 256 := x.isLt
  show x.toNat / 2 ^ 128 % 2 ^ 128 * 2 ^ 128 + x.toNat % 2 ^ 128 = x.toNat
  omega

/-- The randomizer table with base randomizers `lows` and step halves `highs`. -/
def joinTable (lows highs : LTable) : RTable := fun message => joinHalves (lows message) (highs message)

theorem joinTable_bijective : Function.Bijective (fun pair : LTable × LTable => joinTable pair.1 pair.2) := by
  refine ⟨fun a b h => ?_, fun rnd => ⟨(fun m => truncateHash (rnd m), fun m => upperHash (rnd m)), ?_⟩⟩
  · have hl : ∀ m, a.1 m = b.1 m := fun m => by
      have := congrArg (fun t : RTable => truncateHash (t m)) h
      simpa only [joinTable, truncateHash_joinHalves] using this
    have hh : ∀ m, a.2 m = b.2 m := fun m => by
      have := congrArg (fun t : RTable => upperHash (t m)) h
      simpa only [joinTable, upperHash_joinHalves] using this
    exact Prod.ext (funext hl) (funext hh)
  · funext m
    exact joinHalves_truncate (rnd m)

theorem joinTable_update (lows highs : LTable) (message : Message) (low : Randomness) :
    joinTable (Function.update lows message low) highs =
      Function.update (joinTable lows highs) message (joinHalves low (highs message)) := by
  funext m
  by_cases h : m = message
  · subst h
    simp [joinTable]
  · simp [joinTable, Function.update_of_ne h]

/-- The deterministic signer from a scan of `attempts` trials starting at `start`. -/
def seededFrom (sk : Seeded.SecretKey) (message : Message) (step : Randomness) (attempts : Nat)
    (start : Randomness) : OracleComp HashSpec (Option Signature) := do
  let some (randomness, _) ← Seeded.signDigestLoop sk message step attempts start | return none
  Seeded.finishSign sk message randomness

theorem eval_deriveRandomizer (f : QueryImpl HashSpec Id) (prf : HashOutput)
    (parameter : PublicParameter) (message : Message) :
    evalWithAnswerFn f (deriveRandomizer prf parameter message : OracleComp HashSpec (Randomness × Randomness)) =
      (truncateHash (f (randomizerHashInput prf parameter message)),
        walkStep (upperHash (f (randomizerHashInput prf parameter message)))) := by
  simp only [deriveRandomizer, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rfl

theorem eval_signAttempt (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) :
    evalWithAnswerFn f (Seeded.signAttempt sk message randomness : OracleComp HashSpec (Option Index)) =
      if Landed sk.parameter (blockIndex (evalWithAnswerFn f
          (messageDigestCall sk.parameter sk.root message randomness firstCall : OracleComp HashSpec HashOutput)))
      then some (blockIndex (evalWithAnswerFn f
          (messageDigestCall sk.parameter sk.root message randomness firstCall : OracleComp HashSpec HashOutput)))
      else none := by
  simp only [Seeded.signAttempt, evalWithAnswerFn_bind]
  split <;> rfl

end FORS.Security.Det
