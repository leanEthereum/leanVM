module

public import Statement.HashSignatures
public import Mathlib.Data.BitVec
public import Mathlib.Data.FinEnum
public import Mathlib.Data.UInt
public import VCVio.Quantum.Oracle.Model

@[expose] public section

/-!
# leanXMSS and leanSPHINCS in the quantum random-oracle model: the model

Keccak-256 is modelled as one uniform random function `H` to 256 bits (`HashOutput`). The schemes
call it classically, the adversary on superpositions. VCVio's QROM (`qromSpec`, `qromEvalDistMap`)
needs a finite domain, and the statement's `HashInput` is every byte string; every input either
scheme hashes (key generation, signing, the verification of any well-typed forgery) has at most
`maxLen` bytes, so the random function is on byte strings of at most `maxLen` bytes, encoded
injectively into the finite additive group `HashDomain` (`encodeInput`). This domain cap is a
modelling choice: longer inputs, never hashed by the schemes, hash to `0` (`hashQ`).

* `RomOracles`: the classical oracles of the model, coins and `H`; `romSpec`: its quantum
  signature, one port on the register `HashDomain × HashOutput`.
* `SchemeOver O`: a signature scheme over any oracles `O`, the statement's `Common.SufCma.Scheme`
  being the case `O = RandomPermutationOracles` (`Scheme.toOver`, `SchemeOver.toScheme`).
* `forgeryGameOver O`: the statement's `forgeryGame` over `O`, verbatim
  (`forgeryGame_eq_over`, by `rfl`).
* `runWithRandomOracle`: a game over `RomOracles` run with coins passed through and `H` VCVio's
  lazily sampled random oracle (`randomOracle`): the classical ROM.
-/

open OracleComp OracleSpec
open HashSig

namespace Quantum.Qrom

/-! ## The random function's domain -/

/-- The longest hashed input, in bytes: eight Keccak-256 blocks. -/
def maxLen : ℕ := 1088

/-- Byte strings of at most `maxLen` bytes: the length and the bytes, zero-padded. A finite
additive group; the points with nonzero padding are never hashed by the schemes. -/
abbrev HashDomain := Fin (maxLen + 1) × (Fin maxLen → UInt8)

instance instFintypeHashDomain : Fintype HashDomain := instFintypeProd _ _

instance instDecidableEqHashDomain : DecidableEq HashDomain := instDecidableEqProd

instance instAddCommGroupHashDomain : AddCommGroup HashDomain := Prod.instAddCommGroup

instance instFintypeHashOutput : Fintype HashOutput := inferInstance

instance instDecidableEqHashOutput : DecidableEq HashOutput := inferInstance

instance instAddCommGroupHashOutput : AddCommGroup HashOutput := inferInstance

noncomputable instance instSampleableTypeHashOutput : SampleableType HashOutput := inferInstance

/-- The code of a byte string of at most `maxLen` bytes: its length and its bytes, zero-padded;
`none` for a longer string. -/
def encodeInput (l : HashInput) : Option HashDomain :=
  if h : l.length ≤ maxLen then some (⟨l.length, Nat.lt_succ_of_le h⟩, fun i ↦ l.getD i 0)
  else none

/-- The byte string of a code: its first `length` bytes. -/
def decodeInput (x : HashDomain) : HashInput :=
  List.ofFn fun i : Fin x.1 ↦ x.2 (Fin.castLE (Nat.le_of_lt_succ x.1.isLt) i)

theorem encodeInput_of_length_le {l : HashInput} (h : l.length ≤ maxLen) :
    encodeInput l =
      some ((⟨l.length, Nat.lt_succ_of_le h⟩, fun i ↦ l.getD i 0) : HashDomain) := by
  rw [encodeInput]
  split_ifs
  rfl

theorem encodeInput_eq_none_iff {l : HashInput} : encodeInput l = none ↔ maxLen < l.length := by
  unfold encodeInput
  split_ifs with h
  · simp only [false_iff, Nat.not_lt]
    exact h
  · simp only [true_iff]
    omega

theorem isSome_encodeInput_iff {l : HashInput} : (encodeInput l).isSome ↔ l.length ≤ maxLen := by
  rw [← Option.ne_none_iff_isSome, Ne, encodeInput_eq_none_iff, Nat.not_lt]

/-- Decoding a code gives back its byte string. -/
theorem decodeInput_of_encodeInput_eq_some {l : HashInput} {x : HashDomain}
    (h : encodeInput l = some x) : decodeInput x = l := by
  unfold encodeInput at h
  split_ifs at h with hl
  obtain rfl := Option.some.inj h
  refine List.ext_getElem (by simp [decodeInput]) fun n h₁ h₂ ↦ ?_
  simp [decodeInput, List.getD_eq_getElem?_getD]

/-- **The code is injective** on the strings it encodes. -/
theorem encodeInput_injective {l l' : HashInput} {x : HashDomain} (h : encodeInput l = some x)
    (h' : encodeInput l' = some x) : l = l' :=
  (decodeInput_of_encodeInput_eq_some h).symm.trans (decodeInput_of_encodeInput_eq_some h')

/-! ## The model's oracles -/

/-- **The model's classical oracles**: coins and the random function `H`. -/
abbrev RomOracles := unifSpec + (HashDomain →ₒ HashOutput)

/-- **The model's quantum signature**: one port, on the register `HashDomain × HashOutput`. -/
abbrev romSpec := qromSpec HashDomain HashOutput

/-- A call of `H` costs one, a coin nothing. -/
def hashCallCost : RomOracles.Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- **The hash as the schemes call it**: one query of `H` at the code of the input; longer
inputs, never hashed by the schemes, hash to `0` without a query. -/
def hashQ (l : HashInput) : OracleComp RomOracles HashOutput :=
  match encodeInput l with
  | some x => liftM (RomOracles.query (.inr x))
  | none => pure 0

theorem hashQ_of_encodeInput_eq_some {l : HashInput} {x : HashDomain}
    (h : encodeInput l = some x) : hashQ l = liftM (RomOracles.query (.inr x)) := by
  rw [hashQ, h]

/-! ## Schemes over any oracles and the forgery game -/

/-- **A signature scheme over the oracles `O`**: the fields of the statement's
`Common.SufCma.Scheme`, whose algorithms query `O` instead of `RandomPermutationOracles`. -/
structure SchemeOver {ι : Type} (O : OracleSpec.{0, 0} ι) (Seed PK SK Req Resp F : Type) where
  /-- Sample the secret seed. -/
  sampleSeed : ProbComp Seed
  /-- Generate the keys from the seed. -/
  generateKeys : Seed → OracleComp O (PK × SK)
  /-- Answer a signing request. -/
  sign : SK → Req → OracleComp O Resp
  /-- Verify a claimed forgery. -/
  verify : PK → F → OracleComp O Bool
  /-- The transcript and the forgery make a win (when the forgery verifies). -/
  winningCondition : QueryLog (Req →ₒ Resp) → F → Bool

variable {Seed PK SK Req Resp F : Type}

/-- The statement's scheme as a scheme over `RandomPermutationOracles`. -/
def _root_.Common.SufCma.Scheme.toOver (s : Common.SufCma.Scheme Seed PK SK Req Resp F) :
    SchemeOver Common.RandomPermutationOracles Seed PK SK Req Resp F :=
  ⟨s.sampleSeed, s.generateKeys, s.sign, s.verify, s.winningCondition⟩

/-- A scheme over `RandomPermutationOracles` as the statement's scheme. -/
def SchemeOver.toScheme (s : SchemeOver Common.RandomPermutationOracles Seed PK SK Req Resp F) :
    Common.SufCma.Scheme Seed PK SK Req Resp F :=
  ⟨s.sampleSeed, s.generateKeys, s.sign, s.verify, s.winningCondition⟩

theorem SchemeOver.toScheme_toOver (s : Common.SufCma.Scheme Seed PK SK Req Resp F) :
    s.toOver.toScheme = s :=
  rfl

theorem SchemeOver.toOver_toScheme
    (s : SchemeOver Common.RandomPermutationOracles Seed PK SK Req Resp F) :
    s.toScheme.toOver = s :=
  rfl

/-- **The forgery game over the oracles `O`**: the statement's `Common.SufCma.forgeryGame`,
verbatim with `RandomPermutationOracles` replaced by `O`: key generation, the adversary, which
queries `O` and the signing oracle (each request and answer logged), then the verification of its
forgery. -/
noncomputable def forgeryGameOver {ι : Type} (O : OracleSpec.{0, 0} ι)
    [MonadLiftT ProbComp (OracleComp O)]
    (scheme : SchemeOver O Seed PK SK Req Resp F)
    (adversary : PK → OracleComp (O + (Req →ₒ Resp)) F) : OracleComp O Bool := do
  let seed ← liftM scheme.sampleSeed
  let (pk, secretKey) ← scheme.generateKeys seed
  let ((forgery, log) : F × QueryLog (Req →ₒ Resp)) ←
    (simulateQ
      (QueryImpl.ofLift O (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp O)) +
      QueryImpl.withLogging (spec := Req →ₒ Resp) (scheme.sign secretKey))
        (adversary pk)).run
  let verified ← scheme.verify pk forgery
  return scheme.winningCondition log forgery && verified

/-- **The statement's game is the game over its oracles.** -/
theorem forgeryGame_eq_over (scheme : Common.SufCma.Scheme Seed PK SK Req Resp F)
    (adversary : PK → OracleComp (Common.RandomPermutationOracles + (Req →ₒ Resp)) F) :
    Common.SufCma.forgeryGame scheme adversary =
      forgeryGameOver Common.RandomPermutationOracles scheme.toOver adversary :=
  rfl

/-! ## The classical random-oracle model -/

/-- Coins and a function `X → Y` answered classically: coins forwarded, the function VCVio's
lazily sampled, cached random oracle. -/
noncomputable def lazyFunOracles (X Y : Type) [DecidableEq X] [SampleableType Y] :
    QueryImpl (unifSpec + (X →ₒ Y)) (StateT (X →ₒ Y).QueryCache ProbComp)
  | .inl n => liftM (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr x => (X →ₒ Y).randomOracle x

/-- **A game in the classical random-oracle model, run**: coins forwarded and `H` lazily sampled
from the empty cache. -/
noncomputable def runWithRandomOracle {α : Type} (game : OracleComp RomOracles α) : ProbComp α :=
  (simulateQ (lazyFunOracles HashDomain HashOutput) game).run' ∅

end Quantum.Qrom

end
