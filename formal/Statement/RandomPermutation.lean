module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.EvalDist.ProbabilityBounds
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.WriterCost
public import VCVio.EvalDist.Monad.UniformTable
public import Statement.Keccak

/-!
# The random-permutation model

Read second (`statement.tex` states the model): the model (namespace `Common`): `π` and
`π⁻¹` lazily sampled, a cost bounded on every path, the oracles of the model and a game's run
(`RandomPermutationOracles`: coins, `π` and `π⁻¹`, nothing else; `permutationCallCost`,
`runWithRandomPermutation`; a computation's queries recorded, `loggedOracles`), over the state of
Keccak-f[1600] (`KeccakState`, `Keccak.lean`).
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

/-! ## The random permutation: `π` and `π⁻¹`, lazily sampled -/

namespace Common

/-- A query to a permutation `π` of `S`: forward `π x` or inverse `π⁻¹ y`. -/
inductive PermutationQuery (S : Type) where
  /-- The forward query `π x`. -/
  | forward (x : S)
  /-- The inverse query `π⁻¹ y`. -/
  | inverse (y : S)
  deriving DecidableEq

/-- The oracle specification of the random-permutation model: both kinds of query answer a state.
-/
abbrev permutationOracleSpec (S : Type) : OracleSpec (PermutationQuery S) := PermutationQuery S →ₒ S

/-- The state of a lazily sampled permutation: the edges `(x, π x)` fixed so far, newest first. -/
abbrev PermutationEdges (S : Type) := List (S × S)

variable {S : Type} [DecidableEq S]

/-- The recorded forward answer at `x`: the output of the first edge with input `x`. -/
def forwardLookup : PermutationEdges S → S → Option S
  | [], _ => none
  | (a, b) :: E, x => if a = x then some b else forwardLookup E x

/-- The recorded inverse answer at `y`: the input of the first edge with output `y`. -/
def inverseLookup : PermutationEdges S → S → Option S
  | [], _ => none
  | (a, b) :: E, y => if b = y then some a else inverseLookup E y

variable [Fintype S] [SampleableType S]

/-- A uniform draw from the points outside the list `excludedPoints`, or from all of `S` when
`excludedPoints` covers `S` (which the lazy permutation never needs: a full range is a full domain).
-/
noncomputable def uniformAvoiding (excludedPoints : List S) : ProbComp S :=
  if h : ∃ y, y ∉ excludedPoints then
    letI : Nonempty {y // y ∉ excludedPoints} := ⟨⟨h.choose, h.choose_spec⟩⟩
    letI : SampleableType {y // y ∉ excludedPoints} :=
      SampleableType.subtype S (· ∉ excludedPoints)
    Subtype.val <$> ($ᵗ {y // y ∉ excludedPoints})
  else $ᵗ S

/-- **The lazily sampled random permutation.** A recorded point is answered from the log; a
fresh forward query `π x` draws `π x` uniformly outside the current range and records `(x, π x)`;
a fresh inverse query `π⁻¹ y` draws `π⁻¹ y` uniformly outside the current domain and records
`(π⁻¹ y, y)`. -/
noncomputable def lazyRandomPermutation :
    QueryImpl (permutationOracleSpec S) (StateT (PermutationEdges S) ProbComp)
  | .forward x => StateT.mk fun E =>
      match forwardLookup E x with
      | some y => pure (y, E)
      | none => (fun y ↦ (y, (x, y) :: E)) <$> uniformAvoiding (E.map Prod.snd)
  | .inverse y => StateT.mk fun E =>
      match inverseLookup E y with
      | some x => pure (x, E)
      | none => (fun x ↦ (x, (x, y) :: E)) <$> uniformAvoiding (E.map Prod.fst)

/-! ## A query cost bounded on every path of a computation -/

/-- **`oa` makes queries of total cost at most `Q` on every path**: whatever the oracles answer, the
costs of the queries `oa` makes add up to at most `Q`, a query `t` costing `cost t`. A worst-case
count, not an expected one. With `permutationCallCost` (below) it counts the calls of `π` and
`π⁻¹`, coins free. -/
def QueryCostAtMost {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} (oa : OracleComp spec α)
    (cost : ι → ℕ) (Q : ℕ) : Prop :=
  IsQueryBound oa Q (fun t b ↦ cost t ≤ b) (fun t b ↦ b - cost t)

/-! ## The oracles of the model and a game's run -/

section

open LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- A 32-byte Keccak-256 digest. -/
abbrev DigestBytes := Vector UInt8 32

/-- **The oracles of the random-permutation model**: coins, `π` and `π⁻¹` on Keccak states, and
nothing else. Every party hashes with Keccak-256 over `π` (`keccak256With queryPermutation`). -/
abbrev RandomPermutationOracles := unifSpec + permutationOracleSpec KeccakState

/-- **The cost that counts permutation calls**: a call of `π` or `π⁻¹` costs one, a coin nothing. -/
def permutationCallCost : RandomPermutationOracles.Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- A call `π x` of the permutation. Keccak-256 over `π`, `keccak256With queryPermutation`, makes
one per block of the padded message (`⌊n / 136⌋ + 1` for `n` bytes). -/
def queryPermutation (x : KeccakState) : OracleComp RandomPermutationOracles KeccakState :=
  liftM (RandomPermutationOracles.query (.inr (.forward x)))

/-- The model's answers: coins forwarded, `π` and `π⁻¹` the lazily sampled permutation. -/
noncomputable def lazyRandomPermutationOracles :
    QueryImpl RandomPermutationOracles (StateT (PermutationEdges KeccakState) ProbComp)
  | .inl n => liftM (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr q => lazyRandomPermutation q

/-- **A game in the random-permutation model, run** against the lazily sampled random
permutation from no edge. -/
noncomputable def runWithRandomPermutation {α : Type}
    (game : OracleComp RandomPermutationOracles α) : ProbComp α :=
  (simulateQ lazyRandomPermutationOracles game).run' []

/-- A transcript: the queries of the model's oracles with their answers, in order (VCVio's
`QueryLog`): coins, `π` and `π⁻¹`. -/
abbrev OracleQueryLog := QueryLog RandomPermutationOracles

/-- **A computation's queries, recorded**: each query asked of the model's oracles, and appended
with its answer to the transcript. -/
def loggedOracles :
    QueryImpl RandomPermutationOracles
      (StateT OracleQueryLog (OracleComp RandomPermutationOracles)) := fun t ↦ do
  let u ← liftM (RandomPermutationOracles.query t)
  modify (· ++ [⟨t, u⟩])
  pure u

end

end Common
