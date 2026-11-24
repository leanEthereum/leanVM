module

public import Mathlib.Data.Nat.Notation

/-!
# The leanVM verifier: its constants

The leanVM verifier is the readable reference of the deployed Rust verifier (`crates/verifier`),
which the differential tests compare it with. Every citation names an item of the Rust in this tree
and its file, with its path at its first citation. The Lean is the Rust's checked walk,
`verify_execution`; `replay_unchecked`, the same walk with the checks left out, is not
transcribed. It is split as `crates/verifier/src` is, in reading order:

* this file: the WHIR parameters, the security target and the grinding rule, the stacked claims'
  cap (`whir.rs`, `transcript.rs`, `lib.rs`); the Rust test `whir_query_table.rs`
  (`crates/experimental_prover/lean_vm_core/tests/verifiers/`) reads `queryTable` and these
  constants from this file by path;
* `Verifier/Transcript.lean`: the duplex sponge, and a program `VerifierProgram` of a small
  language, which `runProof` reads on a proof over a permutation `π : KeccakState → m KeccakState`
  in any monad `m`, Keccak-256 the sponge over `π`, `keccak256With π` (`transcript.rs`,
  `merkle.rs`);
* `Verifier/Multilinear.lean`, `Verifier/Layout.lean`, `Verifier/Bus.lean`, `Verifier/Whir.lean`,
  `Verifier/Keccak.lean`, `Verifier/RingSwitch.lean`: the arithmetic, the layout, the sumchecks
  and the bus, the WHIR opening, Keccak by GKR, ring switching;
* `Verifier/Lib.lean`: the verifier, ending with `verifyWith π bytecode publicInput proof`.

The proof claims one value of the polynomial the statement fixes (the bytecode's multilinear
extension) at a point the bus phase derives; the verifier checks that claim with a parameter
`bytecodeValue : List K → List E → E → VerifierProgram Unit`. The deployed verifier evaluates the
polynomial (`computedBytecodeValue`). The deferring verifier (`verifyDeferred`), which the Rust
verifier does not have, instead holds the point and the value to a claim it hands on, as an
aggregate's in-circuit verifier of its children does
(`guests/lean_ethereum.py`, `verify_sub`).
-/

@[expose] public section

/-!
## The WHIR parameters

The Rust verifier carries its WHIR constants, the ladder geometry (`derive_config`) and the query
counts (`WHIR_QUERIES`) itself (`crates/verifier/src/whir.rs`); they are the prover's
(`crates/pcs/src/whir_config.rs`, its ladder `derive_ladder` and `derive_ladder_shape`), as the tests `whir_query_table_matches_the_search` and
`grinding_constants_match_the_prover` (`crates/lean_vm_core/tests/verifiers/whir_query_table.rs`)
check, the latter on this file's constants too. The stacking window is `MIN_STACKED_LOG` and
`MAX_STACKED_LOG` (`crates/verifier/src/layout.rs`). The specification describes the protocol these
parameters instantiate (Annex B, `fig:protocol`, `doc/leanvm/body/b-polynomial-commitment-scheme.tex`)
and gives no numbers.

An opening of a stack of `2^μ` elements of `K` at rate `2^-R` runs a *ladder* of levels. Level 0
folds `initialFold = 6` variables; every later level folds `subsequentFold = 4`, or what remains,
until at most `residualMaxLog = 5` variables remain, which the final level closes with a sumcheck.
The rate exponent of a level is the previous one plus the previous fold minus a domain reduction,
`initialReduction = 3` after level 0 and `subsequentReduction = 1` after every later level. Every
fold round grinds `foldGrindingBits = 7` bits before its challenges; each level opens `queries`
positions after `queryGrindingBits = 17` bits of grinding; every level but the last commits its
folded lane and draws its batching challenge right after its query positions, in the same message;
every commitment, the stack's and each level's, takes one out-of-domain point after
`oodGrindingBits = 15` bits (`read_ood`, `crates/verifier/src/lib.rs`), and the stacked
opening's batching grinds `batchGrindingBits = 13` bits.

The query counts are the Rust's *output*, not its derivation: the prover's search (`search_level`,
`whir_config.rs`) minimises the queries of each level subject to the round-by-round target
`2^-125` of Annex B's Theorem `thm:rbr`, through an exact integer check of each count
(`query_count`, `whir_config.rs`), and this module does not restate that search. The table is the Rust
verifier's `WHIR_QUERIES` (`whir.rs`), indexed by rate exponent `1..4` and stack size
`16..30`; outside that window `ladder` is `none`, as the verifier rejects (`whir_queries`,
`whir.rs`; the prover's `validate_log_inv_rate`, `whir_config.rs`). `ladder` takes
the stack size `μ`, as the verifier's `derive_config` does (the PCS crate's API takes
`m = μ + LOG_PACKING`, `crates/pcs/src/pack.rs`), and the rate exponent is announced with the
sizes.
-/

namespace LeanVM.Parameters.Whir

/-- Variables folded at level 0: the lane fold (`INITIAL_FOLDING_FACTOR`, `whir.rs`). -/
def initialFold : ℕ := 6

/-- Variables folded at every later level (`SUBSEQUENT_FOLDING_FACTOR`, `whir.rs`). -/
def subsequentFold : ℕ := 4

/-- Bits the Reed-Solomon domain shrinks by after level 0, so that the rate exponent rises by
`initialFold - initialReduction` (`RS_DOMAIN_INITIAL_REDUCTION_FACTOR`, `whir.rs`). -/
def initialReduction : ℕ := 3

/-- Bits the domain shrinks by after every later level (`RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR`,
`whir.rs`). -/
def subsequentReduction : ℕ := 1

/-- Folding stops once at most this many variables remain; the final level closes them with a
sumcheck (`RESIDUAL_MAX_LOG`, `whir.rs`). -/
def residualMaxLog : ℕ := 5

/-- Grinding bits before each level's query positions are sampled (`QUERY_GRINDING_BITS`,
`whir.rs`). -/
def queryGrindingBits : ℕ := 17

/-- Grinding bits before each fold round's `(α, β)` (`FOLD_GRINDING_BITS`, `whir.rs`). -/
def foldGrindingBits : ℕ := 7

/-- Grinding bits before the stacked opening's batching: the ring-switching map and `λ`
(`BATCH_GRINDING_BITS`, `whir.rs`). A non-final level's `λ` is drawn with its query
positions, after their grind. -/
def batchGrindingBits : ℕ := 13

/-- Grinding bits before every commitment's out-of-domain point, the stack's and each later
level's (`OOD_GRINDING_BITS`, `whir.rs`). -/
def oodGrindingBits : ℕ := 15

/-- The smallest stack the PCS commits, a smaller witness padded up to it: `MIN_STACKED_LOG`
(`crates/verifier/src/layout.rs`). -/
def minLogStack : ℕ := 16

/-- The largest stack the PCS commits: `MAX_STACKED_LOG` (`crates/verifier/src/layout.rs`), the
cap every size shares. -/
def maxLogStack : ℕ := 30

/-- One level of an opening: the number of fold rounds it makes (`ℓ_i`), the rate exponent of
the code its commitment is in (`ν_i`), and the number of positions queried (`ω_i`), in the
notation of Annex B. -/
structure Level where
  /-- `ℓ_i`: the fold rounds it makes. -/
  fold : ℕ
  /-- `ν_i`: the rate exponent of its commitment's code. -/
  logInvRate : ℕ
  /-- `ω_i`: the positions queried. -/
  queries : ℕ
  deriving DecidableEq

/-- The levels after the first, as pairs (fold, rate exponent): while more than `residualMaxLog`
variables remain, fold `subsequentFold` of them (or all that remain) at the rate exponent the
previous level's fold and the pending domain reduction give (`derive_config`, `whir.rs`;
the prover's `derive_ladder`, `whir_config.rs`, with `derive_ladder_shape`'s rate rule). `fuel` bounds the
recursion; every level folds at least one variable, so `remaining` fuel is enough. -/
def levelsFrom : (fuel remaining prevFold prevRate reduction : ℕ) → List (ℕ × ℕ)
  | 0, _, _, _, _ => []
  | fuel + 1, remaining, prevFold, prevRate, reduction =>
    if remaining ≤ residualMaxLog then []
    else
      let rate := prevRate + prevFold - reduction
      let fold := min subsequentFold remaining
      (fold, rate) :: levelsFrom fuel (remaining - fold) fold rate subsequentReduction

/-- The ladder geometry of a `μ`-variable stack at rate exponent `logInvRate`: level 0 folds
`initialFold` at that rate, then `levelsFrom` (`derive_config`, `whir.rs`). -/
def ladderShape (μ logInvRate : ℕ) : List (ℕ × ℕ) :=
  (initialFold, logInvRate) ::
    levelsFrom μ (μ - initialFold) initialFold logInvRate initialReduction

/-- The query counts `WHIR_QUERIES` of `whir.rs`, verbatim: row `R - 1` for the rate
exponent `R`, entry `μ - 16` for the stack size `μ`, one count per level. -/
def queryTable : List (List (List ℕ)) := [
  [[230, 60, 42], [225, 58, 38], [222, 57, 35], [220, 56, 34], [219, 55, 33, 27],
   [218, 55, 32, 25], [218, 55, 32, 24], [218, 55, 32, 23], [218, 55, 32, 23, 20],
   [218, 55, 32, 23, 19], [218, 55, 32, 23, 18], [218, 55, 32, 23, 18], [218, 55, 32, 23, 18, 16],
   [218, 55, 32, 23, 18, 15], [218, 55, 32, 23, 18, 15]],
  [[112, 47, 35], [111, 46, 32], [110, 45, 31], [110, 45, 29], [109, 44, 29, 24],
   [109, 44, 28, 23], [109, 44, 28, 22], [109, 44, 28, 21], [109, 44, 28, 21, 18],
   [109, 44, 28, 21, 17], [109, 44, 28, 21, 17], [109, 44, 28, 21, 17], [109, 44, 28, 21, 17, 15],
   [109, 44, 28, 21, 17, 15], [109, 44, 28, 21, 17, 15]],
  [[74, 39, 30], [74, 38, 28], [73, 37, 27], [73, 37, 26], [73, 37, 25, 22],
   [73, 37, 25, 20], [73, 37, 25, 20], [73, 37, 25, 19], [73, 37, 25, 19, 17], [73, 37, 25, 19, 16],
   [73, 37, 25, 19, 16], [73, 37, 25, 19, 16], [73, 37, 25, 19, 16, 15], [73, 37, 25, 19, 16, 14],
   [73, 37, 25, 19, 16, 15]],
  [[56, 33, 27], [55, 32, 25], [55, 32, 24], [55, 32, 23], [55, 32, 23, 20],
   [55, 32, 23, 19], [55, 32, 23, 18], [55, 32, 23, 18], [55, 32, 23, 18, 16], [55, 32, 23, 18, 15],
   [55, 32, 23, 18, 15], [55, 32, 23, 18, 15], [55, 32, 23, 18, 15, 14], [55, 32, 23, 18, 16, 14],
   [55, 32, 23, 18, 16, 14]]]

/-- The window the parameters are defined on: the stacking window and the rate range `1..4`
(`whir_queries`, `whir.rs`; the rate also `lib.rs` and `whir_config.rs`). -/
def Admissible (μ logInvRate : ℕ) : Prop :=
  minLogStack ≤ μ ∧ μ ≤ maxLogStack ∧ 1 ≤ logInvRate ∧ logInvRate ≤ 4

instance {μ logInvRate : ℕ} : Decidable (Admissible μ logInvRate) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The ladder of an admissible stack size and rate (`derive_config(log_n, log_inv_rate)`,
`whir.rs`): the geometry of `ladderShape` paired with the tabulated query counts, level by
level. `none` outside the window (`WhirShape`), and `none` if the table did not have one count per
level (`QueryCountLadder`, `whir.rs`), so that no level is silently dropped. -/
def ladder (μ logInvRate : ℕ) : Option (List Level) :=
  if Admissible μ logInvRate then
    let geometry := ladderShape μ logInvRate
    let queries := (queryTable.getD (logInvRate - 1) []).getD (μ - minLogStack) []
    if geometry.length = queries.length then
      some (List.zipWith (fun (g : ℕ × ℕ) q ↦ ⟨g.1, g.2, q⟩) geometry queries)
    else none
  else none

end LeanVM.Parameters.Whir

/-! ## The security target and the stacked claims' cap -/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters

/-- `SECURITY_BITS`: every verifier message's round-by-round error, after its grind, is at most
`2^-125` (`transcript.rs`). -/
def securityBits : ℕ := 125

/-- `grinding_bits(numerator)`: the grind before a verifier message whose round-by-round error is
`numerator / |E|`, `|E| = 2^128`, the fewest bits that bring it to `2^-securityBits`: the bit
length of `numerator - 1` (`0` for `numerator ≤ 1`), less `128 - securityBits`, saturating
(`transcript.rs`). -/
def grindingBits (numerator : ℕ) : ℕ :=
  (if numerator ≤ 1 then 0 else Nat.log2 (numerator - 1) + 1) - (128 - securityBits)

end LeanVM.Protocol.Compile

namespace LeanVM.Protocol.Verifier

/-- `MAX_STACKED_CLAIMS`: the stacked opening's batching is accounted for up to this many claims,
the ring-switched one included (`lib.rs`; the prover's `whir_config.rs`). -/
def maxStackedClaims : ℕ := 512

end LeanVM.Protocol.Verifier

end
