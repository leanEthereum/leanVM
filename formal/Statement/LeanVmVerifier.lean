module

public import Statement.LeanIsa
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The leanVM verifier

The readable reference of the deployed Rust verifier (`crates/verifier`), which the differential
tests compare it with. Every citation `<file>.rs:N` is a line of the Rust at the pin
(`../leanvm-rev`), its file named with its path at its first citation. The Lean is the Rust's
checked walk, `verify_execution`; `replay_unchecked`, the same walk with the checks left out, is
not transcribed. Part 1 fixes the WHIR parameters. Part 2 is the transcript: a program
`VerifierProgram` of a small language, which `runProof` reads on a proof over a permutation
`π : KeccakState → m KeccakState` in any monad `m`, Keccak-256 the sponge over `π`,
`keccak256With π`. Part 3 is the verifier, ending with `verifyWith π bytecode publicInput proof`.

The verifier takes the value of the polynomial the statement fixes (the bytecode's multilinear
extension) from a parameter `bytecodeValue : List K → List E → VerifierProgram E`. The deployed
verifier computes it. The deferring verifier (`verifyDeferred`), which the Rust verifier does not
have, takes it from a claim, as an aggregate's in-circuit verifier of its children does
(`crates/rec_aggregation/guests/lean_ethereum.py`, `verify_sub`).
-/

@[expose] public section

/-! # Part 1: the constants

### The WHIR parameters

The constants are transcribed from `crates/pcs/src/whir_config.rs`, the ladder geometry from its
`derive_ladder` and `derive_ladder_shape`, the stacking window from `crates/verifier/src/layout.rs`
(`MIN_STACKED_LOG`, `MAX_STACKED_LOG`), and the query counts from the Rust verifier's
`WHIR_QUERIES` and `derive_config` (`crates/verifier/src/whir.rs`), which carry them verbatim. The
specification describes the protocol these parameters instantiate (Annex B, Protocol B.1,
`doc/leanvm/body/b-polynomial-commitment-scheme.tex`) and gives no numbers.

An opening of a stack of `2^μ` elements of `K` at rate `2^-R` runs a *ladder* of levels. Level 0
folds `initialFold = 6` variables; every later level folds `subsequentFold = 4`, or what remains,
until at most `residualMaxLog = 5` variables remain, which are sent in the clear. The rate
exponent of a level is the previous one plus the previous fold minus a domain reduction,
`initialReduction = 3` after level 0 and `subsequentReduction = 1` after every later level. Each
level opens `queries` positions after `queryGrindingBits = 17` bits of grinding; from level 1 on,
one out-of-domain sample binds the level's commitment (`whir_config.rs`, `whir.rs`).

The query counts are the Rust's *output*, not its derivation: `optimize_johnson_level`
(`whir_config.rs`) minimises the queries of each level subject to the 128-bit round-by-round
targets of Annex B's Theorem B.2 under a floating-point MCA formula
(`paper_thm_ca_johnson_log_a`), and this module does not restate that search. The table is the
Rust verifier's `WHIR_QUERIES`, indexed by rate exponent `1..4` and stack size `16..30`; outside
that window `ladder` is `none`, as the verifier rejects (`whir_queries`; the prover's
`validate_log_inv_rate`, `whir_config.rs`). `ladder` takes the stack size `μ`, as the verifier's
`derive_config` does (the PCS crate's API takes `m = μ + LOG_PACKING`, `crates/pcs/src/pack.rs:5`),
and the rate exponent is announced with the sizes.
-/

namespace LeanVM.Parameters.Whir

/-- Variables folded at level 0: the lane fold (`INITIAL_FOLDING_FACTOR`, `whir_config.rs:67`). -/
def initialFold : ℕ := 6

/-- Variables folded at every later level (`SUBSEQUENT_FOLDING_FACTOR`, `whir_config.rs:68`). -/
def subsequentFold : ℕ := 4

/-- Bits the Reed-Solomon domain shrinks by after level 0, so that the rate exponent rises by
`initialFold - initialReduction` (`RS_DOMAIN_INITIAL_REDUCTION_FACTOR`, `whir_config.rs:73`). -/
def initialReduction : ℕ := 3

/-- Bits the domain shrinks by after every later level (`RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR`,
`whir_config.rs:78`). -/
def subsequentReduction : ℕ := 1

/-- Folding stops once at most this many variables remain; the residual multilinear is sent in
the clear (`RESIDUAL_MAX_LOG`, `whir_config.rs:86`). -/
def residualMaxLog : ℕ := 5

/-- Grinding bits before each level's query positions are sampled (`QUERY_GRINDING_BITS`,
`whir_config.rs:60`). -/
def queryGrindingBits : ℕ := 17

/-- The smallest stack the PCS commits, a smaller witness padded up to it: `MIN_MU`
(`pcs.rs:49`; `MIN_STACKED_LOG`, `crates/verifier/src/layout.rs:94`). -/
def minLogStack : ℕ := 16

/-- The largest stack the PCS commits: `MAX_STACKED_LOG` (`crates/verifier/src/layout.rs:95`), the
cap every size shares. -/
def maxLogStack : ℕ := 30

/-- One level of an opening: the number of sumcheck rounds it folds (`ℓ_i`), the rate exponent
of the code its commitment is in (`R_i`), and the number of positions queried (`t_i`), in the
notation of Annex B. -/
structure Level where
  /-- `ℓ_i`: the sumcheck rounds it folds. -/
  fold : ℕ
  /-- `R_i`: the rate exponent of its commitment's code. -/
  logInvRate : ℕ
  /-- `t_i`: the positions queried. -/
  queries : ℕ
  deriving DecidableEq

/-- The levels after the first, as pairs (fold, rate exponent): while more than `residualMaxLog`
variables remain, fold `subsequentFold` of them (or all that remain) at the rate exponent the
previous level's fold and the pending domain reduction give (`derive_ladder`,
`whir_config.rs:252-286`, with `derive_ladder_shape`'s rate rule, `:292-301`). `fuel` bounds the
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
`initialFold` at that rate, then `levelsFrom` (`derive_config`, `whir.rs:43-56`). -/
def ladderShape (μ logInvRate : ℕ) : List (ℕ × ℕ) :=
  (initialFold, logInvRate) ::
    levelsFrom μ (μ - initialFold) initialFold logInvRate initialReduction

/-- The query counts `WHIR_QUERIES` of `whir.rs`, verbatim: row `R - 1` for the rate exponent
`R`, entry `μ - 16` for the stack size `μ`, one count per level. -/
def queryTable : List (List (List ℕ)) := [
  [[223, 56, 30], [223, 56, 31], [223, 56, 32], [223, 56, 32], [223, 56, 32, 22], [223, 56, 32, 22],
   [224, 56, 32, 23], [224, 56, 32, 23], [224, 56, 32, 23, 17], [224, 56, 32, 23, 17],
   [224, 56, 32, 23, 18], [225, 56, 32, 23, 18], [225, 56, 32, 23, 18, 14],
   [225, 56, 32, 23, 18, 14], [226, 56, 32, 23, 18, 14]],
  [[112, 45, 27], [112, 45, 28], [112, 45, 28], [112, 45, 28], [112, 45, 28, 20], [112, 45, 28, 20],
   [112, 45, 28, 21], [112, 45, 28, 21], [112, 45, 28, 21, 16], [112, 45, 28, 21, 16],
   [112, 45, 28, 21, 16], [112, 45, 28, 21, 16], [112, 45, 28, 21, 16, 13],
   [113, 45, 28, 21, 16, 14], [113, 45, 28, 21, 17, 14]],
  [[75, 37, 24], [75, 37, 25], [75, 38, 25], [75, 38, 25], [75, 38, 25, 18], [75, 38, 25, 19],
   [75, 38, 25, 19], [75, 38, 25, 19], [75, 38, 25, 19, 15], [75, 38, 25, 19, 15],
   [75, 38, 25, 19, 15], [75, 38, 25, 19, 15], [75, 38, 25, 19, 15, 13], [75, 38, 25, 19, 15, 13],
   [75, 38, 25, 19, 16, 13]],
  [[56, 32, 22], [56, 32, 22], [56, 32, 23], [56, 32, 23], [56, 32, 23, 17], [56, 32, 23, 17],
   [56, 32, 23, 18], [56, 32, 23, 18], [56, 32, 23, 18, 14], [56, 32, 23, 18, 14],
   [56, 32, 23, 18, 14], [56, 32, 23, 18, 15], [56, 32, 23, 18, 15, 12], [57, 32, 23, 18, 15, 12],
   [57, 33, 23, 18, 15, 12]]]

/-- The window the parameters are defined on: the stacking window and the rate range `1..4`
(`whir_queries`, `whir.rs:33-38`; the rate also `crates/verifier/src/lib.rs:230` and
`whir_config.rs:44-55`). -/
def Admissible (μ logInvRate : ℕ) : Prop :=
  minLogStack ≤ μ ∧ μ ≤ maxLogStack ∧ 1 ≤ logInvRate ∧ logInvRate ≤ 4

instance {μ logInvRate : ℕ} : Decidable (Admissible μ logInvRate) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The ladder of an admissible stack size and rate (`derive_config(log_n, log_inv_rate)`,
`whir.rs`): the geometry of `ladderShape` paired with the tabulated query counts, level by
level. `none` outside the window, and `none` if the table did not have one count per level, so
that no level is silently dropped. -/
def ladder (μ logInvRate : ℕ) : Option (List Level) :=
  if Admissible μ logInvRate then
    let geometry := ladderShape μ logInvRate
    let queries := (queryTable.getD (logInvRate - 1) []).getD (μ - minLogStack) []
    if geometry.length = queries.length then
      some (List.zipWith (fun (g : ℕ × ℕ) q ↦ ⟨g.1, g.2, q⟩) geometry queries)
    else none
  else none

end LeanVM.Parameters.Whir

/-! # Part 2: the transcript

The verifier touches the proof through five operations of its `Transcript`
(`crates/verifier/src/transcript.rs:77-215`): `next_scalar`, `sample`, `grind_check`, a root read
as two scalars, and `merkle`. It computes everything else from their results; `VerifierProgram α`
is the free monad over them, run (`run`, `runProof`) as the deployed non-interactive verifier: the
challenges squeezed out of a duplex sponge and the rows authenticated by Merkle paths.

The sponge is the duplex of `Field.lean` (`Sponge`, `absorb`, `squeeze`, `seedInput`), over
Keccak-f[1600] in the deployed verifier. Merkle openings come from a separate channel that the
sponge does not absorb: each query's opening is its position, the leaf's words, hashed as bytes,
then one sibling per level, the position's bit at the level choosing the side.

The proof is the Rust verifier's `Proof` (`transcript.rs:9-15`): the scalar stream, and the Merkle
openings grouped in phases, one phase per opened commitment, each query's opening (`MerklePath`,
`crates/verifier/src/merkle.rs:17-25`: position, leaf, siblings) in the order the verifier samples
the queries; the proof's wire encoding (`wire.rs`, a compression layer formalized in `lean_vm`)
needs the phases. A phase is checked as `Transcript::merkle` checks it (`transcript.rs:151-184`):
its shape, then its positions, then its roots.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash

/-- The verifier language: a program returns a value of type `α` after reading scalars,
sampling challenges, checking proofs of work, reading commitments and opening rows, or fails. -/
inductive VerifierProgram (α : Type) : Type where
  /-- Return `a`. -/
  | ret (a : α)
  /-- Reject. -/
  | fail
  /-- Read the next prover scalar, absorbed into the sponge (`next_scalar`). -/
  | read (k : E → VerifierProgram α)
  /-- Sample a challenge, squeezed from the sponge (`sample`). -/
  | sample (k : E → VerifierProgram α)
  /-- Check a proof of work of `bits` bits, the nonce read and absorbed (`grind_check`). -/
  | grind (bits : ℕ) (k : VerifierProgram α)
  /-- Read a Merkle root as two scalars (`Digest::from_halves` of `next_scalars(2)`), the committed
  matrix being `2^height` rows of `width` words. -/
  | commit (height width : ℕ) (k : VerifierProgram α)
  /-- Open rows of the `i`-th commitment at `positions`, each with its authentication path
  (`merkle`); continue with the rows. -/
  | query (i : ℕ) (positions : List ℕ) (k : List (List K) → VerifierProgram α)

namespace VerifierProgram

variable {α β γ : Type}

/-- Sequencing. -/
def bind : VerifierProgram α → (α → VerifierProgram β) → VerifierProgram β
  | ret a, f => f a
  | fail, _ => fail
  | read k, f => read fun x ↦ (k x).bind f
  | sample k, f => sample fun x ↦ (k x).bind f
  | grind b k, f => grind b (k.bind f)
  | commit h w k, f => commit h w (k.bind f)
  | query i ps k, f => query i ps fun r ↦ (k r).bind f

instance : Monad VerifierProgram where
  pure := ret
  bind := bind

/-- Read one prover scalar. -/
def readScalar : VerifierProgram E := read ret

/-- Read `n` prover scalars, in order. -/
def readScalars : ℕ → VerifierProgram (List E)
  | 0 => ret []
  | n + 1 => do
    let x ← readScalar
    let xs ← readScalars n
    return x :: xs

/-- Sample one challenge. -/
def sampleChallenge : VerifierProgram E := sample ret

/-- Sample `n` challenges, in order. -/
def sampleChallenges : ℕ → VerifierProgram (List E)
  | 0 => ret []
  | n + 1 => do
    let x ← sampleChallenge
    let xs ← sampleChallenges n
    return x :: xs

/-- Check a proof of work of `bits` bits; one of no bits is nothing, no nonce read
(`Transcript::grind_check`). -/
def grindProofOfWork (bits : ℕ) : VerifierProgram Unit :=
  if bits = 0 then ret () else grind bits (ret ())

/-- Read a commitment to a matrix of `2^height` rows of `width` words. -/
def readCommitment (height width : ℕ) : VerifierProgram Unit := commit height width (ret ())

/-- Open rows of the `i`-th commitment. -/
def queryOpenings (i : ℕ) (positions : List ℕ) : VerifierProgram (List (List K)) := query i
    positions ret

/-- Reject unless `c` holds (`require`, `lib.rs:117-119`). -/
def require (c : Prop) [Decidable c] : VerifierProgram Unit := if c then ret () else fail

end VerifierProgram

/-- Byte strings, the hash's inputs. -/
abbrev Bytes : Type := List UInt8

/-! ## Proofs and the run -/

/-- The proof-of-work predicate on the challenge sampled after the nonce: the low `bits` bits of
its first limb are zero (`Transcript::grind_check`). -/
def powOk (bits : ℕ) (challenge : E) : Bool :=
  decide ((challenge.limb 0).lane.toNat % 2 ^ bits = 0)

/-- One Merkle opening (`MerklePath`, `crates/verifier/src/merkle.rs:17-25`): the position it
opens, the leaf's words and the siblings from the leaf up. -/
structure Opening where
  /-- The position of the leaf (`leaf_index`). -/
  leafIndex : ℕ
  /-- The leaf's words. -/
  leaf : List K
  /-- The siblings from the leaf up. -/
  path : List Digest

/-- A proof (`Proof`, `crates/verifier/src/transcript.rs:9-15`): the scalar stream, and the Merkle
openings, one phase per commitment opened, each query's opening in the order the verifier samples
the queries. -/
structure Proof where
  /-- The scalars the prover sends, in order. -/
  stream : List E
  /-- The Merkle openings, one list per phase, in order. -/
  openings : List (List Opening)

/-- The compiled verifier's state: the sponge, the scalars and openings not yet read, and the
roots read so far, each with its height and width. -/
structure VerifierProgramState where
  /-- The Fiat-Shamir sponge. -/
  sponge : Sponge
  /-- The scalars not yet read. -/
  stream : List E
  /-- The phases of openings not yet read. -/
  openings : List (List Opening)
  /-- The roots read so far, each with its tree's height and width. -/
  roots : List (Digest × ℕ × ℕ)

section Run

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- Climb a Merkle path from `node` at position `q`: at each level the position's low bit says
whether `node` is the left child (`MerklePath::root`, `merkle.rs:28-38`). -/
def climb : Digest → ℕ → List Digest → m Digest
  | node, _, [] => pure node
  | node, q, s :: ss => do
    let parent ← if q % 2 = 0 then keccak256With π (digestBytes node ++ digestBytes s)
      else keccak256With π (digestBytes s ++ digestBytes node)
    climb parent (q / 2) ss

/-- Check one opening against a root of the given shape at position `position`: its shape
(`transcript.rs:169-174`), then its leaf hashed and climbed to the root (`hash_leaf` and
`MerklePath::root`, `merkle.rs:13-15, 28-38`). -/
def openOne (root : Digest) (height width position : ℕ) (opening : Opening) : m Bool :=
  if opening.leaf.length = width ∧ opening.path.length = height then do
    let leafDigest ← keccak256With π (opening.leaf.flatMap K.toBytes)
    let top ← climb π leafDigest position opening.path
    pure (decide (top.toList = root.toList))
  else pure false

/-- Open every position in order, consuming one opening each; the leaves, and the openings
left. -/
def openAll (root : Digest) (height width : ℕ) :
    List ℕ → List Opening → m (Option (List (List K) × List Opening))
  | [], os => pure (some ([], os))
  | _ :: _, [] => pure none
  | q :: qs, o :: os => do
    if ← openOne π root height width q o then
      let rest ← openAll root height width qs os
      pure (rest.map fun r ↦ (o.leaf :: r.1, r.2))
    else pure none

/-- Open one phase of a commitment of the given shape at `positions` (`Transcript::merkle`,
`crates/verifier/src/transcript.rs:151-184`): reject unless every leaf is `width` words and every
path `height` siblings, then unless the phase's positions are `positions`, in order, then unless
each path climbs to `root`, in order (at its position, which is the query's). The leaves. -/
def openPhase (root : Digest) (height width : ℕ) (positions : List ℕ) (phase : List Opening) :
    m (Option (List (List K))) :=
  if (∀ opening ∈ phase, opening.leaf.length = width ∧ opening.path.length = height) ∧
      phase.map Opening.leafIndex = positions then do
    match ← openAll π root height width positions phase with
    | some (rows, _) => pure (some rows)
    | none => pure none
  else pure none

/-- The compiled reading of a program: run it on the state, every challenge squeezed out of the
sponge and every opening authenticated; `none` on rejection. -/
def run {α : Type} : VerifierProgram α → VerifierProgramState → m (Option (α ×
    VerifierProgramState))
  | .ret a, s => pure (some (a, s))
  | .fail, _ => pure none
  | .read k, s => match s.stream with
    | [] => pure none
    | x :: xs => do
      let sponge ← absorb π s.sponge x dsObserve
      run (k x) { s with sponge := sponge, stream := xs }
  | .sample k, s => do
    let (c, sponge) ← squeeze π s.sponge
    run (k c) { s with sponge := sponge }
  | .grind bits k, s => match s.stream with
    | [] => pure none
    | n :: xs => do
      let sponge ← absorb π s.sponge n dsPowNonce
      let (c, sponge) ← squeeze π sponge
      if powOk bits c then run k { s with sponge := sponge, stream := xs } else pure none
  | .commit height width k, s => match s.stream with
    | x0 :: x1 :: xs => do
      let sponge ← absorb π s.sponge x0 dsObserve
      let sponge ← absorb π sponge x1 dsObserve
      match digestFromHalves (x0, x1) with
      | some root =>
        run k { s with sponge := sponge, stream := xs, roots := s.roots ++ [(root, height, width)] }
      | none => pure none
    | _ => pure none
  | .query i ps k, s => match s.roots[i]?, s.openings with
    | some (root, height, width), phase :: rest => do
      match ← openPhase π root height width ps phase with
      | some rows => run (k rows) { s with openings := rest }
      | none => pure none
    | _, _ => pure none

/-- Run a program on a proof from a seed state, and accept when it returns `true` with the
stream and the openings fully consumed (`Transcript::finish`, `transcript.rs:204-214`). -/
def runProof (program : VerifierProgram Bool) (seed : KeccakState) (proof : Proof) : m Bool := do
  match ← run π program ⟨⟨seed, []⟩, proof.stream, proof.openings, []⟩ with
  | some (true, s) => pure (s.stream.isEmpty && s.openings.isEmpty)
  | _ => pure false

end Run

end LeanVM.Protocol.Compile

/-! # Part 3: the verifier -/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters
open LeanVM.Semantics

/-!
## Verifier arithmetic (`crates/verifier/src/field.rs`, `crates/verifier/src/multilinear.rs`)

A function that transcribes a Rust function has its name in `lowerCamelCase` and computes the same
value on the inputs the verifier gives it; the products and sums are taken in the Rust's order
where it is visible (`foldl` from `1` or `0`), although `E` is a field and neither the order nor
the grouping changes a value. The Rust's `E::new(n, 0, 0)` for an integer `n < 2^64` is
`eOfNat n`: the natural-number cast of `E` is the characteristic-two one (`(2 : E) = 0`) and is
never used for a wire integer. A `K` value that the Rust lifts into `E` (`E::from`,
`field.rs:161-165`) is `ofK`.

**Preconditions the Rust checks and the verifier always meets.** `multilinear_eval` rejects a
table not of `2^|point|` entries, and `eq_eval` and `dot` assert equal lengths. At every call site
of the verifier the lengths agree by construction (the table sizes are `2^k` for the `k`
coordinates the caller passes), so these functions are total here: an excess entry is ignored, as
`zip` ignores it.
-/

/-- The integer value of a `K` word (the Rust's `K.0`). -/
def kToNat (a : K) : ℕ := a.toBitVec.toNat

/-- The three limbs of `e` as one 192-bit integer, limb `0` lowest: the bits `sample_queries`
reads (`whir.rs:81`). -/
def eToNat (e : E) : ℕ :=
  kToNat (e.limb 0) + 2 ^ 64 * kToNat (e.limb 1) + 2 ^ 128 * kToNat (e.limb 2)

/-- `gpow(index) = GEN.pow(index)` (`layout.rs:121-123`): `Parameters.addressOfIndex index`, the
same power in `K`, in limb `0`. -/
def gpow (index : ℕ) : E := gen ^ index

/-- `E::sum(values)`: the sum from `ZERO`, left to right (`field.rs:121-123`). -/
def sumE (values : List E) : E := values.foldl (· + ·) 0

/-- The product from `ONE`, left to right, as the GKR step takes a child's
(`crates/verifier/src/bus.rs:35-37`). -/
def prodE (values : List E) : E := values.foldl (· * ·) 1

/-- `acc, acc·base, acc·base², …`, `count` terms. -/
def powersFrom (acc base : E) : ℕ → List E
  | 0 => []
  | count + 1 => acc :: powersFrom (acc * base) base count

/-- `powers(base, count)`: `1, base, base², …`, `count` terms (`field.rs:258-267`). -/
def powers (base : E) (count : ℕ) : List E := powersFrom 1 base count

/-- `eq_kernel(point)`: the `2^|point|` equality weights, the first coordinate the lowest bit
(`multilinear.rs:6-19`). -/
def eqKernel (point : List E) : List E :=
  point.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) [1]

/-- One fold of `multilinear_eval`: adjacent pairs `(a, b)` become `a·(1 + r) + b·r`. -/
def foldPairs (r : E) : List E → List E
  | a :: b :: rest => (a * (1 + r) + b * r) :: foldPairs r rest
  | _ => []

/-- `multilinear_eval(mle, point)`: the multilinear extension of the table at the point, the
first coordinate folding adjacent entries (`multilinear.rs:45-59`). A table of the wrong size,
which the Rust rejects, never reaches it (see the section note); `0` for an empty result. -/
def multilinearEval (mle point : List E) : E :=
  (point.foldl (fun cur r ↦ foldPairs r cur) mle).headD 0

/-- The bit length of a natural number, `0` at `0`. -/
def bitLength (n : ℕ) : ℕ := if n = 0 then 0 else Nat.log2 n + 1

/-- `log2_ceil(value)`: the bit length of `value - 1`, saturating (`multilinear.rs:61-63`); `0`
at `value = 0`, the height of a table with no row. -/
def log2Ceil (value : ℕ) : ℕ := bitLength (value - 1)

/-- `log2_strict(value)`: the exponent of a power of two, `none` otherwise
(`multilinear.rs:65-68`). -/
def log2Strict (value : ℕ) : Option ℕ :=
  if 0 < value ∧ value &&& (value - 1) = 0 then some (bitLength value - 1) else none

/-- `eq_eval(left, right) = Π (1 + x + y)` (`multilinear.rs:70-77`). -/
def eqEval (left right : List E) : E :=
  (List.zipWith (fun x z ↦ 1 + x + z) left right).foldl (· * ·) 1

/-- `dot(left, right) = Σ x·y` (`multilinear.rs:79-86`). -/
def dot (left right : List E) : E :=
  (List.zipWith (· * ·) left right).foldl (· + ·) 0

/-- `padding_weight(point, n)`: `pad_n(point)`, the multilinear extension of `[z ≥ n]` for
`n ≤ 2^|point|`, unrolled from the low bit (`multilinear.rs:88-96`; `doc/leanvm`, Lemma
`lem:suffix`). -/
def paddingWeight (point : List E) (n : ℕ) : E :=
  (1 + eOfNat ((n >>> point.length) % 2)) *
    point.zipIdx.foldl (fun pad (r, k) ↦
      let b := eOfNat ((n >>> k) % 2)
      (1 + b) * r + (1 + b + r) * pad) 1

/-- `index_mle(point)`: the multilinear extension of `[1, g, g², …]` at an LSB-first point,
`Π (1 + r_i·(1 + g^(2^i)))` (`multilinear.rs:98-107`). -/
def indexMleFrom (generatorPower : E) : List E → E → E
  | [], acc => acc
  | r :: rs, acc => indexMleFrom (generatorPower ^ 2) rs (acc * (1 + r * (1 + generatorPower)))

/-- `index_mle(point)` (`multilinear.rs:98-107`). -/
def indexMle (point : List E) : E := indexMleFrom gen point 1

/-- `poly_eval(coefficients, point)`: Horner's rule over the coefficients, constant first
(`multilinear.rs:109-112`). -/
def polyEval (coefficients : List E) (point : E) : E :=
  coefficients.foldr (fun c acc ↦ acc * point + c) 0

/-- `selector_point(selector, length)`: the low `length` bits of `selector` as `0/1` elements,
lowest first (`multilinear.rs:146-148`). -/
def selectorPoint (selector length : ℕ) : List E :=
  (List.range length).map fun bit ↦ eOfNat ((selector >>> bit) % 2)

/-! ## The verifier's layout (`multilinear.rs:114-148`, `layout.rs`, `bus.rs:53-93`) -/

/-! ### Constants (`layout.rs:12, 70-95, 137-139, 380-386`;
`crates/verifier/src/keccak.rs:18-20, 55-67`) -/

/-- `BUS_BITS`: the bus communicates tuples of `2^BUS_BITS` field elements (`layout.rs:12`). -/
def busBits : ℕ := 4

/-- `NUM_GLOBAL_COLUMNS`: the columns no instruction table owns, first in the global numbering
(`layout.rs:70-71`). -/
def globalColumnCount : ℕ := 6

/-- Global column `MEMORY_0` (`layout.rs:72`); then `MEMORY_1`, `MEMORY_2`,
`MEMORY_FINAL_COUNTERS`, `BYTECODE_FINAL_COUNTERS`. -/
def memory0 : ℕ := 0
def memory1 : ℕ := 1
def memory2 : ℕ := 2
def memoryFinalCounters : ℕ := 3
def bytecodeFinalCounters : ℕ := 4
/-- Global column `QKECCAK`, the Keccak reduction's committed column: per step, its input state's
lanes and the state after every `KECCAK_DEPTH` rounds but the last, a lane per slot, and in the
slots left over the `KECCAK` table's own first committed columns (`keccakSlot`; `layout.rs:77`). -/
def qkeccak : ℕ := 5

/-- `K_BITS`: a `K` word's bits (`layout.rs:79`). -/
def kBits : ℕ := 64

/-- `KECCAK_DEPTH`: the reduction commits a step's state every `12` rounds (`layout.rs:83`). -/
def keccakDepth : ℕ := 12

/-- `KeccakShape::segments`, `ROUNDS / depth` at `depth = KECCAK_DEPTH`, `ROUNDS = 24`
(`keccak.rs:56-58`). -/
def keccakSegments : ℕ := 24 / keccakDepth

/-- The bits of a segment index, `log2_ceil(shape.segments())` (`keccak.rs:247`). -/
def keccakSegmentBits : ℕ := log2Ceil keccakSegments

/-- `KeccakShape::slot_bits`, `log2_ceil(STATE_LANES * segments)`, `STATE_LANES = 25`
(`keccak.rs:64-67`): lane `l` of the state after `KECCAK_DEPTH · m` rounds is slot `25m + l`; the
`2^6 - 50` slots above the states carry `KECCAK` columns (`keccakSlot`). -/
def qkeccakSlotBits : ℕ := log2Ceil (25 * keccakSegments)

/-- `KECCAK_MIN_STEPS_LOG`: the reduction is sized for at least one block of `512` steps
(`layout.rs:84`). -/
def keccakMinStepsLog : ℕ := 9

/-- `BITS = 64 * STATE_LANES`: a state's bits (`keccak.rs:18`). -/
def keccakBits : ℕ := 1600

/-- `LOCAL_BITS`: a bit position is `z + 64 · lane`, in a cube of `2^11` (`keccak.rs:19`). -/
def keccakLocalBits : ℕ := 11

/-- `LANE_BITS`: the bits of a lane's index, `25 ≤ 2^5` (`keccak.rs:20`). -/
def keccakLaneBits : ℕ := 5

/-- The bus separators `SEP_STATE`, `SEP_MEM`, `SEP_BYTECODE` (`layout.rs:137-139`). -/
def sepState : E := 1
def sepMem : E := gen
def sepBytecode : E := gen ^ 2

/-- The opcodes' numbers `OP_XOR`, `OP_MUL`, `OP_SET`, `OP_DEREF`, `OP_JUMP`, `OP_KECCAK`
(`layout.rs:380-385`). -/
def opXor : ℕ := 0
def opMul : ℕ := 1
def opSet : ℕ := 2
def opDeref : ℕ := 3
def opJump : ℕ := 4
def opKeccak : ℕ := 5

/-! ### Placements (`Placement`, `multilinear.rs:114-148`) -/

/-- Where something sits in the stacked cube: a claim's point fills the low `variableCount`
coordinates, the bits of the selector `index` fixing the rest. -/
structure Placement where
  /-- The coordinates the claim's point fills. -/
  variableCount : ℕ
  /-- The selector whose bits fix the other coordinates. -/
  index : ℕ
  deriving Inhabited, DecidableEq

/-- `Placement::stack_point`: the point on the stacked cube (`multilinear.rs:122-125`). -/
def Placement.stackPoint (p : Placement) (point : List E) (stackLog : ℕ) : List E :=
  point ++ selectorPoint (p.index >>> p.variableCount) (stackLog - p.variableCount)

/-- `Placement::eq_above`: the equality weight of the coordinates above the window
(`multilinear.rs:127-131`). -/
def Placement.eqAbove (p : Placement) (point : List E) : E :=
  eqEval (selectorPoint (p.index >>> p.variableCount) (point.length - p.variableCount))
    (point.drop p.variableCount)

/-- `stack_offsets(sizes)`: blocks of `2^size` laid end to end, largest first, ties by index;
their offsets, and the log-size of the total (`multilinear.rs:134-144`). -/
def stackOffsets (sizes : List ℕ) : List ℕ × ℕ :=
  let size := fun i ↦ sizes.getD i 0
  let order := (List.range sizes.length).mergeSort fun i j ↦
    decide (size j < size i) || (decide (size i = size j) && decide (i ≤ j))
  let placed := order.foldl (fun (acc : List ℕ × ℕ) i ↦
    (acc.1.set i acc.2, acc.2 + 2 ^ size i)) (List.replicate sizes.length 0, 0)
  (placed.1, log2Ceil placed.2)

/-! ### Forms (`Form`, `layout.rs:14-53, 125-135`) -/

/-- A polynomial of degree at most two in a table's columns: monomial (sorted column indices) to
coefficient, in insertion order (the Rust's `BTreeMap` orders them by monomial; a form's value does
not depend on the order). -/
structure Form where
  /-- The monomials, each with its coefficient. -/
  terms : List (List ℕ × E) := []
  deriving Inhabited

/-- Add `c` into the coefficient of `m`, appending the monomial if it is new (the
`entry(monomial).or_default() +=` of `Form::add_scaled`). -/
def addTerm : List (List ℕ × E) → List ℕ → E → List (List ℕ × E)
  | [], m, c => [(m, 0 + c)]
  | (m', c') :: rest, m, c =>
    if m' = m then (m', c' + c) :: rest else (m', c') :: addTerm rest m c

/-- `Form::add_scaled`: add `weight · other`. -/
def Form.addScaled (f other : Form) (weight : E) : Form :=
  ⟨other.terms.foldl (fun acc t ↦ addTerm acc t.1 (weight * t.2)) f.terms⟩

/-- `Form + Form`. -/
def Form.add (f g : Form) : Form := f.addScaled g 1

/-- `Form::sum`: the empty sum is the zero polynomial. -/
def Form.sum (forms : List Form) : Form := forms.foldl Form.add {}

/-- `Form::evaluate`: `Σ c · Π column(i)` over the terms. -/
def Form.evaluate (f : Form) (column : ℕ → E) : E :=
  sumE (f.terms.map fun t ↦ t.1.foldl (fun acc i ↦ acc * column i) t.2)

/-- `constant(value)`. -/
def Form.const (value : E) : Form := ⟨[([], value)]⟩

/-- `col(index, exponent)`: `g^exponent · x_index`. -/
def Form.col (index : ℕ) (exponent : ℕ := 0) : Form := ⟨[([index], gpow exponent)]⟩

/-- `prod(a, b, exponent)`: `g^exponent · x_a · x_b`. -/
def Form.prod (a b : ℕ) (exponent : ℕ := 0) : Form := ⟨[([min a b, max a b], gpow exponent)]⟩

/-! ### Flushes (`Flushes`, `layout.rs:141-191`) -/

/-- A table's bus flushes: the tuples it pushes and pulls, in pairs. -/
structure Flushes where
  /-- The tuples pushed. -/
  push : List (List Form) := []
  /-- The tuples pulled, each paired with the push at its position. -/
  pull : List (List Form) := []
  deriving Inhabited

namespace Flushes

/-- `Flushes::pair`. -/
def pair (f : Flushes) (push pull : List Form) : Flushes := ⟨f.push ++ [push], f.pull ++ [pull]⟩

/-- `Flushes::state_derived`. -/
def stateDerived (f : Flushes) (pc fp : ℕ) (npc nfp : Form) : Flushes :=
  f.pair [Form.const sepState, npc, nfp] [Form.const sepState, Form.col pc, Form.col fp]

/-- `Flushes::state_step`. -/
def stateStep (f : Flushes) (pc fp : ℕ) : Flushes :=
  f.stateDerived pc fp (Form.col pc 1) (Form.col fp)

/-- `Flushes::counted`: a pull at `count` and a push at `counter`, the same otherwise. -/
def counted (f : Flushes) (pre : List Form) (counter : Form) (count : ℕ) (suffix : List Form) :
    Flushes :=
  f.pair (pre ++ [counter] ++ suffix) (pre ++ [Form.col count] ++ suffix)

/-- `Flushes::bytecode`. -/
def bytecode (f : Flushes) (pc count opcode : ℕ) (operands : List Form) : Flushes :=
  f.counted [Form.const sepBytecode, Form.col pc] (Form.col count 1) count
    (Form.const (gpow opcode) :: operands)

/-- `Flushes::memory`. -/
def memory (f : Flushes) (address : Form) (count : ℕ) (values : List Form) : Flushes :=
  f.counted [Form.const sepMem, address] (Form.col count 1) count values

/-- `Flushes::memory_if`: `memory` when the column `flag` is `1`. The push's counter is
`count·(1 + flag·(g + 1))`: `g·count` at `1`, and the pull's `count` at `0`, so the pair cancels
and touches no cell. -/
def memoryIf (f : Flushes) (flag : ℕ) (address : Form) (count : ℕ) (values : List Form) :
    Flushes :=
  f.counted [Form.const sepMem, address]
    (Form.sum [Form.col count, Form.prod flag count 1, Form.prod flag count]) count values

/-- `Flushes::memory_cols`: the columns, padded with zeros to three limbs. -/
def memoryCols (f : Flushes) (address : Form) (count : ℕ) (columns : List ℕ) : Flushes :=
  f.memory address count
    (columns.map (Form.col ·) ++ List.replicate (3 - columns.length) (Form.const 0))

end Flushes

/-! ### The instruction tables (`layout.rs:193-497`) -/

/-- `cols(columns, names)`, one name: the index of a column by name (every name the tables use is
in its list, as the Rust's `expect` checks, `layout.rs:112-119`). -/
def columnIndexByName (columns : List String) (name : String) : ℕ := columns.idxOf name

/-- `ARITH_COLUMNS` (`layout.rs:389`). -/
def arithColumns : List String :=
  ["pc", "fp", "o_a", "o_b", "o_c", "va_0", "va_1", "va_2", "vb_0", "vb_1", "vb_2", "cnt_a",
    "cnt_b", "cnt_c", "cnt_bc"]

/-- `SET_COLUMNS` (`layout.rs:390`). -/
def setColumns : List String := ["pc", "fp", "o", "k_0", "k_1", "k_2", "cnt", "cnt_bc"]

/-- `DEREF_COLUMNS` (`layout.rs:392`). -/
def derefColumns : List String :=
  ["pc", "fp", "o1", "o2", "o3", "f_pc", "f_fp", "ptr", "v3_0", "v3_1", "v3_2", "cnt_ptr",
    "cnt_target", "cnt_local", "cnt_bc"]

/-- `JUMP_COLUMNS` (`layout.rs:394`). -/
def jumpColumns : List String :=
  ["pc", "fp", "o_c", "o_d", "o_f", "v_cond", "v_pc", "v_fp", "cnt_c", "cnt_d", "cnt_f", "cnt_bc",
    "w", "b"]

/-- The decimal numeral of `n` (`format!`'s `{}`): its digits below `100`, the column names'
numbers (`toString` past them). -/
def decimalNumeral (n : ℕ) : String :=
  if n < 10 then (Char.ofNat (48 + n)).toString
  else if n < 100 then (Char.ofNat (48 + n / 10)).toString ++ (Char.ofNat (48 + n % 10)).toString
  else toString n

/-- The names of the `25` lanes of a state, with a prefix: `prefix_0, …, prefix_24`. -/
def laneNames (namePrefix : String) : List String :=
  (List.range 25).map fun l ↦ namePrefix ++ "_" ++ decimalNumeral l

/-- `keccak_columns()` (`layout.rs:395-399, 441-450`): the operands, the layout flags, the
bytecode's flags for the output cells written (`out_two`: cell `1`; `out_all`: cells `2…12`), the
read limb that holds no lane (`free`), the fifty value lanes (`in_l`, one of `q_keccak`'s slots
each; `out_l`, claimed by the Keccak reduction, committed nowhere), then the read counts. The
first `QKECCAK_SPARE` (`14`) committed columns, `pc` through `out_all`, ride `q_keccak`'s spare
slots `50…63` (`keccakSlotOf`). -/
def keccakColumns : List String :=
  ["pc", "fp", "o_m0", "o_m1", "o_m2", "o_m3", "o_tail", "o_b8", "o_cap", "o_out", "odd_in",
    "odd_out", "out_two", "out_all", "free"] ++ laneNames "in" ++ laneNames "out" ++
    (List.range 26).map (fun c ↦ "cnt_" ++ decimalNumeral c) ++ ["cnt_bc"]

/-- `KECCAK_IN` (`layout.rs:401`): the local column of input lane `0`. -/
def keccakIn : ℕ := columnIndexByName keccakColumns "in_0"

/-- `KECCAK_OUT` (`layout.rs:402`): the local column of output lane `0`. -/
def keccakOut : ℕ := columnIndexByName keccakColumns "out_0"

/-- `KECCAK_CNT` (`layout.rs:403`): the local column of the first read count. -/
def keccakCnt : ℕ := columnIndexByName keccakColumns "cnt_0"

/-- `QKECCAK_SLOTS = STATE_LANES * (ROUNDS / KECCAK_DEPTH)` (`layout.rs:413-414`): the slots of
`q_keccak` the states take. -/
def qkeccakSlots : ℕ := 25 * keccakSegments

/-- `QKECCAK_SPARE`, `2^qkeccakSlotBits - QKECCAK_SLOTS` (`layout.rs:415`): the slots of
`q_keccak` left over, which carry `KECCAK` columns. -/
def qkeccakSpare : ℕ := 2 ^ qkeccakSlotBits - qkeccakSlots

/-- The local `KECCAK` columns outside the value lanes, `KECCAK_IN ≤ local < KECCAK_CNT`, in
order: the `k`-th is `spare_local(k)` (`layout.rs:406-411`). -/
def keccakCommitted : List ℕ :=
  (List.range keccakColumns.length).filter fun l ↦ ¬ (keccakIn ≤ l ∧ l < keccakCnt)

/-- The `q_keccak` slot of a local `KECCAK` column, if it has one (`qkeccak_slot`,
`layout.rs:429-439`, past the table's base): input lane `l` (local column `KECCAK_IN + l`) is
slot `l`, and the first `QKECCAK_SPARE` committed columns take the slots from `QKECCAK_SLOTS` on,
in order. The Rust tries the spare slots first; the two parts have disjoint keys
(`keccakSlotOf_disjoint`), so the order in which they are tried does not matter. -/
def keccakSlotOf (l : ℕ) : Option ℕ :=
  if keccakIn ≤ l ∧ l < keccakIn + 25 then some (l - keccakIn)
  else ((keccakCommitted.take qkeccakSpare).idxOf? l).map (qkeccakSlots + ·)

/-- `TOWER_LANES`: the limb products of `E` multiplication folded by `y³ = y + 1`
(`layout.rs:229-233`). -/
def towerLanes : List (List (ℕ × ℕ)) :=
  [[(0, 0), (1, 2), (2, 1)], [(0, 1), (1, 0), (1, 2), (2, 1), (2, 2)],
    [(0, 2), (1, 1), (2, 0), (2, 2)]]

/-- `flushes_arith(opcode, multiply)` (`layout.rs:216-241`). -/
def flushesArith (opcode : ℕ) (multiply : Bool) : Flushes :=
  let c := columnIndexByName arithColumns
  let va := [c "va_0", c "va_1", c "va_2"]
  let vb := [c "vb_0", c "vb_1", c "vb_2"]
  let result : List Form :=
    if multiply then
      towerLanes.map fun lane ↦
        Form.sum (lane.map fun (j, k) ↦ Form.prod (va.getD j 0) (vb.getD k 0))
    else (List.range 3).map fun i ↦ (Form.col (va.getD i 0)).add (Form.col (vb.getD i 0))
  let f : Flushes := {}
  let f := f.stateStep (c "pc") (c "fp")
  let f := f.bytecode (c "pc") (c "cnt_bc") opcode
    [Form.col (c "o_a"), Form.col (c "o_b"), Form.col (c "o_c"), Form.const 0, Form.const 0]
  let f := f.memoryCols (Form.prod (c "fp") (c "o_a")) (c "cnt_a") va
  let f := f.memoryCols (Form.prod (c "fp") (c "o_b")) (c "cnt_b") vb
  f.memory (Form.prod (c "fp") (c "o_c")) (c "cnt_c") result

/-- `flushes_set()` (`layout.rs:243-252`). -/
def flushesSet : Flushes :=
  let c := columnIndexByName setColumns
  let k := [c "k_0", c "k_1", c "k_2"]
  let f : Flushes := {}
  let f := f.stateStep (c "pc") (c "fp")
  let f := f.bytecode (c "pc") (c "cnt_bc") opSet
    (Form.col (c "o") :: k.map (Form.col ·) ++ [Form.const 0])
  f.memoryCols (Form.prod (c "fp") (c "o")) (c "cnt") k

/-- `flushes_deref()` (`layout.rs:254-277`). -/
def flushesDeref : Flushes :=
  let c := columnIndexByName derefColumns
  let pc := c "pc"
  let fp := c "fp"
  let fPc := c "f_pc"
  let fFp := c "f_fp"
  let v3 := [c "v3_0", c "v3_1", c "v3_2"]
  let gated := fun lane ↦ [Form.col lane, Form.prod fPc lane, Form.prod fFp lane]
  let store : List Form :=
    [Form.sum (gated (v3.getD 0 0) ++ [Form.prod fPc pc 2, Form.prod fFp fp]),
      Form.sum (gated (v3.getD 1 0)), Form.sum (gated (v3.getD 2 0))]
  let f : Flushes := {}
  let f := f.stateStep pc fp
  let f := f.bytecode pc (c "cnt_bc") opDeref
    [Form.col (c "o1"), Form.col (c "o2"), Form.col (c "o3"), Form.col fPc, Form.col fFp]
  let f := f.memoryCols (Form.prod fp (c "o1")) (c "cnt_ptr") [c "ptr"]
  let f := f.memory (Form.prod (c "ptr") (c "o2")) (c "cnt_target") store
  f.memoryCols (Form.prod fp (c "o3")) (c "cnt_local") v3

/-- `flushes_jump()` (`layout.rs:279-299`): `next_pc = b·dest + (b + 1)·g·pc`,
`next_fp = b·frame + (b + 1)·fp`. -/
def flushesJump : Flushes :=
  let c := columnIndexByName jumpColumns
  let pc := c "pc"
  let fp := c "fp"
  let b := c "b"
  let f : Flushes := {}
  let f := f.stateDerived pc fp
    (((Form.prod b (c "v_pc")).add (Form.prod b pc 1)).add (Form.col pc 1))
    (((Form.prod b (c "v_fp")).add (Form.prod b fp)).add (Form.col fp))
  let f := f.bytecode pc (c "cnt_bc") opJump
    [Form.col (c "o_c"), Form.col (c "o_d"), Form.col (c "o_f"), Form.const 0, Form.const 0]
  let f := f.memoryCols (Form.prod fp (c "o_c")) (c "cnt_c") [c "v_cond"]
  let f := f.memoryCols (Form.prod fp (c "o_d")) (c "cnt_d") [c "v_pc"]
  f.memoryCols (Form.prod fp (c "o_f")) (c "cnt_f") [c "v_fp"]

/-- `jump_constraints(columns)`: `b + cond·w` and `cond·(b + 1)` (`layout.rs:301-304`). -/
def jumpConstraints (columns : List E) : List E :=
  let c := columnIndexByName jumpColumns
  let condition := columns.getD (c "v_cond") 0
  let inverse := columns.getD (c "w") 0
  let flag := columns.getD (c "b") 0
  [flag + condition * inverse, condition * (flag + 1)]

/-- `layout_limb(even, odd, flag, missing)` (`layout.rs:318-334`): a cell limb holding the
column `even` in the even layout and `odd` in the odd one, as the column `flag` selects,
`a + flag·(a + b)`; a missing column is `missing`. -/
def layoutLimb (even odd : Option ℕ) (flag : ℕ) (missing : Option ℕ) : Form :=
  let a := even.orElse fun _ ↦ missing
  let b := odd.orElse fun _ ↦ missing
  if a = b then
    match a with
    | none => Form.const 0
    | some a => Form.col a
  else
    Form.sum ((match a with
      | some a => [Form.col a, Form.prod flag a]
      | none => []) ++
      (match b with
      | some b => [Form.prod flag b]
      | none => []))

/-- `flushes_keccak()` (`layout.rs:336-378`): the state step, the bytecode read, then the
thirteen cells read (four addressed ones, the tail run, `b8`, the cap run) and the thirteen
written, each holding its lanes in the layout its flag names (`keccak_cell_lanes`,
`layout.rs:306-316`, which is `cellLanes`, `LeanIsa.lean`): a read cell's free limb is the column
`free`, a written one's zero. Output cell `0` is always written, cell `1` when `out_two` is `1`,
and cells `2…12` when `out_all` is `1` (`memoryIf`). -/
def flushesKeccak : Flushes :=
  let c := columnIndexByName keccakColumns
  let oM := ["o_m0", "o_m1", "o_m2", "o_m3"].map c
  let fp := c "fp"
  let f : Flushes := {}
  let f := f.stateStep (c "pc") fp
  let f := f.bytecode (c "pc") (c "cnt_bc") opKeccak
    ((oM ++ ["o_tail", "o_b8", "o_cap", "o_out", "odd_in", "odd_out", "out_two",
      "out_all"].map c).map (Form.col ·))
  let address := fun (cell : ℕ) ↦
    if cell < 4 then Form.prod fp (oM.getD cell 0)
    else if cell < 8 then Form.prod fp (c "o_tail") (cell - 4)
    else if cell = 8 then Form.prod fp (c "o_b8")
    else Form.prod fp (c "o_cap") (cell - 9)
  let sides : List (ℕ × ℕ × Option ℕ) := [(keccakIn, c "odd_in", some (c "free")),
    (keccakOut, c "odd_out", none)]
  sides.zipIdx.foldl (fun f ((lanes, flag, missing), side) ↦
    let lane := fun (l : Option ℕ) ↦ l.map (lanes + ·)
    (List.range 13).foldl (fun f cell ↦
      let values := ([0, 1] : List ℕ).map (fun h ↦
        let pick := fun (p : Option ℕ × Option ℕ) ↦ if h = 0 then p.1 else p.2
        layoutLimb (lane (pick (cellLanes false cell)))
          (lane (pick (cellLanes true cell))) flag missing) ++ [Form.const 0]
      let count := keccakCnt + 13 * side + cell
      if side = 0 then f.memory (address cell) count values
      else if cell = 0 then f.memory (Form.prod fp (c "o_out")) count values
      else f.memoryIf (if cell = 1 then c "out_two" else c "out_all")
        (Form.prod fp (c "o_out") cell) count values) f) f

/-- One instruction's table: its columns, its bus flushes, its constraints
(`layout.rs:193-214`). -/
structure Table where
  /-- Its opcode, also its index in `tables()`. -/
  opcode : ℕ
  /-- Its columns' names, in order. -/
  columns : List String
  /-- Its bus flushes. -/
  flushes : Flushes
  /-- Its constraints, as a function of a row's evaluations. -/
  constraints : List E → List E := fun _ ↦ []
  deriving Inhabited

/-- `Table::width`. -/
def Table.width (t : Table) : ℕ := t.columns.length

/-- `Table::n_constraints`: the number of constraints, read off the zero row. -/
def Table.nConstraints (t : Table) : ℕ := (t.constraints (List.replicate t.width 0)).length

/-- `Table::count_columns`: the columns whose name starts with `cnt`. -/
def Table.countColumns (t : Table) : List ℕ :=
  (t.columns.zipIdx.filter fun (name, _) ↦ name.startsWith "cnt").map (·.2)

/-- `tables()`, in opcode order (`layout.rs:452-476`). -/
def tables : List Table :=
  [⟨opXor, arithColumns, flushesArith opXor false, fun _ ↦ []⟩,
    ⟨opMul, arithColumns, flushesArith opMul true, fun _ ↦ []⟩,
    ⟨opSet, setColumns, flushesSet, fun _ ↦ []⟩,
    ⟨opDeref, derefColumns, flushesDeref, fun _ ↦ []⟩,
    ⟨opJump, jumpColumns, flushesJump, jumpConstraints⟩,
    ⟨opKeccak, keccakColumns, flushesKeccak, fun _ ↦ []⟩]

/-- `Table::padding` (`layout.rs:455, 462-467`): the row a padding row holds, zero but for
`KECCAK`'s output lanes `KECCAK_OUT …`, a padding row permuting zeros (`keccak_f` of the zero
state). -/
def Table.padding (t : Table) : List E :=
  let output := keccakF1600 (Vector.replicate 25 0)
  (List.range t.width).map fun i ↦
    if t.opcode = opKeccak ∧ keccakOut ≤ i ∧ i < keccakOut + 25 then
      eOfNat (Keccak.lane output (i - keccakOut)).toNat
    else 0

/-- `TABLE_WIDTHS` (`layout.rs:478-485`). -/
def tableWidths : List ℕ := tables.map Table.width

/-- `GLOBAL_COLUMN_BASES`: each table's first global column (`layout.rs:486-494`). -/
def globalColumnBases : List ℕ :=
  (List.range tables.length).map fun t ↦ globalColumnCount + (tableWidths.take t).sum

/-- `TABLE_LOG_FLOORS` (`layout.rs:496-497`): each table's least log-height, `0` but for
`KECCAK`, the Keccak reduction's block of steps. -/
def tableLogFloors : List ℕ := [0, 0, 0, 0, 0, keccakMinStepsLog]

/-! ### The bus layout (`layout.rs:55-62`, `bus.rs:53-93`, `lib.rs:121-122`) -/

/-- One block of a bus side, owned by a table (`BusBlock`, `layout.rs:55-62`). -/
structure BusBlock where
  /-- The owner's log-height: the block spans `2 ^ logRows` rows. -/
  logRows : ℕ
  /-- The owner's row count: the first `rows` rows flush, the others are padding rows, whose
  leaves are `1`. -/
  rows : ℕ
  /-- The tuple flushed, over the owner's local columns. -/
  coordinates : List Form
  /-- The owner's opcode. -/
  owner : ℕ
  deriving Inhabited

/-- Where a side's blocks sit in the stacked leaf cube: its log-size, the framework blocks'
placements, and the table blocks', in the side's block order (`BusLayout`, `bus.rs:53-59`). -/
structure BusLayout where
  /-- The log-size of the stacked leaf cube. -/
  depth : ℕ
  /-- The framework blocks' placements. -/
  framework : List Placement
  /-- The table blocks' placements, in the side's block order. -/
  tables : List Placement

/-- `bus_layout(framework_log_rows, blocks)` (`bus.rs:61-79`). -/
def busLayout (frameworkLogRows : List ℕ) (blocks : List BusBlock) : BusLayout :=
  let sizes := frameworkLogRows ++ blocks.map (·.logRows)
  let (offsets, depth) := stackOffsets sizes
  let placements := List.zipWith (fun size offset ↦ ({ variableCount := size, index := offset } :
    Placement)) sizes offsets
  ⟨depth, placements.take frameworkLogRows.length, placements.drop frameworkLogRows.length⟩

/-- A column claim: the global column's multilinear extension at `point` (over the column's own
variables) is `value` (`ColumnClaim`, `bus.rs:81-85`). -/
structure ColumnClaim where
  /-- The global column. -/
  column : ℕ
  /-- The point, over the column's own variables. -/
  point : List E
  /-- The claimed value. -/
  value : E
  deriving Inhabited

/-- A claim on the stack: the weight it puts on the stack, and the value it claims for it
(`StackClaim`, `lib.rs:121-122`). -/
abbrev StackClaim : Type := (List E → E) × E

/-! ### `build_layout` (`layout.rs:97-110, 557-621`) -/

/-- The layout the verifier derives from the bytecode and the announced sizes. -/
structure Layout where
  /-- The memory's log-size, `κ`. -/
  logMemory : ℕ
  /-- The bytecode's log-size, in tuples of `2^BUS_BITS` words. -/
  logBytecode : ℕ
  /-- The bytecode's words. -/
  bytecode : List K
  /-- The push side's blocks. -/
  push : List BusBlock
  /-- The pull side's blocks. -/
  pull : List BusBlock
  /-- The count side's blocks. -/
  count : List BusBlock
  /-- Every global column's placement; `none` for a `KECCAK` output lane. -/
  placements : List (Option Placement)
  /-- The stack's log-size: the committed columns stacked in one cube. -/
  stackLog : ℕ
  /-- The tables' log-heights, each the least `h` with `rows ≤ 2 ^ h`, at least its floor. -/
  tableLogHeights : List ℕ

/-- The placement of a committed column (`layout.placements[column]`), which the verifier reads
of `MEMORY_0` and `QKECCAK`. -/
def Layout.placement (layout : Layout) (column : ℕ) : Placement :=
  (layout.placements.getD column none).getD default

/-- `ColumnClaim::on_stack` (`bus.rs:87-93`): the claim as an equality weight on the
stack; `none` for a column nothing commits (a `KECCAK` output lane), whose claim never reaches
the stack. -/
def ColumnClaim.onStack (c : ColumnClaim) (layout : Layout) : Option StackClaim :=
  (layout.placements.getD c.column none).map fun placement ↦
    (fun x ↦ eqEval (placement.stackPoint c.point layout.stackLog) x, c.value)

/-- The bus blocks of every table, side by side: pushes, pulls, counts, each block at its
table's log-height and row count (`layout.rs:578-592`). -/
def busBlocks (tableLogHeights tableRows : List ℕ) :
    List BusBlock × List BusBlock × List BusBlock :=
  let rows := List.zip tables (List.zip tableLogHeights tableRows)
  (rows.flatMap fun (t, h, n) ↦ t.flushes.push.map fun c ↦ ⟨h, n, c, t.opcode⟩,
    rows.flatMap fun (t, h, n) ↦ t.flushes.pull.map fun c ↦ ⟨h, n, c, t.opcode⟩,
    rows.flatMap fun (t, h, n) ↦ t.countColumns.map fun l ↦ ⟨h, n, [Form.col l], t.opcode⟩)

/-- The `q_keccak` slot of a global column (`qkeccak_slot`, `layout.rs:429-439`): a `KECCAK`
input lane's, or a spare slot's column's; `none` for every other column, those of the other tables
(below the `KECCAK` base, where `checked_sub` fails) among them. -/
def keccakSlot (column : ℕ) : Option ℕ :=
  if globalColumnBases.getD opKeccak 0 ≤ column then
    keccakSlotOf (column - globalColumnBases.getD opKeccak 0)
  else none

/-- The global columns of the `KECCAK` output lanes, in lane order (`outputs`,
`layout.rs:527-528`; the columns of `values[KECCAK_OUT..KECCAK_OUT + STATE_LANES]`,
`lib.rs:293`). -/
def keccakOutputColumns : List ℕ :=
  (List.range 25).map (globalColumnBases.getD opKeccak 0 + keccakOut + ·)

/-- Every column's log-size, in global order: the framework's, `q_keccak`'s, then each table's
block (`column_kappas`, `layout.rs:506-521`). -/
def columnKappas (logMemory logBytecode : ℕ) (tableLogHeights : List ℕ) : List ℕ :=
  let qkeccakKappa := tableLogHeights.getD opKeccak 0 + qkeccakSlotBits
  [logMemory, logMemory, logMemory, logMemory, logBytecode, qkeccakKappa] ++
    tables.flatMap fun t ↦ List.replicate t.width (tableLogHeights.getD t.opcode 0)

/-- The placements of every column, and the stack's log-size (`stacked_blocks` and `stack`,
`layout.rs:523-543`; `placement`, `layout.rs:594-607`): the committed columns (every column but those with a `q_keccak` slot, the `KECCAK` input lanes and
the table's first fourteen committed columns, and the `KECCAK` output lanes: `101` of `165`)
stacked by `stack_offsets`, a column with a slot at `q_keccak`'s offset plus its slot's `2^κ`
words, an output lane nowhere. -/
def placementsOf (kappas : List ℕ) : List (Option Placement) × ℕ :=
  let blockCols := (List.range kappas.length).filter fun c ↦
    (keccakSlot c).isNone ∧ c ∉ keccakOutputColumns
  let (blockOffsets, totalLog) := stackOffsets (blockCols.map (kappas.getD · 0))
  let offsetOf := fun c ↦ blockOffsets.getD (blockCols.idxOf c) 0
  let placements := kappas.zipIdx.map fun (kappa, column) ↦
    match keccakSlot column with
    | some slot =>
      some ({ variableCount := kappa, index := offsetOf qkeccak + slot * 2 ^ kappa } : Placement)
    | none =>
      if column ∈ keccakOutputColumns then none
      else some { variableCount := kappa, index := offsetOf column }
  (placements, max Whir.minLogStack totalLog)

/-- `build_layout(bytecode, log_memory, table_rows)` (`layout.rs:557-621`); `none` exactly where
the Rust returns an error: a bytecode whose length is not a power of two (`log2_strict`) or whose
log-length is outside `BUS_BITS ..= 30 + BUS_BITS`, and sizes outside the window. It is also `none`
on row counts not one per table, which the verifier never passes (it reads `N_TABLES` of them). A
table's log-height is the least `h` with `rows ≤ 2^h` (`log2Ceil`), and at least its floor
(`tableLogFloors`). -/
def buildLayout (bytecode : List K) (logMemory : ℕ) (tableRows : List ℕ) : Option Layout :=
  match log2Strict bytecode.length with
  | none => none
  | some logLength =>
    if busBits ≤ logLength ∧ 1 ≤ logMemory ∧ logMemory ≤ 30 ∧
        tableRows.all (· ≤ 2 ^ 30) ∧ logLength - busBits ≤ 30 ∧
        tableRows.length = tables.length then
      let logBytecode := logLength - busBits
      let tableLogHeights := List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) tableRows
        tableLogFloors
      let (push, pull, count) := busBlocks tableLogHeights tableRows
      let (placements, stackLog) :=
        placementsOf (columnKappas logMemory logBytecode tableLogHeights)
      some ⟨logMemory, logBytecode, bytecode, push, pull, count, placements, stackLog,
        tableLogHeights⟩
    else none

open LeanVM.Protocol.Compile

/-!
## Sumcheck rounds (`transcript.rs:186-231`)

A round polynomial of `count` coefficients is sent with one coefficient left out, which the
verifier derives from the running claim: in plain mode (`eq_factor = None`) `q(0) + q(1) = claim`
fixes `c1`; in equality mode (`eq_factor = r`) `(1 + r)·q(0) + r·q(1) = claim` fixes `c0`
(characteristic two).
-/

/-- Fail on `none`: a pure step that returns a `Result` in the Rust. -/
def liftOption {α : Type} : Option α → VerifierProgram α
  | none => VerifierProgram.fail
  | some a => VerifierProgram.ret a

/-- `Transcript::sumcheck_round_poly(count, claim, eq_factor)`: read a round polynomial of `count`
coefficients, deriving the one the claim fixes; its coefficients, constant first
(`transcript.rs:186-202`). -/
def sumcheckRoundPoly (count : ℕ) (claim : E) : Option E → VerifierProgram (List E)
  | none => do
    let constant ← VerifierProgram.readScalar
    let tail ← VerifierProgram.readScalars (count - 2)
    return constant :: (claim + sumE tail) :: tail
  | some eqFactor => do
    let tail ← VerifierProgram.readScalars (count - 1)
    return (claim + eqFactor * sumE tail) :: tail

/-- `sumcheck(transcript, claim, count, equalities)`: one round per entry of `equalities`, each
reading its polynomial and sampling its challenge; the challenges in order, and the final claim
(`transcript.rs:217-231`). -/
def sumcheck (claim : E) (count : ℕ) : List (Option E) → VerifierProgram (List E × E)
  | [] => return ([], claim)
  | equality :: equalities => do
    let message ← sumcheckRoundPoly count claim equality
    let challenge ← VerifierProgram.sampleChallenge
    let (point, final) ← sumcheck (polyEval message challenge) count equalities
    return (challenge :: point, final)

/-!
## The bus phase (`bus.rs:14-213`)

The three GKR trees (push, pull, count) are batched, their roots read as `shared, count` (push and
pull share their root, which is the balance), the layers walked two at a time, one first when the
depth is odd. The leaf decomposition is pure (`accumulateSide`): every side's framework blocks are
evaluated outright, its table blocks accumulate into the owner's form for that side, and the
side's total is the GKR value less the framework and the padding.
-/

/-- The state of the GKR walk: the push, pull and count trees' values at `point`. -/
structure GkrState where
  /-- The push, pull and count trees' values. -/
  values : List E
  /-- The point they are at. -/
  point : List E

/-- One step of `step` levels of the GKR walk (`bus.rs:21-47`). -/
def gkrStep (step : ℕ) (state : GkrState) : VerifierProgram GkrState := do
  let combiner ← VerifierProgram.sampleChallenge
  let claim := polyEval state.values combiner
  let (x, claim) ← sumcheck claim (2 ^ step + 1) (state.point.map some)
  let child0 ← VerifierProgram.readScalars (2 ^ step)
  let child1 ← VerifierProgram.readScalars (2 ^ step)
  let child2 ← VerifierProgram.readScalars (2 ^ step)
  let children := [child0, child1, child2]
  let products := children.map prodE
  VerifierProgram.require (claim = polyEval products combiner)
  let y ← VerifierProgram.sampleChallenges step
  let values := children.map (multilinearEval · y)
  return ⟨values, y ++ x⟩

/-- The `while layer > 0` loop: one level when the remaining depth is odd, two otherwise. -/
def gkrLayers : ℕ → GkrState → VerifierProgram GkrState
  | 0, s => return s
  | 1, s => do
    let s ← gkrStep 1 s
    gkrLayers 0 s
  | n + 2, s =>
    if n % 2 = 1 then do
      let s ← gkrStep 1 s
      gkrLayers (n + 1) s
    else do
      let s ← gkrStep 2 s
      gkrLayers n s

/-- `verify_gkr_grand_products(depth)`: the count root, the GKR point, and the three trees'
values there (`bus.rs:14-51`). -/
def verifyGkrGrandProducts (depth : ℕ) : VerifierProgram (E × List E × List E) := do
  let shared ← VerifierProgram.readScalar
  let count ← VerifierProgram.readScalar
  let s ← gkrLayers depth ⟨[shared, shared, count], []⟩
  return (count, s.point, s.values)

/-- `BusResult` (`bus.rs:98-104`): the framework columns' claims, the GKR point (which the table
sumcheck reuses), each table's form per side (`forms[table][side]`), and the three sides' totals.
The Rust's `bytecode_point`, which only the summary of a walk reads, is left out. -/
structure BusResult where
  /-- The framework columns' claims. -/
  claims : List ColumnClaim
  /-- The GKR point. -/
  point : List E
  /-- Each table's form per side. -/
  forms : List (List Form)
  /-- The three sides' totals. -/
  totals : List E
  deriving Inhabited

/-- The three framework fingerprints of a side (`fingerprints`, `bus.rs:147-159`; the Rust
hoists `memory_index` and `bytecode_index`, `bus.rs:137-138`, pure values inlined here;
`bytecode_value` is the bytecode's value, from `bytecodeValue`). -/
def fingerprints (weights memory memoryLow bytecodeLow : List E) (bytecodeValue : E)
    (pc memoryCount bytecodeCount : E) : List E :=
  [dot (weights.take 3) [sepState, pc, gpow 0],
    dot (weights.take 6) ([sepMem, indexMle memoryLow, memoryCount] ++ memory),
    dot (weights.take 3) [sepBytecode, indexMle bytecodeLow, bytecodeCount] + bytecodeValue]

/-- One table block's form on a side: `side_beta` plus the block's fingerprint, one tuple slot at
a time (`bus.rs:192-195`). -/
def blockForm (block : BusBlock) (sideWeights : List E) (sideBeta : E) : Form :=
  block.coordinates.zipIdx.foldl
    (fun form (coordinate, slot) ↦ form.addScaled coordinate (sideWeights.getD slot 0))
    (Form.const sideBeta)

/-- One side of the leaf decomposition (`bus.rs:183-203`): the forms with the side's table
blocks added, and the side's total. A table's form is summed over its padding rows too, whose
leaves hold `1` instead: the difference, `padding_rows`, is public. -/
def accumulateSide (forms : List (List Form)) (side : ℕ) (blocks : List BusBlock)
    (sideLayout : BusLayout) (frameworkFingerprints sideWeights : List E) (sideBeta : E)
    (point : List E) (treeValue : E) : List (List Form) × E :=
  let frameworkSelectors := sideLayout.framework.map (·.eqAbove point)
  let tableSelectors := sideLayout.tables.map (·.eqAbove point)
  let known := dot frameworkSelectors (frameworkFingerprints.map (sideBeta + ·))
  let (forms, paddingRows) := (List.zip tableSelectors blocks).foldl
    (fun (forms, paddingRows) (selector, block) ↦
      let form := blockForm block sideWeights sideBeta
      let padding := (tables.getD block.owner default).padding
      (forms.modify block.owner fun row ↦ row.modify side fun f ↦ f.addScaled form selector,
        paddingRows + selector * paddingWeight (point.take block.logRows) block.rows *
          (form.evaluate (padding.getD · 0) + 1))) (forms, 0)
  let onesPadding := sumE (frameworkSelectors ++ tableSelectors) + 1
  (forms, treeValue + known + onesPadding + paddingRows)

/-- `verify_bus_balance(layout, transcript)` (`bus.rs:106-213`). **Where the verifier gets the
value of the fixed polynomial**, the stacked bytecode's multilinear extension at the bus point
(`bus.rs:139-145`), which the statement fixes and the proof does not: from `bytecodeValue`, which
the deployed verifier computes (`computedBytecodeValue`) and the verifier inside an aggregate takes
from a claim it hands on (`claimedBytecodeValue`). -/
def verifyBusBalance (bytecodeValue : List K → List E → VerifierProgram E) (layout : Layout) :
    VerifierProgram BusResult := do
  let frameworkLogRows := [0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayout frameworkLogRows layout.push
  let pullLayout := busLayout frameworkLogRows layout.pull
  let countLayout := busLayout [] layout.count
  let alphas ← VerifierProgram.sampleChallenges busBits
  let weights := eqKernel alphas
  let beta ← VerifierProgram.sampleChallenge
  let (countRoot, point, treeValues) ← verifyGkrGrandProducts pushLayout.depth
  VerifierProgram.require (countRoot ≠ 0)
  let memoryLow := point.take layout.logMemory
  let bytecodeLow := point.take layout.logBytecode
  let memory ← VerifierProgram.readScalars 3
  let memoryFinal ← VerifierProgram.readScalar
  let bytecodeFinal ← VerifierProgram.readScalar
  let claims : List ColumnClaim :=
    (List.zipWith (fun column value ↦ ⟨column, memoryLow, value⟩) [memory0, memory1, memory2]
      memory) ++
    [⟨memoryFinalCounters, memoryLow, memoryFinal⟩, ⟨bytecodeFinalCounters, bytecodeLow,
      bytecodeFinal⟩]
  let bytecodeValue ← bytecodeValue layout.bytecode (bytecodeLow ++ alphas)
  let fp := fingerprints weights memory memoryLow bytecodeLow bytecodeValue
  let pcFinal := gpow (2 ^ layout.logBytecode - 1)
  let forms0 : List (List Form) := tables.map fun _ ↦ [{}, {}, {}]
  let (forms1, total0) := accumulateSide forms0 0 layout.push pushLayout (fp (gpow 0) 1 1)
    weights beta point (treeValues.getD 0 0)
  let (forms2, total1) := accumulateSide forms1 1 layout.pull pullLayout
    (fp pcFinal memoryFinal bytecodeFinal) weights beta point (treeValues.getD 1 0)
  let (forms3, total2) := accumulateSide forms2 2 layout.count countLayout [] [1] 0 point
    (treeValues.getD 2 0)
  return ⟨claims, point, forms3, [total0, total1, total2]⟩

/-!
## The table sumcheck (`bus.rs:215-259`)

One plain-mode sumcheck over `max` of the tables' log-heights, its challenges reversed the point;
the terminal claim is `Σ weight · (constraints + forms)`, and a table of log-height `h` has its
evaluations at the point's first `h` coordinates.
-/

/-- The tables' weights at the point (`bus.rs:231-237`): coordinate `v` contributes
`1 + equality_point[v] + r_v` to a table taller than `v`, and `r_v` to the others. -/
def tableWeights (heights : List ℕ) (equalityPoint point : List E) : List E :=
  point.zipIdx.foldl (fun weights (challenge, coord) ↦
    let equality := 1 + equalityPoint.getD coord 0 + challenge
    List.zipWith (fun weight height ↦ weight * if coord < height then equality else challenge)
      weights heights) (heights.map fun _ ↦ 1)

/-- The per-table loops of `table_sumcheck` (`bus.rs:239-257`): read each table's row
evaluations, add its weighted terms to `final`, and collect its point and evaluations. The Rust
reads every table's evaluations before it sums the terms: the same reads, in the same order. -/
def tableTerms (constraintPowers formPowers point : List E) :
    List (Table × ℕ × List Form × E) → ℕ → E → VerifierProgram (E × List (List E × List E))
  | [], _, final => return (final, [])
  | (table, height, forms, weight) :: rest, cursor, final => do
    let evaluations ← VerifierProgram.readScalars table.width
    let summand := dot ((constraintPowers.drop cursor).take table.nConstraints)
      (table.constraints evaluations)
    let final := final +
      weight * (summand + dot formPowers (forms.map (·.evaluate (evaluations.getD · 0))))
    let (final, rows) ← tableTerms constraintPowers formPowers point rest
      (cursor + table.nConstraints) final
    return (final, (point.take height, evaluations) :: rows)

/-- `table_sumcheck(tables, table_log_heights, bus_forms, constraint_powers, form_powers,
equality_point, target, transcript)` (`bus.rs:218-259`): each table's point and its columns'
evaluations there. -/
def tableSumcheck (heights : List ℕ) (busForms : List (List Form))
    (constraintPowers formPowers equalityPoint : List E) (target : E) : VerifierProgram
    (List (List E × List E)) := do
  let nRounds := heights.foldl max 0
  let (challenges, claim) ← sumcheck target 4 (List.replicate nRounds none)
  let point := challenges.reverse
  let weights := tableWeights heights equalityPoint point
  let rows := List.zip tables (List.zip heights (List.zip busForms weights))
  let (final, evaluations) ← tableTerms constraintPowers formPowers point rows 0 0
  VerifierProgram.require (final = claim)
  return evaluations

/-!
## The WHIR opening (`whir.rs`, `lib.rs:124-141`)

**Commitments.** The Rust reads a Merkle root as two scalars (`Digest::from_halves` of
`next_scalars(2)`, `whir.rs:177-178`) and opens it a level later with
`transcript.merkle(current_root, block_length, &queries, leaf_words)` (`whir.rs:196`). The
language's `commit height width` fixes the matrix shape when the root is read, so the shape is
computed from the ladder there:

* the stack's root (commitment `0`, read by `verify_execution` before the bus phase, `commitStack`)
  is opened at level `0`: `2^(log_n − folds[0] + rate_0)` leaves of `2^folds[0]` words;
* the root read at level `ℓ` (commitment `ℓ + 1`) is opened at level `ℓ + 1`:
  `2^(message_log_ℓ − folds[ℓ+1] + rate_{ℓ+1})` leaves of `3 · 2^folds[ℓ+1]` words.

Level `ℓ` therefore opens commitment `ℓ` (`VerifierProgram.queryOpenings ℓ`). The rows come back as
raw words; the level-0 reversal and the regrouping of deeper rows into `E` (`ext_row`) are the
program's.

`derive_config` is `LeanVM.Parameters.Whir.ladder`. `induced_weight` requires
`point.len() == message_log` (`whir.rs:112`); every glued claim is evaluated at
`point[fold_start..]`, the fold challenges from `fold_start` on and then the tail's, of length
`log_n − fold_start = message_log`, so the check always holds and is not repeated. The error after
the level loop (`WhirNoTerminalLevel`, `whir.rs:264`) is `VerifierProgram.fail` on an empty ladder,
which `derive_config` never returns.
-/

/-- The loop of `sample_queries`: each sample yields up to `192 / depth` positions of `depth`
bits, low bits first (`whir.rs:79-88`). -/
def sampleQueriesAux (depth : ℕ) : ℕ → ℕ → VerifierProgram (List ℕ)
  | 0, _ => return []
  | fuel + 1, remaining =>
    if remaining = 0 then return []
    else do
      let bits := eToNat (← VerifierProgram.sampleChallenge)
      let n := min (192 / depth) remaining
      let chunk := (List.range n).map fun c ↦ (bits >>> (c * depth)) % 2 ^ depth
      let rest ← sampleQueriesAux depth fuel (remaining - n)
      return chunk ++ rest

/-- `sample_queries(transcript, 2^depth, count)` (`whir.rs:75-90`), from the block's log-length
`depth` (the Rust recovers it from the length by `log2_strict`, which cannot fail).
`count` rounds of fuel suffice: each yields `min(192 / depth, remaining) ≥ 1` positions, as
`depth ≤ 64`. -/
def sampleQueries (depth count : ℕ) : VerifierProgram (List ℕ) := sampleQueriesAux depth count count

/-- `ext_row(words)`: a deeper level's leaf words regrouped into the `E` values they encode,
three per lane (`whir.rs:65-73`). A trailing partial lane, which the leaf width rules out, is
padded with zeros here and dropped by the Rust. -/
def extRow : List K → List E
  | c0 :: c1 :: c2 :: rest => E.ofLimbs c0 c1 c2 :: extRow rest
  | [c0, c1] => [E.ofLimbs c0 c1 0]
  | [c0] => [E.ofLimbs c0 0 0]
  | [] => []

/-- The level's enforced sum, `Σ_q w_q · ⟨row_q, eq(folds, ·)⟩` (`row_values` and `enforced`,
`whir.rs:197-211`). -/
def enforcedSum (rows : List (List E)) (folds queryWeights : List E) : E :=
  let laneWeights := eqKernel folds
  (List.zip queryWeights rows).foldl (fun total (w, row) ↦ total + w * dot row laneWeights) 0

/-- The layers of `subspace_roots`: square-and-shift the layer by the last root, pop the next
root (`whir.rs:96-102`). -/
def subspaceRootsAux : ℕ → E → List E → List E
  | 0, _, _ => []
  | n + 1, last, layer =>
    match layer.map fun value ↦ value ^ 2 + last * value with
    | [] => []
    | root :: rest => root :: subspaceRootsAux n root rest

/-- `subspace_roots(log_n)`: `1`, then the `log_n` subspace polynomial values (`whir.rs:92-104`;
in `K` there, embedded in `E` here). -/
def subspaceRoots (logN : ℕ) : List E :=
  1 :: subspaceRootsAux logN 1 ((List.range logN).map fun i ↦ eOfNat (2 ^ (i + 1)))

/-- `induced_weight(message_log, queries, query_weights, point)`: the level's batched query
claims as one weight at `point`, `Σ_q w_q Π_k (1 + p_k (1 + Ŵ_k(x_q)))` (`whir.rs:106-126`;
`K::inv` maps zero to zero). -/
def inducedWeight (messageLog : ℕ) (queries : List ℕ) (queryWeights point : List E) : E :=
  let roots := subspaceRoots messageLog
  let inverses := roots.map fun value ↦ if value = 0 then 0 else value⁻¹
  (List.zip queryWeights queries).foldl (fun total (weight, query) ↦
    let product := point.zipIdx.foldl (fun (acc : E × E) (challenge, coordinate) ↦
      (acc.1 * (1 + challenge * (1 + acc.2 * inverses.getD coordinate 0)),
        acc.2 ^ 2 + roots.getD coordinate 0 * acc.2)) (weight, eOfNat query)
    total + product.1) 0

/-- `GluedClaim`: a claim folded into the running sumcheck, and the weight it owes back
(`whir.rs:130-139`). -/
structure GluedClaim where
  /-- The power of the level's `λ` it was glued with. -/
  scalar : E
  /-- How many fold challenges preceded the level. -/
  foldStart : ℕ
  /-- Its weight at the terminal point, restricted to the level's message coordinates. -/
  weightAt : List E → E

/-! ### The level loop (`whir.rs:158-264`) -/

/-- The running state of `verify_whir`: `running_quad`, every fold challenge so far, and the glued
claims so far (`running_target` is the final level's tail rounds', `tailRounds`). -/
structure WhirState where
  /-- `running_quad`: the running sumcheck's quadratic. -/
  runningQuad : List E
  /-- Every fold challenge so far. -/
  folds : List E
  /-- The glued claims so far. -/
  glued : List GluedClaim

/-- A level's fold rounds: sample, fold the running claim, read the next quadratic (`whir.rs`).
Returns the state and the level's own challenges. -/
def foldRounds : ℕ → WhirState → List E → VerifierProgram (WhirState × List E)
  | 0, s, levelFolds => return (s, levelFolds)
  | n + 1, s, levelFolds => do
    let challenge ← VerifierProgram.sampleChallenge
    let quad ← sumcheckRoundPoly 3 (polyEval s.runningQuad challenge) none
    foldRounds n { s with runningQuad := quad, folds := s.folds ++ [challenge] }
      (levelFolds ++ [challenge])

/-- The final level's tail rounds: sample, fold, and read the next quadratic unless it is the
last round (`whir.rs:237-246`). The tail challenges and the final running claim. With no round
the Rust compares against `ZERO` and this fails; the ladder never leaves the final level fewer than
two variables. -/
def tailRounds : ℕ → List E → VerifierProgram (List E × E)
  | 0, _ => VerifierProgram.fail
  | n + 1, quad => do
    let challenge ← VerifierProgram.sampleChallenge
    let target := polyEval quad challenge
    if n = 0 then return ([challenge], target)
    else do
      let quad ← sumcheckRoundPoly 3 target none
      let (rest, target) ← tailRounds n quad
      return (challenge :: rest, target)

/-- Glue a level's pending claims, each an intro message and a weight, into the running sumcheck
with powers of `λ`, the running claim keeping `λ⁰` (`whir.rs:221-232`). -/
def glue (lam : E) (state : WhirState) (pending : List (List E × (List E → E))) : WhirState :=
  (pending.foldl (fun (acc : WhirState × E) (intro, weightAt) ↦
    let scalar := acc.2 * lam
    let state := acc.1
    ({ state with
        runningQuad := List.zipWith (fun q i ↦ q + scalar * i) state.runningQuad intro,
        glued := state.glued ++ [⟨scalar, state.folds.length, weightAt⟩] }, scalar)) (state, 1)).1

/-- The shape of the commitment a level opens: `2^(message_log + rate)` leaves of `width`
words, the message log being the one after the level's folds. -/
def levelShape (messageLogBefore : ℕ) (level : Whir.Level) (width : ℕ) : ℕ × ℕ :=
  (messageLogBefore - level.fold + level.logInvRate, width)

/-- One level of `verify_whir` and every level after it (`whir.rs:158-262`). `index` is
the level's index, which is also the index of the commitment it opens; `laneFolds` is
`config.folds[0]`. -/
def whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ℕ → List Whir.Level → WhirState → VerifierProgram Unit
  | _, [], _ => VerifierProgram.fail
  | index, level :: rest, s => do
    let (s, levelFolds) ← foldRounds level.fold s []
    let messageLog := logN - s.folds.length
    -- The level's claims: the residual on the final level; otherwise the next commitment and
    -- its out-of-domain claim.
    let (residual, pending) ← match rest with
      | [] => do
        let residual ← VerifierProgram.readScalars (2 ^ messageLog)
        pure (residual, ([] : List (List E × (List E → E))))
      | next :: _ => do
        let (height, width) := levelShape messageLog next (3 * 2 ^ next.fold)
        VerifierProgram.readCommitment height width
        let oodPoint ← VerifierProgram.sampleChallenges messageLog
        let oodValue ← VerifierProgram.readScalar
        let intro ← sumcheckRoundPoly 3 oodValue none
        pure ([], [(intro, fun x ↦ eqEval oodPoint x)])
    VerifierProgram.grindProofOfWork Whir.queryGrindingBits
    let queries ← sampleQueries (messageLog + level.logInvRate) level.queries
    let lam ← VerifierProgram.sampleChallenge
    let queryWeights := powers lam queries.length
    let words ← VerifierProgram.queryOpenings index queries
    let rows : List (List E) :=
      if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow
    let enforced := enforcedSum rows levelFolds queryWeights
    let intro ← sumcheckRoundPoly 3 enforced none
    let pending := pending ++ [(intro, fun x ↦ inducedWeight messageLog queries queryWeights x)]
    let s := glue lam s pending
    match rest with
    | [] => do
      let (tailFolds, target) ← tailRounds messageLog s.runningQuad
      let point := s.folds ++ tailFolds
      let weight := s.glued.foldl
        (fun weight claim ↦
          weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ tailFolds))
        (evaluateBasis (point.drop laneFolds ++ point.take laneFolds))
      let terminal := weight * multilinearEval residual tailFolds
      VerifierProgram.require (terminal = target)
    | _ :: _ => whirLevels logN laneFolds evaluateBasis (index + 1) rest s

/-- `verify_whir(transcript, log_n, log_inv_rate, target, root, evaluate_basis)`, the root being
commitment `0` (`whir.rs:141-265`). -/
def verifyWhir (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E) : VerifierProgram
    Unit := do
  let config ← liftOption (Whir.ladder logN logInvRate)
  let quad ← sumcheckRoundPoly 3 target none
  whirLevels logN ((config.head?.map (·.fold)).getD 0) evaluateBasis 0 config ⟨quad, [], []⟩

/-- Read the stack's root (`verify_execution`, step 2, `lib.rs:237-239`): commitment `0`, the
shape level `0` opens it at. -/
def commitStack (logN logInvRate : ℕ) : VerifierProgram Unit := do
  let config ← liftOption (Whir.ladder logN logInvRate)
  match config with
  | [] => VerifierProgram.fail
  | level :: _ =>
    let (height, width) := levelShape logN level (2 ^ level.fold)
    VerifierProgram.readCommitment height width

/-- `verify_stacked_opening(transcript, root, stack_log, log_inv_rate, claims)`: batch the claims
with powers of one challenge into one WHIR opening (`lib.rs:124-141`). -/
def verifyStackedOpening (stackLog logInvRate : ℕ) (claims : List StackClaim) : VerifierProgram
    Unit := do
  let scales := powers (← VerifierProgram.sampleChallenge) claims.length
  verifyWhir stackLog logInvRate (dot scales (claims.map (·.2)))
    fun point ↦ dot scales (claims.map fun c ↦ c.1 point)

/-!
## Keccak, by GKR over its rounds (`keccak.rs`)

The protocol is `doc/leanvm/body/c-keccak-gkr.tex`; `KECCAK_RC`, `KECCAK_RHO`, `KECCAK_PI`
(`crates/verifier/src/hash.rs:11-49`) are `keccakRC`, `keccakRho`, `keccakPi` of `Keccak.lean`.
A claim is a weighted sum of the bits of one state per segment, the weight of bit `j` of instance
`i` of pack `y` (sixteen consecutive steps) in segment `m` being
`eq(point, (y, m)) · weights[j] · mu[i]`; each layer turns a claim on the states after a round into
one on the states before it.

**Representation.**

* The Rust tabulates the embedding, `RMFE_EMBED` and `RMFE_PROJECT` (`keccak.rs:22-46`); it is
  derived here (`rmfe`), from integer polynomials over `GF(2)` as natural numbers, bit `i` the
  coefficient of `x^i`. Their loops are bounded by fuel: `carryless a b` by `b` (each step halves
  `b`), `carrylessDivmod a f` by the bit length of `a` plus one (each step lowers the bit length of
  the remainder when `f ≠ 0`; `f = 0` is never passed).
* A factor's inverse is the first `g` in `1 .. 2^degree - 1` that inverts the cofactor modulo the
  factor, by `List.find?`, `0` if none (every factor of `rmfeFactors` is irreducible, so one is
  found).
* The weight array `g` of `linear_transpose` is an array here, set where the Rust sets it.
-/

/-! ### Constants (`keccak.rs:14-17`) -/

/-- `EMBED_BITS`: a pack's bits embed in a polynomial of `24` coefficients (`keccak.rs:16`). -/
def embedBits : ℕ := 24

/-- `PRODUCT_BITS = 2 · EMBED_BITS − 1`: the product of two embeddings has `47` coefficients
(`keccak.rs:17`). -/
def productBits : ℕ := 2 * embedBits - 1

/-- The moduli the embedding is glued from, with the bits each holds. -/
def rmfeFactors : List (ℕ × ℕ) :=
  [(0b10, 1), (0b11, 1), (0b1011, 2), (0b1101, 2), (0b100101, 3), (0b101001, 3), (0b101111, 3)]

/-! ### The embedding (`RMFE_EMBED`, `RMFE_PROJECT`, `keccak.rs:22-46`) -/

/-- The loop of `carryless`: while `b ≠ 0`, add `a` if `b`'s low bit is set, then shift. -/
def carrylessAux : (fuel a b out : ℕ) → ℕ
  | 0, _, _, out => out
  | fuel + 1, a, b, out =>
    if b = 0 then out
    else carrylessAux fuel (a <<< 1) (b >>> 1) (if b % 2 = 1 then out ^^^ a else out)

/-- `carryless a b`: the product of two binary polynomials. -/
def carryless (a b : ℕ) : ℕ := carrylessAux b a b 0

/-- The loop of `carrylessDivmod`: while the remainder is nonzero and no shorter than `f`,
subtract `f` shifted under its leading bit. -/
def carrylessDivmodAux : (fuel f quotient a : ℕ) → ℕ × ℕ
  | 0, _, quotient, a => (quotient, a)
  | fuel + 1, f, quotient, a =>
    if a ≠ 0 ∧ bitLength f ≤ bitLength a then
      let shift := bitLength a - bitLength f
      carrylessDivmodAux fuel f (quotient ||| (1 <<< shift)) (a ^^^ (f <<< shift))
    else (quotient, a)

/-- `carrylessDivmod a f`: the quotient and remainder of binary polynomials. -/
def carrylessDivmod (a f : ℕ) : ℕ × ℕ := carrylessDivmodAux (bitLength a + 1) f 0 a

/-- The parity of the set bits. -/
def bitParity (n : ℕ) : ℕ := ((List.range (bitLength n)).countP fun i ↦ n.testBit i) % 2

/-- The product of the moduli, by `carryless`. -/
def rmfeModulus : ℕ :=
  match rmfeFactors.map Prod.fst with
  | [] => 0
  | f :: fs => fs.foldl carryless f

/-- One factor's share of `rmfe`: its bits' embeddings (the residues,
lifted through the Chinese remainder theorem), and per bit the projection's mask, the product
coefficients whose parity is the bit. -/
def rmfeFactor (modulus f bits : ℕ) : List ℕ × List ℕ :=
  let cofactor := (carrylessDivmod modulus f).1
  let degree := bitLength f - 1
  let inverse := (((List.range (2 ^ degree)).drop 1).find? fun g ↦
    (carrylessDivmod (carryless (carrylessDivmod cofactor f).2 g) f).2 = 1).getD 0
  let lift := (carrylessDivmod (carryless cofactor inverse) modulus).2
  -- A residue is the polynomial taking the bits as its values at 0, 1 and infinity.
  let residues : List ℕ := if bits = 1 then [1] else if bits = 2 then [0b11, 0b10]
    else [0b011, 0b010, 0b110]
  let embed := residues.map fun r ↦ (carrylessDivmod (carryless lift r) modulus).2
  let masks := (List.range productBits).foldl (fun masks c ↦
    let g := (carrylessDivmod (1 <<< c) f).2
    let atZero := g % 2
    let atOne := bitParity g
    let values : List ℕ := if bits = 1 then [if f = 0b10 then atZero else atOne]
      else if bits = 2 then [atZero, atOne] else [atZero, atOne, g >>> 4]
    List.zipWith (fun mask value ↦ mask ||| (value <<< c)) masks values)
    (List.replicate bits 0)
  (embed, masks)

/-- The embedding (`keccak.rs:22-24`): sixteen bits embed in a binary polynomial of degree at
most `23`, and a product of two embeddings projects to the AND of what they embed. Each unit
vector's embedding, and per bit of the projection the product coefficients it is the parity of;
the last bit rides the leading coefficient, which the residues do not see. -/
def rmfe : List ℕ × List ℕ :=
  let (embed, project) := rmfeFactors.foldl (fun (acc : List ℕ × List ℕ) (f, bits) ↦
    let (e, p) := rmfeFactor rmfeModulus f bits
    (acc.1 ++ e, acc.2 ++ p)) ([], [])
  (embed ++ [rmfeModulus], project ++ [1 <<< (productBits - 1)])

/-- `RMFE_EMBED` (`keccak.rs:25-28`). -/
def rmfeEmbed : List ℕ := rmfe.1

/-- `RMFE_PROJECT` (`keccak.rs:29-46`). -/
def rmfeProject : List ℕ := rmfe.2

/-! ### Claims and the round's linear map (`keccak.rs:70-113`) -/

/-- `Claim` (`keccak.rs:70-75`): a claim's value, the weight of each instance of a pack, its point
(a pack index, then a segment index), and the weight of each bit position. -/
structure KeccakClaim where
  /-- The claimed value. -/
  value : E
  /-- The weight of each instance of a pack. -/
  mu : List E
  /-- Its point: a pack index, then a segment index. -/
  point : List E
  /-- The weight of each bit position. -/
  weights : List E
  deriving Inhabited

/-- `along(j, k)`: the position `k` columns along from `j`, in the same row and slice
(`keccak.rs:77-81`). -/
def keccakAlong (j k : ℕ) : ℕ :=
  let lane := j / 64
  let z := j % 64
  64 * ((lane % 5 + k) % 5 + 5 * (lane / 5)) + z

/-- `linear_transpose(w)` (`keccak.rs:83-101`): the transpose of θ, ρ, π on weight
vectors, `⟨w, L(a)⟩ = ⟨Lᵀ(w), a⟩`. `g` is the weight each position of θ's output carries. -/
def keccakLinearTranspose (w : List E) : List E :=
  let w := w.toArray
  let g : Array E := (List.range 25).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
    g.setIfInBounds (64 * lane + z)
      (w.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
    (Array.replicate keccakBits 0)
  let columns : Array E := ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
    sumE ((List.range 5).map fun y ↦ g.getD (64 * (x + 5 * y) + z) 0)).toArray
  (List.range 25).flatMap fun lane ↦ (List.range 64).map fun z ↦
    g.getD (64 * lane + z) 0 + columns.getD (64 * ((lane % 5 + 1) % 5) + z) 0 +
      columns.getD (64 * ((lane % 5 + 4) % 5) + (z + 1) % 64) 0

/-- `instance_weights(s)` (`keccak.rs:103-113`): the instance weights of a claim made
at the polynomial point `s`, each unit vector's embedding at `s`. -/
def keccakInstanceWeights (s : E) : List E :=
  let sPowers := powers s embedBits
  rmfeEmbed.map fun e ↦
    sumE ((List.range embedBits).filterMap fun b ↦
      if e.testBit b then some (sPowers.getD b 0) else none)

/-! ### A layer (`keccak.rs:115-196`) -/

/-- Step 3 of a layer, the pack and the segment (`keccak.rs:152-161`): an equality-mode round
per coordinate of the claim's point, the value scaled by `1 + r + challenge`. The new value, the
product of the scales, and the challenges. -/
def keccakPackRounds : List E → E → E → VerifierProgram (E × E × List E)
  | [], value, scale => return (value, scale, [])
  | r :: rs, value, scale => do
    let message ← sumcheckRoundPoly 3 value (some r)
    let challenge ← VerifierProgram.sampleChallenge
    let (value, scale, point) ← keccakPackRounds rs
      ((1 + r + challenge) * polyEval message challenge) (scale * (1 + r + challenge))
    return (value, scale, challenge :: point)

/-- `verify_layer(transcript, shape, step, claim)` (`keccak.rs:115-196`): a claim on the states
`step` layers below the committed outputs becomes one on the states a layer further down. The Rust
splits `eq(local, j)`, `j = 64 · lane + z`, into `eq_z[z] · eq_lane[lane]` (`keccak.rs:166-189`);
here it is the one kernel `eqKernel localPoint`, the same values. -/
def verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaim) : VerifierProgram KeccakClaim := do
  let packBits := logSteps - 4
  -- 1] The product polynomial: the claim's weighted sum of the packs' unprojected chi.
  let product ← VerifierProgram.readScalars productBits
  let projected := sumE ((List.range productBits).map fun c ↦
    sumE ((List.zip claim.mu rmfeProject).filterMap fun (m, mask) ↦
      if mask.testBit c then some m else none) * product.getD c 0)
  -- iota flips known positions of lane 0 in every instance.
  let segments := eqKernel (claim.point.drop packBits)
  let iota := sumE ((List.range keccakSegments).map fun segment ↦
    let constant := keccakRC.getD (keccakDepth * (segment + 1) - step - 1) 0
    segments.getD segment 0 * sumE ((List.range 64).filterMap fun z ↦
      if constant.toNat.testBit z then some (claim.weights.getD z 0) else none))
  VerifierProgram.require (projected + iota * sumE claim.mu = claim.value)
  -- 2] At a random point a pack is one field element, and the polynomial's value a sumcheck
  -- claim.
  let s ← VerifierProgram.sampleChallenge
  let mu := keccakInstanceWeights s
  let kappa := sumE mu
  -- 3] The pack and the segment.
  let (value, scale, point) ← keccakPackRounds claim.point (polyEval product s) 1
  -- 4] The bit position: `Σ_j w[j] (κ T[j] + (κ + T[j + 1]) T[j + 2])`.
  let (localPoint, value) ← sumcheck value 4 (List.replicate keccakLocalBits none)
  let t ← VerifierProgram.readScalars 3
  let eq := eqKernel localPoint
  let t0 := t.getD 0 0
  let t1 := t.getD 1 0
  let t2 := t.getD 2 0
  VerifierProgram.require
    (scale * dot (eq.take keccakBits) claim.weights * (kappa * t0 + (kappa + t1) * t2) = value)
  -- 5] `t[k] = Σ_j eq[j] T[j + k]`: one claim on the state before chi, then on the round's
  -- input through the linear map.
  let beta ← VerifierProgram.sampleChallenge
  let weights := (List.range keccakBits).map fun j ↦
    eq.getD j 0 + beta * (eq.getD (keccakAlong j 4) 0 + beta * eq.getD (keccakAlong j 3) 0)
  return ⟨t0 + beta * (t1 + beta * t2), mu, point, keccakLinearTranspose weights⟩

/-- The layers, `step` from `0` to `KECCAK_DEPTH - 1` (`keccak.rs:264-267`). -/
def keccakLayers (logSteps : ℕ) : List ℕ → KeccakClaim → VerifierProgram KeccakClaim
  | [], claim => return claim
  | step :: steps, claim => do
    let claim ← verifyKeccakLayer logSteps step claim
    keccakLayers logSteps steps claim

/-! ### Opening `q_keccak` (`keccak.rs:198-294`) -/

/-- The weights of `open` (`keccak.rs:208-221`): the weight a claim puts on each
`(slot, z)`, its position weights on the slots of the states it speaks of, scaled by the segment;
`first` is the state segment `0` claims, and only the first `count` segments' states are committed.
The slots above the states (`qkeccakSlots …`), which carry `KECCAK` columns, weigh nothing. -/
def keccakSlotWeights (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) : List (List E) :=
  let segments := eqKernel (claim.point.drop (logSteps - 4))
  let weights := claim.weights.toArray
  let rows : Array (Array E) := (List.range count).foldl (fun rows segment ↦
    (List.range keccakBits).foldl (fun rows j ↦
      rows.modify (25 * (first + segment) + j / 64) fun row ↦
        row.setIfInBounds (j % 64) (segments.getD segment 0 * weights.getD j 0)) rows)
    (Array.replicate (2 ^ qkeccakSlotBits) (Array.replicate 64 0))
  rows.toList.map Array.toList

/-- `open(transcript, shape, claim, first, count, value)` (`keccak.rs:198-223`): a sumcheck over
the slot; the point it ends on, the weight the claim puts on each slice there, and what is left to
match. The sumcheck draws nothing from the weights, so computing them after it, as the pin does,
or before is the same. The Rust sums each slot's row scaled by `eq(slot, ·)` (`eq_kernel(&slot)`);
here the table of rows is folded by the slot's challenges, the same values. -/
def keccakOpen (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    VerifierProgram (List E × List E × E) := do
  let (slot, value) ← sumcheck value 3 (List.replicate qkeccakSlotBits none)
  let rows := slot.foldl (fun rows challenge ↦
    (List.range (rows.length / 2)).map fun i ↦
      List.zipWith (fun lo hi ↦ lo + challenge * (lo + hi)) (rows.getD (2 * i) [])
        (rows.getD (2 * i + 1) [])) (keccakSlotWeights logSteps claim first count)
  return (slot, rows.headD [], value)

/-- The first claim of `verify_keccak` (`keccak.rs:247-263`), on every segment's output at
`instance` and the segment `segment`: the last segment's output is the permutation's, claimed by
the table's lanes `output`, the others' `committed`; the lanes are combined as words at
`lanePoint`, bit `z` of a word weighing `x^z`. -/
def keccakFirstClaim (inst segment lanePoint output : List E) (committed : E) : KeccakClaim :=
  let lanes := eqKernel lanePoint
  let weights := (List.range keccakBits).map fun j ↦ lanes.getD (j / 64) 0 * eOfNat (2 ^ (j % 64))
  let last := (eqKernel segment).getD (keccakSegments - 1) 0 * dot (lanes.take 25) output
  ⟨committed + last, eqKernel (inst.take 4), inst.drop 4 ++ segment, weights⟩

/-- `verify_keccak(transcript, shape, instance, output)` (`keccak.rs:225-294`): the reduction, a
random claim on every segment's output at `instance`, `KECCAK_DEPTH` layers down to the committed
inputs. The last segment's output is the permutation's, claimed by the table's lanes `output` at
`instance`; the others are committed. It leaves openings of `q_keccak`: the committed outputs as
words at one point (column claims), and the column's 64 slices at another (the point and the
slices, for ring switching). The Rust first checks the shape (`keccak.rs:243-246`), which the
`KECCAK` table's point and lanes always meet, its log-height at least `keccakMinStepsLog`. -/
def verifyKeccak (logSteps : ℕ) (inst output : List E) : VerifierProgram
    (List ColumnClaim × List E × List E) := do
  let packBits := logSteps - 4
  let rLow := inst.take 4
  let segment ← VerifierProgram.sampleChallenges keccakSegmentBits
  let lanePoint ← VerifierProgram.sampleChallenges keccakLaneBits
  let committed ← if 1 < keccakSegments then VerifierProgram.readScalar else pure 0
  let first := keccakFirstClaim inst segment lanePoint output committed
  let claim ← keccakLayers logSteps (List.range keccakDepth) first
  -- The committed outputs, whose instance weights are an eq already: slice 0 holds the slot's
  -- weight, the others `x^z` times it.
  let outputs ← if 1 < keccakSegments then do
      let (slot, weights, value) ← keccakOpen logSteps first 1 (keccakSegments - 1) committed
      let word ← VerifierProgram.readScalar
      VerifierProgram.require (weights.headD 0 * word = value)
      pure [(⟨qkeccak, rLow ++ inst.drop 4 ++ slot, word⟩ : ColumnClaim)]
    else pure []
  -- The inputs: the instances of a pack first, then the slot.
  let (low, value) ← sumcheck claim.value 3 (List.replicate 4 none)
  let (slot, weights, value) ← keccakOpen logSteps claim 0 keccakSegments value
  let slices ← VerifierProgram.readScalars kBits
  VerifierProgram.require (multilinearEval claim.mu low * dot weights slices = value)
  return (outputs, low ++ claim.point.take packBits ++ slot, slices)

/-!
## Ring switching (`crates/verifier/src/ring_switch.rs`)

The 64 claims `s[i] = z(i, point)` on `q_keccak`'s bit slices become one dense claim
`Σ_u W(u) q_keccak(u) = target` on the committed column.
-/

/-- `RING_MAP_SHIFTS` (`ring_switch.rs:9`; `COMPOSITION_SHIFTS`,
`crates/pcs/src/ring_switch.rs:82`): the Frobenius shifts of the six stages composing `Φ`, one
challenge each. -/
def ringMapShifts : List ℕ := [32, 16, 8, 4, 2, 1]

/-- `ring_map(value, challenges)`: `a ↦ a + f_p · a^(2^shift)`, stage by stage
(`ring_switch.rs:11-17`). -/
def phiMap (value : E) (challenges : List E) : E :=
  (List.zip challenges ringMapShifts).foldl
    (fun value (challenge, shift) ↦ value + challenge * value ^ (2 ^ shift)) value

/-- `ring_weight(r, r_prime, coefficients)`: `Σ_k c_k Π_n (1 + r_n^(2^k) + r'_n)`
(`ring_switch.rs:19-34`). -/
def ringWeight (r rPrime coefficients : List E) : E :=
  (coefficients.foldl (fun (acc : E × List E) c ↦
    let product := (List.zip acc.2 rPrime).foldl
      (fun product (value, challenge) ↦ product * (1 + value + challenge)) c
    (acc.1 + product, acc.2.map (· ^ 2))) (0, r)).1

/-- The Frobenius coefficients of the drawn map, `Φ(a) = Σ_{k < 64} c_k a^(2^k)`
(`ring_switch.rs:42-50`). -/
def ringCoefficients (challenges : List E) : List E :=
  (List.range kBits).map fun k ↦
    ((List.zip challenges ringMapShifts).filter fun (_, s) ↦ k &&& s ≠ 0).foldl
      (fun acc (f, s) ↦ acc * f ^ (2 ^ (k % s))) 1

/-- `ring_switch(point, s, transcript)` (`ring_switch.rs:36-54`): draw the map, and return the
target `Σ_i g^i Φ(s_i)` and the weight `W(u) = Φ(eq(point, u))` as a function of the opening
point. -/
def ringSwitch (point s : List E) : VerifierProgram (E × (List E → E)) := do
  let challenges ← VerifierProgram.sampleChallenges ringMapShifts.length
  let coefficients := ringCoefficients challenges
  let target := polyEval (s.map (phiMap · challenges)) gen
  return (target, fun rPrime ↦ ringWeight point rPrime coefficients)

open LeanVM.Semantics LeanVM.Protocol.KeccakHash

/-!
## The leanVM verifier (`lib.rs:156-159, 217-331`; `layout.rs:64-68`; `transcript.rs:33-46`)

`leanVmVerifierProgram bytecode publicInput` is `verify_execution` in the verifier language, one
`VerifierProgram` function per numbered step of the Rust's `walk` (the steps of `verifyExecution`).
The program returns `true` where the Rust returns `Ok`; `Transcript::finish`, the check that the
proof is consumed, is `runProof`'s.

**The seed.** The sponge starts at Keccak-f of `IV ‖ public_input ‖ 0^17`, `IV` the Keccak-256 hash
of `TAG ‖ bytecode`, the tag `"leanvm-v1"` naming the proof system's version and the bytecode as its
little-endian words. The seed's input has the capacity lanes zero, Keccak-256's initial state, and
nothing separates its domain from a Keccak-256 block: in the random-permutation model the
transcript's duplex calls and Keccak-256's sponge calls query the one permutation from states of the
same kind. This is harmless for the end statements, which are proved for exactly this experiment.
-/

/-- The announced sizes, read and checked, and the layout they give
(`lib.rs:221-235`): the layout and the WHIR rate exponent. -/
def readAnnouncedSizes (bytecode : List K) : VerifierProgram (Layout × ℕ) := do
  let announced ← VerifierProgram.readScalars (2 + tables.length)
  VerifierProgram.require (announced.all fun value ↦ value.limb 1 = 0 ∧ value.limb 2 = 0)
  let logMemory := kToNat ((announced.headD 0).limb 0)
  let tableRows := ((announced.drop 1).take tables.length).map fun value ↦ kToNat (value.limb 0)
  let logInverseRate := kToNat ((announced.getLastD 0).limb 0)
  VerifierProgram.require (1 ≤ logInverseRate ∧ logInverseRate ≤ 4)
  let layout ← liftOption (buildLayout bytecode logMemory tableRows)
  VerifierProgram.require (Whir.minLogStack ≤ layout.stackLog ∧ layout.stackLog ≤ Whir.maxLogStack)
  return (layout, logInverseRate)

/-- Step 4, the table sumcheck at the bus point (`lib.rs:244-260`): each table's point and
evaluations. -/
def tablePhase (layout : Layout) (bus : BusResult) : VerifierProgram (List (List E × List E)) := do
  let xi ← VerifierProgram.sampleChallenge
  let nConstraints := (tables.map Table.nConstraints).sum
  let xiPowers := powers xi (nConstraints + 3)
  let constraintPowers := xiPowers.take nConstraints
  let formPowers := xiPowers.drop nConstraints
  let target := dot formPowers bus.totals
  tableSumcheck layout.tableLogHeights bus.forms constraintPowers formPowers bus.point target

/-- The tables' column claims (`lib.rs:261-268`): each table's evaluations at its point,
on the table's global columns. -/
def tableColumnClaims (evaluations : List (List E × List E)) : List ColumnClaim :=
  (globalColumnBases.zip evaluations).flatMap fun (base, point, values) ↦
    values.zipIdx.map fun (value, column) ↦ ⟨base + column, point, value⟩

/-- Step 5, binding the public input (`lib.rs:270-283`): a challenge, and claims on the
three memory columns at `(challenge, 0, …, 0)`, each limb's claim the line through that limb of
the public input's two halves, evaluated at the challenge by the verifier itself. The prover sends
nothing. -/
def publicInputPhase (layout : Layout) (publicInput : Digest) : VerifierProgram
    (List ColumnClaim) := do
  let publicChallenge ← VerifierProgram.sampleChallenge
  let halves := digestHalves publicInput
  let publicLimbs := ([0, 1, 2] : List (Fin 3)).map fun limb ↦
    multilinearEval [ofK (halves.1.limb limb), ofK (halves.2.limb limb)] [publicChallenge]
  let publicPoint := publicChallenge ::
    List.replicate ((layout.placement memory0).variableCount - 1) 0
  return List.zipWith (fun column value ↦ ⟨column, publicPoint, value⟩)
    [memory0, memory1, memory2] publicLimbs

/-- Step 6, `KECCAK`'s validity (`lib.rs:285-302`): the `KECCAK` table's point and its
output lanes' evaluations, `values[KECCAK_OUT..KECCAK_OUT + STATE_LANES]`, are the Keccak
reduction's claim on the permutation's output. The reduction's column claims, and the point and
slices of `q_keccak` it leaves for ring switching. -/
def keccakPhase (layout : Layout) (evaluations : List (List E × List E)) : VerifierProgram
    (List ColumnClaim × List E × List E) :=
  let (point, values) := evaluations.getD opKeccak ([], [])
  verifyKeccak (layout.tableLogHeights.getD opKeccak 0) point
    ((List.range 25).map fun lane ↦ values.getD (keccakOut + lane) 0)

/-- Step 7's ring-switching claim on the stack: supported on `q_keccak`'s region, its weight
carries the placement's selector (`lib.rs:307-313`). -/
def ringSwitchClaim (layout : Layout) (target : E) (weight : List E → E) : StackClaim :=
  let qkeccakPlacement := layout.placement qkeccak
  (fun x ↦ qkeccakPlacement.eqAbove x * weight (x.take qkeccakPlacement.variableCount), target)

/-- `verify_execution(bytecode, public_input, proof)` without its `finish` (`walk`,
`lib.rs:217-322`), the fixed polynomial's value from `bytecodeValue`. -/
def verifyExecution (bytecodeValue : List K → List E → VerifierProgram E) (bytecode : List K)
    (publicInput : Digest) : VerifierProgram Unit := do
  -- 1] memory log-size, table row counts, and the WHIR rate
  let (layout, logInverseRate) ← readAnnouncedSizes bytecode
  -- 2] the stack's commitment
  commitStack layout.stackLog logInverseRate
  -- 3] the bus
  let bus ← verifyBusBalance bytecodeValue layout
  -- 4] the table sumcheck, and the tables' column claims
  let evaluations ← tablePhase layout bus
  let claims := bus.claims ++ tableColumnClaims evaluations
  -- 5] the public input
  let publicClaims ← publicInputPhase layout publicInput
  let claims := claims ++ publicClaims
  -- 6] KECCAK validity, by GKR over the rounds
  let (outputs, keccakPoint, keccakSlices) ← keccakPhase layout evaluations
  let claims := claims ++ outputs
  -- 7] ring switching, then one opening of the stack for every claim with a placement
  let (ringTarget, ringWeight) ← ringSwitch keccakPoint keccakSlices
  verifyStackedOpening layout.stackLog logInverseRate
    (ringSwitchClaim layout ringTarget ringWeight :: claims.filterMap (·.onStack layout))

/-! ### The fixed polynomial's value -/

/-- The deployed verifier computes the fixed polynomial's value (`Bytecode::evaluate`,
`crates/verifier/src/bytecode.rs:99-136`, the same value by a sparse sum). -/
def computedBytecodeValue (words : List K) (point : List E) : VerifierProgram E :=
  pure (multilinearEval (words.map ofK) point)

/-- What a proof claims of the fixed polynomial, for a verifier that does not evaluate it: the
bytecode's value at its point. -/
structure BytecodeClaim where
  bytecodePoint : List E
  bytecodeValue : E

/-- The value claimed by `claim`, at the point of `claim` only: the run fails where the verifier
asks elsewhere. -/
def claimedBytecodeValue (claim : BytecodeClaim) (_ : List K) (point : List E) : VerifierProgram
    E := do
  VerifierProgram.require (point = claim.bytecodePoint)
  return claim.bytecodeValue

/-- The claim's value is the bytecode's multilinear extension at its point (the value only;
`DeferredClaim.HoldsWithShape`, `LeanVmGuest.lean`, adds the shape and the
power-of-two length). -/
def BytecodeClaim.Holds (bytecode : List K) (claim : BytecodeClaim) : Prop :=
  multilinearEval (bytecode.map ofK) claim.bytecodePoint = claim.bytecodeValue

/-! ### The programs -/

/-- **The leanVM verifier program**: `verify_execution` in the verifier language, accepting
where the Rust returns `Ok`. -/
def leanVmVerifierProgram (bytecode : List K) (publicInput : Digest) : VerifierProgram Bool := do
  verifyExecution computedBytecodeValue bytecode publicInput
  return true

/-- The verifier program with the fixed polynomial's value claimed by `claim`. -/
def deferringVerifierProgram (claim : BytecodeClaim) (bytecode : List K) (publicInput : Digest) :
    VerifierProgram Bool := do
  verifyExecution (claimedBytecodeValue claim) bytecode publicInput
  return true

/-! ### The seed and the compiled verifier -/

/-- `TAG`, the proof system's version (`layout.rs:64-68`), as
bytes. -/
def versionTag : Bytes := "leanvm-v1".toUTF8.toList

section Hash

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- The IV over the permutation `π`: Keccak-256 over `π` of the tag, then the bytecode as its
little-endian words (`Bytecode::new`, `bytecode.rs:46-53`). -/
def fiatShamirIvWith (bytecode : List K) : m Digest :=
  keccak256With π (versionTag ++ bytecode.flatMap K.toBytes)

/-- The sponge's initial state over the permutation `π`: `π` of the IV's and the public input's
words, the other lanes zero (`Sponge::new`, `transcript.rs:33-46`). -/
def spongeSeedWith (bytecode : List K) (publicInput : Digest) : m KeccakState := do
  let fiatShamirIv ← fiatShamirIvWith π bytecode
  π (seedInput fiatShamirIv publicInput)

/-- The compiled verifier over the permutation `π`: the program run on the proof from the seed. -/
def verifyWith (bytecode : List K) (publicInput : Digest) (proof : Proof) : m Bool := do
  let seed ← spongeSeedWith π bytecode publicInput
  runProof π (leanVmVerifierProgram bytecode publicInput) seed proof

/-- **The deferring verifier** over the permutation `π`, as an aggregate runs it on a child's proof
(`verify_sub`): the IV is given rather than hashed from the bytecode, and the fixed polynomial's
value is the one claimed by `claim`. Only the bytecode's length is read. -/
def verifyDeferredWith (bytecode : List K) (iv publicInput : Digest) (claim : BytecodeClaim)
    (proof : Proof) : m Bool := do
  let seed ← π (seedInput iv publicInput)
  runProof π (deferringVerifierProgram claim bytecode publicInput) seed proof

end Hash

/-- The deployed IV, over Keccak-f[1600]. -/
def fiatShamirIv (bytecode : List K) : Digest :=
  Id.run (fiatShamirIvWith (m := Id) keccakF1600 bytecode)

/-- The deployed deferring verifier, over Keccak-f[1600]. -/
def verifyDeferred (bytecode : List K) (iv publicInput : Digest) (claim : BytecodeClaim)
    (proof : Proof) : Bool :=
  Id.run (verifyDeferredWith (m := Id) keccakF1600 bytecode iv publicInput claim proof)

end LeanVM.Protocol.Verifier

/-! ## The sizes a proof announces

The verifier's first step reads the announced sizes and nothing else (`readAnnouncedSizes`): its
reads only absorb, so no hash or permutation is consulted for a value, and running it with every
permutation answered by `default` gives the layout the proof announces. The extractor's budget
(`Statement/CostMachine.lean`) grows with the stack size it announces. -/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters

/-- A run with every permutation answered by `default`, for the steps that only read scalars: what
they read does not depend on the sponge. -/
def runPure {α : Type} (program : VerifierProgram α) (s : VerifierProgramState) : Option
    (α × VerifierProgramState) :=
  Id.run (run (m := Id) (fun _ ↦ default) program s)

end LeanVM.Protocol.Compile

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Protocol.Compile

/-- The announced layout and rate exponent of a stream, read by the program's own
`readAnnouncedSizes` (reads only absorb: no hash or permutation is consulted for a value). -/
def announcedLayoutAndRate (bytecode : List K) (stream : List E) : Option (Layout × ℕ) :=
  (runPure (readAnnouncedSizes bytecode) ⟨⟨default, []⟩, stream, [], []⟩).map (·.1)

end LeanVM.Protocol.Verifier

end
