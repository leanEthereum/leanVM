/-
  LeanVM.Spec.Verifier

  The leanVM verifier: `python-verifier/verifier.py` at leanVM
  `3a37fb6e1c7423e36b67d1cac4eda70c3ad4dd45`, transcribed into Lean, with the constants it reads
  (the WHIR parameters and the Flock constants) and the Fiat-Shamir transcript it runs on.
-/

module

public import LeanVM.Spec.Field
public import LeanVM.Spec.Blake2s
public import LeanVM.Spec.Fast.Hash
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The leanVM verifier

Transcribed from `python-verifier/verifier.py` at leanVM
`3a37fb6e1c7423e36b67d1cac4eda70c3ad4dd45`; every citation `verifier.py:N` below is a line of
that file. The sections follow the Python's:

| Section | `verifier.py` |
|---|---|
| Arithmetic: `eq_kernel`, `multilinear_eval`, `eq_eval`, Lagrange | 180-324, 1111-1143 |
| The layout: tables, flushes, forms, `build_layout` | 294-324, 467-541, 644-917 |
| Sumcheck rounds | 414-421, 428-435 |
| The bus phase: GKR, `verify_bus_balance` | 441-464, 536-606 |
| The table sumcheck | 612-641 |
| WHIR: `derive_config`, `verify_whir`, `verify_stacked_opening` | 920-1106, 1366-1375 |
| Flock and ring switching | 1109-1360 |
| `verify_execution`, the seed, `verify` | 354-358, 644, 1378-1428 |

The file has three parts:

1. **The constants** the verifier reads: the WHIR parameters (`crates/pcs/src/whir_config.rs`,
   the query table of `verifier.py:922-957`) and the Flock constants.
2. **The transcript**: the verifier is a program `Prog` of a small language with five operations
   on the proof (read a scalar, sample a challenge, check a proof of work, read a Merkle root,
   open rows), and `runProof` reads such a program on a proof with a hash function `H : Bytes →
   m Digest` in any monad `m`, as the Python's `Transcript` does with BLAKE2s. With `H` a query to
   a random oracle, it is the verifier of the random-oracle model (`LeanVM.Spec.Statement`).
3. **The verifier**, section by section as in the table above, ending with `verifyWith H bytecode
   publicInput proof`, the verifier with the hash `H`, and `verify`, the deployed one, with
   BLAKE2s.

The verifier takes the values of the two polynomials the statement fixes (the bytecode's, and
flock's matrices') from a parameter `ev : Evaluations`. The deployed verifier computes them. The
deferring verifier (`verifyDeferred`), which has no counterpart in the Python, takes them from
claims, as an aggregate's in-circuit verifier of its children does
(`crates/rec_aggregation/guests/lean_ethereum.py`, `verify_sub`).

The fields are `LeanVM.Spec.Field`, BLAKE2s is `LeanVM.Spec.Blake2s`; `LeanVM.Spec.Fast.Hash`
only makes the compiled hash fast (`@[csimp]`). Reading proofs from files (`verifyFiles`) is
outside the specification, in `LeanVM.Protocol.Verifier`.
-/

/-! # Part 1: the constants -/

/-!
## The WHIR parameters

The constants are transcribed from `crates/pcs/src/whir_config.rs:38-86` of the
pinned leanVM (`3a37fb6e1c7423e36b67d1cac4eda70c3ad4dd45`), the ladder geometry from its
`derive_ladder` and `derive_ladder_shape` (`:252-301`), the stacking window from
`crates/leanvm_core/src/pcs.rs:49-51`, and the query counts from the second verifier,
`python-verifier/verifier.py:922-957` (`WHIR_QUERIES`, `derive_config`), which the portable Rust
verifier carries verbatim (`crates/verifier/src/whir.rs:10-56`). The specification
describes the protocol these parameters instantiate (Annex B, Protocol B.1,
`doc/leanvm/body/b-polynomial-commitment-scheme.tex`) and gives no numbers.

An opening of a stack of `2^μ` elements of `K` at rate `2^-R` runs a *ladder* of levels. Level 0
folds `initialFold = 6` variables; every later level folds `subsequentFold = 4`, or what remains,
until at most `residualMaxLog = 5` variables remain, which are sent in the clear. The rate
exponent of a level is the previous one plus the previous fold minus a domain reduction,
`initialReduction = 3` after level 0 and `subsequentReduction = 1` after every later level. Each
level opens `queries` positions after `queryGrindingBits = 17` bits of grinding; from level 1 on,
one out-of-domain sample binds the level's commitment (`oodSamples`).

The query counts are the Rust's *output*, not its derivation: `optimize_johnson_level`
(`whir_config.rs:607-675`) minimises the queries of each level subject to the 128-bit
round-by-round targets of Annex B's Theorem B.2 under a floating-point MCA formula, and this
module does not restate that search. At this pin the formula charges each fold round the bare
MCA error `ε` (`paper_thm_ca_johnson_log_a`, `whir_config.rs:431-447`, citing Jo, ePrint
2026/891, Thm 4.4), not the row-union `2^(ℓ-j) ε` of the earlier pin, so 25 of the 56 shapes
query one to three positions fewer. The table is the one the Python verifier carries, indexed
by rate exponent `1..4` and stack size `15..28`; outside that window `ladder` is `none`, as both
verifiers reject (`validate_log_inv_rate`, `whir_config.rs:48-56`; `verifier.py:945`).

The Rust API takes the witness size as `m = μ + LOG_PACKING` bits, `LOG_PACKING = 6`
(`crates/pcs/src/pack.rs:5`); `ladder` takes the stack size `μ`, as the Python `derive_config`
does. `LOG_INV_RATE_0 = 1` (`whir_config.rs:41`) is the rate the Rust test suite proves at, not a
verifier parameter: the rate exponent is announced with the sizes.
-/

namespace LeanVM.Parameters.Whir

@[expose] public section

/-! ### Constants (`whir_config.rs`) -/

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

/-- The round-by-round security target the query counts were derived for, in bits
(`SECURITY_BITS`, `whir_config.rs:38`). -/
def securityBits : ℕ := 128

/-- The smallest stack the PCS commits: `MIN_MU` (`pcs.rs:49`;
`MIN_STACKED_LOG`, `verifier.py:929`). A
smaller witness is padded up to it. -/
def minLogStack : ℕ := 15

/-- The largest stack the PCS commits: `MAX_MU` (`pcs.rs:51`;
`MAX_STACKED_LOG`, `verifier.py:930`). -/
def maxLogStack : ℕ := 28

/-- The smallest rate exponent of level 0 (`MIN_LOG_INV_RATE`, `whir_config.rs:44`). -/
def minLogInvRate : ℕ := 1

/-- The largest rate exponent of level 0 (`MAX_LOG_INV_RATE`, `whir_config.rs:45`). -/
def maxLogInvRate : ℕ := 4

/-- Out-of-domain samples taken after a level's commitment: none at level 0, whose commitment the
opening's own evaluation claim binds, and one at every later level (`whir_config.rs:107-114`).
The Rust production test fixes the count for stack sizes 22 to 28 (`whir_config.rs:983, 995`);
for 15 to 21 it is the second verifier's, which takes one sample per level after the first
(`verifier.py:1053-1057`). -/
def oodSamples (level : ℕ) : ℕ := if level = 0 then 0 else 1

/-! ### The ladder -/

/-- One level of an opening: the number of sumcheck rounds it folds (`ℓ_i`), the rate exponent
of the code its commitment is in (`R_i`), and the number of positions queried (`t_i`), in the
notation of Annex B. -/
structure Level where
  fold : ℕ
  logInvRate : ℕ
  queries : ℕ
  deriving DecidableEq

/-- The levels after the first, as pairs (fold, rate exponent): while more than `residualMaxLog`
variables remain, fold `subsequentFold` of them (or all that remain) at the rate exponent the
previous level's fold and the pending domain reduction give (`derive_ladder`,
`whir_config.rs:252-289`, with `derive_ladder_shape`'s rate rule, `:292-301`). `fuel` bounds the
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
`initialFold` at that rate, then `levelsFrom` (`derive_config`, `verifier.py:942-957`). -/
def shape (μ logInvRate : ℕ) : List (ℕ × ℕ) :=
  (initialFold, logInvRate) ::
    levelsFrom μ (μ - initialFold) initialFold logInvRate initialReduction

/-- The variables left after every fold: the size of the residual sent in the clear. -/
def residualLog (μ logInvRate : ℕ) : ℕ := μ - ((shape μ logInvRate).map Prod.fst).sum

/-- The query counts `WHIR_QUERIES` of `verifier.py:932`, verbatim: row `R - 1` for the rate
exponent `R`, entry `μ - 15` for the stack size `μ`, one count per level. -/
def queryTable : List (List (List ℕ)) := [
  [[222, 55], [223, 56, 30], [223, 56, 31], [223, 56, 32], [223, 56, 32], [223, 56, 32, 22],
   [223, 56, 32, 22], [224, 56, 32, 23], [224, 56, 32, 23], [224, 56, 32, 23, 17],
   [224, 56, 32, 23, 17], [224, 56, 32, 23, 18], [225, 56, 32, 23, 18], [225, 56, 32, 23, 18, 14]],
  [[111, 45], [112, 45, 27], [112, 45, 28], [112, 45, 28], [112, 45, 28], [112, 45, 28, 20],
   [112, 45, 28, 20], [112, 45, 28, 21], [112, 45, 28, 21], [112, 45, 28, 21, 16],
   [112, 45, 28, 21, 16], [112, 45, 28, 21, 16], [112, 45, 28, 21, 16], [112, 45, 28, 21, 16, 13]],
  [[75, 37], [75, 37, 24], [75, 37, 25], [75, 38, 25], [75, 38, 25], [75, 38, 25, 18],
   [75, 38, 25, 19], [75, 38, 25, 19], [75, 38, 25, 19], [75, 38, 25, 19, 15],
   [75, 38, 25, 19, 15], [75, 38, 25, 19, 15], [75, 38, 25, 19, 15], [75, 38, 25, 19, 15, 13]],
  [[56, 32], [56, 32, 22], [56, 32, 22], [56, 32, 23], [56, 32, 23], [56, 32, 23, 17],
   [56, 32, 23, 17], [56, 32, 23, 18], [56, 32, 23, 18], [56, 32, 23, 18, 14],
   [56, 32, 23, 18, 14], [56, 32, 23, 18, 14], [56, 32, 23, 18, 15], [56, 32, 23, 18, 15, 12]]]

/-- The window the parameters are defined on: the stacking window and the rate range
(`verifier.py:945`; `crates/verifier/src/whir.rs:33-36`; `whir_config.rs:48-56` the rate). -/
def Admissible (μ logInvRate : ℕ) : Prop :=
  minLogStack ≤ μ ∧ μ ≤ maxLogStack ∧ minLogInvRate ≤ logInvRate ∧ logInvRate ≤ maxLogInvRate

instance {μ logInvRate : ℕ} : Decidable (Admissible μ logInvRate) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The ladder of an admissible stack size and rate: the geometry of `shape` paired with the
tabulated query counts, level by level. `none` outside the window, and `none` if the table did
not have one count per level (`verifier.py:956`), so that no level is silently dropped. -/
def ladder (μ logInvRate : ℕ) : Option (List Level) :=
  if Admissible μ logInvRate then
    let geometry := shape μ logInvRate
    let queries := (queryTable.getD (logInvRate - minLogInvRate) []).getD (μ - minLogStack) []
    if geometry.length = queries.length then
      some (List.zipWith (fun (g : ℕ × ℕ) q ↦ ⟨g.1, g.2, q⟩) geometry queries)
    else none
  else none

/-- The log block lengths `κ_i + R_i` of the levels' codes: the message log after a level's fold
plus its rate exponent (`LevelShapes.block_len`, `whir_config.rs:121-156`). -/
def blockLogs (μ : ℕ) : List Level → List ℕ
  | [] => []
  | l :: rest => (μ - l.fold + l.logInvRate) :: blockLogs (μ - l.fold) rest

end
end LeanVM.Parameters.Whir

namespace LeanVM.Parameters

@[expose] public section

/-!
## The Flock constants

Transcribed from leanVM at pin `3a37fb6e1c7423e36b67d1cac4eda70c3ad4dd45`. The
specification fixes the sizes and the shape of the fixed coordinates (Annex C, §C.1 to §C.2) but
not their values; the values below are the Rust's, cross-checked against the Python verifier.

* `kBlock`, `kSkip`, `kIn` = `14`, `6`, `8`: `python-verifier/verifier.py:650-655`;
  `crates/flock/src/zerocheck.rs:45`.
* `constPos` = `512`: `crates/flock/src/hash.rs:144`; `verifier.py:657`.
* `phi8Basis`, the images of `1, t, …, t^7` under `φ_8 : GF(2^8) → K`:
  `crates/primitives/src/field/phi8_tower.rs:15-24`; `verifier.py:1111`.
* `fixedBytes` = `0xF7, 0x53, 0xB5`: `crates/flock/src/zerocheck/univariate_skip_optimized.rs:68`;
  `verifier.py:1116-1119`.
* `g0`, the limbs `0x243F…08D3, 0x1319…7344, 0xA409…31D0` (π in hexadecimal):
  `univariate_skip_optimized.rs:104-106`; `verifier.py:1114`.
* `ringShifts` = `32, 16, 8, 4, 2, 1`: `crates/pcs/src/ring_switch.rs:80`; `verifier.py:1327`.

`φ_8` is `F_2`-linear in its byte, the sum of the basis images of the byte's set bits
(`phi8_tower.rs:27-42`, `verifier.py:1112`); its image lies in `K`, the `y^0` limb of `E`. The
skip domain is `φ_8(0), …, φ_8(63)` and its coset `φ_8(64), …, φ_8(127)` (Annex C,
§C.2). The fixed coordinates of the zerocheck point are `φ_8` of the three bytes, then
`g0^(2^j) / (1 + g0^(2^j))` for `j < 4` (`univariate_skip_optimized.rs:90-101`,
`verifier.py:1116-1119`). The modulus of `GF(2^8)` is not needed: only the images are used.
-/

namespace Flock

/-- Log-size of a witness block: `2 ^ 14` positions per BLAKE2s compression. -/
abbrev kBlock : ℕ := 14

/-- The univariate skip replaces the low `6` coordinates; `2 ^ 6 = 64` bits pack into one `K`
element. -/
abbrev kSkip : ℕ := 6

/-- The within-block coordinates that remain after the skip, bound by the lincheck. -/
abbrev kIn : ℕ := 8

/-- The position of the constant wire in every block. -/
def constPos : Fin (2 ^ (kSkip + kIn)) := ⟨512, by decide⟩

/-- The images of the polynomial basis `1, t, …, t^7` of `GF(2^8)` under `φ_8`, in `K`
(`phi8_tower.rs:15-24`). -/
def phi8Basis : Vector K 8 :=
  #v[K.ofBits 0x0000000000000001, K.ofBits 0x033CE8BEDDC8A656, K.ofBits 0x512620375ED2A108,
    K.ofBits 0x0C9E636090AAFC01, K.ofBits 0xBA4F3CD82801769C, K.ofBits 0xBA26E7904ADB4A47,
    K.ofBits 0x467698598926DC01, K.ofBits 0x4418AE808B28BDD0]

/-- `φ_8` of a byte: the sum of the basis images of its set bits. -/
def phi8 (b : ℕ) : K := ∑ i : Fin 8, if b.testBit i then phi8Basis[i] else 0

/-- The `i`-th node of the skip domain and its coset, `φ_8(i)` in `E`: nodes `0` to `63` are the
skip domain, `64` to `127` its coset. -/
def skipNode (i : Fin 128) : E := ofK (phi8 i)

/-- The three bytes whose images are the first three fixed coordinates. -/
def fixedBytes : Vector ℕ 3 := #v[0xF7, 0x53, 0xB5]

/-- The public element `g_0` whose powers give the last four fixed coordinates. -/
def g0 : E :=
  E.ofLimbs (K.ofBits 0x243F6A8885A308D3) (K.ofBits 0x13198A2E03707344)
    (K.ofBits 0xA4093822299F31D0)

/-- The coordinate `g_0^(2^j) / (1 + g_0^(2^j))`. -/
def mediumCoord (j : ℕ) : E := g0 ^ 2 ^ j / (1 + g0 ^ 2 ^ j)

/-- The seven fixed coordinates of the zerocheck point, coordinates `0` to `6`. -/
def fixedPoint : Vector E 7 :=
  #v[ofK (phi8 fixedBytes[0]), ofK (phi8 fixedBytes[1]), ofK (phi8 fixedBytes[2]),
    mediumCoord 0, mediumCoord 1, mediumCoord 2, mediumCoord 3]

/-- The Frobenius shifts of the six stages of the ring-switching map: stage `p` adds
`f_p · a^(2^(2^(5 − p)))`. -/
def ringShifts : Vector ℕ 6 := #v[32, 16, 8, 4, 2, 1]

end Flock

end
end LeanVM.Parameters

/-! # Part 2: the transcript -/

/-!
## The verifier language

leanVM's verifier (`python-verifier/verifier.py` at leanVM
`3a37fb6e1c7423e36b67d1cac4eda70c3ad4dd45`, class `Transcript`, lines 354-425) touches the proof
through five operations, and computes everything else from their results:

* `next_scalar`: read the next field element of the proof stream and absorb it into the
  Fiat-Shamir chain (`read`);
* `sample`: squeeze a challenge out of the chain (`sample`);
* `grind_check`: read a nonce, check the proof of work at a number of bits, absorb the nonce
  (`grind`);
* `Digest.from_halves(*next_scalars(2))` at a commitment: read a Merkle root as two scalars
  (`commit`, which also fixes the shape of the committed matrix: `2^height` leaves of `width`
  words);
* `merkle`: open rows of a committed matrix at positions, each with its authentication path
  (`query`).

`Prog α` is the free monad over these operations. A verifier written in it has two readings,
and the point of the language is that they are one program:

* the *compiled* reading (`LeanVM.Protocol.Compile.Run`): the deployed non-interactive
  verifier, run on a proof with a hash function, the challenges squeezed out of a BLAKE2s chain
  and the rows authenticated by Merkle paths;
* the *interactive-oracle* reading, a public-coin protocol in which the prover sends field
  elements and whole matrices, which the soundness proof works with (outside this file).
-/

/-!
## Reading a program on a proof

Transcribed from the Python verifier at leanVM
`3a37fb6e1c7423e36b67d1cac4eda70c3ad4dd45` (`python-verifier/verifier.py:330-425`, `Proof`,
`compress`, `Transcript`), whose Fiat-Shamir chain is the Rust's (the prover's
`crates/fiat_shamir/src/lib.rs:18-174`, the verifier's `crates/verifier/src/transcript.rs:32-216`):

* the chain state is a 256-bit digest `cv`; every step is BLAKE2s-256 of the 64 bytes
  `cv ‖ block`, a block being three little-endian 64-bit words of data and a 64-bit tag
  (`blockOf`): `1` to absorb a scalar, `2` to squeeze, `3` for the proof-of-work base, `4` for a
  nonce;
* `read`: `cv ← H(cv ‖ (x, 1))` for the next scalar `x` of the stream (`next_scalar`);
* `sample`: `cv ← H(cv ‖ (0, 2))`, the challenge being the three low 64-bit words of the new
  state (`sample`, `challengeOf`);
* `grind`: the next scalar of the stream is the nonce `n`, *not* absorbed by `observe`; the
  check is that the low `bits` bits of the first word of `H(H(cv ‖ (0, 3)) ‖ (n, 4))` are zero
  (for `bits = 0`, that `n = 0`); then `cv ← H(cv ‖ (n, 4))` (`grind_check`);
* `commit`: the root is read as two scalars, both absorbed, and must be canonical
  (`Digest.from_halves`, `digestOfScalars`);
* `query`: one opening per position, in order, from a separate channel that the chain does not
  absorb: the leaf's words, hashed as bytes, then one sibling per level, the position's bit at
  the level choosing the side, and the climb must end at the root (`Transcript.merkle`). The
  leaf must have the committed width and the path the committed height; the Python checks both
  implicitly by reading exactly that many bytes, and `Proof` here carries the openings already
  split.

The hash is a parameter `H : Bytes → m Digest` in any monad `m`: the deployed verifier is the
`Id` instance at `blake2sBytes`, and the random-oracle theorem runs the same function with `H`
a query to the oracle.

### Deviation from the Python verifier

The Python verifier reads the Merkle openings from one byte string; `Proof.openings` is that
string already cut into leaves and paths. A byte string that does not cut into the lengths the
verifier asks for is rejected by the Python, and has no `Proof` here; nothing else differs.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Blake2sHash

@[expose] public section

/-! ### Programs -/

/-- The verifier language: a program returns a value of type `α` after reading scalars,
sampling challenges, checking proofs of work, reading commitments and opening rows, or fails. -/
inductive Prog (α : Type) : Type where
  /-- Return a value. -/
  | ret (a : α)
  /-- Reject. -/
  | fail
  /-- Read the next prover scalar (absorbed into the chain). -/
  | read (k : E → Prog α)
  /-- Sample a challenge (squeezed from the chain). -/
  | sample (k : E → Prog α)
  /-- Check a proof of work of `bits` bits (the nonce is read and absorbed). -/
  | grind (bits : ℕ) (k : Prog α)
  /-- Read a commitment to a matrix of `2^height` rows of `width` words. -/
  | commit (height width : ℕ) (k : Prog α)
  /-- Open rows of the `i`-th commitment at `positions`; continue with the rows. -/
  | query (i : ℕ) (positions : List ℕ) (k : List (List K) → Prog α)

namespace Prog

variable {α β γ : Type}

/-- Sequencing. -/
def bind : Prog α → (α → Prog β) → Prog β
  | ret a, f => f a
  | fail, _ => fail
  | read k, f => read fun x ↦ (k x).bind f
  | sample k, f => sample fun x ↦ (k x).bind f
  | grind b k, f => grind b (k.bind f)
  | commit h w k, f => commit h w (k.bind f)
  | query i ps k, f => query i ps fun r ↦ (k r).bind f

instance : Monad Prog where
  pure := ret
  bind := bind


/-! #### The operations as programs -/

/-- Read one prover scalar. -/
def readE : Prog E := read ret

/-- Read `n` prover scalars, in order. -/
def readN : ℕ → Prog (List E)
  | 0 => ret []
  | n + 1 => do
    let x ← readE
    let xs ← readN n
    return x :: xs

/-- Sample one challenge. -/
def sampleE : Prog E := sample ret

/-- Sample `n` challenges, in order. -/
def sampleN : ℕ → Prog (List E)
  | 0 => ret []
  | n + 1 => do
    let x ← sampleE
    let xs ← sampleN n
    return x :: xs

/-- Check a proof of work of `bits` bits. -/
def grindP (bits : ℕ) : Prog Unit := grind bits (ret ())

/-- Read a commitment to a matrix of `2^height` rows of `width` words. -/
def commitP (height width : ℕ) : Prog Unit := commit height width (ret ())

/-- Open rows of the `i`-th commitment. -/
def queryP (i : ℕ) (positions : List ℕ) : Prog (List (List K)) := query i positions ret

/-- Reject unless `c` holds (the Python verifier's `require`). -/
def require (c : Prop) [Decidable c] : Prog Unit := if c then ret () else fail

end Prog

/-- Byte strings, the hash's inputs. -/
abbrev Bytes : Type := List UInt8

/-! ### The chain's blocks -/

/-- The eight little-endian bytes of a 64-bit tag. -/
def tagBytes (tag : ℕ) : Bytes := [tag.toUInt8, 0, 0, 0, 0, 0, 0, 0]

/-- The 32-byte block of a scalar and a tag: its three limbs, then the tag (`lib.rs:36-43`). -/
def blockOf (x : E) (tag : ℕ) : Bytes :=
  kBytes (x.limb 0) ++ kBytes (x.limb 1) ++ kBytes (x.limb 2) ++ tagBytes tag

/-- The challenge squeezed into a state: its three low 64-bit words (`verifier.py:364-366`). -/
def challengeOf (d : Digest) : E :=
  E.ofLimbs (ofWords d[0] d[1]) (ofWords d[2] d[3]) (ofWords d[4] d[5])

/-- The proof-of-work predicate: at `bits = 0` the nonce is `0`; otherwise the low `bits` bits
of the digest's first 64-bit word are zero (`verifier.py:385-391`). -/
def powOk (bits : ℕ) (nonce : E) (d : Digest) : Bool :=
  if bits = 0 then decide (nonce.limb 0 = 0 ∧ nonce.limb 1 = 0 ∧ nonce.limb 2 = 0)
  else decide ((d[0].toNat + 2 ^ 32 * d[1].toNat) % 2 ^ bits = 0)

/-! ### Proofs and verifier states -/

/-- One Merkle opening: the leaf's words and the siblings from the leaf up. -/
structure Opening where
  /-- The leaf's words. -/
  leaf : List K
  /-- The siblings, from the leaf's level up. -/
  path : List Digest

/-- A proof: the scalar stream and the Merkle openings, in the order the verifier reads them
(`verifier.py:330-340`). -/
structure Proof where
  /-- The scalars. -/
  stream : List E
  /-- The openings. -/
  openings : List Opening

/-- The compiled verifier's state: the chain state, what is left of the proof, and the roots
read so far with their shapes. -/
structure St where
  /-- The chain state. -/
  cv : Digest
  /-- The scalars not yet read. -/
  stream : List E
  /-- The openings not yet read. -/
  openings : List Opening
  /-- The roots read so far, each with its height and width. -/
  roots : List (Digest × ℕ × ℕ)

/-! ### The run -/

section Run

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest)

/-- The chain after absorbing a block. -/
def absorbBlock (cv : Digest) (block : Bytes) : m Digest := H (digestBytes cv ++ block)

/-- Climb a Merkle path from `node` at position `q`: at each level the position's low bit says
whether `node` is the left child (`verifier.py:404-405`). -/
def climb : Digest → ℕ → List Digest → m Digest
  | node, _, [] => pure node
  | node, q, s :: ss => do
    let parent ← if q % 2 = 0 then H (digestBytes node ++ digestBytes s)
      else H (digestBytes s ++ digestBytes node)
    climb parent (q / 2) ss

/-- Check one opening against a root of the given shape at position `q`. -/
def openOne (root : Digest) (height width q : ℕ) (o : Opening) : m Bool :=
  if o.leaf.length = width ∧ o.path.length = height then do
    let leafDigest ← H (o.leaf.flatMap kBytes)
    let top ← climb H leafDigest q o.path
    pure (decide (top.toList = root.toList))
  else pure false

/-- Open every position in order, consuming one opening each; the leaves, and the openings
left. -/
def openAll (root : Digest) (height width : ℕ) :
    List ℕ → List Opening → m (Option (List (List K) × List Opening))
  | [], os => pure (some ([], os))
  | _ :: _, [] => pure none
  | q :: qs, o :: os => do
    if ← openOne H root height width q o then
      let rest ← openAll root height width qs os
      pure (rest.map fun r ↦ (o.leaf :: r.1, r.2))
    else pure none

/-- The compiled reading of a program: run it on the state, every challenge squeezed out of the
chain and every opening authenticated; `none` on rejection. -/
def run {α : Type} : Prog α → St → m (Option (α × St))
  | .ret a, s => pure (some (a, s))
  | .fail, _ => pure none
  | .read k, s => match s.stream with
    | [] => pure none
    | x :: xs => do
      let cv ← absorbBlock H s.cv (blockOf x 1)
      run (k x) { s with cv := cv, stream := xs }
  | .sample k, s => do
    let cv ← absorbBlock H s.cv (blockOf 0 2)
    run (k (challengeOf cv)) { s with cv := cv }
  | .grind bits k, s => match s.stream with
    | [] => pure none
    | n :: xs => do
      let base ← absorbBlock H s.cv (blockOf 0 3)
      let d ← absorbBlock H base (blockOf n 4)
      let cv ← absorbBlock H s.cv (blockOf n 4)
      if powOk bits n d then run k { s with cv := cv, stream := xs } else pure none
  | .commit height width k, s => match s.stream with
    | x0 :: x1 :: xs => do
      let cv0 ← absorbBlock H s.cv (blockOf x0 1)
      let cv1 ← absorbBlock H cv0 (blockOf x1 1)
      match digestOfScalars (x0, x1) with
      | some root =>
        run k { s with cv := cv1, stream := xs, roots := s.roots ++ [(root, height, width)] }
      | none => pure none
    | _ => pure none
  | .query i ps k, s => match s.roots[i]? with
    | none => pure none
    | some (root, height, width) => do
      match ← openAll H root height width ps s.openings with
      | some (rows, rest) => run (k rows) { s with openings := rest }
      | none => pure none

/-- Run a program on a proof from a seed state, and accept when it returns `true` with the
stream and the openings fully consumed (`verifier.py:423-425`, `finish`). -/
def runProof (P : Prog Bool) (seed : Digest) (π : Proof) : m Bool := do
  match ← run H P ⟨seed, π.stream, π.openings, []⟩ with
  | some (true, s) => pure (s.stream.isEmpty && s.openings.isEmpty)
  | _ => pure false

end Run

end
end LeanVM.Protocol.Compile

/-! # Part 3: the verifier -/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters

@[expose] public section

/-!
## Verifier arithmetic

From `verifier.py`, lines 180-324 and 1111-1143. Every function has the
Python's name in `lowerCamelCase` and computes the same value on the inputs the verifier gives it;
the products and sums are taken in the Python's order where it is visible (`foldl` from `1` or
`0`), although `E` is a field and the order does not change a value.

### Conventions

* The Python's `E(n)` for an integer `n < 2^64` is `eOfNat n`, the word `n` in limb `0`: the
  natural-number cast of `E` is the characteristic-two one (`(2 : E) = 0`) and is never used for
  a wire integer. `GEN = E(2)` is `gen`, the element `x` of `K`; `yE` is `E(0, 1)`, the tower
  generator `y`.
* `int(e)` of an `E` element is `eToNat e`, its three limbs as one 192-bit integer
  (`verifier.py:125-126`).
* A `K` value that the Python lifts into `E` (`E.lift`) is `ofK`.

### Preconditions the Python checks and the verifier always meets

`multilinear_eval` requires a table of `2^|point|` entries and `eq_eval`/`dot` zip strictly.
At every call site of the verifier the lengths agree by construction (the table sizes are
`2^k` for the `k` coordinates the caller passes), so these functions are total here: an excess
entry is ignored, as `zip` ignores it.
-/

/-! ### Integers and constants -/

/-- The Python `E(n)`: the 64-bit word `n` in limb `0` (`verifier.py:98-101`). -/
def eOfNat (n : ℕ) : E := ofK (K.ofBits n)

/-- The integer value of a `K` word (`K.__index__`). -/
def kToNat (a : K) : ℕ := a.toBitVec.toNat

/-- `int(e)`: the three limbs of `e` as one 192-bit integer, limb `0` lowest
(`verifier.py:125-126`). -/
def eToNat (e : E) : ℕ :=
  kToNat (e.limb 0) + 2 ^ 64 * kToNat (e.limb 1) + 2 ^ 128 * kToNat (e.limb 2)

/-- `GEN = E(2)`, the generator `x` whose powers index the bytecode and the memory
(`verifier.py:182`). -/
def gen : E := eOfNat 2

/-- `E(0, 1)`, the tower generator `y` with `y^3 = y + 1`. -/
def yE : E := E.ofLimbs 0 1 0

/-- `_gpow(index) = GEN ** index` (`verifier.py:678-679`). -/
def gpow (index : ℕ) : E := gen ^ index

/-- `E.sum(values)`: the sum from `ZERO`, left to right (`verifier.py:121-123`). -/
def sumE (values : List E) : E := values.foldl (· + ·) 0

/-- `reduce(mul, values)` with the product of the empty list `1`. -/
def prodE (values : List E) : E := values.foldl (· * ·) 1

/-! ### Powers and multilinear helpers -/

/-- `acc, acc·base, acc·base², …`, `count` terms. -/
def powersFrom (acc base : E) : ℕ → List E
  | 0 => []
  | count + 1 => acc :: powersFrom (acc * base) base count

/-- `powers(base, count) = [1, base, base², …]`, `count` terms (`verifier.py:185-187`). -/
def powers (base : E) (count : ℕ) : List E := powersFrom 1 base count

/-- `eq_kernel(point)`: the `2^|point|` equality weights, the first coordinate the lowest bit
(`verifier.py:232-236`). -/
def eqKernel (point : List E) : List E :=
  point.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) [1]

/-- One fold of `multilinear_eval`: adjacent pairs `(a, b)` become `a·(1 + r) + b·r`. -/
def foldPairs (r : E) : List E → List E
  | a :: b :: rest => (a * (1 + r) + b * r) :: foldPairs r rest
  | _ => []

/-- `multilinear_eval(mle, point)`: the multilinear extension of the table at the point, the
first coordinate folding adjacent entries (`verifier.py:239-244`). A table of the wrong size, which
the Python rejects, never reaches it (see the module note); `0` for an empty result. -/
def multilinearEval (mle point : List E) : E :=
  (point.foldl (fun cur r ↦ foldPairs r cur) mle).headD 0

/-- Python's `int.bit_length` on a natural number. -/
def bitLength (n : ℕ) : ℕ := if n = 0 then 0 else Nat.log2 n + 1

/-- `log2_ceil(value) = (max(value, 1) - 1).bit_length()` (`verifier.py:247-248`): `0` at
`value = 0`, the height of a table with no row. -/
def log2Ceil (value : ℕ) : ℕ := bitLength (value - 1)

/-- `log2_strict(value)`: the exponent of a power of two, `none` otherwise
(`verifier.py:251-253`). -/
def log2Strict (value : ℕ) : Option ℕ :=
  if 0 < value ∧ value &&& (value - 1) = 0 then some (bitLength value - 1) else none

/-- `eq_eval(left, right) = Π (1 + x + y)` (`verifier.py:256-260`). -/
def eqEval (left right : List E) : E :=
  (List.zipWith (fun x z ↦ 1 + x + z) left right).foldl (· * ·) 1

/-- `dot(left, right) = Σ x·y` (`verifier.py:263-267`). -/
def dot (left right : List E) : E :=
  (List.zipWith (· * ·) left right).foldl (· + ·) 0

/-- `padding_weight(point, n)`: `pad_n(point)`, the multilinear extension of `[z ≥ n]` for
`n ≤ 2^|point|`, unrolled from the low bit (`verifier.py:270-276`; `doc/leanvm`, Lemma
`lem:suffix`). -/
def paddingWeight (point : List E) (n : ℕ) : E :=
  (1 + eOfNat ((n >>> point.length) % 2)) *
    point.zipIdx.foldl (fun pad (r, k) ↦
      let b := eOfNat ((n >>> k) % 2)
      (1 + b) * r + (1 + b + r) * pad) 1

/-- `index_mle(point)`: the multilinear extension of `[1, g, g², …]` at an LSB-first point,
`Π (1 + r_i·(1 + g^(2^i)))` (`verifier.py:279-286`). -/
def indexMleFrom (generatorPower : E) : List E → E → E
  | [], acc => acc
  | r :: rs, acc => indexMleFrom (generatorPower ^ 2) rs (acc * (1 + r * (1 + generatorPower)))

/-- `index_mle(point)` (`verifier.py:279-286`). -/
def indexMle (point : List E) : E := indexMleFrom gen point 1

/-- `poly_eval(coefficients, point)`: Horner's rule over the coefficients, constant first
(`verifier.py:289-291`). -/
def polyEval (coefficients : List E) (point : E) : E :=
  coefficients.foldr (fun c acc ↦ acc * point + c) 0

/-- `_selector_point(selector, length)`: the low `length` bits of `selector` as `0/1` elements,
lowest first (`verifier.py:322-323`). -/
def selectorPoint (selector length : ℕ) : List E :=
  (List.range length).map fun bit ↦ eOfNat ((selector >>> bit) % 2)

/-! ### The Flock skip domain (`verifier.py:1111-1143`) -/

/-- `PHI[value]`: the image of the byte `value` under `φ_8`, in `E` (`verifier.py:1112`). -/
def phi (value : ℕ) : E := ofK (Flock.phi8 value)

/-- `_window_denominator(count)`: the inverse of `Π_{0 < k < count} PHI[k]`
(`verifier.py:1122-1129`). -/
def windowDenominator (count : ℕ) : E :=
  (((List.range (count - 1)).map fun k ↦ phi (k + 1)).foldl (· * ·) 1)⁻¹

/-- `lagrange_weights(count, point)`: the barycentric weights of the nodes `PHI[:count]` at
`point`, from prefix and suffix products of the differences (`verifier.py:1132-1138`). -/
def lagrangeWeights (count : ℕ) (point : E) : List E :=
  let differences := (List.range count).map fun k ↦ point + phi k
  let prefixes := differences.scanl (· * ·) 1
  let suffixes := (differences.reverse.scanl (· * ·) 1).reverse
  let denominator := windowDenominator count
  List.zipWith (fun p s ↦ p * s * denominator) (prefixes.take count) (suffixes.drop 1)

/-- `lagrange_interpolate(count, values, point)` (`verifier.py:1141-1142`). -/
def lagrangeInterpolate (count : ℕ) (values : List E) (point : E) : E :=
  dot (lagrangeWeights count point) values

/-!
## The verifier's layout

From `verifier.py`, lines 294-324 (`Placement`, `stack_offsets`,
`_selector_point`), 467-541 (`Form`, `BusBlock`, `BusLayout`, `bus_layout`, `ColumnClaim`), and
644-917 (the constants, `Layout`, `Flushes`, `Table`, the six tables, `build_layout`).

### Representation

* A `Form` is the Python's `dict` from monomials to coefficients, as an association list in
  insertion order: `addScaled` adds into an existing monomial's coefficient and appends a new
  one, as the `dict` does. A monomial is the sorted list of its column indices (`()`, `(i,)`,
  `(i, j)`).
* The Python's column-name lookups `_cols` are `colIdx`, `List.idxOf` on the column-name list;
  every name the tables use is in its list, as the Python's `assert` checks.
* `Table.constraints` is a function of the row's evaluations, as in the Python; only `jump` has
  any (`_jump_constraints`).
* `build_layout` returns `none` exactly where the Python raises: a bytecode whose length is not
  a power of two (`log2_strict`), a bytecode shorter than `2^BUS_BITS` (negative
  `log_bytecode`), the size window, and a list of heights not one per table (the strict `zip`).
-/

/-! ### Constants (`verifier.py:533, 644-658, 694-696, 842-879`) -/

/-- The bus communicates tuples of `2^BUS_BITS` field elements. -/
def busBits : ℕ := 4

/-- The columns no instruction table owns, first in the global numbering. -/
def numGlobalColumns : ℕ := 6

/-- Global column `MEMORY_0`. -/
def memory0 : ℕ := 0
/-- Global column `MEMORY_1`. -/
def memory1 : ℕ := 1
/-- Global column `MEMORY_2`. -/
def memory2 : ℕ := 2
/-- Global column `MEMORY_FINAL_COUNTERS`. -/
def memoryFinalCounters : ℕ := 3
/-- Global column `BYTECODE_FINAL_COUNTERS`. -/
def bytecodeFinalCounters : ℕ := 4
/-- Global column `QFLOCK`, the Flock witness region. -/
def qflock : ℕ := 5

/-- `BLAKE2S_R1CS_LOG_SIZE`: a Flock block has `2^14` positions. -/
def blake2sR1csLogSize : ℕ := 14

/-- `K_BITS`. -/
def kBits : ℕ := 64

/-- `FLOCK_K_SKIP = log2_ceil(K_BITS)`. -/
def flockKSkip : ℕ := log2Ceil kBits

/-- `LOG_PACKING = log2_ceil(K_BITS)`: bits per committed `K` element. -/
def logPacking : ℕ := log2Ceil kBits

/-- `FLOCK_NUM_LINCHECK_ROUNDS`. -/
def flockNumLincheckRounds : ℕ := blake2sR1csLogSize - flockKSkip

/-- `QFLOCK_SLOT_BITS`. -/
def qflockSlotBits : ℕ := blake2sR1csLogSize - logPacking

/-- `BLAKE2S_CONSTANT_COLUMN`: the constant wire of a Flock block. -/
def blake2sConstantColumn : ℕ := 512

/-- `MIN_STACKED_LOG`. -/
def minStackedLog : ℕ := Whir.minLogStack

/-- `MAX_STACKED_LOG`. -/
def maxStackedLog : ℕ := Whir.maxLogStack

/-- `SEP_STATE = ONE`. -/
def sepState : E := 1
/-- `SEP_MEM = GEN`. -/
def sepMem : E := gen
/-- `SEP_BYTECODE = GEN²`. -/
def sepBytecode : E := gen ^ 2

/-- Opcode `XOR`. -/
def opXor : ℕ := 0
/-- Opcode `MUL`. -/
def opMul : ℕ := 1
/-- Opcode `SET`. -/
def opSet : ℕ := 2
/-- Opcode `DEREF`. -/
def opDeref : ℕ := 3
/-- Opcode `JUMP`. -/
def opJump : ℕ := 4
/-- Opcode `BLAKE2S`. -/
def opBlake2s : ℕ := 5

/-! ### Placements (`verifier.py:294-324`) -/

/-- Where something sits in the stacked cube: a claim's point fills the `vars` coordinates
above `low`, the bits of `index` fixing the rest. -/
structure Placement where
  /-- The number of coordinates the claim's point fills. -/
  vars : ℕ
  /-- The selector whose bits fix the other coordinates. -/
  index : ℕ
  /-- The coordinates below the window. -/
  low : ℕ := 0
  deriving Inhabited, DecidableEq, Repr

/-- `Placement.stack_point`: the point on the stacked cube. -/
def Placement.stackPoint (p : Placement) (point : List E) (stackLog : ℕ) : List E :=
  let bits := selectorPoint p.index stackLog
  bits.take p.low ++ point ++ bits.drop (p.low + p.vars)

/-- `Placement.eq_above`: the equality weight of the coordinates above the window. -/
def Placement.eqAbove (p : Placement) (point : List E) : E :=
  let bits := selectorPoint (p.index >>> (p.low + p.vars))
    (point.length - p.low - p.vars)
  eqEval bits (point.drop (p.low + p.vars))

/-- `stack_offsets(sizes)`: blocks of `2^size` laid end to end, largest first, ties by index;
their offsets, and the log-size of the total (`verifier.py:313-319`). -/
def stackOffsets (sizes : List ℕ) : List ℕ × ℕ :=
  let size := fun i ↦ sizes.getD i 0
  let order := (List.range sizes.length).mergeSort fun i j ↦
    decide (size j < size i) || (decide (size i = size j) && decide (i ≤ j))
  let placed := order.foldl (fun (acc : List ℕ × ℕ) i ↦
    (acc.1.set i acc.2, acc.2 + 2 ^ size i)) (List.replicate sizes.length 0, 0)
  (placed.1, log2Ceil placed.2)

/-! ### Forms (`verifier.py:467-489`) -/

/-- A polynomial of degree at most two in a table's columns: monomial (sorted column indices) to
coefficient, in insertion order. -/
structure Form where
  /-- The terms. -/
  terms : List (List ℕ × E) := []
  deriving Inhabited

/-- Add `c` into the coefficient of `m`, appending the monomial if it is new (the `dict`
update). -/
def addTerm : List (List ℕ × E) → List ℕ → E → List (List ℕ × E)
  | [], m, c => [(m, 0 + c)]
  | (m', c') :: rest, m, c =>
    if m' = m then (m', c' + c) :: rest else (m', c') :: addTerm rest m c

/-- `Form.add_scaled`: add `weight · other`. -/
def Form.addScaled (f other : Form) (weight : E) : Form :=
  ⟨other.terms.foldl (fun acc t ↦ addTerm acc t.1 (weight * t.2)) f.terms⟩

/-- `Form.__add__`. -/
def Form.add (f g : Form) : Form := f.addScaled g 1

/-- `Form.sum`: the empty sum is the zero polynomial. -/
def Form.sum (forms : List Form) : Form := forms.foldl Form.add {}

/-- `Form.evaluate`: `Σ c · Π column(i)` over the terms. -/
def Form.evaluate (f : Form) (column : ℕ → E) : E :=
  sumE (f.terms.map fun t ↦ t.1.foldl (fun acc i ↦ acc * column i) t.2)

/-- `_const(value)`. -/
def Form.const (value : E) : Form := ⟨[([], value)]⟩

/-- `_col(index, exponent)`: `g^exponent · x_index`. -/
def Form.col (index : ℕ) (exponent : ℕ := 0) : Form := ⟨[([index], gpow exponent)]⟩

/-- `_prod(a, b, exponent)`: `g^exponent · x_a · x_b`. -/
def Form.prod (a b : ℕ) (exponent : ℕ := 0) : Form := ⟨[([min a b, max a b], gpow exponent)]⟩

/-! ### Flushes (`verifier.py:699-724`) -/

/-- A table's bus flushes: the tuples it pushes and pulls, in pairs. -/
structure Flushes where
  /-- The pushed tuples. -/
  push : List (List Form) := []
  /-- The pulled tuples. -/
  pull : List (List Form) := []
  deriving Inhabited

namespace Flushes

/-- `Flushes.pair`. -/
def pair (f : Flushes) (push pull : List Form) : Flushes := ⟨f.push ++ [push], f.pull ++ [pull]⟩

/-- `Flushes.state_derived`. -/
def stateDerived (f : Flushes) (pc fp : ℕ) (npc nfp : Form) : Flushes :=
  f.pair [Form.const sepState, npc, nfp] [Form.const sepState, Form.col pc, Form.col fp]

/-- `Flushes.state_step`. -/
def stateStep (f : Flushes) (pc fp : ℕ) : Flushes :=
  f.stateDerived pc fp (Form.col pc 1) (Form.col fp)

/-- `Flushes._counted`. -/
def counted (f : Flushes) (pre : List Form) (count : ℕ) (suffix : List Form) : Flushes :=
  f.pair (pre ++ [Form.col count 1] ++ suffix) (pre ++ [Form.col count] ++ suffix)

/-- `Flushes.bytecode`. -/
def bytecode (f : Flushes) (pc count opcode : ℕ) (operands : List Form) : Flushes :=
  f.counted [Form.const sepBytecode, Form.col pc] count (Form.const (gpow opcode) :: operands)

/-- `Flushes.memory`. -/
def memory (f : Flushes) (address : Form) (count : ℕ) (values : List Form) : Flushes :=
  f.counted [Form.const sepMem, address] count values

/-- `Flushes.memory_cols`: the columns, padded with zeros to three limbs. -/
def memoryCols (f : Flushes) (address : Form) (count : ℕ) (columns : List ℕ) : Flushes :=
  f.memory address count
    (columns.map (Form.col ·) ++ List.replicate (3 - columns.length) (Form.const 0))

end Flushes

/-! ### The instruction tables (`verifier.py:730-879`) -/

/-- `_cols(columns, name)`: the index of a column by name. -/
def colIdx (columns : List String) (name : String) : ℕ := columns.idxOf name

/-- `ARITH_COLUMNS`. -/
def arithColumns : List String :=
  ["pc", "fp", "o_a", "o_b", "o_c", "va_0", "va_1", "va_2", "vb_0", "vb_1", "vb_2", "cnt_a",
    "cnt_b", "cnt_c", "cnt_bc"]

/-- `SET_COLUMNS`. -/
def setColumns : List String := ["pc", "fp", "o", "k_0", "k_1", "k_2", "cnt", "cnt_bc"]

/-- `DEREF_COLUMNS`. -/
def derefColumns : List String :=
  ["pc", "fp", "o1", "o2", "o3", "f_pc", "f_fp", "ptr", "v3_0", "v3_1", "v3_2", "cnt_ptr",
    "cnt_target", "cnt_local", "cnt_bc"]

/-- `JUMP_COLUMNS`. -/
def jumpColumns : List String :=
  ["pc", "fp", "o_c", "o_d", "o_f", "v_cond", "v_pc", "v_fp", "cnt_c", "cnt_d", "cnt_f", "cnt_bc",
    "w", "b"]

/-- `BLAKE2S_COLUMNS`. -/
def blake2sColumns : List String :=
  ["pc", "fp", "o_0", "o_1", "o_2", "o_3", "o_v", "o_out", "o_md",
    "m0_lo", "m0_hi", "m1_lo", "m1_hi", "m2_lo", "m2_hi", "m3_lo", "m3_hi",
    "out0_lo", "out0_hi", "out1_lo", "out1_hi", "cv0_lo", "cv0_hi", "cv1_lo", "cv1_hi", "md_lo",
    "md_hi",
    "cnt_m0", "cnt_m1", "cnt_m2", "cnt_m3", "cnt_cv0", "cnt_cv1", "cnt_out0", "cnt_out1", "cnt_md",
    "cnt_bc"]

/-- `TOWER_LANES`: the limb products of `E` multiplication folded by `y³ = y + 1`. -/
def towerLanes : List (List (ℕ × ℕ)) :=
  [[(0, 0), (1, 2), (2, 1)], [(0, 1), (1, 0), (1, 2), (2, 1), (2, 2)],
    [(0, 2), (1, 1), (2, 0), (2, 2)]]

/-- `_flushes_arith(opcode, multiply)` (`verifier.py:759-774`). -/
def flushesArith (opcode : ℕ) (multiply : Bool) : Flushes :=
  let c := colIdx arithColumns
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

/-- `_flushes_set()` (`verifier.py:777-784`). -/
def flushesSet : Flushes :=
  let c := colIdx setColumns
  let k := [c "k_0", c "k_1", c "k_2"]
  let f : Flushes := {}
  let f := f.stateStep (c "pc") (c "fp")
  let f := f.bytecode (c "pc") (c "cnt_bc") opSet
    (Form.col (c "o") :: k.map (Form.col ·) ++ [Form.const 0])
  f.memoryCols (Form.prod (c "fp") (c "o")) (c "cnt") k

/-- `_flushes_deref()` (`verifier.py:787-803`). -/
def flushesDeref : Flushes :=
  let c := colIdx derefColumns
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

/-- `_flushes_jump()` (`verifier.py:806-816`): `next_pc = b·dest + (b + 1)·g·pc`,
`next_fp = b·frame + (b + 1)·fp`. -/
def flushesJump : Flushes :=
  let c := colIdx jumpColumns
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

/-- `_jump_constraints(columns)`: `b + cond·w` and `cond·(b + 1)` (`verifier.py:819-821`). -/
def jumpConstraints (columns : List E) : List E :=
  let c := colIdx jumpColumns
  let condition := columns.getD (c "v_cond") 0
  let inverse := columns.getD (c "w") 0
  let flag := columns.getD (c "b") 0
  [flag + condition * inverse, condition * (flag + 1)]

/-- The nine `BLAKE2S` cells read, as (cell, operand, offset): `verifier.py:833-835`. -/
def blake2sCells : List (String × String × ℕ) :=
  [("m0", "o_0", 0), ("m1", "o_1", 0), ("m2", "o_2", 0), ("m3", "o_3", 0),
    ("cv0", "o_v", 0), ("cv1", "o_v", 1), ("out0", "o_out", 0), ("out1", "o_out", 1),
    ("md", "o_md", 0)]

/-- `_flushes_blake2s()` (`verifier.py:824-839`). -/
def flushesBlake2s : Flushes :=
  let c := colIdx blake2sColumns
  let operands := ["o_0", "o_1", "o_2", "o_3", "o_v", "o_out", "o_md"].map c
  let f : Flushes := {}
  let f := f.stateStep (c "pc") (c "fp")
  let f := f.bytecode (c "pc") (c "cnt_bc") opBlake2s (operands.map (Form.col ·))
  blake2sCells.foldl (fun f (cell, operand, exponent) ↦
    f.memoryCols (Form.prod (c "fp") (c operand) exponent) (c ("cnt_" ++ cell))
      [c (cell ++ "_lo"), c (cell ++ "_hi")]) f

/-- One instruction's table: its columns, its bus flushes, its constraints
(`verifier.py:730-750`). -/
structure Table where
  /-- The table's name. -/
  name : String
  /-- Its opcode, also its index in `TABLES`. -/
  opcode : ℕ
  /-- Its column names. -/
  columns : List String
  /-- Its flushes. -/
  flushes : Flushes
  /-- Its constraints, as a function of a row's evaluations. -/
  constraints : List E → List E := fun _ ↦ []
  deriving Inhabited

/-- `Table.width`. -/
def Table.width (t : Table) : ℕ := t.columns.length

/-- `Table.n_constraints`: the number of constraints, read off the zero row. -/
def Table.nConstraints (t : Table) : ℕ := (t.constraints (List.replicate t.width 0)).length

/-- `Table.count_columns`: the columns whose name starts with `cnt`. -/
def Table.countColumns (t : Table) : List ℕ :=
  (t.columns.zipIdx.filter fun (name, _) ↦ name.startsWith "cnt").map (·.2)

/-- `TABLES`, in opcode order (`verifier.py:857-864`). -/
def tables : List Table :=
  [⟨"xor", opXor, arithColumns, flushesArith opXor false, fun _ ↦ []⟩,
    ⟨"mul", opMul, arithColumns, flushesArith opMul true, fun _ ↦ []⟩,
    ⟨"set", opSet, setColumns, flushesSet, fun _ ↦ []⟩,
    ⟨"deref", opDeref, derefColumns, flushesDeref, fun _ ↦ []⟩,
    ⟨"jump", opJump, jumpColumns, flushesJump, jumpConstraints⟩,
    ⟨"blake2s", opBlake2s, blake2sColumns, flushesBlake2s, fun _ ↦ []⟩]

/-- `BLAKE2S_SLOTS`: the `BLAKE2S` limb each Flock slot carries; slots 8 and 9 carry none
(`verifier.py:868-871`). -/
def blake2sSlots : List (Option String) :=
  [some "cv0_lo", some "cv0_hi", some "cv1_lo", some "cv1_hi", some "out0_lo", some "out0_hi",
    some "out1_lo", some "out1_hi", none, none,
    some "m0_lo", some "m0_hi", some "m1_lo", some "m1_hi", some "m2_lo", some "m2_hi",
    some "m3_lo", some "m3_hi", some "md_lo", some "md_hi"]

/-- `PADDING_INSTANCE`: Flock's padding instance, the compression of BLAKE2s-256 of 64 zero
bytes, in `BLAKE2S_SLOTS` order: the parameterized IV, the digest, a zero message, then the
one-block final metadata, counter 64 and the last-block flag (`verifier.py:875-876`). -/
def paddingInstance : List ℕ :=
  let word := fun (v : Vector UInt32 8) (k : ℕ) ↦
    (v.getD (2 * k) 0).toNat ||| (v.getD (2 * k + 1) 0).toNat <<< 32
  let digest := Blake2sHash.blake2sBytes (List.replicate 64 0)
  (List.range 4).map (word Blake2sHash.paramIv) ++ (List.range 4).map (word digest) ++
    List.replicate 10 0 ++ [64, 0xFFFFFFFF]

/-- `Table.padding`: the row a padding row holds, zero but for `BLAKE2S`'s value limbs, which are
`q_flock`'s slots and so hold its padding instance (`verifier.py:752-756`). -/
def Table.padding (t : Table) : List E :=
  let slots := if t.opcode = opBlake2s then blake2sSlots else []
  t.columns.map fun name ↦
    if some name ∈ slots then eOfNat (paddingInstance.getD (slots.idxOf (some name)) 0) else 0

/-- `TABLE_WIDTHS`. -/
def tableWidths : List ℕ := tables.map Table.width

/-- `GLOBAL_COLUMN_BASES`: each table's first global column. -/
def globalColumnBases : List ℕ :=
  (List.range tables.length).map fun t ↦ numGlobalColumns + (tableWidths.take t).sum

/-! ### The bus layout (`verifier.py:491-541`) -/

/-- One block of a bus side, owned by a table. -/
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

/-- Where a side's blocks sit in the stacked leaf cube. -/
structure BusLayout where
  /-- The log-size of the padded cube. -/
  depth : ℕ
  /-- The framework blocks' placements. -/
  framework : List Placement
  /-- The table blocks' placements, in the side's block order. -/
  tables : List Placement

/-- `bus_layout(framework_log_rows, blocks)` (`verifier.py:514-519`). -/
def busLayout (frameworkLogRows : List ℕ) (blocks : List BusBlock) : BusLayout :=
  let sizes := frameworkLogRows ++ blocks.map (·.logRows)
  let (offsets, depth) := stackOffsets sizes
  let placements := List.zipWith (fun size offset ↦ ({ vars := size, index := offset } :
    Placement)) sizes offsets
  ⟨depth, placements.take frameworkLogRows.length, placements.drop frameworkLogRows.length⟩

/-- A column claim: the column's multilinear extension at `point` is `value`. -/
structure ColumnClaim where
  /-- The global column. -/
  column : ℕ
  /-- The point, over the column's own variables. -/
  point : List E
  /-- The claimed value. -/
  value : E

/-- A claim on the stack: the weight it puts on the stack, and the value it claims for it. -/
abbrev StackClaim : Type := (List E → E) × E

/-! ### `build_layout` (`verifier.py:660-670, 882-917`) -/

/-- The layout the verifier derives from the bytecode and the announced sizes. -/
structure Layout where
  /-- The memory's log-size. -/
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
  /-- Every global column's placement. -/
  placements : List Placement
  /-- The stacked cube's log-size. -/
  stackLog : ℕ
  /-- The tables' log-heights, each the least `h` with `rows ≤ 2 ^ h`. -/
  tableLogHeights : List ℕ

/-- `ColumnClaim.on_stack`: the claim as an equality weight on the stack. -/
def ColumnClaim.onStack (c : ColumnClaim) (layout : Layout) : StackClaim :=
  let point := (layout.placements.getD c.column default).stackPoint c.point layout.stackLog
  (fun x ↦ eqEval point x, c.value)

/-- The bus blocks of every table, side by side: pushes, pulls, counts, each block at its
table's log-height and row count (`verifier.py:888-898`). -/
def busBlocks (tableLogHeights tableRows : List ℕ) :
    List BusBlock × List BusBlock × List BusBlock :=
  let rows := List.zip tables (List.zip tableLogHeights tableRows)
  (rows.flatMap fun (t, h, n) ↦ t.flushes.push.map fun c ↦ ⟨h, n, c, t.opcode⟩,
    rows.flatMap fun (t, h, n) ↦ t.flushes.pull.map fun c ↦ ⟨h, n, c, t.opcode⟩,
    rows.flatMap fun (t, h, n) ↦ t.countColumns.map fun l ↦ ⟨h, n, [Form.col l], t.opcode⟩)

/-- The Flock slot of a global column that is an embedded `BLAKE2S` limb
(`verifier.py:908`). -/
def limbSlot (column : ℕ) : Option ℕ :=
  blake2sSlots.zipIdx.findSome? fun (name?, slot) ↦ name?.bind fun name ↦
    if globalColumnBases.getD opBlake2s 0 + colIdx blake2sColumns name = column then some slot
    else none

/-- Every column's log-size, in global order (`verifier.py:901-904`). -/
def columnKappas (logMemory logBytecode : ℕ) (tableLogHeights : List ℕ) : List ℕ :=
  let qflockKappa := tableLogHeights.getD opBlake2s 0 + qflockSlotBits
  [logMemory, logMemory, logMemory, logMemory, logBytecode, qflockKappa] ++
    tables.flatMap fun t ↦ List.replicate t.width (tableLogHeights.getD t.opcode 0)

/-- The placements of every column, and the stack's log-size (`verifier.py:906-916`): the
committed columns stacked by `stack_offsets`, each limb at `q_flock`'s offset plus its slot. -/
def placementsOf (kappas : List ℕ) : List Placement × ℕ :=
  let blockCols := (List.range kappas.length).filter fun c ↦ (limbSlot c).isNone
  let (blockOffsets, totalLog) := stackOffsets (blockCols.map (kappas.getD · 0))
  let offsetOf := fun c ↦ blockOffsets.getD (blockCols.idxOf c) 0
  let placements := kappas.zipIdx.map fun (kappa, column) ↦
    match limbSlot column with
    | some slot =>
      ({ vars := kappa, index := offsetOf qflock + slot, low := qflockSlotBits } : Placement)
    | none => { vars := kappa, index := offsetOf column }
  (placements, max minStackedLog totalLog)

/-- `build_layout(bytecode, log_memory, table_rows)` (`verifier.py:882-917`); `none` where the
Python raises. A table's log-height is the least `h` with `rows ≤ 2^h` (`log2Ceil`). -/
def buildLayout (bytecode : List K) (logMemory : ℕ) (tableRows : List ℕ) : Option Layout :=
  match log2Strict bytecode.length with
  | none => none
  | some logLength =>
    if busBits ≤ logLength ∧ 16 ≤ logMemory ∧ logMemory ≤ 32 ∧
        tableRows.all (· ≤ 2 ^ 32) ∧ logLength - busBits ≤ 32 ∧
        tableRows.length = tables.length then
      let logBytecode := logLength - busBits
      let tableLogHeights := tableRows.map log2Ceil
      let (push, pull, count) := busBlocks tableLogHeights tableRows
      let (placements, stackLog) :=
        placementsOf (columnKappas logMemory logBytecode tableLogHeights)
      some ⟨logMemory, logBytecode, bytecode, push, pull, count, placements, stackLog,
        tableLogHeights⟩
    else none

open LeanVM.Protocol.Compile

/-!
## Sumcheck rounds

From `verifier.py`, lines 414-421 (`Transcript.sumcheck_round_poly`) and
428-435 (`sumcheck`).

A round polynomial `q(X) = c0 + c1·X + c2·X² + …` of `count` coefficients is sent with one
coefficient left out, which the verifier derives from the running claim:

* plain mode (`eq_factor = None`), `q(0) + q(1) = claim`: the prover sends `c0`, then
  `c2, …, c_{count-1}`; `c1 = claim + Σ_{k ≥ 2} c_k` (characteristic two);
* equality mode (`eq_factor = r`), `(1 + r)·q(0) + r·q(1) = claim`: the prover sends
  `c1, …, c_{count-1}`; `c0 = claim + r·Σ_{k ≥ 1} c_k`.

Every coefficient sent is read (`Prog.read`, the Python's `next_scalar`), so absorbed into the
Fiat-Shamir chain in that order. The round's challenge is sampled after its polynomial, and the
next claim is `q(challenge)`.
-/

/-- Fail on `none`: a pure step the Python performs with a `require` inside. -/
def liftOption {α : Type} : Option α → Prog α
  | none => Prog.fail
  | some a => Prog.ret a

/-- `Transcript.sumcheck_round_poly(count, claim, eq_factor)`: read a round polynomial of `count`
coefficients, deriving the one the claim fixes; its coefficients, constant first
(`verifier.py:414-421`). -/
def sumcheckRoundPoly (count : ℕ) (claim : E) : Option E → Prog (List E)
  | none => do
    let constant ← Prog.readE
    let tail ← Prog.readN (count - 2)
    return constant :: (claim + sumE tail) :: tail
  | some eqFactor => do
    let tail ← Prog.readN (count - 1)
    return (claim + eqFactor * sumE tail) :: tail

/-- `sumcheck(transcript, claim, count, equalities)`: one round per entry of `equalities`, each
reading its polynomial and sampling its challenge; the challenges in order, and the final claim
(`verifier.py:428-435`). -/
def sumcheck (claim : E) (count : ℕ) : List (Option E) → Prog (List E × E)
  | [] => return ([], claim)
  | equality :: equalities => do
    let message ← sumcheckRoundPoly count claim equality
    let challenge ← Prog.sampleE
    let (point, final) ← sumcheck (polyEval message challenge) count equalities
    return (challenge :: point, final)

/-!
## The bus phase

From `verifier.py`, lines 441-464 (`verify_gkr_grand_products`) and
536-606 (`BusResult`, `verify_bus_balance`).

**GKR.** The three trees (push, pull, count) are batched: the roots are read as
`shared, count` (push and pull share their root, which is the balance), and the layers are
walked two at a time, one first when the depth is odd. A layer of `step` levels samples its
combiner, runs an equality-mode sumcheck of `2^step + 1` coefficients over the current point,
reads the three trees' `2^step` children, checks that their products combine to the sumcheck's
claim, and samples the `step` new coordinates. The loop is `gkrLayers`, structural in the
remaining depth.

**Leaf decomposition.** Pure (`accumulateSide`): every side's framework blocks are evaluated
outright, its table blocks accumulate into the owner's form for that side, and the side's total
is the GKR value less the framework and the padding.
-/

/-! ### GKR (`verifier.py:441-464`) -/

/-- The state of the GKR walk: the three trees' values at `point`. -/
structure GkrState where
  /-- The push, pull and count values. -/
  values : List E
  /-- The point the values are at. -/
  point : List E

/-- One step of `step` levels of the GKR walk (`verifier.py:450-461`). -/
def gkrStep (step : ℕ) (s : GkrState) : Prog GkrState := do
  let combiner ← Prog.sampleE
  let claim := polyEval s.values combiner
  let (x, claim) ← sumcheck claim (2 ^ step + 1) (s.point.map some)
  let child0 ← Prog.readN (2 ^ step)
  let child1 ← Prog.readN (2 ^ step)
  let child2 ← Prog.readN (2 ^ step)
  let children := [child0, child1, child2]
  let products := children.map prodE
  Prog.require (claim = polyEval products combiner)
  let y ← Prog.sampleN step
  let values := children.map (multilinearEval · y)
  return ⟨values, y ++ x⟩

/-- The `while layer > 0` loop: one level when the remaining depth is odd, two otherwise. -/
def gkrLayers : ℕ → GkrState → Prog GkrState
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
values there (`verifier.py:441-464`). -/
def verifyGkrGrandProducts (depth : ℕ) : Prog (E × List E × List E) := do
  let shared ← Prog.readE
  let count ← Prog.readE
  let s ← gkrLayers depth ⟨[shared, shared, count], []⟩
  return (count, s.point, s.values)

/-!
## The fixed polynomials

Two of the verifier's values are evaluations of polynomials that the statement fixes and the proof
does not: the stacked bytecode's multilinear extension at the bus point (`verifyBusBalance`), and
flock's matrices against the lincheck's weights (`verifyFlockLincheck`). The verifier asks `ev`
for them. The deployed verifier computes them (`Evaluations.computed`); the verifier inside an
aggregate takes them from claims that it hands on instead of checking (`Evaluations.claimed`).
-/

/-- Where the verifier gets the values of the fixed polynomials. -/
structure Evaluations where
  /-- The value the verifier takes for the multilinear extension of the bytecode `words` at
  `point`. -/
  bytecode (words : List K) (point : List E) : Prog E
  /-- The value the verifier takes for `blake2sBilinear alpha eRow wCol` of the lincheck, whose
  weights its skip challenge `zSkip`, row point `chiIn`, column point `chiInPrime` and slices `s`
  give. -/
  matrices (alpha zSkip : E) (chiIn chiInPrime s : List E) : Prog E

/-! ### The leaf decomposition (`verifier.py:536-606`) -/

/-- `BusResult`: the framework columns' claims, the GKR point, each table's form per side
(`forms[table][side]`), and what the tables owe each side. -/
structure BusResult where
  /-- The framework columns' claims. -/
  claims : List ColumnClaim
  /-- The GKR point, which the table sumcheck reuses. -/
  point : List E
  /-- `forms[table][side]`. -/
  forms : List (List Form)
  /-- The three sides' totals. -/
  totals : List E

/-- The three framework fingerprints of a side (`verifier.py:566-578`, `fingerprints`; the
Python hoists `memory_index` and `bytecode_index`, pure values inlined here; `bytecode_value` is
the bytecode's value, from `Evaluations`). -/
def fingerprints (weights memory memoryLow bytecodeLow : List E) (bytecodeValue : E)
    (pc memoryCount bytecodeCount : E) : List E :=
  [dot (weights.take 3) [sepState, pc, gpow 0],
    dot (weights.take 6) ([sepMem, indexMle memoryLow, memoryCount] ++ memory),
    dot (weights.take 3) [sepBytecode, indexMle bytecodeLow, bytecodeCount] + bytecodeValue]

/-- One table block's form on a side: `side_beta` plus the block's fingerprint, one tuple slot at
a time (`verifier.py:596-598`). -/
def blockForm (block : BusBlock) (sideWeights : List E) (sideBeta : E) : Form :=
  block.coordinates.zipIdx.foldl
    (fun form (coordinate, slot) ↦ form.addScaled coordinate (sideWeights.getD slot 0))
    (Form.const sideBeta)

/-- One side of the leaf decomposition (`verifier.py:589-604`): the forms with the side's table
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

/-- `verify_bus_balance(layout)` (`verifier.py:544-606`), the bytecode's value from `ev`. -/
def verifyBusBalance (ev : Evaluations) (layout : Layout) : Prog BusResult := do
  let frameworkLogRows := [0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayout frameworkLogRows layout.push
  let pullLayout := busLayout frameworkLogRows layout.pull
  let countLayout := busLayout [] layout.count
  let alphas ← Prog.sampleN busBits
  let weights := eqKernel alphas
  let beta ← Prog.sampleE
  let (countRoot, point, treeValues) ← verifyGkrGrandProducts pushLayout.depth
  Prog.require (countRoot ≠ 0)
  let memoryLow := point.take layout.logMemory
  let bytecodeLow := point.take layout.logBytecode
  let memory ← Prog.readN 3
  let memoryFinal ← Prog.readE
  let bytecodeFinal ← Prog.readE
  let claims : List ColumnClaim :=
    (List.zipWith (fun column value ↦ ⟨column, memoryLow, value⟩) [memory0, memory1, memory2]
      memory) ++
    [⟨memoryFinalCounters, memoryLow, memoryFinal⟩, ⟨bytecodeFinalCounters, bytecodeLow,
      bytecodeFinal⟩]
  let bytecodeValue ← ev.bytecode layout.bytecode (bytecodeLow ++ alphas)
  let fp := fingerprints weights memory memoryLow bytecodeLow bytecodeValue
  let finalPc := gpow (2 ^ layout.logBytecode - 1)
  let forms0 : List (List Form) := tables.map fun _ ↦ [{}, {}, {}]
  let (forms1, total0) := accumulateSide forms0 0 layout.push pushLayout (fp (gpow 0) 1 1)
    weights beta point (treeValues.getD 0 0)
  let (forms2, total1) := accumulateSide forms1 1 layout.pull pullLayout
    (fp finalPc memoryFinal bytecodeFinal) weights beta point (treeValues.getD 1 0)
  let (forms3, total2) := accumulateSide forms2 2 layout.count countLayout [] [1] 0 point
    (treeValues.getD 2 0)
  return ⟨claims, point, forms3, [total0, total1, total2]⟩

/-!
## The table sumcheck

From `verifier.py`, lines 612-641 (`table_sumcheck`).

One plain-mode sumcheck of four coefficients per round runs over `max` of the tables'
log-heights. Its challenges, reversed, are the point; a table of log-height `h` weighs the first
`h` coordinates by the equality with the bus point and every later one by the challenge itself
(`tableWeights`). The prover then sends each table's row evaluations, in table order, and the
terminal claim must be `Σ weight · (constraints + forms)`, the constraints batched by a disjoint
range of `constraint_powers` per table and the three sides' forms by `form_powers`. Each
evaluation becomes a claim on its global column at the point's first `h` coordinates.
-/

/-- The tables' weights at the point (`verifier.py:624-628`): coordinate `v` contributes
`1 + equality_point[v] + r_v` to a table taller than `v`, and `r_v` to the others. -/
def tableWeights (heights : List ℕ) (equalityPoint point : List E) : List E :=
  point.zipIdx.foldl (fun weights (challenge, coord) ↦
    let equality := 1 + equalityPoint.getD coord 0 + challenge
    List.zipWith (fun weight height ↦ weight * if coord < height then equality else challenge)
      weights heights) (heights.map fun _ ↦ 1)

/-- The per-table loop of `table_sumcheck` (`verifier.py:630-639`): read each table's row
evaluations, add its weighted terms to `final`, and collect its column claims. -/
def tableTerms (constraintPowers formPowers point : List E) :
    List (Table × ℕ × List Form × E) → ℕ → E → List ColumnClaim → Prog (E × List ColumnClaim)
  | [], _, final, claims => return (final, claims)
  | (table, height, forms, weight) :: rest, cursor, final, claims => do
    let evaluations ← Prog.readN table.width
    let summand := dot ((constraintPowers.drop cursor).take table.nConstraints)
      (table.constraints evaluations)
    let final := final +
      weight * (summand + dot formPowers (forms.map (·.evaluate (evaluations.getD · 0))))
    let claims := claims ++ evaluations.zipIdx.map fun (value, column) ↦
      ⟨globalColumnBases.getD table.opcode 0 + column, point.take height, value⟩
    tableTerms constraintPowers formPowers point rest (cursor + table.nConstraints) final claims

/-- `table_sumcheck(table_log_heights, bus_forms, constraint_powers, form_powers,
equality_point, target)` (`verifier.py:612-641`). -/
def tableSumcheck (heights : List ℕ) (busForms : List (List Form))
    (constraintPowers formPowers equalityPoint : List E) (target : E) :
    Prog (List ColumnClaim) := do
  let nRounds := heights.foldl max 0
  let (challenges, claim) ← sumcheck target 4 (List.replicate nRounds none)
  let point := challenges.reverse
  let weights := tableWeights heights equalityPoint point
  let rows := List.zip tables (List.zip heights (List.zip busForms weights))
  let (final, claims) ← tableTerms constraintPowers formPowers point rows 0 0 []
  Prog.require (final = claim)
  return claims

/-!
## The WHIR opening

From `verifier.py`, lines 920-1106 (`derive_config`, `_ext_row`,
`sample_queries`, `_enforced_sum`, `_subspace_roots`, `_induced_weight`, `GluedClaim`,
`verify_whir`) and 1366-1375 (`verify_stacked_opening`).

### Commitments in the verifier language

The Python reads a Merkle root as two scalars (`Digest.from_halves(*next_scalars(2))`) and opens
it a level later with `merkle(root, block_length, queries, leaf_words)`. The language's
`commit height width` fixes the matrix shape when the root is read, so the shape is computed from
the ladder there:

* the stack's root (commitment `0`, read by `verify_execution` before the bus phase,
  `commitStack`) is opened at level `0`: `2^(log_n − folds[0] + rate_0)` leaves of
  `2^folds[0]` words;
* the root read at level `ℓ` (commitment `ℓ + 1`) is opened at level `ℓ + 1`:
  `2^(message_log_ℓ − folds[ℓ+1] + rate_{ℓ+1})` leaves of `3 · 2^folds[ℓ+1]` words.

Level `ℓ` therefore opens commitment `ℓ` (`Prog.queryP ℓ`). The rows come back as raw words; the
level-0 reversal and the regrouping of deeper rows into `E` (`_ext_row`) are the program's.

### Interpretation

* `derive_config` is `LeanVM.Parameters.Whir.ladder`, whose `shape` is the Python's loop and
  whose table is `WHIR_QUERIES` verbatim; the tests compare all 56 admissible pairs with the
  Python.
* `sample_queries` takes the block's log-length `depth` (the Python takes the length and recovers
  `depth` by `log2_strict`, which cannot fail: the length is `2^depth`). Its loop is bounded by
  `count` rounds of fuel; each round yields `min(192 / depth, remaining) ≥ 1` positions since
  `depth ≤ 64`.
* `_induced_weight` requires `len(point) == message_log`. Every glued claim is evaluated at
  `folds[fold_start:] + tail_folds`, of length `log_n − fold_start = message_log`, so the check
  always holds; it is not repeated.
* The `raise` after the level loop (no terminal level) is `Prog.fail` on an empty ladder, which
  `derive_config` never returns.
-/

/-! ### Configuration and queries -/

/-- `derive_config(log_n, log_inv_rate)`: the ladder of levels, `none` outside the window
(`verifier.py:942-957`). -/
def deriveConfig (logN logInvRate : ℕ) : Option (List Whir.Level) := Whir.ladder logN logInvRate

/-- The loop of `sample_queries`: each sample yields up to `192 / depth` positions of `depth`
bits, low bits first (`verifier.py:965-973`). -/
def sampleQueriesAux (depth : ℕ) : ℕ → ℕ → Prog (List ℕ)
  | 0, _ => return []
  | fuel + 1, remaining =>
    if remaining = 0 then return []
    else do
      let bits := eToNat (← Prog.sampleE)
      let n := min (192 / depth) remaining
      let chunk := (List.range n).map fun c ↦ (bits >>> (c * depth)) % 2 ^ depth
      let rest ← sampleQueriesAux depth fuel (remaining - n)
      return chunk ++ rest

/-- `sample_queries(transcript, 2^depth, count)` (`verifier.py:965-973`). -/
def sampleQueries (depth count : ℕ) : Prog (List ℕ) := sampleQueriesAux depth count count

/-- `_ext_row(words)`: a deeper level's leaf words regrouped into the `E` values they encode,
three per lane (`verifier.py:960-962`). -/
def extRow : List K → List E
  | c0 :: c1 :: c2 :: rest => E.ofLimbs c0 c1 c2 :: extRow rest
  | [c0, c1] => [E.ofLimbs c0 c1 0]
  | [c0] => [E.ofLimbs c0 0 0]
  | [] => []

/-- `_enforced_sum(rows, folds, query_weights)`: `Σ_q w_q · ⟨row_q, eq(folds, ·)⟩`
(`verifier.py:976-981`). -/
def enforcedSum (rows : List (List E)) (folds queryWeights : List E) : E :=
  let laneWeights := eqKernel folds
  (List.zip queryWeights rows).foldl (fun total (w, row) ↦ total + w * dot row laneWeights) 0

/-- The layers of `_subspace_roots`: square-and-shift the layer by the last root, pop the next
root (`verifier.py:987-989`). -/
def subspaceRootsAux : ℕ → E → List E → List E
  | 0, _, _ => []
  | n + 1, last, layer =>
    match layer.map fun value ↦ value ^ 2 + last * value with
    | [] => []
    | root :: rest => root :: subspaceRootsAux n root rest

/-- `_subspace_roots(log_n)`: `1`, then the `log_n` subspace polynomial values
(`verifier.py:984-990`). -/
def subspaceRoots (logN : ℕ) : List E :=
  1 :: subspaceRootsAux logN 1 ((List.range logN).map fun i ↦ eOfNat (2 ^ (i + 1)))

/-- `_induced_weight(message_log, queries, query_weights, point)`: the level's batched query
claims as one weight at `point`, `Σ_q w_q Π_k (1 + p_k (1 + Ŵ_k(x_q)))`
(`verifier.py:993-1011`). -/
def inducedWeight (messageLog : ℕ) (queries : List ℕ) (queryWeights point : List E) : E :=
  let roots := subspaceRoots messageLog
  let inverses := roots.map fun value ↦ if value = 0 then 0 else value⁻¹
  (List.zip queryWeights queries).foldl (fun total (weight, query) ↦
    let product := point.zipIdx.foldl (fun (acc : E × E) (challenge, coordinate) ↦
      (acc.1 * (1 + challenge * (1 + acc.2 * inverses.getD coordinate 0)),
        acc.2 ^ 2 + roots.getD coordinate 0 * acc.2)) (weight, eOfNat query)
    total + product.1) 0

/-- `GluedClaim`: a claim folded into the running sumcheck, and the weight it owes back
(`verifier.py:1014-1025`). -/
structure GluedClaim where
  /-- The power of the level's `λ` it was glued with. -/
  scalar : E
  /-- How many fold challenges preceded the level. -/
  foldStart : ℕ
  /-- Its weight at the terminal point, restricted to the level's message coordinates. -/
  weightAt : List E → E

/-! ### The level loop (`verifier.py:1028-1106`) -/

/-- The running state of `verify_whir`. -/
structure WhirState where
  /-- `running_target`. The Python of `127510d1` sets it only in the final level's tail rounds,
  which overwrite the value threaded here, every final message log being at least `2`. -/
  target : E
  /-- `running_quad`. -/
  quad : List E
  /-- Every fold challenge so far. -/
  folds : List E
  /-- The glued claims so far. -/
  glued : List GluedClaim

/-- A level's fold rounds: sample, fold the running claim, read the next quadratic
(`verifier.py:1040-1044`). Returns the state and the level's own challenges. -/
def foldRounds : ℕ → WhirState → List E → Prog (WhirState × List E)
  | 0, s, levelFolds => return (s, levelFolds)
  | n + 1, s, levelFolds => do
    let challenge ← Prog.sampleE
    let target := polyEval s.quad challenge
    let quad ← sumcheckRoundPoly 3 target none
    foldRounds n { s with target, quad, folds := s.folds ++ [challenge] }
      (levelFolds ++ [challenge])

/-- The final level's tail rounds: sample, fold, and read the next quadratic unless it is the
last round (`verifier.py:1087-1093`). The tail challenges and the final running claim. -/
def tailRounds : ℕ → E → List E → Prog (List E × E)
  | 0, target, _ => return ([], target)
  | n + 1, _, quad => do
    let challenge ← Prog.sampleE
    let target := polyEval quad challenge
    if n = 0 then return ([challenge], target)
    else do
      let quad ← sumcheckRoundPoly 3 target none
      let (rest, target) ← tailRounds n target quad
      return (challenge :: rest, target)

/-- Glue a level's pending claims into the running sumcheck with powers of `λ`, the running claim
keeping `λ⁰` (`verifier.py:1078-1082`, which no longer adds the values to `running_target`). -/
def glue (lam : E) (s : WhirState) (pending : List (E × List E × (List E → E))) : WhirState :=
  (pending.foldl (fun (acc : WhirState × E) (value, intro, weightAt) ↦
    let scalar := acc.2 * lam
    let s := acc.1
    ({ s with quad := List.zipWith (fun q i ↦ q + scalar * i) s.quad intro,
              target := s.target + scalar * value,
              glued := s.glued ++ [⟨scalar, s.folds.length, weightAt⟩] }, scalar)) (s, 1)).1

/-- The shape of the commitment a level opens: `2^(message_log + rate)` leaves of `width`
words, the message log being the one after the level's folds. -/
def levelShape (messageLogBefore : ℕ) (level : Whir.Level) (width : ℕ) : ℕ × ℕ :=
  (messageLogBefore - level.fold + level.logInvRate, width)

/-- One level of `verify_whir` and every level after it (`verifier.py:1038-1106`). `index` is
the level's index, which is also the index of the commitment it opens; `laneFolds` is
`config.folds[0]`. -/
def whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ℕ → List Whir.Level → WhirState → Prog Unit
  | _, [], _ => Prog.fail
  | index, level :: rest, s => do
    let (s, levelFolds) ← foldRounds level.fold s []
    let messageLog := logN - s.folds.length
    -- The level's claims: the residual on the final level; otherwise the next commitment and
    -- its out-of-domain claim.
    let (residual, pending) ← match rest with
      | [] => do
        let residual ← Prog.readN (2 ^ messageLog)
        pure (residual, ([] : List (E × List E × (List E → E))))
      | next :: _ => do
        let (height, width) := levelShape messageLog next (3 * 2 ^ next.fold)
        Prog.commitP height width
        let oodPoint ← Prog.sampleN messageLog
        let oodValue ← Prog.readE
        let intro ← sumcheckRoundPoly 3 oodValue none
        pure ([], [(oodValue, intro, fun x ↦ eqEval oodPoint x)])
    Prog.grindP Whir.queryGrindingBits
    let queries ← sampleQueries (messageLog + level.logInvRate) level.queries
    let lam ← Prog.sampleE
    let queryWeights := powers lam queries.length
    let words ← Prog.queryP index queries
    let rows : List (List E) :=
      if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow
    let enforced := enforcedSum rows levelFolds queryWeights
    let intro ← sumcheckRoundPoly 3 enforced none
    let pending := pending ++
      [(enforced, intro, fun x ↦ inducedWeight messageLog queries queryWeights x)]
    let s := glue lam s pending
    match rest with
    | [] => do
      let (tailFolds, target) ← tailRounds messageLog s.target s.quad
      let point := s.folds ++ tailFolds
      let weight := s.glued.foldl
        (fun weight claim ↦
          weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ tailFolds))
        (evaluateBasis (point.drop laneFolds ++ point.take laneFolds))
      let terminal := weight * multilinearEval residual tailFolds
      Prog.require (terminal = target)
    | _ :: _ => whirLevels logN laneFolds evaluateBasis (index + 1) rest s

/-- `verify_whir(log_n, log_inv_rate, target, root, evaluate_basis)`, the root being commitment
`0` (`verifier.py:1028-1106`). -/
def verifyWhir (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E) : Prog Unit := do
  let config ← liftOption (deriveConfig logN logInvRate)
  let quad ← sumcheckRoundPoly 3 target none
  whirLevels logN ((config.head?.map (·.fold)).getD 0) evaluateBasis 0 config
    ⟨target, quad, [], []⟩

/-- Read the stack's root (`verify_execution`, step 2, `verifier.py:1395`): commitment `0`, the
shape level `0` opens it at. -/
def commitStack (logN logInvRate : ℕ) : Prog Unit := do
  let config ← liftOption (deriveConfig logN logInvRate)
  match config with
  | [] => Prog.fail
  | level :: _ =>
    let (height, width) := levelShape logN level (2 ^ level.fold)
    Prog.commitP height width

/-- `verify_stacked_opening(root, stack_log, log_inv_rate, claims)`: batch the claims with powers
of one challenge into one WHIR opening (`verifier.py:1369-1375`). -/
def verifyStackedOpening (stackLog logInvRate : ℕ) (claims : List StackClaim) : Prog Unit := do
  let scales := powers (← Prog.sampleE) claims.length
  verifyWhir stackLog logInvRate (dot scales (claims.map (·.2)))
    fun point ↦ dot scales (claims.map fun c ↦ c.1 point)

/-!
## Flock and ring switching

From `verifier.py`, lines 1109-1360: the constants (`FIXED_CHALLENGES`,
`RING_MAP_SHIFTS`), `verify_flock_zerocheck`, `verify_flock_lincheck`, `blake2s_row_values`,
`blake2s_bilinear`, `verify_flock`, `_phi`, `_ring_weight` and `ring_switch`.

The constants are the repository's `LeanVM.Parameters.Flock` (`Flock.fixedPoint`,
`Flock.ringShifts`, `Flock.phi8`) and `LeanVM.Parameters.Blake2s` (`iv`, `sigma`); the tests
check them against the Python's values.

`blake2sRowValues` is the Python's forward walk with its two mutable row vectors as the state of
a `StateM`; the word gadgets (`addW`, `add3W`, `linearRows`) write rows exactly where the Python's
closures do, and return the same output words.
-/

/-! ### Constants -/

/-- `FIXED_CHALLENGES`: the seven fixed coordinates of the zerocheck point
(`verifier.py:1116-1119`). -/
def fixedChallenges : List E := Flock.fixedPoint.toList

/-- `RING_MAP_SHIFTS` (`verifier.py:1327`). -/
def ringMapShifts : List ℕ := Flock.ringShifts.toList

/-! ### The zerocheck (`verifier.py:1145-1169`) -/

/-- `ZerocheckResult`. -/
structure ZerocheckResult where
  /-- The skip challenge. -/
  zSkip : E
  /-- The sumcheck's point. -/
  chi : List E
  /-- The claim on `A·z`. -/
  vA : E
  /-- The claim on `B·z`. -/
  vB : E
  /-- The claim on `C·z`. -/
  vC : E

/-- `verify_flock_zerocheck(log_n)` (`verifier.py:1154-1169`): the point is the seven fixed
coordinates then sampled ones; one univariate skip round over the coset, then quadratic
equality-mode rounds, closed by `v_a, v_b`, with `v_c = running + v_a·v_b`. -/
def verifyFlockZerocheck (logN : ℕ) : Prog ZerocheckResult := do
  let sampled ← Prog.sampleN (logN - flockKSkip - fixedChallenges.length)
  let r := fixedChallenges ++ sampled
  let pCoset ← Prog.readN kBits
  let zSkip ← Prog.sampleE
  let vP := lagrangeInterpolate (2 * kBits) (List.replicate kBits 0 ++ pCoset) zSkip
  let (chi, running) ← sumcheck vP 3 (r.map some)
  let vA ← Prog.readE
  let vB ← Prog.readE
  return ⟨zSkip, chi, vA, vB, running + vA * vB⟩

/-! ### The BLAKE2s row vectors (`verifier.py:1199-1314`) -/

/-- `BLAKE2S_G_LANES` (`verifier.py:194`). -/
def blake2sGLanes : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15), (0, 5, 10, 15), (1, 6, 11, 12),
    (2, 7, 8, 13), (3, 4, 9, 14)]

/-- `BLAKE2S_IV[word]` as an integer. -/
def blake2sIv (word : ℕ) : ℕ := (iv.toList.getD word 0).toNat

/-- `BLAKE2S_SIGMA[round][position]`. -/
def blake2sSigma (round position : ℕ) : ℕ :=
  ((sigma.toList.getD round (Vector.replicate 16 0)).toList.getD position 0).val

/-- The state of the forward walk: the left and right row vectors. -/
abbrev RowM : Type → Type := StateM (Array E × Array E)

/-- Write row `i` of both vectors. -/
def setRow (i : ℕ) (left right : E) : RowM Unit :=
  modify fun s ↦ (s.1.set! i left, s.2.set! i right)

/-- The column weight at a position. -/
def weightAt (columnWeights : Array E) (i : ℕ) : E := columnWeights.getD i 0

/-- `slots(base)`: the 32 column weights of a word. -/
def slotsW (columnWeights : Array E) (base : ℕ) : Array E :=
  Array.ofFn (n := 32) fun bit ↦ weightAt columnWeights (base + bit)

/-- `literal(value)`: the constant's weight at the set bits of `value`. -/
def literalW (columnWeights : Array E) (value : ℕ) : Array E :=
  Array.ofFn (n := 32) fun bit ↦
    if value.testBit bit then weightAt columnWeights blake2sConstantColumn else 0

/-- `xor(x, y)`. -/
def xorW (x z : Array E) : Array E := Array.zipWith (· + ·) x z

/-- `rotate_right(word, amount)`. -/
def rotateRightW (word : Array E) (amount : ℕ) : Array E :=
  Array.ofFn (n := 32) fun bit ↦ word.getD ((bit + amount) % 32) 0

/-- `add(x, y, carry_base)`: the ripple adder's 31 carry rows; its output word. -/
def addW (columnWeights : Array E) (x z : Array E) (carryBase : ℕ) : RowM (Array E) := do
  let mut carry : E := 0
  let mut output : Array E := #[]
  for bit in List.range 32 do
    if bit < 31 then
      setRow (carryBase + bit) (x.getD bit 0 + carry) (z.getD bit 0 + carry)
    output := output.push (x.getD bit 0 + z.getD bit 0 + carry)
    if bit < 31 then
      carry := carry + weightAt columnWeights (carryBase + bit)
  return output

/-- `add3(x, y, z, base)`: 31 majority rows, then 30 ripple rows; its output word. -/
def add3W (columnWeights : Array E) (x z w : Array E) (base : ℕ) : RowM (Array E) := do
  let mut majority : Array E := #[]
  for bit in List.range 31 do
    setRow (base + bit) (x.getD bit 0 + w.getD bit 0) (z.getD bit 0 + w.getD bit 0)
    majority := majority.push (weightAt columnWeights (base + bit) + w.getD bit 0)
  let rippleBase := base + 31
  let mut carry : E := 0
  let mut output : Array E := #[]
  for bit in List.range 32 do
    let q := if bit = 0 then 0 else majority.getD (bit - 1) 0
    let left := x.getD bit 0 + z.getD bit 0 + w.getD bit 0 + carry
    output := output.push (left + q)
    if 1 ≤ bit ∧ bit ≤ 30 then
      setRow (rippleBase + bit - 1) left (q + carry)
      carry := carry + weightAt columnWeights (rippleBase + bit - 1)
  return output

/-- `linear_rows(values, base)`: the rows `(value, constant)`. -/
def linearRows (columnWeights : Array E) (values : Array E) (base : ℕ) : RowM Unit := do
  for bit in List.range 32 do
    setRow (base + bit) (values.getD bit 0) (weightAt columnWeights blake2sConstantColumn)

/-- The forward walk of `blake2s_row_values` (`verifier.py:1269-1307`). -/
def blake2sWalk (cw : Array E) : RowM Unit := do
  let constant := weightAt cw blake2sConstantColumn
  for (base, length) in [(0, 256), (640, 512), (1152, 128)] do
    for row in List.range length do
      setRow (base + row) (weightAt cw (base + row)) constant
  let mut state : Array (Array E) := Array.replicate 16 (Array.replicate 32 0)
  for word in List.range 8 do
    state := state.set! word (slotsW cw (32 * word))
  for word in List.range 4 do
    state := state.set! (8 + word) (literalW cw (blake2sIv word))
  for (word, base) in [(0, 1152), (1, 1184), (2, 1216), (3, 1248)] do
    state := state.set! (12 + word) (xorW (literalW cw (blake2sIv (4 + word))) (slotsW cw base))
  for roundIndex in List.range 10 do
    for ((laneA, laneB, laneC, laneD), gateIndex) in blake2sGLanes.zipIdx do
      let gate := roundIndex * 8 + gateIndex
      let gateBase := 1280 + 184 * gate
      let a := state.getD laneA #[]
      let b := state.getD laneB #[]
      let c := state.getD laneC #[]
      let d := state.getD laneD #[]
      let mx := slotsW cw (640 + 32 * blake2sSigma roundIndex (2 * gateIndex))
      let my := slotsW cw (640 + 32 * blake2sSigma roundIndex (2 * gateIndex + 1))
      let a1 ← add3W cw a b mx gateBase
      let d1 := rotateRightW (xorW d a1) 16
      let c1 ← addW cw c d1 (gateBase + 61)
      let b1 := rotateRightW (xorW b c1) 12
      let a2 ← add3W cw a1 b1 my (gateBase + 92)
      let d2 := rotateRightW (xorW d1 a2) 8
      let c2 ← addW cw c1 d2 (gateBase + 153)
      let b2 := rotateRightW (xorW b1 c2) 7
      state := ((state.set! laneA a2).set! laneB b2 |>.set! laneC c2).set! laneD d2
  for word in List.range 8 do
    let out := xorW (xorW (state.getD word #[]) (state.getD (word + 8) #[])) (slotsW cw (32 * word))
    linearRows cw out (256 + 32 * word)
  setRow blake2sConstantColumn constant constant

/-- `blake2s_row_values(column_weights)`: `A0·w` and `B0·w` by one forward walk of the circuit
(`verifier.py:1199-1308`). -/
def blake2sRowValues (columnWeights : List E) : Array E × Array E :=
  let size := 2 ^ blake2sR1csLogSize
  ((blake2sWalk columnWeights.toArray).run (Array.replicate size 0, Array.replicate size 0)).2

/-- `blake2s_bilinear(alpha, row_weights, column_weights)`: `e_rowᵀ (A0 + α B0) w_col`
(`verifier.py:1311-1314`). -/
def blake2sBilinear (alpha : E) (rowWeights columnWeights : List E) : E :=
  let (left, right) := blake2sRowValues columnWeights
  dot rowWeights left.toList + alpha * dot rowWeights right.toList

/-! ### The lincheck (`verifier.py:1172-1196`) -/

/-- The lincheck's row weights: the Lagrange weights at the skip challenge, along the
equality weights of the row point (`verify_flock_lincheck`'s `e_row`). -/
def lincheckRowWeights (zSkip : E) (chiIn : List E) : List E :=
  (eqKernel chiIn).flatMap fun weight ↦ (lagrangeWeights kBits zSkip).map (weight * ·)

/-- The lincheck's column weights: the slices along the equality weights of the column point
(`verify_flock_lincheck`'s `w_col`). -/
def lincheckColumnWeights (chiInPrime s : List E) : List E :=
  (eqKernel chiInPrime).flatMap fun weight ↦ s.map (· * weight)

/-- `verify_flock_lincheck(zc)` (`verifier.py:1172-1196`): eight plain-mode rounds bind the
high column coordinates; the 64 slices `s` close the terminal identity, the matrices' value from
`ev`. Returns the claim's point and the slices. -/
def verifyFlockLincheck (ev : Evaluations) (zc : ZerocheckResult) : Prog (List E × List E) := do
  let alpha ← Prog.sampleE
  let skipWeights := lagrangeWeights kBits zc.zSkip
  let chiIn := zc.chi.take flockNumLincheckRounds
  let claim := zc.vA + alpha * zc.vB + alpha ^ 2 * zc.vC + alpha ^ 3
  let (roundChallenges, rLc) ←
    sumcheck claim 3 (List.replicate flockNumLincheckRounds none)
  let s ← Prog.readN kBits
  let chiInPrime := roundChallenges.reverse
  let wCol := lincheckColumnWeights chiInPrime s
  let matrixValue ← ev.matrices alpha zc.zSkip chiIn chiInPrime s
  let terminal := matrixValue +
    alpha ^ 2 * eqEval chiIn chiInPrime * dot skipWeights s +
    alpha ^ 3 * wCol.getD blake2sConstantColumn 0
  Prog.require (terminal = rLc)
  return (chiInPrime ++ zc.chi.drop flockNumLincheckRounds, s)

/-- `verify_flock(log_n)`: the zerocheck, then the lincheck (`verifier.py:1317-1321`). -/
def verifyFlock (ev : Evaluations) (logN : ℕ) : Prog (List E × List E) := do
  let zc ← verifyFlockZerocheck logN
  verifyFlockLincheck ev zc

/-! ### Ring switching (`verifier.py:1324-1360`) -/

/-- `_phi(value, challenges)`: `a ↦ a + f_p · a^(2^shift)`, stage by stage
(`verifier.py:1330-1334`). -/
def phiMap (value : E) (challenges : List E) : E :=
  (List.zip challenges ringMapShifts).foldl
    (fun value (challenge, shift) ↦ value + challenge * value ^ (2 ^ shift)) value

/-- `_ring_weight(r, r_prime, coefficients)`: `Σ_k c_k Π_n (1 + r_n^(2^k) + r'_n)`
(`verifier.py:1337-1348`). -/
def ringWeight (r rPrime coefficients : List E) : E :=
  (coefficients.foldl (fun (acc : E × List E) c ↦
    let product := (List.zip acc.2 rPrime).foldl
      (fun product (value, challenge) ↦ product * (1 + value + challenge)) c
    (acc.1 + product, acc.2.map (· ^ 2))) (0, r)).1

/-- The Frobenius coefficients of the drawn map, `Φ(a) = Σ_{k < 64} c_k a^(2^k)`
(`verifier.py:1358`). -/
def ringCoefficients (challenges : List E) : List E :=
  (List.range kBits).map fun k ↦
    ((List.zip challenges ringMapShifts).filter fun (_, s) ↦ k &&& s ≠ 0).foldl
      (fun acc (f, s) ↦ acc * f ^ (2 ^ (k % s))) 1

/-- `ring_switch(point, s)` (`verifier.py:1351-1360`): draw the map, and return the target
`Σ_i g^i Φ(s_i)` and the weight `W(u) = Φ(eq(point, u))` as a function of the opening point. -/
def ringSwitch (point s : List E) : Prog (E × (List E → E)) := do
  let challenges ← Prog.sampleN ringMapShifts.length
  let coefficients := ringCoefficients challenges
  let target := polyEval (s.map (phiMap · challenges)) gen
  return (target, fun rPrime ↦ ringWeight point rPrime coefficients)

open LeanVM.Semantics LeanVM.Protocol.Blake2sHash

/-!
## The leanVM verifier

From `verifier.py`, lines 644 (`R1CS_DIGEST`), 1378-1428
(`verify_execution`) and 355-358 (`Transcript.__init__`).

`leanVmProgram bytecode publicInput` is `verify_execution` in the verifier language, one
`Prog` function per phase of the Python:

1. the announced sizes (`readN 8`: the memory's log-size, the six tables' row counts, the rate),
   their checks and `buildLayout`;
2. the stack's root (`commitStack`, commitment `0`);
3. the bus (`verifyBusBalance`);
4. the table sumcheck (`tableSumcheck`) at the bus point;
5. the public input's binding;
6. Flock (`verifyFlock`);
7. ring switching (`ringSwitch`) and the stacked opening (`verifyStackedOpening`), which runs
   WHIR on every claim.

The program returns `true` where the Python returns; `Transcript.finish`, the check that the
proof is consumed, is `Compile.runProof`'s.

**The seed.** The Fiat-Shamir chain starts at `compress(IV, public_input)`, `IV` the BLAKE2s
hash of `"leanvm" ‖ u64le(32) ‖ R1CS_DIGEST ‖ H(bytecode)`, the bytecode hashed as its
little-endian words. `seedWith H` computes it with any hash; `verifyWith H` is the compiled
reading at `H`; `verify` is the deployed verifier, the `Id` instance at `blake2sBytes`
(`verifyWith_blake2sBytes`, by `rfl`).

**Compilation.** `LeanVM.Spec.Fast.Hash` compiles `blake2sBytes` with the rotation
on machine words, as `LeanVM.Spec.Fast.FieldWords` compiles the field arithmetic. Both are
`@[csimp]` lemmas: the definitions here, and the theorems about them, are unchanged.
-/

/-! ### The program -/

/-- The announced sizes, read and checked, and the layout they give
(`verifier.py:1384-1392`): the layout and the WHIR rate exponent. -/
def readSizes (bytecode : List K) : Prog (Layout × ℕ) := do
  let announced ← Prog.readN (2 + tables.length)
  Prog.require (announced.all fun value ↦ value.limb 1 = 0 ∧ value.limb 2 = 0)
  let logMemory := kToNat ((announced.headD 0).limb 0)
  let tableRows := ((announced.drop 1).take tables.length).map fun value ↦ kToNat (value.limb 0)
  let logInverseRate := kToNat ((announced.getLastD 0).limb 0)
  Prog.require (1 ≤ logInverseRate ∧ logInverseRate ≤ 4)
  let layout ← liftOption (buildLayout bytecode logMemory tableRows)
  Prog.require (minStackedLog ≤ layout.stackLog ∧ layout.stackLog ≤ maxStackedLog)
  return (layout, logInverseRate)

/-- Step 4, the table sumcheck at the bus point (`verifier.py:1400-1408`): the claims of the bus
and of the tables. -/
def tablePhase (layout : Layout) (bus : BusResult) : Prog (List ColumnClaim) := do
  let xi ← Prog.sampleE
  let nConstraints := (tables.map Table.nConstraints).sum
  let xiPowers := powers xi (nConstraints + 3)
  let constraintPowers := xiPowers.take nConstraints
  let formPowers := xiPowers.drop nConstraints
  let target := dot formPowers bus.totals
  let tableClaims ← tableSumcheck layout.tableLogHeights bus.forms constraintPowers formPowers
    bus.point target
  return bus.claims ++ tableClaims

/-- Step 5, binding the public input (`verifier.py:1410-1416`): a challenge, and claims on the
three memory columns at `(challenge, 0, …, 0)`, each limb's claim the line through that limb of
the public input's two halves, evaluated at the challenge by the verifier itself. The prover sends
nothing. -/
def publicInputPhase (layout : Layout) (publicInput : Digest) : Prog (List ColumnClaim) := do
  let publicChallenge ← Prog.sampleE
  let halves := digestScalars publicInput
  let publicLimbs := ([0, 1, 2] : List (Fin 3)).map fun limb ↦
    multilinearEval [ofK (halves.1.limb limb), ofK (halves.2.limb limb)] [publicChallenge]
  let publicPoint := publicChallenge ::
    List.replicate ((layout.placements.getD memory0 default).vars - 1) 0
  return List.zipWith (fun column value ↦ ⟨column, publicPoint, value⟩)
    [memory0, memory1, memory2] publicLimbs

/-- Step 7's ring-switching claim on the stack: supported on `q_flock`'s region, its weight
carries the placement's selector (`verifier.py:1425-1426`). -/
def ringSwitchClaim (layout : Layout) (target : E) (weight : List E → E) : StackClaim :=
  let qflockPlacement := layout.placements.getD qflock default
  (fun x ↦ qflockPlacement.eqAbove x * weight (x.take qflockPlacement.vars), target)

/-- `verify_execution(bytecode, public_input, proof)` without its `finish`
(`verifier.py:1378-1427`), the fixed polynomials' values from `ev`. -/
def verifyExecution (ev : Evaluations) (bytecode : List K) (publicInput : Digest) :
    Prog Unit := do
  -- 1] memory log-size, table log-sizes, and the WHIR rate
  let (layout, logInverseRate) ← readSizes bytecode
  -- 2] the stack's commitment
  commitStack layout.stackLog logInverseRate
  -- 3] the bus
  let bus ← verifyBusBalance ev layout
  -- 4] the table sumcheck
  let claims ← tablePhase layout bus
  -- 5] the public input
  let publicClaims ← publicInputPhase layout publicInput
  let claims := claims ++ publicClaims
  -- 6] BLAKE2s validity via Flock
  let (flockPoint, flockS) ←
    verifyFlock ev (blake2sR1csLogSize + layout.tableLogHeights.getD opBlake2s 0)
  -- 7] ring switching, then one opening of the stack for every claim
  let (ringTarget, ringWeight) ← ringSwitch flockPoint flockS
  verifyStackedOpening layout.stackLog logInverseRate
    (ringSwitchClaim layout ringTarget ringWeight :: claims.map (·.onStack layout))

/-! ### The fixed polynomials' values -/

/-- The deployed verifier computes the fixed polynomials' values. -/
def Evaluations.computed : Evaluations where
  bytecode words point := pure (multilinearEval (words.map ofK) point)
  matrices alpha zSkip chiIn chiInPrime s :=
    pure (blake2sBilinear alpha (lincheckRowWeights zSkip chiIn)
      (lincheckColumnWeights chiInPrime s))

/-- What a proof claims of the fixed polynomials, for a verifier that does not evaluate them:
the bytecode's value at its point, and the matrices' value at the lincheck's weights, given by
`alpha`, the skip challenge, the row and column points and the slices. -/
structure FixedClaims where
  /-- Where the bus reads the bytecode. -/
  bytecodePoint : List E
  /-- The bytecode's value there. -/
  bytecodeValue : E
  /-- The lincheck's batching challenge. -/
  alpha : E
  /-- The zerocheck's skip challenge. -/
  zSkip : E
  /-- The lincheck's row point. -/
  rowPoint : List E
  /-- The lincheck's column point. -/
  columnPoint : List E
  /-- The 64 slices. -/
  slices : List E
  /-- The matrices' value at those weights. -/
  matrixValue : E

/-- The values claimed by `c`, at the points of `c` only: the run fails where the verifier asks
elsewhere. -/
def Evaluations.claimed (c : FixedClaims) : Evaluations where
  bytecode _ point := do
    Prog.require (point = c.bytecodePoint)
    return c.bytecodeValue
  matrices alpha zSkip chiIn chiInPrime s := do
    Prog.require (alpha = c.alpha ∧ zSkip = c.zSkip ∧ chiIn = c.rowPoint ∧
      chiInPrime = c.columnPoint ∧ s = c.slices)
    return c.matrixValue

/-- The claims are true of `bytecode` and of flock's matrices. -/
def FixedClaims.Holds (bytecode : List K) (c : FixedClaims) : Prop :=
  multilinearEval (bytecode.map ofK) c.bytecodePoint = c.bytecodeValue ∧
    blake2sBilinear c.alpha (lincheckRowWeights c.zSkip c.rowPoint)
      (lincheckColumnWeights c.columnPoint c.slices) = c.matrixValue

/-! ### The programs -/

/-- **The leanVM verifier program**: `verify_execution` in the verifier language, accepting
where the Python returns. -/
def leanVmProgram (bytecode : List K) (publicInput : Digest) : Prog Bool := do
  verifyExecution .computed bytecode publicInput
  return true

/-- The verifier program with the fixed polynomials' values claimed by `c`. -/
def deferredProgram (c : FixedClaims) (bytecode : List K) (publicInput : Digest) : Prog Bool := do
  verifyExecution (.claimed c) bytecode publicInput
  return true

/-! ### The seed and the compiled verifier -/

/-- `R1CS_DIGEST` (`verifier.py:644`). -/
def r1csDigest : List UInt8 :=
  [0x53, 0x7a, 0xd2, 0x07, 0x90, 0x30, 0x8f, 0x8e, 0xb8, 0xc0, 0xe8, 0xbd, 0x3e, 0x6c, 0x58, 0xee,
    0x64, 0x57, 0x33, 0x71, 0xe3, 0xd5, 0x3c, 0x30, 0x61, 0x3d, 0xd0, 0x4d, 0x87, 0xc0, 0xb7, 0xea]

/-- The IV's preimage, `"leanvm" ‖ u64le(len R1CS_DIGEST) ‖ R1CS_DIGEST ‖ H(bytecode)`
(`verifier.py:1380`). -/
def ivPreimage (bytecodeHash : Digest) : Bytes :=
  [0x6c, 0x65, 0x61, 0x6e, 0x76, 0x6d] ++ [32, 0, 0, 0, 0, 0, 0, 0] ++ r1csDigest ++
    digestBytes bytecodeHash

section Hash

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest)

/-- The chain's initial state with the hash `H`: `compress(IV, public_input)`, the IV being the
hash of `ivPreimage` (`verifier.py:1379-1382`, `Transcript.__init__`). -/
def seedWith (bytecode : List K) (publicInput : Digest) : m Digest := do
  let bytecodeHash ← H (bytecode.flatMap kBytes)
  let fiatShamirIv ← H (ivPreimage bytecodeHash)
  H (digestBytes fiatShamirIv ++ digestBytes publicInput)

/-- The compiled verifier with the hash `H`: the program run on the proof from the seed. -/
def verifyWith (bytecode : List K) (publicInput : Digest) (π : Proof) : m Bool := do
  let seed ← seedWith H bytecode publicInput
  runProof H (leanVmProgram bytecode publicInput) seed π

/-- The IV with the hash `H`, the hash of `ivPreimage` (`Bytecode::new`). -/
def fiatShamirIvWith (bytecode : List K) : m Digest := do
  let bytecodeHash ← H (bytecode.flatMap kBytes)
  H (ivPreimage bytecodeHash)

/-- **The deferring verifier** with the hash `H`, as an aggregate runs it on a child's proof
(`verify_sub`): the IV is given rather than hashed from the bytecode, and the fixed polynomials'
values are those claimed by `c`. Only the bytecode's length is read. -/
def verifyDeferredWith (bytecode : List K) (iv publicInput : Digest) (c : FixedClaims)
    (π : Proof) : m Bool := do
  let seed ← H (digestBytes iv ++ digestBytes publicInput)
  runProof H (deferredProgram c bytecode publicInput) seed π

end Hash

/-- The deployed seed, with BLAKE2s. -/
def seed (bytecode : List K) (publicInput : Digest) : Digest :=
  Id.run (seedWith blake2sBytes bytecode publicInput)

/-- The deployed IV, with BLAKE2s. -/
def fiatShamirIv (bytecode : List K) : Digest := Id.run (fiatShamirIvWith blake2sBytes bytecode)

/-- The deployed deferring verifier, with BLAKE2s. -/
def verifyDeferred (bytecode : List K) (iv publicInput : Digest) (c : FixedClaims) (π : Proof) :
    Bool :=
  Id.run (verifyDeferredWith blake2sBytes bytecode iv publicInput c π)

/-- **The deployed leanVM verifier**: the program's compiled reading with BLAKE2s, from the
deployed seed. -/
def verify (bytecode : List K) (publicInput : Digest) (π : Proof) : Bool :=
  Id.run (runProof blake2sBytes (leanVmProgram bytecode publicInput) (seed bytecode publicInput) π)

end
end LeanVM.Protocol.Verifier
