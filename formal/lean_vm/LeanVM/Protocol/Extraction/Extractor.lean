module

public import Statement.LeanVm
public import LeanVM.Protocol.Compile.RunPure
public import CompPoly.Univariate.Roots.Shoup.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.Finite.Basic
public import CompPoly.Bivariate.GuruswamiSudan.Executable
public import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness.Completeness
public import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Correctness
public import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.FiniteField
public import CompPoly.Univariate.Roots.Shoup
public import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.Fast

/-!
# The knowledge extractor

The straight-line extractor `lean_vm` proves knowledge soundness for, `extract`, which
`LeanVM.transcriptExtractor` (at the end of this file) applies to the program's bytecode and to
the Keccak-256 evaluations of the adversary's transcript of queries to the random permutation (the byte strings
whose whole sponge path the adversary queried, with their digests, and the list of those byte
strings, `keys`). It reads the statement (the program, its bytecode and the public input), the proof
and those evaluations, and nothing else: it neither queries the permutation, nor sees the verifier's
queries, nor runs the adversary again. It is deterministic and computable (no coins, no classical
choice: every loop is a traversal of an explicitly sized list or array, or a recursion on an
explicit natural number). Of the proof it reads only the stream's first `10` scalars (the
announced sizes and the stack's root), so its running time does not grow with the proof: it is
polynomial in the announced committed size `2^μ` and the number `N` of evaluations given, and
linear in the bytecode; it is infeasible at deployed sizes except on a word without errors
(`fastStacks`). The cost table below is read off its loops, not proved.

1. **The announced sizes and the stack's root** (`afterRoot`): read off the proof as the
   verifier's steps 1 and 2 read them (`crates/verifier/src/lib.rs:219-237`), with every hash and
   permutation answered by a constant (`runPure`): what they read does not depend on the sponge.
2. **The committed word** (`committedLeaves`, `leafAt`): the Merkle tree under the root inverted
   through the evaluations, top down: a node's children are the two digests its unique answered
   64-byte preimage holds, a leaf the words of its unique answered preimage; an unanswered node
   gives zero leaves. Proved, when no two answered strings share a digest: leaf `v` is the leaf of
   any opening at position `v` that climbs to the root through the evaluations (the check of
   `Transcript::merkle`, `crates/verifier/src/transcript.rs:153-186`).
3. **The candidates** (`decodeStacks`). Level 0 commits the stack (the committed columns, stacked,
   `2^μ` words of `K`) in `2^6` lanes: lane `u` is the stack's block `u`, its cells
   `j + 2^(μ−6)·u` for `j < 2^(μ−6)`, read as coefficients in the novel polynomial basis `X_j`,
   and column `v` of the word is the leaf holding the values of the `64` lanes at the domain point
   `x_v = K.ofBits v`, in reverse order (`whir.rs:198-207`, `row.iter().rev()`): the binary
   Reed–Solomon code of Annex B, §B.2 (`doc/leanvm/body/b-polynomial-commitment-scheme.tex`)
   and the encoder of Annex D, `def:enc` (`doc/leanvm/body/d-novel-basis.tex`). The candidates are
   the stacks whose encoding agrees with the word on at least the Johnson threshold of columns
   (`johnsonThreshold`), at most `2^12` at every admissible shape. The extractor lists them: it
   decodes each lane with the Guruswami–Sudan list decoder over `K` (`gsLaneAt`), and extends
   prefixes of lanes one lane at a time, keeping a prefix while its lanes agree with the word on at
   least the threshold of common columns (`pruneUpTo`). Every candidate is listed (proved). A word
   without errors, an honest prover's, is decoded first by interpolation alone (`fastStacks`).
4. **The execution** (`candidateExecutionIn`): a listed stack's memory image run from the initial
   state for at most as many steps as the announced tables have rows (`stepCap`; a halting run
   never repeats a state and each of its steps takes a row of its own, so a valid execution a
   stack represents halts within the cap, proved). The first listed stack's run that halts with
   the public input at its boundary, a valid execution; `none` if there is none.

**Cost**, in operations of `K`, 64-bit words and byte comparisons; `N` the number of evaluations
given, `n = 2^(κ+R)` the columns (`κ = μ − 6 ≤ 22`, `R ≤ 4`), `k = 2^κ`, `L` the list size (at most
`2^12` candidates, `LeanVM.candidates_ncard_le`, and at most `2^12` prefixes kept after any number
of lanes, `pruneUpTo_length_le`), `m ≤ 256` the decoder's multiplicity, `ℓ ≤ 513` its
`Y`-degree, `w = m·A − 1` its weighted degree and `|Q| ≈ n·m(m+1)/2` its coefficients
(`gsMultiplicityAt`), `M = 2^logMemory`, `B = 2^logBytecode`. The figures are at the worst shape
over all 64 lanes, from `lean_vm/scripts/extractor-cost` (a model of the code, not a proof):

| Step | Cost | At worst |
| --- | --- | --- |
| sizes and root (`afterRoot`) | the stream's first `10` scalars; the bytecode's length | |
| the evaluations (`keccakEvaluationsOfTranscript`, `lookupEvaluation`) | linear lookups on byte strings: a chain of `N` padded blocks makes `136·N³/6` byte comparisons | in `N` |
| Merkle inversion (`committedLeaves`) | `N` evaluations, then `2^(height+1)` scans of `N` pairs | `2^27·N` |
| interpolation (`gsLaneAt`: Lee–O'Sullivan, Mulders–Storjohann) | `(ℓ+1)³·(m·n)²` per lane | `2^88.6` |
| roots (Roth–Ruckenstein, `substituteYRootPlusXY`) | per substitution, `|Q|·ℓ/2` monomials added one by one to a dense accumulator (`|Q|²·ℓ/2`) and as many bignum binomials; `k` substitutions per path, `1` to `ℓ` paths | `2^103.6` to `2^110.6` |
| final root check (`isRootYDegreeLtBool`) | `ℓ·(w + ℓ·k)²` per candidate (quadratic `mulRaw`), at most `ℓ` per lane | `2^79.7` |
| distance filter, novel coefficients (`toNovel`, `novelInv`, `novelFwd`) | `n·k` per candidate; `κ·2^(κ+R)` butterflies | `2^60.9` |
| pruning (`pruneUpTo`), 64 lanes | `64·L²·n` comparisons | `2^56` |
| a candidate's execution | `M + B` to index the addresses, at most `stepCap ≤ 2^μ` steps of a fetch and at most 26 reads | `2^52` for all |

The whole is dominated by Roth–Ruckenstein's substitution as implemented, then the interpolation,
and, in `N`, by the lookups, cubic. Polynomial, but not a meaningful concrete bound: an extractor
of `2^111` operations, or `N³` for an adversary of `N` queries, makes a reduction no better than
generic search.

**The same function, faster** (proof side, `lean_vm/LeanVM/Protocol/Extraction/Fast/`):
`transcriptExtractorFast`, proved equal to `transcriptExtractor` (`transcriptExtractorFast_eq`);
the compiled program's list decoder (`decOf`, `Fast/Compiled.lean`) is `decodeStacksDistinctPM`
(`Fast/LanePM.lean`), which interpolates each lane by CompPoly's approximant basis (the certified
solve of the Guruswami–Sudan modular equations by an ordered-weak-Popov PM-basis, its polynomial
products by the additive FFT) and is proved to list the same stacks
(`decodeStacksDistinctPM_eq`; the proof side's reference interpolation, Lee and O'Sullivan's
algorithm with Mulders and Storjohann's reduction, is no longer compiled). It substitutes in
Roth–Ruckenstein by a
Taylor shift with binomials by parity, modulo `X^(k−depth)` with an exact fallback at repeated
roots (`ℓ²·k/2` per substitution, `2^68.8` in all), skips the final root check where the
Guruswami–Sudan lemma makes it redundant, looks up addresses by binary search in sorted tables,
and keeps the replay, the first answers and the preimages in sorted maps (`O(log² N)` comparisons
per lookup, worst-case, keeping evaluations of at most `L = max(64, 8·width)` bytes). Compiled to
the cost machine of `Statement/CostMachine.lean` (`Cost/Extractor/Top.lean`), it is the program
`compiledKnowledgeExtractor` (`Cost/ExtractorProgram.lean`) of the end statement:
`knowledgeExtractorOf extractorProgram = transcriptExtractor` (`Cost/Efficient.lean`). Its price is
proved (`LeanVM.Cost.Bounds.extractorC_cost`): at most about `2^94.07` at the worst shape for at
most
`2^40` queries, the list decoder dominating (`extractorPrice_28_4`), and `2^156.69` for `2^128`
queries, the transcript's index dominating (`extractorPrice_28_4_2_128`).
Each lane's list is sorted (`laneListAt`, `coeffsLE`), so it depends only on the set the decoder
returns, whichever interpolation computes it.

**Where it was.** This file and the transcript's extractor were the trusted statement's
(`Statement/Extractor.lean`, `Statement/LeanVm.lean`) until the end statement took the extractor
as a cost-machine program within a size bound and a budget (`LeanVM.extractorComputedBy`,
`Statement/CostMachine.lean`): moved here verbatim, but for the address indices and the public
boundary (`powIndex`, `gLogIn`, `boundaryOK`, `Statement/Prover/Witness.lean`), which the
statement keeps for the honest prover. The budget reads the announced shape off the stream
(`announced`, `Statement/LeanVmVerifier.lean`), the shape `afterRoot` returns.

The Annexes are cited at leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`.

**Credits.** The list decoder over `K` is CompPoly's (github.com/Verified-zkEVM/CompPoly at
`572f997390aa4fc131ef30b1186fa1dcf292ca10`, Apache-2.0, "Copyright (c) 2026 CompPoly
Contributors"): by Valerii Huhnin, the executable Guruswami–Sudan decoder and its core and filter
(`Bivariate/GuruswamiSudan/{Executable,Core,Filter,Context}.lean`), its interpolation by the
algorithm of Lee and O'Sullivan (*List decoding of Reed–Solomon codes from a Gröbner basis
perspective*, J. Symbolic Comput. 43, 2008) with the reduction of Mulders and Storjohann (*On
lattice reduction for polynomial matrices*, J. Symbolic Comput. 35, 2003), its bivariate roots by
the algorithm of Roth and Ruckenstein (*Efficient decoding of Reed–Solomon codes beyond half the
minimum distance*, IEEE Trans. Inf. Theory 46, 2000), the roots in a finite field and their
deterministic splitting by Shoup's small-characteristic trace splitter (*A fast deterministic
algorithm for factoring polynomials over finite fields of small characteristic*, ISSAC 1991; at
characteristic two, Berlekamp's trace algorithm), the vanishing polynomial and batch evaluation
(`Univariate/{Vanishing,BatchEval/Context}.lean`), and `SmallPrimeTraceContext`; by Nicolas
Schleicher, `BF64`; and `CPolynomial` (Quang Dao, Gregor Mitscha-Baude, Derek Sorensen, Desmond
Coles, Valerii Huhnin, Julian Sutherland). The decoder's parameter check mirrors ArkLib's
certificate (github.com/Verified-zkEVM/ArkLib at `4dae3acff846125521b7b3998010885071746f16`,
Apache-2.0; not imported): `GSParamCert` (`GuruswamiSudan/Executable.lean`, Valerii Huhnin) and
the closed form of `numVars` (`GuruswamiSudan/Basic.lean`, Stefano Rocca). The novel-basis
transforms are the additive NTT of Lin, Chung and Han (FOCS 2014), as in Diamond and Posen,
*Polylogarithmic proofs for multilinears over binary towers* (2024), Algorithm 2, whose forward
stage and point order are CompPoly's `AdditiveNTT` (Chung Thai Nguyen and Quang Dao); no code of
it is copied. The list decoding is Guruswami and Sudan's (*Improved decoding of Reed–Solomon and
algebraic-geometry codes*, IEEE Trans. Inf. Theory 45, 1999).
-/

@[expose] public section

namespace LeanVM.Extraction

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Parameters.Whir LeanVM.Protocol.KeccakHash
open CompPoly CompPoly.GuruswamiSudan CompPoly.CPolynomial.Roots.FiniteField

/-! ### 1. The announced sizes and the stack's root -/

/-- `verify_execution`'s steps 1 and 2 (`lib.rs:219-237`): read the announced sizes, then
the stack's root; the layout and the WHIR rate exponent. -/
def announceSizesAndRoot (bytecode : List K) : VerifierProgram (Layout × ℕ) := do
  let (layout, logInverseRate) ← readAnnouncedSizes bytecode
  commitStack layout.stackLog logInverseRate
  return (layout, logInverseRate)

/-- The verifier's state after its steps 1 and 2 on the proof `π`: the announced layout and rate
exponent, and the state, whose first root is the stack's; `none` if the steps reject. The layout
and the rate are the ones the stream announces (`announced`, which the statement's budget reads):
`LeanVM.Extraction.Fast.announced_of_afterRoot`. -/
def afterRoot (bytecode : List K) (π : Proof) : Option ((Layout × ℕ) × VerifierProgramState) :=
  runPure (announceSizesAndRoot bytecode) ⟨⟨default, [], none⟩, π.stream, π.openings, []⟩

/-! ### 2. The committed word -/

/-- The little-endian 64-bit word of the first eight bytes (the inverse of `wordBytes`). -/
def bytesWord (b : Bytes) : UInt64 :=
  UInt64.ofNat ((b.take 8).foldr (fun x acc ↦ x.toNat + 256 * acc) 0)

/-- The first `L` little-endian 64-bit words of a byte string. -/
def bytesLanes : ℕ → Bytes → List UInt64
  | 0, _ => []
  | L + 1, b => bytesWord b :: bytesLanes L (b.drop 8)

/-- The digest of the first 32 bytes (the inverse of `digestBytes`). -/
def bytesDigest (b : Bytes) : Digest := Vector.ofFn fun i : Fin 4 ↦ (bytesLanes 4 b).getD i.val 0

/-- The `w` words of `K` of the first `8w` bytes (the inverse of `flatMap kBytes`). -/
def bytesWords (w : ℕ) (b : Bytes) : List K := (bytesLanes w b).map K.ofLane

/-- The two children of a node, from the 64 bytes it hashes. -/
def splitNode (b : Bytes) : Digest × Digest := (bytesDigest b, bytesDigest (b.drop 32))

/-- The answered pairs `(x, answers x)` of the keys, one call of `answers` per key. -/
def answerPairs (answers : Bytes → Option Digest) (keys : List Bytes) : List (Bytes × Digest) :=
  keys.filterMap fun x ↦ (answers x).map (x, ·)

/-- The byte string of length `len` answered by `d`, if exactly one is; `none` otherwise. -/
def preimage (pairs : List (Bytes × Digest)) (d : Digest) (len : ℕ) : Option Bytes :=
  let hit : Bytes × Digest → Bool := fun p ↦
    decide (p.2.toList = d.toList) && decide (p.1.length = len)
  match pairs.find? hit with
  | none => none
  | some p => if pairs.all (fun p' ↦ !hit p' || decide (p'.1 = p.1)) then some p.1 else none

/-- The leaf under a digest: the `w` words of its preimage of `8w` bytes, zeros if there is none. -/
def leafOf (pairs : List (Bytes × Digest)) (w : ℕ) (d : Digest) : List K :=
  match preimage pairs d (8 * w) with
  | some x => bytesWords w x
  | none => List.replicate w 0

/-- The `2^h` leaves under the digest `d` at height `h`, left to right: a node's children are the
halves of its 64-byte preimage; zero leaves under a node without one. -/
def subtreeLeaves (pairs : List (Bytes × Digest)) (w : ℕ) : ℕ → Digest → Array (List K)
  | 0, d => #[leafOf pairs w d]
  | h + 1, d =>
    match preimage pairs d 64 with
    | some x => subtreeLeaves pairs w h (splitNode x).1 ++ subtreeLeaves pairs w h (splitNode x).2
    | none => Array.replicate (2 ^ (h + 1)) (List.replicate w 0)

/-- **The committed leaves**: the `2^height` leaves of `width` words under `root`, read off the
answers to the keys. -/
def committedLeaves (answers : Bytes → Option Digest) (keys : List Bytes) (root : Digest)
    (height width : ℕ) : Array (List K) :=
  subtreeLeaves (answerPairs answers keys) width height root

/-- Position `v` of the committed word: leaf `v mod 2^height` (`width` zeros if absent). -/
def leafAt (leaves : Array (List K)) (height width v : ℕ) : List K :=
  leaves.getD (v % 2 ^ height) (List.replicate width 0)

/-! ### 3. The Johnson threshold -/

/-- The subspace polynomial `W_i(a) = ∏_{v < 2^i} (a + x_v)`, `x_v = K.ofBits v`: it vanishes
exactly on `U_i = {x_v | v < 2^i}`. -/
def subspacePoly (i : ℕ) (a : K) : K := ∏ v ∈ Finset.range (2 ^ i), (a + K.ofBits v)

/-- Level 0's Johnson slacks, `η = e / 2^22`: entry `[R − 1][μ − 15]` for the stack size `μ` and
the rate exponent `R`. The soundness proof certifies the opening's `2^-128` per query at these
slacks, each the largest at which every group of level 0 is at most `2^-128` (chosen offline by
`lean_vm/scripts/whir-params/gen.py`): a larger slack means a smaller list of candidates and a
smaller multiplicity, so a cheaper decoder. The table is copied from the proof's certificates,
and the proof checks the copy against them for every admissible shape (`certOf_e_eq`,
`thrOf_eq_johnsonThreshold` in `LeanVM.Protocol.EndToEnd.Sound`). -/
def johnsonSlack : List (List ℕ) := [
  [6676, 7275, 5527, 5165, 4984, 4765, 4720,
    9241, 9214, 9200, 9198, 9194, 13737, 13737],
  [2049, 14336, 13824, 13312, 13184, 13120, 13056,
    13040, 13032, 13024, 13022, 13021, 13020, 13019],
  [22794, 21557, 21195, 20886, 20796, 20750, 20728,
    20716, 20707, 20704, 20703, 20701, 20701, 20700],
  [14336, 13824, 13440, 13248, 13152, 13104, 13080,
    13068, 13064, 13062, 13061, 13060, 13059, 13059]]

/-- Level 0's slack `e` (`η = e/2^22`) for a stack of `2^μ` words at rate `2^-R`. -/
def johnsonSlackOf (μ R : ℕ) : ℕ := (johnsonSlack.getD (R - 1) []).getD (μ - minLogStack) 0

/-- `⌈√x⌉` on natural numbers. -/
def ceilSqrt (x : ℕ) : ℕ := if Nat.sqrt x * Nat.sqrt x = x then Nat.sqrt x else Nat.sqrt x + 1

/-- **The Johnson threshold** of level 0 for a stack of `2^μ` words at rate `2^-R`: with
`κ = μ − 6` message variables, `n = 2^(κ+R)` columns and the degree bound `D = 2^κ − 1`, the
agreement `⌈(√(D/n) + η)·n⌉`, the Johnson radius `√(D/n)` plus the slack `η = e/2^22`
(`johnsonSlackOf`), computed exactly in natural numbers: `(√(D/n) + η)·n = (√X + e·n)/2^22` with
`X = 2^44·D·n`, and `⌈(√X + b)/c⌉ = ⌈(⌈√X⌉ + b)/c⌉` (the real form is equal,
`johnsonThreshold_eq_real` in `LeanVM.Extraction`). The table's default `0` is never read: the
extractor reaches the threshold only after `readAnnouncedSizes` accepted the sizes, so `1 ≤ R ≤ 4`
and
`15 ≤ μ ≤ 28`, the table's range. -/
def johnsonThreshold (μ R : ℕ) : ℕ :=
  let κ := μ - initialFold
  let n := 2 ^ (κ + R)
  let D := 2 ^ κ - 1
  (ceilSqrt (2 ^ 44 * D * n) + johnsonSlackOf μ R * n + 2 ^ 22 - 1) / 2 ^ 22

/-! ### 4. Novel-basis coefficients and evaluations

The additive NTT in the novel basis `X_j(a) = ∏_{i < 64, bit i of j} Ŵ_i(a)`, `Ŵ_i` the
normalized subspace polynomial `W_i(a) / W_i(x_{2^i})`, on the points `x_v`. Stage `i` pairs the positions `p`
and `p + 2^i` (bit `i` of `p` clear) with the twiddle `t = Ŵ_i(x_{⌊p/2^(i+1)⌋·2^(i+1)})`: the
forward stage maps `(lo, hi)` to `(lo + t·hi, lo + (t + 1)·hi)`, the inverse stage maps it back
(characteristic two). -/

/-- Stage `i`'s twiddles over a buffer of `2^m`: entry `w` is `Ŵ_i(x_{w·2^(i+1)})`. -/
def novelTwiddles (m i : ℕ) : Array K :=
  let nrm := (subspacePoly i (K.ofBits (2 ^ i)))⁻¹
  Array.ofFn fun w : Fin (2 ^ (m - (i + 1))) ↦ subspacePoly i (K.ofBits (w.val * 2 ^ (i + 1))) * nrm

/-- The forward butterfly stage `i` over a buffer of `2^m`. -/
def novelFwdStage (m i : ℕ) (b : Array K) : Array K :=
  let tw := novelTwiddles m i
  Array.ofFn fun p : Fin (2 ^ m) ↦
    let t := tw.getD (p.val / 2 ^ (i + 1)) 0
    if p.val.testBit i then
      b.getD (p.val - 2 ^ i) 0 + (t + 1) * b.getD p.val 0
    else
      b.getD p.val 0 + t * b.getD (p.val + 2 ^ i) 0

/-- The inverse butterfly stage `i` over a buffer of `2^m`. -/
def novelInvStage (m i : ℕ) (b : Array K) : Array K :=
  let tw := novelTwiddles m i
  Array.ofFn fun p : Fin (2 ^ m) ↦
    let t := tw.getD (p.val / 2 ^ (i + 1)) 0
    if p.val.testBit i then
      b.getD (p.val - 2 ^ i) 0 + b.getD p.val 0
    else
      b.getD p.val 0 + t * (b.getD p.val 0 + b.getD (p.val + 2 ^ i) 0)

/-- **The forward transform**: the `2^κ` novel-basis coefficients `c`, tiled `2^R` times, through
stages `κ − 1, …, 0`; entry `v` is `Σ_{j<2^κ} c_j·X_j(x_v)` for `v < 2^(κ+R)`, so the encoding of
a lane. -/
def novelFwd (κ R : ℕ) (c : Array K) : Array K :=
  (List.range κ).foldr (fun i b ↦ novelFwdStage (κ + R) i b)
    (Array.ofFn fun p : Fin (2 ^ (κ + R)) ↦ c.getD (p.val % 2 ^ κ) 0)

/-- **The inverse transform** on `U_κ`: the evaluations `y_v`, `v < 2^κ`, through stages
`0, …, κ − 1`, give the novel-basis coefficients. -/
def novelInv (κ : ℕ) (y : Array K) : Array K :=
  (List.range κ).foldl (fun b i ↦ novelInvStage κ i b) y

/-- **Monomial to novel basis**: the novel-basis coefficients of `p` (of degree `< 2^κ`), from its
evaluations on `U_κ`. -/
def toNovel (κ : ℕ) (p : CPolynomial K) : Array K :=
  novelInv κ (Array.ofFn fun v : Fin (2 ^ κ) ↦ p.eval (K.ofBits v.val))

end LeanVM.Extraction

/-! ### The facts the root finder needs (theorems only)

Shoup's trace context (`traceCtx`, §5) takes two proofs about `K = GF(2^64)`, its basis
`x^i = K.ofBits (2^i)`, `i < 64`, and the trace `Tr(z) = Σ_{i<64} z^(2^i)` (CompPoly's
`tracePowerSum 2 64`): `Tr(z) ∈ {0, 1}` (`tracePowerSum_mem_base`, as `Tr(z)^2 = Tr(z)`), and for
`a ≠ b` some basis element `β` with `Tr(β·(a − b)) ≠ 0` (`tracePowerSum_separates`: `β ↦ Tr(β·c)`
is additive, every element is a sum of basis elements, `ofBits_eq_sum`, and `Σ_{i<64} X^(2^i)`, of
degree at most `2^63`, cannot have `2^64` roots). With them, the facts about words they use:
`K.ofBits` is injective below `2^64`, turns `xor` into `+`, and the word with bits `v` is
`Σ_c v_c · x^c`. Every declaration of this section is a theorem: nothing in it changes what the
extractor computes, and a reviewer may skip it.

Credits: the obligations are those of `SmallPrimeTraceContext` and `tracePowerSum`
(`CompPoly/Univariate/Roots/Shoup/Basic.lean`, Valerii Huhnin), and `K` is `BF64`
(`CompPoly/Fields/Binary/BF64/Impl.lean`, Nicolas Schleicher), both from CompPoly
(github.com/Verified-zkEVM/CompPoly) at `572f997390aa4fc131ef30b1186fa1dcf292ca10`, Apache-2.0.
The word facts are adapted from `lean_vm/LeanVM/Protocol/Whir/Subspace.lean`. -/

namespace LeanVM.Extraction.Words

open LeanVM.Parameters


/-- `K.ofBits 0 = 0`. -/
theorem ofBits_zero : K.ofBits 0 = 0 := rfl

/-- A word below `2^64` is read back exactly. -/
theorem toNat_ofBits {n : ℕ} (hn : n < 2 ^ 64) : (K.ofBits n).toBitVec.toNat = n := by
  simpa [K.ofBits] using hn

/-- Every element is the word of its bits. -/
theorem ofBits_toNat (a : K) : K.ofBits a.toBitVec.toNat = a := by
  apply BF64.ext
  simp [K.ofBits]

/-- The bits of an element are below `2^64`. -/
theorem toNat_lt (a : K) : a.toBitVec.toNat < 2 ^ 64 := a.toBitVec.isLt

/-- Words below `2^64` are distinct field elements. -/
theorem ofBits_injOn : Set.InjOn K.ofBits {n | n < 2 ^ 64} := by
  intro a ha b hb h
  rw [← toNat_ofBits ha, ← toNat_ofBits hb, h]

/-- A word below `2^64` is zero only when it is `0`. -/
theorem ofBits_eq_zero_iff {n : ℕ} (hn : n < 2 ^ 64) : K.ofBits n = 0 ↔ n = 0 :=
  ⟨fun h ↦ ofBits_injOn (show n < 2 ^ 64 from hn) (show 0 < 2 ^ 64 by norm_num) h,
    fun h ↦ h ▸ ofBits_zero⟩

/-- Below `2^i`, adding `2^i` sets a bit that is clear: it is the exclusive or. -/
theorem two_pow_add_eq_xor {i v : ℕ} (hv : v < 2 ^ i) : 2 ^ i + v = 2 ^ i ^^^ v := by
  have h := Nat.two_pow_add_eq_or_of_lt hv 1
  rw [mul_one] at h
  rw [h]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hj : i = j
  · subst hj
    simp [Nat.testBit_lt_two_pow hv]
  · simp [hj]

/-- Sum in `K` is bitwise exclusive or of words. -/
theorem ofBits_xor (a b : ℕ) : K.ofBits (a ^^^ b) = K.ofBits a + K.ofBits b := by
  simp only [K.ofBits, BitVec.ofNat_xor]
  rfl

/-- `x_{2^i + v} = x^i + x_v` for `v < 2^i`. -/
theorem ofBits_two_pow_add {i v : ℕ} (hv : v < 2 ^ i) :
    K.ofBits (2 ^ i + v) = K.ofBits (2 ^ i) + K.ofBits v := by
  rw [two_pow_add_eq_xor hv, ofBits_xor]

/-- The word with bits `v` is `Σ_c v_c · x^c`. -/
theorem ofBits_eq_sum {i v : ℕ} (hv : v < 2 ^ i) :
    K.ofBits v = ∑ c ∈ Finset.range i, if v.testBit c then K.ofBits (2 ^ c) else 0 := by
  induction i generalizing v with
  | zero =>
    obtain rfl : v = 0 := by simpa using hv
    simp [ofBits_zero]
  | succ i ih =>
    rw [Finset.sum_range_succ]
    by_cases hb : v.testBit i
    · have hlt : v - 2 ^ i < 2 ^ i := by
        have := Nat.ge_two_pow_of_testBit hb
        rw [pow_succ] at hv
        omega
      have hv' : v = 2 ^ i + (v - 2 ^ i) := by
        have := Nat.ge_two_pow_of_testBit hb
        omega
      have hbits : ∀ c < i, v.testBit c = (v - 2 ^ i).testBit c := by
        intro c hc
        conv_lhs => rw [hv']
        exact Nat.testBit_two_pow_add_gt hc _
      have hb' : (2 ^ i + (v - 2 ^ i)).testBit i = true := by rw [← hv']; exact hb
      rw [hv', ofBits_two_pow_add hlt, ih hlt, hb']
      simp only [ite_true]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun c hc ↦ ?_
      rw [← hv', hbits c (Finset.mem_range.mp hc)]
    · have hlt : v < 2 ^ i := by
        by_contra h
        have h1 : 2 ^ i ≤ v := not_lt.mp h
        have : v.testBit i = true := by
          have hv2 : v - 2 ^ i < 2 ^ i := by rw [pow_succ] at hv; omega
          have := Nat.testBit_two_pow_add_eq (v - 2 ^ i) i
          rw [Nat.add_sub_cancel' h1, Nat.testBit_lt_two_pow hv2] at this
          simpa using this
        exact hb this
      simp only [Bool.not_eq_true] at hb
      rw [ih hlt, hb]
      simp

end LeanVM.Extraction.Words

namespace LeanVM.Extraction.Bf64Trace

open LeanVM.Parameters LeanVM.Extraction.Words Polynomial
open CompPoly.CPolynomial.Roots.FiniteField


/-- Frobenius fixes `K`: `a^(2^64) = a`. -/
theorem pow_two_pow_64 (a : K) : a ^ 2 ^ 64 = a := by
  let _ : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card a
  rwa [BF64.card_bf64] at h

/-- The trace as a sum. -/
theorem trace_eq_sum (z : K) : tracePowerSum 2 64 z = ∑ i ∈ Finset.range 64, z ^ 2 ^ i :=
  tracePowerSum_eq_sum_range 2 64 z

/-- The trace is additive. -/
theorem trace_add (a b : K) :
    tracePowerSum 2 64 (a + b) = tracePowerSum 2 64 a + tracePowerSum 2 64 b := by
  simp only [trace_eq_sum, add_pow_char_pow, Finset.sum_add_distrib]

/-- The trace of a finite sum. -/
theorem trace_sum {ι : Type*} (s : Finset ι) (f : ι → K) :
    tracePowerSum 2 64 (∑ i ∈ s, f i) = ∑ i ∈ s, tracePowerSum 2 64 (f i) :=
  map_sum (AddMonoidHom.mk' (tracePowerSum 2 64) trace_add) f s

/-- `Tr(z)^2 = Tr(z)`. -/
theorem trace_sq (z : K) : tracePowerSum 2 64 z ^ 2 = tracePowerSum 2 64 z := by
  rw [trace_eq_sum, sum_pow_char]
  have hshift : ∑ i ∈ Finset.range 64, (z ^ 2 ^ i) ^ 2 = ∑ i ∈ Finset.range 64, z ^ 2 ^ (i + 1) :=
    Finset.sum_congr rfl fun i _ ↦ by rw [← pow_mul, pow_succ]
  rw [hshift]
  have h := Finset.sum_range_succ' (fun i ↦ z ^ 2 ^ i) 64
  rw [Finset.sum_range_succ, pow_two_pow_64, pow_zero, pow_one] at h
  exact add_right_cancel h.symm

/-- **The trace lies in the base field** `{0, 1}`. -/
theorem tracePowerSum_mem_base (z : K) : tracePowerSum 2 64 z ∈ (#[0, 1] : Array K).toList := by
  have h := trace_sq z
  have h' : tracePowerSum 2 64 z * (tracePowerSum 2 64 z - 1) = 0 := by
    rw [mul_sub, mul_one, ← pow_two, h, sub_self]
  rcases mul_eq_zero.mp h' with h0 | h1
  · simp [h0]
  · simp [sub_eq_zero.mp h1]

/-- The trace polynomial `Σ_{i<64} X^(2^i)` evaluates to the trace. -/
theorem eval_tracePoly (z : K) :
    (∑ i ∈ Finset.range 64, (X : K[X]) ^ 2 ^ i).eval z = tracePowerSum 2 64 z := by
  simp [eval_finsetSum, trace_eq_sum]

/-- The trace polynomial is not zero: its coefficient of `X` is `1`. -/
theorem tracePoly_ne_zero : (∑ i ∈ Finset.range 64, (X : K[X]) ^ 2 ^ i) ≠ 0 := by
  intro h
  have h1 := congrArg (fun p : K[X] ↦ p.coeff 1) h
  simp only [finsetSum_coeff, coeff_X_pow, coeff_zero] at h1
  rw [Finset.sum_range_succ'] at h1
  have hrest : ∑ i ∈ Finset.range 63, (if 1 = 2 ^ (i + 1) then (1 : K) else 0) = 0 :=
    Finset.sum_eq_zero fun i _ ↦ by
      rw [ite_eq_right_iff]
      intro h1
      have : 2 ≤ 2 ^ (i + 1) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  rw [hrest] at h1
  simp at h1

/-- The trace polynomial has degree at most `2^63`. -/
theorem natDegree_tracePoly_le :
    (∑ i ∈ Finset.range 64, (X : K[X]) ^ 2 ^ i).natDegree ≤ 2 ^ 63 := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  rw [natDegree_X_pow]
  exact Nat.pow_le_pow_right (by norm_num) (by simpa [Nat.lt_succ_iff] using hi)

/-- The trace is not identically zero. -/
theorem exists_trace_ne_zero : ∃ z : K, tracePowerSum 2 64 z ≠ 0 := by
  by_contra! h
  let _ : Fintype K := Fintype.ofFinite K
  have hsub : (Finset.univ : Finset K).val ⊆
      (∑ i ∈ Finset.range 64, (X : K[X]) ^ 2 ^ i).roots := by
    intro z _
    rw [mem_roots tracePoly_ne_zero, IsRoot, eval_tracePoly, h z]
  have hcard := card_le_degree_of_subset_roots hsub
  rw [Finset.card_univ, BF64.card_bf64] at hcard
  have := hcard.trans natDegree_tracePoly_le
  norm_num at this

/-- **The trace separates** distinct elements on the basis `x^i`. -/
theorem tracePowerSum_separates {a b : K} (hab : a ≠ b) :
    ∃ beta, beta ∈ (Array.ofFn fun i : Fin 64 ↦ K.ofBits (2 ^ i.val)).toList ∧
      tracePowerSum 2 64 (beta * (a - b)) ≠ 0 := by
  have hc : a - b ≠ 0 := sub_ne_zero.mpr hab
  by_contra! h
  have hbasis : ∀ c < 64, tracePowerSum 2 64 (K.ofBits (2 ^ c) * (a - b)) = 0 := by
    intro c hc64
    refine h _ ?_
    rw [Array.mem_toList_iff, Array.mem_ofFn]
    exact ⟨⟨c, hc64⟩, Eq.refl (K.ofBits (2 ^ c))⟩
  have hall : ∀ y : K, tracePowerSum 2 64 (y * (a - b)) = 0 := by
    intro y
    rw [← ofBits_toNat y, ofBits_eq_sum (toNat_lt y), Finset.sum_mul, trace_sum]
    refine Finset.sum_eq_zero fun c hc64 ↦ ?_
    split
    · exact hbasis c (Finset.mem_range.mp hc64)
    · simp [trace_eq_sum]
  obtain ⟨z, hz⟩ := exists_trace_ne_zero
  apply hz
  have := hall (z * (a - b)⁻¹)
  rw [inv_mul_cancel_right₀ hc] at this
  exact this

end LeanVM.Extraction.Bf64Trace

namespace LeanVM.Extraction

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Parameters.Whir LeanVM.Protocol.KeccakHash
open CompPoly CompPoly.GuruswamiSudan CompPoly.CPolynomial.Roots.FiniteField

/-! ### 5. The list decoder of one lane

CompPoly's executable Guruswami–Sudan decoder over `K`, deterministic: Lee–O'Sullivan
interpolation, Roth–Ruckenstein roots, and the roots of a univariate polynomial as its `gcd` with
`X^(2^64) − X`, split by Shoup's trace splitter at `p = 2`, `k = 64` over the basis `x^i`, with
the trace `Tr(z) = Σ_{i<64} z^(2^i)`. A context's proof fields are theorems (CompPoly's, and the
two trace facts above); only its data is run. -/

/-- Shoup's trace context over `K`: `q = 2^64`, base constants `{0, 1}`, the basis `x^i`,
`i < 64`, and the trace `Σ_{i<64} z^(2^i)`. -/
def traceCtx : SmallPrimeTraceContext K where
  q := 2 ^ 64
  finite := inferInstance
  card_eq := BF64.nat_card_bf64
  frobenius_fixed := Bf64Trace.pow_two_pow_64
  p := 2
  k := 64
  p_prime := Nat.prime_two
  q_eq := rfl
  baseConstants := #[0, 1]
  baseConstants_size := rfl
  basis := Array.ofFn fun i : Fin 64 ↦ K.ofBits (2 ^ i.val)
  basis_size := Array.size_ofFn
  traceValue := tracePowerSum 2 64
  traceValue_eq_powerSum := fun _ ↦ rfl
  traceValue_mem_base := Bf64Trace.tracePowerSum_mem_base
  trace_separates := Bf64Trace.tracePowerSum_separates

/-- Deterministic univariate root finding over `K`. -/
def fieldRootCtx : FieldRootContext K :=
  finiteFieldRootContext K traceCtx.toFiniteFieldContext (shoupLinearFactorProductSplitter traceCtx)
    (fun hp ↦ finiteFieldRootProduct_shoupSplitterInput traceCtx hp)

/-- The list decoder's context: Lee–O'Sullivan interpolation and Roth–Ruckenstein roots. -/
def gsContext : GSFilteredCoreContext K :=
  filteredCoreContextOfInterpRootContexts
    (LeeOSullivan.leeOSullivanInterpContext CPolynomial.VanishingPolynomialContext.direct
      (CPolynomial.BatchEvalContext.horner K)
      (PolynomialMatrix.muldersStorjohannFastReducerContext K))
    (rothRuckensteinRootContext K fieldRootCtx)

/-- The number of unknowns of the interpolation, `#{(i, j) | i + (k−1)·j ≤ W}`, in closed form. -/
def gsNumVars (k W : ℕ) : ℕ := (W / (k - 1) + 1) * (2 * W + 2 - (k - 1) * (W / (k - 1))) / 2

/-- The number of interpolation conditions, `n·m(m+1)/2`. -/
def gsNumConstraints (n m : ℕ) : ℕ := n * (m * (m + 1) / 2)

/-- The parameter check at message length `k`, `n` points and radius `e`: more unknowns than
conditions, and a weighted degree below `m` times the agreement. -/
def gsPass (k n e : ℕ) (params : GSExecParams) : Bool :=
  decide (params.interp.messageDegree = k) && decide (params.radius = e) &&
    decide (0 < params.interp.multiplicity) &&
    decide (gsNumConstraints n params.interp.multiplicity <
      gsNumVars k params.interp.weightedDegreeBound) &&
    decide (params.interp.weightedDegreeBound < params.interp.multiplicity * (n - e))

/-- The parameters at multiplicity `m` for message length `k`, `n` points and agreement `A`:
weighted degree `W = m·A − 1`, radius `n − A`. -/
def gsParamsAt (k n A m : ℕ) : GSExecParams :=
  { interp := { messageDegree := k, multiplicity := m, weightedDegreeBound := m * A - 1 }
    radius := n - A }

/-- A multiplicity that passes the check whenever `A² > (k − 1)·n`:
`⌊((k−1)·n + 1)/(A² − (k−1)·n)⌋ + 1`. -/
def gsMultiplicityBoundAt (k n A : ℕ) : ℕ := ((k - 1) * n + 1) / (A * A - (k - 1) * n) + 1

/-- The least multiplicity, up to `gsMultiplicityBoundAt`, that passes the check. -/
def gsMultiplicityAt (k n A : ℕ) : ℕ :=
  ((List.range' 1 (gsMultiplicityBoundAt k n A)).find?
    fun m ↦ gsPass k n (n - A) (gsParamsAt k n A m)).getD (gsMultiplicityBoundAt k n A)

/-- The decoder's parameters for message length `k`, `n` points and agreement `A`. -/
def gsParamsFor (k n A : ℕ) : GSExecParams := gsParamsAt k n A (gsMultiplicityAt k n A)

/-- The symbol of lane `u` at column `v` of a word: the leaf's word `63 − u`, as `agreement`
reads it. -/
def laneSymbol (W : ℕ → List K) (u v : ℕ) : K := (W v).reverse.getD u 0

/-- The decoder's input for lane `u` on `n` columns: the pairs `(x_v, W_u(v))`, `v < n`. -/
def lanePoints (n : ℕ) (W : ℕ → List K) (u : ℕ) : Array (K × K) :=
  Array.ofFn fun v : Fin n ↦ (K.ofBits v.val, laneSymbol W u v.val)

/-- **The lane decoder**: Guruswami–Sudan over `K` on lane `u` of `W`, for messages of `2^κ`
coefficients on `2^(κ+R)` columns, at agreement `A`: every polynomial of degree `< 2^κ` that
agrees with the lane on at least `A` columns (when `A² > (2^κ − 1)·2^(κ+R)`). -/
def gsLaneAt (κ R A : ℕ) (W : ℕ → List K) (u : ℕ) : Array (CPolynomial K) :=
  GuruswamiSudan.decodeWithParams gsContext (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A)
    ⟨lanePoints (2 ^ (κ + R)) W u⟩

/-- Lexicographic order on lists of natural numbers. -/
def lexLE : List ℕ → List ℕ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => decide (a < b) || (decide (a = b) && lexLE as bs)

/-- The lane lists' order: lexicographic on the coefficients' 64-bit lanes. -/
def coeffsLE (a b : Array K) : Bool :=
  lexLE (a.toList.map fun x ↦ x.lane.toNat) (b.toList.map fun x ↦ x.lane.toNat)

/-- The lane decoder's list as novel-basis coefficients, without duplicates, in increasing order
(`coeffsLE`): it depends only on the set of polynomials the decoder returns, not on their
order. -/
def laneListAt (κ R A : ℕ) (W : ℕ → List K) (u : ℕ) : List (Array K) :=
  (((gsLaneAt κ R A W u).toList.map (toNovel κ)).dedup).mergeSort coeffsLE

/-! ### 6. The 64 lanes: prefix pruning -/

/-- One lane: extend every survivor `(cs, S)` (the coefficients of the lanes so far, and the
columns, in increasing order, where all of them agree with the word) by every `(c, e)` of the
lane's list, `e` the encoding of `c`, keeping the columns of `S` at which `e` agrees with the
lane's symbols `sym`; keep the extension if at least `A` columns remain. -/
def pruneStep (A : ℕ) (sym : ℕ → K) (L : List (Array K × Array K))
    (st : List (List (Array K) × List ℕ)) : List (List (Array K) × List ℕ) :=
  st.flatMap fun s ↦ L.filterMap fun ce ↦
    let S' := s.2.filter fun v ↦ decide (ce.2.getD v 0 = sym v)
    if A ≤ S'.length then some (s.1 ++ [ce.1], S') else none

/-- Lane `u`'s list with each element's encoding on the `2^(κ+R)` columns. -/
def laneEncodedAt (κ R A : ℕ) (W : ℕ → List K) (u : ℕ) : List (Array K × Array K) :=
  (laneListAt κ R A W u).map fun c ↦ (c, novelFwd κ R c)

/-- The survivors after lanes `0, …, U − 1`; a lane is decoded only while survivors remain. -/
def pruneUpTo (κ R A : ℕ) (W : ℕ → List K) (U : ℕ) : List (List (Array K) × List ℕ) :=
  (List.range U).foldl
    (fun st u ↦
      if st.isEmpty then [] else pruneStep A (laneSymbol W u) (laneEncodedAt κ R A W u) st)
    [([], List.range (2 ^ (κ + R)))]

/-- The stack of `2^μ` words whose lane `u` is `cs[u]`: cell `i` is entry `i mod 2^κ` of lane
`⌊i / 2^κ⌋`, `κ = μ − 6`. -/
def stackOf (μ : ℕ) (cs : List (Array K)) : Vector K (2 ^ μ) :=
  Vector.ofFn fun i ↦
    (cs.getD (i.val / 2 ^ (μ - initialFold)) #[]).getD (i.val % 2 ^ (μ - initialFold)) 0

/-- The decoded stacks at agreement `A`: the survivors of all `2^6` lanes, as stacks. -/
def decodeStacksAt (μ R A : ℕ) (W : ℕ → List K) : List (Vector K (2 ^ μ)) :=
  (pruneUpTo (μ - initialFold) R A W (2 ^ initialFold)).map fun s ↦ stackOf μ s.1

/-- **The decoded stacks** of a committed word: every candidate at the Johnson threshold. -/
def decodeStacks (μ R : ℕ) (W : ℕ → List K) : List (Vector K (2 ^ μ)) :=
  decodeStacksAt μ R (johnsonThreshold μ R) W

/-- **The fast path**, for a word without errors: the same pruning, with lane `u`'s list the one
array interpolated from its first `2^κ` columns (`novelInv`). At most one stack, a candidate,
for `2^6` inverse and forward transforms. -/
def fastStacks (μ R : ℕ) (W : ℕ → List K) : List (Vector K (2 ^ μ)) :=
  let κ := μ - initialFold
  let st := (List.range (2 ^ initialFold)).foldl
    (fun st u ↦
      let c := novelInv κ (Array.ofFn fun v : Fin (2 ^ κ) ↦ laneSymbol W u v.val)
      pruneStep (johnsonThreshold μ R) (laneSymbol W u) [(c, novelFwd κ R c)] st)
    [([], List.range (2 ^ (κ + R)))]
  st.map fun s ↦ stackOf μ s.1

/-! ### 7. The execution -/

/-- **The memory image of a stack**: `2^logMemory` words, word `i` the two limbs at cell `i` of
the memory columns `MEMORY_0`, `MEMORY_1` (`layout.rs`), each at its placement's offset on the
stack. -/
def memoryImage (layout : Layout) {μ : ℕ} (q : Vector K (2 ^ μ)) : MemoryImage layout.logMemory :=
  fun i ↦
    let limb (column : ℕ) : K := q.getD ((layout.placement column).index + i) 0
    E.ofLimbs (limb memory0) (limb memory1)

/-- One step (`step`, computed) with the memory index `memIdx` and the bytecode index `codeIdx`:
fetch the instruction at `pc`, then execute it (`executeWith`), reading the memory through
`memIdx`. -/
def stepIn (memIdx codeIdx : Std.HashMap UInt64 ℕ) (prog : LeanIsaProgram) {κ : ℕ}
    (L : MemoryImage κ) (r : Registers K) : Option (Registers K) :=
  (gLogIn codeIdx prog.logSize r.pc).map prog.instructions >>=
    executeWith (fun a ↦ (gLogIn memIdx κ a).map L) r

/-- The halting search from `r`, reached after `n` steps, with at most `fuel` more steps: `some m`
when the run is in the final state after `m` steps in all; `none` if a step fails or the fuel runs
out first. -/
def haltLoop (memIdx codeIdx : Std.HashMap UInt64 ℕ) (prog : LeanIsaProgram) {κ : ℕ}
    (L : MemoryImage κ) : ℕ → ℕ → Registers K → Option ℕ
  | 0, n, r => if r = Registers.final prog then some n else none
  | fuel + 1, n, r =>
    if r = Registers.final prog then some n
    else
      match stepIn memIdx codeIdx prog L r with
      | none => none
      | some r' => haltLoop memIdx codeIdx prog L fuel (n + 1) r'

/-- The image, run from the initial state `(pcInitial, fpInitial)` for the least number `n ≤ cap`
of steps after which it is in the final state `(pcFinal, fpFinal)`, if any. -/
def haltingRunIn (memIdx codeIdx : Std.HashMap UInt64 ℕ) (prog : LeanIsaProgram) {κ : ℕ}
    (image : MemoryImage κ) (cap : ℕ) : Option (Execution prog) :=
  (haltLoop memIdx codeIdx prog image cap 0 Registers.initial).map fun n ↦ ⟨κ, image, n⟩

/-- **The step cap of a layout**: the rows its tables hold, `2^τ_j` for each opcode table's
log-height `τ_j`, the `2^logMemory` words of the memory and the `2^logBytecode` slots of the
bytecode. -/
def stepCap (layout : Layout) : ℕ :=
  (layout.tableLogHeights.map (2 ^ ·)).sum + 2 ^ layout.logMemory + 2 ^ layout.logBytecode

/-- **The execution of a stack**: the halting run of its memory image within the layout's step
cap, if it has the public boundary of `input`; `memIdx` and `codeIdx` index the memory's and the
bytecode's addresses. -/
def candidateExecutionIn (memIdx codeIdx : Std.HashMap UInt64 ℕ) (prog : LeanIsaProgram)
    (input : PublicInput) (layout : Layout) {μ : ℕ} (q : Vector K (2 ^ μ)) :
      Option (Execution prog) :=
  (haltingRunIn memIdx codeIdx prog (memoryImage layout q) (stepCap layout)).filter
    (boundaryOK input)

/-! ### 8. The extractor -/

/-- **The extractor.** From the adversary's answers and the keys they answer (byte strings
`answers` is `none` outside of), and the proof, with the bytecode's words as the verifier reads
them: the announced layout, rate exponent and stack root (`afterRoot`), the word the root commits
to (`committedLeaves`), and the execution of the first decoded stack (the fast path's, then the
list decoder's) that has one; `none` otherwise. The leaves and the two address indices are
computed once, for every stack. -/
def extract (prog : LeanIsaProgram) (input : PublicInput) (bytecode : List K)
    (answers : Bytes → Option Digest) (keys : List Bytes) (π : Proof) : Option (Execution prog) :=
      do
  let ((layout, logInverseRate), state) ← afterRoot bytecode π
  let (root, height, width) ← state.roots.head?
  let leaves := committedLeaves answers keys root height width
  let word := leafAt leaves height width
  let memIdx := powIndex layout.logMemory
  let codeIdx := powIndex prog.logSize
  let execution := candidateExecutionIn memIdx codeIdx prog input layout
  (fastStacks layout.stackLog logInverseRate word).findSome? execution <|>
    (decodeStacks layout.stackLog logInverseRate word).findSome? execution

end LeanVM.Extraction

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open Common

/-! ## The transcript's extractor -/

/-- The bytes Keccak-256 absorbs for the message `m`: its whole blocks of `136` bytes, then the
padded last block (`padBlock`, as `keccak256With` absorbs them). -/
def keccakPadded (m : Bytes) : Bytes :=
  m.take (rate * (m.length / rate)) ++ padBlock (m.drop (rate * (m.length / rate)))

/-- The message whose padding is `bs`, if any: the prefix of `bs` short of `1` to `136` bytes
that pads to `bs` (there is at most one). -/
def keccakUnpadded (bs : Bytes) : Option Bytes :=
  ((List.range rate).map fun k ↦ bs.take (bs.length - 1 - k)).find? (keccakPadded · = bs)

/-- The extractor's bookkeeping of a transcript: the edges `(x, π x)` fixed so far, newest first,
and the states that a chain of forward queries reaches from the zero state, each with the bytes
its path absorbed, newest first. -/
structure TranscriptReplay where
  /-- The edges `(x, π x)` fixed so far, newest first. -/
  edges : PermutationEdges KeccakState
  /-- The states reached from the zero state, with the bytes their paths absorbed. -/
  spongePaths : List (KeccakState × Bytes)

/-- One query and its answer. A forward query `π x` that fixes a new edge extends the chain of a
state `s` with the capacity of `x` (lanes `17 … 24`), if there is one, by the block that takes
`s` to `x`: the bytes of their rates' XOR, lanes `0 … 16`. An inverse query extends no chain. -/
def TranscriptReplay.step (σ : TranscriptReplay) :
    PermutationQuery KeccakState × KeccakState → TranscriptReplay
  | (.forward x, y) =>
    match Common.forwardLookup σ.edges x with
    | some _ => σ
    | none =>
      match σ.spongePaths.find? (fun p ↦ p.1.toList.drop 17 = x.toList.drop 17) with
      | some (s, bs) =>
        ⟨(x, y) :: σ.edges, (y, bs ++ (List.range 17).flatMap fun i ↦
          wordBytes (Keccak.lane s i ^^^ Keccak.lane x i)) :: σ.spongePaths⟩
      | none => ⟨(x, y) :: σ.edges, σ.spongePaths⟩
  | (.inverse y, x) =>
    match Common.inverseLookup σ.edges y with
    | some _ => σ
    | none => ⟨(x, y) :: σ.edges, σ.spongePaths⟩

/-- **The Keccak-256 evaluations a transcript holds**: the byte strings whose whole padded sponge
path the transcript (oldest first) holds as a chain of forward queries from the zero state, each
query absorbing the next block into the answer of the one before and each the query that first
fixed its edge (an edge first fixed by an inverse query extends no path), with the first four lanes
of the path's last answer. -/
def keccakEvaluationsOfTranscript (T : List (PermutationQuery KeccakState × KeccakState)) :
    List (Bytes × Digest) :=
  (T.foldl TranscriptReplay.step ⟨[], [(Vector.replicate 25 0, [])]⟩).spongePaths.filterMap fun p ↦
    (keccakUnpadded p.2).map fun m ↦ (m, #v[p.1[0], p.1[1], p.1[2], p.1[3]])

/-- The Keccak-256 evaluation of `x` among the paths `P`, if `P` holds one. -/
def lookupEvaluation (P : List (Bytes × Digest)) (x : Bytes) : Option Digest :=
  (P.find? (·.1 = x)).map (·.2)

/-- **The extractor in the random-permutation model**: from the statement, the adversary's
transcript and the proof, an execution of the program: the extractor of `Extractor.lean`
(`LeanVM.Extraction.extract`) on the Keccak-256 evaluations of the transcript's permutation queries
(`lookupEvaluation (keccakEvaluationsOfTranscript (permutationQueries T))`), the byte strings they
answer being those of the transcript's paths. The paths are computed once. -/
def transcriptExtractor (prog : LeanIsaProgram) (input : PublicInput) (T : OracleQueryLog)
    (proof : Proof) : Option (Execution prog) :=
  let paths := keccakEvaluationsOfTranscript (permutationQueries T)
  Extraction.extract prog input (bytecodeWords prog) (lookupEvaluation paths)
    (paths.map (·.1)) proof

end LeanVM

end
