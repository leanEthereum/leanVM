module

import Statement.LeanVm
import LeanVM.Protocol.Compile.RunPure
public import CompPoly.Univariate.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.FieldTheory.Finite.Basic
public import Statement.RandomPermutation
public import Statement.Prover.Witness

/-!
# The knowledge extractor's pieces

The pieces of the straight-line extractor the agreement-set extractor (`Extraction/AS/Lite.lean`,
`LeanVM.transcriptExtractor`, `Cost/AS/End.lean`) is built from and proved against. They read
the statement (the program, its bytecode and the public input), the proof and the Keccak-256
evaluations of the adversary's transcript, and nothing else; every definition is computable and
deterministic.

1. **The announced sizes and the stack's root** (`afterRoot`): read off the proof as the
   verifier's steps 1 and 2 read them (`crates/verifier/src/lib.rs`), with every hash and
   permutation answered by a constant (`runPure`): what they read does not depend on the sponge.
2. **A committed word** (`committedLeaves`, `leafAt`): the Merkle tree under a root inverted
   through the evaluations, top down: a node's children are the two digests its unique answered
   64-byte preimage holds, a leaf the words of its unique answered preimage; an unanswered node
   gives zero leaves.
3. **The subspace polynomials** (`subspacePoly`).
4. **Novel-basis coefficients from evaluations** (`novelInv`): the inverse additive NTT of
   Annex D (`doc/leanvm/body/d-novel-basis.tex`); `stackOf`, the stack of `2^μ` words of `64`
   lanes' low parts.
5. **The execution** (`candidateExecutionIn`): a stack's memory image run from the initial state
   for at most as many steps as the announced tables have rows (`stepCap`; a halting run never
   repeats a state and each of its steps takes a row of its own, so a valid execution a stack
   represents halts within the cap, proved), kept if it halts with the public input at its
   boundary.
6. **The transcript's evaluations** (`keccakEvaluationsOfTranscript`, `lookupEvaluation`): the
   byte strings whose whole padded sponge path the transcript holds as a chain of forward queries.

**Where it was.** These pieces were the trusted statement's (`Statement/Extractor.lean`,
`Statement/LeanVm.lean`) until the end statement took the extractor as a cost-machine program
within a size bound and a budget (`LeanVM.extractorComputedBy`, `Statement/CostMachine.lean`):
moved here verbatim, but for the address indices and the public boundary (`powIndex`, `gLogIn`,
`boundaryOK`, `Statement/Prover/Witness.lean`), which the statement keeps for the honest prover.

**Credits.** `K` is CompPoly's `BF64` (github.com/Verified-zkEVM/CompPoly at
`572f997390aa4fc131ef30b1186fa1dcf292ca10`, Apache-2.0, Nicolas Schleicher). The inverse
novel-basis transform is the inverse additive NTT of Lin, Chung and Han (FOCS 2014), as in
Diamond and Posen, *Polylogarithmic proofs for multilinears over binary towers* (2024),
Algorithm 2, in the point order of CompPoly's `AdditiveNTT` (Chung Thai Nguyen and Quang Dao); no
code of it is copied.
-/

@[expose] public section

namespace LeanVM.Extraction

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Parameters.Whir LeanVM.Protocol.KeccakHash
open CompPoly

/-! ### 1. The announced sizes and the stack's root -/

/-- `verify_execution`'s steps 1 and 2 (`lib.rs`): read the announced sizes, then
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

/-! ### 3. The subspace polynomials -/

/-- The subspace polynomial `W_i(a) = ∏_{v < 2^i} (a + x_v)`, `x_v = K.ofBits v`: it vanishes
exactly on `U_i = {x_v | v < 2^i}`. -/
def subspacePoly (i : ℕ) (a : K) : K := ∏ v ∈ Finset.range (2 ^ i), (a + K.ofBits v)

/-! ### 4. Novel-basis coefficients from evaluations

The inverse additive NTT in the novel basis `X_j(a) = ∏_{i < 64, bit i of j} Ŵ_i(a)`, `Ŵ_i` the
normalized subspace polynomial `W_i(a) / W_i(x_{2^i})`, on the points `x_v`. Stage `i` pairs the
positions `p` and `p + 2^i` (bit `i` of `p` clear) with the twiddle
`t = Ŵ_i(x_{⌊p/2^(i+1)⌋·2^(i+1)})` and maps `(lo, hi)` to `(lo + t·(lo + hi), lo + hi)`. -/

/-- Stage `i`'s twiddles over a buffer of `2^m`: entry `w` is `Ŵ_i(x_{w·2^(i+1)})`. -/
def novelTwiddles (m i : ℕ) : Array K :=
  let nrm := (subspacePoly i (K.ofBits (2 ^ i)))⁻¹
  Array.ofFn fun w : Fin (2 ^ (m - (i + 1))) ↦ subspacePoly i (K.ofBits (w.val * 2 ^ (i + 1))) * nrm

/-- The inverse butterfly stage `i` over a buffer of `2^m`. -/
def novelInvStage (m i : ℕ) (b : Array K) : Array K :=
  let tw := novelTwiddles m i
  Array.ofFn fun p : Fin (2 ^ m) ↦
    let t := tw.getD (p.val / 2 ^ (i + 1)) 0
    if p.val.testBit i then
      b.getD (p.val - 2 ^ i) 0 + b.getD p.val 0
    else
      b.getD p.val 0 + t * (b.getD p.val 0 + b.getD (p.val + 2 ^ i) 0)

/-- **The inverse transform** on `U_κ`: the evaluations `y_v`, `v < 2^κ`, through stages
`0, …, κ − 1`, give the novel-basis coefficients. -/
def novelInv (κ : ℕ) (y : Array K) : Array K :=
  (List.range κ).foldl (fun b i ↦ novelInvStage κ i b) y

end LeanVM.Extraction

/-! ### Facts about words (theorems only)

`K.ofBits` is injective below `2^64`, turns `xor` into `+`, and the word with bits `v` is
`Σ_c v_c · x^c`. Every declaration of this section is a theorem: nothing in it changes what the
extractor computes. Adapted from `lean_vm/LeanVM/Protocol/Whir/Subspace.lean`. -/

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


namespace LeanVM.Extraction

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Parameters.Whir LeanVM.Protocol.KeccakHash
open CompPoly

/-- The stack of `2^μ` words whose lane `u` is `cs[u]`: cell `i` is entry `i mod 2^κ` of lane
`⌊i / 2^κ⌋`, `κ = μ − 6` (of a decoded lane's `2^(κ+1)` coefficients, its low part). -/
def stackOf (μ : ℕ) (cs : List (Array K)) : Vector K (2 ^ μ) :=
  Vector.ofFn fun i ↦
    (cs.getD (i.val / 2 ^ (μ - initialFold)) #[]).getD (i.val % 2 ^ (μ - initialFold)) 0

/-! ### 5. The execution -/

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

end LeanVM

end
