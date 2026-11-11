/-
  LeanVM.Protocol.Extraction.Defs

  The extractor's reference definitions, proof side: what the computable extractor of
  `LeanVM/Protocol/Extraction/Extractor.lean` is proved against (the committed word as a classical choice over
  openings, the halting run as a least number of steps) and the per-call forms of its pieces.
-/

module

public import LeanVM.Protocol.Extraction.Extractor
public import LeanVM.Protocol.WithHash

/-!
# Reference definitions for the extractor

The knowledge extractor (`LeanVM.Extraction.extract`, `Extraction/Extractor.lean`) is computable.
Its proofs compare it with these definitions, which are not computable or not efficient, and are
not part of the statement:

* `committedWord`: leaf `v` of the word a Merkle root commits to under `answers` is the leaf of an
  opening at position `v` that `openOne` accepts, if there is one (a classical choice), and zeros
  otherwise; `committedWordC` is the extractor's computed word as a function
  (`leafAt (committedLeaves …)`), equal to it without collisions (`MerkleProofs.committedWordC_eq`);
* `haltingRun`: the run of a memory image for the least number of steps after which it is in the
  final state (`Nat.find`); `haltingRunC` is the extractor's capped search with fresh indices,
  equal to it when the cap is large enough (`Halting.haltingRunC_eq_haltingRun`);
* `gLogC`, `stepC`, `runC`, `candidateExecution`: the address lookup, step, run and a stack's
  execution with indices built per call (`addressIndex?`, `step`, `run` for `κ < 64`);
* `laneCoeffs`: lane `u` of a stack, the coefficients `encode q u` evaluates;
* `gsParams`, `gsMultiplicity`: the lane decoder's parameters at a shape.

These were the statement's own definitions before the extractor became computable
(`committedWord`, `haltingRun`: `Statement/Extractor.lean` at `8e8e4d2f`, verbatim), or the
specification-level forms of the extractor's pieces.
-/

namespace LeanVM.Extraction

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Parameters.Whir

@[expose] public section

/-! ## The code and the candidates (moved here from `Statement/Extractor.lean`, names kept) -/

/-- The normalized subspace polynomial `Ŵ_i(a) = W_i(a) / W_i(x_{2^i})`. -/
def normSubspacePoly (i : ℕ) (a : K) : K :=
  subspacePoly i a * (subspacePoly i (K.ofBits (2 ^ i)))⁻¹

/-- The novel basis polynomial `X_j(a) = ∏_{i < 64, bit i of j} Ŵ_i(a)`. -/
def novelBasis (j : ℕ) (a : K) : K :=
  ∏ i ∈ Finset.range 64, if j.testBit i then normSubspacePoly i a else 1

/-- **The encoding of a stack** of `2^μ` words, at lane `u` and column `v`: with `κ = μ − 6`,
lane `u` is the message of the `2^κ` cells `j + 2^κ·u`, `j < 2^κ`, as coefficients of the novel
basis, evaluated at the domain point `x_v`: `Σ_j q[j + 2^κ·u] · X_j(x_v)`. -/
def encode {μ : ℕ} (q : Vector K (2 ^ μ)) (u v : ℕ) : K :=
  ∑ j ∈ Finset.range (2 ^ (μ - initialFold)),
    q.getD (j + 2 ^ (μ - initialFold) * u) 0 * novelBasis j (K.ofBits v)

/-- The columns, among the `2^(μ − 6 + R)` of the code at rate `2^-R`, at which the word `W`
agrees with the encoding of `q` on every lane, a leaf holding lane `u` at word `63 − u`. -/
def agreement {μ : ℕ} (R : ℕ) (W : ℕ → List K) (q : Vector K (2 ^ μ)) : Finset ℕ :=
  (Finset.range (2 ^ (μ - initialFold + R))).filter fun v ↦
    ∀ u : Fin (2 ^ initialFold), (W v).reverse.getD u 0 = encode q u v

/-- The columns at which the word `W` agrees, on every lane `u`, with the level-0 polynomial of
low part lane `u` of `q` and high part `W_κ·H_u`: `encode q u v + W_κ(x_v)·H_u(x_v)`. -/
def agreementWith {μ : ℕ} (R : ℕ) (W : ℕ → List K) (q : Vector K (2 ^ μ))
    (H : Fin (2 ^ initialFold) → Polynomial K) : Finset ℕ :=
  (Finset.range (2 ^ (μ - initialFold + R))).filter fun v ↦
    ∀ u : Fin (2 ^ initialFold), (W v).reverse.getD u 0 =
      encode q u v + subspacePoly (μ - initialFold) (K.ofBits v) * (H u).eval (K.ofBits v)

/-- **The candidates** of a committed word: the stacks of `2^μ` words such that, for some high
parts `H_u` of degree below `6`, the lanes `encode q u + W_κ·H_u` (`κ = μ − 6`; polynomials of
degree at most `2^κ + 5` whose low part, their novel coefficients below `2^κ`, is lane `u` of
`q`) agree with the word on at least `A` columns: the low parts of level 0's list at its
degree `2^κ − 1 + 6`, which WHIR's soundness quantifies over. The extractor must list every one of
them at the Johnson threshold (`decodeStacks`). With `H = 0` a stack whose encoding agrees with
the word is one (`agreement`). -/
def Candidates (μ R A : ℕ) (W : ℕ → List K) : Set (Vector K (2 ^ μ)) :=
  {q | ∃ H : Fin (2 ^ initialFold) → Polynomial K, (∀ u, (H u).degree < initialFold) ∧
    A ≤ (agreementWith R W q H).card}

/-! ## The committed word -/

open Classical in
/-- The word a Merkle root of `2^height` leaves of `width` words commits to under `answers`:
leaf `v` is the leaf of an opening at position `v` that `openOne` accepts against the root, the
hash being `answers` (its climb reaches the root through answered queries), if there is one (a
classical choice), and `width` zeros otherwise. -/
noncomputable def committedWord (answers : Bytes → Option Digest) (root : Digest)
    (height width : ℕ) : ℕ → List K := fun v ↦
  if h : ∃ o : Opening, openOneWithHash answers root height width v o = some true then h.choose.leaf
  else List.replicate width 0

/-- **The committed word, computed**, as a function of the position: leaf `v mod 2^height` of
`committedLeaves`. (Compiled, it would rebuild the leaves at every position; the extractor binds
`committedLeaves` once and reads it with `leafAt`, which is this by `rfl`.) -/
def committedWordC (answers : Bytes → Option Digest) (keys : List Bytes) (root : Digest)
    (height width : ℕ) : ℕ → List K :=
  leafAt (committedLeaves answers keys root height width) height width

open Classical in
/-- The byte strings `answers` answers, when they are finitely many (a classical enumeration);
`[]` otherwise. The keys the random-oracle model's extractor is given (`LeanVM.extractor`). -/
noncomputable def supportKeys (answers : Bytes → Option Digest) : List Bytes :=
  if h : {x | answers x ≠ none}.Finite then h.toFinset.toList else []

/-! ## The halting run -/

open Classical in
/-- The execution of `prog` on a memory image: the image, run from the initial state
`(pcInitial, fpInitial)` for the least number of steps after which it halts in the final state
`(pcFinal, fpFinal)`; `none` if it never does. -/
noncomputable def haltingRun (prog : LeanIsaProgram) {κ : ℕ} (image : MemoryImage κ) : Option (Execution prog) :=
  if h : ∃ n, Semantics.run prog image n Registers.initial = some (Registers.final prog) then
    some ⟨κ, image, Nat.find h⟩
  else none

/-- **The index of an address**, computably: `gLogIn` in a fresh `powIndex κ`. It is `addressIndex?` when
`κ < 64`. -/
def gLogC (κ : ℕ) (a : K) : Option (Fin (2 ^ κ)) := gLogIn (powIndex κ) κ a

/-- One step, computably: `stepIn` with fresh indices. It is `step` when `κ < 64`. -/
def stepC (prog : LeanIsaProgram) {κ : ℕ} (L : MemoryImage κ) (r : Registers K) : Option
    (Registers K) :=
  stepIn (powIndex κ) (powIndex prog.logSize) prog L r

/-- `n` steps from `r`, halting in the final state, computably: `run` with `stepC`. It is `run`
when `κ < 64`. -/
def runC {κ : ℕ} (prog : LeanIsaProgram) (L : MemoryImage κ) : ℕ → Registers K → Option
    (Registers K)
  | 0, r => some r
  | n + 1, r => if r = Registers.final prog then none else stepC prog L r >>= runC prog L n

/-- **The capped halting run**, with the indices built per search. -/
def haltingRunC (prog : LeanIsaProgram) {κ : ℕ} (image : MemoryImage κ) (cap : ℕ) : Option (Execution prog) :=
  haltingRunIn (powIndex κ) (powIndex prog.logSize) prog image cap

/-- **The execution of a candidate**, with the indices built per call. -/
def candidateExecution (prog : LeanIsaProgram) (input : PublicInput) (layout : Layout) {μ : ℕ}
    (q : Vector K (2 ^ μ)) : Option (Execution prog) :=
  candidateExecutionIn (powIndex layout.logMemory) (powIndex prog.logSize) prog input layout q

/-! ## Lanes and the decoder's parameters -/

/-- Lane `u` of a stack of `2^μ` words: its `2^κ` cells `j + 2^κ·u`, `κ = μ − 6`, the novel-basis
coefficients that `encode q u` evaluates. -/
def laneCoeffs {μ : ℕ} (q : Vector K (2 ^ μ)) (u : ℕ) : Array K :=
  Array.ofFn fun j : Fin (2 ^ (μ - initialFold)) ↦ q.getD (j.val + 2 ^ (μ - initialFold) * u) 0

/-- **The per-lane decoder's parameters** for a stack of `2^μ` words at rate `2^-R`:
message length `k = 2^κ`, `n = 2^(κ+R)` points, agreement `A = johnsonThreshold μ R`. -/
def gsParams (μ R : ℕ) : CompPoly.GuruswamiSudan.GSExecParams :=
  gsParamsFor (2 ^ (μ - initialFold)) (2 ^ (μ - initialFold + R)) (johnsonThreshold μ R)

/-- The multiplicity of `gsParams μ R`. -/
def gsMultiplicity (μ R : ℕ) : ℕ := (gsParams μ R).interp.multiplicity

end
end LeanVM.Extraction
