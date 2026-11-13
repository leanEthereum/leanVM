/-
  LeanVM.Protocol.EndToEnd.Candidates

  The stacks a level-0 commitment binds: those whose encoding agrees with the committed word on
  enough columns. The object the front phases' doom and WHIR's starting relation quantify over,
  and from which the knowledge extractor picks.
-/

module

public import LeanVM.Protocol.Whir.NovelBasis
public import LeanVM.Protocol.Compile.Prog

/-!
# The candidates of a commitment

The deployed commitment (`verify_execution` step 2 and `verify_whir` level 0,
`crates/verifier/src/lib.rs:235-237` and `whir.rs:185-211` at leanVM `40f877dc`) is a Merkle
root of a word of `2^(μ − 6 + R)` columns, each a leaf of `64` words of `K`. The
leaf stores the lanes of its column in reverse order (`row.reverse`): lane `u` of column `v` is
word `63 − u` of leaf `v` (`laneOf`). Lane `u` of an honest word is the encoding (`enc`, the
novel-basis Reed-Solomon code) of the stack's block `u`: the `2^(μ−6)` consecutive cells at offset
`u · 2^(μ−6)`, so that the stack's coordinates are the message's `μ − 6` low bits and the lane's
six high bits (`blockOf`, Annex B "Optimizations", `f(u, x) = q(x, u)`).

Level 0's fold rounds are analysed at its final degree `2^κ − 1 + 6` (`κ = μ − 6`), so the list
the opening starts on holds lane polynomials of that degree: block `u` of a stack in the low part
(the novel-basis coefficients below `2^κ`) and a free high part, `W_κ·H_u` with
`deg H_u < 6`, `W_κ` the subspace polynomial (Annex B, `thm:rbr`). The claims weigh only the low
part. `Agrees μ R W q S` says that for some high parts `H` the lanes `enc(block u) + W_κ·H_u`
agree with the word `W` on every lane at every column of `S` (`H = 0`: the stack's encoding).
`Candidates μ R A W` are the stacks that agree so with `W` on at least `A` columns: with
`A = ⌈(√ρ₋ + η)·n⌉`, the low parts of the Johnson list at radius `1 − √ρ₋ − η` and degree
`2^κ + 5`. The front phases' doom (no candidate is in their state function) and WHIR's starting
relation (every candidate violates a pooled claim) quantify over them; the knowledge extractor
returns the candidate satisfying the relation when there is one.

Candidates are `K`-valued stacks by type, with `K`-polynomial high parts: a polynomial over `E` of
degree below the threshold that agrees with a `K`-valued word is over `K` (WHIR's soundness proves
the list members' low parts are candidates).
-/

namespace LeanVM.Protocol.EndToEnd

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir Polynomial

@[expose] public section

/-- The number of lanes of the level-0 commitment: `2^6`. -/
abbrev laneBits : ℕ := 6

/-- Lane `u` of column `v` of a committed level-0 word, as an element of `E`: word `63 − u` of the
leaf (the leaf stores the lanes reversed; a missing word reads `0`). -/
def laneOf (W : Word) (u : Fin (2 ^ laneBits)) (v : ℕ) : E :=
  ofK ((W v).reverse.getD u 0)

/-- Block `u` of the stack: cell `x + 2^(μ−6)·u`, the message the lane `u` encodes, indexed by the
`μ − 6` low bits `x` (bit `0` first). -/
def blockOf {μ : ℕ} (q : Column μ) (u : Fin (2 ^ laneBits)) :
    (Fin (μ - laneBits) → Bool) → E :=
  fun x ↦ ofK (q.values.getD (bitsToNat x + 2 ^ (μ - laneBits) * u) 0)

/-- Lane `u` at column `v` of the level-0 polynomial with low part block `u` of `q` and high part
`W_κ·H`: `enc(block u)(x_v) + W_κ(x_v)·H(x_v)`, `κ = μ − 6`. -/
def laneValue (μ R : ℕ) (q : Column μ) (H : K[X]) (u : Fin (2 ^ laneBits))
    (v : Fin (2 ^ (μ - laneBits + R))) : E :=
  enc (μ - laneBits) R (blockOf q u) v +
    ofK (vanishingAt (μ - laneBits) (K.ofBits v) * H.eval (K.ofBits v))

/-- For some high parts `H_u` of degree below `6`, the lanes `enc(block u) + W_κ·H_u` of the stack
`q` agree with the word `W` at every lane of every column of `S`. -/
def Agrees (μ R : ℕ) (W : Word) (q : Column μ) (S : Finset (Fin (2 ^ (μ - laneBits + R)))) :
    Prop :=
  ∃ H : Fin (2 ^ laneBits) → K[X], (∀ u, (H u).degree < laneBits) ∧
    ∀ v ∈ S, ∀ u, laneOf W u v = laneValue μ R q (H u) u v

/-- The **candidates** of a committed word: the stacks that agree with it, for some high parts,
on at least `A` columns. -/
def Candidates (μ R A : ℕ) (W : Word) : Set (Column μ) :=
  {q | ∃ S, A ≤ S.card ∧ Agrees μ R W q S}

end
end LeanVM.Protocol.EndToEnd
