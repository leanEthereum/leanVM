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
`python-verifier/verifier.py:1008-1065` at leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`)
is a Merkle root of a word of `2^(μ − 6 + R)` columns, each a leaf of `64` words of `K`. The
leaf stores the lanes of its column in reverse order (`row.reverse`): lane `u` of column `v` is
word `63 − u` of leaf `v` (`laneOf`). Lane `u` of an honest word is the encoding (`enc`, the
novel-basis Reed-Solomon code) of the stack's block `u`: the `2^(μ−6)` consecutive cells at offset
`u · 2^(μ−6)`, so that the stack's coordinates are the message's `μ − 6` low bits and the lane's
six high bits (`blockOf`, Annex B "Optimizations", `f(u, x) = q(x, u)`).

`Agrees μ R W q S` says the encoding of the stack `q` agrees with the word `W` on every lane at
every column of `S`. `Candidates μ R A W` are the stacks whose encoding agrees with `W` on at
least `A` columns: with `A = ⌈(√ρ₋ + η)·n⌉`, the stacks of the Johnson list at radius
`1 − √ρ₋ − η`. The front phases' doom (no candidate is in their state function) and WHIR's
starting relation (every candidate violates a pooled claim) quantify over them; the knowledge
extractor returns the candidate satisfying the relation when there is one.

Candidates are `K`-valued stacks by type: a codeword of the `E`-code close to a `K`-valued word is
`K`-valued (WHIR's soundness proves the list members are the encodings of candidates).
-/

namespace LeanVM.Protocol.EndToEnd

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir

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

/-- The encoding of the stack `q` agrees with the word `W` at every lane of every column of `S`. -/
def Agrees (μ R : ℕ) (W : Word) (q : Column μ) (S : Finset (Fin (2 ^ (μ - laneBits + R)))) :
    Prop :=
  ∀ v ∈ S, ∀ u, laneOf W u v = enc (μ - laneBits) R (blockOf q u) v

/-- The **candidates** of a committed word: the stacks whose encoding agrees with it on at least
`A` columns. -/
def Candidates (μ R A : ℕ) (W : Word) : Set (Column μ) :=
  {q | ∃ S, A ≤ S.card ∧ Agrees μ R W q S}

end
end LeanVM.Protocol.EndToEnd
