import LeanVM.Protocol.Extraction.Defs

/-!
# Tests: toy words for the extractor's decoders

What the extraction tests share (`Toy*.lean`, `Fast.lean`, `FFT.lean`, `LanePM.lean`,
`Cost/Decoder.lean`): pseudo-random stacks of `2^μ` words over `K`, their encodings on the `64`
lanes at rate `2^-R` (with or without random high parts), whole columns replaced by random
leaves, whether a decoder lists the stack, and small pseudo-random polynomials.
-/

namespace LeanVMTests.Extraction

open CompPoly LeanVM.Parameters LeanVM.Parameters.Whir LeanVM.Extraction
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile

/-- A linear congruential generator. -/
def lcg (s : ℕ) : ℕ := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- `len` pseudo-random 64-bit numbers from a seed. -/
def randoms (seed len : ℕ) : Array ℕ := Id.run do
  let mut s := lcg (seed + 1)
  let mut out := #[]
  for _ in [0:len] do
    s := lcg s
    out := out.push s
  return out

/-- A pseudo-random stack of `2^μ` words. -/
def randomStack (seed μ : ℕ) : Vector K (2 ^ μ) :=
  let r := randoms seed (2 ^ μ)
  Vector.ofFn fun i ↦ K.ofBits (r.getD i.val 0)

/-- The word of a stack at rate `2^-R`: column `v` holds lane `u`'s encoding at word `63 − u`. -/
def wordOf {μ : ℕ} (R : ℕ) (q : Vector K (2 ^ μ)) : Array (List K) :=
  let κ := μ - initialFold
  let lanes := (List.range 64).map fun u ↦ novelFwd κ R (laneCoeffs q u)
  Array.ofFn fun v : Fin (2 ^ (κ + R)) ↦ (lanes.map fun e ↦ e.getD v.val 0).reverse

/-- The word of a stack with random high parts: lane `u` at column `v` is the encoding plus
`W_κ(x_v)·H_u(x_v)`, `H_u` of degree `< 6` drawn from the seed (level 0's polynomials at its
degree `2^κ + 5`, of low part the lane). -/
def wordHighOf {μ : ℕ} (R seed : ℕ) (q : Vector K (2 ^ μ)) : Array (List K) :=
  let κ := μ - initialFold
  let lanes := (List.range 64).map fun u ↦ novelFwd κ R (laneCoeffs q u)
  let hs := (List.range 64).map fun u ↦ (randoms (seed + 500 + u) 6).toList.map K.ofBits
  Array.ofFn fun v : Fin (2 ^ (κ + R)) ↦
    let x := K.ofBits v.val
    ((lanes.zip hs).map fun eh ↦
      eh.1.getD v.val 0 + subspacePoly κ x * eh.2.foldr (fun c acc ↦ c + x * acc) 0).reverse

/-- The word with the columns `cols` replaced by random leaves. -/
def corrupt (seed : ℕ) (cols : List ℕ) (w : Array (List K)) : Array (List K) :=
  cols.foldl (fun w v ↦ w.set! v ((randoms (seed + 1000 + v) 64).toList.map K.ofBits)) w

/-- Whether the list decoder at agreement `A` lists the stack, and the list's length. -/
def decodes {μ : ℕ} (R A : ℕ) (q : Vector K (2 ^ μ)) (w : Array (List K)) : Bool × ℕ :=
  let l := decodeStacksAt μ R A fun v ↦ w.getD v []
  (l.any fun d ↦ d.toList == q.toList, l.length)

/-- Whether the fast path returns exactly the stack. -/
def fastDecodes {μ : ℕ} (R : ℕ) (q : Vector K (2 ^ μ)) (w : Array (List K)) : Bool :=
  (fastStacks μ R fun v ↦ w.getD v []).map Vector.toList == [q.toList]

/-- A pseudo-random bivariate polynomial over `K` of `Y`-degree `< ny` and `X`-degree `< nx`. -/
def randomBivariate (seed nx ny : ℕ) : CBivariate K :=
  let r := randoms seed (nx * ny)
  CPolynomial.ofArray (Array.ofFn fun y : Fin ny ↦
    CPolynomial.ofArray (Array.ofFn fun x : Fin nx ↦ K.ofBits (r.getD (y.val * nx + x.val) 0)))

/-- `(X − 3)(X − 5)(X − 7)(X² + X + 1)`: five roots in `K` (`X² + X + 1` splits: `GF(4) ⊆ K`). -/
def rootPoly : CPolynomial K :=
  CPolynomial.linearFactor (K.ofBits 3) * CPolynomial.linearFactor (K.ofBits 5) *
    CPolynomial.linearFactor (K.ofBits 7) *
    (CPolynomial.X * CPolynomial.X + CPolynomial.X + CPolynomial.C 1)

end LeanVMTests.Extraction
