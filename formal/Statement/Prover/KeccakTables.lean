module

public import Statement.Prover.Script
public import Statement.Prover.Mle

/-!
# Tables for the Keccak prover

Coefficient lists (constant first) added and scaled, and the byte tables by which a sum of
weights selected by the bits of a word is a few table reads.
-/

@[expose] public section

namespace LeanVM.Prover.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-! ## Coefficient lists -/

/-- The sum of two coefficient lists of the same length. -/
def addCoeffs (a b : List E) : List E := List.zipWith (· + ·) a b

/-- `Σ_{i < n} v i` for coefficient lists of `k` entries. -/
def sumCoeffs (k n : ℕ) (v : ℕ → List E) : List E :=
  (List.range n).foldl (fun acc i ↦ addCoeffs acc (v i)) (List.replicate k 0)

/-- A coefficient list scaled. -/
def scaleCoeffs (s : E) (a : List E) : List E := a.map (s * ·)

/-! ## Bits -/

/-- The booleans `f 0, …, f (n - 1)` as the bits of a number. -/
def packBits (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => packBits f n ||| (if f n then 1 <<< n else 0)

/-- The `256` subset sums of `v 0, …, v 7`: entry `b` is `Σ_{t < 8, bit t of b} v t`. -/
def byteSums (v : ℕ → E) : Array E :=
  Array.ofFn (n := 256) fun b ↦
    (List.range 8).foldl (fun acc t ↦ if b.val.testBit t then acc + v t else acc) 0

/-- `Σ_{t < 64} [bit t of word]·v(t)` by eight reads of byte tables, `tabs[k]` the table of
`v(8k), …, v(8k + 7)`. -/
def wordDot (tabs : Array (Array E)) (word : ℕ) : E :=
  sumRange 8 fun k ↦ (tabs.getD k #[]).getD ((word >>> (8 * k)) % 256) 0

/-- The byte tables of `v(64·l + ·)`, for `wordDot`. -/
def laneTabs (v : ℕ → E) (l : ℕ) : Array (Array E) :=
  Array.ofFn (n := 8) fun k ↦ byteSums fun t ↦ v (64 * l + 8 * k.val + t)

/-- `x` added to the entries of `acc` at the set bits of `g` below `n`. -/
def addBits (x : E) (g : ℕ) : ℕ → Array E → Array E
  | 0, acc => acc
  | n + 1, acc => addBits x g n (if g.testBit n then acc.modify n (· + x) else acc)

end LeanVM.Prover.KeccakGkr

end
