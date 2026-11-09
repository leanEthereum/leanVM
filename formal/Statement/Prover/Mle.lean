module

public import Statement.LeanVmVerifier

/-!
# Tables as arrays

The verifier's list operations on tables (`eqKernel`, `foldPairs`, `multilinearEval`), on arrays,
for every phase of the prover, and a sum as a loop.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-- `eqKernel point` on an array: the `2^|point|` equality weights, the first coordinate the
lowest bit. -/
def eqTable (point : List E) : Array E :=
  point.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) #[1]

/-- `foldPairs r` on an array: adjacent pairs `(a, b)` become `a·(1 + r) + b·r`. -/
def foldPairsA (r : E) (t : Array E) : Array E :=
  Array.ofFn (n := t.size / 2) fun i ↦
    t[2 * i.1]'(by omega) * (1 + r) + t[2 * i.1 + 1]'(by omega) * r

/-- `multilinearEval` on an array: one fold per coordinate; `0` for an empty result. -/
def mleA (t : Array E) (point : List E) : E :=
  (point.foldl (fun cur r ↦ foldPairsA r cur) t).getD 0 0

/-- `mleA` of a table over `K`. -/
def mleK (t : Array K) (point : List E) : E := mleA (t.map ofK) point

/-- `Σ_{i < n} f i`, as a loop. -/
def sumRange (n : ℕ) (f : ℕ → E) : E := Nat.fold n (fun i _ acc ↦ acc + f i) 0

end LeanVM.Prover

end
