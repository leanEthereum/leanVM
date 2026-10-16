module

public import Mathlib.Data.Nat.Bitwise

@[expose] public section

/-!
The plan of `flock::gadgets::Multiplier`: the carry-save steps that sum the 66 affine rows of `a b`.

Row `i < 64` holds `a_i ? b : NOT b` shifted down a place, row 64 `NOT a >> 1` and `a 2^63`, row 65 the same for
`b`; the constant one and `g = NOT a_0 NOT b_0` fill column 0 of rows 2 and 3. A step takes the three live rows that
end lowest and replaces them by their sum row and their carry row: a product at each position with two bits or more,
unless exactly two are present and the carry row is free there, when one bit moves into it instead. A ripple addition
sums the last two rows. The masks say which positions of a row can be nonzero; the plan is a function of the width
`n` alone, computed here as `Multiplier::build` computes it.
-/

namespace LeanVMCircuits.Multiply

/-- The rows: 64 partial rows, then the `a` and `b` rows. -/
def nRows : ℕ := 66
def aRow : ℕ := 64
def bRow : ℕ := 65

/-- Bit `p` of a mask. -/
def bit (m p : ℕ) : Bool := m.testBit p

/-- The mask of positions `p < n` where `f p` holds. -/
def maskOf (n : ℕ) (f : ℕ → Bool) : ℕ := (List.range n).foldl (fun m p => if f p then m ||| 2 ^ p else m) 0

/-- Which positions of row `r` start present: where `Multiplier::build` puts a nonzero wire. -/
def initialPresent (n r : ℕ) : ℕ :=
  maskOf n fun p =>
    if r < 64 then
      -- Partial row `r`: `b_j` at `p = r + j - 1`, and the constant and `g` at column 0 of rows 2 and 3.
      (decide (p + 1 ≥ r) && decide (p + 1 - r < 64) && decide (p + 1 ≠ 0 || r ≠ 0) &&
        !(r == 0 && p + 1 == 0)) || (p == 0 && (r == 2 || r == 3))
    else
      -- `NOT a >> 1`'s 63 bits, then `a`'s bits up to the width, and for 128 bits half of `2^128` in row 64.
      decide (p < 63) || (decide (63 ≤ p) && decide (p - 63 < min 64 (n - 63))) ||
        (r == aRow && n == 128 && p == 127)

/-- One carry-save step: rows `x`, `y`, `z` become the sum row in `x` and the carry row in `y`. -/
structure Csa where
  x : ℕ
  y : ℕ
  z : ℕ
  products : ℕ
  moveY : ℕ
  moveZ : ℕ
  deriving Repr, DecidableEq, Inhabited

/-- A row's `(highest, lowest)` position, the key `Multiplier::build` sorts by. -/
def ends (m : ℕ) : ℕ × ℕ :=
  ((List.range 128).foldl (fun hi p => if m.testBit p then p else hi) 0,
    (List.range 128).find? (fun p => m.testBit p) |>.getD 128)

/-- The key order: lexicographic, highest position first. -/
def keyLe (a b : ℕ × ℕ) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)

/-- A stable sort, as `sort_by_key`: by structural recursion, so the kernel evaluates it. -/
def insertionSort (le : ℕ → ℕ → Bool) : List ℕ → List ℕ
  | [] => []
  | x :: xs => insertBy' le x (insertionSort le xs)
where
  /-- Insert `x`, which came before every element of the list, ahead of the first one strictly above it. -/
  insertBy' (le : ℕ → ℕ → Bool) (x : ℕ) : List ℕ → List ℕ
    | [] => [x]
    | y :: ys => if le x y then x :: y :: ys else y :: insertBy' le x ys

/-- A step's products and moves from its rows' masks: a pair position below the top takes a move when it is not a
triple and the carry row is free there, that is the position below takes no product. -/
def productsAndMoves (n px py pz : ℕ) : ℕ × ℕ :=
  let pairs := ((px &&& py) ||| (px &&& pz) ||| (py &&& pz)) &&& ((2 ^ n - 1) >>> 1)
  let triples := px &&& py &&& pz
  (List.range (n - 1)).foldl (fun (products, moves) p =>
    if bit pairs p then
      if !bit triples p && !(p > 0 && bit products (p - 1)) then (products, moves ||| 2 ^ p)
      else (products ||| 2 ^ p, moves)
    else (products, moves)) (0, 0)

/-- The carry-save steps, the two rows left, from the masks and the live rows. -/
def stepsFrom (n : ℕ) : ℕ → List ℕ → (ℕ → ℕ) → List Csa → List Csa × (ℕ × ℕ)
  | 0, live, _, steps => (steps.reverse, (live.getD 0 0, live.getD 1 0))
  | fuel + 1, live, present, steps =>
    if live.length ≤ 2 then (steps.reverse, (live.getD 0 0, live.getD 1 0)) else
    let order := insertionSort (fun s t => keyLe (ends (present (live.getD s 0)))
      (ends (present (live.getD t 0)))) (List.range live.length)
    let x := live.getD (order.getD 0 0) 0
    let y := live.getD (order.getD 1 0) 0
    let z := live.getD (order.getD 2 0) 0
    let live := live.filter (fun r => r ≠ x && r ≠ y && r ≠ z) ++ [x, y]
    let (px, py, pz) := (present x, present y, present z)
    let (products, moves) := productsAndMoves n px py pz
    let step : Csa := { x, y, z, products, moveY := moves ^^^ (moves &&& pz), moveZ := moves &&& pz }
    let present := fun r => if r = x then px ||| py ||| pz else if r = y then (products <<< 1) ||| moves else present r
    stepsFrom n fuel live present (step :: steps)

/-- The plan for an `n`-bit product: its steps and the two rows it leaves. -/
@[irreducible] def plan (n : ℕ) : List Csa × (ℕ × ℕ) := stepsFrom n nRows (List.range nRows) (initialPresent n) []

end LeanVMCircuits.Multiply
