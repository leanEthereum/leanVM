/-
  LeanVMTests.Protocol.Stack

  Controls for the stack of columns: the reading law on a column that is not an honest stack, the
  aligned layout in the layout field of an instance, and the two padding decompositions.
-/

import LeanVM.Protocol.Stack
import LeanVM.Protocol.Spine.Toy
import LeanVMTests.Protocol.Stacking

/-!
# Stack of columns controls

The fixture is the three blocks of heights 4, 2, 1 of `LeanVMTests.Protocol.Stacking`. The
reading law is checked on a column no honest prover would commit and at a point outside `K`; a
selector with its bits reversed breaks it; a placement with the small block first has no
selector at all. Three blocks of height 2, renamed to the columns of the toy instance, take the
place of its hand-written layout, and the relation decides the same. One block of height 8 read
as two strided slots: the slots against the aligned halves, the lifted points against the
Python verifier's `Placement.stack_point`, the reading law at a point outside `K` against the
aligned reading, and the union with the aligned layout. A plain file, so `#guard` evaluates the
compiled definitions.
-/

namespace LeanVMTests.Protocol.Stack

open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval

/-! ## The honest stack -/

-- Blocks at their windows, zero in the one uncovered cell.
#guard (blocks.stackColumn tables 3).values = #v[1, K.ofBits 2, K.ofBits 3, K.ofBits 4, K.ofBits 5, K.ofBits 6, K.ofBits 7, 0]

-- Reading the honest stack returns each block.
#guard (blocks.readColumn blocks_total_le (blocks.stackColumn tables 3)
  (0 : Fin 3)).values.toList = [1, K.ofBits 2, K.ofBits 3, K.ofBits 4]
#guard (blocks.readColumn blocks_total_le (blocks.stackColumn tables 3)
  (1 : Fin 3)).values.toList = [K.ofBits 5, K.ofBits 6]
#guard (blocks.readColumn blocks_total_le (blocks.stackColumn tables 3)
  (2 : Fin 3)).values.toList = [K.ofBits 7]

/-! ## The reading law on an arbitrary column -/

/-- A column that is not the stack of the fixture's blocks, with a nonzero uncovered cell. -/
def arbitrary : Column 3 := ⟨#v[K.ofBits 9, K.ofBits 8, K.ofBits 7, K.ofBits 6, K.ofBits 5, K.ofBits 4, K.ofBits 3, K.ofBits 2]⟩

/-- A point of `E` outside `K`. -/
def u : E := E.ofLimbs 0 1 0

example : ¬ IsInK u := by decide

-- The blocks read off it are its windows: cells 0 to 3, cells 4 and 5, cell 6.
#guard (blocks.readColumn blocks_total_le arbitrary (0 : Fin 3)).values.toList = [K.ofBits 9, K.ofBits 8, K.ofBits 7, K.ofBits 6]
#guard (blocks.readColumn blocks_total_le arbitrary (1 : Fin 3)).values.toList = [K.ofBits 5, K.ofBits 4]
#guard (blocks.readColumn blocks_total_le arbitrary (2 : Fin 3)).values.toList = [K.ofBits 3]

-- A lifted point is the point followed by the selector bits, low bit first: block 1 sits at
-- selector index 2, bits `(0, 1)`.
#guard blocks.extendPoint blocks_total_le (1 : Fin 3) (#v[u] : Vector E 1) = #v[u, 0, 1]
#guard blocks.extendPoint blocks_total_le (0 : Fin 3) (#v[u, u + 1] : Vector E 2) =
  #v[u, u + 1, 0]
#guard blocks.extendPoint blocks_total_le (2 : Fin 3) (#v[] : Vector E 0) = #v[0, 1, 1]

-- The law, through the `Layout` an instance carries, for every block.
#guard eval₂Mle ((blocks.layout blocks_total_le).read arbitrary (0 : Fin 3)).values
    (algebraMap K E) #v[u, u + 1] =
  eval₂Mle arbitrary.values (algebraMap K E)
    ((blocks.layout blocks_total_le).extend (0 : Fin 3) #v[u, u + 1])
#guard eval₂Mle ((blocks.layout blocks_total_le).read arbitrary (1 : Fin 3)).values
    (algebraMap K E) #v[u] =
  eval₂Mle arbitrary.values (algebraMap K E)
    ((blocks.layout blocks_total_le).extend (1 : Fin 3) #v[u])
#guard eval₂Mle ((blocks.layout blocks_total_le).read arbitrary (2 : Fin 3)).values
    (algebraMap K E) #v[] =
  eval₂Mle arbitrary.values (algebraMap K E)
    ((blocks.layout blocks_total_le).extend (2 : Fin 3) #v[])

-- Mutation: block 1's selector bits reversed, `(1, 0)`, select cells 2 and 3 instead.
#guard eval₂Mle (blocks.readColumn blocks_total_le arbitrary (1 : Fin 3)).values
    (algebraMap K E) #v[u] ≠
  eval₂Mle arbitrary.values (algebraMap K E) #v[u, 1, 0]

/-! ## Alignment needs the largest block first -/

-- Sizes 0, 1, 2 in that order are not a `Blocks`.
example : ¬ Antitone (![0, 1, 2] : Fin 3 → ℕ) := fun h ↦
  absurd (h (show (0 : Fin 3) ≤ 1 by decide)) (by decide)

/-- The same cells with the small block first: the block `[5, 6]` sits at offset 1. -/
def smallFirst : CMlPolynomialEval K 3 := #v[K.ofBits 7, K.ofBits 5, K.ofBits 6, 1, K.ofBits 2, K.ofBits 3, K.ofBits 4, 0]

-- No selector reads the block `[5, 6]` off that placement: every slice of height 2 differs.
#guard (List.finRange 4).all fun j ↦
  slice (k := 1) (m := 2) smallFirst j ≠ (#v[K.ofBits 5, K.ofBits 6] : CMlPolynomialEval K 1)
-- Largest first, the selector of index 2 reads it.
#guard slice (k := 1) (m := 2) (blocks.stackColumn tables 3).values (2 : Fin 4) =
  (#v[K.ofBits 5, K.ofBits 6] : CMlPolynomialEval K 1)

/-! ## The aligned layout in an instance -/

/-- Three blocks of height 2, the columns of the toy instance. -/
def toyBlocks : Blocks where
  n := 3
  size := fun _ ↦ 1
  descending := fun _ _ _ ↦ le_refl 1

theorem toyBlocks_total_le : toyBlocks.total ≤ 2 ^ 3 := by decide

/-- The aligned layout of `toyBlocks`, its blocks renamed to the columns of the toy's table. -/
def toyLayout : Layout 3 Toy.Col (fun _ ↦ 1) :=
  (toyBlocks.layout toyBlocks_total_le).comap (fun c ↦ c.2) (fun _ ↦ rfl)

-- It reads the cells the toy's hand-written layout reads, on its honest stack and on an
-- arbitrary column, and lifts points the same way.
#guard (List.finRange 3).all fun c ↦
  (toyLayout.read Toy.honest ⟨0, c⟩).values.toList =
    (Toy.layout.read Toy.honest ⟨0, c⟩).values.toList
#guard (List.finRange 3).all fun c ↦
  (toyLayout.read arbitrary ⟨0, c⟩).values.toList =
    (Toy.layout.read arbitrary ⟨0, c⟩).values.toList
#guard (List.finRange 3).all fun c ↦
  toyLayout.extend ⟨0, c⟩ #v[u] = Toy.layout.extend ⟨0, c⟩ #v[u]

/-- The toy instance with the aligned layout in place of its own. -/
abbrev toyAligned : M3Instance := { Toy.toy with layout := toyLayout }

-- The relation decides the same: the honest stack passes, and a stack with one cell of the
-- constrained column changed fails.
#guard M3Holds toyAligned (1: K) Toy.honest
#guard ¬ M3Holds toyAligned (1: K) ⟨#v[1, 1, 1, 1, K.ofBits 2, 0, 0, 0]⟩
#guard ¬ M3Holds toyAligned (0: K) Toy.honest

/-! ## Evaluation at an arbitrary point -/

/-- A point of `E^3` off the cube and outside `K`. -/
def ζ : Vector E 3 := #v[u, u + 1, u * u]

-- The zero-padded stack is the weighted sum of its blocks.
#guard eval₂Mle (blocks.stackColumn tables 3).values (algebraMap K E) ζ =
  ∑ b : Fin blocks.n, blocks.selectorWeight blocks_total_le b ζ *
    eval₂Mle (tables b) (algebraMap K E) (blocks.lowPoint blocks_total_le b ζ)

/-- The fixture's tables over `E`, as the leaves of a product tree are. -/
def tablesE : blocks.Tables E := fun b ↦ CMlPolynomialEval.map (algebraMap K E) (tables b)

/-- The weighted sum of the blocks at `ζ`. -/
def covered : E :=
  ∑ b : Fin blocks.n, blocks.selectorWeight blocks_total_le b ζ *
    evalMle (tablesE b) (blocks.lowPoint blocks_total_le b ζ)

/-- The total selector weight at `ζ`. -/
def weight : E := ∑ b : Fin blocks.n, blocks.selectorWeight blocks_total_le b ζ

-- The one-padded stack adds the weight of the uncovered cell.
#guard evalMle (blocks.stackAt tablesE 3 1) ζ = covered + (1 + weight)
-- Mutations: the padding term is neither absent nor the constant `1`.
#guard evalMle (blocks.stackAt tablesE 3 1) ζ ≠ covered
#guard evalMle (blocks.stackAt tablesE 3 1) ζ ≠ covered + 1

/-! ## Strided slots -/

/-- One block of height `2 ^ 3`, filling a stack of height `2 ^ 3`. -/
def oneBlock : Blocks where
  n := 1
  size := fun _ ↦ 3
  descending := fun _ _ _ ↦ le_refl 3

theorem oneBlock_total_le : oneBlock.total ≤ 2 ^ 3 := by decide

/-- Stride two: slots `0` and `1` of the block, each a column of height `2 ^ 2`. -/
def strided : Layout 3 (Fin 2) (fun _ ↦ 2) :=
  oneBlock.stridedLayout oneBlock_total_le (0 : Fin 1) 1 (fun c ↦ c) (fun _ ↦ rfl)

/-- Eight distinct cells. -/
def cells : Column 3 :=
  ⟨#v[K.ofBits 10, K.ofBits 11, K.ofBits 12, K.ofBits 13, K.ofBits 14, K.ofBits 15,
    K.ofBits 16, K.ofBits 17]⟩

-- Slot 0 reads the cells at even indices and slot 1 those at odd indices, where the aligned
-- slice of height 4 at index 0 reads the first four.
#guard (strided.read cells 0).values.toList =
  [K.ofBits 10, K.ofBits 12, K.ofBits 14, K.ofBits 16]
#guard (strided.read cells 1).values.toList =
  [K.ofBits 11, K.ofBits 13, K.ofBits 15, K.ofBits 17]
#guard (slice (k := 2) (m := 1) cells.values 0).toList =
  [K.ofBits 10, K.ofBits 11, K.ofBits 12, K.ofBits 13]

-- A claim on slot 1 at `(u, u + 1)` lifts to `(1, u, u + 1)`: the slot bit, the point, and no
-- selector bit, the block filling the stack.
#guard (strided.extend 1 #v[u, u + 1]).toList = [1, u, u + 1]

/-- The Python verifier's `Placement.stack_point` (`python-verifier/verifier.py:285-295` at
leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`): the bits of `index` as a point of
`stackLog` coordinates, low bit first; the low `low` of them, then the claim's point, then the
bits above the window. -/
def stackPoint (nvars index low : ℕ) (point : List E) (stackLog : ℕ) : List E :=
  let bits := (List.range stackLog).map fun k ↦ if index.testBit k then (1 : E) else 0
  bits.take low ++ point ++ bits.drop (low + nvars)

-- The lifted point of a slot is the Python's placement of a two-variable claim at the slot's
-- index with one low coordinate, on a stack of `2 ^ 3`; the fixture's aligned block 1, at
-- offset 4 with no low coordinate, agrees too.
#guard (strided.extend 1 #v[u, u + 1]).toList = stackPoint 2 1 1 [u, u + 1] 3
#guard (strided.extend 0 #v[u, u + 1]).toList = stackPoint 2 0 1 [u, u + 1] 3
#guard (blocks.extendPoint blocks_total_le (1 : Fin 3) (#v[u] : Vector E 1)).toList =
  stackPoint 1 4 0 [u] 3

/-- Slot 1 read off the cells, at `(u, u + 1)`. -/
def slotValue : E := eval₂Mle (strided.read cells 1).values (algebraMap K E) #v[u, u + 1]

/-- The cells at the lifted point. -/
def liftedValue : E :=
  eval₂Mle cells.values (algebraMap K E) (strided.extend 1 #v[u, u + 1])

/-- The cells at `(u, u + 1, 1)`: the slot bit on top, the aligned reading of the upper half. -/
def alignedValue : E := eval₂Mle cells.values (algebraMap K E) #v[u, u + 1, 1]

-- The reading law at that point, and a mutation: the slot bit on top reads another column.
#guard slotValue = liftedValue
#guard slotValue ≠ alignedValue

-- The union with the aligned layout of the block reads a slot on the left and the block on
-- the right.
#guard ((strided.piecewise (oneBlock.layout oneBlock_total_le)).read cells
  (.inl 1)).values.toList = [K.ofBits 11, K.ofBits 13, K.ofBits 15, K.ofBits 17]
#guard ((strided.piecewise (oneBlock.layout oneBlock_total_le)).read cells
  (.inr (0 : Fin 1))).values.toList = cells.values.toList

end LeanVMTests.Protocol.Stack
