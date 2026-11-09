/-
  LeanVMTests.Protocol.Stacking
-/

module

public import LeanVM.Protocol.ToCompPoly.Stacking
public import LeanVM.Parameters.Field
public import Mathlib.Data.ZMod.Defs
meta import LeanVM.Protocol.ToCompPoly.Stacking
meta import LeanVM.Parameters.Field
meta import CompPoly.Multilinear.Basic

/-!
# Aligned stacking tests

Three blocks on 2, 1 and 0 variables (heights 4, 2, 1), largest first, stacked on three
variables: the offsets and selectors decided in the kernel, the stack's entries, the selection
identity evaluated for every block and with both pads for the first, the same layout carrying
tables over another ring, the empty layout, a stack too small for its tables, and a map of the
entries that is not injective.
-/

namespace LeanVMTests.Protocol

open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval

@[expose] public section

/-- Blocks on 2, 1 and 0 variables: heights 4, 2, 1. -/
def blocks : Blocks where
  n := 3
  size := ![2, 1, 0]
  descending := by
    show ∀ a b : Fin 3, a ≤ b → ![2, 1, 0] b ≤ ![2, 1, 0] a
    decide

/-- The tables `[1, 2, 3, 4]`, `[5, 6]`, `[7]` over `K`. -/
def tables : blocks.Tables K :=
  show (b : Fin 3) → CMlPolynomialEval K (![2, 1, 0] b) from fun b ↦ match b with
    | 0 => (#v[1, K.ofBits 2, K.ofBits 3, K.ofBits 4] : CMlPolynomialEval K 2)
    | 1 => (#v[K.ofBits 5, K.ofBits 6] : CMlPolynomialEval K 1)
    | 2 => (#v[K.ofBits 7] : CMlPolynomialEval K 0)

/-- The blocks fit on three variables. -/
theorem blocks_total_le : blocks.total ≤ 2 ^ 3 := by decide

-- Offsets are prefix sums of the heights; selectors are the offsets shifted by the sizes.
example : blocks.total = 7 := by decide
example : blocks.offset (1 : Fin 3) = 4 := by decide
example : blocks.offset (2 : Fin 3) = 6 := by decide
example : (blocks.selector blocks_total_le (0 : Fin 3)).val = 0 := by decide
example : (blocks.selector blocks_total_le (1 : Fin 3)).val = 2 := by decide
example : (blocks.selector blocks_total_le (2 : Fin 3)).val = 6 := by decide

/-- The stack with pad `0`. -/
def stack0 : CMlPolynomialEval K 3 := blocks.stackAt tables 3 0

-- The stack lays the blocks out in order and pads the last entry.
#guard stack0 = #v[1, K.ofBits 2, K.ofBits 3, K.ofBits 4, K.ofBits 5, K.ofBits 6, K.ofBits 7, 0]
#guard blocks.stackAt tables 3 1 = #v[1, K.ofBits 2, K.ofBits 3, K.ofBits 4, K.ofBits 5, K.ofBits 6, K.ofBits 7, 1]

-- A lifted point is the point followed by the selector bits, low bit first.
#guard blocks.extendPoint blocks_total_le (0 : Fin 3) (#v[K.ofBits 9, K.ofBits 11] : Vector K 2) = #v[K.ofBits 9, K.ofBits 11, 0]
#guard blocks.extendPoint blocks_total_le (1 : Fin 3) (#v[K.ofBits 13] : Vector K 1) = #v[K.ofBits 13, 0, 1]
#guard blocks.extendPoint blocks_total_le (2 : Fin 3) (#v[] : Vector K 0) = #v[0, 1, 1]

-- The selection identity: block 0 at `(9, 11)`, with either pad.
#guard evalMle stack0 (blocks.extendPoint blocks_total_le (0 : Fin 3) (#v[K.ofBits 9, K.ofBits 11] : Vector K 2)) =
  evalMle (#v[1, K.ofBits 2, K.ofBits 3, K.ofBits 4] : CMlPolynomialEval K 2) #v[K.ofBits 9, K.ofBits 11]
#guard evalMle (blocks.stackAt tables 3 1)
    (blocks.extendPoint blocks_total_le (0 : Fin 3) (#v[K.ofBits 9, K.ofBits 11] : Vector K 2)) =
  evalMle (#v[1, K.ofBits 2, K.ofBits 3, K.ofBits 4] : CMlPolynomialEval K 2) #v[K.ofBits 9, K.ofBits 11]
-- Block 1 at `13`, block 2 at the empty point.
#guard evalMle stack0 (blocks.extendPoint blocks_total_le (1 : Fin 3) (#v[K.ofBits 13] : Vector K 1)) =
  evalMle (#v[K.ofBits 5, K.ofBits 6] : CMlPolynomialEval K 1) #v[K.ofBits 13]
#guard evalMle stack0 (blocks.extendPoint blocks_total_le (2 : Fin 3) (#v[] : Vector K 0)) = K.ofBits 7
-- Mutation: with block 1's selector bits reversed, `(1, 0)`, the stack does not answer block 1.
#guard evalMle stack0 (#v[K.ofBits 13, 1, 0] : Vector K 3) ≠
  evalMle (#v[K.ofBits 5, K.ofBits 6] : CMlPolynomialEval K 1) #v[K.ofBits 13]

/-! ## One layout, tables over another ring -/

-- Mapping the stack maps the tables and the pad.
example : CMlPolynomialEval.map (algebraMap K E) stack0 =
    blocks.stackAt (fun b ↦ CMlPolynomialEval.map (algebraMap K E) (tables b)) 3 0 := by
  simpa only [stack0, map_zero] using blocks.map_stackAt (algebraMap K E) tables 3 0

example : CMlPolynomialEval.map (algebraMap K E) (blocks.stackAt tables 3 1) =
    blocks.stackAt (fun b ↦ CMlPolynomialEval.map (algebraMap K E) (tables b)) 3 1 := by
  simpa only [map_one] using blocks.map_stackAt (algebraMap K E) tables 3 1

-- The identity at every point of the larger field, not only at embedded points of `K`.
example (z : Vector E 2) :
    eval₂Mle stack0 (algebraMap K E) (blocks.extendPoint blocks_total_le (0 : Fin 3) z) =
      eval₂Mle (tables (0 : Fin 3)) (algebraMap K E) z :=
  blocks.stack_eval₂ (algebraMap K E) tables blocks_total_le 0 (0 : Fin 3) z

-- This point is outside the embedded base field.
example : ¬ IsInK (E.ofLimbs 0 1 0) := by decide
#guard eval₂Mle stack0 (algebraMap K E)
    (#v[E.ofLimbs 0 1 0, E.ofLimbs 1 1 0, 0] : Vector E 3) =
  eval₂Mle (tables (0 : Fin 3)) (algebraMap K E) #v[E.ofLimbs 0 1 0, E.ofLimbs 1 1 0]

/-! ## Boundary layouts -/

/-- The layout with no block. -/
def emptyBlocks : Blocks where
  n := 0
  size := Fin.elim0
  descending := fun i ↦ Fin.elim0 i

/-- The one family of tables on the empty layout. -/
def emptyTables : emptyBlocks.Tables K := fun b ↦ Fin.elim0 b

-- With no block the stack is the pad, on zero variables too.
#guard emptyBlocks.stackAt emptyTables 0 1 = (#v[1] : CMlPolynomialEval K 0)
#guard emptyBlocks.stackAt emptyTables 2 1 = (#v[1, 1, 1, 1] : CMlPolynomialEval K 2)

-- A stack too small for its tables truncates, and mapping still commutes with it.
example : ¬ blocks.total ≤ 2 ^ 0 := by decide
#guard blocks.stackAt tables 0 1 = (#v[1] : CMlPolynomialEval K 0)
example : CMlPolynomialEval.map (algebraMap K E) (blocks.stackAt tables 0 1) =
    blocks.stackAt (fun b ↦ CMlPolynomialEval.map (algebraMap K E) (tables b)) 0 1 := by
  simpa only [map_one] using blocks.map_stackAt (algebraMap K E) tables 0 1

-- The map need not be injective: this one identifies 0 and 5, and sends the pad 7 to 2.
example : ¬ Function.Injective (Int.castRingHom (ZMod 5)) := by
  intro h
  have h05 : (0 : ℤ) = 5 := h (by decide)
  norm_num at h05

example (B : Blocks) (t : B.Tables ℤ) (μ : ℕ) :
    CMlPolynomialEval.map (Int.castRingHom (ZMod 5)) (B.stackAt t μ 7) =
      B.stackAt (fun b ↦ CMlPolynomialEval.map (Int.castRingHom (ZMod 5)) (t b)) μ 2 := by
  have hpad : (Int.castRingHom (ZMod 5)) 7 = 2 := by decide
  simpa only [hpad] using B.map_stackAt (Int.castRingHom (ZMod 5)) t μ 7

end
end LeanVMTests.Protocol
