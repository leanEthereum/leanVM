/-
  LeanVM.Guest.B1.Da.HonestDefs

  The words an honest run of `da_vector` and its callees leaves in their buffers and frame runs,
  as functions of the challenge `z`, and reading a layout's word.
-/

module

public import LeanVM.Guest.B1.Da.VectorMath
public import LeanVM.Guest.B1.Da.AtBase

/-!
# The honest words of the dual codeword's builders

* `zsCells z`: `zs` (`z^(2^j)` for `j < 13`, then `0`); `aboveCells`: `above_top` (zeros);
  `facCells Z top D`: a `da_factors` buffer (node `n`'s factor for `1 ≤ n < 2^D`);
  `offCells Z`: `da_column_offsets`'
  buffer (`offsets[7h + j] = Z_j · Ŵ_j(128 h)`); `stepCells Z b`: its run `steps` of bit `b`.
* `facOut`, `expOut`, `offOut`, `vecOut`: what these functions return: pointers to those words,
  held in the returned layout.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## A layout's words -/

/-! ## The honest words -/

/-- `da_vector`'s `zs`: `z^(2^j)` for `j < 13`, then `0` (`14` words). -/
def zsCells (z : E) : List E := (List.range 14).map (zsVal z)

/-- `da_vector`'s `above_top`: zeros (`14` words, `7 … 13` written). -/
def aboveCells : List E := List.replicate 14 0

/-- A `da_factors` buffer over the bits `top, top - 1, …` with the powers `Z`: node `n`'s factor
for `1 ≤ n < 2^D`, `0` elsewhere (`128` words). -/
def facCells (Z : ℕ → E) (top D : ℕ) : List E :=
  (List.range 128).map fun n => if 1 ≤ n ∧ n < 2 ^ D then factorAt Z top n else 0

/-- `da_column_offsets`' buffer: `offsets[7h + j] = Z_j · Ŵ_j(128 h)` (`896` words). -/
def offCells (Z : ℕ → E) : List E :=
  (List.range 896).map fun i => Z (i % 7) * ofK (wK (i % 7) (128 * (i / 7)))

/-- `da_column_offsets`' run `steps` of bit `b`: `Z_j · Ŵ_j(e_(7 + b))` (`7` words). -/
def stepCells (Z : ℕ → E) (b : ℕ) : List E :=
  (List.range 7).map fun j => Z j * ofK (wK j (2 ^ (7 + b)))

/-! ## What they return -/

/-- `da_factors` returns a pointer to its buffer. -/
def facOut (Z : ℕ → E) (top D : ℕ) : List E → Layout → Prop := fun rets Lo =>
  ∃ b, rets = [gen ^ b] ∧ (b, facCells Z top D) ∈ Lo

/-- A `da_expand` run (`256` words): node `n` of its tree at word `n`, `1 ≤ n < 2^(D + 1)`
(`expandLeaf` at depth `log n`), zeros elsewhere. -/
def expRunVals (root : E) (F Z S : ℕ → E) (top D : ℕ) : List E :=
  (List.range 256).map fun i =>
    if 1 ≤ i ∧ i < 2 ^ (D + 1) then expandLeaf root F Z S top (Nat.log 2 i) (i - 2 ^ Nat.log 2 i)
    else 0

/-- `da_expand` returns a pointer to its tree's leaves, word `2^D` of its run. -/
def expOutAt (root : E) (F Z S : ℕ → E) (top D b : ℕ) : List E → Layout → Prop := fun rets Lo =>
  rets = [gen ^ (b + 2 ^ D)] ∧ (b, expRunVals root F Z S top D) ∈ Lo

/-- `da_expand` returns its run at its leaves, somewhere. -/
def expOut (root : E) (F Z S : ℕ → E) (top D : ℕ) : List E → Layout → Prop := fun rets Lo =>
  ∃ b, expOutAt root F Z S top D b rets Lo

/-- `da_column_offsets` returns a pointer to its buffer. -/
def offOut (Z : ℕ → E) : List E → Layout → Prop := fun rets Lo =>
  ∃ b, rets = [gen ^ b] ∧ (b, offCells Z) ∈ Lo

/-- The top tree's run: `da_expand__L13_L7` from `1` over the factors of `z`'s bits `13 … 7`,
no shifts. -/
def topRun (z : E) : List E := expRunVals 1 (factorAt (zsVal z) 13) (zsVal z) (fun _ => 0) 13 7

/-- `da_vector` returns pointers to the powers, the top leaves (word `128` of the top tree's run
in `da_expand`'s frame), the cell factors and the column offsets of `z`. -/
def vecOut (z : E) : List E → Layout → Prop := fun rets Lo =>
  ∃ bz bt bc bo, rets = [gen ^ bz, gen ^ (bt + 2 ^ 7), gen ^ bc, gen ^ bo] ∧ (bz, zsCells z) ∈ Lo ∧
    (bt, topRun z) ∈ Lo ∧ (bc, facCells (zsVal z) 6 7) ∈ Lo ∧ (bo, offCells (zsVal z)) ∈ Lo

/-! ## A returned buffer's base -/

/-- The bases `b` a callee's result `o` satisfies `P b` at, chosen; `default` if none. -/
noncomputable def outB {α : Type} [Inhabited α] (P : α → List E → Layout → Prop) (o : List E × Layout) : α :=
  open Classical in if h : ∃ b, P b o.1 o.2 then Classical.choose h else default

theorem outB_spec {α : Type} [Inhabited α] {P : α → List E → Layout → Prop} {o : List E × Layout}
    (h : ∃ b, P b o.1 o.2) : P (outB P o) o.1 o.2 := by
  unfold outB
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec h

end
end LeanVM.Guest.B1.Da
