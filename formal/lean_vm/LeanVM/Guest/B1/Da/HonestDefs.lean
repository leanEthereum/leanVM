/-
  LeanVM.Guest.B1.Da.HonestDefs

  The words an honest run of `da_vector` and its callees leaves in their buffers and frame runs,
  as functions of the challenge `z` (G:4371-4435), and reading a layout's word.
-/

module

public import LeanVM.Guest.B1.Da.VectorMath
public import LeanVM.Guest.B1.Da.AtBase

/-!
# The honest words of the dual codeword's builders

* `WordAt L i v`: word `i` of the layout `L` is `v`; `loadHolds_of_wordAt`, `regionL_of_wordAt`:
  on a memory holding `L`, a load at `g^b · g^k`, `b + k = i`, reads `v`, and `i` is in `L`'s
  region.
* `zsCells z`: `zs` (`z^(2^j)` for `j < 14`, then `0`); `aboveCells`: `above_top` (zeros);
  `facCells Z top D`: a `da_factors` buffer (node `n`'s factor for `1 ≤ n < 2^D`);
  `expLeaves root F Z S top D`: a `da_expand` tree's leaves; `offCells Z`: `da_column_offsets`'
  buffer (`offsets[8h + j] = Z_j · Ŵ_j(256 h)`); `stepCells Z b`: its run `steps` of bit `b`.
* `facOut`, `expOut`, `offOut`, `vecOut`: what these functions return: pointers to those words,
  held in the returned layout.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## A layout's words -/

/-- **Word `i` of the layout `L` is `v`.** -/
def WordAt (L : Layout) (i : ℕ) (v : E) : Prop :=
  ∃ q ∈ L, q.1 ≤ i ∧ i < q.1 + q.2.length ∧ q.2.getD (i - q.1) 0 = v

theorem regionL_of_wordAt {L : Layout} {i : ℕ} {v : E} (h : WordAt L i v) : RegionL L i :=
  let ⟨q, hq, h1, h2, _⟩ := h
  ⟨q, hq, h1, h2⟩

theorem loadHolds_of_wordAt {rd : Reader} {L : Layout} (hm : MemL rd L) {b k : ℕ} {v : E}
    (h : WordAt L (b + k) v) : LoadHolds rd (gen ^ b) k v := by
  obtain ⟨⟨c, xs⟩, hq, h1, h2, hv⟩ := h
  simp only at h1 h2 hv
  have hr : LoadHolds rd (gen ^ c) (b + k - c) (xs.getD (b + k - c) 0) := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact reads_of_memL hm hq (b + k - c) (by omega)
  rw [hv, ← Nat.add_zero (b + k - c), ← loadHolds_mul_gen_pow, ← pow_add,
    show c + (b + k - c) = b + k by omega, pow_add, loadHolds_mul_gen_pow, Nat.add_zero] at hr
  exact hr

/-! ## The honest words -/

/-- `da_vector`'s `zs`: `z^(2^j)` for `j < 14`, then `0` (`15` words). -/
def zsCells (z : E) : List E := (List.range 15).map (zsVal z)

/-- `da_vector`'s `above_top`: zeros (`15` words, `8 … 14` written). -/
def aboveCells : List E := List.replicate 15 0

/-- A `da_factors` buffer over the bits `top, top - 1, …` with the powers `Z`: node `n`'s factor
for `1 ≤ n < 2^D`, `0` elsewhere (`256` words). -/
def facCells (Z : ℕ → E) (top D : ℕ) : List E :=
  (List.range 256).map fun n => if 1 ≤ n ∧ n < 2 ^ D then factorAt Z top n else 0

/-- A `da_expand` tree's leaves. -/
def expLeaves (root : E) (F Z S : ℕ → E) (top D : ℕ) : List E :=
  (List.range (2 ^ D)).map (expandLeaf root F Z S top D)

/-- `da_column_offsets`' buffer: `offsets[8h + j] = Z_j · Ŵ_j(256 h)` (`1024` words). -/
def offCells (Z : ℕ → E) : List E :=
  (List.range 1024).map fun i => Z (i % 8) * ofK (wK (i % 8) (256 * (i / 8)))

/-- `da_column_offsets`' run `steps` of bit `b`: `Z_j · Ŵ_j(e_(8 + b))` (`8` words). -/
def stepCells (Z : ℕ → E) (b : ℕ) : List E :=
  (List.range 8).map fun j => Z j * ofK (wK j (2 ^ (8 + b)))

/-! ## What they return -/

/-- `da_factors` returns a pointer to its buffer. -/
def facOut (Z : ℕ → E) (top D : ℕ) : List E → Layout → Prop := fun rets Lo =>
  ∃ b, rets = [gen ^ b] ∧ (b, facCells Z top D) ∈ Lo

/-- A `da_expand` run (`512` words): node `n` of its tree at word `n`, `1 ≤ n < 2^(D + 1)`
(`expandLeaf` at depth `log n`), zeros elsewhere. -/
def expRunVals (root : E) (F Z S : ℕ → E) (top D : ℕ) : List E :=
  (List.range 512).map fun i =>
    if 1 ≤ i ∧ i < 2 ^ (D + 1) then expandLeaf root F Z S top (Nat.log 2 i) (i - 2 ^ Nat.log 2 i)
    else 0

/-- `da_expand` returns a pointer to its tree's leaves, word `2^D` of its run. -/
def expOut (root : E) (F Z S : ℕ → E) (top D : ℕ) : List E → Layout → Prop := fun rets Lo =>
  ∃ b, rets = [gen ^ (b + 2 ^ D)] ∧ (b, expRunVals root F Z S top D) ∈ Lo

/-- `da_column_offsets` returns a pointer to its buffer. -/
def offOut (Z : ℕ → E) : List E → Layout → Prop := fun rets Lo =>
  ∃ b, rets = [gen ^ b] ∧ (b, offCells Z) ∈ Lo

/-- The top tree's run: `da_expand__L14_L7` from `1` over the factors of `z`'s bits `14 … 8`,
no shifts. -/
def topRun (z : E) : List E := expRunVals 1 (factorAt (zsVal z) 14) (zsVal z) (fun _ => 0) 14 7

/-- `da_vector` returns pointers to the powers, the top leaves (word `128` of the top tree's run
in `da_expand`'s frame), the cell factors and the column offsets of `z`. -/
def vecOut (z : E) : List E → Layout → Prop := fun rets Lo =>
  ∃ bz bt bc bo, rets = [gen ^ bz, gen ^ (bt + 2 ^ 7), gen ^ bc, gen ^ bo] ∧ (bz, zsCells z) ∈ Lo ∧
    (bt, topRun z) ∈ Lo ∧ (bc, facCells (zsVal z) 7 8) ∈ Lo ∧ (bo, offCells (zsVal z)) ∈ Lo

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
