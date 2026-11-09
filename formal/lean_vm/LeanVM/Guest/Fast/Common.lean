module

public import LeanVM.Guest.Fast.Numbers
public import LeanVM.Guest.Core

/-!
# The readers' common pieces

`sibN`, a Merkle path level's sibling (`mSib`, `B1/Sig/Merkle.lean`), and the lemmas reading a
table built by `List.range`.

**Tables as arrays.** A literal table (`Fast/*Tables.lean`) is a list, and a compiled reader that
names it builds it at each use and walks it to the entry. The readers over tables (`xmssSigOfA`,
`sphincsSigOfA`, `vsPiOfA`) take them as arrays, built once by the caller: `tabA t`, a table of
rows, read by `offAtA` in constant time (`offAtA_tabA`: it is `offAt`), and `l.toArray`, read by
`Array.getD` (`getD_toArray`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest.Core

@[expose] public section

/-- A path level's sibling: the hinted child at `b`, `b + 1` the node is not (`mSib`). -/
def sibN (σ : Val) (bit b : ℕ) : E := if σ (.n bit) = 1 then σ (.n b) else σ (.n (b + 1))

theorem getD_map_range {α : Type} {f : ℕ → α} {n l : ℕ} {d : α} (hl : l < n) :
    ((List.range n).map f).getD l d = f l := by
  simp [List.getD_eq_getElem?_getD, hl]

theorem offAt_map {f : ℕ → ℕ → ℕ} {n m r k : ℕ} (hr : r < n) (hk : k < m) :
    offAt ((List.range n).map fun r ↦ (List.range m).map (f r)) r k = f r k := by
  simp [offAt, List.getD_eq_getElem?_getD, hr, hk]

theorem ite_sigma {σ : Val} (p : Prop) [Decidable p] (x y : ℕ) :
    σ (if p then V.n x else V.n y) = σ (.n (if p then x else y)) := by
  split <;> rfl

/-- A table of rows, each row an array. -/
def tabA (t : List (List ℕ)) : Array (Array ℕ) := (t.map List.toArray).toArray

/-- Entry `k` of row `r` of a table of arrays (`offAt`). -/
def offAtA (tab : Array (Array ℕ)) (r k : ℕ) : ℕ := (tab.getD r #[]).getD k 0

theorem getD_toArray {α : Type} (l : List α) (i : ℕ) (d : α) : l.toArray.getD i d = l.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem offAtA_tabA (t : List (List ℕ)) (r k : ℕ) : offAtA (tabA t) r k = offAt t r k := by
  unfold offAtA tabA offAt
  rw [getD_toArray]
  by_cases hr : r < t.length
  · simp [List.getD_eq_getElem?_getD, hr]
  · simp [List.getD_eq_getElem?_getD, hr]

end
end LeanVM.Guest.Fast
