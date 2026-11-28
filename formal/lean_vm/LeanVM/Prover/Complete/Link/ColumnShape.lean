/-
  LeanVM.Prover.Complete.Link.ColumnShape

  The pointer-column rounds' shape: one column per pointer column, every table of `2^qVars`
  entries, every term at most `columnCount - 1` factors.
-/

module

public import LeanVM.Prover.Complete.Link.RowShape

/-!
# The pointer columns' shape

`length_linkColumns`: the row point's pointer columns are the tables' pointer columns, `33`.
`tabs_columnProds`, `termsLE_columnProds`: the pointer-column rounds' sum is well shaped at
`columnCount = max (d + 1) 3 + 1`.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover LeanVM.Protocol.Verifier.Defers

/-- The column at a pointer column `(pointer, k)`, from the position `pos` of its tables. -/
def columnOf (W : Witness) (inp : RowInputs) (t q₀ : ℕ) (rt : RowTable) (chi : List E)
    (pos pointer k : ℕ) : ColumnAt :=
  let ch := inp.ch
  let d := W.chunks.d
  let links := (tables.getD t default).links
  let mu := ch.mu.getD t []
  let cols := W.tableCols t
  let point := chi.take rt.height
  let P := rt.prods
  let omega := P.at 0
  let slices := columnSlices (cols.getD pointer #[]) point
  let coef := omega * P.at pos + P.at 1 * P.at (pos + 1)
  let shifts := (List.range inp.maxShift).map fun s ↦
    sumE ((accessesAt links mu pointer).map fun (a, m) ↦
      if a.shift = s + 1 then
        ch.etaMem * inp.yMem * m * omega * ((a.gate.map fun g ↦ P.at (3 + g)).getD 1)
      else 0)
  let certs := (List.range d).map fun i ↦
    omega * inp.cert * ch.eps.getD (q₀ + k) 0 * ch.nu.getD i 0
  let c := rt.corner
  ⟨c * coef, shifts.map (c * ·), inp.functionals.values W.chunks slices, certs.map (c * ·), slices⟩

/-- The step of `columnsAt`. -/
def columnStep (W : Witness) (inp : RowInputs) (t q₀ : ℕ) (rt : RowTable) (chi : List E)
    (acc : List ColumnAt × ℕ) (pk : ℕ × ℕ) : List ColumnAt × ℕ :=
  (acc.1 ++ [columnOf W inp t q₀ rt chi acc.2 pk.1 pk.2],
    acc.2 + 2 + 2 * W.chunks.d +
      (shiftsAt (tables.getD t default).links (inp.ch.mu.getD t []) pk.1).length)

theorem columnsAt_eq (W : Witness) (inp : RowInputs) (t q₀ : ℕ) (rt : RowTable) (chi : List E) :
    columnsAt W inp t q₀ rt chi = ((tables.getD t default).links.pointers.zipIdx.foldl
      (columnStep W inp t q₀ rt chi) ([], 3 + (tables.getD t default).width)).1 := by
  unfold columnsAt columnStep columnOf
  rfl

theorem length_foldl_columnStep (W : Witness) (inp : RowInputs) (t q₀ : ℕ) (rt : RowTable)
    (chi : List E) : ∀ (L : List (ℕ × ℕ)) (acc : List ColumnAt × ℕ),
    (L.foldl (columnStep W inp t q₀ rt chi) acc).1.length = acc.1.length + L.length
  | [], _ => rfl
  | pk :: L, acc => by
    rw [List.foldl_cons, length_foldl_columnStep W inp t q₀ rt chi L]
    simp [columnStep]
    omega

theorem length_columnsAt (W : Witness) (inp : RowInputs) (t q₀ : ℕ) (rt : RowTable)
    (chi : List E) :
    (columnsAt W inp t q₀ rt chi).length = (tables.getD t default).links.pointers.length := by
  rw [columnsAt_eq, length_foldl_columnStep]
  simp

/-- **The row point's pointer columns** are the tables' pointer columns. -/
theorem length_linkColumns (W : Witness) (htab : W.layout.tables = tables) (x : LinkProverPre)
    (chi : List E) (st : RowState) :
    (linkColumns W x chi st).length = linkNPointers W.layout := by
  unfold linkColumns linkNPointers
  rw [htab, List.length_flatMap]
  simp only [length_columnsAt]
  decide +kernel

/-- **The pointer-column rounds' tables have `2^qVars` entries.** -/
theorem tabs_columnProds (d maxShift : ℕ) (mirrors : List E) (columns : List ColumnAt)
    (qVars : ℕ) (base : E) : Tabs qVars (columnProds d maxShift mirrors columns qVars base) := by
  have hall : ∀ y ∈ (columnProds d maxShift mirrors columns qVars base).tables,
      y.size = 2 ^ qVars := by
    intro y hy
    simp only [columnProds, Array.mem_append, List.mem_toArray, List.mem_map, List.mem_range,
      List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with (((rfl | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | rfl <;> simp
  refine ⟨hall, hall _ ?_⟩
  simp [columnProds, Array.getD_eq_getD_getElem?]

/-- **The pointer-column rounds' terms have at most `columnCount - 1` factors.** -/
theorem termsLE_columnProds (d maxShift : ℕ) (hd : 1 ≤ d) (mirrors : List E)
    (columns : List ColumnAt) (qVars : ℕ) (base : E) :
    ∀ cf ∈ (columnProds d maxShift mirrors columns qVars base).terms,
      cf.2.size + 1 ≤ (roundCoefficients d).2 := by
  intro cf hcf
  simp only [columnProds, Array.mem_append, List.mem_toArray, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap] at hcf
  simp only [roundCoefficients]
  rcases hcf with ((rfl | ⟨s, _, rfl⟩) | ⟨i, _, hi⟩) | rfl
  · simp; omega
  · simp; omega
  · rcases hi with rfl | rfl <;> simp
  · simp

end LeanVM.Prover.Complete

end
