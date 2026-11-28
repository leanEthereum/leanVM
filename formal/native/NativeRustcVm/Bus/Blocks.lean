module

public import NativeRustcVm.Layout.Values

/-!
# The bus blocks as fixed data

The Rust keeps a side's blocks as fixed data (`PUSH_BLOCKS`, `PULL_BLOCKS`, `COUNT_BLOCKS`: each
block's owner and tuple), its rows looked up from the layout (`LayoutW::block_rows`), its tuple's
forms read from `TUPLES` (`tuple_forms`), each form by `form_terms` (`formAt`). The model builds the
blocks (`busBlocks`) from the tables. They agree:

- `tupleOf tu`: tuple `tu`'s forms, those of `TUPLES[tu]`; `blockW h r b`: block `b` at the
  heights `h` and rows `r`.
- `tupleOf_eq`: the data reads back every tuple of `Data.allTuples`.
- **`busBlocks_eq`**: `busBlocks h r` is the three sides' data blocks, each `blockW h r`.
-/

namespace NativeRustcVm.Bus

open NativeVm.Model LeanVM.Protocol.Verifier NativeRustcVm.Data NativeRustcVm.Layout

@[expose] public section

/-- `tuple_forms(tu)` then `form_terms`: the forms of `TUPLES[tu]` (none past `TUPLES`). -/
def tupleOf (tu : Nat) : Array FormW :=
  match tuples[tu]? with
  | some sp => ((List.range sp.len).map fun i ↦ formAt (sp.start + i)).toArray
  | none => #[]

/-- **A block of the data** at the tables' heights `h` and rows `r`: its owner's height and rows
(`block_rows`), its tuple's forms, its owner. -/
def blockW (h r : Array Nat) (b : Block) : BusBlockW :=
  ⟨h.getD b.owner 0, r.getD b.owner 0, tupleOf b.tuple, b.owner⟩

/-- A tuple of `allTuples` as a block at the heights `h` and rows `r`. -/
def tupleBlock (h r : Array Nat) (x : Nat × Nat × List Form) : BusBlockW :=
  ⟨h.getD x.1 0, r.getD x.1 0, (x.2.2.map FormW.ofForm).toArray, x.1⟩

/-! ## Spans read back -/

/-- **A span reads back its list**: span `i` of the lengths of `L` from `|P|`, in `P` then `L`'s
lists end to end, is `L[i]`. -/
theorem read_spansFrom {α : Type} (P : List α) (L : List (List α)) (i : Nat) (hi : i < L.length) :
    ∃ sp, (spansFrom P.length (L.map List.length))[i]? = some sp ∧ sp.len = L[i].length ∧
      ((P ++ L.flatten).drop sp.start).take sp.len = L[i] := by
  induction L generalizing P i with
  | nil => cases hi
  | cons l L ih =>
    cases i with
    | zero =>
      refine ⟨⟨P.length, l.length⟩, rfl, rfl, ?_⟩
      simp
    | succ i =>
      obtain ⟨sp, hsp, hlen, hread⟩ := ih (P ++ l) i (by simp at hi; omega)
      refine ⟨sp, ?_, by simpa using hlen, ?_⟩
      · simpa [spansFrom] using hsp
      · simpa using hread

theorem read_spans {α : Type} (L : List (List α)) (i : Nat) (hi : i < L.length) :
    ∃ sp, (spansFrom 0 (L.map List.length))[i]? = some sp ∧ sp.len = L[i].length ∧
      (L.flatten.drop sp.start).take sp.len = L[i] := by
  simpa using read_spansFrom [] L i hi

/-! ## The data's tuples -/

theorem allForms_eq : allForms = (allTuples.map fun x ↦ x.2.2).flatten := by
  simp [allForms, List.flatMap]

theorem tuples_eq :
    tuples = spansFrom 0 ((allTuples.map fun x ↦ x.2.2).map List.length) := by
  simp [tuples, Function.comp_def]

/-- **`tuple_forms` and `form_terms` read back every tuple.** -/
theorem tupleOf_eq (tu : Nat) (ht : tu < allTuples.length) :
    tupleOf tu = (allTuples[tu].2.2.map FormW.ofForm).toArray := by
  obtain ⟨sp, hsp, hlen, hread⟩ :=
    read_spans (allTuples.map fun x ↦ x.2.2) tu (by simpa using ht)
  rw [← tuples_eq] at hsp
  rw [← allForms_eq] at hread
  simp only [List.getElem_map] at hlen hread
  rw [tupleOf, hsp]
  have hle : sp.len ≤ allForms.length - sp.start := by
    have h3 : ((allForms.drop sp.start).take sp.len).length = sp.len := by
      rw [hread, hlen]
    rw [← h3, List.length_take, List.length_drop]
    exact Nat.min_le_right _ _
  apply Array.ext'
  rw [← hread]
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop,
    formAt]
  rw [List.getElem?_eq_getElem (by omega), Option.map_some, Option.getD_some]

/-! ## The blocks -/

theorem blocks_map (h r : Array Nat) (side : Nat) :
    (blocks side).map (blockW h r) = (allTuples.filter (·.2.1 == side)).map (tupleBlock h r) := by
  have hz : ∀ x ∈ allTuples.zipIdx, blockW h r ⟨x.1.1, x.2⟩ = tupleBlock h r x.1 := by
    intro x hx
    rw [List.mem_zipIdx_iff_getElem?] at hx
    obtain ⟨hlt, hx⟩ := List.getElem?_eq_some_iff.mp hx
    simp only [blockW, tupleBlock, tupleOf_eq _ hlt, hx]
  rw [blocks, List.map_map, Function.comp_def]
  rw [List.map_congr_left (fun x hx ↦ hz x (List.mem_of_mem_filter hx))]
  rw [show (fun x : (Nat × Nat × List Form) × Nat ↦ tupleBlock h r x.1) =
    tupleBlock h r ∘ Prod.fst from rfl, ← List.map_map]
  congr 1
  rw [show (fun x : (Nat × Nat × List Form) × Nat ↦ x.1.2.1 == side) =
    (fun x : Nat × Nat × List Form ↦ x.2.1 == side) ∘ Prod.fst from rfl, ← List.filter_map,
    List.zipIdx_map_fst]

/-- **The bus blocks are the data's**: `busBlocks h r` is `PUSH_BLOCKS`, `PULL_BLOCKS` and
`COUNT_BLOCKS`, each block at its owner's height and rows (`blockW`). -/
theorem busBlocks_eq (h r : Array Nat) :
    NativeVm.Model.busBlocks h r = ((pushBlocks.map (blockW h r)).toArray, (pullBlocks.map (blockW h r)).toArray,
      (countBlocks.map (blockW h r)).toArray) := by
  simp only [pushBlocks, pullBlocks, countBlocks, blocks_map]
  simp only [NativeVm.Model.busBlocks, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> apply Array.ext' <;>
    simp [allTuples, List.filter_flatMap, List.filter_map, Function.comp_def, tuplesOf, tupleBlock,
      List.map_flatMap, tablesW, countCols_eq, List.flatMap_map]
  all_goals
    congr 1
    first
      | done
      | funext t
        simp only [TableW.ofTable, Array.toList_map, List.map_map]
        apply List.map_congr_left
        intro x _
        simp

end

end NativeRustcVm.Bus
