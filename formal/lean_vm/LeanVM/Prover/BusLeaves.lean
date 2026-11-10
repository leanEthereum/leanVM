/-
  LeanVM.Prover.BusLeaves

  The bus phase's leaves, filled into arrays from the instance's columns
  (`Statement/Prover/Bus.lean`), are the specification's honest leaves (`pushLeaves`,
  `pullLeaves`, `countLeaves`).
-/

module

public import Statement.Prover.Bus
public import LeanVM.Prover.Mle
public import LeanVM.Protocol.EndToEnd.Complete.Bus

/-!
# The leaves

The instance's columns are given as arrays `cols`, indexed by the verifier's global column number:
`cols.getD (refCol c) #[]` is column `c`'s table (`ColsOk`).

* `toList_stackA`: a side's leaves are `stackLeaves` of its blocks' lists;
* `getD_powsA`: the running powers;
* `rowOf_eq`: a table's row read off the arrays is `rowAt`;
* `toList_tableTabA`, `toList_memTabA_push/pull`, `toList_bcTabA_push/pull`: the blocks;
* `toList_pushLeaves`, `toList_pullLeaves`, `toList_countLeaves`: **the three sides' leaves are
  the specification's**, at the verifier's layout.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Whir.Complete LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol (Column)

@[expose] public section

/-- **The columns as arrays**: entry `refCol c` of `cols` is column `c`'s table. -/
def ColsOk (prog : LeanIsaProgram) (s : Sizes) (q : Column (leanIsaμ prog s)) (cols : Array
    (Array K)) :
    Prop :=
  ∀ c : Col, cols.getD (refCol c) #[] = ((inst prog s).column q c).values.toArray

/-! ## Arrays and lists -/

/-- An array of a function of the indices is that function over the range. -/
theorem toList_ofFn_eq_map {α : Type} {n : ℕ} (f : Fin n → α) (g : ℕ → α)
    (h : ∀ i : Fin n, f i = g i) : (Array.ofFn f).toList = (List.range n).map g := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [Array.toList_ofFn, List.getElem_ofFn, List.getElem_map, List.getElem_range]
  exact h ⟨i, by simpa using h1⟩

/-- A vector's array read in range. -/
theorem getD_toArray_vec {α : Type} {n : ℕ} (v : Vector α n) (i : ℕ) (h : i < n) (d : α) :
    v.toArray.getD i d = v.get ⟨i, h⟩ := by
  simp [Array.getD_eq_getD_getElem?, h, Vector.get]

theorem ofK_one : ofK (1 : K) = 1 := map_one (algebraMap K E)

/-- A list lifted to `E`, read anywhere. -/
theorem getD_map_ofK (l : List K) (i : ℕ) : (l.map ofK).getD i 0 = ofK (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

/-! ## Stacking -/

theorem toList_foldl_append {β : Type} (tab : β → Array E) : ∀ (l : List β) (acc : Array E),
    (l.foldl (fun acc b ↦ acc ++ tab b) acc).toList = acc.toList ++ l.flatMap fun b ↦ (tab b).toList
  | [], acc => by simp
  | b :: l, acc => by
    rw [List.foldl_cons, toList_foldl_append tab l, Array.toList_append, List.flatMap_cons,
      List.append_assoc]

/-- **A side's leaves** are `stackLeaves` of its blocks' lists. -/
theorem toList_stackA (sizes : List ℕ) (tab : ℕ → Array E) (D : ℕ) :
    (stackA sizes tab D).toList = stackLeaves sizes (fun b ↦ (tab b).toList) D := by
  have hb := toList_foldl_append tab (blockOrder sizes) #[]
  simp only [List.nil_append] at hb
  rw [stackA, Array.toList_append, hb, Array.toList_replicate, ← Array.length_toList, hb]
  rfl

theorem flatMap_congr' {f g : ℕ → List E} : ∀ {l : List ℕ}, (∀ b ∈ l, f b = g b) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a (by simp),
      flatMap_congr' fun b hb ↦ h b (by simp [hb])]

/-- Leaves of blocks equal on the blocks are equal. -/
theorem stackLeaves_congr {sizes : List ℕ} {tabs tabs' : ℕ → List E} (D : ℕ)
    (h : ∀ b < sizes.length, tabs b = tabs' b) :
    stackLeaves sizes tabs D = stackLeaves sizes tabs' D := by
  have hf : (stackOrder sizes).flatMap tabs = (stackOrder sizes).flatMap tabs' :=
    flatMap_congr' fun b hb ↦ h b (mem_stackOrder.mp hb)
  rw [stackLeaves, stackLeaves, hf]

/-! ## Powers -/

theorem powsA_spec (a : E) (c : ℕ) : ∀ n : ℕ,
    (Nat.fold n (fun _ _ (acc : Array E × E) ↦ (acc.1.push acc.2, acc.2 * a))
      (Array.emptyWithCapacity c, 1)).1.toList = (List.range n).map (a ^ ·) ∧
    (Nat.fold n (fun _ _ (acc : Array E × E) ↦ (acc.1.push acc.2, acc.2 * a))
      (Array.emptyWithCapacity c, 1)).2 = a ^ n
  | 0 => ⟨by simp, by simp⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := powsA_spec a c n
    simp only [Nat.fold_succ, Array.toList_push, h1, h2, List.range_succ, List.map_append,
      List.map_singleton, pow_succ]
    exact ⟨trivial, trivial⟩

/-- The running powers. -/
theorem getD_powsA (a : E) {n y : ℕ} (hy : y < n) : (powsA a n).getD y 0 = a ^ y := by
  rw [powsA, getD_toList, (powsA_spec a n n).1, List.getD_eq_getElem _ _ (by simpa using hy)]
  simp

/-- The running powers of `g`. -/
theorem getD_powsA_gen {n y : ℕ} (hy : y < n) : (powsA gen n).getD y 0 = Protocol.Verifier.gpow y :=
  getD_powsA gen hy

/-! ## The columns -/

section Cols

variable {prog : LeanIsaProgram} {s : Sizes} {q : Column (leanIsaμ prog s)} {cols : Array (Array K)}

/-- A cell of a column read off the arrays. -/
theorem cell_eq (hcols : ColsOk prog s q cols) (c : Col) {y : ℕ} (hy : y < 2 ^ kappa prog s c) :
    ofK ((cols.getD (refCol c) #[]).getD y 0) = (colList prog s q c).getD y 0 := by
  rw [hcols]
  exact (congrArg ofK (getD_toArray_vec ((inst prog s).column q c).values y hy 0)).trans
    (getD_colList prog s q c y hy).symm

/-- A column's extension, off the arrays. -/
theorem mleK_col (hcols : ColsOk prog s q cols) (c : Col) (z : List E) :
    mleK (cols.getD (refCol c) #[]) z = multilinearEval (colList prog s q c) z := by
  rw [mleK_eq, hcols, colList]
  rfl

/-- **A table's row read off the arrays** is the instance's row. -/
theorem rowOf_eq (hcols : ColsOk prog s q cols) (t : Fin 6) {x : ℕ} (hx : x < 2 ^ s.τ t) :
    busRowOf cols (globalColumnBases.getD t 0) (tables.getD t default).width x =
      rowAt prog s q t x := by
  have h := rowAt_eq prog s q t ⟨x, hx⟩
  simp only at h
  rw [h]
  funext i
  rw [rowVal, busRowOf]
  by_cases hi : i < width (opIdx t)
  · have hi' : i < (tables.getD t default).width := by rwa [← width_opIdx]
    simp only [hi, hi', ↓reduceDIte, ↓reduceIte]
    rw [← refCol_opIdx t ⟨i, hi⟩, hcols]
    exact congrArg ofK
      (getD_toArray_vec ((inst prog s).column q ⟨opIdx t, ⟨i, hi⟩⟩).values x hx 0)
  · have hi' : ¬ i < (tables.getD t default).width := by rwa [← width_opIdx]
    simp only [hi, hi', ↓reduceDIte, ↓reduceIte]

/-- **A table block's leaves.** -/
theorem toList_tableTabA (hcols : ColsOk prog s q cols) (β : E) (w : List E) (t : Fin 6)
    (cs : List Form) :
    (tableTabA cols β w ⟨s.τ t, s.rows t, cs, t⟩).toList =
      tableTab prog s q β w ⟨s.τ t, s.rows t, cs, t⟩ := by
  rw [tableTabA, tableTab]
  refine toList_ofFn_eq_map _ _ fun x ↦ ?_
  try dsimp only
  split_ifs
  · rw [blockVal, List.map_map, rowOf_eq hcols t x.isLt]
    rfl
  · rfl

/-- A block of a side owned by a table. -/
theorem toList_tableTabA_owned (hcols : ColsOk prog s q cols) (β : E) (w : List E)
    {blk : BusBlock} (hb : ∃ t : Fin 6, blk = ⟨s.τ t, s.rows t, blk.coordinates, t⟩) :
    (tableTabA cols β w blk).toList = tableTab prog s q β w blk := by
  obtain ⟨t, ht⟩ := hb
  rw [ht]
  exact toList_tableTabA hcols β w t _

theorem cols_memCol (hcols : ColsOk prog s q cols) (i : Fin 3) :
    cols.getD (i : ℕ) #[] = ((inst prog s).column q (memCol i)).values.toArray := by
  rw [← hcols, refCol_memCol]

/-- The memory block's leaves, `cnt` its counts. -/
theorem toList_memTabA (hcols : ColsOk prog s q cols) {N : ℕ} (hN : 2 ^ s.logMem ≤ N) (β : E)
    (w : List E) (cnt : ℕ → E) (cntL : List E)
    (hcnt : ∀ y < 2 ^ s.logMem, cnt y = cntL.getD y 0) :
    (memTabA cols s.logMem (powsA gen N) β w cnt).toList = memTab prog s q β w cntL := by
  rw [memTabA, memTab]
  refine toList_ofFn_eq_map _ _ fun y ↦ ?_
  have hy := y.isLt
  have hk : y.1 < 2 ^ kappa prog s (memCol 0) := hy
  rw [getD_powsA_gen (by omega), hcnt y hy, ← cell_eq hcols (memCol 0) hk,
    ← cell_eq hcols (memCol 1) hk, refCol_memCol, refCol_memCol]
  rfl

/-- The bytecode block's leaves, `cnt` its counts. -/
theorem toList_bcTabA {N : ℕ} (hN : 2 ^ prog.logSize ≤ N) (β : E) (w : List E) (cnt : ℕ → E)
    (cntL : List E) (hcnt : ∀ y < 2 ^ prog.logSize, cnt y = cntL.getD y 0) :
    (bcTabA (bytecodeWords prog).toArray prog.logSize (powsA gen N) β w cnt).toList =
      bcTab prog β w cntL := by
  rw [bcTabA, bcTab]
  refine toList_ofFn_eq_map _ _ fun y ↦ ?_
  have hy := y.isLt
  rw [getD_powsA_gen (by omega), hcnt y hy]
  simp only [getD_toList, getD_map_ofK]

end Cols

end
end LeanVM.Prover
