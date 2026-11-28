/-
  LeanVM.Prover.Complete.Link.ColumnFold

  The row rounds' tables once bound: each table's value is its multilinear extension at its row
  point, its corner the factors of the rounds past its height, and a functional table of a
  pointer column is the functional of the column's bit-slices.
-/

module

public import LeanVM.Prover.Complete.Link.Fields
public import LeanVM.Facts.Hotwire

/-!
# The bound tables

* `at_foldl`: a sum of products bound at `pt` reads each table's multilinear extension there;
* `foldl_rowFold_ofFn`, `foldl_rowTableFold`: after the row rounds at `χ`, a table of height `h`
  is bound at `χ.take h`, its corner `Π (1 + x)` over `χ.drop h`;
* `mleA_eq_mle`: the array evaluation is `mle`;
* `mleA_functionalTable`: the functional table of a column's words, at the row point, is the
  functional applied to the column's `64` bit-slices there (`Functionals.values`), each functional
  linear in the bits, for a table no longer than its chunk's one-hot block, inside the word.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open LeanVM.Protocol.Hotwire Finset

/-! ## Sums of products, bound -/

theorem foldl_foldPairsA_empty : ∀ pt : List E, pt.foldl (fun t x ↦ foldPairsA x t) #[] = #[]
  | [] => rfl
  | x :: pt => by
    rw [List.foldl_cons, show foldPairsA x #[] = #[] by simp [foldPairsA]]
    exact foldl_foldPairsA_empty pt

theorem foldl_fold_tables : ∀ (pt : List E) (P : Prods),
    (pt.foldl Prods.fold P).tables = P.tables.map (fun t ↦ pt.foldl (fun t x ↦ foldPairsA x t) t)
  | [], P => by simp
  | x :: pt, P => by
    rw [List.foldl_cons, foldl_fold_tables pt (P.fold x)]
    simp only [Prods.fold, Array.map_map]
    rfl

/-- **A sum of products bound at `pt` reads each table's extension there.** -/
theorem at_foldl (pt : List E) (P : Prods) (f : ℕ) :
    (pt.foldl Prods.fold P).at f = mleA (P.tables.getD f #[]) pt := by
  unfold Prods.at mleA
  rw [foldl_fold_tables]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases P.tables[f]? with
  | none => simp only [Option.map_none, Option.getD_none]; rw [foldl_foldPairsA_empty]
  | some t => rfl

theorem foldl_rowTableFold : ∀ (chi : List E) (rt : RowTable), rt.bound ≤ rt.height →
    chi.foldl rowTableFold rt =
      { rt with prods := (chi.take (rt.height - rt.bound)).foldl Prods.fold rt.prods
                bound := rt.bound + min (rt.height - rt.bound) chi.length
                corner := rt.corner * (((chi.drop (rt.height - rt.bound)).map (1 + ·)).prod) }
  | [], rt, _ => by cases rt; simp
  | x :: chi, rt, hb => by
    rw [List.foldl_cons]
    by_cases hlt : rt.bound < rt.height
    · have e : rowTableFold rt x = { rt with prods := rt.prods.fold x, bound := rt.bound + 1 } := by
        simp [rowTableFold, hlt]
      rw [e, foldl_rowTableFold chi _ (by simp only; omega)]
      obtain ⟨k, hk⟩ : ∃ k, rt.height - rt.bound = k + 1 := ⟨rt.height - rt.bound - 1, by omega⟩
      cases rt
      simp only at hk ⊢
      rw [hk, show _ - (_ + 1) = k by omega]
      simp only [List.take_succ_cons, List.foldl_cons, List.drop_succ_cons, List.length_cons,
        RowTable.mk.injEq, true_and, and_true]
      omega
    · have e : rowTableFold rt x = { rt with corner := rt.corner * (1 + x) } := by
        simp [rowTableFold, hlt]
      rw [e, foldl_rowTableFold chi _ (by simp only; omega)]
      have h0 : rt.height - rt.bound = 0 := by omega
      cases rt
      simp only at h0 ⊢
      rw [h0]
      simp only [List.take_zero, List.foldl_nil, List.drop_zero, List.map_cons, List.prod_cons,
        Nat.zero_min, add_zero, RowTable.mk.injEq, true_and]
      refine ⟨?_, ?_⟩ <;> first | ring | trivial

theorem rowFold_ofFn {n : ℕ} (f : Fin n → RowTable) (x : E) :
    rowFold (Array.ofFn f) x = Array.ofFn fun t ↦ rowTableFold (f t) x := by
  simp only [rowFold, Array.map_ofFn]
  rfl

theorem foldl_rowFold_ofFn : ∀ (chi : List E) {n : ℕ} (f : Fin n → RowTable),
    chi.foldl rowFold (Array.ofFn f) = Array.ofFn fun t ↦ chi.foldl rowTableFold (f t)
  | [], _, _ => rfl
  | x :: chi, _, f => by
    rw [List.foldl_cons, rowFold_ofFn, foldl_rowFold_ofFn chi]
    rfl

/-! ## Multilinear extensions of arrays -/

theorem mleA_eq_mle (t : Array E) (pt : List E) (h : t.size = 2 ^ pt.length) :
    mleA t pt = mle pt (fun u ↦ t.getD u 0) := by
  rw [Keccak.mleA_eq, multilinearEval_eq_mle _ _ (by simpa using h)]
  simp

theorem eqTable_getD_eqAt (pt : List E) (u : ℕ) :
    (eqTable pt).getD u 0 = if u < 2 ^ pt.length then eqAt pt u else 0 := by
  rw [Keccak.getD_toList, Keccak.toList_eqTable, eqKernel_getD]

/-! ## The functionals, linear in the bits -/

theorem sumE_eq_sum (l : List E) : sumE l = l.sum := by
  rw [sumE, foldl_add_eq, zero_add]

theorem sum_map_zipIdx_ite (q : ℕ → Prop) [DecidablePred q] :
    ∀ (l : List E) (n : ℕ), ((l.zipIdx n).map fun x ↦ if q x.2 then x.1 else 0).sum =
      ∑ v ∈ range l.length, if q (n + v) then l.getD v 0 else 0
  | [], _ => by simp
  | a :: l, n => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_map_zipIdx_ite q l (n + 1),
      List.length_cons, sum_range_succ']
    simp only [add_zero, List.getD_cons_zero, List.getD_cons_succ]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun v _ ↦ ?_
    rw [show n + 1 + v = n + (v + 1) by omega]

theorem sumE_filter_map (L : List (E × ℕ)) (p : E × ℕ → Bool) :
    sumE ((L.filter p).map (·.1)) = (L.map fun x ↦ if p x then x.1 else 0).sum := by
  rw [sumE_eq_sum]
  induction L with
  | nil => rfl
  | cons a L ih =>
    by_cases h : p a
    · simp [h, ih]
    · simp [h, ih]

theorem shiftRight_mod_two_eq_ite (x n : ℕ) : (x >>> n) % 2 = if x.testBit n then 1 else 0 := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ n) with h | h
  · simp [Nat.one_and_eq_mod_two, h]
  · simp [Nat.one_and_eq_mod_two, h]

theorem getD_drop' (l : List E) (n v : ℕ) : (l.drop n).getD v 0 = l.getD (n + v) 0 := by
  simp [List.getD_eq_getElem?_getD]

/-- A chunk's functional at a word: the table summed over the chunk's set bits. -/
theorem evalChunk_eq (chunks : Chunks) (table : List E) (word i : ℕ) :
    evalChunk chunks table word i = ∑ v ∈ range table.length,
      if (chunks.bits word i >>> v) % 2 = 1 then table.getD v 0 else 0 := by
  unfold evalChunk
  rw [sumE_filter_map]
  have := sum_map_zipIdx_ite (fun v ↦ (chunks.bits word i >>> v) % 2 = 1) table 0
  simp only [zero_add] at this
  rw [← this]
  refine congrArg List.sum (List.map_congr_left fun x _ ↦ ?_)
  obtain ⟨a, v⟩ := x
  simp [shiftRight_mod_two_eq_ite]

/-- A chunk's indicator bit `v` is the word's bit `wordShift + v`. -/
theorem bits_bit (chunks : Chunks) (word i v : ℕ) (hv : v < 2 ^ chunks.widths.getD i 0) :
    (chunks.bits word i >>> v) % 2 = (word >>> (chunks.wordShifts.getD i 0 + v)) % 2 := by
  rw [shiftRight_mod_two_eq_ite, shiftRight_mod_two_eq_ite]
  unfold Chunks.bits
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp only [hv, decide_true, Bool.true_and]

theorem sumE_zipWith (a b : List E) (h : a.length ≤ b.length) :
    sumE (List.zipWith (· * ·) a b) = ∑ v ∈ range a.length, a.getD v 0 * b.getD v 0 := by
  rw [sumE_eq_sum]
  induction a generalizing b with
  | nil => simp
  | cons x a ih =>
    cases b with
    | nil => simp at h
    | cons y b =>
      rw [List.zipWith_cons_cons, List.sum_cons, ih b (by simpa using h), List.length_cons,
        sum_range_succ']
      simp [add_comm]

theorem length_columnSlices (words : Array K) (pt : List E) : (columnSlices words pt).length = 64 := by
  simp [columnSlices]

/-- A pointer column's slice `b` at the row point: the extension of its bit `b`. -/
theorem getD_columnSlices (words : Array K) (pt : List E) (hw : words.size = 2 ^ pt.length) {b : ℕ}
    (hb : b < 64) : (columnSlices words pt).getD b 0 =
      ∑ u ∈ range (2 ^ pt.length), if (kToNat (words.getD u 0) >>> b) % 2 = 1 then eqAt pt u else 0 := by
  simp only [columnSlices, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hb,
    Option.map_some, Option.getD_some]
  rw [Keccak.sumRange_eq, hw]
  refine sum_congr rfl fun u hu ↦ ?_
  rw [eqTable_getD_eqAt, ite_eq_left (mem_range.mp hu)]

/-- **A functional table at the row point is the functional of the column's bit-slices.** -/
theorem mleA_functionalTable (chunks : Chunks) (words : Array K) (pt : List E)
    (hw : words.size = 2 ^ pt.length) (i : ℕ) (table : List E)
    (h1 : table.length ≤ 2 ^ chunks.widths.getD i 0)
    (h2 : chunks.wordShifts.getD i 0 + table.length ≤ 64) :
    mleA (functionalTable chunks words (i, table)) pt =
      sumE (List.zipWith (· * ·) table ((columnSlices words pt).drop (chunks.wordShifts.getD i 0))) := by
  rw [mleA_eq_mle _ _ (by rw [size_functionalTable, hw]),
    sumE_zipWith _ _ (by rw [List.length_drop, length_columnSlices]; omega)]
  unfold mle
  beta_reduce
  have hget : ∀ u ∈ range (2 ^ pt.length), (functionalTable chunks words (i, table)).getD u 0 =
      evalChunk chunks table (kToNat (words.getD u 0)) i := by
    intro u hu
    have hu' : u < words.size := by rw [hw]; exact mem_range.mp hu
    simp [functionalTable, Array.getD_eq_getD_getElem?, hu']
  rw [sum_congr rfl fun u hu ↦ by rw [hget u hu, evalChunk_eq]]
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun v hv ↦ ?_
  have hv' := mem_range.mp hv
  rw [getD_drop', getD_columnSlices words pt hw (by omega), mul_sum]
  refine sum_congr rfl fun u _ ↦ ?_
  rw [bits_bit chunks _ i v (by omega)]
  split_ifs <;> ring

end LeanVM.Prover.Complete

end
