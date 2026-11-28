/-
  LeanVM.Prover.Complete.Link.ColumnTerms

  The pointer-column rounds' sum, column by column: its cube sum is every column's part plus the
  base terms' total.
-/

module

public import LeanVM.Prover.Complete.Link.ColumnFold
public import LeanVM.Facts.Stack

/-!
# The pointer columns' terms

`termsVal ev terms`: the terms' value at an evaluation `ev` of the tables; `Prods.value` and
`termsAt` are such values (`value_eq_termsVal`, `termsAt_eq_termsVal`). `colTerm`: one pointer
column's part of `columnProds`, `(c·D_0 + Σ_s c_s·T_s)·Π_{i ≥ 1} D_i + Σ_i e_i·(D_i·D̄_i + π_i)` from
its values. `cubeSum_columnProds`: the pointer-column rounds' cube sum is the columns' parts plus
the base terms' total.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open Finset

/-! ## Terms at an evaluation of the tables -/

/-- A term's value where table `f` reads `ev f`. -/
def termVal (ev : ℕ → E) (cf : E × Array ℕ) : E := cf.1 * (cf.2.toList.map ev).prod

/-- The terms' value where table `f` reads `ev f`. -/
def termsVal (ev : ℕ → E) (terms : Array (E × Array ℕ)) : E := (terms.toList.map (termVal ev)).sum

theorem foldl_mul_eq_prod (g : ℕ → E) :
    ∀ (l : List ℕ) (c : E), l.foldl (fun v f ↦ v * g f) c = c * (l.map g).prod
  | [], c => by simp
  | f :: l, c => by
    rw [List.foldl_cons, foldl_mul_eq_prod g l, List.map_cons, List.prod_cons]
    ring

theorem foldl_add_map {α : Type} (h : α → E) :
    ∀ (l : List α) (a : E), l.foldl (fun acc x ↦ acc + h x) a = a + (l.map h).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, foldl_add_map h l, List.map_cons, List.sum_cons]
    ring

theorem termsVal_eq_foldl (ev : ℕ → E) (terms : Array (E × Array ℕ)) :
    terms.foldl (fun acc cf ↦ acc + cf.2.foldl (fun v f ↦ v * ev f) cf.1) 0 = termsVal ev terms := by
  rw [← Array.foldl_toList, foldl_add_map, zero_add, termsVal]
  congr 1
  refine List.map_congr_left fun cf _ ↦ ?_
  rw [← Array.foldl_toList, foldl_mul_eq_prod]
  rfl

theorem value_eq_termsVal (P : Prods) : P.value = termsVal P.at P.terms :=
  termsVal_eq_foldl _ _

theorem termsAt_eq_termsVal (P : Prods) (u : ℕ) :
    termsAt P u = termsVal (fun f ↦ (P.tables.getD f #[]).getD u 0) P.terms :=
  termsVal_eq_foldl _ _

theorem termsVal_push (ev : ℕ → E) (terms : Array (E × Array ℕ)) (cf : E × Array ℕ) :
    termsVal ev (terms.push cf) = termsVal ev terms + termVal ev cf := by
  simp [termsVal]

theorem termsVal_foldl {α : Type} (ev : ℕ → E) (f : Array (E × Array ℕ) → α → Array (E × Array ℕ))
    (δ : α → E) (hf : ∀ T x, termsVal ev (f T x) = termsVal ev T + δ x) :
    ∀ (L : List α) (T : Array (E × Array ℕ)), termsVal ev (L.foldl f T) = termsVal ev T + (L.map δ).sum
  | [], T => by simp
  | x :: L, T => by
    rw [List.foldl_cons, termsVal_foldl ev f δ hf L, hf, List.map_cons, List.sum_cons]
    ring

theorem sum_flatMap_pair {α : Type} (x y : α → E) :
    ∀ L : List α, (L.flatMap fun i ↦ [x i, y i]).sum = (L.map fun i ↦ x i + y i).sum
  | [] => rfl
  | i :: L => by
    rw [List.flatMap_cons, List.sum_append, sum_flatMap_pair x y L, List.map_cons, List.sum_cons]
    simp

theorem sum_map_range (n : ℕ) (f : ℕ → E) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-! ## One column's part -/

/-- **A pointer column's part of the pointer-column rounds' sum**, from its values `v`:
`(c·v_0 + Σ_s c_s·v_{2d+s})·Π_{1 ≤ i < d} v_i + Σ_i e_i·(v_i·v_{d+i} + π_i)`. -/
def colTerm (d maxShift : ℕ) (mirrors : List E) (c : ColumnAt) : E :=
  let v := fun j ↦ c.values.getD j 0
  let rest := ((List.range (d - 1)).map fun i ↦ v (1 + i)).prod
  c.coef * v 0 * rest +
    ((List.range maxShift).map fun s ↦ c.shifts.getD s 0 * v (2 * d + s) * rest).sum +
    ((List.range d).map fun i ↦
      c.certs.getD i 0 * v i * v (d + i) + mirrors.getD i 0 * c.certs.getD i 0).sum

theorem colTerm_default (d maxShift : ℕ) (mirrors : List E) :
    colTerm d maxShift mirrors default = 0 := by
  have h : (default : ColumnAt) = ⟨0, [], [], [], []⟩ := rfl
  simp [colTerm, h]

/-! ## The pointer-column rounds' tables -/

section Tables

variable (d M : ℕ) (mirrors : List E) (columns : List ColumnAt) (qVars : ℕ) (base : E) {q : ℕ}

theorem columnProds_tables_toList :
    (columnProds d M mirrors columns qVars base).tables.toList =
      (Array.ofFn (n := 2 ^ qVars) fun q ↦ (columns.getD q.val default).coef) ::
        (((List.range (2 * d + M)).map fun j ↦
            Array.ofFn (n := 2 ^ qVars) fun q ↦ (columns.getD q.val default).values.getD j 0) ++
          (((List.range M).map fun s ↦
              Array.ofFn (n := 2 ^ qVars) fun q ↦ (columns.getD q.val default).shifts.getD s 0) ++
            (((List.range d).map fun i ↦
                Array.ofFn (n := 2 ^ qVars) fun q ↦ (columns.getD q.val default).certs.getD i 0) ++
              [(Array.replicate (2 ^ qVars) (0 : E)).set! 0 base]))) := by
  simp [columnProds]

theorem getD_ofFn_getD (f : ColumnAt → E) (hq : q < 2 ^ qVars) :
    (Array.ofFn (n := 2 ^ qVars) fun q ↦ f (columns.getD q.val default)).getD q 0 =
      f (columns.getD q default) := by
  simp [Array.getD_eq_getD_getElem?, hq]

theorem getD_map_range_arr (n j : ℕ) (g : ℕ → Array E) (hj : j < n) :
    ((List.range n).map g).getD j #[] = g j := by
  simp [List.getD_eq_getElem?_getD, hj]

/-- The table of `columnProds` at `f`, read at the column `q`. -/
noncomputable def colTab (q f : ℕ) : E :=
  (((columnProds d M mirrors columns qVars base).tables.getD f #[]).getD q 0)

theorem colTab_coef : colTab d M mirrors columns qVars base q 0 =
    if q < 2 ^ qVars then (columns.getD q default).coef else 0 := by
  unfold colTab
  rw [Keccak.getD_toList (columnProds d M mirrors columns qVars base).tables, columnProds_tables_toList, List.getD_cons_zero]
  split_ifs with hq
  · exact getD_ofFn_getD columns qVars (fun c : ColumnAt ↦ c.coef) hq
  · simp [Array.getD_eq_getD_getElem?, hq]

theorem colTab_value (hq : q < 2 ^ qVars) {j : ℕ} (hj : j < 2 * d + M) :
    colTab d M mirrors columns qVars base q (1 + j) = (columns.getD q default).values.getD j 0 := by
  unfold colTab
  rw [Keccak.getD_toList (columnProds d M mirrors columns qVars base).tables, columnProds_tables_toList, Nat.add_comm 1 j, List.getD_cons_succ,
    List.getD_append _ _ _ _ (by simpa using hj), getD_map_range_arr _ _ _ hj]
  exact getD_ofFn_getD columns qVars (fun c : ColumnAt ↦ c.values.getD j 0) hq

theorem colTab_shift (hq : q < 2 ^ qVars) {s : ℕ} (hs : s < M) :
    colTab d M mirrors columns qVars base q (1 + (2 * d + M) + s) =
      (columns.getD q default).shifts.getD s 0 := by
  unfold colTab
  rw [Keccak.getD_toList (columnProds d M mirrors columns qVars base).tables, columnProds_tables_toList, show 1 + (2 * d + M) + s = (2 * d + M + s) + 1 by
    omega, List.getD_cons_succ, List.getD_append_right _ _ _ _ (by simp),
    List.getD_append _ _ _ _ (by simp; omega)]
  simp only [List.length_map, List.length_range, Nat.add_sub_cancel_left]
  rw [getD_map_range_arr _ _ _ hs]
  exact getD_ofFn_getD columns qVars (fun c : ColumnAt ↦ c.shifts.getD s 0) hq

theorem colTab_cert (hq : q < 2 ^ qVars) {i : ℕ} (hi : i < d) :
    colTab d M mirrors columns qVars base q (1 + (2 * d + M) + M + i) =
      (columns.getD q default).certs.getD i 0 := by
  unfold colTab
  rw [Keccak.getD_toList (columnProds d M mirrors columns qVars base).tables, columnProds_tables_toList,
    show 1 + (2 * d + M) + M + i = (2 * d + M + M + i) + 1 by omega, List.getD_cons_succ,
    List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega),
    List.getD_append _ _ _ _ (by simp; omega)]
  simp only [List.length_map, List.length_range,
    show 2 * d + M + M + i - (2 * d + M) - M = i by omega]
  rw [getD_map_range_arr _ _ _ hi]
  exact getD_ofFn_getD columns qVars (fun c : ColumnAt ↦ c.certs.getD i 0) hq

theorem colTab_base (hq : q < 2 ^ qVars) :
    colTab d M mirrors columns qVars base q (1 + (2 * d + M) + M + d) = if q = 0 then base else 0 := by
  unfold colTab
  rw [Keccak.getD_toList (columnProds d M mirrors columns qVars base).tables, columnProds_tables_toList,
    show 1 + (2 * d + M) + M + d = (2 * d + M + M + d) + 1 by omega, List.getD_cons_succ,
    List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega),
    List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_map, List.length_range,
    show 2 * d + M + M + d - (2 * d + M) - M - d = 0 by omega, List.getD_cons_zero]
  have hpos : 0 < 2 ^ qVars := Nat.pos_of_ne_zero (pow_ne_zero _ two_ne_zero)
  by_cases h0 : q = 0
  · subst h0
    simp [Array.getD_eq_getD_getElem?, hpos]
  · simp [Array.getD_eq_getD_getElem?, h0, Ne.symm h0, hq]

end Tables

/-- **The pointer-column rounds' sum at a column `q`**: its part, and the base terms' total at
`q = 0`. -/
theorem termsAt_columnProds (d M : ℕ) (hd : 1 ≤ d) (mirrors : List E) (columns : List ColumnAt)
    (qVars : ℕ) (base : E) {q : ℕ} (hq : q < 2 ^ qVars) :
    termsAt (columnProds d M mirrors columns qVars base) q =
      colTerm d M mirrors (columns.getD q default) + if q = 0 then base else 0 := by
  rw [termsAt_eq_termsVal]
  have ev : (fun f ↦ ((columnProds d M mirrors columns qVars base).tables.getD f #[]).getD q 0) =
      colTab d M mirrors columns qVars base q := rfl
  rw [ev]
  set c := columns.getD q default
  set g := colTab d M mirrors columns qVars base q with hg
  have hv : ∀ j < 2 * d + M, g (1 + j) = c.values.getD j 0 := fun j hj ↦ by
    rw [hg]; exact colTab_value _ _ _ _ _ _ hq hj
  have hrest : (((List.range (d - 1)).map (1 + 1 + ·)).map g).prod =
      ((List.range (d - 1)).map fun i ↦ c.values.getD (1 + i) 0).prod := by
    rw [List.map_map]
    refine congrArg List.prod (List.map_congr_left fun i hi ↦ ?_)
    have := List.mem_range.mp hi
    simp only [Function.comp, show 1 + 1 + i = 1 + (1 + i) by omega]
    exact hv _ (by omega)
  simp only [termsVal, columnProds, Array.toList_append,
    List.map_append, List.sum_append, List.map_map, List.map_flatMap, List.map_cons, List.map_nil,
    Function.comp_def]
  rw [sum_flatMap_pair]
  unfold colTerm
  simp only [termVal, List.cons_append, List.nil_append, List.map_cons, List.sum_cons, List.sum_nil,
    List.prod_cons, Array.toList_append,
    List.map_nil, List.prod_nil]
  have h0 : g 0 = c.coef := by rw [hg, colTab_coef, ite_eq_left hq]
  have hb : g (1 + (2 * d + M) + M + d) = if q = 0 then base else 0 := by
    rw [hg]; exact colTab_base _ _ _ _ _ _ hq
  have e1 : ((List.range M).map fun x ↦ 1 * (g (1 + (2 * d + M) + x) *
      (g (1 + 2 * d + x) * (((List.range (d - 1)).map (fun x ↦ 1 + 1 + x)).map g).prod))).sum =
      ((List.range M).map fun s ↦ c.shifts.getD s 0 * c.values.getD (2 * d + s) 0 *
        ((List.range (d - 1)).map fun i ↦ c.values.getD (1 + i) 0).prod).sum := by
    refine congrArg List.sum (List.map_congr_left fun s hs ↦ ?_)
    have hs' := List.mem_range.mp hs
    rw [hrest, show g (1 + (2 * d + M) + s) = c.shifts.getD s 0 by
      rw [hg]; exact colTab_shift _ _ _ _ _ _ hq hs', show 1 + 2 * d + s = 1 + (2 * d + s) by omega,
      hv _ (by omega)]
    ring
  have e2 : ((List.range d).map fun i ↦ 1 * (g (1 + (2 * d + M) + M + i) * (g (1 + i) *
      (g (1 + d + i) * 1))) + mirrors.getD i 0 * (g (1 + (2 * d + M) + M + i) * 1)).sum =
      ((List.range d).map fun i ↦ c.certs.getD i 0 * c.values.getD i 0 * c.values.getD (d + i) 0 +
        mirrors.getD i 0 * c.certs.getD i 0).sum := by
    refine congrArg List.sum (List.map_congr_left fun i hi ↦ ?_)
    have hi' := List.mem_range.mp hi
    rw [show g (1 + (2 * d + M) + M + i) = c.certs.getD i 0 by
      rw [hg]; exact colTab_cert _ _ _ _ _ _ hq hi', hv i (by omega),
      show 1 + d + i = 1 + (d + i) by omega, hv (d + i) (by omega)]
    ring
  rw [e1, e2, hrest, h0, hv 0 (by omega), hb]
  ring

theorem sum_range_getD {α : Type} [Inhabited α] (f : α → E) :
    ∀ l : List α, ∑ q ∈ range l.length, f (l.getD q default) = (l.map f).sum
  | [] => by simp
  | a :: l => by
    rw [List.length_cons, sum_range_succ', List.map_cons, List.sum_cons, ← sum_range_getD f l]
    simp [add_comm]

/-- **The pointer-column rounds' cube sum**: every column's part, and the base terms' total. -/
theorem cubeSum_columnProds (d M : ℕ) (hd : 1 ≤ d) (mirrors : List E) (columns : List ColumnAt)
    (qVars : ℕ) (base : E) (hlen : columns.length ≤ 2 ^ qVars) :
    cubeSum (2 ^ qVars) (columnProds d M mirrors columns qVars base) =
      (columns.map (colTerm d M mirrors)).sum + base := by
  have hpos : 0 < 2 ^ qVars := Nat.pos_of_ne_zero (pow_ne_zero _ two_ne_zero)
  unfold cubeSum
  rw [sum_congr rfl fun q hq ↦ termsAt_columnProds d M hd mirrors columns qVars base
    (mem_range.mp hq), sum_add_distrib, sum_ite_eq' (range (2 ^ qVars)) 0, ite_eq_left (mem_range.mpr hpos),
    ← sum_range_add_sum_Ico _ hlen, sum_range_getD]
  rw [sum_eq_zero fun q hq ↦ by
    rw [List.getD_eq_default _ _ (mem_Ico.mp hq).1, colTerm_default], add_zero]

end LeanVM.Prover.Complete

end
