/-
  LeanVM.Prover.Complete.Link.TailRowAlg

  The algebra the link's row side rests on: forms evaluated, affine functions of a row commuting
  with the extension, the summand as a column's part, and the functionals linear in the slices.
-/

module

public import LeanVM.Prover.Complete.Link.TailFold
public import LeanVM.Prover.Complete.Link.OneHot

/-!
# The row side's algebra

* `evaluate_eq_sum`, `evaluate_addScaled`, `evaluate_congr`: a form's value is its monomials' sum,
  `addScaled` adds, and only the columns it reads count;
* `Affine F`: `F` of a weighted sum of rows, the weights summing to one, is the weighted sum of
  `F`; `affine_evaluate` for a form of degree at most one; `mleA_rows`: the extension of
  `u ↦ F (row u)` is `F` of the columns' extensions;
* `summand_eq_colTerm`: `Functionals.summand` is `colTerm` of its arguments;
* `termsVal_columnProds`: `columnProds`' terms at any evaluation of its tables are `colTerm` of the
  column the evaluation reads, plus its base;
* `getD_values_sum`: `Functionals.values` is linear in the slices.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open LeanVM.Protocol.Hotwire (eqAt sum_eqAt)
open Finset

/-! ## Forms -/

/-- A monomial's value. -/
def tailRowMono (col : ℕ → E) (m : List ℕ × E) : E := m.2 * (m.1.map col).prod

theorem evaluate_eq_sum (f : Form) (col : ℕ → E) :
    f.evaluate col = (f.terms.map (tailRowMono col)).sum := by
  unfold Form.evaluate
  rw [sumE_eq_sum]
  congr 1
  exact List.map_congr_left fun m _ ↦ foldl_mul_eq_prod col m.1 m.2

theorem sum_addTerm (col : ℕ → E) : ∀ (l : List (List ℕ × E)) (v : List ℕ) (c : E),
    ((addTerm l v c).map (tailRowMono col)).sum = (l.map (tailRowMono col)).sum + c * (v.map col).prod
  | [], v, c => by simp [addTerm, tailRowMono]
  | (m', c') :: rest, v, c => by
    simp only [addTerm]
    split_ifs with h
    · subst h
      simp only [List.map_cons, List.sum_cons, tailRowMono]
      ring
    · simp only [List.map_cons, List.sum_cons, sum_addTerm col rest v c]
      ring

theorem sum_foldl_addTerm (col : ℕ → E) (w : E) : ∀ (ts acc : List (List ℕ × E)),
    ((ts.foldl (fun acc t ↦ addTerm acc t.1 (w * t.2)) acc).map (tailRowMono col)).sum =
      (acc.map (tailRowMono col)).sum + w * (ts.map (tailRowMono col)).sum
  | [], acc => by simp
  | t :: ts, acc => by
    rw [List.foldl_cons, sum_foldl_addTerm col w ts, sum_addTerm, List.map_cons, List.sum_cons]
    simp only [tailRowMono]
    ring

theorem evaluate_addScaled (f g : Form) (w : E) (col : ℕ → E) :
    (f.addScaled g w).evaluate col = f.evaluate col + w * g.evaluate col := by
  rw [evaluate_eq_sum, evaluate_eq_sum, evaluate_eq_sum]
  exact sum_foldl_addTerm col w g.terms f.terms

theorem evaluate_empty (col : ℕ → E) : ({} : Form).evaluate col = 0 := by
  simp [Form.evaluate, sumE]

theorem evaluate_const (v : E) (col : ℕ → E) : (Form.const v).evaluate col = v := by
  simp [Form.evaluate, Form.const, sumE]

/-- **Only the columns a form reads count.** -/
theorem evaluate_congr {f : Form} {col col' : ℕ → E}
    (h : ∀ m ∈ f.terms, ∀ v ∈ m.1, col v = col' v) : f.evaluate col = f.evaluate col' := by
  rw [evaluate_eq_sum, evaluate_eq_sum]
  refine congrArg List.sum (List.map_congr_left fun m hm ↦ ?_)
  unfold tailRowMono
  rw [List.map_congr_left (h m hm)]

/-! ## Affine functions of a row -/

/-- `F` commutes with weighted sums of rows whose weights sum to one. -/
def Affine (F : (ℕ → E) → E) : Prop :=
  ∀ (N : ℕ) (w : ℕ → E) (rows : ℕ → ℕ → E), ∑ u ∈ range N, w u = 1 →
    ∑ u ∈ range N, w u * F (rows u) = F (fun c ↦ ∑ u ∈ range N, w u * rows u c)

theorem Affine.congr {F G : (ℕ → E) → E} (h : ∀ col, F col = G col) (hG : Affine G) : Affine F :=
  fun N w rows hw ↦ by simp only [h]; exact hG N w rows hw

theorem affine_const (a : E) : Affine fun _ ↦ a :=
  fun _ _ _ hw ↦ by rw [← sum_mul, hw, one_mul]

theorem affine_col (c : ℕ) : Affine fun col ↦ col c := fun _ _ _ _ ↦ rfl

theorem Affine.add {F G : (ℕ → E) → E} (hF : Affine F) (hG : Affine G) :
    Affine fun col ↦ F col + G col :=
  fun N w rows hw ↦ by simp only [mul_add, sum_add_distrib, hF N w rows hw, hG N w rows hw]

theorem Affine.mul_left {F : (ℕ → E) → E} (a : E) (hF : Affine F) : Affine fun col ↦ a * F col :=
  fun N w rows hw ↦ by
    show ∑ u ∈ range N, w u * (a * F (rows u)) = a * F _
    rw [← hF N w rows hw, mul_sum]
    exact sum_congr rfl fun _ _ ↦ by ring

theorem affine_sum {α : Type} (F : α → (ℕ → E) → E) :
    ∀ L : List α, (∀ a ∈ L, Affine (F a)) → Affine fun col ↦ (L.map fun a ↦ F a col).sum
  | [], _ => (affine_const 0).congr fun _ ↦ by simp
  | a :: L, h => ((h a List.mem_cons_self).add
      (affine_sum F L fun b hb ↦ h b (List.mem_cons_of_mem _ hb))).congr fun _ ↦ by simp

/-- A form of degree at most one is affine. -/
theorem affine_evaluate {f : Form} (h : ∀ m ∈ f.terms, m.1.length ≤ 1) :
    Affine fun col ↦ f.evaluate col := by
  refine Affine.congr (fun col ↦ evaluate_eq_sum f col) (affine_sum _ _ fun m hm ↦ ?_)
  obtain ⟨vs, c⟩ := m
  have hl := h _ hm
  match vs, hl with
  | [], _ => exact (affine_const c).congr fun _ ↦ by simp [tailRowMono]
  | [v], _ => exact ((affine_col v).mul_left c).congr fun _ ↦ by simp [tailRowMono]

/-- A row's value at `ofK`, summed under the equality weights. -/
noncomputable def rowSum (cols : Array (Array K)) (pt : List E) (c : ℕ) : E :=
  ∑ u ∈ range (2 ^ pt.length), eqAt pt u * rowValue cols u c

/-- **An affine function of the rows, extended, is the function of the columns' extensions.** -/
theorem mleA_rows {F : (ℕ → E) → E} (hF : Affine F) (cols : Array (Array K)) (pt : List E) :
    mleA (Array.ofFn (n := 2 ^ pt.length) fun u ↦ F (rowValue cols u.val)) pt =
      F (rowSum cols pt) := by
  rw [mleA_eq_sum _ _ (by simp)]
  unfold rowSum
  rw [← hF _ _ (fun u c ↦ rowValue cols u c) (sum_eqAt pt)]
  refine sum_congr rfl fun u hu ↦ ?_
  simp [Array.getD_eq_getD_getElem?, mem_range.mp hu]

theorem mleA_empty (pt : List E) : mleA #[] pt = 0 := by
  unfold mleA
  rw [foldl_foldPairsA_empty]
  rfl

theorem tailRow_getD_map_ofK (a : Array K) (u : ℕ) : (a.map ofK).getD u 0 = ofK (a.getD u 0) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[u]? with
  | none => exact (map_zero (algebraMap K E)).symm
  | some _ => rfl

/-- A column of `2^|pt|` rows, or none, summed under the weights: its extension. -/
theorem rowSum_eq_mleK (cols : Array (Array K)) (pt : List E) (c : ℕ)
    (h : (cols.getD c #[]).size = 2 ^ pt.length ∨ cols.getD c #[] = #[]) :
    rowSum cols pt c = mleK (cols.getD c #[]) pt := by
  unfold rowSum rowValue mleK
  rcases h with h | h
  · rw [mleA_eq_sum _ _ (by simpa using h)]
    refine sum_congr rfl fun u _ ↦ ?_
    rw [tailRow_getD_map_ofK]
  · rw [h]
    simp [mleA_empty]

/-! ## Products and sums of lists -/

theorem foldl_mul_eq (l : List E) : ∀ a : E, l.foldl (· * ·) a = a * l.prod := by
  induction l with
  | nil => intro a; simp
  | cons x l ih => intro a; rw [List.foldl_cons, ih, List.prod_cons]; ring

theorem tailRow_prodE_eq_prod (l : List E) : prodE l = l.prod := by
  unfold prodE
  rw [foldl_mul_eq, one_mul]

theorem getD_map_range_E (n j : ℕ) (f : ℕ → E) (hj : j < n) : ((List.range n).map f).getD j 0 = f j := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem sumE_zipWith_min : ∀ (a b : List E),
    sumE (List.zipWith (· * ·) a b) = ∑ v ∈ range (min a.length b.length), a.getD v 0 * b.getD v 0
  | [], b => by simp [sumE]
  | x :: a, [] => by simp [sumE]
  | x :: a, y :: b => by
    rw [List.zipWith_cons_cons, sumE_eq_sum, List.sum_cons, ← sumE_eq_sum, sumE_zipWith_min a b,
      List.length_cons, List.length_cons, Nat.add_min_add_right, sum_range_succ']
    simp [add_comm]

theorem prodE_drop_take (values : List E) (d : ℕ) (h : d ≤ values.length) :
    prodE ((values.drop 1).take (d - 1)) = ((List.range (d - 1)).map fun i ↦ values.getD (1 + i) 0).prod := by
  rw [tailRow_prodE_eq_prod]
  congr 1
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range,
    List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simp at h1; omega)]
  simp [Nat.add_comm]

/-! ## The summand -/

/-- **`Functionals.summand` is the part `colTerm` of its arguments.** -/
theorem summand_eq_colTerm (f : Functionals) (M : ℕ) (coef : E) (shifts values certs : List E)
    (hs : shifts.length = M) (hv : values.length = 2 * f.d + M) :
    f.summand coef shifts values certs = colTerm f.d M f.mirrors ⟨coef, shifts, values, certs, []⟩ := by
  unfold Functionals.summand colTerm
  dsimp only
  rw [prodE_drop_take _ _ (by omega), sumE_zipWith_min, List.length_drop, hs, hv,
    show min M (2 * f.d + M - 2 * f.d) = M by omega, sumE_eq_sum, sum_map_range, sum_map_range,
    sum_map_range]
  simp only [getD_drop']
  set R := (List.map (fun i ↦ values.getD (1 + i) 0) (List.range (f.d - 1))).prod
  rw [show ∑ i ∈ range f.d, certs.getD i 0 * (values.getD i 0 * values.getD (f.d + i) 0 +
      f.mirrors.getD i 0) = ∑ i ∈ range f.d, (certs.getD i 0 * values.getD i 0 *
      values.getD (f.d + i) 0 + f.mirrors.getD i 0 * certs.getD i 0) from
    sum_congr rfl fun _ _ ↦ by ring, ← sum_mul]
  ring

/-! ## The pointer-column rounds' terms at an evaluation -/

/-- **`columnProds`' terms at an evaluation `ev` of its tables**: the part of the column `ev`
reads, plus the base table's value. -/
theorem termsVal_columnProds (d M : ℕ) (hd : 1 ≤ d) (mirrors : List E) (columns : List ColumnAt)
    (qVars : ℕ) (base : E) (ev : ℕ → E) (c : ColumnAt) (h0 : ev 0 = c.coef)
    (hv : ∀ j < 2 * d + M, ev (1 + j) = c.values.getD j 0)
    (hs : ∀ s < M, ev (1 + (2 * d + M) + s) = c.shifts.getD s 0)
    (hc : ∀ i < d, ev (1 + (2 * d + M) + M + i) = c.certs.getD i 0) :
    termsVal ev (columnProds d M mirrors columns qVars base).terms =
      colTerm d M mirrors c + ev (1 + (2 * d + M) + M + d) := by
  set g := ev
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
  have e1 : ((List.range M).map fun x ↦ 1 * (g (1 + (2 * d + M) + x) *
      (g (1 + 2 * d + x) * (((List.range (d - 1)).map (fun x ↦ 1 + 1 + x)).map g).prod))).sum =
      ((List.range M).map fun s ↦ c.shifts.getD s 0 * c.values.getD (2 * d + s) 0 *
        ((List.range (d - 1)).map fun i ↦ c.values.getD (1 + i) 0).prod).sum := by
    refine congrArg List.sum (List.map_congr_left fun s hs' ↦ ?_)
    have hs'' := List.mem_range.mp hs'
    rw [hrest, hs s hs'', show 1 + 2 * d + s = 1 + (2 * d + s) by omega, hv _ (by omega)]
    ring
  have e2 : ((List.range d).map fun i ↦ 1 * (g (1 + (2 * d + M) + M + i) * (g (1 + i) *
      (g (1 + d + i) * 1))) + mirrors.getD i 0 * (g (1 + (2 * d + M) + M + i) * 1)).sum =
      ((List.range d).map fun i ↦ c.certs.getD i 0 * c.values.getD i 0 * c.values.getD (d + i) 0 +
        mirrors.getD i 0 * c.certs.getD i 0).sum := by
    refine congrArg List.sum (List.map_congr_left fun i hi ↦ ?_)
    have hi' := List.mem_range.mp hi
    rw [hc i hi', hv i (by omega), show 1 + d + i = 1 + (d + i) by omega, hv (d + i) (by omega)]
    ring
  rw [e1, e2, hrest, h0, hv 0 (by omega)]
  ring

/-! ## The functionals, linear in the slices -/

theorem getD_values (f : Functionals) (chunks : Chunks) (slices : List E) (j : ℕ) :
    (f.values chunks slices).getD j 0 =
      ((f.tables[j]?).map fun e ↦ sumE (List.zipWith (· * ·) e.2
        (slices.drop (chunks.wordShifts.getD e.1 0)))).getD 0 := by
  simp only [Functionals.values, List.getD_eq_getElem?_getD, List.getElem?_map]

/-- **The functionals are linear in the slices**, for slices of `64` entries each. -/
theorem getD_values_sum {α : Type} (f : Functionals) (chunks : Chunks) (L : List α) (w : α → E)
    (s : α → List E) (hs : ∀ a ∈ L, (s a).length = 64) (j : ℕ) :
    (f.values chunks ((List.range 64).map fun b ↦ (L.map fun a ↦ w a * (s a).getD b 0).sum)).getD j 0 =
      (L.map fun a ↦ w a * (f.values chunks (s a)).getD j 0).sum := by
  simp only [getD_values]
  cases f.tables[j]? with
  | none => simp
  | some e =>
    obtain ⟨i, tb⟩ := e
    simp only [Option.map_some, Option.getD_some, sumE_zipWith_min, List.length_drop,
      List.length_map, List.length_range]
    have hS : ∀ v ∈ range (min tb.length (64 - chunks.wordShifts.getD i 0)),
        tb.getD v 0 * (((List.range 64).map fun b ↦ (L.map fun a ↦ w a * (s a).getD b 0).sum).drop
          (chunks.wordShifts.getD i 0)).getD v 0 =
        (L.map fun a ↦ w a * (tb.getD v 0 * ((s a).drop (chunks.wordShifts.getD i 0)).getD v 0)).sum := by
      intro v hv
      have hv' : chunks.wordShifts.getD i 0 + v < 64 := by have := mem_range.mp hv; omega
      rw [getD_drop', getD_map_range_E _ _ _ hv', ← List.sum_map_mul_left]
      refine congrArg List.sum (List.map_congr_left fun a _ ↦ ?_)
      rw [getD_drop']
      ring
    rw [sum_congr rfl hS, sum_map_comm]
    refine congrArg List.sum (List.map_congr_left fun a ha ↦ ?_)
    rw [hs a ha, mul_sum]

end LeanVM.Prover.Complete

end
