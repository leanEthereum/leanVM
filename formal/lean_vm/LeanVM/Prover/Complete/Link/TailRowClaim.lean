/-
  LeanVM.Prover.Complete.Link.TailRowClaim

  The pointer-column rounds' folded value: one column's part at the columns' extensions over
  `q`, plus the base under `eq(0, q*)`.
-/

module

public import LeanVM.Prover.Complete.Link.TailRowSum

/-!
# The claim's side

`value_foldl_columnProds`: `columnProds` bound at `q*` is `colTerm` of the column whose fields are
the columns' fields summed under `eq(q*, q)` (`qSum`), plus `eq(0, q*)` times the base.
`qSum_flatMap`: over the tables' columns, a sum per table. `colTerm_congr`: `colTerm` reads its
column's fields only in range.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open LeanVM.Protocol.Hotwire (eqAt)
open Finset

/-- A field `g` of the columns, summed under `eq(q*, q)`. -/
def qSum (columns : List ColumnAt) (qPoint : List E) (g : ColumnAt → E) : E :=
  ((columns.zipIdx).map fun cq ↦ (eqKernel qPoint).getD cq.2 0 * g cq.1).sum

theorem sum_range_getD_zipIdx {α : Type} [Inhabited α] (F : ℕ → α → E) :
    ∀ (l : List α) (k : ℕ), ∑ q ∈ range l.length, F (k + q) (l.getD q default) =
      ((l.zipIdx k).map fun cq ↦ F cq.2 cq.1).sum
  | [], _ => by simp
  | a :: l, k => by
    rw [List.length_cons, sum_range_succ', List.zipIdx_cons, List.map_cons, List.sum_cons,
      ← sum_range_getD_zipIdx F l (k + 1)]
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    exact sum_congr rfl fun q _ ↦ by rw [show k + (q + 1) = k + 1 + q by omega]

theorem sum_eqAt_qSum (columns : List ColumnAt) (qPoint : List E) (g : ColumnAt → E)
    (hg : g default = 0) (hlen : columns.length ≤ 2 ^ qPoint.length) :
    ∑ q ∈ range (2 ^ qPoint.length), eqAt qPoint q * g (columns.getD q default) =
      qSum columns qPoint g := by
  rw [← sum_range_add_sum_Ico _ hlen, sum_eq_zero (s := Ico _ _) fun q hq ↦ by
    rw [List.getD_eq_default _ _ (mem_Ico.mp hq).1, hg, mul_zero], add_zero]
  unfold qSum
  rw [← sum_range_getD_zipIdx (fun q c ↦ (eqKernel qPoint).getD q 0 * g c) columns 0]
  refine sum_congr rfl fun q hq ↦ ?_
  rw [zero_add, LeanVM.Protocol.Hotwire.eqKernel_getD, ite_eq_left (by have := mem_range.mp hq; omega)]

theorem eqAt_zero (p : List E) : eqAt p 0 = prodE (p.map (1 + ·)) := by
  induction p with
  | nil => simp [prodE]
  | cons z p ih =>
    rw [LeanVM.Protocol.Hotwire.eqAt_cons, Nat.zero_div, ih, tailRow_prodE_eq_prod,
      tailRow_prodE_eq_prod]
    simp [CharTwo.sub_eq_add]

/-- **The pointer-column rounds bound at `q*`.** -/
theorem value_foldl_columnProds (d M : ℕ) (hd : 1 ≤ d) (mirrors : List E) (columns : List ColumnAt)
    (qPoint : List E) (base : E) (hlen : columns.length ≤ 2 ^ qPoint.length) :
    (qPoint.foldl Prods.fold (columnProds d M mirrors columns qPoint.length base)).value =
      colTerm d M mirrors ⟨qSum columns qPoint (·.coef),
        (List.range M).map (fun s ↦ qSum columns qPoint (·.shifts.getD s 0)),
        (List.range (2 * d + M)).map (fun j ↦ qSum columns qPoint (·.values.getD j 0)),
        (List.range d).map (fun i ↦ qSum columns qPoint (·.certs.getD i 0)), []⟩ +
        prodE (qPoint.map (1 + ·)) * base := by
  set CP := columnProds d M mirrors columns qPoint.length base
  rw [value_eq_termsVal, foldl_fold_terms]
  have hat : (qPoint.foldl Prods.fold CP).at = fun f ↦ mleA (CP.tables.getD f #[]) qPoint :=
    funext fun f ↦ at_foldl qPoint CP f
  rw [hat]
  have htabs := tabs_columnProds d M mirrors columns qPoint.length base
  have hev : ∀ f, mleA (CP.tables.getD f #[]) qPoint =
      ∑ q ∈ range (2 ^ qPoint.length), eqAt qPoint q * colTab d M mirrors columns qPoint.length base q f := by
    intro f
    by_cases hf : f < CP.tables.size
    · rw [mleA_eq_sum _ _ (htabs.1 _ (by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hf, Option.getD_some]
        exact Array.getElem_mem hf))]
      rfl
    · have he : CP.tables.getD f #[] = #[] := by
        simp [Array.getD_eq_getD_getElem?, show CP.tables.size ≤ f by omega]
      rw [he, mleA_empty]
      symm
      refine sum_eq_zero fun q _ ↦ ?_
      unfold colTab
      rw [show (columnProds d M mirrors columns qPoint.length base).tables.getD f #[] = #[] from he]
      simp
  have hq : ∀ q ∈ range (2 ^ qPoint.length), q < 2 ^ qPoint.length := fun q hq ↦ mem_range.mp hq
  have h0 : mleA (CP.tables.getD 0 #[]) qPoint = qSum columns qPoint (·.coef) := by
    rw [hev, ← sum_eqAt_qSum columns qPoint _ rfl hlen]
    exact sum_congr rfl fun q hq' ↦ by rw [colTab_coef, ite_eq_left (hq q hq')]
  have hv : ∀ j < 2 * d + M, mleA (CP.tables.getD (1 + j) #[]) qPoint =
      ((List.range (2 * d + M)).map (fun j ↦ qSum columns qPoint (·.values.getD j 0))).getD j 0 := by
    intro j hj
    rw [getD_map_range_E _ _ _ hj, hev, ← sum_eqAt_qSum columns qPoint _ rfl hlen]
    exact sum_congr rfl fun q hq' ↦ by rw [colTab_value _ _ _ _ _ _ (hq q hq') hj]
  have hs : ∀ s < M, mleA (CP.tables.getD (1 + (2 * d + M) + s) #[]) qPoint =
      ((List.range M).map (fun s ↦ qSum columns qPoint (·.shifts.getD s 0))).getD s 0 := by
    intro s hs
    rw [getD_map_range_E _ _ _ hs, hev, ← sum_eqAt_qSum columns qPoint _ rfl hlen]
    exact sum_congr rfl fun q hq' ↦ by rw [colTab_shift _ _ _ _ _ _ (hq q hq') hs]
  have hc : ∀ i < d, mleA (CP.tables.getD (1 + (2 * d + M) + M + i) #[]) qPoint =
      ((List.range d).map (fun i ↦ qSum columns qPoint (·.certs.getD i 0))).getD i 0 := by
    intro i hi
    rw [getD_map_range_E _ _ _ hi, hev, ← sum_eqAt_qSum columns qPoint _ rfl hlen]
    exact sum_congr rfl fun q hq' ↦ by rw [colTab_cert _ _ _ _ _ _ (hq q hq') hi]
  rw [termsVal_columnProds d M hd mirrors columns qPoint.length base _ ⟨qSum columns qPoint (·.coef),
        (List.range M).map (fun s ↦ qSum columns qPoint (·.shifts.getD s 0)),
        (List.range (2 * d + M)).map (fun j ↦ qSum columns qPoint (·.values.getD j 0)),
        (List.range d).map (fun i ↦ qSum columns qPoint (·.certs.getD i 0)), []⟩ h0 hv hs hc, hev,
    sum_congr rfl fun q hq' ↦ by rw [colTab_base _ _ _ _ _ _ (hq q hq'), mul_ite, mul_zero],
    sum_ite_eq' (range _) 0, ite_eq_left (mem_range.mpr (Nat.two_pow_pos _)), eqAt_zero]

/-- **`colTerm` reads its column's fields in range only.** -/
theorem colTerm_congr (d M : ℕ) (hd : 1 ≤ d) (mirrors : List E) (c c' : ColumnAt)
    (h0 : c.coef = c'.coef) (hv : ∀ j < 2 * d + M, c.values.getD j 0 = c'.values.getD j 0)
    (hs : ∀ s < M, c.shifts.getD s 0 = c'.shifts.getD s 0)
    (hc : ∀ i < d, c.certs.getD i 0 = c'.certs.getD i 0) :
    colTerm d M mirrors c = colTerm d M mirrors c' := by
  unfold colTerm
  have hr : ((List.range (d - 1)).map fun i ↦ c.values.getD (1 + i) 0) =
      ((List.range (d - 1)).map fun i ↦ c'.values.getD (1 + i) 0) :=
    List.map_congr_left fun i hi ↦ hv _ (by have := List.mem_range.mp hi; omega)
  have e1 : ((List.range M).map fun s ↦ c.shifts.getD s 0 * c.values.getD (2 * d + s) 0 *
      ((List.range (d - 1)).map fun i ↦ c.values.getD (1 + i) 0).prod) =
      ((List.range M).map fun s ↦ c'.shifts.getD s 0 * c'.values.getD (2 * d + s) 0 *
      ((List.range (d - 1)).map fun i ↦ c'.values.getD (1 + i) 0).prod) :=
    List.map_congr_left fun s hs' ↦ by
      have := List.mem_range.mp hs'
      rw [hs s this, hv _ (by omega), hr]
  have e2 : ((List.range d).map fun i ↦ c.certs.getD i 0 * c.values.getD i 0 * c.values.getD (d + i) 0 +
      mirrors.getD i 0 * c.certs.getD i 0) =
      ((List.range d).map fun i ↦ c'.certs.getD i 0 * c'.values.getD i 0 * c'.values.getD (d + i) 0 +
      mirrors.getD i 0 * c'.certs.getD i 0) :=
    List.map_congr_left fun i hi ↦ by
      have := List.mem_range.mp hi
      rw [hc i this, hv i (by omega), hv (d + i) (by omega)]
  simp only
  rw [e1, e2, hr, h0, hv 0 (by omega)]

end LeanVM.Prover.Complete

end
