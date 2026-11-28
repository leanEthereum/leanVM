/-
  LeanVM.Prover.Complete.Link.RowIdAlg

  The algebra the row identity reads: a folded sum of products' value as the tables' extensions, a
  table's extension as its equality-weighted sum, forms and their scaling.
-/

module

public import LeanVM.Prover.Complete.Link.Fields

/-!
# The row identity's algebra

* `foldl_fold_at`, `value_foldl`: a sum of products bound at a point `r` reads each table's
  multilinear extension at `r` (`mleA`);
* `prodE_eq_prod`: the verifier's product as a list product.
-/

@[expose] public section

namespace LeanVM.Prover.Complete.RowId

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover Finset
open LeanVM.Protocol.KeccakGkr (eqAt)

/-! ## Loops -/

theorem foldl_mul_eq_prod' : ∀ (l : List E) (c : E), l.foldl (· * ·) c = c * l.prod
  | [], c => by simp
  | a :: l, c => by rw [List.foldl_cons, foldl_mul_eq_prod' l, List.prod_cons]; ring

theorem prodE_eq_prod (l : List E) : prodE l = l.prod := by
  rw [prodE, foldl_mul_eq_prod', one_mul]

theorem foldl_mul_map (g : ℕ → E) : ∀ (l : List ℕ) (c : E),
    l.foldl (fun v f ↦ v * g f) c = c * (l.map g).prod
  | [], c => by simp
  | a :: l, c => by rw [List.foldl_cons, foldl_mul_map g l, List.map_cons, List.prod_cons]; ring

theorem foldl_add_map {α : Type} (g : α → E) : ∀ (l : List α) (c : E),
    l.foldl (fun v f ↦ v + g f) c = c + (l.map g).sum
  | [], c => by simp
  | a :: l, c => by rw [List.foldl_cons, foldl_add_map g l, List.map_cons, List.sum_cons]; ring

/-! ## A sum of products bound at a point -/

theorem foldPairsA_empty (x : E) : foldPairsA x #[] = #[] := by
  simp [foldPairsA]

theorem foldl_foldPairsA_empty : ∀ r : List E, r.foldl (fun cur x ↦ foldPairsA x cur) #[] = #[]
  | [] => rfl
  | x :: r => by rw [List.foldl_cons, foldPairsA_empty, foldl_foldPairsA_empty r]

theorem foldl_fold_tables : ∀ (r : List E) (P : Prods),
    (r.foldl Prods.fold P).tables = P.tables.map (fun t ↦ r.foldl (fun cur x ↦ foldPairsA x cur) t)
  | [], P => by simp
  | x :: r, P => by
    rw [List.foldl_cons, foldl_fold_tables r]
    simp [Prods.fold, Array.map_map, Function.comp_def]

/-- **A table bound at `r`** reads its extension. -/
theorem foldl_fold_at (r : List E) (P : Prods) (f : ℕ) :
    (r.foldl Prods.fold P).at f = mleA (P.tables.getD f #[]) r := by
  rw [Prods.at, foldl_fold_tables, mleA]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases P.tables[f]? with
  | none => simp [foldl_foldPairsA_empty]
  | some t => rfl

/-- **The value of a sum of products bound at `r`**: each term's coefficient times its tables'
extensions at `r`. -/
theorem value_foldl (r : List E) (P : Prods) :
    (r.foldl Prods.fold P).value =
      P.terms.foldl (fun acc cf ↦ acc + cf.2.foldl (fun v f ↦ v * mleA (P.tables.getD f #[]) r) cf.1)
        0 := by
  rw [Prods.value, foldl_fold_terms]
  simp only [foldl_fold_at]

end LeanVM.Prover.Complete.RowId

end
