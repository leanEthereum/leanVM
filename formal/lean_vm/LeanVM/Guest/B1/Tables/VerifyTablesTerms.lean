/-
  LeanVM.Guest.B1.Tables.VerifyTablesTerms

  The table sumcheck's terms (`ttVal`) over the six tables: its final value table by table, and
  its claims.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesBusSpec

/-!
# The tables' terms

`ttVal_snd`: the claims are each table's evaluations on its global columns at the point's first
`h` coordinates. `ttVal_fst6`: the final value is the six tables' weighted terms, `JUMP`'s two
constraints batched by the first two constraint powers. `evaluate_congr`: a form's value reads
only its columns, all of them below the table's width (`flush_cols_push`, …).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Complete

@[expose] public section

/-- A table row's claims. -/
def rowClaims (point : List E) (q : (Table × ℕ × List Form × E) × List E) : List ColumnClaim :=
  q.2.zipIdx.map fun p ↦ ⟨globalColumnBases.getD q.1.1.opcode 0 + p.2, point.take q.1.2.1, p.1⟩

theorem ttVal_snd (cp fp pt : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (evss : List (List E)) (cursor : ℕ) (final : E)
      (claims : List ColumnClaim), evss.length = rows.length →
      (ttVal cp fp pt rows evss cursor final claims).2 =
        claims ++ (List.zip rows evss).flatMap (rowClaims pt)
  | [], [], _, _, claims, _ => by simp [ttVal]
  | (table, height, forms, weight) :: rest, evs :: evss, cursor, final, claims, hl => by
    simp only [ttVal]
    rw [ttVal_snd cp fp pt rest evss _ _ _ (by simpa using hl)]
    simp [rowClaims, List.append_assoc]
  | [], _ :: _, _, _, _, hl => absurd hl (by simp)
  | _ :: _, [], _, _, _, hl => absurd hl (by simp)

theorem tables_six : tables = [tables.getD 0 default, tables.getD 1 default, tables.getD 2 default,
    tables.getD 3 default, tables.getD 4 default, tables.getD 5 default] := rfl

theorem vt_dot_nil (l : List E) : dot l [] = 0 := by simp [dot]

/-- **The final value** over the six tables. -/
theorem ttVal_fst6 (cp fp pt : List E) (h0 h1 h2 h3 h4 h5 : ℕ) (f0 f1 f2 f3 f4 f5 : List Form)
    (w0 w1 w2 w3 w4 w5 : E) (e0 e1 e2 e3 e4 e5 : List E) :
    (ttVal cp fp pt (List.zip tables (List.zip [h0, h1, h2, h3, h4, h5]
      (List.zip [f0, f1, f2, f3, f4, f5] [w0, w1, w2, w3, w4, w5]))) [e0, e1, e2, e3, e4, e5]
        0 0 []).1 =
      w0 * dot fp (f0.map (·.evaluate (e0.getD · 0))) +
      w1 * dot fp (f1.map (·.evaluate (e1.getD · 0))) +
      w2 * dot fp (f2.map (·.evaluate (e2.getD · 0))) +
      w3 * dot fp (f3.map (·.evaluate (e3.getD · 0))) +
      w4 * (dot (cp.take 2) (jumpConstraints e4) + dot fp (f4.map (·.evaluate (e4.getD · 0)))) +
      w5 * dot fp (f5.map (·.evaluate (e5.getD · 0))) := by
  rw [tables_six]
  simp only [List.zip_cons_cons, List.zip_nil_left, ttVal]
  have c0 : (tables.getD 0 default).constraints e0 = [] := rfl
  have c1 : (tables.getD 1 default).constraints e1 = [] := rfl
  have c2 : (tables.getD 2 default).constraints e2 = [] := rfl
  have c3 : (tables.getD 3 default).constraints e3 = [] := rfl
  have c4 : (tables.getD 4 default).constraints e4 = jumpConstraints e4 := rfl
  have c5 : (tables.getD 5 default).constraints e5 = [] := rfl
  have n0 : (tables.getD 0 default).nConstraints = 0 := rfl
  have n1 : (tables.getD 1 default).nConstraints = 0 := rfl
  have n2 : (tables.getD 2 default).nConstraints = 0 := rfl
  have n3 : (tables.getD 3 default).nConstraints = 0 := rfl
  have n4 : (tables.getD 4 default).nConstraints = 2 := rfl
  rw [c0, c1, c2, c3, c4, c5, n0, n1, n2, n3, n4]
  simp only [vt_dot_nil, List.drop_zero, zero_add]

/-! ## Columns -/

theorem termVal_congr {c1 c2 : ℕ → E} (m : List ℕ) : ∀ (a : E), (∀ i ∈ m, c1 i = c2 i) →
    m.foldl (fun acc i ↦ acc * c1 i) a = m.foldl (fun acc i ↦ acc * c2 i) a := by
  induction m with
  | nil => intro a _; simp only [List.foldl_nil]
  | cons i m ih =>
    intro a h
    simp only [List.foldl_cons]
    rw [h i (List.mem_cons_self ..)]
    exact ih _ fun j hj => h j (List.mem_cons_of_mem _ hj)

/-- A form's value reads only its columns. -/
theorem evaluate_congr (f : Form) {c1 c2 : ℕ → E} (h : ∀ t ∈ f.terms, ∀ i ∈ t.1, c1 i = c2 i) :
    f.evaluate c1 = f.evaluate c2 := by
  rw [evaluate_eq, evaluate_eq]
  exact congrArg sumE (List.map_congr_left fun t ht => termVal_congr t.1 t.2 (h t ht))

theorem flush_cols_push : ∀ t : Fin 6, ∀ cs ∈ pySideC t .push, ∀ f ∈ cs, ∀ tm ∈ FormC.terms f,
    ∀ i ∈ tm.1, i < (vtEvalVars.getD t []).length := by decide +kernel

theorem flush_cols_pull : ∀ t : Fin 6, ∀ cs ∈ pySideC t .pull, ∀ f ∈ cs, ∀ tm ∈ FormC.terms f,
    ∀ i ∈ tm.1, i < (vtEvalVars.getD t []).length := by decide +kernel

theorem count_cols : ∀ t < 6, ∀ i ∈ vtCountCols.getD t [], i < (vtEvalVars.getD t []).length := by
  decide +kernel

/-- A block form's value at two column functions agreeing on its coordinates' columns. -/
theorem vt_blockForm_congr (b : BusBlock) (w : List E) (beta : E) {c1 c2 : ℕ → E}
    (h : ∀ f ∈ b.coordinates, ∀ t ∈ f.terms, ∀ i ∈ t.1, c1 i = c2 i) :
    (blockForm b w beta).evaluate c1 = (blockForm b w beta).evaluate c2 := by
  rw [evaluate_blockForm, evaluate_blockForm]
  refine congrArg (beta + ·) (congrArg sumE (List.map_congr_left fun p hp => ?_))
  rw [evaluate_congr p.1 (h p.1 (List.fst_mem_of_mem_zipIdx hp))]

end
end LeanVM.Guest.B1.VerifySub
