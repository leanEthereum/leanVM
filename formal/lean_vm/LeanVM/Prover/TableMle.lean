/-
  LeanVM.Prover.TableMle

  The executable table sumcheck's building blocks, proved: the equality table and the high fold on
  arrays, the quadratics a row's polynomial becomes in the round's variable, the loops as sums,
  and a table's polynomial (`rowTerms`) as the verifier's constraints and forms.
-/

module

public import Statement.Prover.Table
public import Statement.Prover.Mle
public import LeanVM.Protocol.EndToEnd.Complete.Table

/-!
# The table sumcheck's building blocks

* `multilinearEval_foldHigh`: fixing a table's highest coordinate at `c` (`foldHigh`) and
  extending at `p` is extending the table at `p ++ [c]`; `multilinearEval_line`: on a cube point
  of the lower coordinates and `X` on the highest, the extension is the line between the halves.
* `evalQuad_formQuad`: a polynomial whose monomials have at most two columns, each column a line
  in `X`, is the quadratic `formQuad` computes.
* `evaluate_rowTerms`: a table's batched polynomial is the verifier's constraints and forms
  (`consPart`, `formPart`).
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Complete Finset
open LeanVM.Protocol.EndToEnd (boolPoint)
open LeanVM.Protocol.EndToEnd.Complete (consPart formPart FormsDeg2 sum_range_mul_split
  multilinearEval_boolPoint_getD)

@[expose] public section

/-! ## Arrays -/

theorem toList_getD (a : Array E) (i : ℕ) : a.toList.getD i 0 = a.getD i 0 := by
  simp

/-- An array of a function of the indices, read in range. -/
theorem ofFn_getD {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) (h : i < n) (d : α) :
    (Array.ofFn f).getD i d = f ⟨i, h⟩ := by
  simp [Array.getD_eq_getD_getElem?, h]

private theorem toList_eqTable_go (p : List E) : ∀ out : Array E,
    (p.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) out).toList =
      p.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) out.toList := by
  induction p with
  | nil => intro out; rfl
  | cons r p ih =>
    intro out
    rw [List.foldl_cons, List.foldl_cons, ih]
    simp

/-- Entry `j` of the array equality table is `eq(j, p)`. -/
theorem eqTable_getD (p : List E) (j : ℕ) (hj : j < 2 ^ p.length) :
    (eqTable p).getD j 0 = eqEval (boolPoint p.length j) p := by
  rw [← toList_getD, eqTable, toList_eqTable_go]
  exact getD_eqKernel p j hj

theorem size_foldHigh (c : E) (a : Array E) : (foldHigh c a).size = a.size / 2 := by
  simp [foldHigh]

theorem getD_foldHigh (c : E) (a : Array E) (i : ℕ) (hi : i < a.size / 2) :
    (foldHigh c a).getD i 0 = a.getD i 0 * (1 + c) + a.getD (i + a.size / 2) 0 * c :=
  ofFn_getD _ i hi _

/-- **The high fold.** Fixing the highest coordinate at `c`, then extending at `p`, is extending at
`p ++ [c]`. -/
theorem multilinearEval_foldHigh (c : E) (a : Array E) (m : ℕ) (ha : a.size = 2 ^ (m + 1))
    (p : List E) (hp : p.length = m) :
    multilinearEval (foldHigh c a).toList p = multilinearEval a.toList (p ++ [c]) := by
  have hs : a.size / 2 = 2 ^ m := by rw [ha, pow_succ]; omega
  rw [multilinearEval_eq_sum m _ p (by simp [size_foldHigh, hs]) hp,
    multilinearEval_eq_sum (m + 1) _ (p ++ [c]) (by simp [ha]) (by simp [hp]),
    show 2 ^ (m + 1) = 2 ^ m * 2 by ring, sum_range_mul_split _ _ 2]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun y hy ↦ ?_
  have hy' := mem_range.mp hy
  have hl : (boolPoint m y).length = p.length := by rw [length_boolPoint, hp]
  have hb0 : boolPoint 1 0 = [0] := rfl
  have hb1 : boolPoint 1 1 = [1] := rfl
  have h0 : eqEval (boolPoint 1 0) [c] = 1 + c := by
    rw [hb0, eqEval_cons, eqEval_nil_left, mul_one, add_zero]
  have h1 : eqEval (boolPoint 1 1) [c] = c := by
    rw [hb1, eqEval_cons, eqEval_nil_left, mul_one, one_add_one_E, zero_add]
  simp only [toList_getD]
  rw [getD_foldHigh c a y (by omega), hs, boolPoint_add m 1 y 0 hy', boolPoint_add m 1 y 1 hy',
    eqEval_append _ _ _ _ hl, eqEval_append _ _ _ _ hl, h0, h1]
  simp only [mul_zero, add_zero, mul_one]
  ring

/-- **The line between the halves.** On a cube point of the lower coordinates and `X` on the
highest, the extension of a table is `a[x]·(1 + X) + a[x + 2^m]·X`. -/
theorem multilinearEval_line (a : Array E) (m : ℕ) (ha : a.size = 2 ^ (m + 1)) (x : ℕ)
    (hx : x < 2 ^ m) (X : E) :
    multilinearEval a.toList (boolPoint m x ++ [X]) =
      a.getD x 0 * (1 + X) + a.getD (x + 2 ^ m) 0 * X := by
  have hs : a.size / 2 = 2 ^ m := by rw [ha, pow_succ]; omega
  rw [← multilinearEval_foldHigh X a m ha _ (length_boolPoint m x),
    multilinearEval_boolPoint_getD m _ x (by simp [size_foldHigh, hs]) hx, toList_getD,
    getD_foldHigh X a x (by omega), hs]

/-! ## Quadratics and cubics -/

/-- The value of a quadratic at `X`. -/
def evalQuad (a : Quad) (X : E) : E := a.1 + a.2.1 * X + a.2.2 * X ^ 2

/-- The value of a cubic at `X`. -/
def evalCubic (a : Cubic) (X : E) : E := a.1 + a.2.1 * X + a.2.2.1 * X ^ 2 + a.2.2.2 * X ^ 3

theorem evalQuad_add (a b : Quad) (X : E) :
    evalQuad (Quad.add a b) X = evalQuad a X + evalQuad b X := by
  simp only [evalQuad, Quad.add]; ring

theorem evalQuad_smul (s : E) (a : Quad) (X : E) :
    evalQuad (Quad.smul s a) X = s * evalQuad a X := by
  simp only [evalQuad, Quad.smul]; ring

theorem evalQuad_zero (X : E) : evalQuad (0, 0, 0) X = 0 := by
  simp [evalQuad]

theorem evalCubic_add (a b : Cubic) (X : E) :
    evalCubic (Cubic.add a b) X = evalCubic a X + evalCubic b X := by
  simp only [evalCubic, Cubic.add]; ring

theorem evalCubic_zero (X : E) : evalCubic (0, 0, 0, 0) X = 0 := by
  simp [evalCubic]

/-- A monomial of at most two columns, each a line, is the quadratic `termQuad`. -/
theorem evalQuad_termQuad (line : ℕ → E × E) (term : List ℕ × E) (h : term.1.length ≤ 2)
    (X : E) : evalQuad (termQuad line term) X =
      term.1.foldl (fun acc i ↦ acc * ((line i).1 + X * (line i).2)) term.2 := by
  obtain ⟨m, c⟩ := term
  match m, h with
  | [], _ =>
    simp only [termQuad, evalQuad, List.foldl_nil]
    ring
  | [i], _ =>
    simp only [termQuad, evalQuad, Quad.mulLine, List.foldl_cons, List.foldl_nil]
    ring
  | [i, j], _ =>
    simp only [termQuad, evalQuad, Quad.mulLine, List.foldl_cons, List.foldl_nil]
    ring
  | _ :: _ :: _ :: _, h =>
    simp only [List.length_cons] at h
    omega

private theorem evalQuad_foldl (line : ℕ → E × E) (X : E) :
    ∀ (terms : List (List ℕ × E)) (a : Quad), (∀ term ∈ terms, term.1.length ≤ 2) →
      evalQuad (terms.foldl (fun acc term ↦ Quad.add acc (termQuad line term)) a) X =
        evalQuad a X + (terms.map fun term ↦
          term.1.foldl (fun acc i ↦ acc * ((line i).1 + X * (line i).2)) term.2).sum
  | [], a, _ => by simp
  | term :: terms, a, h => by
    rw [List.foldl_cons, evalQuad_foldl line X terms _ fun t ht ↦ h t (by simp [ht]),
      evalQuad_add, evalQuad_termQuad line term (h term (by simp)), List.map_cons, List.sum_cons]
    ring

/-- **A row's polynomial at `X`.** With every column a line in `X` and every monomial of at most
two columns, the polynomial is the quadratic `formQuad`. -/
theorem evalQuad_formQuad (terms : List (List ℕ × E)) (line : ℕ → E × E)
    (h : ∀ term ∈ terms, term.1.length ≤ 2) (X : E) :
    evalQuad (formQuad terms line) X =
      (Form.mk terms).evaluate fun i ↦ (line i).1 + X * (line i).2 := by
  rw [formQuad, evalQuad_foldl line X terms _ h, evalQuad_zero, zero_add, Form.evaluate, sumE_eq]

/-! ## Loops as sums -/

theorem evalQuad_fold (f : ℕ → Quad) (a : Quad) (X : E) : ∀ n : ℕ,
    evalQuad (Nat.fold n (fun x _ acc ↦ Quad.add acc (f x)) a) X =
      evalQuad a X + ∑ x ∈ range n, evalQuad (f x) X
  | 0 => by simp
  | n + 1 => by
    rw [Nat.fold_succ, evalQuad_add, evalQuad_fold f a X n, sum_range_succ, add_assoc]

theorem evalCubic_fold (f : ℕ → Cubic) (a : Cubic) (X : E) : ∀ n : ℕ,
    evalCubic (Nat.fold n (fun x _ acc ↦ Cubic.add acc (f x)) a) X =
      evalCubic a X + ∑ x ∈ range n, evalCubic (f x) X
  | 0 => by simp
  | n + 1 => by
    rw [Nat.fold_succ, evalCubic_add, evalCubic_fold f a X n, sum_range_succ, add_assoc]

theorem fold_add_eq_sum (f : ℕ → E) : ∀ n : ℕ,
    Nat.fold n (fun x _ acc ↦ acc + f x) 0 = ∑ x ∈ range n, f x
  | 0 => by simp
  | n + 1 => by rw [Nat.fold_succ, fold_add_eq_sum f n, sum_range_succ]

/-- An active table's rows: the equality-weighted sum of the rows' quadratics. -/
theorem evalQuad_activeQuad (terms : List (List ℕ × E)) (F : Array (Array E)) (eqm : Array E)
    (half : ℕ) (X : E) :
    evalQuad (activeQuad terms F eqm half) X =
      ∑ x ∈ range half, eqm.getD x 0 * evalQuad (formQuad terms (rowLine F half x)) X := by
  rw [activeQuad, evalQuad_fold, evalQuad_zero, zero_add]
  exact sum_congr rfl fun x _ ↦ evalQuad_smul _ _ _

/-- A waiting table's contribution: `ω·X·σ`. -/
theorem evalCubic_tableCubic_wait (e : List E) (m : ℕ) (eqm : Array E) (h : ℕ) (w σ : E)
    (terms : List (List ℕ × E)) (F : Array (Array E)) (hh : h ≤ m) (X : E) :
    evalCubic (tableCubic e m eqm h w σ terms F) X = w * (X * σ) := by
  simp only [tableCubic, hh, ↓reduceIte, evalCubic]; ring

/-- An active table's contribution: `ω·(1 + e_m + X)·Σ_x eq[x]·P(row x at X)`. -/
theorem evalCubic_tableCubic_active (e : List E) (m : ℕ) (eqm : Array E) (h : ℕ) (w σ : E)
    (terms : List (List ℕ × E)) (F : Array (Array E)) (hh : m < h) (X : E) :
    evalCubic (tableCubic e m eqm h w σ terms F) X =
      w * ((1 + e.getD m 0 + X) * evalQuad (activeQuad terms F eqm (2 ^ m)) X) := by
  simp only [tableCubic, not_le.mpr hh, ↓reduceIte, evalCubic, evalQuad]; ring

/-- The round's message evaluates as the sum of the six tables' contributions. -/
theorem polyEval_tableRound (e : List E) (logs : List ℕ) (terms : Array (List (List ℕ × E)))
    (sigma : Array E) (st : TableState) (X : E) :
    polyEval (tableRound e logs terms sigma st) X = ∑ t ∈ range 6,
      evalCubic (tableCubic e (st.free - 1) (eqTable (e.take (st.free - 1))) (logs.getD t 0)
        (st.weights.getD t 0) (sigma.getD t 0) (terms.getD t []) (st.cols.getD t #[])) X := by
  have key : ∀ c : Cubic, polyEval [c.1, c.2.1, c.2.2.1, c.2.2.2] X = evalCubic c X := by
    intro c; simp [polyEval, evalCubic]; ring
  simp only [tableRound]
  rw [key, evalCubic_fold, evalCubic_zero, zero_add]

theorem length_tableRound (e : List E) (logs : List ℕ) (terms : Array (List (List ℕ × E)))
    (sigma : Array E) (st : TableState) : (tableRound e logs terms sigma st).length = 4 := rfl

/-! ## A table's polynomial -/

private theorem foldl_mul_col (col : ℕ → E) (m : List ℕ) (a : E) :
    m.foldl (fun acc i ↦ acc * col i) a = a * (m.map col).prod := by
  rw [← foldl_mul_eq, List.foldl_map]

theorem evaluate_append (A B : List (List ℕ × E)) (col : ℕ → E) :
    (Form.mk (A ++ B)).evaluate col = (Form.mk A).evaluate col + (Form.mk B).evaluate col := by
  simp [Form.evaluate, sumE_eq]

private theorem sum_scaled (w : E) (col : ℕ → E) : ∀ l : List (List ℕ × E),
    ((l.map fun term ↦ (term.1, w * term.2)).map fun t ↦
        t.1.foldl (fun acc i ↦ acc * col i) t.2).sum =
      w * (l.map fun t ↦ t.1.foldl (fun acc i ↦ acc * col i) t.2).sum
  | [] => by simp
  | t :: l => by
    simp only [List.map_cons, List.sum_cons]
    rw [sum_scaled w col l, foldl_mul_col, foldl_mul_col]
    ring

/-- The batched forms are the verifier's `dot` of the form powers and the forms' values. -/
theorem evaluate_formTerms : ∀ (fp : List E) (forms : List Form) (col : ℕ → E),
    (Form.mk (formTerms fp forms)).evaluate col = dot fp (forms.map (·.evaluate col))
  | [], forms, col => by simp [formTerms, Form.evaluate, sumE_eq]
  | _ :: _, [], col => by simp [formTerms, Form.evaluate, sumE_eq]
  | w :: fp, f :: forms, col => by
    have hft : formTerms (w :: fp) (f :: forms) =
        f.terms.map (fun term ↦ (term.1, w * term.2)) ++ formTerms fp forms := by
      simp [formTerms]
    rw [hft, evaluate_append, evaluate_formTerms fp forms col, List.map_cons, dot_cons]
    congr 1
    simp only [Form.evaluate, sumE_eq]
    exact sum_scaled w col f.terms

/-- `JUMP`'s batched constraints. -/
theorem evaluate_jumpTerms (cp : List E) (hcp : 2 ≤ cp.length) (ev : List E) :
    (Form.mk (jumpTerms cp)).evaluate (ev.getD · 0) = dot (cp.take 2) (jumpConstraints ev) := by
  obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, cp = a :: b :: rest := by
    match cp, hcp with
    | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
  simp [jumpTerms, jumpConstraints, Form.evaluate, sumE_eq, dot_cons]
  try ring

/-- **A table's polynomial** is the verifier's constraints and forms. -/
theorem evaluate_rowTerms (cp fp : List E) (hcp : 2 ≤ cp.length) (bus : BusResult) (t : Fin 6)
    (ev : List E) :
    (Form.mk (rowTerms cp fp bus.forms t)).evaluate (ev.getD · 0) =
      consPart cp t ev + formPart fp bus t ev := by
  rw [rowTerms, evaluate_append, evaluate_formTerms, consPart, formPart]
  by_cases ht : t = 4
  · subst ht
    rw [ite_eq_left (show ((4 : Fin 6) : ℕ) = 4 from rfl), ite_eq_left (rfl : (4 : Fin 6) = 4),
      evaluate_jumpTerms cp hcp]
  · have ht' : (t : ℕ) ≠ 4 := fun h ↦ ht (Fin.ext h)
    rw [ite_eq_right ht', ite_eq_right ht]
    simp [Form.evaluate, sumE_eq]

/-- Every monomial of a table's polynomial has at most two columns. -/
theorem rowTerms_deg (cp fp : List E) (forms : List (List Form)) (t : ℕ) (hd : FormsDeg2 forms) :
    ∀ term ∈ rowTerms cp fp forms t, term.1.length ≤ 2 := by
  intro term h
  simp only [rowTerms, List.mem_append] at h
  rcases h with h | h
  · split at h
    · simp only [jumpTerms, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> simp
    · simp at h
  · simp only [formTerms, List.mem_flatMap, List.mem_map] at h
    obtain ⟨⟨w, f⟩, hwf, ⟨m, c⟩, hmc, rfl⟩ := h
    have hf : f ∈ forms.getD t [] := (List.of_mem_zip hwf).2
    obtain ⟨side, hside, hfs⟩ := List.getElem_of_mem hf
    refine hd t side (m, c) ?_
    rw [List.getD_eq_getElem _ _ hside, hfs]
    exact hmc

end
end LeanVM.Prover
