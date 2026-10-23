/-
  LeanVM.Protocol.EndToEnd.Complete.Table

  The honest prover of the verifier program's table phase: the batched table sumcheck's round
  polynomials, the tables' column evaluations at the sumcheck's point, and the simulation of
  `tablePhase` by it, which ends on true column claims.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.TableMath
public import LeanVM.Protocol.EndToEnd.Complete.Facts
public import LeanVM.Protocol.EndToEnd.Complete.Flushes
public import LeanVM.Protocol.Verifier

/-!
# The table phase

Step 4 of `verify_execution` (`tablePhase`, `python-verifier/verifier.py:1380-1388`, and
`table_sumcheck`, `:599-628`, at leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`). The verifier
samples `ξ`, splits its powers into the constraint powers and the three form powers, and runs one
plain sumcheck of four coefficients per round over `n = max_t τ_t` coordinates against the target
`Σ_side ξ^side · total_side`; it then reads every table's row evaluations at the point (the
challenges reversed), checks the terminal claim, and claims each evaluation on its column.

**The summand.** At a point `r` of `n` coordinates the honest summand (`summand`) is exactly what
the verifier computes in `tableTerms` from the honest evaluations (`evalsAt`: each column's
extension at `r`'s first `τ_t` coordinates): `Σ_t weight_t(r) · (constraints + forms)`. So the
terminal check holds by construction, and the running claims (`claimOf`) are the summand summed
over the free coordinates, the first challenge binding the highest one.

* `coordPoly_summand`: the summand has degree at most three in each coordinate: the weight is a
  product of one affine factor per coordinate, the forms and the `JUMP` constraints have degree
  two in the columns' extensions (`BusGood.forms_deg`).
* `sum_summand`: over the cube the summand sums to the target: a table's weight on the cube is the
  equality weight of its rows against the bus point times the product of the high coordinates,
  which only the all-ones corner survives (`sum_prod_bits`); on a row the extensions are the cells
  (`multilinearEval_boolPoint_getD`), the constraints vanish (`M3Holds`), and the forms sum to the
  true totals, which `BusGood.totals` makes the bus's.
* `follows_tablePhase`: the honest prover follows `tablePhase`, every claim it returns true.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Complete
open Finset

@[expose] public section

/-! ## The verifier's per-table loop, pure -/

/-- `tableTerms` with the evaluations given: the terminal value and the claims. -/
def termsPure (cp fp point : List E) :
    List ((Table × ℕ × List Form × E) × List E) → ℕ → E → List Verifier.ColumnClaim →
      E × List Verifier.ColumnClaim
  | [], _, final, claims => (final, claims)
  | ((table, height, forms, weight), evaluations) :: rest, cursor, final, claims =>
    termsPure cp fp point rest (cursor + table.nConstraints)
      (final + weight * (dot ((cp.drop cursor).take table.nConstraints)
        (table.constraints evaluations) + dot fp (forms.map (·.evaluate (evaluations.getD · 0)))))
      (claims ++ evaluations.zipIdx.map fun (value, column) ↦
        ⟨globalColumnBases.getD table.opcode 0 + column, point.take height, value⟩)

/-- Sending a concatenation is sending the parts in turn. -/
theorem sendList_append : ∀ (a b : List E),
    Script.sendList (a ++ b) = (Script.sendList a).bind fun _ ↦ Script.sendList b
  | [], b => rfl
  | x :: a, b => by
    simp only [List.cons_append, Script.sendList, Script.bind, sendList_append a b]

/-- **The per-table loop.** Sending every table's evaluations in turn follows `tableTerms`, which
returns what `termsPure` computes. -/
theorem follows_tableTerms (cp fp point : List E) :
    ∀ (pairs : List ((Table × ℕ × List Form × E) × List E)) (cursor : ℕ) (final : E)
      (claims : List Verifier.ColumnClaim) (cs : Commits),
      (∀ p ∈ pairs, p.2.length = p.1.1.width) →
      Follows (fun cs' _ b ↦ cs' = cs ∧ b = termsPure cp fp point pairs cursor final claims)
        (Script.sendList (pairs.flatMap (·.2)))
        (tableTerms cp fp point (pairs.map (·.1)) cursor final claims) cs
  | [], cursor, final, claims, cs, _ => by
    simp [Script.sendList, tableTerms, termsPure, Follows]
  | ((table, height, forms, weight), ev) :: rest, cursor, final, claims, cs, h => by
    have hev : ev.length = table.width := h ((table, height, forms, weight), ev) (by simp)
    simp only [List.flatMap_cons, List.map_cons, tableTerms, termsPure, Prog.bind_eq]
    rw [sendList_append, ← hev]
    refine Follows.bind (fun cs' _ b hb ↦ ?_) _ _ _ (Follows.sendList_readN cs ev)
    obtain ⟨rfl, rfl⟩ := hb
    exact follows_tableTerms cp fp point rest _ _ _ cs' fun p hp ↦ h p (by simp [hp])

/-- The claims `termsPure` returns: the given ones, then every table's evaluations, each on its
column at the point's first `height` coordinates. -/
theorem termsPure_snd (cp fp point : List E) :
    ∀ (pairs : List ((Table × ℕ × List Form × E) × List E)) (cursor : ℕ) (final : E)
      (claims : List Verifier.ColumnClaim),
      (termsPure cp fp point pairs cursor final claims).2 = claims ++ pairs.flatMap fun p ↦
        p.2.zipIdx.map fun (value, column) ↦
          (⟨globalColumnBases.getD p.1.1.opcode 0 + column, point.take p.1.2.1, value⟩ :
            Verifier.ColumnClaim)
  | [], _, _, claims => by simp [termsPure]
  | ((table, height, forms, weight), ev) :: rest, cursor, final, claims => by
    rw [termsPure, termsPure_snd cp fp point rest]
    simp

/-! ## The honest summand -/

section Honest

variable (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))

/-- Column `i` of opcode table `t` read off the stack, lifted to `E`: `2^τ_t` entries. -/
def tableColList (t : Fin 6) (i : Fin (width (opIdx t))) : List E :=
  ((inst prog s).column q ⟨opIdx t, i⟩).values.toList.map ofK

/-- A column has `2^τ_t` entries. -/
theorem length_tableColList (t : Fin 6) (i : Fin (width (opIdx t))) :
    (tableColList prog s q t i).length = 2 ^ s.τ t := by
  simp only [tableColList, List.length_map, Vector.length_toList]
  rfl

/-- The honest evaluations of table `t` at a point: every column's extension at the point's first
`τ_t` coordinates. -/
def evalsAt (t : Fin 6) (r : List E) : List E :=
  (List.finRange (width (opIdx t))).map fun i ↦
    multilinearEval (tableColList prog s q t i) (r.take (s.τ t))

/-- The number of rounds of the table sumcheck: the largest table log-height. -/
def nRounds : ℕ := (tableLogs s).foldl max 0

/-- What the verifier's loop reads for table `t` at the point `r`: the table, its height, its
bus forms and its weight, and the honest evaluations. -/
def tableRow (bus : BusResult) (r : List E) (t : Fin 6) :
    (Table × ℕ × List Form × E) × List E :=
  ((tables.getD t default, s.τ t, bus.forms.getD t [],
    (tableWeights (tableLogs s) bus.point r).getD t 0), evalsAt prog s q t r)

/-- The six tables' rows, in table order. -/
def pairsAt (bus : BusResult) (r : List E) : List ((Table × ℕ × List Form × E) × List E) :=
  [tableRow prog s q bus r 0, tableRow prog s q bus r 1, tableRow prog s q bus r 2,
    tableRow prog s q bus r 3, tableRow prog s q bus r 4, tableRow prog s q bus r 5]

/-- **The honest summand** at a point: the terminal value the verifier computes from the honest
evaluations there. -/
def summand (cp fp : List E) (bus : BusResult) (r : List E) : E :=
  (termsPure cp fp r (pairsAt prog s q bus r) 0 0 []).1

/-- The forms of table `t` evaluated at the evaluations `ev`, batched by the form powers. -/
def formPart (fp : List E) (bus : BusResult) (t : Fin 6) (ev : List E) : E :=
  dot fp ((bus.forms.getD t []).map (·.evaluate (ev.getD · 0)))

/-- The constraints of table `t` at the evaluations `ev`, batched: only `JUMP` has any. -/
def consPart (cp : List E) (t : Fin 6) (ev : List E) : E :=
  if t = 4 then dot (cp.take 2) (jumpConstraints ev) else 0

/-- The honest summand, table by table: weight times constraints and forms. -/
theorem summand_eq (cp fp : List E) (bus : BusResult) (r : List E) :
    summand prog s q cp fp bus r = ∑ t : Fin 6,
      (tableWeights (tableLogs s) bus.point r).getD t 0 *
        (consPart cp t (evalsAt prog s q t r) + formPart fp bus t (evalsAt prog s q t r)) := by
  have e0 : ∀ ev, (tables.getD ((0 : Fin 6) : ℕ) default).constraints ev = [] := fun _ ↦ rfl
  have e1 : ∀ ev, (tables.getD ((1 : Fin 6) : ℕ) default).constraints ev = [] := fun _ ↦ rfl
  have e2 : ∀ ev, (tables.getD ((2 : Fin 6) : ℕ) default).constraints ev = [] := fun _ ↦ rfl
  have e3 : ∀ ev, (tables.getD ((3 : Fin 6) : ℕ) default).constraints ev = [] := fun _ ↦ rfl
  have e5 : ∀ ev, (tables.getD ((5 : Fin 6) : ℕ) default).constraints ev = [] := fun _ ↦ rfl
  have e4 : (tables.getD ((4 : Fin 6) : ℕ) default).constraints = jumpConstraints := rfl
  have n0 : (tables.getD ((0 : Fin 6) : ℕ) default).nConstraints = 0 := rfl
  have n1 : (tables.getD ((1 : Fin 6) : ℕ) default).nConstraints = 0 := rfl
  have n2 : (tables.getD ((2 : Fin 6) : ℕ) default).nConstraints = 0 := rfl
  have n3 : (tables.getD ((3 : Fin 6) : ℕ) default).nConstraints = 0 := rfl
  have n4 : (tables.getD ((4 : Fin 6) : ℕ) default).nConstraints = 2 := rfl
  simp only [summand, pairsAt, tableRow, termsPure, Fin.sum_univ_six, consPart, formPart, e0, e1,
    e2, e3, e4, e5, n0, n1, n2, n3, n4, dot_nil_right, add_zero, zero_add, List.drop_zero]
  simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, zero_add]

end Honest

/-! ## Degree -/

/-- A form of degree at most two in columns of degree one has degree two. -/
theorem coordPoly_evaluate {n : ℕ} (f : Form) (col : List E → ℕ → E)
    (hcol : ∀ i, CoordPoly 1 n fun r ↦ col r i) (hdeg : ∀ term ∈ f.terms, term.1.length ≤ 2) :
    CoordPoly 2 n fun r ↦ f.evaluate (col r) := by
  have hterm : ∀ term ∈ f.terms,
      CoordPoly 2 n fun r ↦ term.1.foldl (fun acc i ↦ acc * col r i) term.2 := by
    rintro ⟨m, c⟩ hm
    have hl := hdeg _ hm
    match m, hl with
    | [], _ => exact CoordPoly.const 2 n c
    | [i], _ =>
      exact (((hcol i).const_mul c).mono (by omega)).congr fun r _ ↦ by simp
    | [i, j], _ =>
      exact (((hcol i).const_mul c).mul (hcol j)).congr fun r _ ↦ by simp
  have h := CoordPoly.list_sum (f.terms.map fun term r ↦
    term.1.foldl (fun acc i ↦ acc * col r i) term.2) (by
      intro F hF
      obtain ⟨term, hterm', rfl⟩ := List.mem_map.mp hF
      exact hterm term hterm')
  refine h.congr fun r _ ↦ ?_
  simp only [Form.evaluate, sumE_eq, List.map_map]
  rfl

/-- `JUMP`'s constraints, with the Python's column indices resolved. -/
theorem jumpConstraints_eq (ev : List E) :
    jumpConstraints ev = [ev.getD 13 0 + ev.getD 5 0 * ev.getD 12 0,
      ev.getD 5 0 * (ev.getD 13 0 + 1)] := by
  have h5 : colIdx jumpColumns "v_cond" = 5 := by decide +kernel
  have h12 : colIdx jumpColumns "w" = 12 := by decide +kernel
  have h13 : colIdx jumpColumns "b" = 13 := by decide +kernel
  simp only [jumpConstraints, h5, h12, h13]

section Degree

variable (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))

/-- The announced heights, read back. -/
theorem getD_tableLogs (t : Fin 6) : (tableLogs s).getD t 0 = s.τ t := by
  rw [List.getD_eq_getElem _ _ (by simp [tableLogs])]
  simp only [tableLogs, List.getElem_ofFn]

/-- Every table's height is at most the number of rounds. -/
theorem τ_le_nRounds (t : Fin 6) : s.τ t ≤ nRounds s := by
  refine (le_foldl_max (tableLogs s) 0).2 _ ?_
  simp only [tableLogs, List.mem_ofFn]
  exact ⟨t, rfl⟩

/-- An honest evaluation has degree one in each coordinate. -/
theorem coordPoly_evalsAt (t : Fin 6) (i : ℕ) :
    CoordPoly 1 (nRounds s) fun r ↦ (evalsAt prog s q t r).getD i 0 := by
  by_cases hi : i < width (opIdx t)
  · refine (coordPoly_multilinearEval_take (τ_le_nRounds s t) (tableColList prog s q t ⟨i, hi⟩)
      (length_tableColList prog s q t ⟨i, hi⟩)).congr fun r _ ↦ ?_
    simp [evalsAt, List.getD_eq_getElem?_getD, hi]
  · exact (CoordPoly.const 1 _ 0).congr fun r _ ↦ by
      simp [evalsAt, List.getD_eq_getElem?_getD, hi]

/-- **The honest summand has degree at most three in each coordinate.** -/
theorem coordPoly_summand {bus : BusResult} (hb : BusGood prog s q bus) (cp fp : List E) :
    CoordPoly 3 (nRounds s) (summand prog s q cp fp bus) := by
  refine (CoordPoly.sum (n := nRounds s) Finset.univ (F := fun (t : Fin 6) r ↦
    (∏ v ∈ range (nRounds s), weightFactor bus.point (s.τ t) v (r.getD v 0)) *
      (consPart cp t (evalsAt prog s q t r) + formPart fp bus t (evalsAt prog s q t r)))
    fun t _ ↦ (coordPoly_weight bus.point (s.τ t) (nRounds s)).mul (d' := 2) ?_).congr
      fun r hr ↦ ?_
  · refine CoordPoly.add ?_ ?_
    · unfold consPart
      by_cases ht : t = 4
      · simp only [ht, ↓reduceIte, jumpConstraints_eq]
        refine (CoordPoly.dot_map (cp.take 2) [fun r ↦ (evalsAt prog s q 4 r).getD 13 0 +
            (evalsAt prog s q 4 r).getD 5 0 * (evalsAt prog s q 4 r).getD 12 0,
          fun r ↦ (evalsAt prog s q 4 r).getD 5 0 * ((evalsAt prog s q 4 r).getD 13 0 + 1)]
          ?_).congr fun r _ ↦ by simp
        intro F hF
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
        rcases hF with rfl | rfl
        · exact ((coordPoly_evalsAt prog s q 4 13).mono (by omega)).add
            ((coordPoly_evalsAt prog s q 4 5).mul (coordPoly_evalsAt prog s q 4 12))
        · exact (coordPoly_evalsAt prog s q 4 5).mul
            ((coordPoly_evalsAt prog s q 4 13).add (CoordPoly.const 1 _ 1))
      · simp only [ht, ↓reduceIte]
        exact CoordPoly.const 2 _ 0
    · unfold formPart
      refine (CoordPoly.dot_map fp ((bus.forms.getD t []).map fun f r ↦
        f.evaluate ((evalsAt prog s q t r).getD · 0)) ?_).congr fun r _ ↦ by
          simp only [List.map_map]; rfl
      intro F hF
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hF
      refine coordPoly_evaluate f _ (fun i ↦ coordPoly_evalsAt prog s q t i) fun term hterm ↦ ?_
      obtain ⟨side, hside⟩ := List.getElem_of_mem hf
      refine hb.forms_deg t side term ?_
      rw [List.getD_eq_getElem _ _ hside.1, hside.2]
      exact hterm
  · rw [summand_eq]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [getD_tableWeights _ _ _ _ (by simp [tableLogs]), hr, getD_tableLogs]

end Degree

/-! ## The cube sum -/

/-- A sum over `a · b` indices, split into the low index `y < a` and the high index `z < b`. -/
theorem sum_range_mul_split (f : ℕ → E) (a : ℕ) : ∀ b : ℕ,
    ∑ x ∈ range (a * b), f x = ∑ z ∈ range b, ∑ y ∈ range a, f (y + a * z)
  | 0 => by simp
  | b + 1 => by
    rw [Nat.mul_succ, sum_range_add, sum_range_mul_split f a b, sum_range_succ]
    exact congrArg _ (sum_congr rfl fun y _ ↦ by rw [add_comm])

/-- **A table's weight on the cube**: summed against a function of the first `h` coordinates,
the weight of a table of log-height `h` is the equality weight of its rows against the point. -/
theorem sum_cube_weight (e : List E) {h n : ℕ} (hn : h ≤ n) (he : h ≤ e.length)
    (G : List E → E) (hG : ∀ r, G r = G (r.take h)) :
    ∑ x ∈ range (2 ^ n), (∏ v ∈ range n, weightFactor e h v ((boolPoint n x).getD v 0)) *
        G (boolPoint n x) =
      ∑ y : Fin (2 ^ h), eqEval (e.take h) (boolPoint h y) * G (boolPoint h y) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = h + k := ⟨n - h, by omega⟩
  rw [pow_add, sum_range_mul_split,
    Fin.sum_univ_eq_sum_range (fun y ↦ eqEval (e.take h) (boolPoint h y) * G (boolPoint h y))]
  have htake : ∀ y z, y < 2 ^ h → (boolPoint (h + k) (y + 2 ^ h * z)).take h = boolPoint h y :=
    fun y z hy ↦ by
      rw [boolPoint_add h k y z hy, List.take_left' (Whir.Complete.length_boolPoint h y)]
  calc ∑ z ∈ range (2 ^ k), ∑ y ∈ range (2 ^ h),
        (∏ v ∈ range (h + k), weightFactor e h v ((boolPoint (h + k) (y + 2 ^ h * z)).getD v 0)) *
          G (boolPoint (h + k) (y + 2 ^ h * z))
      = ∑ z ∈ range (2 ^ k), ∑ y ∈ range (2 ^ h),
          (∏ v ∈ range k, (boolPoint k z).getD v 0) *
            (eqEval (e.take h) (boolPoint h y) * G (boolPoint h y)) := by
        refine sum_congr rfl fun z _ ↦ sum_congr rfl fun y hy ↦ ?_
        have hy' := mem_range.mp hy
        rw [prod_weightFactor_boolPoint e (by omega) he y z hy', Nat.add_sub_cancel_left, hG,
          htake y z hy']
        ring
    _ = ∑ y ∈ range (2 ^ h), eqEval (e.take h) (boolPoint h y) * G (boolPoint h y) := by
        rw [sum_comm]
        refine sum_congr rfl fun y _ ↦ ?_
        rw [← sum_mul, sum_prod_bits, one_mul]

section Sum

variable (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))

/-- Cell `i` of row `y` of opcode table `t`, read off the stack. -/
def rowCell (t : Fin 6) (y : Fin (2 ^ s.τ t)) (i : Fin (width (opIdx t))) : K :=
  ((inst prog s).column q ⟨opIdx t, i⟩).values.get y

/-- The rows of table `t`, read as the evaluations the verifier would see at a cube point. -/
def rowEvals (t : Fin 6) (y : Fin (2 ^ s.τ t)) : List E :=
  (List.finRange (width (opIdx t))).map fun i ↦ ofK (rowCell prog s q t y i)

/-- At a cube point, the honest evaluations are the row's cells. -/
theorem evalsAt_boolPoint (t : Fin 6) (y : Fin (2 ^ s.τ t)) :
    evalsAt prog s q t (boolPoint (s.τ t) y) = rowEvals prog s q t y := by
  unfold evalsAt rowEvals
  rw [List.take_of_length_le (le_of_eq (Whir.Complete.length_boolPoint (s.τ t) y))]
  refine List.map_congr_left fun i _ ↦ ?_
  rw [multilinearEval_boolPoint_getD _ _ _ (length_tableColList prog s q t i) y.isLt,
    List.getD_eq_getElem _ _ (by rw [length_tableColList]; exact y.isLt)]
  simp only [tableColList, List.getElem_map, Vector.getElem_toList]
  rfl

/-- The row's cells, read by index, are `rowVal`. -/
theorem getD_rowEvals (t : Fin 6) (y : Fin (2 ^ s.τ t)) (i : ℕ) :
    (rowEvals prog s q t y).getD i 0 = rowVal prog s q t y i := by
  have hlen : (rowEvals prog s q t y).length = width (opIdx t) := by
    unfold rowEvals; rw [List.length_map, List.length_finRange]
  unfold rowVal
  by_cases hi : i < width (opIdx t)
  · rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hi)]
    simp only [hi, ↓reduceDIte]
    unfold rowEvals
    rw [List.getElem_map, List.getElem_finRange]
    rfl
  · rw [List.getD_eq_default _ _ (by rw [hlen]; exact not_lt.mp hi)]
    simp only [hi, ↓reduceDIte]

/-- **The cube sum of the honest summand** is the target `Σ_side ξ^side · total_side`, when the
constraints vanish on `JUMP`'s rows. -/
theorem sum_summand {bus : BusResult} (hb : BusGood prog s q bus) (cp fp : List E)
    (hfp : fp.length = 3)
    (hcons : ∀ y : Fin (2 ^ s.τ 4), consPart cp 4 (rowEvals prog s q 4 y) = 0) :
    ∑ x ∈ range (2 ^ nRounds s), summand prog s q cp fp bus (boolPoint (nRounds s) x) =
      dot fp bus.totals := by
  have hform : ∀ (t : Fin 6) (y : Fin (2 ^ s.τ t)),
      formPart fp bus t (rowEvals prog s q t y) = ∑ i ∈ range 3, fp.getD i 0 *
        ((bus.forms.getD t []).getD i {}).evaluate (rowVal prog s q t y) := by
    intro t y
    have hl : ((bus.forms.getD t []).map (·.evaluate ((rowEvals prog s q t y).getD · 0))).length
        = 3 := by rw [List.length_map]; exact hb.forms_row_length t t.isLt
    rw [formPart, dot_eq_sum _ _ (by rw [hl, hfp]), hfp]
    refine sum_congr rfl fun i hi ↦ ?_
    have hi' : i < (bus.forms.getD t []).length := by
      rw [hb.forms_row_length t t.isLt]; exact mem_range.mp hi
    rw [List.getD_eq_getElem ((bus.forms.getD t []).map
        (·.evaluate ((rowEvals prog s q t y).getD · 0))) _ (by rw [List.length_map]; exact hi'),
      List.getElem_map, List.getD_eq_getElem (bus.forms.getD t []) _ hi']
    congr 2
    funext j
    exact getD_rowEvals prog s q t y j
  have htab : ∀ t : Fin 6, ∑ x ∈ range (2 ^ nRounds s),
      (tableWeights (tableLogs s) bus.point (boolPoint (nRounds s) x)).getD t 0 *
        (consPart cp t (evalsAt prog s q t (boolPoint (nRounds s) x)) +
          formPart fp bus t (evalsAt prog s q t (boolPoint (nRounds s) x))) =
      ∑ y : Fin (2 ^ s.τ t), eqEval (bus.point.take (s.τ t)) (boolPoint (s.τ t) y) *
        ∑ i ∈ range 3, fp.getD i 0 *
          ((bus.forms.getD t []).getD i {}).evaluate (rowVal prog s q t y) := by
    intro t
    have hw : ∀ x, (tableWeights (tableLogs s) bus.point (boolPoint (nRounds s) x)).getD t 0 =
        ∏ v ∈ range (nRounds s), weightFactor bus.point (s.τ t) v
          ((boolPoint (nRounds s) x).getD v 0) := fun x ↦ by
      rw [getD_tableWeights _ _ _ _ (by simp [tableLogs]), Whir.Complete.length_boolPoint,
        getD_tableLogs]
    simp only [hw]
    rw [sum_cube_weight bus.point (τ_le_nRounds s t) (hb.point_length t)
      (fun r ↦ consPart cp t (evalsAt prog s q t r) + formPart fp bus t (evalsAt prog s q t r))
      (fun r ↦ by simp only [evalsAt, List.take_take, min_self])]
    refine sum_congr rfl fun y _ ↦ ?_
    rw [evalsAt_boolPoint, hform]
    congr 1
    by_cases ht : t = 4
    · subst ht
      rw [hcons, zero_add]
    · simp only [consPart, ht, ↓reduceIte, zero_add]
  simp only [summand_eq]
  rw [sum_comm]
  simp only [htab]
  rw [dot_eq_sum _ _ (by rw [hfp, hb.totals_length]), hfp]
  have hR : ∀ i ∈ range 3, fp.getD i 0 * bus.totals.getD i 0 = ∑ t : Fin 6,
      ∑ y : Fin (2 ^ s.τ t), eqEval (bus.point.take (s.τ t)) (boolPoint (s.τ t) y) *
        (fp.getD i 0 * ((bus.forms.getD t []).getD i {}).evaluate (rowVal prog s q t y)) := by
    intro i hi
    rw [hb.totals i (mem_range.mp hi), trueTotal, mul_sum]
    refine sum_congr rfl fun t _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun y _ ↦ ?_
    ring
  rw [sum_congr rfl hR, sum_comm]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [sum_comm]
  refine sum_congr rfl fun y _ ↦ ?_
  rw [mul_sum]

end Sum

/-! ## The honest prover -/

section Prover

variable (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))

/-- The constraint powers of `ξ` (`verifier.py:1382-1384`). -/
def cpOf (xi : E) : List E :=
  (powers xi ((tables.map Table.nConstraints).sum + 3)).take (tables.map Table.nConstraints).sum

/-- The form powers of `ξ`, one per side. -/
def fpOf (xi : E) : List E :=
  (powers xi ((tables.map Table.nConstraints).sum + 3)).drop (tables.map Table.nConstraints).sum

/-- The running claim after the challenges `pre` (the first binding the highest coordinate): the
honest summand summed over the free coordinates. -/
def claimOf (cp fp : List E) (bus : BusResult) (pre : List E) : E :=
  ∑ x ∈ range (2 ^ (nRounds s - pre.length)),
    summand prog s q cp fp bus (boolPoint (nRounds s - pre.length) x ++ pre.reverse)

/-- **The honest prover of the table phase**: receive `ξ`, run the honest sumcheck rounds of the
running claims, send every table's evaluations at the point, and return the verifier's claims. -/
noncomputable def hTable (bus : BusResult) : Script (List Verifier.ColumnClaim) :=
  Script.sampleE.bind fun xi ↦
    (hSumcheck 4 (claimOf prog s q (cpOf xi) (fpOf xi) bus) (List.replicate (nRounds s) none)
      []).bind fun r ↦
      (Script.sendList ((pairsAt prog s q bus r.1.reverse).flatMap (·.2))).bind fun _ ↦
        .ret (bus.claims ++
          (termsPure (cpOf xi) (fpOf xi) r.1.reverse (pairsAt prog s q bus r.1.reverse) 0 0 []).2)

/-- The honest evaluation of a column is its true value. -/
theorem colEval_opIdx (t : Fin 6) (i : Fin (width (opIdx t))) (z : Vector E (s.τ t)) :
    colEval prog s q ⟨opIdx t, i⟩ z = multilinearEval (tableColList prog s q t i) z.toList := by
  unfold colEval CompPoly.CMlPolynomialEval.eval₂Mle
  refine (Front.multilinearEval_eq_evalMle (CompPoly.CMlPolynomialEval.map (algebraMap K E)
    ((inst prog s).column q ⟨opIdx t, i⟩).values) z).symm.trans ?_
  congr 1
  simp [CompPoly.CMlPolynomialEval.map, tableColList, Vector.toList_map]

/-- Each Python table's opcode is its index. -/
theorem opcode_tables_getD : ∀ t : Fin 6, (tables.getD t default).opcode = t := by decide

/-- Every claim of table `t`'s row is a true claim. -/
theorem trueClaim_tableRow (bus : BusResult) (pt : List E) (t : Fin 6)
    (hpt : s.τ t ≤ pt.length) :
    ∀ p ∈ (tableRow prog s q bus pt t).2.zipIdx, TrueClaim prog s q
      ⟨globalColumnBases.getD (tableRow prog s q bus pt t).1.1.opcode 0 + p.2,
        pt.take (tableRow prog s q bus pt t).1.2.1, p.1⟩ := by
  rintro ⟨value, column⟩ hmem
  rw [List.mk_mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff] at hmem
  obtain ⟨hlt, hval⟩ := hmem
  have hc : column < width (opIdx t) := by simpa [tableRow, evalsAt] using hlt
  have hz : (pt.take (s.τ t)).toArray.size = s.τ t := by simp; omega
  have hv : colEval prog s q ⟨opIdx t, ⟨column, hc⟩⟩ ⟨(pt.take (s.τ t)).toArray, hz⟩ = value := by
    refine (colEval_opIdx prog s q t ⟨column, hc⟩ ⟨_, hz⟩).trans ?_
    rw [← hval]
    simp [tableRow, evalsAt]
  refine ⟨⟨opIdx t, ⟨column, hc⟩⟩, ⟨(pt.take (s.τ t)).toArray, hz⟩, ?_⟩
  rw [hv, pyCol_opIdx t ⟨column, hc⟩]
  simp only [tableRow, opcode_tables_getD t]
  rfl

/-- The verifier's rows of the loop are the honest rows. -/
theorem rows_eq (bus : BusResult) (hf : bus.forms.length = 6) (pt : List E) :
    tables.zip ((tableLogs s).zip (bus.forms.zip (tableWeights (tableLogs s) bus.point pt))) =
      (pairsAt prog s q bus pt).map (·.1) := by
  have hw : (tableWeights (tableLogs s) bus.point pt).length = 6 := by
    rw [length_tableWeights]; simp [tableLogs]
  have ht : tables.length = 6 := rfl
  have hl : (tableLogs s).length = 6 := by simp [tableLogs]
  unfold pairsAt tableRow
  generalize tableWeights (tableLogs s) bus.point pt = W at hw ⊢
  apply List.ext_getElem (by simp [ht, hw, hf, hl])
  intro i h1 h2
  have hi : i < 6 := by simpa using h2
  simp only [List.getElem_zip, List.getElem_map]
  interval_cases i <;>
    simp [List.getD_eq_getElem?_getD, hw, hf, ht, tableLogs]

/-- `dot` against zeros is zero. -/
theorem dot_eq_zero_of_forall : ∀ (c l : List E), (∀ x ∈ l, x = 0) → dot c l = 0
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: c, x :: l, h => by
    rw [dot_cons, h x (by simp), dot_eq_zero_of_forall c l fun y hy ↦ h y (by simp [hy])]
    ring

/-- `powersFrom` has as many entries as asked. -/
theorem length_powersFrom (acc base : E) : ∀ n, (powersFrom acc base n).length = n
  | 0 => rfl
  | n + 1 => by simp [powersFrom, length_powersFrom _ base n]

/-- The claims the honest loop returns are true. -/
theorem trueClaims_termsPure (bus : BusResult) (cp fp pt : List E) (hpt : nRounds s ≤ pt.length) :
    TrueClaims prog s q (termsPure cp fp pt (pairsAt prog s q bus pt) 0 0 []).2 := by
  intro cl hcl
  rw [termsPure_snd, List.nil_append] at hcl
  obtain ⟨p, hp, hcl⟩ := List.mem_flatMap.mp hcl
  obtain ⟨⟨value, column⟩, hmem, rfl⟩ := List.mem_map.mp hcl
  simp only [pairsAt, List.mem_cons, List.not_mem_nil, or_false] at hp
  have hτ : ∀ t : Fin 6, s.τ t ≤ pt.length := fun t ↦ (τ_le_nRounds s t).trans hpt
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact trueClaim_tableRow prog s q bus _ 0 (hτ 0) _ hmem
  · exact trueClaim_tableRow prog s q bus _ 1 (hτ 1) _ hmem
  · exact trueClaim_tableRow prog s q bus _ 2 (hτ 2) _ hmem
  · exact trueClaim_tableRow prog s q bus _ 3 (hτ 3) _ hmem
  · exact trueClaim_tableRow prog s q bus _ 4 (hτ 4) _ hmem
  · exact trueClaim_tableRow prog s q bus _ 5 (hτ 5) _ hmem

/-- Every honest row carries as many evaluations as its table has columns. -/
theorem width_pairsAt (bus : BusResult) (pt : List E) :
    ∀ p ∈ pairsAt prog s q bus pt, p.2.length = p.1.1.width := by
  intro p hp
  simp only [pairsAt, List.mem_cons, List.not_mem_nil, or_false] at hp
  have hw : ∀ t : Fin 6, (tableRow prog s q bus pt t).2.length =
      (tableRow prog s q bus pt t).1.1.width := fun t ↦ by
    simp only [tableRow, evalsAt, List.length_map, List.length_finRange]
    exact width_opIdx t
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hw 0, hw 1, hw 2, hw 3, hw 4, hw 5]

/-- **After the rounds**: sending the rows' evaluations passes the terminal check when their
loop's value is the final claim, and returns the claims. -/
theorem follows_tableTail (claims : List Verifier.ColumnClaim) (cp fp pt : List E) (fin : E)
    (P : List ((Table × ℕ × List Form × E) × List E)) (hP : ∀ p ∈ P, p.2.length = p.1.1.width)
    (hcheck : (termsPure cp fp pt P 0 0 []).1 = fin)
    (Good : List Verifier.ColumnClaim → Prop)
    (hgood : Good (claims ++ (termsPure cp fp pt P 0 0 []).2))
    (cs : Commits) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ Good b)
      ((Script.sendList (P.flatMap (·.2))).bind fun _ ↦
        Script.ret (claims ++ (termsPure cp fp pt P 0 0 []).2))
      ((tableTerms cp fp pt (P.map (·.1)) 0 0 []).bind fun a ↦
        ((Prog.require (a.1 = fin)).bind fun _ ↦ pure a.2).bind fun tableClaims ↦
          pure (claims ++ tableClaims)) cs := by
  refine Follows.bind (fun cs' _ b h ↦ ?_) _ _ _ (follows_tableTerms cp fp pt P 0 0 [] cs hP)
  obtain ⟨rfl, rfl⟩ := h
  simp only [Prog.require, hcheck, ↓reduceIte, Prog.ret_bind, Prog.pure_eq, Follows, true_and]
  exact hgood

/-- Setting the entry after a prefix. -/
theorem set_append_cons (x : E) : ∀ (l₁ l₂ : List E) (a : E),
    (l₁ ++ a :: l₂).set l₁.length x = l₁ ++ x :: l₂
  | [], _, _ => rfl
  | b :: l₁, l₂, a => by
    simp only [List.cons_append, List.length_cons, List.set_cons_succ, set_append_cons x l₁ l₂ a]

/-- The running claim after one more challenge `x`: the summand summed over the free coordinates
below it. -/
theorem claimOf_snoc (cp fp : List E) (bus : BusResult) (ext : List E) (x : E) :
    claimOf prog s q cp fp bus (ext ++ [x]) =
      ∑ y ∈ range (2 ^ (nRounds s - ext.length - 1)), summand prog s q cp fp bus
        (boolPoint (nRounds s - ext.length - 1) y ++ x :: ext.reverse) := by
  simp only [claimOf, List.length_append, List.length_singleton, List.reverse_append,
    List.reverse_singleton, List.singleton_append, Nat.sub_add_eq]

/-- The honest running claims are polynomials of degree at most three in the next challenge. -/
theorem polyLE_claimOf {bus : BusResult} (hb : BusGood prog s q bus) (cp fp : List E)
    (ext : List E) (hk : ext.length < nRounds s) :
    PolyLE 3 fun x ↦ claimOf prog s q cp fp bus (ext ++ [x]) := by
  simp only [claimOf_snoc]
  refine PolyLE.sum _ fun y _ ↦ ?_
  have hm : nRounds s - ext.length - 1 < nRounds s := by omega
  have hr : (boolPoint (nRounds s - ext.length - 1) y ++ 0 :: ext.reverse).length = nRounds s := by
    simp; omega
  refine (coordPoly_summand prog s q hb cp fp _ hr _ hm).congr fun x ↦ ?_
  have := set_append_cons x (boolPoint (nRounds s - ext.length - 1) y) ext.reverse 0
  rw [Whir.Complete.length_boolPoint] at this
  rw [this]

/-- The honest running claims split as a plain round checks them. -/
theorem claimOf_split (cp fp : List E) (bus : BusResult) (ext : List E)
    (hk : ext.length < nRounds s) :
    claimOf prog s q cp fp bus (ext ++ [0]) + claimOf prog s q cp fp bus (ext ++ [1]) =
      claimOf prog s q cp fp bus ext := by
  obtain ⟨m, hm⟩ : ∃ m, nRounds s - ext.length = m + 1 := ⟨nRounds s - ext.length - 1, by omega⟩
  rw [claimOf_snoc, claimOf_snoc, claimOf, hm, Nat.add_sub_cancel, pow_succ,
    sum_range_mul_split _ _ 2, sum_range_succ, sum_range_succ, sum_range_zero, zero_add]
  have h1 : ∀ y ∈ range (2 ^ m), ∀ z, boolPoint (m + 1) (y + 2 ^ m * z) =
      boolPoint m y ++ boolPoint 1 z := fun y hy z ↦ boolPoint_add m 1 y z (mem_range.mp hy)
  refine congrArg₂ (· + ·) (sum_congr rfl fun y hy ↦ ?_) (sum_congr rfl fun y hy ↦ ?_)
  · rw [h1 y hy 0]; simp [boolPoint]
  · rw [h1 y hy 1]; simp [boolPoint]

/-- On a stack satisfying `M3Holds`, `JUMP`'s constraints vanish on every row (the Python's
constraints are the instance's, `pyConstraints_eval`). -/
theorem consPart_rowEvals {input : PublicInput} (hq : M3Holds (inst prog s) input q)
    (cp : List E) (y : Fin (2 ^ s.τ 4)) : consPart cp 4 (rowEvals prog s q 4 y) = 0 := by
  have h := pyConstraints_eval 4 (rowCell prog s q 4 y)
  have hz : ∀ x ∈ (LeanIsa.constraints (opIdx 4)).map
      (fun P ↦ ofK (P.eval (rowCell prog s q 4 y))), x = 0 := by
    intro x hx
    obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hx
    have hv : P.eval (rowCell prog s q 4 y) = 0 := hq.1 (opIdx 4) P hP y
    rw [hv]
    simp
  simp only [consPart, ↓reduceIte]
  apply dot_eq_zero_of_forall
  rw [show jumpConstraints (rowEvals prog s q 4 y) =
    (tables.getD ((4 : Fin 6) : ℕ) default).constraints
      ((List.finRange (width (opIdx 4))).map fun i ↦ ofK (rowCell prog s q 4 y i)) from rfl, h]
  exact hz

-- The table heights are `Nat.clog` of the row counts, which unification unfolds.
set_option maxHeartbeats 800000 in
variable {prog s q} in
/-- **The honest prover follows the table phase.** On a stack satisfying `M3Holds`, from a true
bus result, every check of `tablePhase` passes and every claim it returns is true. -/
theorem follows_tablePhase {input : PublicInput} (hq : M3Holds (inst prog s) input q)
    (bus : BusResult) (hb : BusGood prog s q bus) (cs : Commits) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ TrueClaims prog s q b) (hTable prog s q bus)
      (tablePhase (verifierLayout prog s) bus) cs := by
  unfold tablePhase tableSumcheck hTable
  simp only [Prog.bind_eq]
  refine Follows.bind (fun cs₁ xi xi' h ↦ ?_) _ _ _ (Follows.sampleE_sampleE cs)
  obtain ⟨rfl, rfl⟩ := h
  have hh : (verifierLayout prog s).tableLogHeights = tableLogs s := rfl
  have hfp : (fpOf xi).length = 3 := by
    simp only [fpOf, List.length_drop, powers, length_powersFrom]; omega
  rw [show (powers xi ((tables.map Table.nConstraints).sum + 3)).take
      (tables.map Table.nConstraints).sum = cpOf xi from rfl,
    show (powers xi ((tables.map Table.nConstraints).sum + 3)).drop
      (tables.map Table.nConstraints).sum = fpOf xi from rfl]
  have htarget : dot (fpOf xi) bus.totals = claimOf prog s q (cpOf xi) (fpOf xi) bus [] := by
    rw [claimOf]
    simp only [List.length_nil, Nat.sub_zero, List.reverse_nil, List.append_nil]
    exact (sum_summand prog s q hb (cpOf xi) (fpOf xi) hfp
      (consPart_rowEvals prog s q hq (cpOf xi))).symm
  rw [hh, htarget, Prog.bind_assoc]
  refine Follows.bind (fun cs₂ r r' h ↦ ?_) _ _ _
    (follows_sumcheck 4 (by norm_num) (claimOf prog s q (cpOf xi) (fpOf xi) bus)
      (List.replicate (nRounds s) none) [] cs₁ ?_ ?_)
  · obtain ⟨rfl, rfl, hlen, hfin⟩ := h
    simp only [List.length_replicate] at hlen
    simp only [List.nil_append] at hfin
    rw [rows_eq prog s q bus hb.forms_length, Prog.bind_assoc]
    have hcheck : (termsPure (cpOf xi) (fpOf xi) r.1.reverse
        (pairsAt prog s q bus r.1.reverse) 0 0 []).1 = r.2 := by
      rw [hfin, claimOf, hlen, Nat.sub_self, pow_zero, sum_range_one]
      rfl
    have hgood := trueClaims_append hb.claims
      (trueClaims_termsPure prog s q bus (cpOf xi) (fpOf xi) r.1.reverse
        (by rw [List.length_reverse, hlen]))
    have hP := width_pairsAt prog s q bus r.1.reverse
    generalize pairsAt prog s q bus r.1.reverse = P at hcheck hgood hP ⊢
    exact follows_tableTail bus.claims (cpOf xi) (fpOf xi) r.1.reverse r.2 P hP hcheck _ hgood cs₂
  · intro ext hext
    simp only [List.length_replicate] at hext
    exact polyLE_claimOf prog s q hb _ _ ext hext
  · intro ext hext
    simp only [List.length_replicate] at hext
    simp only [List.getElem_replicate, RoundSplit, List.nil_append]
    exact claimOf_split prog s q _ _ bus ext hext

end Prover

end
end LeanVM.Protocol.EndToEnd.Complete
