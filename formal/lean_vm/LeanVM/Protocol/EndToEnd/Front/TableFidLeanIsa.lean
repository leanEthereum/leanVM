/-
  LeanVM.Protocol.EndToEnd.Front.TableFidLeanIsa

  The table phase's identities (`TableFid`) at the leanISA instance and the verifier's layout, and
  the bus phase's depth conditions: the bus phase followed by the table sumcheck, specified with
  no fidelity hypothesis left.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.TableFidLeanIsaBus
public import LeanVM.Protocol.EndToEnd.Front.BusTable
public import LeanVM.Protocol.EndToEnd.Complete.TableMath

/-!
# The table phase's identities at leanISA

The bus/table bridge (`busTableSpec`, `LeanVM.Protocol.EndToEnd.Front.BusTable`) specifies the
verifier program's bus phase and table sumcheck (`python-verifier/verifier.py:534-628` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`) on the oracle protocol's relations, given three facts
about the instance and the layout. This module proves them at the leanISA instance
`leanIsaInstance F prog s` and the verifier's layout `verifierLayout prog s`, for every Flock
specification `F`, program `prog` and size vector `s`:

* `tableFid_leanIsa`: the table phase's identities (`TableFid`, with the global column numbering
  `pyCol`) for every read of the bus phase of the right shape whose fingerprint challenges are
  four: the rounds are `τ_max` (`rounds_leanIsa`); the target `Σ_s ξ^(2+s) · totals[s]` is the
  protocol's batched claim (`target_leanIsa`); the final check's value is the protocol's formula
  at the reversed challenges and the values read (`formula_leanIsa`: weights `prodWeight_eq`,
  values `tableValues_eq`, constraints and forms `rowValue_eq`); every claim of the protocol's
  output is the program's (`busOut_columns_mem`, `finalClaims_mem`);
* `μBus_ne_zero` and `busDepth_leanIsa`: the leaf stacks have a variable, and the push layout's
  depth is `μ_bus`;
* `busTableSpec_leanIsa`: the bus phase, then the table sumcheck, at leanISA, with no fidelity
  hypothesis left, only the error hypotheses.

**The fingerprint challenges are four.** `TableFid` is false for a read with five or more
challenges: the Python weighs coordinate `i` of a flush by entry `i` of `eq_kernel(alphas)`, the
protocol by `lagrangeBasis` of the first four, and with a fifth challenge `1` the Python's first
sixteen weights vanish (`tests/LeanVMTests/Protocol/EndToEnd/Front/TableFid.lean`). The wire
always draws four (`sample_n(BUS_BITS)`), but `BusWit.Shaped` does not record it, so
`busTableSpec` asks for `TableFid` at reads `tableFid_leanIsa` cannot cover. The leanISA spec is
therefore assembled from `busThenSpec4`, the bus phase with the length of the challenges recorded
(`abSpec4`, from `abProg_bind_guard`: guarding the wire's challenges by their length changes
nothing), which asks for the continuation only at reads with four challenges.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.TableSumcheck CompPoly CPoly CMlPolynomialEval
open Finset
open scoped NNReal ENNReal

@[expose] public section

/-! ## The powers of `ξ` -/

/-- `powers_from(acc, base, n)` is `acc · base^i` for `i < n`. -/
theorem powersFrom_eq (base : E) : ∀ (n : ℕ) (acc : E),
    powersFrom acc base n = (List.range n).map fun i ↦ acc * base ^ i
  | 0, _ => rfl
  | n + 1, acc => by
    rw [powersFrom, powersFrom_eq base n, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [pow_zero, mul_one, Function.comp_def, pow_succ']
    exact congrArg (_ :: ·) (List.map_congr_left fun i _ ↦ by ring)

/-- The number of constraints of the Python's tables. -/
theorem nCons_eq : nCons = 2 := by
  unfold nCons
  rw [Complete.pyNConstraints]
  rfl

/-- The constraint powers: `1, ξ`. -/
theorem cpsOf_eq (ξ : E) : cpsOf ξ = [1, ξ] := by
  simp [cpsOf, nCons_eq, powers, powersFrom_eq, List.range_succ]

/-- The form powers: `ξ², ξ³, ξ⁴`. -/
theorem fpsOf_eq (ξ : E) : fpsOf ξ = [ξ ^ 2, ξ ^ 3, ξ ^ 4] := by
  simp [fpsOf, nCons_eq, powers, powersFrom_eq, List.range_succ]

variable (F : FlockSpec) (prog : Program) (s : Sizes) (input : PublicInput)

/-! ## The rounds and the target -/

/-- **The rounds**: the largest announced log-height is `τ_max`. -/
theorem rounds_leanIsa :
    (verifierLayout prog s).tableLogHeights.foldl max 0 = (leanIsaInstance F prog s).τmax :=
  (τmax_leanIsa F prog s).symm

/-- **The target**: the form powers against the Python's totals are the protocol's batched claim. -/
theorem target_leanIsa (w : BusWit) (hp : w.point.length = (leanIsaInstance F prog s).μBus)
    (ha : w.alphas.length = 4) (hm : w.memory.length = 3) (ξ : E) :
    dot (fpsOf ξ) (w.result (verifierLayout prog s)).totals =
      powerBatch (claimed (leanIsaInstance F prog s)
        (busStmt (leanIsaInstance F prog s) (leanIsa_conditions F prog s) input w)) ξ := by
  rw [powerBatch, claimed, Fin.sum_univ_add]
  simp only [Fin.append_left, zero_mul, Finset.sum_const_zero, zero_add, Fin.append_right,
    Fin.val_natAdd]
  rw [sumcheckB_leanIsa F prog s, Whir.Complete.dot_eq_sum _ _ (by rw [fpsOf_eq]; rfl), fpsOf_eq,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [busStmt, busOut_totals F prog s input w hp ha hm i, mul_comm]
  fin_cases i <;> rfl

/-! ## The Python's final value, table by table -/

/-- A list of six entries, listed. -/
theorem list_six {α : Type} (l : List α) (d : α) (h : l.length = 6) :
    l = [l.getD 0 d, l.getD 1 d, l.getD 2 d, l.getD 3 d, l.getD 4 d, l.getD 5 d] := by
  match l, h with
  | [a, b, c, e, f, g], _ => rfl

/-- The Python's shape of the bus phase's forms: six tables, three sides each. -/
theorem result_forms_shape (w : BusWit) :
    (w.result (verifierLayout prog s)).forms.length = 6 ∧
      ∀ t < 6, ((w.result (verifierLayout prog s)).forms.getD t []).length = 3 := by
  rw [result_forms]
  obtain ⟨a1, a2, -, -⟩ := Complete.accFold_spec 0 (by norm_num) (eqKernel w.alphas) w.beta
    _ _ Complete.forms0_length Complete.forms0_row
    (Complete.owner_lt_six s (Complete.pushBlocks_owned s) _)
  obtain ⟨b1, b2, -, -⟩ := Complete.accFold_spec 1 (by norm_num) (eqKernel w.alphas) w.beta
    _ _ a1 a2 (Complete.owner_lt_six s (Complete.pullBlocks_owned s) _)
  obtain ⟨c1, c2, -, -⟩ := Complete.accFold_spec 2 (by norm_num) [1] 0
    _ _ b1 b2 (Complete.owner_lt_six s (Complete.countBlocks_owned s) _)
  exact ⟨c1, c2⟩

/-- The constraints' part of table `t` in the Python's final value: only `JUMP` has any. -/
def pyCons (ξ : E) (t : Fin 6) (ev : List E) : E :=
  if t = 4 then dot [1, ξ] (jumpConstraints ev) else 0

/-- The forms' part of table `t` in the Python's final value. -/
def pyForms (ξ : E) (fs : List Form) (ev : List E) : E :=
  ∑ k ∈ range 3, ξ ^ (2 + k) * (fs.getD k {}).evaluate (ev.getD · 0)

/-- `dot` of the form powers against three forms' values. -/
theorem dot_fpsOf (ξ : E) (fs : List Form) (hfs : fs.length = 3) (col : ℕ → E) :
    dot (fpsOf ξ) (fs.map (·.evaluate col)) =
      ∑ k ∈ range 3, ξ ^ (2 + k) * (fs.getD k {}).evaluate col := by
  rw [Whir.Complete.dot_eq_sum _ _ (by rw [fpsOf_eq, List.length_map, hfs]; rfl), fpsOf_eq]
  simp only [List.length_cons, List.length_nil]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' := Finset.mem_range.mp hk
  rw [List.getD_eq_getElem (fs.map _) _ (by simp [hfs]; omega), List.getElem_map,
    List.getD_eq_getElem fs _ (by omega)]
  interval_cases k <;> rfl

/-- Table `t`'s row of the final loop. -/
def pyRow (bus : BusResult) (pt : List E) (t : Fin 6) : Table × ℕ × List Form × E :=
  (tables.getD t default, s.τ t, bus.forms.getD t [],
    (tableWeights (tableLogs s) bus.point pt).getD t 0)

/-- The rows of the final loop, listed. -/
theorem rowsOf_eq (bus : BusResult) (hf : bus.forms.length = 6) (pt : List E) :
    rowsOf (verifierLayout prog s) bus pt =
      [pyRow s bus pt 0, pyRow s bus pt 1, pyRow s bus pt 2, pyRow s bus pt 3, pyRow s bus pt 4,
        pyRow s bus pt 5] := by
  have hw : (tableWeights (tableLogs s) bus.point pt).length = 6 := by
    rw [Complete.length_tableWeights]; rfl
  have ht : tables.length = 6 := rfl
  have hl : (tableLogs s).length = 6 := by simp [tableLogs]
  unfold rowsOf pyRow
  rw [show (verifierLayout prog s).tableLogHeights = tableLogs s from rfl]
  generalize tableWeights (tableLogs s) bus.point pt = W at hw ⊢
  apply List.ext_getElem (by simp [ht, hw, hf, hl])
  intro i h1 h2
  have hi : i < 6 := by simpa using h2
  simp only [List.getElem_zip]
  interval_cases i <;> simp [List.getD_eq_getElem?_getD, hw, hf, ht, tableLogs]

/-- **The Python's final value** of the table sumcheck, table by table. -/
theorem pyTableTerms_eq (w : BusWit) (ξ : E) (pt : List E) (evs : List (List E))
    (hs : ReadShape (rowsOf (verifierLayout prog s) (w.result (verifierLayout prog s)) pt) evs) :
    (pyTableTerms (cpsOf ξ) (fpsOf ξ) pt
        (rowsOf (verifierLayout prog s) (w.result (verifierLayout prog s)) pt) evs 0 0 []).1 =
      ∑ t : Fin 6, (tableWeights (tableLogs s) w.point pt).getD t 0 *
        (pyCons ξ t (evs.getD t []) +
          pyForms ξ ((w.result (verifierLayout prog s)).forms.getD t []) (evs.getD t [])) := by
  obtain ⟨hf6, hf3⟩ := result_forms_shape prog s w
  set bus := w.result (verifierLayout prog s) with hbus
  have hrows := rowsOf_eq prog s bus hf6 pt
  have hev : evs.length = 6 := by
    have := hs.length_eq
    rw [hrows] at this
    simpa using this.symm
  rw [hrows] at hs ⊢
  rw [list_six evs [] hev] at hs ⊢
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
  have hpt : bus.point = w.point := rfl
  simp only [pyTableTerms, pyRow, e0, e1, e2, e3, e4, e5, n0, n1, n2, n3, n4, hpt,
    Whir.Complete.dot_nil_right, add_zero, zero_add, List.drop_zero, Fin.sum_univ_six, pyCons,
    pyForms]
  have hd : ∀ (t : Fin 6) (col : ℕ → E),
      dot (fpsOf ξ) ((bus.forms.getD t []).map (·.evaluate col)) =
      ∑ k ∈ range 3, ξ ^ (2 + k) * ((bus.forms.getD t []).getD k {}).evaluate col :=
    fun t col ↦ dot_fpsOf _ _ (hf3 t t.isLt) col
  simp only [hd, cpsOf_eq]
  simp

/-! ## The weights -/

/-- The equality factor in characteristic two. -/
theorem eq_factor (a b : E) : (1 - a) * (1 - b) + a * b = 1 + b + a := by
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add]
  linear_combination (a * b) * Whir.Complete.two_eq_zero_E

/-- **The weights**: the protocol's weight of opcode table `t` at the reversed challenges is the
Python's. -/
theorem prodWeight_eq (w : BusWit) (ch : List E)
    (hch : ch.length = (leanIsaInstance F prog s).τmax) (t : Fin 6) :
    prodWeight (tableWeights (leanIsaInstance F prog s)
        (busStmt (leanIsaInstance F prog s) (leanIsa_conditions F prog s) input w).2.point
        (stEquiv F prog s t)) (vecOf _ ch).reverse =
      (Verifier.tableWeights (tableLogs s) w.point ch.reverse).getD t 0 := by
  rw [Complete.getD_tableWeights _ _ _ _ (by simp [tableLogs]), List.length_reverse, hch,
    prodWeight, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  have hz : ((vecOf (leanIsaInstance F prog s).τmax ch).reverse)[a.val] = ch.reverse.getD a 0 := by
    rw [Vector.getElem_reverse, List.getD_eq_getElem _ _ (by simp [hch]), List.getElem_reverse]
    simp only [vecOf, Vector.getElem_ofFn]
    rw [List.getD_eq_getElem _ _ (by omega)]
    congr 1
    omega
  have hζ :
      ((busStmt (leanIsaInstance F prog s) (leanIsa_conditions F prog s) input w).2.point)[a.val] =
      w.point.getD a 0 := by
    simp [busStmt, Bus.busOut, Bus.point, Gkr.lowPoint, BusWit.layer, layerStmtOf, vecOf]
  have hτ : (tableLogs s).getD t 0 = (leanIsaInstance F prog s).τ (stEquiv F prog s t).1 := by
    simp [tableLogs, List.getD_eq_getElem?_getD]
    fin_cases t <;> rfl
  rw [Fin.getElem_fin, hz, hτ]
  simp only [TableSumcheck.tableWeights, Complete.weightFactor]
  split_ifs with h
  · simp only [Fin.getElem_fin, hζ]
    exact eq_factor _ _
  · simp

/-! ## The values read -/

/-- Entry `i` of list `t` of a list of lists, inside the concatenation. -/
theorem flatten_getD : ∀ (l : List (List E)) (t i : ℕ), t < l.length → i < (l.getD t []).length →
    l.flatten.getD ((∑ u ∈ range t, (l.getD u []).length) + i) 0 = (l.getD t []).getD i 0
  | [], _, _, h, _ => by simp at h
  | a :: l, 0, i, _, hi => by
    simp only [List.getD_cons_zero] at hi ⊢
    rw [Finset.sum_range_zero, zero_add, List.flatten_cons, List.getD_append _ _ _ _ hi]
  | a :: l, t + 1, i, ht, hi => by
    simp only [List.getD_cons_succ, List.length_cons] at hi ht ⊢
    rw [Finset.sum_range_succ', List.getD_cons_zero, List.flatten_cons]
    simp only [List.getD_cons_succ]
    rw [add_comm _ a.length, add_assoc, List.getD_append_right _ _ _ _ (by omega),
      Nat.add_sub_cancel_left]
    exact flatten_getD l t i (by omega) hi

/-- The constraint counts of the tables before `JUMP`'s. -/
theorem constraints_length_lt_seven :
    ∀ j : Fin 9, j.val < 7 → (LeanIsa.constraints j).length = 0 := by
  decide +kernel

/-- A prefix sum over the instance's tables, kept on the sumcheck tables, as a sum over the
opcode tables before. -/
theorem prefix_onSumcheck (f : Fin (leanIsaInstance F prog s).ntab → ℕ) (t : Fin 6) :
    ∑ j : Fin (stEquiv F prog s t).1.val,
        onSumcheck (leanIsaInstance F prog s) f (Fin.castLE (stEquiv F prog s t).1.isLt.le j) =
      ∑ u ∈ range t, if h : u < 6 then f (opI F prog s ⟨u, h⟩) else 0 := by
  let G : ℕ → ℕ := fun k ↦ if h : k < 9 then onSumcheck (leanIsaInstance F prog s) f ⟨k, h⟩ else 0
  have hL : ∑ j : Fin (stEquiv F prog s t).1.val,
      onSumcheck (leanIsaInstance F prog s) f (Fin.castLE (stEquiv F prog s t).1.isLt.le j) =
        ∑ k ∈ range (3 + t), G k := by
    rw [show 3 + t.val = (stEquiv F prog s t).1.val by simp [opIdx]; omega,
      ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hj : j.val < 9 := lt_trans j.isLt (stEquiv F prog s t).1.isLt
    simp only [G, hj, dite_true]
    rfl
  rw [hL, Finset.sum_range_add]
  have h0 : ∑ k ∈ range 3, G k = 0 := Finset.sum_eq_zero fun k hk ↦ by
    have hk' := Finset.mem_range.mp hk
    simp only [G, show k < 9 by omega, dite_true, onSumcheck]
    exact ite_eq_right_iff.mpr fun hs ↦
      absurd (three_le_of_sumcheckTable F prog s _ hs) (by simp; omega)
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  have hu' : u < 6 := lt_of_lt_of_le (Finset.mem_range.mp hu) (by omega)
  have he : (⟨3 + u, by show 3 + u < 9; omega⟩ : Fin (leanIsaInstance F prog s).ntab) =
      opI F prog s ⟨u, hu'⟩ :=
    Fin.ext (by simp [opI, opIdx]; omega)
  have hst : (leanIsaInstance F prog s).SumcheckTable (opI F prog s ⟨u, hu'⟩) :=
    sumcheckTable_opIdx F prog s ⟨u, hu'⟩
  simp only [G, show 3 + u < 9 by omega, dite_true, hu', onSumcheck]
  rw [he]
  simp only [hst, ↓reduceIte]

/-- **The values read are the protocol's**: column `i` of opcode table `t` among the values of all
the columns is entry `i` of table `t`'s read. -/
theorem tableValues_eq (evs : List (List E)) (hlen : evs.length = 6)
    (hw : ∀ t : Fin 6, (evs.getD t []).length = width (opIdx t)) (t : Fin 6)
    (i : Fin ((leanIsaInstance F prog s).width (stEquiv F prog s t).1)) :
    tableValues (leanIsaInstance F prog s) (vecOf _ evs.flatten) (stEquiv F prog s t) i =
      (evs.getD t []).getD i 0 := by
  unfold tableValues
  simp only [vecOf, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [show (((columnPos (leanIsaInstance F prog s)) ⟨stEquiv F prog s t, i⟩ : Fin _) : ℕ) = _
    from position_val _ _ _, prefix_onSumcheck]
  have hsum : ∑ u ∈ range t, (if h : u < 6 then
      (leanIsaInstance F prog s).width (opI F prog s ⟨u, h⟩) else 0) =
      ∑ u ∈ range t, (evs.getD u []).length := Finset.sum_congr rfl fun u hu ↦ by
    have hu' : u < 6 := lt_of_lt_of_le (Finset.mem_range.mp hu) (by omega)
    simp only [hu', ↓reduceDIte]
    exact (hw ⟨u, hu'⟩).symm
  rw [hsum]
  exact flatten_getD evs t i (by rw [hlen]; exact t.isLt) (by rw [hw t]; exact i.isLt)

/-! ## The terms of a table -/

/-- A sum over a list's positions, as a sum over the indices. -/
theorem sum_fin_length {α : Type} (l : List α) (c : ℕ) (ξ : E) (g : α → E) :
    ∑ i : Fin l.length, ξ ^ (c + i.val) * g l[i] =
      ∑ k ∈ range l.length, ξ ^ (c + k) * (l.map g).getD k 0 := by
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map]
  rfl

/-- The constraints of opcode table `t`, batched by `ξ` at their positions, are the Python's. -/
theorem consPart_eq (ξ : E) (t : Fin 6)
    (e : Fin ((leanIsaInstance F prog s).width (stEquiv F prog s t).1) → E) (ev : List E)
    (hev : ∀ i, ev.getD i 0 = rowE e i) :
    ∑ i : Fin ((leanIsaInstance F prog s).constraints (stEquiv F prog s t).1).length,
        ξ ^ (constraintPos (leanIsaInstance F prog s) ⟨stEquiv F prog s t, i⟩ : ℕ) *
          evalRow ((leanIsaInstance F prog s).constraints (stEquiv F prog s t).1)[i] e =
      pyCons ξ t ev := by
  let c₀ := ∑ u ∈ range t, if h : u < 6 then
    ((leanIsaInstance F prog s).constraints (opI F prog s ⟨u, h⟩)).length else 0
  have hpos : ∀ i, (constraintPos (leanIsaInstance F prog s) ⟨stEquiv F prog s t, i⟩ : ℕ) =
      c₀ + i := fun i ↦ by
    rw [show ((constraintPos (leanIsaInstance F prog s) ⟨stEquiv F prog s t, i⟩ : Fin _) : ℕ) = _
      from position_val _ _ _, prefix_onSumcheck]
  rw [Finset.sum_congr rfl fun i _ ↦ by rw [hpos i],
    sum_fin_length ((leanIsaInstance F prog s).constraints (stEquiv F prog s t).1) c₀ ξ
      (fun P ↦ evalRow P e)]
  have hlen := constraints_opIdx_length t
  by_cases ht : t = 4
  · subst ht
    have hc : c₀ = 0 := by
      simp only [c₀]
      refine Finset.sum_eq_zero fun u hu ↦ ?_
      have hu' : u < 4 := Finset.mem_range.mp hu
      simp only [show u < 6 by omega, ↓reduceDIte]
      have := constraints_opIdx_length ⟨u, by omega⟩
      rw [ite_eq_right_of_eq_false _ _
        (eq_false fun h ↦ by have := congrArg Fin.val h; simp at this; omega)]
        at this
      exact this
    have hmap : ((leanIsaInstance F prog s).constraints (stEquiv F prog s 4).1).map
        (evalRow · e) = jumpConstraints ev := (jumpConstraints_evalE e ev hev).symm
    rw [hc, hmap, show ((leanIsaInstance F prog s).constraints (stEquiv F prog s 4).1).length = 2
      from hlen, pyCons, ite_eq_left_of_eq_true _ _ (eq_true rfl), jumpConstraints_getD]
    simp [Finset.sum_range_succ, Whir.Complete.dot_cons]
  · rw [show ((leanIsaInstance F prog s).constraints (stEquiv F prog s t).1).length = 0 from
      hlen.trans (ite_eq_right_of_eq_false _ _ (eq_false ht)), pyCons,
      ite_eq_right_of_eq_false _ _ (eq_false ht), Finset.sum_range_zero]

/-- **What a table owes is the Python's**: at values `e` of opcode table `t`'s columns, read as
`ev`, the protocol's constraints and forms batched by `ξ` are the Python's. -/
theorem rowValue_eq (w : BusWit) (hp : w.point.length = (leanIsaInstance F prog s).μBus)
    (ha : w.alphas.length = 4) (ξ : E) (t : Fin 6)
    (e : Fin ((leanIsaInstance F prog s).width (stEquiv F prog s t).1) → E) (ev : List E)
    (hev : ∀ i, ev.getD i 0 = rowE e i) :
    rowValue (leanIsaInstance F prog s)
        (busStmt (leanIsaInstance F prog s) (leanIsa_conditions F prog s) input w, ξ)
        (stEquiv F prog s t) e =
      pyCons ξ t ev + pyForms ξ ((w.result (verifierLayout prog s)).forms.getD t []) ev := by
  have hcol : rowE e = fun i ↦ ev.getD i 0 := funext fun i ↦ (hev i).symm
  unfold rowValue pyForms
  refine congrArg₂ (· + ·) ?_ ?_
  · exact consPart_eq F prog s ξ t e ev hev
  · rw [sumcheckB_leanIsa F prog s, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [show (busStmt (leanIsaInstance F prog s) (leanIsa_conditions F prog s) input w).2 =
      Bus.busOut (leanIsa_conditions F prog s) (w.layer (leanIsaInstance F prog s) input)
        (w.vals (leanIsaInstance F prog s)) from rfl,
      formAt_busOut_forms F prog s input w hp ha k t e]
    exact congrArg (fun col ↦ ξ ^ (2 + (k : ℕ)) *
      (((w.result (verifierLayout prog s)).forms.getD t []).getD k {}).evaluate col) hcol

/-! ## The formula -/

/-- What a read of the right shape is: six lists, one per table, of the table's width. -/
theorem readShape_facts (w : BusWit) (pt : List E) (evs : List (List E))
    (hs : ReadShape (rowsOf (verifierLayout prog s) (w.result (verifierLayout prog s)) pt) evs) :
    evs.length = 6 ∧ ∀ t : Fin 6, (evs.getD t []).length = width (opIdx t) := by
  rw [rowsOf_eq prog s _ (result_forms_shape prog s w).1] at hs
  have hl := hs.length_eq
  simp only [List.length_cons, List.length_nil] at hl
  refine ⟨hl.symm, fun t ↦ ?_⟩
  rw [width_opIdx]
  obtain ⟨-, h⟩ := List.forall₂_iff_get.mp hs
  have := h t (by simp) (by rw [← hl]; exact t.isLt)
  rw [List.getD_eq_getElem _ _ (by rw [← hl]; exact t.isLt)]
  fin_cases t <;> exact this

/-- **The final check's value is the protocol's formula**: at the reversed challenges and the
values read, the Python's final value is the table sumcheck's formula. -/
theorem formula_leanIsa (w : BusWit) (hp : w.point.length = (leanIsaInstance F prog s).μBus)
    (ha : w.alphas.length = 4) (ξ : E) (ch : List E) (evs : List (List E))
    (hch : ch.length = (leanIsaInstance F prog s).τmax)
    (hs : ReadShape (rowsOf (verifierLayout prog s) (w.result (verifierLayout prog s)) ch.reverse)
      evs) :
    (pyTableTerms (cpsOf ξ) (fpsOf ξ) ch.reverse
        (rowsOf (verifierLayout prog s) (w.result (verifierLayout prog s)) ch.reverse) evs 0 0
        []).1 =
      formula (leanIsaInstance F prog s)
        (busStmt (leanIsaInstance F prog s) (leanIsa_conditions F prog s) input w, ξ)
        (vecOf (leanIsaInstance F prog s).τmax ch).reverse
        (vecOf (leanIsaInstance F prog s).tableColumns evs.flatten) := by
  obtain ⟨hlen, hw⟩ := readShape_facts prog s w _ evs hs
  rw [pyTableTerms_eq prog s w ξ ch.reverse evs hs]
  unfold TableSumcheck.formula
  rw [← (stEquiv F prog s).sum_comp]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  have hev : ∀ i, (evs.getD t []).getD i 0 = rowE (tableValues (leanIsaInstance F prog s)
      (vecOf _ evs.flatten) (stEquiv F prog s t)) i := fun i ↦ by
    unfold rowE
    split_ifs with hi
    · exact (tableValues_eq F prog s evs hlen hw t ⟨i, hi⟩).symm
    · exact List.getD_eq_default _ _ (by rw [hw t]; exact not_lt.mp hi)
  rw [prodWeight_eq F prog s input w ch hch t, rowValue_eq F prog s input w hp ha ξ t _ _ hev]

/-! ## The claims -/

/-- The claims the final loop returns: the given ones, then every table's values, each on its
column at the point's first `height` coordinates. -/
theorem pyTableTerms_snd (cps fps pt : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (evs : List (List E)) (cursor : ℕ) (final : E)
      (claims : List Verifier.ColumnClaim),
      (pyTableTerms cps fps pt rows evs cursor final claims).2 = claims ++
        (List.zip rows evs).flatMap fun p ↦ p.2.zipIdx.map fun (value, column) ↦
          (⟨globalColumnBases.getD p.1.1.opcode 0 + column, pt.take p.1.2.1, value⟩ :
            Verifier.ColumnClaim)
  | [], _, _, _, claims => by simp [pyTableTerms]
  | _ :: _, [], _, _, claims => by simp [pyTableTerms]
  | (table, height, forms, weight) :: rest, ev :: evs, cursor, final, claims => by
    rw [pyTableTerms, pyTableTerms_snd cps fps pt rest evs]
    simp

/-- The bus phase's claims, listed: the three memory columns, `MFCNT` and `BFCNT`. -/
theorem result_claims (w : BusWit) (hm : w.memory.length = 3) :
    (w.result (verifierLayout prog s)).claims =
      [⟨0, w.point.take s.logMem, w.memory.getD 0 0⟩, ⟨1, w.point.take s.logMem, w.memory.getD 1 0⟩,
        ⟨2, w.point.take s.logMem, w.memory.getD 2 0⟩, ⟨3, w.point.take s.logMem, w.mf⟩,
        ⟨4, w.point.take prog.logSize, w.bf⟩] := by
  obtain ⟨a, b, c, habc⟩ : ∃ a b c, w.memory = [a, b, c] := by
    match h : w.memory, hm with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  rw [result_eq_busOut, habc]
  rfl

/-- The low coordinates of a list read as a vector. -/
theorem ofFn_vecOf (p : List E) {μ m : ℕ} (hm : m ≤ μ) (hp : p.length = μ) :
    (List.ofFn fun j : Fin m ↦ (vecOf μ p)[j.val]'(by omega)) = p.take m := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_ofFn, vecOf, Vector.getElem_ofFn, List.getElem_take]
  rw [List.getD_eq_getElem _ _ (by simp at h1; omega)]

/-- **The protocol's bus claims are the program's.** -/
theorem busOut_columns_mem (w : BusWit) (hp : w.point.length = (leanIsaInstance F prog s).μBus)
    (hm : w.memory.length = 3)
    (c : ColumnClaim (leanIsaInstance F prog s))
    (hc : c ∈ (Bus.busOut (leanIsa_conditions F prog s) (w.layer (leanIsaInstance F prog s) input)
      (w.vals (leanIsaInstance F prog s))).columns.toList) :
    (⟨pyCol c.col, c.point.toList, c.value⟩ : Verifier.ColumnClaim) ∈
      (w.result (verifierLayout prog s)).claims := by
  simp only [Bus.busOut, Vector.toList_ofFn, List.mem_ofFn] at hc
  obtain ⟨⟨i, hi⟩, rfl⟩ := hc
  have h5 : (leanIsaInstance F prog s).busClaims = 5 := by
    show (leanIsaInstance F prog s).boundaryColumns.length = 5
    rw [boundaryColumns_leanIsa]
    rfl
  have hi5 : i < 5 := h5 ▸ hi
  have hbc := List.getElem_of_eq (boundaryColumns_leanIsa F prog s) hi
  have hval : (w.vals (leanIsaInstance F prog s))[i] = (w.memory ++ [w.mf, w.bf]).getD i 0 := by
    simp [BusWit.vals, vecOf]
  have hκ : (leanIsaInstance F prog s).κ (leanIsaInstance F prog s).boundaryColumns[i] ≤
      (leanIsaInstance F prog s).μBus :=
    (leanIsa_conditions F prog s).κ_le_of_boundaryColumn (List.getElem_mem hi)
  rw [result_claims prog s w hm]
  simp only [Bus.columnPoint, Gkr.lowPoint, Vector.toList_ofFn, Fin.getElem_fin, hval]
  rw [show (BusWit.layer (leanIsaInstance F prog s) input w).2.1 =
    vecOf (leanIsaInstance F prog s).μBus w.point from rfl, ofFn_vecOf w.point hκ hp]
  simp only [hbc]
  obtain ⟨a, b, c, habc⟩ : ∃ a b c, w.memory = [a, b, c] := by
    match h : w.memory, hm with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  rw [habc]
  interval_cases i
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))

/-- **The protocol's final claims are among the program's**: the claim on column `i` of opcode table
`t` at the final point is the program's claim on the same column. -/
theorem finalClaims_mem (ξ : E) (w : BusWit) (ch : List E) (evs : List (List E))
    (hch : ch.length = (leanIsaInstance F prog s).τmax)
    (hs : ReadShape (rowsOf (verifierLayout prog s) (w.result (verifierLayout prog s)) ch.reverse)
      evs)
    (c : ColumnClaim (leanIsaInstance F prog s))
    (hc : c ∈ (finalClaims (leanIsaInstance F prog s) (vecOf _ ch).reverse
      (vecOf (leanIsaInstance F prog s).tableColumns evs.flatten)).toList) :
    (⟨pyCol c.col, c.point.toList, c.value⟩ : Verifier.ColumnClaim) ∈
      (pyTableTerms (cpsOf ξ) (fpsOf ξ) ch.reverse
        (rowsOf (verifierLayout prog s) (w.result (verifierLayout prog s)) ch.reverse) evs 0 0
        []).2 := by
  obtain ⟨hlen, hw⟩ := readShape_facts prog s w _ evs hs
  simp only [finalClaims, Vector.toList_ofFn, List.mem_ofFn] at hc
  obtain ⟨k, rfl⟩ := hc
  obtain ⟨⟨j, i⟩, hk⟩ : ∃ p, (columnPos (leanIsaInstance F prog s)).symm k = p := ⟨_, rfl⟩
  obtain ⟨t, rfl⟩ := (stEquiv F prog s).surjective j
  have hk' : k = columnPos (leanIsaInstance F prog s) ⟨stEquiv F prog s t, i⟩ := by
    rw [← hk, Equiv.apply_symm_apply]
  have hv : (vecOf (leanIsaInstance F prog s).tableColumns evs.flatten)[k] =
      (evs.getD t []).getD i 0 := by
    subst hk'
    exact tableValues_eq F prog s evs hlen hw t i
  have hi : i.val < (evs.getD t []).length := by rw [hw t]; exact i.isLt
  simp only [finalClaim, hv]
  rw [pyTableTerms_snd, List.nil_append, List.mem_flatMap]
  refine ⟨(pyRow s (w.result (verifierLayout prog s)) ch.reverse t, evs.getD t []), ?_, ?_⟩
  · rw [rowsOf_eq prog s _ (result_forms_shape prog s w).1, list_six evs [] hlen]
    fin_cases t <;> simp
  · refine List.mem_map.mpr ⟨((evs.getD t []).getD i 0, i), ?_, ?_⟩
    · rw [List.mk_mem_zipIdx_iff_getElem?, List.getD_eq_getElem _ _ hi]
      simp
    · simp only [pyRow, Complete.opcode_tables]
      have hcol := pyCol_opIdx t i
      have hpt : (M3Instance.lowPoint (leanIsaInstance F prog s) (vecOf _ ch).reverse
          (stEquiv F prog s t)).toList = ch.reverse.take (s.τ t) := by
        simp only [M3Instance.lowPoint, Vector.toList_cast, Vector.take_eq_extract,
          Vector.toList_extract, Vector.toList_reverse, toList_vecOf _ hch,
          List.drop_zero, Nat.sub_zero]
        rfl
      rw [hk]
      simp only [hpt]
      exact congrArg (fun n ↦ (⟨n, ch.reverse.take (s.τ t), (evs.getD t []).getD i 0⟩ :
        Verifier.ColumnClaim)) hcol.symm

/-! ## The table phase's identities -/

/-- **The table phase's identities hold at leanISA**, at the verifier's layout and the global
column numbering `pyCol`, for every read of the bus phase of the right shape whose fingerprint
challenges are four. -/
theorem tableFid_leanIsa (hI : Bus.Conditions (leanIsaInstance F prog s)) (w : BusWit)
    (hw : w.Shaped (leanIsaInstance F prog s)) (ha : w.alphas.length = 4) :
    TableFid (leanIsaInstance F prog s) hI input (verifierLayout prog s) pyCol w where
  rounds := rounds_leanIsa F prog s
  target ξ := target_leanIsa F prog s input w hw.1 ha hw.2.2 ξ
  formula ξ ch evs hch hs := formula_leanIsa F prog s input w hw.1 ha ξ ch evs hch hs
  claims ξ ch claim evs hch hs c hc := by
    simp only [tableOut, tableStmt, Vector.toList_append, List.mem_append] at hc
    rcases hc with hc | hc
    · exact List.mem_append_left _ (busOut_columns_mem F prog s input w hw.1 hw.2.2 c hc)
    · exact List.mem_append_right _ (finalClaims_mem F prog s ξ w ch evs hch hs c hc)

/-! ## The bus phase's depth -/

/-- Summing over a list with repetitions. -/
theorem sum_flatMap_replicate' {α : Type} (l : List α) (a f : α → ℕ) (g : ℕ → ℕ) :
    ((l.flatMap fun x ↦ List.replicate (a x) (f x)).map g).sum =
      (l.map fun x ↦ a x * g (f x)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_replicate,
      List.sum_replicate, smul_eq_mul, List.map_cons, List.sum_cons]

/-- The push side's leaves are its blocks' sizes summed. -/
theorem pushLeaves_eq_leafCount (I : M3Instance) : I.pushLeaves = Bus.leafCount I 0 := by
  rw [Bus.leafCount, M3Instance.pushLeaves]
  change _ = ((Bus.sideSources I .push).map fun src ↦ 2 ^ src.κ).sum
  rw [show (fun src : Bus.Source I ↦ 2 ^ src.κ) = (2 ^ ·) ∘ Bus.Source.κ from rfl,
    ← List.map_map, Bus.sideSources_map_κ, List.map_append,
    List.sum_append, sum_flatMap_replicate', List.map_map]
  rfl

/-- **The push side's leaves at leanISA** are the Python's push layout's total. -/
theorem pushLeaves_eq_pushTotal : (leanIsaInstance F prog s).pushLeaves =
    Complete.blockTotal (Complete.sideSizes (Complete.fwLogs prog s) (Complete.pushBlocks s)) := by
  rw [pushLeaves_eq_leafCount, Bus.leafCount, Complete.blockTotal_eq,
    show (fun src : Bus.Source (leanIsaInstance F prog s) ↦ 2 ^ src.κ) = (2 ^ ·) ∘ Bus.Source.κ
      from rfl, ← List.map_map, sources_zero, sideSources_map_κ F prog s .push _ (pushBlocks_eq s)]
  rfl

/-- **The bus phase's depth** at the verifier's layout is the instance's `μ_bus`. -/
theorem busDepth_leanIsa :
    (busLayout [0, (verifierLayout prog s).logMemory, (verifierLayout prog s).logBytecode]
      (verifierLayout prog s).push).depth = (leanIsaInstance F prog s).μBus := by
  rw [Complete.busLayout_depth_verifier, Complete.busDepth, log2Ceil_eq_clog, M3Instance.μBus,
    pushLeaves_eq_pushTotal]

/-- **The leaf stacks have a variable**: `μ_bus ≠ 0` at leanISA. -/
theorem μBus_ne_zero : (leanIsaInstance F prog s).μBus ≠ 0 := by
  rw [M3Instance.μBus, pushLeaves_eq_pushTotal, Complete.blockTotal_eq]
  refine (Nat.clog_pos (by norm_num) ?_).ne'
  simp only [Complete.sideSizes, Complete.fwLogs, List.map_append, List.sum_append, List.map_cons,
    List.sum_cons, pow_zero]
  rw [add_assoc]
  exact Nat.lt_add_of_pos_right (by positivity)

/-! ## The fingerprint challenges are four -/

section Spec

open LeanVM.Protocol.Compile

variable {εmax : ℝ≥0∞}

/-- `n` challenges are a list of `n`: continuations that agree on such lists give one program. -/
theorem sampleN_bind_congr {β : Type} : ∀ (n : ℕ) (k k' : List E → Prog β),
    (∀ as, as.length = n → k as = k' as) → (Prog.sampleN n).bind k = (Prog.sampleN n).bind k'
  | 0, k, k', h => h [] rfl
  | n + 1, k, k', h => by
    simp only [Prog.sampleN, Prog.bind_eq, Prog.bind_assoc]
    exact congrArg (Prog.sampleE.bind ·) (funext fun x ↦
      sampleN_bind_congr n _ _ fun as has ↦ h (x :: as) (by simp [has]))

/-- The guard that the fingerprint challenges are four. -/
def abGuard (ab : List E × E) : Prog (List E × E) :=
  if ab.1.length = 4 then Prog.ret ab else Prog.fail

/-- The wire's fingerprint challenges are four: guarding it changes nothing. -/
theorem abProg_bind_guard : abProg.bind abGuard = abProg := by
  unfold abProg
  rw [Prog.bind_assoc]
  refine sampleN_bind_congr 4 _ _ fun as has ↦ ?_
  rw [Prog.bind_assoc]
  refine congrArg (Prog.sampleE.bind ·) (funext fun b ↦ ?_)
  simp [abGuard, has]

variable (I : M3Instance) (hI : Bus.Conditions I) (cands : Word → Set (∀ i, TheOracle I i))
  (input : I.Stmt) (layout : Verifier.Layout)

/-- **The fingerprint challenges, four of them**: `abSpec` with the length of the challenges
recorded. -/
noncomputable def abSpec4 {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hlt : abError I L₀ < 1) :
    Spec abProg (HDoom cands (Seam.commit I) input)
      (fun ab h ↦ ab.1.length = 4 ∧
        HDoom cands (Bus.afterChallenge I) (input, (toAlpha ab.1, ab.2)) h) εmax
      (abError I L₀ + 0) 0 :=
  let P4 : List E × E → List Ev → Prop := fun ab h ↦ ab.1.length = 4 ∧
    HDoom cands (Bus.afterChallenge I) (input, (toAlpha ab.1, ab.2)) h
  let G : ∀ ab : List E × E, Spec (abGuard ab)
      (fun h ↦ HDoom cands (Bus.afterChallenge I) (input, (toAlpha ab.1, ab.2)) h) P4 εmax 0 0 :=
    fun ab ↦ if h : ab.1.length = 4 then
      Spec.congr (p := Prog.ret ab) (by simp [abGuard, h])
        ((Spec.ret (Post := P4) ab).mono (fun _ hp ↦ ⟨h, hp⟩) (fun _ _ hq ↦ hq) le_rfl le_rfl
          le_rfl)
    else Spec.congr (p := Prog.fail) (by simp [abGuard, h]) Spec.fail
  Spec.congr abProg_bind_guard ((abSpec I cands input hI hfin hcard hlt (T := 0)).bind' G)

/-- **The bus phase's tail, then a continuation**, `busTailSpec` for continuations specified at
reads whose fingerprint challenges are four. -/
noncomputable def busTailSpec4 {β : Type} {k : BusWit → Prog β} {Q : β → List Ev → Prop}
    {Lk T : ℝ≥0∞} (hLk : Lk ≤ εmax)
    (K : ∀ w : BusWit, w.alphas.length = 4 → Spec (k w) (BusAt I hI cands input w) Q εmax Lk T)
    (alphas : List E) (halpha : alphas.length = 4) (beta : E) (r : E × List E × List E) :
    Spec (busTailK k alphas beta r) (GkrPost I cands (input, (toAlpha alphas, beta)) r) Q
      εmax 0 T :=
  match r with
  | (countRoot, point, values) =>
    let P : List Ev → Prop := fun h ↦ point.length = I.μBus ∧ values.length = 3 ∧
      HDoom cands (Gkr.relOut 3 I.μBus (Bus.leaves I) (Bus.riders I))
        (layerStmtOf (input, (toAlpha alphas, beta)) I.μBus ⟨values, point⟩) h
    have hP : ∀ h x, P h → P (h ++ [Ev.read x]) := fun _ _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2.append _⟩
    (Spec.require (Post := fun _ h ↦ P h) fun _ hp hc ↦ hp.resolve_left hc).bind' fun _ ↦
    (readNSuccSpec P hP zero_le 2).bind' fun memory ↦
    (Spec.readE (Post := fun _ h ↦ memory.length = 3 ∧ P h)
      (fun _ _ hp ↦ ⟨hp.1, hP _ _ hp.2⟩) zero_le).bind' fun mf ↦
    (Spec.readE (Post := fun bf h ↦ BusAt I hI cands input ⟨alphas, beta, point, values, memory,
        mf, bf⟩ h)
      (fun _ bf hp ↦ by
        obtain ⟨hm, hl, hv, W, hW, hR⟩ := hp
        exact ⟨hl, hv, hm, W, firstWord_append hW _, values_keep I hI hR _⟩) hLk).bind'
      fun bf ↦ K ⟨alphas, beta, point, values, memory, mf, bf⟩ halpha

/-- **The bus phase, then a continuation**, `busThenSpec` for continuations specified at reads
whose fingerprint challenges are four. -/
noncomputable def busThenSpec4 {β : Type} {f : BusResult → Prog β} {Q : β → List Ev → Prop}
    {Lk T : ℝ≥0∞} (hLk : Lk ≤ εmax)
    (K : ∀ w : BusWit, w.alphas.length = 4 →
      Spec (f (w.result layout)) (BusAt I hI cands input w) Q εmax Lk T)
    {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hμ : I.μBus ≠ 0)
    (hdepth : (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth = I.μBus)
    (hab : abError I L₀ < 1) (he : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax) :
    Spec ((verifyBusBalance .computed layout).bind f) (HDoom cands (Seam.commit I) input) Q εmax
      (abError I L₀ + 0) T :=
  Spec.congr (verifyBusBalance_bind_eq layout f).symm
    ((abSpec4 I hI cands input hfin hcard hab).bind' fun ab ↦
      if h : ab.1.length = 4 then
        ((Spec.congr (by rw [hdepth])
          (gkrSpec I cands (input, (toAlpha ab.1, ab.2)) hI hfin hcard hμ he hT hlam)).bind'
          fun r ↦ busTailSpec4 I hI cands input hLk K ab.1 h ab.2 r).mono (fun _ hp ↦ hp.2)
          (fun _ _ hq ↦ hq) le_rfl le_rfl le_rfl
      else specOfFalse fun _ hp ↦ h hp.1)

end Spec

/-! ## The bus phase and the table sumcheck at leanISA -/

section LeanIsaSpec

open LeanVM.Protocol.Compile

variable {εmax : ℝ≥0∞} (cands : Word → Set (∀ i, TheOracle (leanIsaInstance F prog s) i))

/-- **The bus phase, then the table sumcheck, at leanISA**: `busTableSpec` at the leanISA
instance and the verifier's layout, with every fidelity hypothesis discharged (`TableFid` by
`tableFid_leanIsa`, `μ_bus ≠ 0` by `μBus_ne_zero`, the push layout's depth by `busDepth_leanIsa`).
Only the error hypotheses remain. -/
noncomputable def busTableSpec_leanIsa {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hab : abError (leanIsaInstance F prog s) L₀ < 1)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) {T : ℝ≥0∞} (he3 : roundError L₀ 3 + T ≤ εmax)
    (hTf : T ≤ εmax)
    (hxi : xiError (leanIsaInstance F prog s) L₀ + sumcheckLead
      (List.replicate ((verifierLayout prog s).tableLogHeights.foldl max 0) none) T ≤ εmax) :
    Spec ((verifyBusBalance .computed (verifierLayout prog s)).bind (tablePhase (verifierLayout prog s)))
      (HDoom cands (Seam.commit (leanIsaInstance F prog s)) input)
      (TablePost (leanIsaInstance F prog s) cands input pyCol) εmax
      (abError (leanIsaInstance F prog s) L₀ + 0) T :=
  busThenSpec4 (leanIsaInstance F prog s) (leanIsa_conditions F prog s) cands input
    (verifierLayout prog s) hxi
    (fun w h4 ↦ if hw : w.Shaped (leanIsaInstance F prog s) then
      tablePhaseSpec (leanIsaInstance F prog s) (leanIsa_conditions F prog s) cands input
        (verifierLayout prog s) pyCol w
        (tableFid_leanIsa F prog s input (leanIsa_conditions F prog s) w hw h4) le_rfl hfin hcard
        he3 hTf
    else specOfFalse fun _ hp ↦ hw ⟨hp.1, hp.2.1, hp.2.2.1⟩)
    hfin hcard (μBus_ne_zero F prog s) (busDepth_leanIsa F prog s) hab he4 hT hlam

end LeanIsaSpec

end
end LeanVM.Protocol.EndToEnd.Front
