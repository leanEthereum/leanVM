/-
  LeanVM.Protocol.EndToEnd.Front.TableFidLeanIsa

  The table phase's identities (`TableFid`) at the leanISA instance and the verifier's layout, and
  the bus phase's depth conditions: the bus phase followed by the table sumcheck, specified with
  no fidelity hypothesis left.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Protocol.EndToEnd.Front.TableFidLeanIsaBus
public import LeanVM.Protocol.EndToEnd.Front.BusTable
public import LeanVM.Protocol.EndToEnd.Complete.TableMath

/-!
# The table phase's identities at leanISA

The bus/table bridge (`busTableSpec`, `LeanVM.Protocol.EndToEnd.Front.BusTable`) specifies the
verifier program's bus phase and table sumcheck (`crates/verifier/src/bus.rs:130-297`) on the oracle protocol's relations, given three facts
about the instance and the layout. This module proves them at the leanISA instance
`leanIsaWith prog s fl` and the verifier's layout `verifierLayout prog s`, for every program
`prog` and size vector `s`:

* `tableFid_leanIsa`: the table phase's identities (`TableFid`, with the global column numbering
  `refCol`) for every read of the bus phase of the right shape whose slot weights are sixteen: the rounds are `τ_max` (`rounds_leanIsa`); the target `Σ_s ξ^(2+s) · totals[s]` is the
  protocol's batched claim (`target_leanIsa`); the final check's value is the protocol's formula
  at the reversed challenges and the values read (`formula_leanIsa`: weights `prodWeight_eq`,
  values `tableValues_eq`, constraints and forms `rowValue_eq`); every claim of the protocol's
  output is the program's (`busOut_columns_mem`, `finalClaims_mem`);
* `μBus_ne_zero` and `busDepth_leanIsa`: the leaf stacks have a variable, and the push layout's
  depth is `μ_bus`;
* `busTableSpec_leanIsa`: the bus phase, then the table sumcheck, at leanISA, with no fidelity
  hypothesis left, only the error hypotheses.

**The slot weights are sixteen.** The boundary blocks' fingerprints are read sixteen weights at a
time (`bnd_push`), so `TableFid` is proved at reads with sixteen; the wire always draws sixteen
(`samples(2^BUS_BITS)`), and `busThenSpec` asks for the continuation only at such reads
(`abSpec16`, from `abProg_bind_guard`: guarding the wire's weights by their count changes
nothing). The share is the bytecode's (`BusWit.Shaped`, from the bus phase's `BusAt`).

**At every Keccak region.** The identities, the depth conditions and `busTableSpec_leanIsa` are
stated at `leanIsaWith prog s fl` (`Front.InstanceWith`, the region implicit), which the bus and
the table sumcheck do not read: at `fl = some (keccakRegion prog s)` they are the deployed
instance's, at `fl = none` the reduction-blind instance's.
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

/-- The number of constraints of the verifier's tables. -/
theorem nCons_eq : nCons = 2 := by
  unfold nCons
  rw [Complete.refNConstraints]
  rfl

/-- The constraint powers: `1, ξ`. -/
theorem cpsOf_eq (ξ : E) : cpsOf ξ = [1, ξ] := by
  simp [cpsOf, nCons_eq, nTrees, powers, powersFrom_eq, List.range_succ]

/-- The form powers: `ξ², ξ³, ξ⁴`. -/
theorem fpsOf_eq (ξ : E) : fpsOf ξ = [ξ ^ 2, ξ ^ 3, ξ ^ 4] := by
  simp [fpsOf, nCons_eq, nTrees, powers, powersFrom_eq, List.range_succ]

variable (prog : LeanIsaProgram) (s : Sizes) {fl : Option (KeccakRegion (shape prog s))}
  (input : PublicInput)

/-! ## The rounds and the target -/

/-- **The rounds**: the largest announced log-height is `τ_max`. -/
theorem rounds_leanIsa :
    (verifierLayout prog s).tableLogHeights.foldl max 0 = (leanIsaWith prog s fl).τmax :=
  (τmax_leanIsa prog s).symm

/-- **The target**: the form powers against the verifier's totals are the protocol's batched
claim. -/
theorem target_leanIsa (w : BusWit) (hp : w.point.length = (leanIsaWith prog s fl).μBus)
    (ha : w.alphas.length = 16) (hm : w.memory.length = 2)
    (hsh : w.share = shareTotal (vecOf (2 ^ 4) w.alphas)
      (slotValues (verifierLayout prog s).bytecode (w.point.take prog.logSize))) (ξ : E) :
    dot (fpsOf ξ) (w.result (verifierLayout prog s)).totals =
      powerBatch (claimed (leanIsaWith prog s fl)
        (busStmt (leanIsaWith prog s fl) (leanIsaWith_conditions prog s fl) input w)) ξ := by
  rw [powerBatch, claimed, Fin.sum_univ_add]
  simp only [Fin.append_left, zero_mul, Finset.sum_const_zero, zero_add, Fin.append_right,
    Fin.val_natAdd]
  rw [sumcheckB_leanIsa prog s, Whir.Complete.dot_eq_sum _ _ (by rw [fpsOf_eq]; rfl), fpsOf_eq,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [busStmt, busOut_totals prog s input w hp ha hm hsh i, mul_comm]
  fin_cases i <;> rfl

/-! ## The verifier's final value, table by table -/

/-- A list of six entries, listed. -/
theorem list_six {α : Type} (l : List α) (d : α) (h : l.length = 6) :
    l = [l.getD 0 d, l.getD 1 d, l.getD 2 d, l.getD 3 d, l.getD 4 d, l.getD 5 d] := by
  match l, h with
  | [a, b, c, e, f, g], _ => rfl

/-- The verifier's shape of the bus phase's forms: six tables, three sides each. -/
theorem result_forms_shape (w : BusWit) :
    (w.result (verifierLayout prog s)).forms.length = 6 ∧
      ∀ t < 6, ((w.result (verifierLayout prog s)).forms.getD t []).length = 3 := by
  rw [result_forms]
  obtain ⟨a1, a2, -, -⟩ := Complete.accFold_spec 0 (by norm_num) (w.alphas) w.beta
    _ _ Complete.forms0_length Complete.forms0_row
    (Complete.owner_lt_six s (Complete.pushBlocks_owned s) _)
  obtain ⟨b1, b2, -, -⟩ := Complete.accFold_spec 1 (by norm_num) (w.alphas) w.beta
    _ _ a1 a2 (Complete.owner_lt_six s (Complete.pullBlocks_owned s) _)
  obtain ⟨c1, c2, -, -⟩ := Complete.accFold_spec 2 (by norm_num) [1] 0
    _ _ b1 b2 (Complete.owner_lt_six s (Complete.countBlocks_owned s) _)
  exact ⟨c1, c2⟩

/-- The constraints' part of table `t` in the verifier's final value: only `JUMP` has any. -/
def refCons (ξ : E) (t : Fin 6) (ev : List E) : E :=
  if t = 4 then dot [1, ξ] (jumpConstraints ev) else 0

/-- The forms' part of table `t` in the verifier's final value. -/
def refForms (ξ : E) (fs : List Form) (ev : List E) : E :=
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
def refRow (bus : BusResult) (pt : List E) (t : Fin 6) : Table × ℕ × List Form × E :=
  (tables.getD t default, s.τ t, bus.forms.getD t [],
    (tableWeights (tableLogs s) bus.point pt).getD t 0)

/-- The rows of the final loop, listed. -/
theorem rowsOf_eq (bus : BusResult) (hf : bus.forms.length = 6) (pt : List E) :
    rowsOf (verifierLayout prog s) bus pt =
      [refRow s bus pt 0, refRow s bus pt 1, refRow s bus pt 2, refRow s bus pt 3, refRow s bus pt 4,
        refRow s bus pt 5] := by
  have hw : (tableWeights (tableLogs s) bus.point pt).length = 6 := by
    rw [Complete.length_tableWeights]; rfl
  have ht : tables.length = 6 := rfl
  have hl : (tableLogs s).length = 6 := by simp [tableLogs]
  unfold rowsOf refRow
  rw [show (verifierLayout prog s).tableLogHeights = tableLogs s from rfl]
  generalize tableWeights (tableLogs s) bus.point pt = W at hw ⊢
  apply List.ext_getElem (by simp [ht, hw, hf, hl])
  intro i h1 h2
  have hi : i < 6 := by simpa using h2
  simp only [List.getElem_zip]
  interval_cases i <;> simp [List.getD_eq_getElem?_getD, hw, hf, ht, tableLogs]

/-- **The verifier's final value** of the table sumcheck, table by table. -/
theorem refTableTerms_eq (w : BusWit) (ξ : E) (pt : List E) (evs : List (List E))
    (hs : ReadShape (rowsOf (verifierLayout prog s) (w.result (verifierLayout prog s)) pt) evs) :
    (refTableTerms (cpsOf ξ) (fpsOf ξ) pt
        (rowsOf (verifierLayout prog s) (w.result (verifierLayout prog s)) pt) evs 0 0 []).1 =
      ∑ t : Fin 6, (tableWeights (tableLogs s) w.point pt).getD t 0 *
        (refCons ξ t (evs.getD t []) +
          refForms ξ ((w.result (verifierLayout prog s)).forms.getD t []) (evs.getD t [])) := by
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
  simp only [refTableTerms, refRow, e0, e1, e2, e3, e4, e5, n0, n1, n2, n3, n4, hpt,
    Whir.Complete.dot_nil_right, add_zero, zero_add, List.drop_zero, Fin.sum_univ_six, refCons,
    refForms]
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
verifier's. -/
theorem prodWeight_eq (w : BusWit) (ch : List E)
    (hch : ch.length = (leanIsaWith prog s fl).τmax) (t : Fin 6) :
    prodWeight (tableWeights (leanIsaWith prog s fl)
        (busStmt (leanIsaWith prog s fl) (leanIsaWith_conditions prog s fl) input w).2.point
        (stEquiv prog s fl t)) (vecOf _ ch).reverse =
      (Verifier.tableWeights (tableLogs s) w.point ch.reverse).getD t 0 := by
  rw [Complete.getD_tableWeights _ _ _ _ (by simp [tableLogs]), List.length_reverse, hch,
    prodWeight, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  have hz : ((vecOf (leanIsaWith prog s fl).τmax ch).reverse)[a.val] = ch.reverse.getD a 0 := by
    rw [Vector.getElem_reverse, List.getD_eq_getElem _ _ (by simp [hch]), List.getElem_reverse]
    simp only [vecOf, Vector.getElem_ofFn]
    rw [List.getD_eq_getElem _ _ (by omega)]
    congr 1
    omega
  have hζ :
      ((busStmt (leanIsaWith prog s fl) (leanIsaWith_conditions prog s fl) input
        w).2.point)[a.val] =
      w.point.getD a 0 := by
    simp [busStmt, Bus.busOut, Bus.point, Gkr.lowPoint, BusWit.layer, layerStmtOf, vecOf]
  have hτ : (tableLogs s).getD t 0 = (leanIsaWith prog s fl).τ (stEquiv prog s fl t).1 := by
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

/-- A prefix sum over the instance's tables, kept on the sumcheck tables, as a sum over the
opcode tables before. -/
theorem prefix_onSumcheck (f : Fin (leanIsaWith prog s fl).ntab → ℕ) (t : Fin 6) :
    ∑ j : Fin (stEquiv prog s fl t).1.val,
        onSumcheck (leanIsaWith prog s fl) f (Fin.castLE (stEquiv prog s fl t).1.isLt.le j) =
      ∑ u ∈ range t, if h : u < 6 then f (opI prog s fl ⟨u, h⟩) else 0 := by
  let G : ℕ → ℕ := fun k ↦ if h : k < 9 then onSumcheck (leanIsaWith prog s fl) f ⟨k, h⟩ else 0
  have hL : ∑ j : Fin (stEquiv prog s fl t).1.val,
      onSumcheck (leanIsaWith prog s fl) f (Fin.castLE (stEquiv prog s fl t).1.isLt.le j) =
        ∑ k ∈ range (3 + t), G k := by
    rw [show 3 + t.val = (stEquiv prog s fl t).1.val by simp [opIdx]; omega,
      ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hj : j.val < 9 := lt_trans j.isLt (stEquiv prog s fl t).1.isLt
    simp only [G, hj, dite_true]
    rfl
  rw [hL, Finset.sum_range_add]
  have h0 : ∑ k ∈ range 3, G k = 0 := Finset.sum_eq_zero fun k hk ↦ by
    have hk' := Finset.mem_range.mp hk
    simp only [G, show k < 9 by omega, dite_true, onSumcheck]
    exact ite_eq_right_iff.mpr fun hs ↦
      absurd (three_le_of_sumcheckTable prog s _ hs) (by simp; omega)
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  have hu' : u < 6 := lt_of_lt_of_le (Finset.mem_range.mp hu) (by omega)
  have he : (⟨3 + u, by show 3 + u < 9; omega⟩ : Fin (leanIsaWith prog s fl).ntab) =
      opI prog s fl ⟨u, hu'⟩ :=
    Fin.ext (by simp [opI, opIdx]; omega)
  have hst : (leanIsaWith prog s fl).SumcheckTable (opI prog s fl ⟨u, hu'⟩) :=
    sumcheckTable_opIdx prog s ⟨u, hu'⟩
  simp only [G, show 3 + u < 9 by omega, dite_true, hu', onSumcheck]
  rw [he]
  simp only [hst, ↓reduceIte]

/-- **The values read are the protocol's**: column `i` of opcode table `t` among the values of all
the columns is entry `i` of table `t`'s read. -/
theorem tableValues_eq (evs : List (List E)) (hlen : evs.length = 6)
    (hw : ∀ t : Fin 6, (evs.getD t []).length = width (opIdx t)) (t : Fin 6)
    (i : Fin ((leanIsaWith prog s fl).width (stEquiv prog s fl t).1)) :
    tableValues (leanIsaWith prog s fl) (vecOf _ evs.flatten) (stEquiv prog s fl t) i =
      (evs.getD t []).getD i 0 := by
  unfold tableValues
  simp only [vecOf, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [show (((columnPos (leanIsaWith prog s fl)) ⟨stEquiv prog s fl t, i⟩ : Fin _) : ℕ) = _
    from position_val _ _ _, prefix_onSumcheck]
  have hsum : ∑ u ∈ range t, (if h : u < 6 then
      (leanIsaWith prog s fl).width (opI prog s fl ⟨u, h⟩) else 0) =
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

/-- The constraints of opcode table `t`, batched by `ξ` at their positions, are the verifier's. -/
theorem consPart_eq (ξ : E) (t : Fin 6)
    (e : Fin ((leanIsaWith prog s fl).width (stEquiv prog s fl t).1) → E) (ev : List E)
    (hev : ∀ i, ev.getD i 0 = rowE e i) :
    ∑ i : Fin ((leanIsaWith prog s fl).constraints (stEquiv prog s fl t).1).length,
        ξ ^ (constraintPos (leanIsaWith prog s fl) ⟨stEquiv prog s fl t, i⟩ : ℕ) *
          evalRow ((leanIsaWith prog s fl).constraints (stEquiv prog s fl t).1)[i] e =
      refCons ξ t ev := by
  let c₀ := ∑ u ∈ range t, if h : u < 6 then
    ((leanIsaWith prog s fl).constraints (opI prog s fl ⟨u, h⟩)).length else 0
  have hpos : ∀ i, (constraintPos (leanIsaWith prog s fl) ⟨stEquiv prog s fl t, i⟩ : ℕ) =
      c₀ + i := fun i ↦ by
    rw [show ((constraintPos (leanIsaWith prog s fl) ⟨stEquiv prog s fl t, i⟩ : Fin _) : ℕ) = _
      from position_val _ _ _, prefix_onSumcheck]
  rw [Finset.sum_congr rfl fun i _ ↦ by rw [hpos i],
    sum_fin_length ((leanIsaWith prog s fl).constraints (stEquiv prog s fl t).1) c₀ ξ
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
    have hmap : ((leanIsaWith prog s fl).constraints (stEquiv prog s fl 4).1).map
        (evalRow · e) = jumpConstraints ev := (jumpConstraints_evalE e ev hev).symm
    rw [hc, hmap, show ((leanIsaWith prog s fl).constraints (stEquiv prog s fl 4).1).length = 2
      from hlen, refCons, ite_eq_left_of_eq_true _ _ (eq_true rfl), jumpConstraints_getD]
    simp [Finset.sum_range_succ, Whir.Complete.dot_cons]
  · rw [show ((leanIsaWith prog s fl).constraints (stEquiv prog s fl t).1).length = 0 from
      hlen.trans (ite_eq_right_of_eq_false _ _ (eq_false ht)), refCons,
      ite_eq_right_of_eq_false _ _ (eq_false ht), Finset.sum_range_zero]

/-- **What a table owes is the verifier's**: at values `e` of opcode table `t`'s columns, read as
`ev`, the protocol's constraints and forms batched by `ξ` are the verifier's. -/
theorem rowValue_eq (w : BusWit) (hp : w.point.length = (leanIsaWith prog s fl).μBus)
    (ha : w.alphas.length = 16) (ξ : E) (t : Fin 6)
    (e : Fin ((leanIsaWith prog s fl).width (stEquiv prog s fl t).1) → E) (ev : List E)
    (hev : ∀ i, ev.getD i 0 = rowE e i) :
    rowValue (leanIsaWith prog s fl)
        (busStmt (leanIsaWith prog s fl) (leanIsaWith_conditions prog s fl) input w, ξ)
        (stEquiv prog s fl t) e =
      refCons ξ t ev + refForms ξ ((w.result (verifierLayout prog s)).forms.getD t []) ev := by
  have hcol : rowE e = fun i ↦ ev.getD i 0 := funext fun i ↦ (hev i).symm
  unfold rowValue refForms
  refine congrArg₂ (· + ·) ?_ ?_
  · exact consPart_eq prog s ξ t e ev hev
  · rw [sumcheckB_leanIsa prog s, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [show (busStmt (leanIsaWith prog s fl) (leanIsaWith_conditions prog s fl) input w).2 =
      Bus.busOut (leanIsaWith_conditions prog s fl) (w.layer (leanIsaWith prog s fl) input)
        (w.vals (leanIsaWith prog s fl)) from rfl,
      formAt_busOut_forms prog s input w hp ha k t e]
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
values read, the verifier's final value is the table sumcheck's formula. -/
theorem formula_leanIsa (w : BusWit) (hp : w.point.length = (leanIsaWith prog s fl).μBus)
    (ha : w.alphas.length = 16) (ξ : E) (ch : List E) (evs : List (List E))
    (hch : ch.length = (leanIsaWith prog s fl).τmax)
    (hs : ReadShape (rowsOf (verifierLayout prog s) (w.result (verifierLayout prog s)) ch.reverse)
      evs) :
    (refTableTerms (cpsOf ξ) (fpsOf ξ) ch.reverse
        (rowsOf (verifierLayout prog s) (w.result (verifierLayout prog s)) ch.reverse) evs 0 0
        []).1 =
      formula (leanIsaWith prog s fl)
        (busStmt (leanIsaWith prog s fl) (leanIsaWith_conditions prog s fl) input w, ξ)
        (vecOf (leanIsaWith prog s fl).τmax ch).reverse
        (vecOf (leanIsaWith prog s fl).tableColumns evs.flatten) := by
  obtain ⟨hlen, hw⟩ := readShape_facts prog s w _ evs hs
  rw [refTableTerms_eq prog s w ξ ch.reverse evs hs]
  unfold TableSumcheck.formula
  rw [← (stEquiv prog s fl).sum_comp]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  have hev : ∀ i, (evs.getD t []).getD i 0 = rowE (tableValues (leanIsaWith prog s fl)
      (vecOf _ evs.flatten) (stEquiv prog s fl t)) i := fun i ↦ by
    unfold rowE
    split_ifs with hi
    · exact (tableValues_eq prog s evs hlen hw t ⟨i, hi⟩).symm
    · exact List.getD_eq_default _ _ (by rw [hw t]; exact not_lt.mp hi)
  rw [prodWeight_eq prog s input w ch hch t, rowValue_eq prog s input w hp ha ξ t _ _ hev]

/-! ## The claims -/

/-- The claims the final loop returns: the given ones, then every table's values, each on its
column at the point's first `height` coordinates. -/
theorem refTableTerms_snd (cps fps pt : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (evs : List (List E)) (cursor : ℕ) (final : E)
      (claims : List Verifier.ColumnClaim),
      (refTableTerms cps fps pt rows evs cursor final claims).2 = claims ++
        (List.zip rows evs).flatMap fun p ↦ p.2.zipIdx.map fun (value, column) ↦
          (⟨globalColumnBases.getD p.1.1.opcode 0 + column, pt.take p.1.2.1, value⟩ :
            Verifier.ColumnClaim)
  | [], _, _, _, claims => by simp [refTableTerms]
  | _ :: _, [], _, _, claims => by simp [refTableTerms]
  | (table, height, forms, weight) :: rest, ev :: evs, cursor, final, claims => by
    rw [refTableTerms, refTableTerms_snd cps fps pt rest evs]
    simp

/-- The bus phase's claims, listed: the two memory limbs, `MFCNT` and `BFCNT`. -/
theorem result_claims (w : BusWit) (hm : w.memory.length = 2) :
    (w.result (verifierLayout prog s)).claims =
      [⟨0, w.point.take s.logMem, w.memory.getD 0 0⟩, ⟨1, w.point.take s.logMem, w.memory.getD 1 0⟩,
        ⟨2, w.point.take s.logMem, w.mf⟩, ⟨3, w.point.take prog.logSize, w.bf⟩] := by
  obtain ⟨a, b, habc⟩ : ∃ a b, w.memory = [a, b] := by
    match h : w.memory, hm with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  rw [result_eq_busOut, habc]
  rfl

/-- The low coordinates of a list read as a vector. -/
theorem ofFn_vecOf (p : List E) {μ m : ℕ} (hm : m ≤ μ) (hp : p.length = μ) :
    (List.ofFn fun j : Fin m ↦ (vecOf μ p)[j.val]'(by omega)) = p.take m := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_ofFn, vecOf, Vector.getElem_ofFn, List.getElem_take]
  rw [List.getD_eq_getElem _ _ (by simp at h1; omega)]

/-- The bus phase's values at `i`: the memory words, then the two finalize counts. -/
theorem busWit_vals_getElem (I : M3Instance) (w : BusWit) (i : ℕ) (hi : i < I.busClaims) :
    (w.vals I)[i] = (w.memory ++ [w.mf, w.bf]).getD i 0 := by
  simp only [BusWit.vals, vecOf, Vector.getElem_ofFn]

/-- The bus phase's point, as the layer's. -/
theorem busWit_layer_point (I : M3Instance) (input : I.Stmt) (w : BusWit) :
    (w.layer I input).2.1 = vecOf I.μBus w.point := rfl

/-- **The protocol's bus claims are the program's.** -/
theorem busOut_columns_mem (w : BusWit) (hp : w.point.length = (leanIsaWith prog s fl).μBus)
    (hm : w.memory.length = 2)
    (c : ColumnClaim (leanIsaWith prog s fl))
    (hc : c ∈ (Bus.busOut (leanIsaWith_conditions prog s fl)
      (w.layer (leanIsaWith prog s fl) input)
      (w.vals (leanIsaWith prog s fl))).columns.toList) :
    (⟨refCol c.col, c.point.toList, c.value⟩ : Verifier.ColumnClaim) ∈
      (w.result (verifierLayout prog s)).claims := by
  simp only [Bus.busOut, Vector.toList_ofFn, List.mem_ofFn] at hc
  obtain ⟨⟨i, hi⟩, rfl⟩ := hc
  have h5 : (leanIsaWith prog s fl).busClaims = 4 := by
    show (leanIsaWith prog s fl).boundaryColumns.length = 4
    rw [boundaryColumns_leanIsa]
    rfl
  have hi5 : i < 4 := h5 ▸ hi
  have hiL : i < (leanIsaWith prog s fl).boundaryColumns.length := by
    rw [boundaryColumns_leanIsa]; exact hi5
  have hbc := List.getElem_of_eq (boundaryColumns_leanIsa prog s) hiL
  -- The type inferred: stated, it makes the elaborator unfold the instance's columns.
  have hκ := (leanIsaWith_conditions prog s fl).κ_le_of_boundaryColumn (List.getElem_mem hiL)
  rw [result_claims prog s w hm]
  simp only [Bus.columnPoint, Gkr.lowPoint, Vector.toList_ofFn, Fin.getElem_fin,
    busWit_vals_getElem]
  simp only [busWit_layer_point]
  rw [ofFn_vecOf w.point hκ hp]
  simp only [hbc]
  obtain ⟨a, b, habc⟩ : ∃ a b, w.memory = [a, b] := by
    match h : w.memory, hm with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  rw [habc]
  interval_cases i
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self))

/-- **The protocol's final claims are among the program's**: the claim on column `i` of opcode table
`t` at the final point is the program's claim on the same column. -/
theorem finalClaims_mem (ξ : E) (w : BusWit) (ch : List E) (evs : List (List E))
    (hch : ch.length = (leanIsaWith prog s fl).τmax)
    (hs : ReadShape (rowsOf (verifierLayout prog s) (w.result (verifierLayout prog s)) ch.reverse)
      evs)
    (c : ColumnClaim (leanIsaWith prog s fl))
    (hc : c ∈ (finalClaims (leanIsaWith prog s fl) (vecOf _ ch).reverse
      (vecOf (leanIsaWith prog s fl).tableColumns evs.flatten)).toList) :
    (⟨refCol c.col, c.point.toList, c.value⟩ : Verifier.ColumnClaim) ∈
      (refTableTerms (cpsOf ξ) (fpsOf ξ) ch.reverse
        (rowsOf (verifierLayout prog s) (w.result (verifierLayout prog s)) ch.reverse) evs 0 0
        []).2 := by
  obtain ⟨hlen, hw⟩ := readShape_facts prog s w _ evs hs
  simp only [finalClaims, Vector.toList_ofFn, List.mem_ofFn] at hc
  obtain ⟨k, rfl⟩ := hc
  obtain ⟨⟨j, i⟩, hk⟩ : ∃ p, (columnPos (leanIsaWith prog s fl)).symm k = p := ⟨_, rfl⟩
  obtain ⟨t, rfl⟩ := (stEquiv prog s fl).surjective j
  have hk' : k = columnPos (leanIsaWith prog s fl) ⟨stEquiv prog s fl t, i⟩ := by
    rw [← hk, Equiv.apply_symm_apply]
  have hv : (vecOf (leanIsaWith prog s fl).tableColumns evs.flatten)[k] =
      (evs.getD t []).getD i 0 := by
    subst hk'
    exact tableValues_eq prog s evs hlen hw t i
  have hi : i.val < (evs.getD t []).length := by rw [hw t]; exact i.isLt
  simp only [finalClaim, hv]
  rw [refTableTerms_snd, List.nil_append, List.mem_flatMap]
  refine ⟨(refRow s (w.result (verifierLayout prog s)) ch.reverse t, evs.getD t []), ?_, ?_⟩
  · rw [rowsOf_eq prog s _ (result_forms_shape prog s w).1, list_six evs [] hlen]
    fin_cases t <;> simp
  · refine List.mem_map.mpr ⟨((evs.getD t []).getD i 0, i), ?_, ?_⟩
    · rw [List.mk_mem_zipIdx_iff_getElem?, List.getD_eq_getElem _ _ hi]
      simp
    · simp only [refRow, Complete.opcode_tables]
      have hcol := refCol_opIdx t i
      have hpt : (M3Instance.lowPoint (leanIsaWith prog s fl) (vecOf _ ch).reverse
          (stEquiv prog s fl t)).toList = ch.reverse.take (s.τ t) := by
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
column numbering `refCol`, for every read of the bus phase of the right shape whose slot weights
are sixteen. -/
theorem tableFid_leanIsa (hI : Bus.Conditions (leanIsaWith prog s fl)) (w : BusWit)
    (hw : w.Shaped (leanIsaWith prog s fl) (verifierLayout prog s)) (ha : w.alphas.length = 16) :
    TableFid (leanIsaWith prog s fl) hI input (verifierLayout prog s) refCol w where
  rounds := rounds_leanIsa prog s
  target ξ := target_leanIsa prog s input w hw.1 ha hw.2.2.1 hw.2.2.2 ξ
  formula ξ ch evs hch hs := formula_leanIsa prog s input w hw.1 ha ξ ch evs hch hs
  claims ξ ch claim evs hch hs c hc := by
    simp only [tableOut, tableStmt, Vector.toList_append, List.mem_append] at hc
    rcases hc with hc | hc
    · exact List.mem_append_left _ (busOut_columns_mem prog s input w hw.1 hw.2.2.1 c hc)
    · exact List.mem_append_right _ (finalClaims_mem prog s ξ w ch evs hch hs c hc)

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

/-- **The push side's leaves at leanISA** are the verifier's push layout's total. -/
theorem pushLeaves_eq_pushTotal : (leanIsaWith prog s fl).pushLeaves =
    Complete.blockTotal (Complete.sideSizes (Complete.fwLogs prog s) (Complete.pushBlocks s)) := by
  rw [pushLeaves_eq_leafCount, Bus.leafCount, Complete.blockTotal_eq,
    show (fun src : Bus.Source (leanIsaWith prog s fl) ↦ 2 ^ src.κ) = (2 ^ ·) ∘ Bus.Source.κ
      from rfl, ← List.map_map, sources_zero, sideSources_map_κ prog s .push _ (pushBlocks_eq s)]
  rfl

/-- **The bus phase's depth** at the verifier's layout is the instance's `μ_bus`. -/
theorem busDepth_leanIsa :
    (busLayout [0, (verifierLayout prog s).logMemory, (verifierLayout prog s).logBytecode]
      (verifierLayout prog s).push).depth = (leanIsaWith prog s fl).μBus := by
  rw [Complete.busLayout_depth_verifier, Complete.busDepth, log2Ceil_eq_clog, M3Instance.μBus,
    pushLeaves_eq_pushTotal]

/-- **The leaf stacks have a variable**: `μ_bus ≠ 0` at leanISA. -/
theorem μBus_ne_zero : (leanIsaWith prog s fl).μBus ≠ 0 := by
  rw [M3Instance.μBus, pushLeaves_eq_pushTotal, Complete.blockTotal_eq]
  refine (Nat.clog_pos (by norm_num) ?_).ne'
  simp only [Complete.sideSizes, Complete.fwLogs, List.map_append, List.sum_append, List.map_cons,
    List.sum_cons, pow_zero]
  rw [add_assoc]
  exact Nat.lt_add_of_pos_right (by positivity)

/-! ## The bus phase and the table sumcheck at leanISA -/

section LeanIsaSpec

open LeanVM.Protocol.Compile

/-- **The bytecode's length**: `2 ^ (logBytecode + busBits)` words. -/
theorem bytecode_length_leanIsa :
    (verifierLayout prog s).bytecode.length =
      2 ^ ((verifierLayout prog s).logBytecode + busBits) :=
  length_bytecodeWords prog

/-- **The bytecode's log-size is within the bus's depth.** -/
theorem logBytecode_le_μBus :
    (verifierLayout prog s).logBytecode ≤ (leanIsaWith prog s fl).μBus := by
  rw [← busDepth_leanIsa prog s, Complete.busLayout_depth_verifier]
  exact Complete.logSize_le_busDepth prog s

/-- An oracle of the instance: the zero stack. -/
def zeroOracle : ∀ i, TheOracle (leanIsaWith prog s fl) i :=
  fun _ ↦ ⟨Vector.replicate _ 0⟩

variable {εmax : ℝ≥0∞} (cands : Word → Set (∀ i, TheOracle (leanIsaWith prog s fl) i))

/-- **The bus phase, then the table sumcheck, at leanISA**: `busTableSpec` at the leanISA
instance and the verifier's layout, with every fidelity hypothesis discharged (`TableFid` by
`tableFid_leanIsa`, `μ_bus ≠ 0` by `μBus_ne_zero`, the push layout's depth by `busDepth_leanIsa`,
the bytecode's shape by `bytecode_length_leanIsa` and `logBytecode_le_μBus`). Only the error
hypotheses remain: the fingerprint challenges' after their grind (`hab`), the GKR's, the
bytecode share's (`hs`), `ξ`'s after its grind (`hxi`) and the table rounds'. -/
noncomputable def busTableSpec_leanIsa {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hlt : abError (leanIsaWith prog s fl) L₀ < 1)
    (hab : (2 : ℝ≥0∞)⁻¹ ^ busGrindingBits (leanIsaWith prog s fl).μBus *
      (abError (leanIsaWith prog s fl) L₀ + 0) ≤ εmax)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) (hs : roundError 1 2 + 0 ≤ εmax) {T : ℝ≥0∞}
    (he3 : roundError L₀ 3 + T ≤ εmax) (hTf : T ≤ εmax)
    (hxi : (2 : ℝ≥0∞)⁻¹ ^ xiGrindBits * (xiError (leanIsaWith prog s fl) L₀ + sumcheckLead
      (List.replicate ((verifierLayout prog s).tableLogHeights.foldl max 0) none) T) ≤ εmax) :
    Spec ((verifyBusBalance computedBytecodeValue (verifierLayout prog s)).bind
        (tablePhaseClaims (verifierLayout prog s)))
      (HDoom cands (Seam.commit (leanIsaWith prog s fl)) input)
      (TablePost (leanIsaWith prog s fl) cands input refCol) εmax
      (if busGrindingBits (leanIsaWith prog s fl).μBus = 0 then
        abError (leanIsaWith prog s fl) L₀ + 0 else 0) T :=
  busTableSpec (leanIsaWith prog s fl) (leanIsaWith_conditions prog s fl) cands input
    (verifierLayout prog s) refCol
    (fun w hw h16 ↦ tableFid_leanIsa prog s input (leanIsaWith_conditions prog s fl) w hw h16)
    le_rfl hfin hcard (μBus_ne_zero prog s) (busDepth_leanIsa prog s)
    (bytecode_length_leanIsa prog s) (logBytecode_le_μBus prog s) (zeroOracle prog s) hlt hab
    he4 hT hlam hs he3 hTf hxi

end LeanIsaSpec

end
end LeanVM.Protocol.EndToEnd.Front
