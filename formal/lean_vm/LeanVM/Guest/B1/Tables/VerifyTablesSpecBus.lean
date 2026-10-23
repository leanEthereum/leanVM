/-
  LeanVM.Guest.B1.Tables.VerifyTablesSpecBus

  The value of `verify_tables`' bus totals (VerifyTablesBus): what each side's tables owe is
  `accumulateSide`'s total (V:589-604).
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesBus
public import LeanVM.Guest.B1.Tables.VerifyTablesSpecCe
public import LeanVM.Guest.B1.Tables.VerifyTablesSpec

/-!
# The bus totals' values

`pushTotalEx_eval`, `pullTotalEx_eval`, `countTotalEx_eval`: at the guest's values, the push,
pull and count totals are `accumulateSide`'s second component: the tree value, the framework
blocks' fingerprints weighted by their selectors, the selectors' sum plus one, and each table
block's selector times its padding weight times its form at the padding row plus one
(`padMass_eval`, the padding row `padK`, `coordPad_eval`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Complete

@[expose] public section

theorem layoutPushOwners_eq : layoutPushOwners = pushOwners := rfl

theorem layoutCountOwners_eq : layoutCountOwners = countOwners := rfl

/-! ## The padding rows -/

/-- `padK`'s body for any table. -/
def padKT (tb : Table) (c : ℕ) : K :=
  let slots := if tb.opcode = opBlake2s then blake2sSlots else []
  match tb.columns[c]? with
  | some name => if some name ∈ slots then K.ofBits (paddingInstance.getD (slots.idxOf (some name)) 0)
      else 0
  | none => 0

theorem padding_getD' (tb : Table) (c : ℕ) : tb.padding.getD c 0 = ofK (padKT tb c) := by
  rw [Table.padding, List.getD_eq_getElem?_getD, List.getElem?_map]
  unfold padKT
  cases tb.columns[c]? with
  | none => exact ofK_zero.symm
  | some name =>
    simp only [Option.map_some, Option.getD_some]
    split_ifs <;> first | rfl | exact ofK_zero.symm

/-- A table's padding row (V:752-756) in `K`. -/
theorem padding_getD (t c : ℕ) : (tables.getD t default).padding.getD c 0 = ofK (padK t c) :=
  padding_getD' _ c

/-- A coordinate at a table's padding row. -/
theorem coordPad_eval (t : ℕ) (f : FormC) :
    f.toForm.evaluate ((tables.getD t default).padding.getD · 0) = ofK (coordPadK t f) := by
  simp only [padding_getD, evaluate_eq_termsEval, FormC.toForm, coordPadK, FormC.termsK]
  rw [← termsEval_map_ofK, List.map_map]
  congr 1
  exact List.map_congr_left fun u _ => by simp [Coef.ev_eq]

/-! ## Sums -/

theorem sumE_map_range (n : ℕ) (f : ℕ → E) :
    sumE ((List.range n).map f) = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, vt_sumE_append, ih, Finset.sum_range_succ,
      List.map_singleton, vt_sumE_cons, vt_sumE_nil, add_zero]

theorem sumE_map_getD {α : Type} [Inhabited α] (l : List α) (f : α → E) :
    sumE (l.map f) = ∑ j ∈ Finset.range l.length, f (l.getD j default) := by
  rw [← sumE_map_range]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < l.length by simpa using h2), Option.getD_some]

theorem pushCoordsC_short : ∀ c ∈ pushCoordsC, c.length ≤ 16 := by
  intro c hc
  obtain ⟨t, -, ht⟩ := List.mem_flatMap.mp hc
  exact pySideC_short t .push c ht

theorem pullCoordsC_short : ∀ c ∈ pullCoordsC, c.length ≤ 16 := by
  intro c hc
  obtain ⟨t, -, ht⟩ := List.mem_flatMap.mp hc
  exact pySideC_short t .pull c ht

theorem pushCoordsC_length : pushCoordsC.length = 34 := by decide +kernel

theorem pullCoordsC_length : pullCoordsC.length = 34 := by decide +kernel

variable (ρ χ : ℕ → E)

/-- A table block's padding form plus one. -/
theorem padBlockEx_eval (t : ℕ) (coords : List FormC) (hc : coords.length ≤ 16) :
    (padBlockEx t coords).eval ρ χ = (blockForm ⟨0, 0, coords.map FormC.toForm, t⟩
      ((List.range 16).map χ) (ρ 12)).evaluate ((tables.getD t default).padding.getD · 0) + 1 := by
  rw [evaluate_blockForm, padBlockEx]
  simp only [Ex.eval, ofK_one, sumEx_eval, List.map_map]
  refine congrArg (· + 1) (congrArg (ρ 12 + ·) (congrArg sumE ?_))
  rw [List.zipIdx_map]
  simp only [List.map_map]
  refine List.map_congr_left fun p hp => ?_
  have hp2 : p.2 < 16 := by
    have := List.mem_zipIdx hp
    omega
  simp only [Function.comp_apply, Ex.eval]
  rw [show (Prod.map FormC.toForm id p).2 = p.2 from rfl,
    show (Prod.map FormC.toForm id p).1 = p.1.toForm from rfl, getD_map_range' _ _ hp2,
    coordPad_eval]

theorem ofK_two : ofK (K.ofBits 2) = gen := by rw [← word_ofK]; exact word_gen

theorem ofK_four : ofK (K.ofBits 4) = gen ^ 2 := by
  rw [← word_ofK]; exact word_two_pow (a := 2) (by decide)

/-- A block's form depends on its coordinates and the weights of its slots only. -/
private theorem blockForm_congr {b b' : BusBlock} {w w' : List E} {beta : E} (column : ℕ → E)
    (hc : b.coordinates = b'.coordinates) (hw : ∀ i < b.coordinates.length, w.getD i 0 = w'.getD i 0) :
    (blockForm b w beta).evaluate column = (blockForm b' w' beta).evaluate column := by
  rw [evaluate_blockForm, evaluate_blockForm, ← hc]
  refine congrArg (beta + ·) (congrArg sumE (List.map_congr_left fun p hp => ?_))
  have := List.mem_zipIdx hp
  rw [hw p.2 (by omega)]

/-- **A side's padding mass** (V:597-602): block `j`'s selector times its table's padding weight
times its form at the padding row plus one. -/
theorem padMass_eval (side : ℕ) (coordsC : List (List FormC)) (hshort : ∀ c ∈ coordsC, c.length ≤ 16)
    (owners : List ℕ) (nb base : ℕ) {forms : List (List Form)} {blocks : List BusBlock}
    {sels w : List E} {beta : E} {point : List E}
    (hsl : sels.length = nb) (hbl : blocks.length = nb) (hcl : coordsC.length = nb)
    (hsel : ∀ j < nb, ρ (selVal.getD (base + j) 0 + 23) = sels.getD j 0)
    (hown : ∀ j < nb, (blocks.getD j default).owner = owners.getD j 0)
    (hcoord : ∀ j < nb, (blocks.getD j default).coordinates = (coordsC.getD j []).map FormC.toForm)
    (hpw : ∀ j < nb, ρ (1739 + 14 * owners.getD j 0) =
      paddingWeight (point.take (blocks.getD j default).logRows) (blocks.getD j default).rows)
    (hw : ∀ i < 16, w.getD i 0 = χ i) (hbeta : ρ 12 = beta) :
    (sumEx ((List.range nb).map fun j => .mul (.mul (busSel (base + j))
      (.var (1739 + 14 * owners.getD j 0))) (padBlockEx (owners.getD j 0) (coordsC.getD j [])))).eval
        ρ χ = ((List.zip sels blocks).foldl (accStep side w beta point) (forms, 0)).2 := by
  rw [accStep_fold_padding, zero_add, sumEx_eval, List.map_map, sumE_map_range, sumE_map_getD,
    List.length_zip, hsl, hbl, min_self]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  have hz : (List.zip sels blocks).getD j default = (sels.getD j 0, blocks.getD j default) := by
    rw [List.getD_eq_getElem _ _ (by simp [hsl, hbl]; omega), List.getElem_zip,
      List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  have hcs : (coordsC.getD j []).length ≤ 16 :=
    hshort _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  rw [hz]
  simp only [Function.comp_apply, Ex.eval, busSel]
  rw [padBlockEx_eval ρ χ _ _ hcs, hsel j hj', hpw j hj', ← hown j hj', hbeta]
  refine congrArg (fun x => _ * _ * (x + 1))
    (blockForm_congr _ (by rw [hcoord j hj']) fun i hi => ?_)
  have hi' : i < 16 := by
    have : i < (List.map FormC.toForm (coordsC.getD j [])).length := hi
    rw [List.length_map] at this; omega
  rw [getD_map_range' _ _ hi', hw i hi']

/-- **What the push side's tables owe** (`bus_table_total[PUSH]`, V:589-604). -/
theorem pushTotalEx_eval {ρ χ : ℕ → E} {forms : List (List Form)} (hsh : FormsShaped forms)
    {blocks : List BusBlock} {sl : BusLayout} {fps w : List E} {beta tv : E} {point : List E}
    (hfwl : sl.framework.length = 3) (htl : sl.tables.length = 34) (hbl : blocks.length = 34)
    (hsel : ∀ i < 37, ρ (selVal.getD i 0 + 23) =
      ((sl.framework ++ sl.tables).getD i default).eqAbove point)
    (hown : ∀ j < 34, (blocks.getD j default).owner = pushOwners.getD j 0)
    (hcoord : ∀ j < 34, (blocks.getD j default).coordinates =
      (pushCoordsC.getD j []).map FormC.toForm)
    (hpw : ∀ j < 34, ρ (1739 + 14 * pushOwners.getD j 0) =
      paddingWeight (point.take (blocks.getD j default).logRows) (blocks.getD j default).rows)
    (hwl : w.length = 16) (hw : ∀ i < 16, w.getD i 0 = χ i) (hbeta : ρ 12 = beta) (htv : ρ 21 = tv)
    (hfps : fps = [χ 0 * 1 + χ 1 * 1 + χ 2 * 1,
      χ 0 * gen + χ 1 * ρ 1931 + χ 2 * 1 + χ 3 * ρ 1937 + χ 4 * ρ 1955 + χ 5 * ρ 1973,
      χ 0 * gen ^ 2 + χ 1 * ρ 2035 + χ 2 * 1 + ρ 1732]) :
    pushTotalEx.eval ρ χ = (accumulateSide forms 0 blocks sl fps w beta point tv).2 := by
  have _u1 := hsh
  have _u2 := hwl
  obtain ⟨F0, F1, F2, hfw⟩ : ∃ a b c, sl.framework = [a, b, c] := by
    match h : sl.framework, hfwl with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  have h0 := hsel 0 (by omega)
  have h1 := hsel 1 (by omega)
  have h2 := hsel 2 (by omega)
  rw [hfw] at h0 h1 h2
  simp only [List.cons_append, List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2
  have hpad := padMass_eval ρ χ 0 pushCoordsC pushCoordsC_short pushOwners 34 3 (forms := forms)
    (sels := sl.tables.map (·.eqAbove point)) (by simp [htl]) hbl pushCoordsC_length
    (fun j hj => by
      rw [hsel (3 + j) (by omega), List.getD_eq_getElem _ _ (by simp [hfwl, htl]; omega),
        List.getElem_append_right (by omega), List.getD_eq_getElem _ _ (by simp [htl]; omega),
        List.getElem_map]
      simp only [hfwl, Nat.add_sub_cancel_left]) hown hcoord hpw hw hbeta
  have hsum : (sumEx ((List.range 37).map busSel)).eval ρ χ =
      sumE ((sl.framework.map (·.eqAbove point)) ++ (sl.tables.map (·.eqAbove point))) := by
    rw [sumEx_eval, List.map_map, sumE_map_range, ← List.map_append, sumE_map_getD,
      List.length_append, hfwl, htl]
    exact Finset.sum_congr rfl fun i hi => hsel i (Finset.mem_range.mp hi)
  rw [accumulateSide_eq]
  simp only
  rw [← hpad, ← hsum, hfw, hfps]
  simp only [List.map_cons, List.map_nil, dot_three]
  rw [pushTotalEx, sumEx_eval]
  simp only [List.map_cons, List.map_nil, vt_sumE_cons, vt_sumE_nil, Ex.eval, add_zero, pushFwEx,
    sumEx_eval, busSel, ofK_two, ofK_four, ofK_one, pushPadEx]
  rw [h0, h1, h2, htv, hbeta]
  ring

/-- **What the pull side's tables owe** (`bus_table_total[PULL]`, V:589-604). -/
theorem pullTotalEx_eval {ρ χ : ℕ → E} {forms : List (List Form)} (hsh : FormsShaped forms)
    {blocks : List BusBlock} {sl : BusLayout} {fps w : List E} {beta tv : E} {point : List E}
    (hfwl : sl.framework.length = 3) (htl : sl.tables.length = 34) (hbl : blocks.length = 34)
    (hsel : ∀ i < 37, ρ (selVal.getD i 0 + 23) =
      ((sl.framework ++ sl.tables).getD i default).eqAbove point)
    (hown : ∀ j < 34, (blocks.getD j default).owner = pushOwners.getD j 0)
    (hcoord : ∀ j < 34, (blocks.getD j default).coordinates =
      (pullCoordsC.getD j []).map FormC.toForm)
    (hpw : ∀ j < 34, ρ (1739 + 14 * pushOwners.getD j 0) =
      paddingWeight (point.take (blocks.getD j default).logRows) (blocks.getD j default).rows)
    (hwl : w.length = 16) (hw : ∀ i < 16, w.getD i 0 = χ i) (hbeta : ρ 12 = beta) (htv : ρ 22 = tv)
    (hfps : fps = [χ 0 * 1 + χ 1 * ofK (gpowK (2 ^ 18 - 1)) + χ 2 * 1,
      χ 0 * gen + χ 1 * ρ 1931 + χ 2 * ρ 3359 + χ 3 * ρ 1937 + χ 4 * ρ 1955 + χ 5 * ρ 1973,
      χ 0 * gen ^ 2 + χ 1 * ρ 2035 + χ 2 * ρ 3409 + ρ 1732]) :
    pullTotalEx.eval ρ χ = (accumulateSide forms 1 blocks sl fps w beta point tv).2 := by
  have _u1 := hsh
  have _u2 := hwl
  obtain ⟨F0, F1, F2, hfw⟩ : ∃ a b c, sl.framework = [a, b, c] := by
    match h : sl.framework, hfwl with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  have h0 := hsel 0 (by omega)
  have h1 := hsel 1 (by omega)
  have h2 := hsel 2 (by omega)
  rw [hfw] at h0 h1 h2
  simp only [List.cons_append, List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2
  have hpad := padMass_eval ρ χ 1 pullCoordsC pullCoordsC_short pushOwners 34 3 (forms := forms)
    (sels := sl.tables.map (·.eqAbove point)) (by simp [htl]) hbl pullCoordsC_length
    (fun j hj => by
      rw [hsel (3 + j) (by omega), List.getD_eq_getElem _ _ (by simp [hfwl, htl]; omega),
        List.getElem_append_right (by omega), List.getD_eq_getElem _ _ (by simp [htl]; omega),
        List.getElem_map]
      simp only [hfwl, Nat.add_sub_cancel_left]) hown hcoord hpw hw hbeta
  have hsum : (sumEx ((List.range 37).map busSel)).eval ρ χ =
      sumE ((sl.framework.map (·.eqAbove point)) ++ (sl.tables.map (·.eqAbove point))) := by
    rw [sumEx_eval, List.map_map, sumE_map_range, ← List.map_append, sumE_map_getD,
      List.length_append, hfwl, htl]
    exact Finset.sum_congr rfl fun i hi => hsel i (Finset.mem_range.mp hi)
  rw [accumulateSide_eq]
  simp only
  rw [← hpad, ← hsum, hfw, hfps]
  simp only [List.map_cons, List.map_nil, dot_three]
  rw [pullTotalEx, sumEx_eval]
  simp only [List.map_cons, List.map_nil, vt_sumE_cons, vt_sumE_nil, Ex.eval, add_zero, pullFwEx,
    sumEx_eval, busSel, ofK_two, ofK_four, ofK_one, pullPadEx]
  rw [h0, h1, h2, htv, hbeta]
  ring

theorem col_evaluate (l : ℕ) (column : ℕ → E) : (Form.col l).evaluate column = column l := by
  simp only [Form.evaluate, Form.col, List.map_cons, List.map_nil, vt_sumE_cons, vt_sumE_nil,
    List.foldl_cons, List.foldl_nil, Verifier.gpow, pow_zero, one_mul, add_zero]

/-- **What the count side's tables owe** (`bus_table_total[COUNT]`, V:589-604). -/
theorem countTotalEx_eval {ρ χ : ℕ → E} {forms : List (List Form)} (hsh : FormsShaped forms)
    {blocks : List BusBlock} {sl : BusLayout} {point : List E} {tv : E}
    (hfw : sl.framework = []) (htl : sl.tables.length = 28) (hbl : blocks.length = 28)
    (hsel : ∀ j < 28, ρ (selVal.getD (37 + j) 0 + 23) = (sl.tables.getD j default).eqAbove point)
    (hown : ∀ j < 28, (blocks.getD j default).owner = countOwners.getD j 0)
    (hcoord : ∀ j < 28, (blocks.getD j default).coordinates = [Form.col (vtCountCols.flatten.getD j 0)])
    (hpw : ∀ j < 28, ρ (1739 + 14 * countOwners.getD j 0) =
      paddingWeight (point.take (blocks.getD j default).logRows) (blocks.getD j default).rows)
    (htv : ρ 23 = tv) :
    countTotalEx.eval ρ χ = (accumulateSide forms 2 blocks sl [] [1] 0 point tv).2 := by
  have _u1 := hsh
  have hpad : countPadEx.eval ρ χ =
      ((List.zip (sl.tables.map (·.eqAbove point)) blocks).foldl (accStep 2 [1] 0 point) (forms, 0)).2 := by
    rw [accStep_fold_padding, zero_add, countPadEx, sumEx_eval, List.map_map, sumE_map_range,
      sumE_map_getD, List.length_zip, List.length_map, htl, hbl, min_self]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    have hz : (List.zip (sl.tables.map (·.eqAbove point)) blocks).getD j default =
        ((sl.tables.getD j default).eqAbove point, blocks.getD j default) := by
      rw [List.getD_eq_getElem _ _ (by simp [htl, hbl]; omega), List.getElem_zip,
        List.getElem_map, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    rw [hz]
    simp only [Function.comp_apply, Ex.eval, busSel]
    rw [hsel j hj', hpw j hj', evaluate_blockForm, hcoord j hj', ← hown j hj', ofK_one]
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, vt_sumE_cons,
      vt_sumE_nil, add_zero, zero_add, List.getD_cons_zero, one_mul, col_evaluate, padding_getD]
  have hsum : (sumEx ((List.range 28).map fun j => busSel (37 + j))).eval ρ χ =
      sumE (sl.tables.map (·.eqAbove point)) := by
    rw [sumEx_eval, List.map_map, sumE_map_range, sumE_map_getD, htl]
    exact Finset.sum_congr rfl fun j hj => hsel j (Finset.mem_range.mp hj)
  rw [accumulateSide_eq]
  simp only
  rw [← hpad, hfw, List.map_nil, List.nil_append, ← hsum, countTotalEx, sumEx_eval]
  simp only [List.map_cons, List.map_nil, vt_sumE_cons, vt_sumE_nil, Ex.eval, add_zero, ofK_one]
  rw [htv, show dot [] [] = 0 from rfl]
  ring

end
end LeanVM.Guest.B1.VerifySub
