/-
  LeanVM.Guest.B1.Tables.Vt.AsmForms

  The tables' evaluations as the specification's table loop reads them, and every table's three
  bus forms evaluated at its evaluations: the guest's form values.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.AsmRun
public import LeanVM.Guest.B1.Tables.Vt.FormsT0
public import LeanVM.Guest.B1.Tables.Vt.FormsT1
public import LeanVM.Guest.B1.Tables.Vt.FormsT2
public import LeanVM.Guest.B1.Tables.Vt.FormsT3
public import LeanVM.Guest.B1.Tables.Vt.FormsT4
public import LeanVM.Guest.B1.Tables.Vt.FormsT5
public import LeanVM.Guest.B1.Tables.Vt.PullSels

/-!
# The evaluations and the forms' values (V:664-673)

`vtEvT σ t`: table `t`'s `width_t` evaluations, the guest's values at `vtEvB (base_t + c)`;
`vtEvsT σ`: the six lists, whose concatenation is the `153` words read (`vt_evsT_flatten`).
`vt_forms_val`: table `t`'s three bus forms, evaluated at its evaluations, are the guest's form
values `vtFV[t]` (push, pull, count).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (accFold_spec accumulateSide_fst blockSel)

@[expose] public section

/-- The tables' widths. -/
def vtW6 : List ℕ := [13, 13, 7, 14, 14, 92]

/-- The tables' first evaluations. -/
def vtB6 : List ℕ := [0, 13, 26, 33, 47, 61]

/-- Table `t`'s evaluations. -/
def vtEvT (σ : Val) (t : ℕ) : List E :=
  (List.range (vtW6.getD t 0)).map fun c ↦ σ (.n (vtEvB (vtB6.getD t 0 + c)))

/-- The six tables' evaluations. -/
def vtEvsT (σ : Val) : List (List E) :=
  [vtEvT σ 0, vtEvT σ 1, vtEvT σ 2, vtEvT σ 3, vtEvT σ 4, vtEvT σ 5]

theorem vt_evT_getD (σ : Val) (t c : ℕ) (hc : c < vtW6.getD t 0) :
    (vtEvT σ t).getD c 0 = σ (.n (vtEvB (vtB6.getD t 0 + c))) := by
  rw [vtEvT, List.getD_eq_getElem _ _ (by simpa using hc)]
  simp

theorem vt_range_add_map (f : ℕ → E) (a b : ℕ) :
    (List.range (a + b)).map f = (List.range a).map f ++ (List.range b).map fun c ↦ f (a + c) := by
  rw [List.range_add, List.map_append, List.map_map]
  rfl

/-- The six lists are the `153` words. -/
theorem vt_evsT_flatten (σ : Val) : (vtEvsT σ).flatten = vtEvs σ := by
  rw [vtEvs, show (153 : ℕ) = 13 + 13 + 7 + 14 + 14 + 92 from rfl, vt_range_add_map,
    vt_range_add_map, vt_range_add_map, vt_range_add_map, vt_range_add_map]
  simp only [vtEvsT, vtEvT, vtW6, vtB6, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.append_assoc, List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add]

theorem vtEvsT_length (σ : Val) : (vtEvsT σ).length = 6 := rfl

theorem vt_tables_six : tables = [tables.getD 0 default, tables.getD 1 default,
    tables.getD 2 default, tables.getD 3 default, tables.getD 4 default, tables.getD 5 default] :=
  rfl

/-- The evaluations fit the tables' widths. -/
theorem vt_evsT_widths (σ : Val) {α : Type} (X : List α) :
    ∀ p ∈ List.zip (List.zip tables X) (vtEvsT σ), p.2.length = p.1.1.width := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have h6 : (vtEvsT σ).length = 6 := rfl
  have hi6 : i < 6 := by simp only [List.length_zip] at hi; omega
  simp only [List.getElem_zip]
  interval_cases i <;> rfl

/-- A list of length `3`, by its entries. -/
theorem vt_three {α : Type} (l : List α) (h : l.length = 3) (d : α) :
    l = [l.getD 0 d, l.getD 1 d, l.getD 2 d] := by
  match l, h with
  | [a, b, c], _ => rfl

/-- The bus forms' shape: six tables, three sides. -/
theorem vt_forms3_shape (bc : List K) (lm : ℕ) {rows : List ℕ} (hr : rows.length = 6)
    (weights : List E) (β : E) (p memory : List E) (mf bf bv tv0 tv1 tv2 : E) :
    (vtAcc2 (layoutOf bc lm rows) weights β p memory mf bf bv tv0 tv1 tv2).1.length = 6 ∧
      ∀ t < 6, ((vtAcc2 (layoutOf bc lm rows) weights β p memory mf bf bv tv0 tv1 tv2).1.getD t
        []).length = 3 := by
  obtain ⟨hpush, hpull, hcount⟩ := vt_layout_blocks bc lm hr
  have own := vt_blocks_owner_lt rows
  obtain ⟨h6, h3⟩ := vt_forms0_shape
  simp only [vtAcc2, vtAcc1, vtAcc0, hpush, hpull, hcount, accumulateSide_fst]
  obtain ⟨l1, r1, -, -⟩ := accFold_spec 0 (by norm_num) weights β _ _ h6 h3
    (fun x hx ↦ own.1 _ (List.of_mem_zip hx).2)
  obtain ⟨l2, r2, -, -⟩ := accFold_spec 1 (by norm_num) weights β _ _ l1 r1
    (fun x hx ↦ own.2.1 _ (List.of_mem_zip hx).2)
  obtain ⟨l3, r3, -, -⟩ := accFold_spec 2 (by norm_num) [1] 0 _ _ l2 r2
    (fun x hx ↦ own.2.2 _ (List.of_mem_zip hx).2)
  exact ⟨l3, r3⟩

/-- The guest's form values: table `t`'s push, pull and count forms. -/
def vtFV : List (List ℕ) :=
  [[2894, 2915, 2924], [3183, 3204, 3213], [3368, 3381, 3386], [3654, 3675, 3684],
    [3979, 4004, 4013], [5769, 5882, 5937]]

section
variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ)
include hμ

/-- **The forms' values.** -/
theorem vt_forms_val {σ : Val} (h : VtH Lm.read σ) (bc : List K) (hbc : bc.length = 2 ^ 23)
    {point : List E} (hz : TbReadsAt Lm.read (σ (.n 8)) point)
    (hmu : σ (.n 9) = gen ^ point.length) (hml : point.length < 33)
    (hE : ExpTablesAt Lm.read (σ (.n 12))) {lm : ℕ} (hlm : lm ≤ 32)
    {rows : List ℕ} (hr : rows.length = 6) (hτ : ∀ t < 6, vtHt rows t < 29)
    (hkb : ∀ i < 8, σ (.n (25 + i)) = gen ^ ([0, lm] ++ vtTauList (vtHt rows)).getD i 0)
    {weights : List E} (hwl : weights.length = 16)
    (hW : TbReadsAt Lm.read (σ (.n 13)) weights) {t : ℕ} (ht : t < 6) :
    ((vtAcc2 (layoutOf bc lm rows) weights (σ (.n 14)) point
        [σ (.n 812), σ (.n 816)] (σ (.n 1302)) (σ (.n 1316)) (σ (.n 1840))
        (σ (.n 2441)) (σ (.n 2487)) (σ (.n 2542))).1.getD t []).map
        (·.evaluate ((vtEvT σ t).getD · 0)) =
      (vtFV.getD t []).map fun v ↦ σ (.n v) := by
  obtain ⟨-, -, -, -, -, -, -, -, hP, -, hC, -⟩ :=
    vt_sels hμ Lm h hz hmu hml hE hlm hτ hkb
  have hw : ∀ i < 16, LoadHolds Lm.read (σ (.n 13)) i (weights.getD i 0) :=
    fun i hi ↦ by
      have := hW i (by omega)
      rwa [← List.getD_eq_getElem _ 0] at this
  obtain ⟨e0, e1, e2⟩ := vt_forms hbc weights (σ (.n 14)) point
    [σ (.n 812), σ (.n 816)] (σ (.n 1302)) (σ (.n 1316)) (σ (.n 1840))
    (σ (.n 2441)) (σ (.n 2487)) (σ (.n 2542)) (fun c ↦ σ (.n c)) hP hC hr ⟨t, ht⟩ ((vtEvT σ t).getD · 0)
  simp only at e0 e1 e2
  rw [vt_three _ ((vt_forms3_shape bc lm hr _ _ _ _ _ _ _ _ _ _).2 t ht) {}]
  simp only [List.map_cons, List.map_nil, e0, e1, e2]
  have hev : ∀ c < vtW6.getD t 0, σ (.n (vtEvB (vtB6.getD t 0 + c))) = (vtEvT σ t).getD c 0 :=
    fun c hc ↦ (vt_evT_getD σ t c hc).symm
  interval_cases t
  · simp only [vtFV, List.getD_cons_zero, List.map_cons, List.map_nil]
    rw [vtSide00 h hw hev, vtSide10 h hw hev, vtPullSels0 h, vtSide20 h hev]
    rfl
  · simp only [vtFV, List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil]
    rw [vtSide01 h hw hev, vtSide11 h hw hev, vtPullSels1 h, vtSide21 h hev]
    rfl
  · simp only [vtFV, List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil]
    rw [vtSide02 h hw hev, vtSide12 h hw hev, vtPullSels2 h, vtSide22 h hev]
    rfl
  · simp only [vtFV, List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil]
    rw [vtSide03 h hw hev, vtSide13 h hw hev, vtPullSels3 h, vtSide23 h hev]
    rfl
  · simp only [vtFV, List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil]
    rw [vtSide04 h hw hev, vtSide14 h hw hev, vtPullSels4 h, vtSide24 h hev]
    rfl
  · simp only [vtFV, List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil]
    rw [vtSide05 h hw hev, vtSide15 h hw hev, vtPullSels5 h, vtSide25 h hev]
    rfl

end

end
end LeanVM.Guest.B1.Tables
