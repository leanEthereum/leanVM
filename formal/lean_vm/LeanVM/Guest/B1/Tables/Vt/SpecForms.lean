/-
  LeanVM.Guest.B1.Tables.Vt.SpecForms

  The specification's bus forms, evaluated: a side's blocks owned by a table, with their
  selectors, are the guest's `vtSideVal` of the table's baked terms.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.SpecLayout
public import LeanVM.Guest.B1.Tables.Vt.FormsVal
public import LeanVM.Guest.B1.Tables.Vt.FormsTie0
public import LeanVM.Guest.B1.Tables.Vt.FormsTie1
public import LeanVM.Guest.B1.Tables.Vt.FormsTie2
public import LeanVM.Guest.B1.Tables.Vt.FormsTie3
public import LeanVM.Guest.B1.Tables.Vt.FormsTie4
public import LeanVM.Guest.B1.Tables.Vt.FormsTie5

/-!
# The forms (V:623-638, 664-673)

`accumulateSide` adds each block's form, scaled by its selector, to its owner's form of the side
(`accFold_spec`): evaluated at a table's row, the owner's form is the sum over its blocks of the
selector times `blockVal`. `vt_side_push` (and `vt_side_pull`, `vt_side_count`): over the side's
blocks with the guest's selectors, the blocks of table `t` sum to `vtSideVal` of the table's baked
terms, by the kernel-checked tie of the flushes and the baked terms (`vtTie0t`, `vtTie1t`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (refSide refSide_eq refSideC FormC canon termsEval blockVal
  evaluate_eq_sum)

@[expose] public section

/-- The baked terms of side `sd`, table `t`. -/
def vtBT (sd t : ℕ) : List (List (List (List ℕ × ℕ))) :=
  ([[vtBTerms00, vtBTerms01, vtBTerms02, vtBTerms03, vtBTerms04, vtBTerms05],
    [vtBTerms10, vtBTerms11, vtBTerms12, vtBTerms13, vtBTerms14, vtBTerms15],
    [vtBTerms20, vtBTerms21, vtBTerms22, vtBTerms23, vtBTerms24, vtBTerms25]].getD sd []).getD t []

theorem vt_tie_push : ∀ t : Fin 6, vtTieCheck (refSideC t .push) (vtBT 0 t) = true
  | 0 => vtTie00 | 1 => vtTie01 | 2 => vtTie02 | 3 => vtTie03 | 4 => vtTie04 | 5 => vtTie05

theorem vt_tie_pull : ∀ t : Fin 6, vtTieCheck (refSideC t .pull) (vtBT 1 t) = true
  | 0 => vtTie10 | 1 => vtTie11 | 2 => vtTie12 | 3 => vtTie13 | 4 => vtTie14 | 5 => vtTie15

theorem vt_bt_count : ∀ t : Fin 6, vtBT 2 t = (vtCountCols.getD t []).map fun l ↦ [[([l], 1)]] := by
  decide

/-- A tie of lists, one entry at a time. -/
theorem vtTieCheck_cons (s : List FormC) (ss : List (List FormC)) (b : List (List (List ℕ × ℕ)))
    (bs : List (List (List (List ℕ × ℕ)))) (h : vtTieCheck (s :: ss) (b :: bs) = true) :
    (s.length = b.length ∧ ∀ q ∈ List.zip s b, canon q.1.termsK = canon (vtTermsK q.2)) ∧
      vtTieCheck ss bs = true := by
  simp only [vtTieCheck, List.length_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true,
    decide_eq_true_eq, Nat.add_right_cancel_iff, List.all_eq_true] at h ⊢
  exact ⟨⟨h.2.1.1, h.2.1.2⟩, h.1, h.2.2⟩

theorem vtTieCheck_length {spec : List (List FormC)} {baked : List (List (List (List ℕ × ℕ)))}
    (h : vtTieCheck spec baked = true) : spec.length = baked.length := by
  simp only [vtTieCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- A coordinate tied to its baked terms evaluates to their value. -/
theorem vt_coord_evaluate (f : FormC) (c : List (List ℕ × ℕ))
    (h : canon f.termsK = canon (vtTermsK c)) (col : ℕ → E) :
    f.toForm.evaluate col = vtCoordVal col c := by
  rw [toForm_evaluate, ← termsEval_liftT_canon, h, termsEval_liftT_canon]
  rfl

theorem vt_coords_sum (W : List E) (col : ℕ → E) :
    ∀ (s : List FormC) (b : List (List (List ℕ × ℕ))), s.length = b.length →
      (∀ q ∈ List.zip s b, canon q.1.termsK = canon (vtTermsK q.2)) → ∀ n,
      (((s.map FormC.toForm).zipIdx n).map fun cs ↦ W.getD cs.2 0 * cs.1.evaluate col).sum =
        ((b.zipIdx n).map fun cs ↦ W.getD cs.2 0 * vtCoordVal col cs.1).sum
  | [], [], _, _, _ => rfl
  | f :: s, c :: b, hl, hq, n => by
    simp only [List.map_cons, List.zipIdx_cons, List.sum_cons]
    rw [vt_coord_evaluate f c (hq (f, c) (by simp)) col,
      vt_coords_sum W col s b (by simpa using hl) (fun q hq' ↦ hq q (by simp [hq'])) (n + 1)]
  | [], _ :: _, hl, _, _ => absurd hl (by simp)
  | _ :: _, [], hl, _, _ => absurd hl (by simp)

/-- **A side's blocks of one table**, tied to the baked terms, with their selectors. -/
theorem vt_tie_sum (h n o : ℕ) (β : E) (W : List E) (col : ℕ → E) :
    ∀ (sels : List E) (spec : List (List FormC)) (baked : List (List (List (List ℕ × ℕ)))),
      vtTieCheck spec baked = true →
      ((sels.zip (spec.map fun s ↦ (⟨h, n, s.map FormC.toForm, o⟩ : BusBlock))).map
          fun x ↦ x.1 * blockVal β W x.2 col).sum =
        vtSideVal sels β (W.getD · 0) col (baked.take sels.length)
  | [], _, _, _ => by simp [vtSideVal]
  | _ :: _, [], baked, ht => by
    have := vtTieCheck_length ht
    simp only [List.length_nil] at this
    obtain rfl : baked = [] := List.length_eq_zero_iff.mp this.symm
    simp [vtSideVal]
  | x :: sels, s :: spec, [], ht => absurd (vtTieCheck_length ht) (by simp)
  | x :: sels, s :: spec, b :: baked, ht => by
    obtain ⟨⟨hl, hq⟩, ht'⟩ := vtTieCheck_cons s spec b baked ht
    have ih := vt_tie_sum h n o β W col sels spec baked ht'
    simp only [vtSideVal, List.map_cons, List.zip_cons_cons, List.sum_cons, List.length_cons,
      List.take_succ_cons, List.zipWith_cons_cons] at ih ⊢
    rw [ih, blockVal, vtBlockVal]
    exact congrArg (fun v ↦ x * (β + v) + _) (vt_coords_sum W col s b hl hq 0)

/-- The count side's blocks of one table, with their selectors. -/
theorem vt_count_sum (h n o : ℕ) (col : ℕ → E) :
    ∀ (sels : List E) (cols : List ℕ), sels.length = cols.length →
      ((sels.zip (cols.map fun l ↦ (⟨h, n, [Form.col l], o⟩ : BusBlock))).map
          fun x ↦ x.1 * blockVal 0 [1] x.2 col).sum =
        vtSideVal sels 0 (fun _ ↦ 1) col (cols.map fun l ↦ [[([l], 1)]])
  | [], [], _ => by simp [vtSideVal]
  | x :: sels, l :: cols, hl => by
    have ih := vt_count_sum h n o col sels cols (by simpa using hl)
    simp only [vtSideVal, List.map_cons, List.zip_cons_cons, List.sum_cons,
      List.zipWith_cons_cons] at ih ⊢
    rw [ih]
    simp [blockVal, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, evaluate_eq_sum,
      Form.col, Verifier.gpow, vt_ofK_ofBits_one]
  | [], _ :: _, hl => absurd hl (by simp)
  | _ :: _, [], hl => absurd hl (by simp)

/-- Filtering a zip by its second component's owner. -/
theorem vt_zip_filter {α : Type} (g : α → E) (key : α → ℕ) (t : ℕ) :
    ∀ (data : List α) (blocks : List BusBlock), blocks.map (·.owner) = data.map key →
      ((data.map g).zip blocks).filter (fun x ↦ x.2.owner = t) =
        ((data.filter fun d ↦ key d = t).map g).zip (blocks.filter fun b ↦ b.owner = t)
  | [], [], _ => rfl
  | d :: data, b :: blocks, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.map_cons, List.zip_cons_cons, List.filter_cons, h.1]
    split_ifs <;> simp [vt_zip_filter g key t data blocks h.2]
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)

theorem vt_push_owners (rows : List ℕ) :
    (vtPushBlocks rows).map (·.owner) = vtPushPadData.map (·.2.1) := by
  simp only [vtPushBlocks, List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil,
    List.map_append, List.map_map]
  rfl

theorem vt_pull_owners (rows : List ℕ) :
    (vtPullBlocks rows).map (·.owner) = vtPushPadData.map (·.2.1) := by
  simp only [vtPullBlocks, List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil,
    List.map_append, List.map_map]
  rfl

theorem vt_count_owners (rows : List ℕ) :
    (vtCountBlocks rows).map (·.owner) = vtCountPadData.map (·.2.1) := by
  simp only [vtCountBlocks, vt_countColumns, List.ofFn_succ, List.ofFn_zero, List.flatten_cons,
    List.flatten_nil, List.map_append, List.map_map]
  rfl

theorem vt_push_filter (rows : List ℕ) (t : Fin 6) :
    (vtPushBlocks rows).filter (fun b ↦ b.owner = (t : ℕ)) =
      (refSide t .push).map fun c ↦ (⟨vtHt rows t, vtRw rows t, c, t⟩ : BusBlock) := by
  fin_cases t <;>
    simp [vtPushBlocks, List.ofFn_succ, List.filter_append, List.filter_map, Function.comp_def]

theorem vt_pull_filter (rows : List ℕ) (t : Fin 6) :
    (vtPullBlocks rows).filter (fun b ↦ b.owner = (t : ℕ)) =
      (refSide t .pull).map fun c ↦ (⟨vtHt rows t, vtRw rows t, c, t⟩ : BusBlock) := by
  fin_cases t <;>
    simp [vtPullBlocks, List.ofFn_succ, List.filter_append, List.filter_map, Function.comp_def]

theorem vt_count_filter (rows : List ℕ) (t : Fin 6) :
    (vtCountBlocks rows).filter (fun b ↦ b.owner = (t : ℕ)) =
      (vtCountCols.getD t []).map fun l ↦ (⟨vtHt rows t, vtRw rows t, [Form.col l], t⟩ : BusBlock) := by
  rw [← vt_countColumns]
  fin_cases t <;>
    simp [vtCountBlocks, List.ofFn_succ, List.filter_append, List.filter_map, Function.comp_def]

end
end LeanVM.Guest.B1.Tables
