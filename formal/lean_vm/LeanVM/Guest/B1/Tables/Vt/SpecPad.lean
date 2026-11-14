/-
  LeanVM.Guest.B1.Tables.Vt.SpecPad

  The specification's padding rows' sum (`padding_rows`) on each side is the guest's
  `vtPadSum` of its baked `COORD_PADDING` values.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.SpecForms

/-!
# The padding sums

`accumulateSide`'s `padding_rows` adds, per table block, its selector times the padding weight of
its owner's rows times its form at the owner's padding row, plus one (`padSum`). By the
kernel-checked tie of the flushes at the padding rows (`vtPadTie0t`, `vtPadTie1t`), a block's form
there is `β + Σ_slot w_slot·pad_slot`, the baked padding values; split by table, the sum is the
guest's `vtPadSum` (`vt_padSum_push`, `vt_padSum_pull`, `vt_padSum_count`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (refSide refSide_eq refSideC FormC termsEval blockVal padSum
  evaluate_eq_sum termsEval_cons termsEval_nil)
open Finset

@[expose] public section

/-- A side's sum split by the owner of its blocks. -/
theorem vt_split_owner {α : Type} (g : α → E) (key : α → ℕ) :
    ∀ l : List α, (∀ x ∈ l, key x < 6) →
      (l.map g).sum = ∑ t ∈ range 6, ((l.filter fun x ↦ key x = t).map g).sum
  | [], _ => by simp
  | x :: l, hl => by
    rw [List.map_cons, List.sum_cons, vt_split_owner g key l fun y hy ↦ hl y (by simp [hy])]
    have hx := hl x (by simp)
    simp only [List.filter_cons]
    have : ∀ t, ((if decide (key x = t) = true then x :: l.filter (fun y ↦ key y = t)
        else l.filter (fun y ↦ key y = t)).map g).sum =
        (if key x = t then g x else 0) + ((l.filter fun y ↦ key y = t).map g).sum := by
      intro t; split_ifs <;> simp_all
    simp only [this, sum_add_distrib, sum_ite_eq, mem_range, hx, ↓reduceIte]

/-- The terms' value through `ofK`. -/
theorem vt_termsEval_ofK (r : ℕ → K) :
    ∀ l : List (List ℕ × K), termsEval (fun c ↦ ofK (r c)) (liftT l) = ofK (termsEval r l)
  | [] => by simp [liftT]
  | u :: l => by
    have hp : ∀ m : List ℕ, (m.map fun c ↦ ofK (r c)).prod = ofK (m.map r).prod := by
      intro m
      induction m with
      | nil => simp
      | cons a m ih => simp [ih, ofK_mul]
    simp only [liftT, List.map_cons, termsEval_cons] at *
    rw [show termsEval (fun c ↦ ofK (r c)) (l.map fun u ↦ (u.1, ofK u.2)) =
      termsEval (fun c ↦ ofK (r c)) (liftT l) from rfl, vt_termsEval_ofK r l, hp, ofK_add, ofK_mul]

theorem vt_getD_map_ofK (row : List K) (c : ℕ) : (row.map ofK).getD c 0 = ofK (row.getD c 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases row[c]? <;> simp

/-- A coordinate's value on a padding row. -/
theorem vt_pad_coord (f : FormC) (row : List K) :
    f.toForm.evaluate ((row.map ofK).getD · 0) = ofK (termsEval (row.getD · 0) f.termsK) := by
  rw [toForm_evaluate]
  simp only [vt_getD_map_ofK]
  exact vt_termsEval_ofK _ _

/-- The nonzero baked padding values of a block: `(slot, value)`. -/
def vtNz (pads : List ℕ) : List (ℕ × ℕ) :=
  ((pads.zipIdx).filter fun x ↦ x.1 ≠ 0).map fun x ↦ (x.2, x.1)

theorem vt_pad_coords (W : List E) (row : List K) :
    ∀ (s : List FormC) (pads : List ℕ), s.length = pads.length →
      (∀ q ∈ List.zip s pads, K.ofBits q.2 = termsEval (row.getD · 0) q.1.termsK) → ∀ n,
      (((s.map FormC.toForm).zipIdx n).map fun cs ↦
          W.getD cs.2 0 * cs.1.evaluate ((row.map ofK).getD · 0)).sum =
        ((((pads.zipIdx n).filter fun x ↦ x.1 ≠ 0).map fun x ↦ (x.2, x.1)).map
          fun ic ↦ W.getD ic.1 0 * word ic.2 0).sum
  | [], [], _, _, _ => rfl
  | f :: s, v :: pads, hl, hq, n => by
    have hv := hq (f, v) (by simp)
    have ih := vt_pad_coords W row s pads (by simpa using hl)
      (fun q hq' ↦ hq q (by simp [hq'])) (n + 1)
    simp only [List.map_cons, List.zipIdx_cons, List.sum_cons, List.filter_cons]
    rw [vt_pad_coord, ← hv, ih]
    by_cases h0 : v = 0
    · subst h0; simp [vt_ofK_ofBits_zero]
    · simp [h0, vt_word_ofK]
  | [], _ :: _, hl, _, _ => absurd hl (by simp)
  | _ :: _, [], hl, _, _ => absurd hl (by simp)

theorem vtPadTieCheck_cons (s : List FormC) (ss : List (List FormC)) (p : List ℕ)
    (ps : List (List ℕ)) (row : List K) (h : vtPadTieCheck (s :: ss) (p :: ps) row = true) :
    (s.length = p.length ∧ ∀ q ∈ List.zip s p, K.ofBits q.2 = termsEval (row.getD · 0) q.1.termsK) ∧
      vtPadTieCheck ss ps row = true := by
  simp only [vtPadTieCheck, List.length_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true,
    decide_eq_true_eq, Nat.add_right_cancel_iff, List.all_eq_true] at h ⊢
  exact ⟨⟨h.2.1.1, h.2.1.2⟩, h.1, h.2.2⟩

theorem vtPadTieCheck_length {spec : List (List FormC)} {pads : List (List ℕ)} {row : List K}
    (h : vtPadTieCheck spec pads row = true) : spec.length = pads.length := by
  simp only [vtPadTieCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- **A table's blocks' padding terms.** -/
theorem vt_pad_table (h n o : ℕ) (β pw : E) (W : List E) (row : List K) (S : ℕ → E) :
    ∀ (dataT : List (ℕ × ℕ × ℕ × List (ℕ × ℕ))) (spec : List (List FormC)) (pads : List (List ℕ)),
      vtPadTieCheck spec pads row = true → dataT.map (·.2.2.2) = pads.map vtNz →
      (((dataT.map fun x ↦ S x.2.2.1).zip (spec.map fun s ↦
          (⟨h, n, s.map FormC.toForm, o⟩ : BusBlock))).map fun x ↦
          x.1 * pw * (blockVal β W x.2 ((row.map ofK).getD · 0) + 1)).sum =
        pw * (dataT.map fun x ↦ S x.2.2.1 * ((β + 1) +
          (x.2.2.2.map fun ic ↦ W.getD ic.1 0 * word ic.2 0).sum)).sum
  | [], _, _, _, _ => by simp
  | _ :: _, [], pads, ht, hd => by
    have := vtPadTieCheck_length ht
    obtain rfl : pads = [] := List.length_eq_zero_iff.mp (by simpa using this.symm)
    simp at hd
  | x :: dataT, s :: spec, [], ht, _ => absurd (vtPadTieCheck_length ht) (by simp)
  | x :: dataT, s :: spec, p :: pads, ht, hd => by
    obtain ⟨⟨hl, hq⟩, ht'⟩ := vtPadTieCheck_cons s spec p pads row ht
    simp only [List.map_cons, List.cons.injEq] at hd
    have ih := vt_pad_table h n o β pw W row S dataT spec pads ht' hd.2
    simp only [List.map_cons, List.zip_cons_cons, List.sum_cons] at ih ⊢
    rw [ih, blockVal, hd.1, vtNz]
    have e := vt_pad_coords W row s p hl hq 0
    simp only at e ⊢
    rw [e]
    ring

/-- The baked padding values of side `sd`'s table `t`. -/
def vtPadsT (t : ℕ) : List (List ℕ) :=
  [vtPads00, vtPads01, vtPads02, vtPads03, vtPads04, vtPads05].getD t []

theorem vt_padTie_push : ∀ t : Fin 6,
    vtPadTieCheck (refSideC t .push) (vtPadsT t) (paddingRowK (tables.getD t default)) = true
  | 0 => vtPadTie00 | 1 => vtPadTie01 | 2 => vtPadTie02 | 3 => vtPadTie03 | 4 => vtPadTie04
  | 5 => vtPadTie05

theorem vt_padTie_pull : ∀ t : Fin 6,
    vtPadTieCheck (refSideC t .pull) (vtPadsT t) (paddingRowK (tables.getD t default)) = true
  | 0 => vtPadTie10 | 1 => vtPadTie11 | 2 => vtPadTie12 | 3 => vtPadTie13 | 4 => vtPadTie14
  | 5 => vtPadTie15

theorem vt_pushPad_data : ∀ t : Fin 6,
    (vtPushPadData.filter fun x ↦ x.2.1 = (t : ℕ)).map (·.2.2.2) = (vtPadsT t).map vtNz := by
  decide

theorem vt_padding (t : ℕ) :
    (tables.getD t default).padding = (paddingRowK (tables.getD t default)).map ofK := by
  rw [padding_eq, paddingRow_eq]

theorem vt_blocks_owner_lt (rows : List ℕ) :
    (∀ b ∈ vtPushBlocks rows, b.owner < 6) ∧ (∀ b ∈ vtPullBlocks rows, b.owner < 6) ∧
      ∀ b ∈ vtCountBlocks rows, b.owner < 6 := by
  refine ⟨fun b hb ↦ ?_, fun b hb ↦ ?_, fun b hb ↦ ?_⟩ <;>
  · obtain ⟨l, hl, hbl⟩ := List.mem_flatten.mp hb
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hl
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hbl
    exact t.isLt

/-- A guest padding sum, as a sum over the tables. -/
theorem vt_padSum_range (eqc pw W : ℕ → E) (β1 : E) (data : List (ℕ × ℕ × ℕ × List (ℕ × ℕ))) :
    vtPadSum eqc pw W β1 data = ∑ t ∈ range 6, pw t * vtPadTable eqc W β1 data t := by
  simp [vtPadSum, sum_range_succ]

/-- **The push side's padding sum.** -/
theorem vt_padSum_push (rows : List ℕ) (p : List E) (β : E) (W : List E) (S pw : ℕ → E)
    (hpw : ∀ t < 6, paddingWeight (p.take (vtHt rows t)) (vtRw rows t) = pw t) :
    padSum W β p ((vtPushPadData.map fun x ↦ S x.2.2.1).zip (vtPushBlocks rows)) =
      vtPadSum S pw (W.getD · 0) (β + 1) vtPushPadData := by
  have hown := vt_push_owners rows
  rw [padSum, vt_split_owner _ (fun x ↦ x.2.owner) _ (fun x hx ↦
    (vt_blocks_owner_lt rows).1 _ (List.of_mem_zip hx).2), vt_padSum_range]
  refine sum_congr rfl fun t ht ↦ ?_
  have ht6 := mem_range.mp ht
  rw [vt_zip_filter _ _ _ _ _ hown]
  obtain ⟨t, rfl⟩ : ∃ t' : Fin 6, (t' : ℕ) = t := ⟨⟨t, ht6⟩, rfl⟩
  rw [vt_push_filter, refSide_eq, List.map_map]
  simp only [Function.comp_def]
  have e := vt_pad_table (vtHt rows t) (vtRw rows t) t β (pw t) W
    (paddingRowK (tables.getD t default)) S _ _ _ (vt_padTie_push t) (vt_pushPad_data t)
  rw [List.map_congr_left (g := fun x ↦ x.1 * pw t * (blockVal β W x.2
    (((paddingRowK (tables.getD t default)).map ofK).getD · 0) + 1)) ?_]
  · rw [e, vtPadTable]
  · intro x hx
    obtain ⟨c, -, hc⟩ := List.mem_map.mp (List.of_mem_zip hx).2
    rw [← hc, hpw t ht6, vt_padding]

/-- **The pull side's padding sum**: the push side's, its blocks' forms taking the push side's
values on the padding rows. -/
theorem vt_padSum_pull (rows : List ℕ) (p : List E) (β : E) (W : List E) (S pw : ℕ → E)
    (hpw : ∀ t < 6, paddingWeight (p.take (vtHt rows t)) (vtRw rows t) = pw t) :
    padSum W β p ((vtPushPadData.map fun x ↦ S x.2.2.1).zip (vtPullBlocks rows)) =
      vtPadSum S pw (W.getD · 0) (β + 1) vtPushPadData := by
  have hown := vt_pull_owners rows
  rw [padSum, vt_split_owner _ (fun x ↦ x.2.owner) _ (fun x hx ↦
    (vt_blocks_owner_lt rows).2.1 _ (List.of_mem_zip hx).2), vt_padSum_range]
  refine sum_congr rfl fun t ht ↦ ?_
  have ht6 := mem_range.mp ht
  rw [vt_zip_filter _ _ _ _ _ hown]
  obtain ⟨t, rfl⟩ : ∃ t' : Fin 6, (t' : ℕ) = t := ⟨⟨t, ht6⟩, rfl⟩
  rw [vt_pull_filter, refSide_eq, List.map_map]
  simp only [Function.comp_def]
  have e := vt_pad_table (vtHt rows t) (vtRw rows t) t β (pw t) W
    (paddingRowK (tables.getD t default)) S _ _ _ (vt_padTie_pull t) (vt_pushPad_data t)
  rw [List.map_congr_left (g := fun x ↦ x.1 * pw t * (blockVal β W x.2
    (((paddingRowK (tables.getD t default)).map ofK).getD · 0) + 1)) ?_]
  · rw [e, vtPadTable]
  · intro x hx
    obtain ⟨c, -, hc⟩ := List.mem_map.mp (List.of_mem_zip hx).2
    rw [← hc, hpw t ht6, vt_padding]

theorem vt_countPad_data : ∀ t : Fin 6,
    (vtCountPadData.filter fun x ↦ x.2.1 = (t : ℕ)).map (·.2.2.2) =
      (vtCountCols.getD t []).map fun _ ↦ [] := by
  decide

theorem vt_countPad_zero : ∀ t : Fin 6, ∀ l ∈ vtCountCols.getD t [],
    (paddingRowK (tables.getD t default)).getD l 0 = 0 := by
  have h := vtPadCount
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  intro t l hl
  exact h t t.isLt l hl

/-- A count table's blocks' padding terms. -/
theorem vt_count_pad_table (h n o : ℕ) (pw : E) (row : List K) (S W : ℕ → E) :
    ∀ (dataT : List (ℕ × ℕ × ℕ × List (ℕ × ℕ))) (cols : List ℕ),
      dataT.map (·.2.2.2) = cols.map (fun _ ↦ []) → (∀ l ∈ cols, row.getD l 0 = 0) →
      (((dataT.map fun x ↦ S x.2.2.1).zip (cols.map fun l ↦
          (⟨h, n, [Form.col l], o⟩ : BusBlock))).map fun x ↦
          x.1 * pw * (blockVal 0 [1] x.2 ((row.map ofK).getD · 0) + 1)).sum =
        pw * (dataT.map fun x ↦ S x.2.2.1 * (1 +
          (x.2.2.2.map fun ic ↦ W ic.1 * word ic.2 0).sum)).sum
  | [], _, _, _ => by simp
  | _ :: _, [], hd, _ => by simp at hd
  | x :: dataT, l :: cols, hd, hz => by
    simp only [List.map_cons, List.cons.injEq] at hd
    have ih := vt_count_pad_table h n o pw row S W dataT cols hd.2
      fun l' hl' ↦ hz l' (by simp [hl'])
    have hzl : (row.map ofK).getD l 0 = 0 := by rw [vt_getD_map_ofK, hz l (by simp), ofK_zero]
    have hb : blockVal 0 [1] ⟨h, n, [Form.col l], o⟩ ((row.map ofK).getD · 0) = 0 := by
      simp only [blockVal, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, evaluate_eq_sum, Form.col, List.prod_cons, List.prod_nil, hzl]
      ring
    simp only [List.map_cons, List.zip_cons_cons, List.sum_cons] at ih ⊢
    rw [ih, hd.1, hb]
    simp only [List.map_nil, List.sum_nil]
    ring

/-- **The count side's padding sum.** -/
theorem vt_padSum_count (rows : List ℕ) (p : List E) (S pw W : ℕ → E)
    (hpw : ∀ t < 6, paddingWeight (p.take (vtHt rows t)) (vtRw rows t) = pw t) :
    padSum [1] 0 p ((vtCountPadData.map fun x ↦ S x.2.2.1).zip (vtCountBlocks rows)) =
      vtPadSum S pw W 1 vtCountPadData := by
  have hown := vt_count_owners rows
  rw [padSum, vt_split_owner _ (fun x ↦ x.2.owner) _ (fun x hx ↦
    (vt_blocks_owner_lt rows).2.2 _ (List.of_mem_zip hx).2), vt_padSum_range]
  refine sum_congr rfl fun t ht ↦ ?_
  have ht6 := mem_range.mp ht
  rw [vt_zip_filter _ _ _ _ _ hown]
  obtain ⟨t, rfl⟩ : ∃ t' : Fin 6, (t' : ℕ) = t := ⟨⟨t, ht6⟩, rfl⟩
  rw [vt_count_filter]
  have e := vt_count_pad_table (vtHt rows t) (vtRw rows t) t (pw t)
    (paddingRowK (tables.getD t default)) S W _ _ (vt_countPad_data t) (vt_countPad_zero t)
  rw [List.map_congr_left (g := fun x ↦ x.1 * pw t * (blockVal 0 [1] x.2
    (((paddingRowK (tables.getD t default)).map ofK).getD · 0) + 1)) ?_]
  · rw [e, vtPadTable]
  · intro x hx
    obtain ⟨c, -, hc⟩ := List.mem_map.mp (List.of_mem_zip hx).2
    rw [← hc, hpw t ht6, vt_padding]

end
end LeanVM.Guest.B1.Tables
