/-
  LeanVM.Protocol.Relation.Link.Facts

  The layout's facts in the link's arithmetization package: the Keccak defect's extension is
  multilinear, the `KECCAK` row point of the link's end, and the drawn group's numerator is small.
-/

module

public import LeanVM.Protocol.Relation.Link.Spec
public import LeanVM.Protocol.Relation.Link.Shape
import LeanVM.Protocol.Tables
import LeanVM.Protocol.Relation.Link.Valid

/-!
# The layout's facts

`LinkArith` (`Link/Spec.lean`) is `LinkCore`, the arithmetization proper, with three facts of the
layout alone, proved here (`linkArith_of_core`):

* `keccak_deg`: a multilinear extension at a prefix of the point is of degree at most one in each
  coordinate (`perVarDeg_rowMle_take`);
* `keccak_point`: the row side's fold puts table `t`'s row point, the first `h_t` row challenges, in
  the end's columns (`tailValues_rowPoint`, by `rowInv_fold`);
* `group_small`: the row variables are at most `2^MAX_TABLE_LOG` and the width at most `24`
  (`linkRows_le`, `chunks_width_le`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.Link Finset

@[expose] public section

/-! ## The defect is multilinear -/

/-- A point with its coordinate `k` set apart. -/
theorem split_at_coord {L : List E} {k : ℕ} (hk : k < L.length) :
    L = L.take k ++ L.getD k 0 :: L.drop (k + 1) := by
  rw [List.getD_eq_getElem _ _ hk, ← List.drop_eq_getElem_cons hk, List.take_append_drop]

/-- **A multilinear extension at a prefix of the point** is of degree at most one in each
coordinate. -/
theorem perVarDeg_rowMle_take (h n : ℕ) (f : ℕ → E) :
    PerVarDeg (fun p ↦ rowMle (p.take h) f) n 1 := by
  intro pre rest _
  by_cases hk : pre.length < h
  · set rest' := rest.take (h - pre.length - 1)
    have htake : ∀ c : E, (pre ++ c :: rest).take h = pre ++ c :: rest' := by
      intro c
      rw [List.take_append, List.take_of_length_le hk.le,
        show h - pre.length = (h - pre.length - 1) + 1 by omega, List.take_succ_cons]
    set m := pre.length + 1 + rest'.length with hm
    let w : ℕ → E := fun i ↦ f i * eqEval ((Tables.boolPoint m i).take pre.length) pre *
      eqEval ((Tables.boolPoint m i).drop (pre.length + 1)) rest'
    refine ⟨∑ i ∈ range (2 ^ m), (Polynomial.C (w i) * Polynomial.X +
      Polynomial.C (w i * (1 + (Tables.boolPoint m i).getD pre.length 0))), ?_, fun c ↦ ?_⟩
    · exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ ↦ Polynomial.natDegree_linear_le
    · have hl : (pre ++ c :: rest').length = m := by simp [hm]; omega
      simp only [htake, rowMle, hl]
      rw [Tables.multilinearEval_eq_sum m _ _ (by simp) hl, ← Polynomial.coe_evalRingHom, map_sum]
      refine sum_congr rfl fun i hi ↦ ?_
      have hlen : (Tables.boolPoint m i).length = m := Tables.length_boolPoint m i
      have he : eqEval (Tables.boolPoint m i) (pre ++ c :: rest') =
          eqEval ((Tables.boolPoint m i).take pre.length) pre *
            ((1 + (Tables.boolPoint m i).getD pre.length 0 + c) *
              eqEval ((Tables.boolPoint m i).drop (pre.length + 1)) rest') := by
        conv_lhs => rw [split_at_coord (show pre.length < (Tables.boolPoint m i).length by omega)]
        rw [Tables.eqEval_append _ _ _ _ (by simp [hlen]; omega), Tables.eqEval_cons]
      have hf : ((List.range (2 ^ m)).map f).getD i 0 = f i := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (mem_range.mp hi)]
        rfl
      rw [he, hf]
      simp only [Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, w]
      ring
  · refine ⟨Polynomial.C (rowMle (pre.take h) f), by simp, fun c ↦ ?_⟩
    beta_reduce
    rw [Polynomial.eval_C, List.take_append_of_le_length (by omega)]

/-- **The Keccak defect's extension is multilinear** in the row side's variables. -/
theorem keccakDefectRow_perVarDeg (layout : Layout) {μ : ℕ} (q : Column μ) (l : ℕ) :
    PerVarDeg (keccakDefectRow layout q l) (linkRowVars layout) 1 :=
  perVarDeg_rowMle_take _ _ _

/-! ## The `KECCAK` row point -/

/-- **Table `t`'s row point in the link's end** is the first `h_t` row challenges. -/
theorem tailValues_rowPoint (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E)
    (m1 : E) (fresh : List E) (split : Split) (chi qPoint message : List E) {t : ℕ}
    (ht : t < layout.tables.length) :
    ((tailValues layout chunks theta0 drawn r m1 fresh split chi qPoint message).2.columns.getD t
      ([], [])).1 = chi.take (layout.tableLogHeights.getD t 0) := by
  unfold tailValues
  dsimp only
  refine ((rowInv_fold layout chi _ ?_ _ ⟨rfl, rfl⟩).2.1 t ht).1
  intro acc table t
  dsimp only
  refine ⟨⟨(nonPointerCols layout t table).zip
    (acc.sent.take (nonPointerCols layout t table).length), ?_, map_fst_zip_prefix _ _⟩, ?_⟩
  · rw [foldl_columns]
    · rfl
    · intro a x
      obtain ⟨p, k⟩ := x
      rfl
  · intro pc hpc
    have key := foldl_pieces _ (GoodPiece layout chi t) _ ?_ _ pc hpc
    · exact key
    intro a x hx pc' hpc'
    obtain ⟨p, k⟩ := x
    simp only [List.mem_append, List.mem_singleton] at hpc'
    rcases hpc' with h | rfl
    · exact .inl h
    · exact .inr ⟨p, fst_mem_of_mem_zipIdx _ _ _ hx, rfl, rfl⟩

/-! ## The group's numerator -/

theorem foldl_max_le_of : ∀ (L : List ℕ) (a B : ℕ), a ≤ B → (∀ x ∈ L, x ≤ B) → L.foldl max a ≤ B
  | [], _, _, ha, _ => ha
  | x :: L, _, B, ha, hL =>
    foldl_max_le_of L _ B (max_le ha (hL x (by simp))) fun y hy ↦ hL y (by simp [hy])

theorem log2Ceil_le_self (n : ℕ) : log2Ceil n ≤ n := by
  unfold log2Ceil bitLength
  split_ifs with h
  · omega
  · have := (Nat.log2_lt h).mpr (Nat.lt_two_pow_self (n := n - 1))
    omega

theorem zipWith_heights_le : ∀ (rows floors : List ℕ) (B : ℕ), (∀ x ∈ rows, x ≤ B) →
    (∀ x ∈ floors, x ≤ B) →
    ∀ y ∈ List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) rows floors, y ≤ B
  | [], _, _, _, _, y, hy => by simp at hy
  | _ :: _, [], _, _, _, y, hy => by simp at hy
  | r :: rs, f :: fs, B, hr, hf, y, hy => by
    simp only [List.zipWith_cons_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact max_le ((log2Ceil_le_self r).trans (hr r (by simp))) (hf f (by simp))
    · exact zipWith_heights_le rs fs B (fun x hx ↦ hr x (by simp [hx]))
        (fun x hx ↦ hf x (by simp [hx])) y hy

/-- The row side's row variables are at most `2^MAX_TABLE_LOG`. -/
theorem linkRows_le {bytecode : List K} {layout : Layout} {ρ : ℕ}
    (hA : Announced bytecode layout ρ) : linkRows layout ≤ 2 ^ maxTableLog := by
  obtain ⟨lm, rows, hB⟩ := announced_build hA
  unfold buildLayout at hB
  split at hB
  · cases hB
  · split at hB
    · next hc =>
      simp only [Option.some.injEq] at hB
      subst hB
      unfold linkRows
      refine foldl_max_le_of _ _ _ (Nat.zero_le _) (zipWith_heights_le _ _ _ (fun x hx ↦ ?_)
        (fun x hx ↦ ?_))
      · simpa using List.all_eq_true.mp hc.2.2.1 x hx
      · simp only [tableLogFloors, keccakMinStepsLog, List.mem_cons, List.not_mem_nil,
          or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [maxTableLog]
    · cases hB

/-- The pointer width is at most `24`. -/
theorem chunks_width_le {w : ℕ} {c : Chunks} (h : Chunks.new w = some c) :
    c.width ≤ maxPointerWidth := by
  rw [Chunks.new_width h]
  unfold Chunks.new at h
  split_ifs at h with hw
  exact hw.2

/-- **The drawn group's numerator is below `|E|`.** -/
theorem linkGroupError_small {bytecode : List K} {layout : Layout} {ρ : ℕ}
    (hA : Announced bytecode layout ρ) {chunks : Chunks}
    (hch : Chunks.new (linkWidth layout) = some chunks) : linkGroupError layout chunks < 2 ^ 128 := by
  have h1 : linkRows layout ≤ 2 ^ 30 := linkRows_le hA
  have h2 : chunks.width ≤ 24 := chunks_width_le hch
  have h3 : linkGroupError layout chunks ≤ 2 ^ 30 + 7 := by
    unfold linkGroupError
    rw [show bytecodeSlotBits = 4 from rfl]
    exact max_le (by omega) (by omega)
  exact lt_of_le_of_lt h3 (by norm_num)

/-! ## The package -/

/-- **The link's arithmetization from its core**, at an announced layout and the link's chunks. -/
def linkArith_of_core {bytecode : List K} {layout : Layout} {ρ : ℕ}
    (hA : Announced bytecode layout ρ) {μ : ℕ} {q : Column μ} {chunks : Chunks}
    (hch : Chunks.new (linkWidth layout) = some chunks) (C : LinkCore layout q chunks) :
    LinkArith layout q chunks where
  toLinkCore := C
  keccak_deg := keccakDefectRow_perVarDeg layout q
  keccak_point theta0 drawn r m1 fresh split chi qPoint message := by
    have hT := (announced_facts hA).2.1
    exact tailValues_rowPoint layout chunks theta0 drawn r m1 fresh split chi qPoint message
      (by rw [hT, tables_length]; decide)
  group_small := linkGroupError_small hA hch

end

end LeanVM.Protocol.Relation
