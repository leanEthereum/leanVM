/-
  LeanVM.Prover.Complete.Link.TailRow

  The link's terminal summand on the honest message is the pointer-column rounds' folded value.
-/

module

public import LeanVM.Prover.Complete.Link.TailRowClaim
public import LeanVM.Prover.Complete.Link.TailOut

/-!
# The link's tail, its row side

`tailRowSide_honest`: on the honest message the verifier's row side is `rowSideOf` at the honest
prover's challenges, index values and message values (`honestIndexAt`). `qSum_linkColumns`: a
field of the pointer columns under `eq(q*, ·)` is the tables' sums (`tailRowPT`).
`honestTail_value`: the terminal check's summand is the pointer-column rounds' folded value, both
being `colTerm` of the pointer columns' fields under `eq(q*, ·)` plus `eq(0, q*)` times the base
terms (`rowSide_honest`, `value_foldl_columnProds`, `summand_eq_colTerm`).
`linkTailHolds_honest`: `LinkTailHolds` on the honest witness.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover LeanVM.Protocol.Verifier.Defers

/-! ## Sums over the tables' columns -/

theorem zipIdx_flatMap_sum {α : Type} (F : ℕ → List α) (G : α × ℕ → E) : ∀ (n k : ℕ),
    ((((List.range n).flatMap F).zipIdx k).map G).sum =
      ((List.range n).map fun t ↦
        (((F t).zipIdx (k + ((List.range t).map fun t' ↦ (F t').length).sum)).map G).sum).sum
  | 0, _ => by simp
  | n + 1, k => by
    rw [List.range_succ, List.flatMap_append, List.zipIdx_append, List.map_append, List.sum_append,
      zipIdx_flatMap_sum F G n k, List.map_append, List.sum_append]
    simp [List.length_flatMap]

theorem zipIdx_map_zipIdx {α β : Type} (Fm : β × ℕ → α) (G : α × ℕ → E) (s : ℕ) :
    ∀ (L : List β) (k0 : ℕ), ((((L.zipIdx k0).map Fm).zipIdx (s + k0)).map G).sum =
      ((L.zipIdx k0).map fun pk ↦ G (Fm pk, s + pk.2)).sum
  | [], _ => by simp
  | a :: L, k0 => by
    rw [List.zipIdx_cons, List.map_cons, List.zipIdx_cons, List.map_cons, List.sum_cons,
      List.map_cons, List.sum_cons, show s + k0 + 1 = s + (k0 + 1) by omega,
      zipIdx_map_zipIdx Fm G s L (k0 + 1)]

section Honest

variable {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog} {W : Witness}
  (hW : witness? prog input ex = some W) (x : LinkProverPre) (chi qPoint : List E)
  (hchi : chi.length = linkNRows W) (htau : x.ch.tau.length = linkNRows W)

include hW hchi htau in
/-- **A field of the pointer columns under `eq(q*, ·)`, table by table.** -/
theorem qSum_linkColumns (g : ColumnAt → E) :
    qSum (linkColumns W x chi (chi.foldl rowFold (linkRowStart W x))) qPoint g =
      ((List.range nTables).map fun t ↦ tailRowPT W x chi qPoint t g).sum := by
  unfold qSum linkColumns
  rw [zipIdx_flatMap_sum]
  refine congrArg List.sum (List.map_congr_left fun t ht ↦ ?_)
  have ht' := List.mem_range.mp ht
  have hoff : 0 + ((List.range t).map fun t' ↦ (columnsAt W (linkRowInputs W x) t'
      (pointerStarts.getD t' 0) ((chi.foldl rowFold (linkRowStart W x)).getD t' default) chi).length).sum =
      pointerStarts.getD t 0 + 0 := by
    rw [zero_add, add_zero, pointerStarts_eq t ht']
    refine congrArg List.sum (List.map_congr_left fun t' _ ↦ ?_)
    rw [length_columnsAt]
  rw [hoff, (boundAt hW x chi hchi htau ht').2.2.2.2.2.2, zipIdx_map_zipIdx]
  rfl

include hW hchi htau in
theorem linkColumns_values {c : ColumnAt}
    (hc : c ∈ linkColumns W x chi (chi.foldl rowFold (linkRowStart W x))) :
    c.values = (linkRowInputs W x).functionals.values W.chunks c.slices ∧ c.slices.length = 64 := by
  unfold linkColumns at hc
  obtain ⟨t, ht, hc⟩ := List.mem_flatMap.mp hc
  have ht' := List.mem_range.mp ht
  rw [(boundAt hW x chi hchi htau ht').2.2.2.2.2.2] at hc
  obtain ⟨pk, -, rfl⟩ := List.mem_map.mp hc
  have h := colSpec_eq hW x chi hchi htau ht' (mcolOf W t (chi.take (W.layout.tableLogHeights.getD t 0)))
    (fun _ _ ↦ rfl) pk.1 pk.2
  exact ⟨h.2.2.2.1, h.2.2.2.2⟩

/-! ## The terminal summand -/

theorem tailRow_tailNValues_eq (layout : Layout) (htab : layout.tables = tables) (chi : List E) (W : Witness) :
    tailNValues layout = (hValues W chi).length := by
  have h : (tables.zipIdx.map fun (tt : Table × ℕ) ↦ ((List.range tt.1.width).filter fun c ↦
      !((tables.map (·.links.pointers)).getD tt.2 []).contains c).length).sum =
      ((List.range nTables).map fun t ↦ (nonPtr t).length).sum := by decide +kernel
  unfold tailNValues hValues
  rw [htab, List.length_flatMap]
  simp only [List.length_map]
  exact h

/-- The honest message's slices: the pointer columns' slices under `eq(q*, ·)`. -/
def hSlices (columns : List ColumnAt) (qPoint : List E) : List E :=
  (List.range 64).map fun b ↦ sumE (columns.zipIdx.map fun (c, q) ↦ (eqTable qPoint).getD q 0 * c.slices.getD b 0)

theorem tailRow_linkMessage_eq (W : Witness) (x : LinkProverPre) (chi qPoint : List E) (st : RowState) :
    linkMessage W x chi qPoint st = hValues W chi ++ hSlices (linkColumns W x chi st) qPoint := rfl

include hW in
/-- **The verifier's row side on the honest message** is `rowSideOf` at the honest prover's
challenges, index values and message values. -/
theorem tailRowSide_honest {y : LinkPre} (hp : HonestPre W y x) (L : List E) :
    tailRowSide W.layout y (honestProgramSide W y) chi qPoint (hValues W chi ++ L) =
      rowSideOf W.layout (linkRowInputs W x).ch chi (linkRowInputs W x).jump
        (linkRowInputs W x).eqZeta (linkRowInputs W x).shiftZeta (linkRowInputs W x).xBc
        (linkRowInputs W x).pFp (linkRowInputs W x).yMem (linkRowInputs W x).m1 (linkRowInputs W x).eq0
        (eqKernel qPoint) (linkRowInputs W x).maxShift (hValues W chi) := by
  obtain ⟨i6, i7, i3, i5, i12⟩ := honestIndexAt hW hp
  unfold tailRowSide
  dsimp only at i6 i7 i3 i5 i12 ⊢
  rw [← i6, ← i7, ← i3, ← i5, ← i12, verCh_honest hW hp, hp.fresh, hp.m1, hp.r, hp.chunks,
    (linkSizes hW).1, tailRow_tailNValues_eq W.layout (linkSizes hW).1 chi W, List.take_left' rfl]
  rfl

theorem tailRow_getD_map_mul (l : List E) (a : E) (i : ℕ) : (l.map fun n ↦ a * n).getD i 0 = a * l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

theorem mul_sum_mul (l : List E) (a b : E) : a * l.sum * b = (l.map fun z ↦ a * z * b).sum := by
  induction l with
  | nil => simp
  | cons z l ih => rw [List.sum_cons, List.map_cons, List.sum_cons, ← ih]; ring

include hW in
/-- **The terminal check's summand on the honest message is the pointer-column rounds' folded
value.** -/
theorem honestTail_value {y : LinkPre} (hp : HonestPre W y x) (hchi : chi.length = linkNRows W)
    (hq : qPoint.length = log2Ceil (linkNPointers W.layout)) :
    (honestTail W y x chi qPoint).1 = (qPoint.foldl Prods.fold
      (linkColumnProds W x chi (chi.foldl rowFold (linkRowStart W x)))).value := by
  have hlay := (linkSizes hW).1
  have hd := one_le_d (linkSizes hW).2.1
  have htau : x.ch.tau.length = linkNRows W := by rw [hp.ch]; exact length_tau _ _ _ _ _ hp.drawn
  have hlenC := length_linkColumns W hlay x chi (chi.foldl rowFold (linkRowStart W x))
  have hqv : log2Ceil (linkColumns W x chi (chi.foldl rowFold (linkRowStart W x))).length =
      qPoint.length := by rw [hlenC, hq]
  have hle : (linkColumns W x chi (chi.foldl rowFold (linkRowStart W x))).length ≤ 2 ^ qPoint.length := by
    rw [← hqv]; exact (log2Ceil_le_iff _ _).mp le_rfl
  obtain ⟨-, -, hcoef, hsl, hsh, hcw, hbase⟩ := rowSide_honest hW x chi qPoint hchi htau hp.freshlen
  -- the claim's side
  unfold linkColumnProds
  rw [hqv, value_foldl_columnProds _ _ hd _ _ _ _ hle]
  -- the verifier's side
  unfold honestTail
  rw [tailRow_linkMessage_eq, tailOut_eq_tailVia]
  unfold tailVia
  dsimp only
  rw [tailRowSide_honest hW x chi qPoint hp, tailRow_tailNValues_eq W.layout hlay chi W, List.drop_left' rfl,
    verCh_honest hW hp, hp.chunks, hp.r, hp.fresh, hlay]
  set R := rowSideOf W.layout (linkRowInputs W x).ch chi (linkRowInputs W x).jump
    (linkRowInputs W x).eqZeta (linkRowInputs W x).shiftZeta (linkRowInputs W x).xBc
    (linkRowInputs W x).pFp (linkRowInputs W x).yMem (linkRowInputs W x).m1 (linkRowInputs W x).eq0
    (eqKernel qPoint) (linkRowInputs W x).maxShift (hValues W chi) with hR
  set Cq := linkColumns W x chi (chi.foldl rowFold (linkRowStart W x)) with hCq
  set f := Functionals.new W.chunks x.r (tables.foldl (fun m t ↦ max m t.links.maxShift) 0) with hf
  have hfl : (f.values W.chunks (hSlices Cq qPoint)).length = 2 * f.d + (linkRowInputs W x).maxShift := by
    simp only [Functionals.values, List.length_map]
    exact length_functionals_new _ _ _
  rw [summand_eq_colTerm f (linkRowInputs W x).maxShift _ _ _ _ hsl hfl]
  have hb : R.base = linkBase (chi.foldl rowFold (linkRowStart W x)) := by
    rw [hbase, linkBase, sumE_eq_sum]
  rw [hb]
  -- the columns' fields
  have hsl' : hSlices Cq qPoint = (List.range 64).map fun b ↦
      (Cq.zipIdx.map fun cq ↦ (eqTable qPoint).getD cq.2 0 * cq.1.slices.getD b 0).sum := by
    unfold hSlices
    refine List.map_congr_left fun b _ ↦ ?_
    rw [sumE_eq_sum]
  have hval : ∀ c ∈ Cq, c.values = f.values W.chunks c.slices ∧ c.slices.length = 64 :=
    fun c hc ↦ linkColumns_values hW x chi hchi htau hc
  refine (congrArg (· + prodE (qPoint.map (1 + ·)) * linkBase (chi.foldl rowFold (linkRowStart W x)))
    (colTerm_congr W.chunks.d (linkRowInputs W x).maxShift hd f.mirrors _
      ⟨qSum Cq qPoint (·.coef),
        (List.range (linkRowInputs W x).maxShift).map (fun s ↦ qSum Cq qPoint (·.shifts.getD s 0)),
        (List.range (2 * W.chunks.d + (linkRowInputs W x).maxShift)).map
          (fun j ↦ qSum Cq qPoint (·.values.getD j 0)),
        (List.range W.chunks.d).map (fun i ↦ qSum Cq qPoint (·.certs.getD i 0)), []⟩
      ?_ (fun j hj ↦ ?_) (fun s hs ↦ ?_) (fun i hi ↦ ?_))).trans rfl
  · show R.coef = qSum Cq qPoint (·.coef)
    rw [hcoef, qSum_linkColumns hW x chi qPoint hchi htau]
  · show (f.values W.chunks (hSlices Cq qPoint)).getD j 0 = _
    rw [getD_map_range_E _ _ _ hj, hsl', getD_values_sum f W.chunks Cq.zipIdx _ (fun cq ↦ cq.1.slices)
      (fun cq hcq ↦ (hval _ (List.fst_mem_of_mem_zipIdx hcq)).2)]
    unfold qSum
    refine congrArg List.sum (List.map_congr_left fun cq hcq ↦ ?_)
    beta_reduce
    rw [(hval _ (List.fst_mem_of_mem_zipIdx hcq)).1, Keccak.getD_toList, Keccak.toList_eqTable]
  · show R.shifts.getD s 0 = _
    rw [getD_map_range_E _ _ _ hs, hsh s hs, qSum_linkColumns hW x chi qPoint hchi htau]
  · show ((linkRowInputs W x).ch.nu.map fun n ↦ x.fresh.getD 0 0 * R.certWeight * n).getD i 0 = _
    rw [tailRow_getD_map_mul, getD_map_range_E _ _ _ hi, qSum_linkColumns hW x chi qPoint hchi htau,
      hcw, mul_sum_mul, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun t ht ↦ ?_)
    have ht' := List.mem_range.mp ht
    simp only [Function.comp]
    unfold tailRowCW tailRowPT
    rw [mul_sum_mul, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun pk _ ↦ ?_)
    have h := colSpec_eq hW x chi hchi htau ht' (mcolOf W t (chi.take (W.layout.tableLogHeights.getD t 0)))
      (fun _ _ ↦ rfl) pk.1 pk.2
    simp only [Function.comp]
    rw [h.2.2.1 i hi]
    simp only [linkRowInputs]
    ring

/-- **`LinkTailHolds` on the honest witness.** -/
theorem linkTailHolds_honest (hW : witness? prog input ex = some W) : LinkTailHolds W :=
  linkTailHolds_of_value hW fun _ x hp chi qPoint hchi hq ↦ honestTail_value hW x chi qPoint hp hchi hq

end Honest

end LeanVM.Prover.Complete

end
