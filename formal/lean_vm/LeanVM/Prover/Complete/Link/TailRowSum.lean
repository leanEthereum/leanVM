/-
  LeanVM.Prover.Complete.Link.TailRowSum

  The verifier's row side on the honest message, table by table: its coefficient, shifts,
  certificate weight and base are sums over the honest pointer columns and base terms.
-/

module

public import LeanVM.Prover.Complete.Link.TailRowFold
public import LeanVM.Prover.Complete.Link.TailIndex

/-!
# The verifier's row side on the honest message

`tailRowInv m`: after the first `m` tables, the verifier's pointer count and unread values, and
its coefficient, shifts, certificate weight and base, are the first `m` tables' (`tailRowPT`, a
table's pointer columns `Σ_k eq(q*, q_t + k)·g(colSpec)`, `tailRowCW`, `baseAt`).
`tailRowInv_step`: one table keeps it. `rowSide_honest`: all six tables.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover LeanVM.Protocol.Verifier.Defers

/-- The honest message's values: each table's non-pointer columns at its row point. -/
noncomputable def hValues (W : Witness) (chi : List E) : List E :=
  (List.range nTables).flatMap fun t ↦
    (nonPtr t).map (mcolOf W t (chi.take (W.layout.tableLogHeights.getD t 0)))

/-- Table `t`'s pointer columns, `g` of each under `eq(q*, ·)`. -/
noncomputable def tailRowPT (W : Witness) (x : LinkProverPre) (chi qPoint : List E) (t : ℕ)
    (g : ColumnAt → E) : E :=
  ((tables.getD t default).links.pointers.zipIdx.map fun pk ↦
    (eqKernel qPoint).getD (pointerStarts.getD t 0 + pk.2) 0 *
      g (colSpec W (linkRowInputs W x) t (pointerStarts.getD t 0)
        ((chi.foldl rowFold (linkRowStart W x)).getD t default) chi pk.1 pk.2)).sum

/-- Table `t`'s part of the certificate weight. -/
noncomputable def tailRowCW (W : Witness) (x : LinkProverPre) (chi qPoint : List E) (t : ℕ) : E :=
  ((tables.getD t default).links.pointers.zipIdx.map fun pk ↦
    (eqKernel qPoint).getD (pointerStarts.getD t 0 + pk.2) 0 *
      ((chi.foldl rowFold (linkRowStart W x)).getD t default).corner *
      ((chi.foldl rowFold (linkRowStart W x)).getD t default).prods.at 0 *
      (linkRowInputs W x).ch.eps.getD (pointerStarts.getD t 0 + pk.2) 0).sum

/-- The verifier's row side after the first `m` tables. -/
def tailRowInv (W : Witness) (x : LinkProverPre) (chi qPoint : List E) (m : ℕ) (acc : LinkRowSide) :
    Prop :=
  acc.q = ((List.range m).map fun t ↦ (tables.getD t default).links.pointers.length).sum ∧
  acc.sent = (hValues W chi).drop ((List.range m).map fun t ↦ (nonPtr t).length).sum ∧
  acc.coef = ((List.range m).map fun t ↦ tailRowPT W x chi qPoint t (·.coef)).sum ∧
  acc.shifts.length = (linkRowInputs W x).maxShift ∧
  (∀ s < (linkRowInputs W x).maxShift, acc.shifts.getD s 0 =
    ((List.range m).map fun t ↦ tailRowPT W x chi qPoint t (·.shifts.getD s 0)).sum) ∧
  acc.certWeight = ((List.range m).map fun t ↦ tailRowCW W x chi qPoint t).sum ∧
  acc.base = ((List.range m).map fun t ↦
    baseAt ((chi.foldl rowFold (linkRowStart W x)).getD t default)).sum

theorem getD_map_pointers {t : ℕ} (ht : t < nTables) :
    (tables.map (·.links.pointers)).getD t [] = (tables.getD t default).links.pointers := by
  have hl : tables.length = nTables := by decide +kernel
  simp [List.getD_eq_getElem?_getD, show t < tables.length by omega]

theorem mem_zipIdx_lt_two {l : List ℕ} {pk : ℕ × ℕ} (h : pk ∈ l.zipIdx) (hk : pk.2 < 2) :
    pk.1 ∈ l.take 2 := by
  obtain ⟨p, k⟩ := pk
  rw [List.mem_zipIdx_iff_getElem?] at h
  simp only at h hk
  have hlt : k < l.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h
    cases h
  rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at h
  subst h
  exact List.mem_iff_getElem.mpr ⟨k, by simp; omega, by simp⟩

theorem vValuesOf_getD {t : ℕ} (sent : List E) (f : ℕ → E)
    (hs : sent.take (nonPtr t).length = (nonPtr t).map f) {c : ℕ} (hc : c ∈ nonPtr t) :
    (vValuesOf (tables.getD t default) (nonPtr t) sent).getD c 0 = f c := by
  unfold vValuesOf
  rw [getD_map_range_E _ _ _ (lt_of_mem_nonPtr hc), hs,
    lookup_zip_map f (nonPtr t) (by unfold nonPtr; exact List.Nodup.filter _ List.nodup_range) c hc]
  rfl

theorem hValues_take {W : Witness} {chi : List E} {m : ℕ} (hm : m < nTables) :
    ((hValues W chi).drop ((List.range m).map fun t ↦ (nonPtr t).length).sum).take (nonPtr m).length =
      (nonPtr m).map (mcolOf W m (chi.take (W.layout.tableLogHeights.getD m 0))) := by
  have := tailRow_take_drop_flatMap (fun t ↦ (nonPtr t).map
    (mcolOf W t (chi.take (W.layout.tableLogHeights.getD t 0)))) hm
  simp only [List.length_map] at this
  exact this

theorem sum_range_succ_map (m : ℕ) (f : ℕ → E) :
    ((List.range (m + 1)).map f).sum = ((List.range m).map f).sum + f m := by
  simp [List.range_succ]

theorem sum_range_succ_mapN (m : ℕ) (f : ℕ → ℕ) :
    ((List.range (m + 1)).map f).sum = ((List.range m).map f).sum + f m := by
  simp [List.range_succ]

section Step

variable {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog} {W : Witness}
  (hW : witness? prog input ex = some W) (x : LinkProverPre) (chi qPoint : List E)
  (hchi : chi.length = linkNRows W) (htau : x.ch.tau.length = linkNRows W)
  (hfresh : x.fresh.length = 5)

include hW hchi htau hfresh in
/-- **One table keeps the invariant.** -/
theorem tailRowInv_step {m : ℕ} (hm : m < nTables) (acc : LinkRowSide)
    (hI : tailRowInv W x chi qPoint m acc) :
    tailRowInv W x chi qPoint (m + 1) (vTableStep W.layout (linkRowInputs W x).ch chi
      (linkRowInputs W x).jump (linkRowInputs W x).eqZeta (linkRowInputs W x).shiftZeta
      (linkRowInputs W x).xBc (linkRowInputs W x).pFp (linkRowInputs W x).yMem (linkRowInputs W x).m1
      (linkRowInputs W x).eq0 (eqKernel qPoint) acc (tables.getD m default, m)) := by
  have hlay := (linkSizes hW).1
  obtain ⟨hq, hsent, hcoef, hsl, hsh, hcw, hbase⟩ := hI
  have hf := tableFacts hm
  obtain ⟨-, hcorner, h0, h1, h2, hcol, -⟩ := boundAt hW x chi hchi htau hm
  set inp := linkRowInputs W x with hinp
  set rt := (chi.foldl rowFold (linkRowStart W x)).getD m default with hrt
  set h := W.layout.tableLogHeights.getD m 0 with hh
  have hhle : h ≤ chi.length := hchi ▸ le_foldl_max _ _
  have hlen : (chi.take h).length = h := by rw [List.length_take, min_eq_left hhle]
  obtain ⟨-, steps, -, -, hl, -, -, -, -⟩ := witness?_spec hW
  have hrows : W.layout.tableRows.getD m 0 = W.rows.getD m 0 := by
    rw [(buildLayout_spec hl).2.1]
  have hrle : W.rows.getD m 0 ≤ 2 ^ h := by
    rw [← hrows, (buildLayout_spec hl).2.1]; exact rows_le_height hl hm
  have homega : omegaAt (inp.ch.theta.getD m 0) (inp.ch.tau.take h) (chi.take h)
      (W.layout.tableRows.getD m 0) = rt.prods.at 0 := by
    rw [hrows, h0]
    exact omegaAt_eq_mleA _ _ _ (by rw [show inp.ch.tau.length = linkNRows W from htau]; exact hchi ▸ hhle)
      hlen hrle
  have hact : lessThan (chi.take h) (W.layout.tableRows.getD m 0) = rt.prods.at 1 := by
    rw [hrows, h1]
  have hptrs : (W.layout.tables.map (·.links.pointers)).getD m [] =
      (tables.getD m default).links.pointers := by rw [hlay, getD_map_pointers hm]
  have hS : ∀ pk ∈ ((W.layout.tables.map (·.links.pointers)).getD m []).zipIdx,
      ∀ am ∈ accessesAt (tables.getD m default).links (inp.ch.mu.getD m []) pk.1,
        am.1.shift ≤ acc.shifts.length := by
    intro pk _ am ham
    rw [hsl]
    exact tables_shift_le m hm _ (mem_memory_of_accessesAt ham)
  have hlow : ∀ pk ∈ ((W.layout.tables.map (·.links.pointers)).getD m []).zipIdx, pk.2 < 2 →
      accessesAt (tables.getD m default).links (inp.ch.mu.getD m []) pk.1 = [] := by
    intro pk hpk hk
    rw [hptrs] at hpk
    have hp := mem_zipIdx_lt_two hpk hk
    unfold accessesAt
    rw [List.filter_eq_nil_iff]
    intro am ham hpe
    have ha := (List.of_mem_zip ham).1
    simp only [decide_eq_true_eq] at hpe
    exact hf.pointer _ ha (hpe ▸ hp)
  -- the values the verifier reads
  have hv : ∀ c ∈ nonPtr m, (vValuesOf (tables.getD m default)
      ((List.range (tables.getD m default).width).filter
        fun c ↦ !(tables.getD m default).links.pointers.contains c) acc.sent).getD c 0 =
      mcolOf W m (chi.take h) c := by
    intro c hc
    exact vValuesOf_getD acc.sent _ (by rw [hsent]; exact hValues_take hm) hc
  have hps : acc.q = pointerStarts.getD m 0 := by rw [hq, pointerStarts_eq m hm]
  obtain ⟨F1, F2, F3, F4, F5, F6, F7⟩ := vTableStep_fields W.layout inp.ch chi inp.jump inp.eqZeta
    inp.shiftZeta inp.xBc inp.pFp inp.yMem inp.m1 inp.eq0 (eqKernel qPoint) acc (tables.getD m default)
    m hS hlow
  simp only [← hh] at F1 F2 F3 F4 F5 F6 F7
  simp only [hptrs, homega, hact, ← hcorner, hps] at F1 F2 F3 F4 F5 F6 F7
  have hjl : inp.jump.length = 4 := by simp [hinp, linkRowInputs, hfresh]
  refine ⟨?_, ?_, ?_, ?_, fun s hs ↦ ?_, ?_, ?_⟩
  · rw [F1, pointerStarts_eq m hm, sum_range_succ_mapN]
  · rw [F2, hsent, List.drop_drop, sum_range_succ_mapN]
    congr 1
  · rw [F3, hcoef, sum_range_succ_map]
    refine congrArg (HAdd.hAdd _) ?_
    unfold tailRowPT
    simp only [← hinp, ← hrt]
    refine congrArg List.sum (List.map_congr_left fun pk _ ↦ ?_)
    have hc := colSpec_eq hW x chi hchi htau hm _ hv pk.1 pk.2
    simp only [← hinp, ← hrt] at hc
    rw [hc.1]
    ring
  · rw [F5, hsl]
  · rw [F6 s (hsl ▸ hs), hsh s hs, sum_range_succ_map]
    refine congrArg (HAdd.hAdd _) ?_
    unfold tailRowPT
    simp only [← hinp, ← hrt]
    refine congrArg List.sum (List.map_congr_left fun pk _ ↦ ?_)
    have hc := colSpec_eq hW x chi hchi htau hm _ hv pk.1 pk.2
    simp only [← hinp, ← hrt] at hc
    rw [hc.2.1 s hs]
    ring
  · rw [F4, hcw, sum_range_succ_map]
    rfl
  · rw [F7, hbase, sum_range_succ_map]
    refine congrArg (HAdd.hAdd _) ?_
    have hb := baseAt_eq_payload hW x chi hchi hm
    simp only [← hinp, ← hrt] at hb
    rw [hb]
    have hpay : payloadAt inp.ch (tables.getD m default).links (inp.ch.mu.getD m [])
        (fun c ↦ (vValuesOf (tables.getD m default)
          ((List.range (tables.getD m default).width).filter
            fun c ↦ !(tables.getD m default).links.pointers.contains c) acc.sent).getD c 0) =
        payloadAt inp.ch (tables.getD m default).links (inp.ch.mu.getD m [])
          (fun c ↦ rt.prods.at (3 + c)) :=
      payloadAt_congr hf _ _ fun c hc ↦ by rw [hv c hc, hcol c (lt_of_mem_nonPtr hc)]
    by_cases hn : 0 < (tables.getD m default).nConstraints
    · have h4 := hf.jump hn
      subst h4
      simp only [hn, ↓reduceIte, hpay, jump_constraints]
      rw [← jump_evaluate inp.jump _ (fun c ↦ rt.prods.at (3 + c)) hjl (fun c hc ↦ by
        have hc' := jumpCols_nonPtr c hc
        rw [hv c hc', hcol c (lt_of_mem_nonPtr hc')]), ← h2]
    · simp only [hn, ↓reduceIte, hpay]
      ring

include hW hchi htau hfresh in
theorem tailRowInv_take : ∀ m ≤ nTables, tailRowInv W x chi qPoint m
    ((tables.zipIdx.take m).foldl (vTableStep W.layout (linkRowInputs W x).ch chi
      (linkRowInputs W x).jump (linkRowInputs W x).eqZeta (linkRowInputs W x).shiftZeta
      (linkRowInputs W x).xBc (linkRowInputs W x).pFp (linkRowInputs W x).yMem (linkRowInputs W x).m1
      (linkRowInputs W x).eq0 (eqKernel qPoint))
      ⟨0, List.replicate (linkRowInputs W x).maxShift 0, 0, 0, [], 0, [], hValues W chi⟩)
  | 0, _ => by
    refine ⟨rfl, rfl, rfl, by simp, fun s hs ↦ ?_, rfl, rfl⟩
    simp [List.getD_eq_getElem?_getD, hs]
  | m + 1, hm => by
    have hl : tables.length = nTables := by decide +kernel
    have hm' : m < tables.length := by rw [hl]; omega
    rw [List.take_add_one, List.foldl_append, List.getElem?_zipIdx, List.getElem?_eq_getElem hm']
    simp only [Option.map_some, Option.toList_some, List.foldl_cons, List.foldl_nil, zero_add]
    have hg : tables[m] = tables.getD m default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm', Option.getD_some]
    rw [hg]
    exact tailRowInv_step hW x chi qPoint hchi htau hfresh (by omega) _
      (tailRowInv_take m (by omega))

include hW hchi htau hfresh in
/-- **The verifier's row side on the honest message.** -/
theorem rowSide_honest :
    tailRowInv W x chi qPoint nTables (rowSideOf W.layout (linkRowInputs W x).ch chi
      (linkRowInputs W x).jump (linkRowInputs W x).eqZeta (linkRowInputs W x).shiftZeta
      (linkRowInputs W x).xBc (linkRowInputs W x).pFp (linkRowInputs W x).yMem (linkRowInputs W x).m1
      (linkRowInputs W x).eq0 (eqKernel qPoint) (linkRowInputs W x).maxShift (hValues W chi)) := by
  have hl : tables.length = nTables := by decide +kernel
  rw [rowSideOf_eq, (linkSizes hW).1, ← List.take_of_length_le (l := tables.zipIdx) (i := nTables)
    (by simp [hl])]
  exact tailRowInv_take hW x chi qPoint hchi htau hfresh nTables le_rfl

end Step

end LeanVM.Prover.Complete

end
