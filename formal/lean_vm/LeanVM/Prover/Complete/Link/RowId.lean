/-
  LeanVM.Prover.Complete.Link.RowId

  The row side's identity on the honest witness: the index side's value at `r` is the rows' claim.
-/

module

public import LeanVM.Prover.Complete.Link.RowIdIndex

/-!
# The row identity

`rowIdentity_of (hA : Admitted prog input t ρ W) : RowIdentity W`. The rows' claim is every
table's sum over its rows (`rowClaim_linkRowStart`), each its pointer columns' reads over the
executed rows plus its base terms (`cubeSum_rowProds`); the base terms are the payload at `eq(0, r)`,
`JUMP`'s identities vanishing (`baseSum`); the pointer reads regroup per access and word read
(`ptrSum_eq`). The index side's value at `r` is its arrays' extensions (`index_value`), each a sum
over the executed rows (`RowIdIndex.lean`). Row by row the two agree: the cycle pointer names the
row's cycle, an access of nonzero gate reads inside its window (`ScatterOK`, `scatterOK_of`), and
the word reads scale by `γ_word` (`wordReads_val`).
-/

@[expose] public section

namespace LeanVM.Prover.Complete.RowId

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover Finset

/-- A table's payload forms at a row: the program link's and each access's. -/
def payVal (ch : LinkChallenges) (t : ℕ) (col : ℕ → E) : E :=
  (payloadForms ch (tables.getD t default).links (ch.mu.getD t [])).1.evaluate col +
    gatedVal col col (payloadForms ch (tables.getD t default).links (ch.mu.getD t [])).2

theorem gatedVal_eq (wt col : ℕ → E) (L : List (ℕ × Form)) :
    gatedVal wt col L = (L.map fun p ↦ wt p.1 * p.2.evaluate col).sum := rfl

/-- A table's blocks at a row: the payload under `ω` scaled by `s`, and `JUMP`'s identities. -/
theorem blocks_sum (ch : LinkChallenges) (t : ℕ) (s : E) (jump : List E) (col : ℕ → E) (eT ω : E) :
    ((tableBlocks ch t s (some jump)).map fun b ↦
      (if b.onEq then eT else ω) * (b.gate.map col).getD 1 * b.form.evaluate col).sum =
      s * ω * payVal ch t col +
        (if 0 < (tables.getD t default).nConstraints then
          eT * (jumpConstraintForm jump).evaluate col else 0) := by
  have h : tableBlocks ch t s (some jump) =
      (⟨false, none, ({} : Form).addScaled
          (payloadForms ch (tables.getD t default).links (ch.mu.getD t [])).1 s⟩ ::
        (payloadForms ch (tables.getD t default).links (ch.mu.getD t [])).2.map fun x ↦
          (⟨false, some x.1, ({} : Form).addScaled x.2 s⟩ : Block)) ++
      (if 0 < (tables.getD t default).nConstraints then
        [(⟨true, none, jumpConstraintForm jump⟩ : Block)] else []) := rfl
  rw [h, payVal, gatedVal_eq]
  generalize (payloadForms ch (tables.getD t default).links (ch.mu.getD t [])) = pf
  have hg : ((pf.2.map fun x ↦ (⟨false, some x.1, ({} : Form).addScaled x.2 s⟩ : Block)).map
      fun b ↦ (if b.onEq then eT else ω) * (b.gate.map col).getD 1 * b.form.evaluate col).sum =
      s * ω * (pf.2.map fun p ↦ col p.1 * p.2.evaluate col).sum := by
    rw [List.map_map, ← List.sum_map_mul_left]
    refine congrArg _ (List.map_congr_left fun p _ ↦ ?_)
    simp only [Function.comp_apply, Bool.false_eq_true, ↓reduceIte, Option.map_some,
      Option.getD_some, LeanVM.Prover.Complete.Form.evaluate_addScaled,
      LeanVM.Prover.Complete.Form.evaluate_empty]
    ring
  rw [List.map_append, List.sum_append, List.map_cons, List.sum_cons, hg]
  simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none, Option.getD_none,
    LeanVM.Prover.Complete.Form.evaluate_addScaled, LeanVM.Prover.Complete.Form.evaluate_empty]
  split
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
      Option.map_none, Option.getD_none]
    ring
  · simp only [List.map_nil, List.sum_nil]
    ring

theorem jump_only : ∀ t < nTables, 0 < (tables.getD t default).nConstraints → t = opJump := by
  intro t ht
  have : t < 6 := ht
  interval_cases t <;> decide

/-- **A table's base terms over its rows**: the payload at `eq(0, r)`, `JUMP`'s identities
vanishing on the honest rows. -/
theorem baseSum {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (hv : ValidExecution prog input ex)
    (inp : RowInputs) {t : ℕ} (ht : t < nTables)
    (hn : W.rows.getD t 0 ≤ 2 ^ W.layout.tableLogHeights.getD t 0) :
    ∑ u ∈ range (2 ^ W.layout.tableLogHeights.getD t 0), baseVal W inp t u =
      inp.eq0 * ∑ u ∈ range (W.rows.getD t 0),
        omegaU W inp t u * payVal inp.ch t (rowValue (W.tableCols t) u) := by
  have hb : ∀ u ∈ range (2 ^ W.layout.tableLogHeights.getD t 0), baseVal W inp t u =
      inp.eq0 * (omegaU W inp t u * payVal inp.ch t (rowValue (W.tableCols t) u)) := by
    intro u hu
    unfold baseVal
    dsimp only
    rw [blocks_sum]
    split
    · rename_i hc
      have h4 := jump_only t ht hc
      subst h4
      rw [jumpForm_witness hW hv _ (mem_range.mp hu)]
      ring
    · ring
  rw [sum_congr rfl hb, ← mul_sum, ← sum_range_add_sum_Ico _ hn,
    sum_eq_zero (s := Ico _ _) fun u hu ↦ by
      rw [omegaU_of_ge W inp t (mem_Ico.mp hu).1, zero_mul], add_zero]

/-- **The rows' claim** at the start: every table's sum over its rows. -/
theorem rowClaim_linkRowStart (W : Witness) (x : LinkProverPre) :
    rowClaim (linkRowStart W x) = ∑ t ∈ range nTables,
      cubeSum (2 ^ W.layout.tableLogHeights.getD t 0)
        (rowProds W (linkRowInputs W x) t (pointerStarts.getD t 0)).1 := by
  unfold rowClaim linkRowStart
  rw [Array.toList_ofFn, List.map_ofFn, List.sum_ofFn, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  simp [rowPart]

/-- **An executed row's share agrees** between the row side and the index side, the index
side's constants `c3, c5, c6, c7, c10, c12` being the rows' `Y`, `X_ω`, `eq(ζ, r)`, the shift,
`M_1` and `P_fp`. -/
theorem share_eq (W : Witness) (inp : RowInputs) (r : List E) {t : ℕ} (ht : t < nTables) (u cyc : ℕ)
    (hS : ∀ a ∈ (tables.getD t default).links.memory,
      gateOf (rowValue (W.tableCols t) u) a ≠ 0 →
        W.chunks.shifted (ptrAt W t a.pointer u) a.shift = some (ptrAt W t a.pointer u + a.shift))
    (hcyc : ptrAt W t (tables.getD t default).links.stateLink.cycle u = cyc) :
    ((tables.getD t default).links.pointers.zipIdx.map fun pk ↦
        ptrVal W inp t r (ptrAt W t pk.1 u) u pk.1 pk.2).sum +
      inp.eq0 * (omegaU W inp t u * payVal inp.ch t (rowValue (W.tableCols t) u)) =
    inp.eqZeta * (LeanVM.Protocol.Hotwire.eqAt r cyc *
        (stateValues inp.ch (tables.getD t default).links (rowValue (W.tableCols t) u)).1) +
      inp.shiftZeta * (LeanVM.Protocol.Hotwire.eqAt r cyc *
        (stateValues inp.ch (tables.getD t default).links (rowValue (W.tableCols t) u)).2) +
      inp.ch.etaMem * inp.yMem *
        (((tables.getD t default).links.memory.zip (inp.ch.mu.getD t [])).map fun am ↦
          gateOf (rowValue (W.tableCols t) u) am.1 * (am.2 * omegaU W inp t u) *
            LeanVM.Protocol.Hotwire.eqAt r (ptrAt W t am.1.pointer u + am.1.shift)).sum +
      inp.xBc * (omegaU W inp t u * LeanVM.Protocol.Hotwire.eqAt r
        (ptrAt W t (tables.getD t default).links.bytecodeLink.pointer u)) +
      inp.eq0 * (omegaU W inp t u * payVal inp.ch t (rowValue (W.tableCols t) u)) +
      inp.ch.etaMem * inp.m1 *
        ((wordReads (tables.getD t default).links (inp.ch.mu.getD t []) (inp.ch.gammaMem.getD 1 0)).map
          fun pf ↦ pf.2.evaluate (rowValue (W.tableCols t) u) * omegaU W inp t u *
            LeanVM.Protocol.Hotwire.eqAt r (ptrAt W t pf.1 u)).sum +
      inp.pFp * (omegaU W inp t u * rowValue (W.tableCols t) u
        (tables.getD t default).links.stateLink.fp * LeanVM.Protocol.Hotwire.eqAt r
          (ptrAt W t (tables.getD t default).links.bytecodeLink.pointer u)) := by
  rw [ptrSum_eq W inp r ht u, hcyc]
  simp only [eqAt_keccak]
  have hacc : (((tables.getD t default).links.memory.zip (inp.ch.mu.getD t [])).map fun am ↦
      inp.ch.etaMem * inp.yMem * am.2 * omegaU W inp t u * gateOf (rowValue (W.tableCols t) u) am.1 *
        shEq W.chunks r (ptrAt W t am.1.pointer u) am.1.shift).sum =
      inp.ch.etaMem * inp.yMem *
        (((tables.getD t default).links.memory.zip (inp.ch.mu.getD t [])).map fun am ↦
          gateOf (rowValue (W.tableCols t) u) am.1 * (am.2 * omegaU W inp t u) *
            LeanVM.Protocol.Hotwire.eqAt r (ptrAt W t am.1.pointer u + am.1.shift)).sum := by
    rw [← List.sum_map_mul_left]
    refine congrArg _ (List.map_congr_left fun am ham ↦ ?_)
    by_cases hg : gateOf (rowValue (W.tableCols t) u) am.1 = 0
    · rw [hg]; ring
    · have hsh := hS am.1 (List.of_mem_zip ham).1 hg
      unfold shEq
      rw [hsh]
      dsimp only
      rw [eqAt_keccak]
      ring
  have hsum : ((wordReads (tables.getD t default).links (inp.ch.mu.getD t []) (inp.ch.gammaMem.getD 1 0)).map
      fun pf ↦ pf.2.evaluate (rowValue (W.tableCols t) u) * omegaU W inp t u *
        LeanVM.Protocol.Hotwire.eqAt r (ptrAt W t pf.1 u)).sum =
      omegaU W inp t u * gatedVal (fun p ↦ LeanVM.Protocol.Hotwire.eqAt r (ptrAt W t p u))
        (rowValue (W.tableCols t) u)
        (wordReads (tables.getD t default).links (inp.ch.mu.getD t []) (inp.ch.gammaMem.getD 1 0)) := by
    rw [gatedVal_eq, ← List.sum_map_mul_left]
    refine congrArg _ (List.map_congr_left fun pf _ ↦ ?_)
    ring
  rw [hacc, hsum, wordReads_val, wordReads_val]
  ring

theorem shifts_le : ∀ t < nTables, ∀ a ∈ (tables.getD t default).links.memory,
    a.shift ≤ tables.foldl (fun m t ↦ max m t.links.maxShift) 0 := by
  decide +kernel

/-- **The row identity on the honest witness**: the index side's value at `r` is the rows'
claim. -/
theorem rowIdentity_of {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog} {ρ : ℕ}
    {W : Witness} (hA : Admitted prog input ex ρ W) : RowIdentity W := by
  intro y x hp
  have hW := hA.witness
  have hv := hA.valid
  have hS := scatterOK_of hA
  obtain ⟨-, hch, -, -⟩ := linkSizes hW
  have hc := chunkFacts_of hch
  have hok := (chunksOK_new hch).1
  have hr : x.r.length = W.chunks.width := hp.rlen
  have hT : Tabs W.chunks.width (indexProds W x.ch) := by
    rw [hp.ch]; exact indexTabs_of W _ _ hp.drawn
  obtain ⟨hrows, hcols, hl, -⟩ := witness_steps hW hv
  have hlm : W.layout.logMemory = ex.logMemorySize := (buildLayout_spec hl).1
  have hL : W.layout.logMemory ≤ W.chunks.width := hlm ▸ (width_witness hW hv).2.2.2.1
  have hm0 : (W.cols.getD memory0 #[]).size = 2 ^ W.layout.logMemory := by
    rw [hcols, colsOf_getD _ _ _ (by decide), hlm]; simp
  have hm1 : (W.cols.getD memory1 #[]).size = 2 ^ W.layout.logMemory := by
    rw [hcols, colsOf_getD _ _ _ (by decide), hlm]; simp [memory0, memory1]
  have hfield : ∀ f, x.index.at f = idxM W x.ch x.r f := fun f ↦ by rw [hp.index, at_index]
  have hm1' : (linkRowInputs W x).m1 = idxM W x.ch x.r 10 := by
    rw [idxM_words W x.ch x.r hr hL hm0 hm1 hT]; exact hp.m1eq
  have heq0 : (linkRowInputs W x).eq0 = LeanVM.Protocol.Hotwire.eqAt x.r 0 := by
    show prodE ((x.r.drop (min 0 W.chunks.width)).map (1 + ·)) = _
    rw [eqAt_zero_prodE]; simp
  have hrow : ∀ t ∈ range nTables, cubeSum (2 ^ W.layout.tableLogHeights.getD t 0)
      (rowProds W (linkRowInputs W x) t (pointerStarts.getD t 0)).1 =
      ∑ u ∈ range (W.rows.getD t 0),
        (idxM W x.ch x.r 6 * (LeanVM.Protocol.Hotwire.eqAt x.r (rowCycle (traceSteps ex) t u) *
            (stateValues x.ch (tables.getD t default).links (rowValue (W.tableCols t) u)).1) +
          idxM W x.ch x.r 7 * (LeanVM.Protocol.Hotwire.eqAt x.r (rowCycle (traceSteps ex) t u) *
            (stateValues x.ch (tables.getD t default).links (rowValue (W.tableCols t) u)).2) +
          x.ch.etaMem * idxM W x.ch x.r 3 *
            (((tables.getD t default).links.memory.zip (x.ch.mu.getD t [])).map fun am ↦
              gateOf (rowValue (W.tableCols t) u) am.1 * (am.2 * omegaU W (linkRowInputs W x) t u) *
                LeanVM.Protocol.Hotwire.eqAt x.r (ptrAt W t am.1.pointer u + am.1.shift)).sum +
          idxM W x.ch x.r 5 * (omegaU W (linkRowInputs W x) t u * LeanVM.Protocol.Hotwire.eqAt x.r
            (ptrAt W t (tables.getD t default).links.bytecodeLink.pointer u)) +
          LeanVM.Protocol.Hotwire.eqAt x.r 0 * (omegaU W (linkRowInputs W x) t u *
            payVal x.ch t (rowValue (W.tableCols t) u)) +
          x.ch.etaMem * idxM W x.ch x.r 10 *
            ((wordReads (tables.getD t default).links (x.ch.mu.getD t []) (x.ch.gammaMem.getD 1 0)).map
              fun pf ↦ pf.2.evaluate (rowValue (W.tableCols t) u) * omegaU W (linkRowInputs W x) t u *
                LeanVM.Protocol.Hotwire.eqAt x.r (ptrAt W t pf.1 u)).sum +
          idxM W x.ch x.r 12 * (omegaU W (linkRowInputs W x) t u * rowValue (W.tableCols t) u
            (tables.getD t default).links.stateLink.fp * LeanVM.Protocol.Hotwire.eqAt x.r
              (ptrAt W t (tables.getD t default).links.bytecodeLink.pointer u))) := by
    intro t ht
    have ht' := mem_range.mp ht
    have hn : W.rows.getD t 0 ≤ 2 ^ W.layout.tableLogHeights.getD t 0 := rows_le_height hl ht'
    obtain ⟨hwid, hptr⟩ := tables_pointers t ht'
    have hsize : ∀ c < (tables.getD t default).width,
        ((W.tableCols t).getD c #[]).size = 2 ^ W.layout.tableLogHeights.getD t 0 :=
      fun c hc' ↦ size_tableCols_getD hW ht' (by rw [← hwid]; exact hc')
    have hoh : ∀ p ∈ (tables.getD t default).links.pointers,
        OneHotWords W.chunks ((W.tableCols t).getD p #[]) (W.rows.getD t 0)
          (fun u ↦ ptrAt W t p u) := by
      intro p hp' u hu
      obtain ⟨σ, hσ, hword⟩ := ptr_honest hA ht' hu hp'
      dsimp only
      rw [ptrAt_of hok hσ hword]
      exact ⟨hσ, hword⟩
    rw [cubeSum_rowProds W (linkRowInputs W x) t _ (fun p u ↦ ptrAt W t p u) ht' hc hok hr rfl
      (shifts_le t ht') hn hsize hoh, baseSum hW hv _ ht' hn, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun u hu ↦ ?_
    have hu' := mem_range.mp hu
    obtain ⟨hcσ, hcw⟩ := cycle_oneHot hW hv ht' u hu'
    rw [share_eq W (linkRowInputs W x) x.r ht' u (rowCycle (traceSteps ex) t u)
      (fun a ha hg ↦ (hS.2 t ht' u hu' a ha hg).1) (ptrAt_of hok hcσ hcw)]
    rw [show (linkRowInputs W x).eqZeta = x.index.at 6 from rfl,
      show (linkRowInputs W x).shiftZeta = x.index.at 7 from rfl,
      show (linkRowInputs W x).yMem = x.index.at 3 from rfl,
      show (linkRowInputs W x).xBc = x.index.at 5 from rfl,
      show (linkRowInputs W x).pFp = x.index.at 12 from rfl,
      hfield, hfield, hfield, hfield, hfield, hm1', heq0]
    rfl
  rw [hp.index, index_value, rowClaim_linkRowStart, sum_congr rfl hrow,
    idxM_state W x.ch x.r hT hr hW hv (k := 0) (by norm_num),
    idxM_state W x.ch x.r hT hr hW hv (k := 1) (by norm_num),
    idxM_mem W x.ch x.r hT hr hS, idxM_bc W x.ch x.r hT hr hS, idxM_pay W x.ch x.r hT hr,
    idxM_word W x.ch x.r hT hr hS, idxM_fp W x.ch x.r hT hr hS]
  simp only [mul_sum, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun t _ ↦ sum_congr rfl fun u _ ↦ ?_
  have hch' : (linkRowInputs W x).ch = x.ch := rfl
  simp only [stateWeight, omegaRow, colAt, omegaU, payVal, ↓reduceIte, one_ne_zero, hch']
  ring

end LeanVM.Prover.Complete.RowId

namespace LeanVM.Prover.Complete

open LeanVM.Prover

/-- **The row identity on the honest witness** (`RowId.rowIdentity_of`). -/
theorem rowIdentity_of {prog : LeanVM.Semantics.LeanIsaProgram} {input : LeanVM.Semantics.PublicInput}
    {ex : LeanVM.Semantics.Execution prog} {ρ : ℕ} {W : Witness} (hA : Admitted prog input ex ρ W) :
    RowIdentity W :=
  RowId.rowIdentity_of hA

end LeanVM.Prover.Complete

end
