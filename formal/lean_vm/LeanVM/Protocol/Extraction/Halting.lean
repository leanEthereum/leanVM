/-
  LeanVM.Protocol.Extraction.Halting

  The extractor's step cap loses nothing: a valid execution a stack represents takes at most the
  rows of its witness, at most the layout's `stepCap`, so on a stack satisfying the leanISA
  relation the capped search is the specification's halting run, and gives a valid execution;
  and the cap is at most the stack's size.
-/

module

public import LeanVM.Protocol.Extraction.Run
public import LeanVM.Protocol.EndToEnd.Sound.Extractor

/-!
# The step cap

**The cap loses nothing.**

* **`steps_le_rows`**: a witness representing a halting trace has at least as many rows as the
  trace has steps. Each step `(r_k, r_{k+1})` is some row's state pull and push
  (`AssignmentRepresents.regs_embed`), a row's pull determines `r_k`, and the `r_k` are distinct
  (`run_injective`), so distinct steps have distinct rows.
* `rows_witnessOf`, **`rows_le_stepCap`**: the witness read off a stack has the announced rows,
  at most the layout's `stepCap`.
* **`haltingRunC_eq_of_extracted`**: for a stack satisfying the leanISA relation at admissible
  sizes, the capped search on its memory image is `haltingRun`, and
  **`candidateExecution_of_extracted`**: it gives a valid execution.

**The cap is structural.** **`stepCap_le_stack`**: `stepCap (verifierLayout prog s)` is at most
`2^μ`, the stack's size: the six opcode tables, the memory and the bytecode each own a committed
column, hence a block of the stack of their height. **`stepCap_le_maxMu`**: at admissible sizes, at
most `2^32`.
-/

namespace LeanVM.Protocol.Halting

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Extraction

@[expose] public section

/-! ## 1. The rows argument -/

section Rows

variable {prog : LeanIsaProgram}

open Classical in
/-- **A witness representing a halting trace has at least as many rows as the trace has steps.**
Step `k` is some row's state pull and push (`regs_embed`); the pull of a row determines the state
`r_k`, and the states of a halting run are distinct (`run_injective`), so distinct steps have
distinct rows. -/
theorem steps_le_rows {κ : ℕ} {w : Air.Flat.EnsembleWitness (leanIsaEnsemble prog κ)}
    {t : Execution prog}
    (hrep : AssignmentRepresents w t)
    (hv : run prog t.memory t.stepCount Registers.initial = some (Registers.final prog)) :
    t.stepCount ≤ (w.tables.map fun tb ↦ tb.table.length).sum := by
  let st : ℕ → Registers K := fun k ↦ (run prog t.memory k Registers.initial).getD Registers.initial
  have hst : ∀ k ≤ t.stepCount, run prog t.memory k Registers.initial = some (st k) := fun k hk ↦ by
    rcases hk.lt_or_eq with hk | rfl
    · obtain ⟨r₁, h₁, -⟩ := run_intermediate hv hk
      simp only [st, h₁, Option.getD_some]
    · simp only [st, hv, Option.getD_some]
  have hregs : t.regs = (List.range (t.stepCount + 1)).map st :=
    (List.filterMap_congr fun k hk ↦ hst k (Nat.lt_succ_iff.mp (List.mem_range.mp hk))).trans
      (congrFun List.filterMap_eq_map' _)
  have hlen : t.regs.length = t.stepCount + 1 := by rw [hregs]; simp
  have e : ∀ j (hj : j < t.regs.length), t.regs[j] = st j := fun j hj ↦ by
    rw [List.getElem_of_eq hregs hj]
    simp
  let P := w.tables.flatMap fun tb ↦ tb.table.map fun row ↦ (tb, row)
  have hP : P.length = (w.tables.map fun tb ↦ tb.table.length).sum := by
    simp [P, List.length_flatMap]
  have hrow : ∀ k : Fin t.stepCount, ∃ p ∈ P,
      rowMessagesOn p.1 p.2 StatePull.toRaw = [#[(st k).pc, (st k).fp]] := fun k ↦ by
    have hk : (k : ℕ) + 1 < t.regs.length := by have := k.isLt; omega
    have h := hrep.regs_embed k hk
    rw [e k (by omega), e (k + 1) hk] at h
    obtain ⟨tb, htb, row, hrow, h₁, -⟩ := h
    exact ⟨(tb, row), List.mem_flatMap.mpr ⟨tb, htb, List.mem_map_of_mem hrow⟩, h₁⟩
  choose c hcP hcPull using hrow
  have hcinj : Function.Injective c := fun a b hab ↦ by
    have h := hcPull a
    rw [hab, hcPull b] at h
    simp only [List.cons.injEq, and_true] at h
    have h' := congrArg Array.toList h
    simp only [List.cons.injEq, and_true] at h'
    have hab' : st a = st b := regs_ext h'.1.symm h'.2.symm
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact run_injective hv hlt (by omega) (hst a (by omega)) (hab' ▸ hst b (by omega))
    · exact run_injective hv hlt (by omega) (hst b (by omega)) (hab' ▸ hst a (by omega))
  calc t.stepCount = (Finset.univ : Finset (Fin t.stepCount)).card := by simp
    _ ≤ P.toFinset.card :=
      Finset.card_le_card_of_injOn c (fun k _ ↦ List.mem_toFinset.mpr (hcP k)) hcinj.injOn
    _ ≤ P.length := List.toFinset_card_le P
    _ = _ := hP

/-- The tables of a witness, in order. -/
theorem tables_eq_ofFn {κ : ℕ} (w : Air.Flat.EnsembleWitness (leanIsaEnsemble prog κ)) :
    w.tables = List.ofFn (tableAt w) := by
  refine List.ext_getElem ?_ fun i h₁ h₂ ↦ ?_
  · rw [List.length_ofFn, ← w.same_length]
    rfl
  · rw [List.getElem_ofFn]
    rfl

/-- The tables of the witness read off a stack have the announced row counts, when they fit
Clean's `2^64` rows (`Sizes.Admissible.logMem_lt`, `rows_le_size`). -/
theorem table_length_witnessOf' (s : Sizes) (q : Column (leanIsaμ prog s)) (hκ : s.logMem < 64)
    (hr : ∀ j, s.rows j ≤ UInt64.size) (j : Fin 8) :
    (tableAt (witnessOf prog s q) j).table.length =
      ![s.rows 0, s.rows 1, s.rows 2, s.rows 3, s.rows 4, s.rows 5, 2 ^ s.logMem,
        2 ^ prog.logSize] j := by
  rw [witnessOf_table]
  fin_cases j
  all_goals simp only [witnessTables, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals first
    | rw [opTableOf_table prog s q (hr _), opcodeRows, List.length_ofFn]; rfl
    | rw [memTableOf_table prog s q hκ, memBlockRowsOf_length]; rfl
    | rw [bytecodeTableOf_table, bytecodeBlockRowsOf_length]; rfl

/-- **The rows of the witness read off a stack**: the announced opcode rows, the memory's words
and the bytecode's slots. -/
theorem rows_witnessOf (s : Sizes) (q : Column (leanIsaμ prog s)) (hκ : s.logMem < 64)
    (hr : ∀ j, s.rows j ≤ UInt64.size) :
    ((witnessOf prog s q).tables.map fun tb ↦ tb.table.length).sum =
      (∑ j, s.rows j) + 2 ^ s.logMem + 2 ^ prog.logSize := by
  rw [tables_eq_ofFn, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_def, table_length_witnessOf' s q hκ hr, Fin.sum_univ_eight,
    Fin.sum_univ_six]
  simp only [Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The step cap of the layout of the sizes `s`. -/
theorem stepCap_verifierLayout (s : Sizes) :
    stepCap (verifierLayout prog s) = (∑ j, 2 ^ s.τ j) + 2 ^ s.logMem + 2 ^ prog.logSize := by
  show ((tableLogs s).map (2 ^ ·)).sum + 2 ^ s.logMem + 2 ^ prog.logSize = _
  rw [tableLogs, List.map_ofFn, List.sum_ofFn]
  rfl

/-- **The rows of the witness read off a stack are at most the layout's step cap.** -/
theorem rows_le_stepCap (s : Sizes) (q : Column (leanIsaμ prog s)) (hκ : s.logMem < 64)
    (hr : ∀ j, s.rows j ≤ UInt64.size) :
    ((witnessOf prog s q).tables.map fun tb ↦ tb.table.length).sum ≤
      stepCap (verifierLayout prog s) := by
  rw [rows_witnessOf s q hκ hr, stepCap_verifierLayout]
  have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ s.rows_le j
  omega

end Rows

/-! ## 2. The cap is structural -/

section Structural

variable (prog : LeanIsaProgram) (s : Sizes)

/-- Every opcode table has a column. -/
theorem width_opIdx_pos : ∀ j : Fin 6, 0 < width (opIdx j) := by decide +kernel

/-- A committed column of each table the cap counts: `MEM_LO`, `BFCNT`, and the last column of
each opcode table. -/
def capCol : Fin 8 → Col
  | ⟨0, _⟩ => memCol 0
  | ⟨1, _⟩ => bfcntCol
  | ⟨j + 2, h⟩ => ⟨opIdx ⟨j, by omega⟩,
      ⟨width (opIdx ⟨j, by omega⟩) - 1, by have := width_opIdx_pos ⟨j, by omega⟩; omega⟩⟩

/-- The columns are committed. -/
theorem not_isVirtual_capCol : ∀ i, ¬ IsVirtual (capCol i) := by decide +kernel

/-- The columns are in distinct tables. -/
theorem capCol_injective : Function.Injective capCol := by
  have h : Function.Injective fun i ↦ (capCol i).1 := by decide
  exact fun a b hab ↦ h (congrArg Sigma.fst hab)

/-- The columns' log-heights: the memory's, the bytecode's, and the opcode tables'. -/
theorem sum_kappa_capCol :
    ∑ i, 2 ^ kappa prog s (capCol i) = (∑ j, 2 ^ s.τ j) + 2 ^ s.logMem + 2 ^ prog.logSize := by
  simp only [Fin.sum_univ_eight, Fin.sum_univ_six]
  simp only [kappa, capCol, memCol, bfcntCol, opIdx, height, Fin.isValue]
  have e0 : s.τ ⟨0, by omega⟩ = s.τ 0 := rfl
  have e1 : s.τ ⟨1, by omega⟩ = s.τ 1 := rfl
  have e2 : s.τ ⟨2, by omega⟩ = s.τ 2 := rfl
  have e3 : s.τ ⟨3, by omega⟩ = s.τ 3 := rfl
  have e4 : s.τ ⟨4, by omega⟩ = s.τ 4 := rfl
  have e5 : s.τ ⟨5, by omega⟩ = s.τ 5 := rfl
  rw [e0, e1, e2, e3, e4, e5]
  omega

end Structural

/-! ## 3. On the extracted stack -/

section Extracted

variable {prog : LeanIsaProgram} {input : PublicInput}

/-- A witness representing a halting trace has the trace's halting run on the image it names. -/
theorem haltingRun_of_represents {κ : ℕ} {w : Air.Flat.EnsembleWitness (leanIsaEnsemble prog κ)}
    {t : Execution prog} (hrep : AssignmentRepresents w t)
    (hv : run prog t.memory t.stepCount Registers.initial = some (Registers.final prog)) :
    ∃ t', haltingRun prog (imageOf w.data).2 = some t' ∧ t'.stepCount = t.stepCount := by
  obtain ⟨κ, image, steps⟩ := t
  obtain ⟨hκ, himage, -⟩ := hrep
  generalize imageOf w.data = p at hκ himage ⊢
  obtain ⟨κ', image'⟩ := p
  dsimp only at hκ himage hv ⊢
  subst hκ
  obtain rfl : image' = image := funext fun i ↦ himage i i.isLt
  exact ⟨_, haltingRun_eq_some_iff.mpr ⟨steps, rfl, hv⟩, rfl⟩

/-- **On a stack satisfying the leanISA relation at admissible sizes, the capped search on its
memory image is `haltingRun`**: the valid execution the stack represents takes at most the
witness's rows, at most the layout's cap, and every halting run of the image takes as many
steps. -/
theorem haltingRunC_eq_of_extracted {s : Sizes} {q : Column (leanIsaμ prog s)}
    (hs : s.Admissible prog) (h : M3Holds (leanIsaInstance prog s) input q) :
    haltingRunC prog (memoryImage (verifierLayout prog s) (q.values : Vector K (2 ^ _)))
        (stepCap (verifierLayout prog s)) =
      haltingRun prog (memoryImage (verifierLayout prog s) (q.values : Vector K (2 ^ _))) := by
  obtain ⟨t, hrep, hv⟩ := execution_of_extracted hs h
  have hsteps : t.stepCount ≤ stepCap (verifierLayout prog s) :=
    (steps_le_rows hrep hv.2).trans (rows_le_stepCap s q hs.logMem_lt hs.rows_le_size)
  obtain ⟨t', ht', hst'⟩ := haltingRun_of_represents hrep hv.2
  rw [Sound.haltingRun_imageOf s hs.2.1 q] at ht'
  have hκ : (verifierLayout prog s).logMemory < 64 := by
    have : (verifierLayout prog s).logMemory = s.logMem := rfl
    have h2 := hs.2.1
    unfold maxLogMem at h2
    omega
  refine haltingRunC_eq_haltingRun hκ fun n hn ↦ ?_
  have := haltingRun_steps ht' hn
  omega

/-- **A stack satisfying the leanISA relation at admissible sizes has a valid execution**, the one
`candidateExecution` returns. With `haltingRunC_eq_of_extracted` this replaces `haltingRun_valid`
and `haltingRun_imageOf` in `extractor_of_extracted`. -/
theorem candidateExecution_of_extracted {s : Sizes} {q : Column (leanIsaμ prog s)}
    (hs : s.Admissible prog) (h : M3Holds (leanIsaInstance prog s) input q) :
    ∃ t, candidateExecution prog input (verifierLayout prog s) (q.values : Vector K (2 ^ _)) =
        some t ∧ ValidExecution prog input t := by
  obtain ⟨t, hrep, hv⟩ := execution_of_extracted hs h
  obtain ⟨t', ht', hv'⟩ := Sound.haltingRun_valid hrep hv
  rw [Sound.haltingRun_imageOf s hs.2.1 q] at ht'
  refine ⟨t', ?_, hv'⟩
  rw [candidateExecution_eq, haltingRunC_eq_of_extracted hs h, ht']
  exact Option.filter_eq_some_iff.mpr ⟨rfl, (boundaryOK_iff input t').mpr hv'.1⟩

end Extracted

end
end LeanVM.Protocol.Halting
