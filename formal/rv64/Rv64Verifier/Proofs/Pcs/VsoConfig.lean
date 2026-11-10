import Rv64Verifier.Model.Whir
import Rv64Verifier.Proofs.Rodata

/-!
# The opening's configuration, as the image derives it

`derive_config` inlined into `verify_stacked_opening`. `whir_queries` reads `WHIR_QUERIES` from
`.rodata`: the table of slices (pointer, length) at `0xa0000948`, a row of fourteen per rate, each
slice's words elsewhere in `.rodata` (`RodataOk.queries`). The ladder's loop is compiled to a count:
past `log_n >= 15` its first iteration always runs and folds four, as every later one does, so the
image pushes `(log_n - 12) / 4 + 1` folds of four and rates three apart (`configLoop_eq`).
-/

namespace Rv64Verifier.Model.Pcs
open RiscvZkvm.Rv64

/-! ## `WHIR_QUERIES` in `.rodata` -/

/-- The `.rodata` word at `a`, if there is one. -/
def rodataWord? (a : Word) : Option Word := (rodataWords.find? fun p ↦ p.1 == a).map Prod.snd

theorem _root_.Rv64Verifier.RodataOk.word? {s : MachineState} (h : RodataOk s) {a v : Word}
    (hv : rodataWord? a = some v) : s.getMem a = v := by
  unfold rodataWord? at hv
  cases hf : rodataWords.find? (fun p ↦ p.1 == a) with
  | none => rw [hf] at hv; cases hv
  | some p =>
    rw [hf] at hv
    cases hv
    have hm := List.mem_of_find?_eq_some hf
    have he := List.find?_some hf
    simp only [beq_iff_eq] at he
    rw [← he]
    exact h p hm

/-- The slice `WHIR_QUERIES[r][n]`, a pointer and a length. -/
@[rv_addr] def queriesEntry (r n : ℕ) : Word := 0xa0000948 + BitVec.ofNat 64 (224 * r + 16 * n)

/-- `n` words from `p`, as naturals. -/
def natsAt (s : MachineState) (p : Word) (n : ℕ) : List ℕ :=
  (List.range n).map fun i ↦ (s.getMem (p + BitVec.ofNat 64 (8 * i))).toNat

/-- The slice at `WHIR_QUERIES[r][n]` holds the table's row, within `.rodata`. -/
def queriesEntryOk (r n : ℕ) : Bool :=
  match rodataWord? (queriesEntry r n), rodataWord? (queriesEntry r n + 8) with
  | some p, some l =>
    let row := (whirQueriesTable.getD r []).getD n []
    l.toNat == row.length && p.toNat % 8 == 0 && 0xa0000000 ≤ p.toNat &&
      p.toNat + 8 * row.length ≤ 0xa0000f30 &&
      (List.range row.length).all fun i ↦
        rodataWord? (p + BitVec.ofNat 64 (8 * i)) == some (BitVec.ofNat 64 (row.getD i 0))
  | _, _ => false

theorem queriesEntryOk_all : ∀ r < 4, ∀ n < 14, queriesEntryOk r n = true := by
  decide +kernel

theorem natsAt_eq {s : MachineState} (h : RodataOk s) {p : Word} {row : List ℕ}
    (hrow : ∀ x ∈ row, x < 2 ^ 64)
    (hall : ((List.range row.length).all fun i ↦
      rodataWord? (p + BitVec.ofNat 64 (8 * i)) == some (BitVec.ofNat 64 (row.getD i 0))) = true) :
    natsAt s p row.length = row := by
  apply List.ext_getElem (by simp [natsAt])
  intro i hi _
  simp only [natsAt, List.getElem_map, List.getElem_range]
  have := List.all_eq_true.mp hall i (List.mem_range.mpr (by simpa [natsAt] using hi))
  simp only [beq_iff_eq] at this
  rw [h.word? this, BitVec.toNat_ofNat, List.getD_eq_getElem _ _ (by simpa [natsAt] using hi)]
  exact Nat.mod_eq_of_lt (hrow _ (List.getElem_mem _))

theorem whirQueriesTable_lt : ∀ r ∈ whirQueriesTable, ∀ row ∈ r, ∀ x ∈ row, x < 2 ^ 64 := by
  decide +kernel

/-- **`whir_queries` as the image reads it**: in the window, the slice the table's entry points
to, its words in `.rodata`. -/
theorem RodataOk.queries {s : MachineState} (h : RodataOk s) {r n : ℕ} (hr : 1 ≤ r ∧ r ≤ 4)
    (hn : 15 ≤ n ∧ n ≤ 28) :
    let p := s.getMem (queriesEntry (r - 1) (n - 15))
    let l := (s.getMem (queriesEntry (r - 1) (n - 15) + 8)).toNat
    whirQueriesRust n r = some (natsAt s p l) ∧ p.toNat % 8 = 0 ∧ 0xa0000000 ≤ p.toNat ∧
      p.toNat + 8 * l ≤ 0xa0000f30 := by
  intro p l
  have hok := queriesEntryOk_all (r - 1) (by omega) (n - 15) (by omega)
  unfold queriesEntryOk at hok
  split at hok
  swap
  · cases hok
  rename_i p' l' hp hl
  have hp' := h.word? hp
  have hl' := h.word? hl
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hlen, hal⟩, hlo⟩, hhi⟩, hall⟩ := hok
  have hpp : p = p' := hp'
  have hll : l = ((whirQueriesTable.getD (r - 1) []).getD (n - 15) []).length := by
    simp only [l, hl', hlen]
  have hrow : ∀ x ∈ (whirQueriesTable.getD (r - 1) []).getD (n - 15) [], x < 2 ^ 64 := by
    intro x hx
    have h1 : r - 1 < whirQueriesTable.length := by
      have : whirQueriesTable.length = 4 := rfl
      omega
    have h2 : n - 15 < (whirQueriesTable[r - 1]'h1).length := by
      have : ∀ row ∈ whirQueriesTable, row.length = 14 := by decide +kernel
      rw [this _ (List.getElem_mem h1)]
      omega
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at hx
    exact whirQueriesTable_lt _ (List.getElem_mem h1) _ (List.getElem_mem h2) x hx
  refine ⟨?_, hpp ▸ hal, hpp ▸ hlo, hpp ▸ hll ▸ hhi⟩
  rw [hpp, hll, natsAt_eq h hrow hall]
  unfold whirQueriesRust checkedSub
  have h1 : r - 1 < whirQueriesTable.length := by
    have : whirQueriesTable.length = 4 := rfl
    omega
  have h2 : n - 15 < (whirQueriesTable[r - 1]'h1).length := by
    have : ∀ row ∈ whirQueriesTable, row.length = 14 := by decide +kernel
    rw [this _ (List.getElem_mem h1)]
    omega
  simp only [show 1 ≤ r from hr.1, ite_true, minStackedLog, Option.bind_eq_bind, Option.bind_some,
    List.getElem?_eq_getElem h1, List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
  simp only [hn.1, ite_true, Option.bind_some]
  exact List.getElem?_eq_getElem h2

/-! ## The ladder -/

/-- The folds after `k` iterations: the initial six, then fours. -/
def ladderFolds (k : ℕ) : List ℕ := 6 :: List.replicate k 4

/-- The rates after `k` iterations: three apart after the first. -/
def ladderRates (r k : ℕ) : List ℕ := r :: (List.range k).map fun i ↦ r + 3 * (i + 1)

theorem ladderFolds_succ (k : ℕ) : ladderFolds k ++ [4] = ladderFolds (k + 1) := by
  simp [ladderFolds, List.replicate_succ']

theorem ladderRates_succ (r k : ℕ) :
    ladderRates r k ++ [r + 3 * (k + 1)] = ladderRates r (k + 1) := by
  simp [ladderRates, List.range_succ]

theorem ladderFolds_last (k : ℕ) (hk : 1 ≤ k) : (ladderFolds k).getLastD 0 = 4 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [← ladderFolds_succ j, List.getLastD_eq_getLast?, List.getLast?_concat]
  rfl

theorem ladderRates_last (r k : ℕ) (hk : 1 ≤ k) : (ladderRates r k).getLastD 0 = r + 3 * k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [← ladderRates_succ r j, List.getLastD_eq_getLast?, List.getLast?_concat]
  rfl

theorem configLoop_ladder (r : ℕ) : ∀ (m j fuel e : ℕ), 1 ≤ j → 2 ≤ e → e ≤ 5 → m ≤ fuel →
    configLoop fuel (4 * m + e) (ladderFolds j) (ladderRates r j) =
      (ladderFolds (j + m), ladderRates r (j + m))
  | 0, j, fuel, e, _, _, he5, _ => by
    cases fuel with
    | zero => rfl
    | succ f =>
      rw [configLoop, ite_eq_right (by simp only [residualMaxLogRust]; omega)]
      rfl
  | m + 1, j, fuel, e, hj, he2, he5, hm => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [configLoop, ite_eq_left (by simp only [residualMaxLogRust]; omega)]
    have hlen : (ladderFolds j).length ≠ 1 := by simp [ladderFolds]; omega
    simp only [hlen, ite_false, ladderFolds_last j hj, ladderRates_last r j hj,
      rsDomainSubsequentReductionFactor, subsequentFoldingFactor]
    rw [show min 4 (4 * (m + 1) + e) = 4 by omega, show 4 * (m + 1) + e - 4 = 4 * m + e by omega,
      show r + 3 * j + 4 - 1 = r + 3 * (j + 1) by omega, ladderFolds_succ, ladderRates_succ,
      configLoop_ladder r m (j + 1) f e (by omega) he2 he5 (by omega)]
    rw [show j + 1 + m = j + (m + 1) by omega]

/-- **`derive_config`'s loop, as the image runs it.** -/
theorem configLoop_eq (n r : ℕ) (hn : 15 ≤ n) :
    configLoop n (n - initialFoldingFactor) [initialFoldingFactor] [r] =
      (ladderFolds ((n - 12) / 4 + 1), ladderRates r ((n - 12) / 4 + 1)) := by
  obtain ⟨f, hf⟩ : ∃ f, n = f + 1 := ⟨n - 1, by omega⟩
  rw [hf, configLoop, ite_eq_left (by simp only [residualMaxLogRust, initialFoldingFactor]; omega)]
  simp only [List.length_singleton, ite_true, initialFoldingFactor,
    rsDomainInitialReductionFactor, subsequentFoldingFactor]
  have h := configLoop_ladder r ((f + 1 - 12) / 4) 1 f ((f + 1 - 10) - 4 * ((f + 1 - 12) / 4))
    (le_refl _) (by omega) (by omega) (by omega)
  rw [show 4 * ((f + 1 - 12) / 4) + (f + 1 - 10 - 4 * ((f + 1 - 12) / 4)) = f + 1 - 6 - 4 by omega,
    show 1 + (f + 1 - 12) / 4 = (f + 1 - 12) / 4 + 1 by omega] at h
  have e1 : [6] ++ [4] = ladderFolds 1 := rfl
  have e2 : [r] ++ [[r].getLastD 0 + [6].getLastD 0 - 3] = ladderRates r 1 := by
    simp [ladderRates]
  rw [show min 4 (f + 1 - 6) = 4 by omega, e1, e2]
  exact h

end Rv64Verifier.Model.Pcs
