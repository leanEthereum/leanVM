module

public import LeanVM.Cost.AS.Bounds.Top

/-!
# The agreement-set extractor's price within its budget

`asBudget μ N = 2^max(58, 2μ + 9) + (N + 2^30)·(D + 2)²·(2^15 + 2D)`, `D = log₂(N + 2) + 1`: the
first term pays for the descent (level 0's dominating), level 0's stack, the candidate execution
(every table row's state read, `≤ 2^53`) and every other price independent of the transcript
(`traceBound_ok`); the second for the transcript's two indexes (its first forward answers, and one
preimage index every root shares) and every lookup in them, per query (`queryPart_le`) and per
replayed operation, packed scalar or hashed block (`fixedPart_le`). **`asPrice_le`**: the price
where the extraction succeeds, the entry's `14` included, is within it; `asBudget_le_statement`:
it is the statement's budget.
-/

namespace LeanVM.Cost.Bounds.AS

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.AS LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Protocol.Whir.Sound LeanVM.Extraction.AS LeanVM.Extraction.Fast
open LeanVM.Protocol.EndToEnd.Sound

public section

/-- **The agreement-set extractor's budget**, at a stack of `2^μ` and `N` permutation queries. -/
@[expose] def asBudget (μ N : ℕ) : ℕ :=
  2 ^ max 58 (2 * μ + 9) +
    (N + 2 ^ 30) * (Nat.log2 (N + 2) + 3) ^ 2 * (2 ^ 15 + 2 * (Nat.log2 (N + 2) + 1))

/-- The budget is the statement's. -/
theorem asBudget_le_statement (μ N : ℕ) : asBudget μ N ≤ leanVmKnowledgeExtractorBudget μ N :=
  le_refl _

/-- An index's price per query. -/
@[expose] def idxPerQuery (L D W : ℕ) : ℕ :=
  (replayStepPrice (L + 136) D W + 16) + (120 * (L + 136) + 9363) +
    (firstAnswersStepPrice L D W + 11 + preimageStepPrice L D W + 11 +
      D * (20 + (40 + 26 * L + 9 * W) * (D + 2)) + 67)

/-- An index's price but per query. -/
@[expose] def idxFixed (L D W : ℕ) : ℕ :=
  (26 * 8 + 37) * D + (120 * (L + 136) + 9363) + 442 +
    (firstAnswersStepPrice L D W + 11 + preimageStepPrice L D W + 11 +
      D * (20 + (40 + 26 * L + 9 * W) * (D + 2)) + 67) + 44

theorem transcriptIndexPrice_split (D L N W : ℕ) :
    transcriptIndexPrice D L N W = N * idxPerQuery L D W + idxFixed L D W := by
  unfold transcriptIndexPrice idxPerQuery idxFixed
  ring

/-- **The price per query**: the index of the first forward answers and the roots' index. -/
theorem queryPart_le (D W : ℕ) (hD : 2 ≤ D) (hW : 64 * W ≤ D + 65) :
    (fwdStepPrice D W + 14) + idxPerQuery 512 D W ≤ (D + 2) ^ 2 * (2 ^ 15 + 2 * D) := by
  unfold fwdStepPrice fwdGetPrice idxPerQuery replayStepPrice firstAnswersStepPrice preimageStepPrice
  nlinarith [Nat.mul_le_mul_right (D * D) hW, Nat.mul_le_mul_right D hW, hW,
    Nat.zero_le (D * D * D), Nat.zero_le (D * D), Nat.zero_le (W * D * D)]

/-- **The price but per query**, per replayed operation or packed scalar, hashed block or
committed leaf. -/
theorem fixedPart_le (D W : ℕ) (hD : 2 ≤ D) (hW : 64 * W ≤ D + 65) :
    (2 ^ 30 + 2) * fwdLookupPrice D W + 82016 * (fwdLookupPrice D W + 4) +
        6 * (2 ^ 28 * (2 * (D * (20 + (162 + 9 * W) * (D + 2))))) + idxFixed 512 D W + 1000 ≤
      2 ^ 30 * ((D + 2) ^ 2 * (2 ^ 15 + 2 * D)) := by
  unfold fwdLookupPrice fwdGetPrice idxFixed firstAnswersStepPrice preimageStepPrice
  nlinarith [Nat.mul_le_mul_right (D * D) hW, Nat.mul_le_mul_right D hW, hW,
    Nat.zero_le (D * D * D), Nat.zero_le (D * D), Nat.zero_le (W * D * D)]

/-- **The price where the extraction succeeds within the budget**, the entry's `14` included, at
every admissible shape the announced sizes and the trace give. -/
theorem asPrice_le (N ℓ : ℕ) (lay : LayoutLite) (ρ : ℕ) (tr : WhirTrace)
    (roots : List (LeanVM.Protocol.Digest × ℕ × ℕ)) (hℓ : ℓ ≤ 30)
    (h1 : 16 ≤ lay.stackLog) (h2 : lay.stackLog ≤ 30) (h3 : 1 ≤ ρ) (h4 : ρ ≤ 4)
    (hroots : RootsOk lay.stackLog ρ (roots.map Prod.snd))
    (hsh : TraceShape lay.stackLog 0 ((Whir.ladder lay.stackLog ρ).getD []) tr) :
    headPrice N (extractorSortedMapLevels N) (limbsBelowTwoPow (extractorSortedMapLevels N + 1)) ℓ +
        finishPrice (extractorSortedMapLevels N) (limbsBelowTwoPow (extractorSortedMapLevels N + 1)) N
          (10 ^ 7) lay ρ tr roots + 14 ≤ asBudget lay.stackLog N := by
  -- the first term
  obtain ⟨m, hm⟩ : ∃ m, lay.stackLog = m + 16 := ⟨lay.stackLog - 16, by omega⟩
  obtain ⟨r, hr⟩ : ∃ r, ρ = r + 1 := ⟨ρ - 1, by omega⟩
  have hok := traceBound_ok m (by omega) r (by omega)
  rw [← hm, ← hr] at hok
  have htr := traceCostB_le_bound lay.stackLog ρ 64 0 0 _ tr hsh
  -- the levels and the limbs
  have hW64 : 64 * limbsBelowTwoPow (extractorSortedMapLevels N + 1) ≤ extractorSortedMapLevels N + 65 := by
    unfold limbsBelowTwoPow; omega
  have hD2 : 2 ≤ extractorSortedMapLevels N := by
    unfold extractorSortedMapLevels
    have : 1 ≤ Nat.log2 (N + 2) := (Nat.le_log2 (by omega)).2 (by omega)
    omega
  have eD : Nat.log2 (N + 2) = extractorSortedMapLevels N - 1 := by
    unfold extractorSortedMapLevels; omega
  unfold asBudget
  rw [eD, show extractorSortedMapLevels N - 1 + 3 = extractorSortedMapLevels N + 2 by omega,
    show extractorSortedMapLevels N - 1 + 1 = extractorSortedMapLevels N by omega]
  generalize extractorSortedMapLevels N = D at hW64 hD2 ⊢
  generalize limbsBelowTwoPow (D + 1) = W at hW64 ⊢
  have hA := queryPart_le D W hD2 hW64
  have hB := fixedPart_le D W hD2 hW64
  -- the words and the roots' index
  obtain ⟨hl, hx, hs⟩ := hroots
  rw [List.length_map] at hl
  have hw := wordsPrice_le D W lay.stackLog ρ 28 h2 h4 le_rfl roots 0 (by omega) fun x hx' ↦ by
    have := hx x.2 (List.mem_map_of_mem hx'); omega
  have hcap := capOf_le 64 roots fun x hx' ↦ (hx x.2 (List.mem_map_of_mem hx')).2.2
  have hmono := transcriptIndexPrice_mono D N W (show capOf roots ≤ 512 by omega)
  have hlenw := Nat.mul_le_mul_right (wordConst + 2 ^ 28 * (2 * (D * (20 + (162 + 9 * W) * (D + 2))))) hl
  have hpow : 2 ^ roots.length ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hl
  rw [transcriptIndexPrice_split, transcriptIndexPrice_split] at hmono
  -- the seed's blocks
  have hpl : 2 ^ ℓ ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) hℓ
  have hq : (9 + 8 * (16 * 2 ^ ℓ)) / 136 + 2 ≤ 2 ^ 30 + 2 := by omega
  have hseed := Nat.mul_le_mul_right (fwdLookupPrice D W + 430004) hq
  -- the queries
  have hNA := Nat.mul_le_mul_left N hA
  have e1 : N * ((fwdStepPrice D W + 14) + idxPerQuery 512 D W) =
      (fwdStepPrice D W + 14) * N + N * idxPerQuery 512 D W := by ring
  have e2 : (N + 2 ^ 30) * (D + 2) ^ 2 * (2 ^ 15 + 2 * D) =
      N * ((D + 2) ^ 2 * (2 ^ 15 + 2 * D)) + 2 ^ 30 * ((D + 2) ^ 2 * (2 ^ 15 + 2 * D)) := by ring
  have e3 : (2 ^ 30 + 2) * (fwdLookupPrice D W + 430004) =
      (2 ^ 30 + 2) * fwdLookupPrice D W + (2 ^ 30 + 2) * 430004 := by ring
  have e4 : 6 * (wordConst + 2 ^ 28 * (2 * (D * (20 + (162 + 9 * W) * (D + 2))))) =
      6 * wordConst + 6 * (2 ^ 28 * (2 * (D * (20 + (162 + 9 * W) * (D + 2))))) := by ring
  rw [e2]
  unfold headPrice finishPrice bytecodeWordsPrice bodyReplayPrice at *
  rw [transcriptIndexPrice_split]
  have hwc : wordConst ≤ 70000000000000 := by unfold wordConst; norm_num
  linarith

end

end LeanVM.Cost.Bounds.AS
