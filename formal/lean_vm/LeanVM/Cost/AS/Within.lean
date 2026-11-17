module

public import LeanVM.Cost.AS.Bounds.Top

/-!
# The agreement-set extractor's price within its budget

`asBudget μ N = 2^max(58, 2μ + 9) + (N + 2^30)·(D + 2)²·(2^17 + 8D)`, `D = log₂(N + 2) + 1`: the
first term pays for the descent (level 0's dominating), level 0's stack, the candidate run and every
other price independent of the transcript (`traceBound_ok`); the second for the transcript's index
and every lookup in it, per query (`queryPart_le`) and per committed leaf or replayed operation
(`fixedPart_le`). **`asPrice_le`**: the price where the extraction succeeds, the entry's `14`
included, is within it.
-/

namespace LeanVM.Cost.Bounds.AS

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.AS LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Protocol.Whir.Sound LeanVM.Extraction.AS LeanVM.Extraction.Fast

public section

/-- **The agreement-set extractor's budget**, at a stack of `2^μ` and `N` permutation queries. -/
@[expose] def asBudget (μ N : ℕ) : ℕ :=
  2 ^ max 58 (2 * μ + 9) +
    (N + 2 ^ 30) * (Nat.log2 (N + 2) + 3) ^ 2 * (2 ^ 17 + 8 * (Nat.log2 (N + 2) + 1))

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

/-- **The price per query**: four indexes of the first forward answers, the roots' indexes. -/
theorem queryPart_le (D W : ℕ) (hD : 2 ≤ D) (hW : 64 * W ≤ D + 65) :
    4 * (fwdStepPrice D W + 14) + idxPerQuery 1792 D W + 6 * idxPerQuery 0 D W ≤
      (D + 2) ^ 2 * (2 ^ 17 + 8 * D) := by
  unfold fwdStepPrice fwdGetPrice idxPerQuery replayStepPrice firstAnswersStepPrice preimageStepPrice
  nlinarith [Nat.mul_le_mul_right (D * D) hW, Nat.mul_le_mul_right D hW, hW,
    Nat.zero_le (D * D * D), Nat.zero_le (D * D), Nat.zero_le (W * D * D)]

/-- **The price but per query**, per committed leaf, hashed block or replayed operation. -/
theorem fixedPart_le (D W : ℕ) (hD : 2 ≤ D) (hW : 64 * W ≤ D + 65) :
    (2 ^ 30 + 2) * fwdLookupPrice D W + 80016 * (fwdLookupPrice D W + 4) +
        6 * (2 ^ 28 * (2 * (D * (20 + (162 + 9 * W) * (D + 2))))) + idxFixed 1792 D W +
        6 * idxFixed 0 D W + 1000 ≤
      2 ^ 30 * ((D + 2) ^ 2 * (2 ^ 17 + 8 * D)) := by
  unfold fwdLookupPrice fwdGetPrice idxFixed firstAnswersStepPrice preimageStepPrice
  nlinarith [Nat.mul_le_mul_right (D * D) hW, Nat.mul_le_mul_right D hW, hW,
    Nat.zero_le (D * D * D), Nat.zero_le (D * D), Nat.zero_le (W * D * D)]

/-- The candidate run's price at its worst shape. -/
theorem runnerPrice_le (lay : LayoutLite) (ℓ : ℕ) (hF : LayoutFacts lay) (hℓ : ℓ ≤ 30) :
    runnerPrice lay ℓ ≤ 4682 * 2 ^ 30 + 395201 * 2 ^ 35 + 45 * 2 ^ 30 + 5000 := by
  have hcap := stepCapLite_le lay hF.logMemory_le hF.logBytecode_le hF.heights_le hF.heights_length
  have hm := hF.logMemory_le
  have hS : runnerStepPrice lay.logMemory ℓ + 41 ≤ 395201 := by unfold runnerStepPrice; omega
  have e1 : (74 * lay.logMemory + 121) * 2 ^ lay.logMemory ≤ 2341 * 2 ^ 30 :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) hm)
  have e2 : (74 * ℓ + 121) * 2 ^ ℓ ≤ 2341 * 2 ^ 30 :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) hℓ)
  have e3 : 2 ^ lay.logMemory ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) hm
  have := Nat.mul_le_mul hS hcap
  unfold runnerPrice
  omega

/-- **The price where the extraction succeeds within the budget**, the entry's `14` included, at
every admissible shape the announced sizes and the trace give. -/
theorem asPrice_le (N ℓ : ℕ) (lay : LayoutLite) (ρ : ℕ) (tr : WhirTrace)
    (roots : List (LeanVM.Protocol.Digest × ℕ × ℕ)) (hℓ : ℓ ≤ 30) (hF : LayoutFacts lay)
    (h1 : 16 ≤ lay.stackLog) (h2 : lay.stackLog ≤ 30) (h3 : 1 ≤ ρ) (h4 : ρ ≤ 4)
    (hroots : RootsOk lay.stackLog ρ (roots.map Prod.snd))
    (hsh : TraceShape lay.stackLog 0 ((Whir.ladder lay.stackLog ρ).getD []) tr) :
    headPrice N (extractorSortedMapLevels N) (limbsBelowTwoPow (extractorSortedMapLevels N + 1)) ℓ +
        finishPrice (extractorSortedMapLevels N) (limbsBelowTwoPow (extractorSortedMapLevels N + 1)) N ℓ
          lay ρ tr roots + 14 ≤ asBudget lay.stackLog N := by
  -- the first term
  obtain ⟨m, hm⟩ : ∃ m, lay.stackLog = m + 16 := ⟨lay.stackLog - 16, by omega⟩
  obtain ⟨r, hr⟩ : ∃ r, ρ = r + 1 := ⟨ρ - 1, by omega⟩
  have hok := traceBound_ok m (by omega) r (by omega)
  rw [← hm, ← hr] at hok
  have htr := traceCostB_le_bound lay.stackLog ρ 64 0 0 _ tr hsh
  have hrun := runnerPrice_le lay ℓ hF hℓ
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
  -- the words
  obtain ⟨hl, hx, hs⟩ := hroots
  rw [List.length_map] at hl
  have hw := wordsPrice_le D W N lay.stackLog ρ 28 h2 h4 le_rfl roots 0 (by omega) fun x hx' ↦ by
    have := hx x.2 (List.mem_map_of_mem hx'); omega
  have hsum := sum_transcriptIndexPrice_le D N W roots
  have hsw : 8 * (roots.map fun x ↦ x.2.2).sum ≤ 1792 := by
    have : (roots.map fun x ↦ x.2.2) = (roots.map Prod.snd).map Prod.snd := by simp [List.map_map]
    rw [this]; omega
  have hmono := transcriptIndexPrice_mono D N W hsw
  have hlen0 := Nat.mul_le_mul_right (transcriptIndexPrice D 0 N W) hl
  have hlenw := Nat.mul_le_mul_right (wordConst + 2 ^ 28 * (2 * (D * (20 + (162 + 9 * W) * (D + 2))))) hl
  rw [transcriptIndexPrice_split, transcriptIndexPrice_split] at hmono
  rw [transcriptIndexPrice_split] at hlen0
  rw [transcriptIndexPrice_split, transcriptIndexPrice_split] at hsum
  -- the seed's blocks
  have hpl : 2 ^ ℓ ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) hℓ
  have hq : (9 + 8 * (16 * 2 ^ ℓ)) / 136 + 2 ≤ 2 ^ 30 + 2 := by omega
  have hseed := Nat.mul_le_mul_right (fwdLookupPrice D W + 430004) hq
  -- the queries
  have hNA := Nat.mul_le_mul_left N hA
  have e1 : N * (4 * (fwdStepPrice D W + 14) + idxPerQuery 1792 D W + 6 * idxPerQuery 0 D W) =
      4 * ((fwdStepPrice D W + 14) * N) + N * idxPerQuery 1792 D W + 6 * (N * idxPerQuery 0 D W) := by
    ring
  have e2 : (N + 2 ^ 30) * (D + 2) ^ 2 * (2 ^ 17 + 8 * D) =
      N * ((D + 2) ^ 2 * (2 ^ 17 + 8 * D)) + 2 ^ 30 * ((D + 2) ^ 2 * (2 ^ 17 + 8 * D)) := by ring
  have e3 : (2 ^ 30 + 2) * (fwdLookupPrice D W + 430004) =
      (2 ^ 30 + 2) * fwdLookupPrice D W + (2 ^ 30 + 2) * 430004 := by ring
  have e4 : 6 * (wordConst + 2 ^ 28 * (2 * (D * (20 + (162 + 9 * W) * (D + 2))))) =
      6 * wordConst + 6 * (2 ^ 28 * (2 * (D * (20 + (162 + 9 * W) * (D + 2))))) := by ring
  have e5 : 6 * (N * idxPerQuery 0 D W + idxFixed 0 D W) =
      6 * (N * idxPerQuery 0 D W) + 6 * idxFixed 0 D W := by ring
  rw [e2]
  unfold headPrice finishPrice lookPrice bytecodeWordsPrice at *
  have hwc : wordConst ≤ 70000000000000 := by unfold wordConst; norm_num
  linarith

end

end LeanVM.Cost.Bounds.AS
