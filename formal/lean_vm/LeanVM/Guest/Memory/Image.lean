/-
  LeanVM.Guest.Memory.Image

  A memory image from a list of writes: each address holds the word written there, `0` where
  nothing is, so every write reads back when no two writes to one address disagree; and the log
  of the least memory size that holds a number of words.
-/

module

public import LeanVM.Semantics.Lemmas

/-!
# Write-once images

The honest memory is built as the ISA's write-once memory is filled: a list of writes
`(address, word)`, consistent when two writes to one address write one word (`Consistent`).
`image κ ws` is the memory of `2^κ` words whose word `i` is the word of the first write to
`g^i`, and `0` where there is none, the word the Rust runner reads from a cell nothing writes.
`image_read`: every write at an address below `2^κ` reads back.

`logMem n` is the log of the memory size the prover commits for `n` allocated words, at least
`minLogMem`; it is at most `maxLogMem` for `n ≤ 2^32`, and below any `k ≥ minLogMem` with
`n ≤ 2^k`, which is how a bound on the allocation bounds `Trace.committedSize`.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- A write: the word at an address. -/
abbrev Write := K × E

/-- **Write-once consistency**: two writes to one address write one word. -/
def Consistent (ws : List Write) : Prop := ∀ a ∈ ws, ∀ b ∈ ws, a.1 = b.1 → a.2 = b.2

section

open Classical

/-- The memory of `2^κ` words holding the writes, `0` where nothing is written. -/
noncomputable def image (κ : ℕ) (ws : List Write) : MemImage κ := fun i =>
  match ws.find? (fun q => decide (q.1 = gpow i)) with
  | some q => q.2
  | none => 0

end

variable {κ : ℕ} {ws : List Write}

/-- **Every write reads back** from a consistent image, at an address below `2^κ`. -/
theorem image_read (hκ : κ < 64) (hc : Consistent ws) {q : Write} (hq : q ∈ ws)
    (ha : ∃ i : Fin (2 ^ κ), q.1 = gpow i) : (image κ ws).read q.1 = some q.2 := by
  classical
  obtain ⟨i, hi⟩ := ha
  rw [hi, MemImage.read_gpow hκ]
  congr 1
  unfold image
  split
  · rename_i q' hq'
    have h1 := List.find?_some hq'
    have h2 := List.mem_of_find?_eq_some hq'
    exact hc q' h2 q hq (by rw [hi]; simpa using h1)
  · rename_i hn
    have := List.find?_eq_none.mp hn q hq
    simp [hi] at this

/-- Where nothing is written, an image holds `0`. -/
theorem image_read_zero (hκ : κ < 64) (i : Fin (2 ^ κ)) (hn : ∀ q ∈ ws, q.1 ≠ gpow i) :
    (image κ ws).read (gpow i) = some 0 := by
  classical
  rw [MemImage.read_gpow hκ]
  congr 1
  unfold image
  split
  · rename_i q hq
    exact absurd (by simpa using List.find?_some hq) (hn q (List.mem_of_find?_eq_some hq))
  · rfl

/-- Writes all read back from one reader are consistent. -/
theorem consistent_of_read {rd : K → Option E} (h : ∀ q ∈ ws, rd q.1 = some q.2) :
    Consistent ws := fun a ha b hb hab =>
  Option.some.inj ((h a ha).symm.trans (hab ▸ h b hb))

/-- Two consistent lists that agree where they meet. -/
theorem Consistent.append {ws' : List Write} (h : Consistent ws) (h' : Consistent ws')
    (hx : ∀ a ∈ ws, ∀ b ∈ ws', a.1 = b.1 → a.2 = b.2) : Consistent (ws ++ ws') := by
  intro a ha b hb hab
  rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
  · exact h a ha b hb hab
  · exact hx a ha b hb hab
  · exact (hx b hb a ha hab.symm).symm
  · exact h' a ha b hb hab

/-! ## The memory size -/

/-- The log of the memory size holding `n` words: `⌈log₂ n⌉`, at least `minLogMem`. -/
def logMem (n : ℕ) : ℕ := max minLogMem (Nat.clog 2 n)

theorem le_two_pow_logMem (n : ℕ) : n ≤ 2 ^ logMem n :=
  (Nat.le_pow_clog (by decide) n).trans (Nat.pow_le_pow_right (by decide) (le_max_right _ _))

theorem minLogMem_le_logMem (n : ℕ) : minLogMem ≤ logMem n := le_max_left _ _

/-- The memory size is the least power of two at least `2^minLogMem` holding the words. -/
theorem logMem_le_iff {n k : ℕ} : logMem n ≤ k ↔ minLogMem ≤ k ∧ n ≤ 2 ^ k := by
  rw [logMem, max_le_iff, Nat.clog_le_iff_le_pow (by decide)]

theorem logMem_le_maxLogMem {n : ℕ} (h : n ≤ 2 ^ 32) : logMem n ≤ maxLogMem :=
  logMem_le_iff.mpr ⟨by decide, h⟩

/-- The memory is less than twice the words, or the least memory. -/
theorem two_pow_logMem_le (n : ℕ) : 2 ^ logMem n ≤ max (2 ^ minLogMem) (2 * n) := by
  rcases le_total (Nat.clog 2 n) minLogMem with h | h
  · rw [logMem, max_eq_left h]; exact le_max_left _ _
  · rw [logMem, max_eq_right h]
    have h1 : 1 < n := by
      by_contra h1
      have : Nat.clog 2 n = 0 := Nat.clog_of_right_le_one (by omega) 2
      simp only [minLogMem] at h; omega
    have := Nat.pow_pred_clog_lt_self (b := 2) (by decide) h1
    have hpos := Nat.clog_pos (b := 2) (by decide) h1
    refine le_max_of_le_right ?_
    calc 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n).pred := by
          rw [← pow_succ', Nat.add_one, Nat.succ_pred_eq_of_pos hpos]
      _ ≤ 2 * n := by omega

end
end LeanVM.Guest.Memory
