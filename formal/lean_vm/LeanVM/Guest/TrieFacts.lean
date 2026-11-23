/-
  LeanVM.Guest.TrieFacts

  Reading a trie after a store: the facts the certificate checkers and the core route share.
-/

module

public import LeanVM.Guest.Check

/-!
# Reading a trie after a store

`get_set_eq`: a store's key reads its value, every other key what it read before. `getF_setF`: what a
key reads after a store is the stored value at its key, or what it read before.
-/

namespace LeanVM.Guest.Check

open LeanVM.Guest LeanVM.Guest.Exec

public section

theorem get_set_eq {α : Type} (a : α) :
    ∀ (d : ℕ) (t : Exec.Trie α) (n m : ℕ), n + 1 < 2 ^ d →
      (t.set a d n).get m = if m = n then some a else t.get m
  | 0, _, n, _, h => by simp at h
  | d + 1, t, n, m, h => by
    have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ]; ring
    rw [Exec.Trie.set_succ, Exec.Trie.get_eq_node t m]
    by_cases h0 : n = 0
    · subst h0
      simp only [↓reduceIte, Exec.Trie.get_node]
      by_cases hm : m = 0 <;> simp [hm]
    · by_cases h1 : n % 2 = 1
      · simp only [h0, h1, ↓reduceIte, Exec.Trie.get_node]
        by_cases hm : m = 0
        · simp only [hm, ↓reduceIte]
          simp only [Ne.symm h0, ↓reduceIte]
        · by_cases hm1 : m % 2 = 1
          · rw [get_set_eq a d _ _ _ (by omega)]
            by_cases he : m = n
            · subst he; simp [hm, hm1]
            · have : m / 2 ≠ n / 2 := by omega
              simp [hm, hm1, he, this]
          · have : m ≠ n := by omega
            simp [hm, hm1, this]
      · simp only [h0, h1, ↓reduceIte, Exec.Trie.get_node]
        by_cases hm : m = 0
        · simp only [hm, ↓reduceIte]
          simp only [Ne.symm h0, ↓reduceIte]
        · by_cases hm1 : m % 2 = 1
          · have : m ≠ n := by omega
            simp [hm, hm1, this]
          · rw [get_set_eq a d _ _ _ (by omega)]
            by_cases he : m = n
            · subst he; simp [hm, hm1]
            · have : m / 2 - 1 ≠ n / 2 - 1 := by omega
              simp [hm, hm1, he, this]

theorem getF_setF {α : Type} {a b : α} {d n m : ℕ} {t : Exec.Trie α}
    (h : getF (setF a d t n) m = some b) : (m = n ∧ b = a) ∨ getF t m = some b := by
  rw [getF_eq, setF_eq] at h; rw [getF_eq]; exact Exec.Trie.get_set h

end

end LeanVM.Guest.Check
