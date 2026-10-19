/-
  LeanVM.Guest.JumpTable.Entries

  What the jump table's check reads at each entry of `Data.jtTrie`.
-/

module

public import LeanVM.Guest.Pow
public import LeanVM.Guest.Data.Bytecode00

/-!
# The entries of the jump table

`entryOk s t` says entry `(s, t)` of `Data.jtTrie` is the `SET` at instruction `s - 167` of
`__jump_tables`, and `allEntries p t a b` that `p` holds at every entry of a subtree. The
subtrees are checked by the kernel in `JumpTable.Ok*`.
-/

namespace LeanVM.Guest.JumpTable

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

/-- The entry `(s, t)` is the `SET` at instruction `s - 167` of `__jump_tables`. -/
noncomputable def entryOk (s t : ℕ) : Bool :=
  Nat.blt (s - 167) Data.f0.len &&
    match Data.f0.instrAt (s - 167) with
    | .set o k0 k1 k2 => o == s && k1 == 0 && k2 == 0 && Data.powTree.find k0 == some t
    | _ => false

/-- `p` at every entry of the trie, whose key `n` is the global key `a * n + b`. -/
noncomputable def allEntries (p : ℕ → ℕ → Bool) : Trie ℕ → ℕ → ℕ → Bool :=
  Trie.rec (motive := fun _ ↦ ℕ → ℕ → Bool) (fun _ _ ↦ true)
    (fun v _ _ cl cr a b ↦ v.all (p b) && cl (2 * a) (a + b) && cr (2 * a) (2 * a + b))

theorem allEntries_get {p : ℕ → ℕ → Bool} :
    ∀ {t : Trie ℕ} {a b : ℕ}, allEntries p t a b = true → ∀ {n x : ℕ}, t.get n = some x → p (a * n + b) x = true
  | .nil, _, _, _, _, _, h => by simp at h
  | .node v l r, a, b, hall, n, x, h => by
    have hall' : v.all (p b) = true ∧ allEntries p l (2 * a) (a + b) = true ∧
        allEntries p r (2 * a) (2 * a + b) = true := by
      simpa [allEntries, Bool.and_eq_true, and_assoc] using hall
    rw [Trie.get_node] at h
    split_ifs at h with h0 h1
    · subst h0
      have := hall'.1
      rw [h] at this
      simpa using this
    · have := allEntries_get hall'.2.1 h
      have e : a * n + b = 2 * a * (n / 2) + (a + b) := by
        have : n = 2 * (n / 2) + 1 := by omega
        conv_lhs => rw [this]
        ring
      rwa [e]
    · have := allEntries_get hall'.2.2 h
      have e : a * n + b = 2 * a * (n / 2 - 1) + (2 * a + b) := by
        have : n = 2 * (n / 2 - 1) + 2 := by omega
        conv_lhs => rw [this]
        ring
      rwa [e]

theorem allEntries_split {p : ℕ → ℕ → Bool} {t : Trie ℕ} {a b : ℕ} (hv : t.val.all (p b) = true)
    (hl : allEntries p t.left (2 * a) (a + b) = true) (hr : allEntries p t.right (2 * a) (2 * a + b) = true) :
    allEntries p t a b = true := by
  cases t with
  | nil => rfl
  | node v l r =>
    simp only [allEntries, Trie.val, Trie.left, Trie.right, Bool.and_eq_true] at hv hl hr ⊢
    exact ⟨⟨hv, hl⟩, hr⟩

end
end LeanVM.Guest.JumpTable
