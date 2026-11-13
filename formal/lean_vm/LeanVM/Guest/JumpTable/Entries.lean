/-
  LeanVM.Guest.JumpTable.Entries

  What the jump table's check reads at each entry of `Data.jtTrie`.
-/

module

public import LeanVM.Guest.Data.FrameSizes
public import LeanVM.Guest.Bytecode
public import LeanVM.Guest.Pow
public import Statement.Data.Bytecode00
public import LeanVM.Guest.Code
public import LeanVM.Guest.Memory.Walk

/-!
# The entries of the jump table

`entryOk s t` says entry `(s, t)` of `Data.jtTrie` is the `SET` at instruction
`s - Data.mainCells` of `__jump_tables`, and `allEntries p t a b` that `p` holds at every entry of a subtree. The kernel
checks it in two walks, neither indexing the code: of the trie, that every key is a slot of an
instruction (`keysOk`, `JumpTable.Keys`), and of the code, that each instruction sets its slot to
the trie's target there (`codeOk`, `JumpTable.Code`).
-/

namespace LeanVM.Guest.JumpTable

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

/-- The entry `(s, t)` is the `SET` at instruction `s - Data.mainCells` of `__jump_tables`. -/
noncomputable def entryOk (s t : ℕ) : Bool :=
  Nat.blt (s - Data.mainCells) Data.f0.instructionCount &&
    match Data.f0.instructionAt (s - Data.mainCells) with
    | .set o k0 k1 => o == s && k1 == 0 && Data.powTree.find k0 == some t
    | _ => false

/-- Key `s` is the slot of an instruction `s - Data.mainCells` of `__jump_tables`. -/
def keysOk (s _ : ℕ) : Bool :=
  Nat.ble Data.mainCells s && Nat.blt (s - Data.mainCells) Data.f0.instructionCount

/-- Instruction `i` of `__jump_tables` is the `SET` of slot `i + Data.mainCells` to the trie's target
there,
if any. -/
noncomputable def codeOk (i : ℕ) (ins : OffsetInstruction) : Bool :=
  match Data.jtTrie.get (i + Data.mainCells) with
  | some t => match ins with
    | .set o k0 k1 => o == i + Data.mainCells && k1 == 0 && Data.powTree.find k0 == some t
    | _ => false
  | none => true

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

theorem allEntries_of_get {p : ℕ → ℕ → Bool} :
    ∀ (t : Trie ℕ) (a b : ℕ), (∀ n x, t.get n = some x → p (a * n + b) x = true) → allEntries p t a b = true
  | .nil, _, _, _ => rfl
  | .node v l r, a, b, h => by
    have h0 : v.all (p b) = true := by
      cases v with
      | none => rfl
      | some x =>
        have := h 0 x (by rw [Trie.get_node]; simp)
        simpa using this
    have hl : allEntries p l (2 * a) (a + b) = true := allEntries_of_get l _ _ fun n x hx => by
      have := h (2 * n + 1) x (by
        rw [Trie.get_node]
        simp only [show ¬ (2 * n + 1 = 0) by omega, show (2 * n + 1) % 2 = 1 by omega,
          show (2 * n + 1) / 2 = n by omega, hx, ↓reduceIte])
      rwa [show a * (2 * n + 1) + b = 2 * a * n + (a + b) by ring] at this
    have hr : allEntries p r (2 * a) (2 * a + b) = true := allEntries_of_get r _ _ fun n x hx => by
      have := h (2 * n + 2) x (by
        rw [Trie.get_node]
        simp only [show ¬ (2 * n + 2 = 0) by omega, show ¬ ((2 * n + 2) % 2 = 1) by omega,
          show (2 * n + 2) / 2 - 1 = n by omega, hx, ↓reduceIte])
      rwa [show a * (2 * n + 2) + b = 2 * a * n + (2 * a + b) by ring] at this
    show (v.all (p b) && allEntries p l (2 * a) (a + b) && allEntries p r (2 * a) (2 * a + b)) = true
    rw [h0, hl, hr]; rfl

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
