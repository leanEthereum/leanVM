/-
  LeanVM.Guest.JumpTable

  The jump table of the checker's `Glob` holds in a memory that holds `__jump_tables`' writes.
-/

module

public import LeanVM.Guest.End
public import LeanVM.Guest.Data.Pows
public import LeanVM.Guest.Pow

/-!
# The jump table by the `SET`s of `__jump_tables`

`End.JumpTables L` says each `SET` of `__jump_tables` holds in `L`. `Data.jtTrie` maps a slot `s`
to the exponent `t` of the target `g^t` the checker expects there. `jtOk` checks, at every entry
`(s, t)` of the trie, that instruction `s - 167` of `__jump_tables` is `SET s, k0, 0, 0` with
`Data.powTree` giving `k0 ↦ t`, so that `K.ofBits k0 = g^t` (`PowTree.Ok`).
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

set_option maxRecDepth 100000 in
theorem jtOk_0 : allEntries entryOk (Data.jtTrie.left.left.left.left) 16 15 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_1 : allEntries entryOk (Data.jtTrie.left.left.left.right) 16 23 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_2 : allEntries entryOk (Data.jtTrie.left.left.right.left) 16 19 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_3 : allEntries entryOk (Data.jtTrie.left.left.right.right) 16 27 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_4 : allEntries entryOk (Data.jtTrie.left.right.left.left) 16 17 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_5 : allEntries entryOk (Data.jtTrie.left.right.left.right) 16 25 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_6 : allEntries entryOk (Data.jtTrie.left.right.right.left) 16 21 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_7 : allEntries entryOk (Data.jtTrie.left.right.right.right) 16 29 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_8 : allEntries entryOk (Data.jtTrie.right.left.left.left) 16 16 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_9 : allEntries entryOk (Data.jtTrie.right.left.left.right) 16 24 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_10 : allEntries entryOk (Data.jtTrie.right.left.right.left) 16 20 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_11 : allEntries entryOk (Data.jtTrie.right.left.right.right) 16 28 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_12 : allEntries entryOk (Data.jtTrie.right.right.left.left) 16 18 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_13 : allEntries entryOk (Data.jtTrie.right.right.left.right) 16 26 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_14 : allEntries entryOk (Data.jtTrie.right.right.right.left) 16 22 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk_15 : allEntries entryOk (Data.jtTrie.right.right.right.right) 16 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jtOk : allEntries entryOk Data.jtTrie 1 0 = true :=
  allEntries_split (by decide +kernel) (allEntries_split (by decide +kernel) (allEntries_split (by decide +kernel) (allEntries_split (by decide +kernel) jtOk_0 jtOk_1) (allEntries_split (by decide +kernel) jtOk_2 jtOk_3)) (allEntries_split (by decide +kernel) (allEntries_split (by decide +kernel) jtOk_4 jtOk_5) (allEntries_split (by decide +kernel) jtOk_6 jtOk_7))) (allEntries_split (by decide +kernel) (allEntries_split (by decide +kernel) (allEntries_split (by decide +kernel) jtOk_8 jtOk_9) (allEntries_split (by decide +kernel) jtOk_10 jtOk_11)) (allEntries_split (by decide +kernel) (allEntries_split (by decide +kernel) jtOk_12 jtOk_13) (allEntries_split (by decide +kernel) jtOk_14 jtOk_15)))

/-- The jump table the checker reads is what `__jump_tables` wrote. -/
theorem jt_of_jumpTables {κ : ℕ} {L : MemImage κ} (h : End.JumpTables L) (hpows : Data.powTree.Ok) :
    ∀ s t, Data.jtTrie.get s = some t → L.read (gpow s) = some (ofK (gpow t)) := by
  intro s t hs
  have he := allEntries_get jtOk hs
  rw [Nat.one_mul, Nat.add_zero] at he
  unfold entryOk at he
  rw [Bool.and_eq_true] at he
  obtain ⟨hlt, he⟩ := he
  have hlen : s - 167 < Data.f0.len := by simpa using hlt
  obtain ⟨o, k0, k1, k2, hins, hmem⟩ := End.f0_instr hlen
  rw [hins] at he
  simp only [Bool.and_eq_true, beq_iff_eq] at he
  obtain ⟨⟨⟨ho, hk1⟩, hk2⟩, hf⟩ := he
  subst ho hk1 hk2
  have := h _ hmem
  rwa [imm_of_ofBits (PowTree.find_ok hpows hf)] at this

end
end LeanVM.Guest.JumpTable
