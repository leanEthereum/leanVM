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

open LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

/-- The entry `(s, t)` is the `SET` at instruction `s - 167` of `__jump_tables`. -/
def entryOk (s t : ℕ) : Bool :=
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

set_option maxRecDepth 100000 in
theorem jtOk : allEntries entryOk Data.jtTrie 1 0 = true := by
  decide +kernel

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
  rwa [imm_of_ofBits (PowTree.find_ok hpows (Option.some_inj.mp hf))] at this

end
end LeanVM.Guest.JumpTable
