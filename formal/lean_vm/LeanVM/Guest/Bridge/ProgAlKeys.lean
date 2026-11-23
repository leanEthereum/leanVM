/-
  LeanVM.Guest.Bridge.ProgAlKeys

  The callees the alignment's tables name are compiled functions (`calleesOf_mem`), the guest's entries are
  keys of the tries (`entry_key`), and a trie built from a list holds only its pairs (`trieOf_mem`), apart from
  the deployed alignment's checks.
-/

module

public import LeanVM.Guest.Bridge.AlignDefs
public import LeanVM.Guest.Bridge.ProgAlDefs
public import LeanVM.Guest.B2C.CplRun
public import LeanVM.Guest.CheckSplit
public import LeanVM.Guest.Bytecode

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core
open LeanVM.Guest.Exec (Trie trieAll trieAll_get)
open LeanVM.Guest.Check (getF)

public section

/-- **The callees the checks name are compiled functions.** -/
theorem calleesOk : trieAll (fun l ↦ l.all fun c ↦ Nat.ble 1 c && Nat.blt c nFns) alignCallees = true := by
  decide +kernel

theorem calleesOf_mem {j c : ℕ} (h : c ∈ calleesOf j) : 1 ≤ c ∧ c < nFns := by
  unfold calleesOf at h
  cases hg : getF alignCallees j with
  | none => simp [hg] at h
  | some l =>
    rw [hg, Option.getD_some] at h
    rw [Check.getF_eq] at hg
    have h1 := trieAll_get calleesOk hg
    simp only [List.all_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h1
    exact h1 c h

theorem entry_le_of_mem : ∀ {s e : ℕ} {fns : List CompiledFunction}, LeanVM.Guest.consecutive s fns e = true →
    ∀ {f : CompiledFunction}, f ∈ fns → f.entryPc ≤ e
  | _, _, [], _, _, hf => absurd hf List.not_mem_nil
  | s, e, f' :: fs, h, f, hf => by
    simp only [LeanVM.Guest.consecutive, Bool.and_eq_true, beq_iff_eq] at h
    have hle := consecutive_le h.2
    rcases List.mem_cons.mp hf with rfl | hf
    · omega
    · exact entry_le_of_mem h.2 hf

/-- A guest function's entry is a key of the tries. -/
theorem entry_key {c : ℕ} (hc : c < nFns) : (fnOf c).entryPc + 1 < 2 ^ Exec.indexDepth := by
  have h1 := entry_le_of_mem functions_consecutive (B2C.fnOf_memC hc)
  have h2 : Data.codeLen < 2 ^ 19 - 1 := codeLen_lt
  have h3 : (2 : ℕ) ^ Exec.indexDepth = 1048576 := by norm_num [Exec.indexDepth]
  omega

theorem trieGo_mem {α : Type} : ∀ (l : List (ℕ × α)) (t : Trie α) {k : ℕ} {v : α},
    (∀ p ∈ l, p.1 + 1 < 2 ^ Exec.indexDepth) → getF (trieGo l t) k = some v → (k, v) ∈ l ∨ getF t k = some v
  | [], _, _, _, _, h => Or.inr h
  | p :: l, t, k, v, hb, h => by
    simp only [trieGo, Exec.Trie.seq_eq] at h
    rcases trieGo_mem l _ (fun q hq ↦ hb q (List.mem_cons_of_mem _ hq)) h with h' | h'
    · exact Or.inl (List.mem_cons_of_mem _ h')
    · rw [Check.getF_setF_eq _ _ _ (hb p List.mem_cons_self)] at h'
      by_cases hk : k = p.1
      · rw [ite_eq_left hk] at h'
        subst hk
        obtain rfl := Option.some.inj h'
        exact Or.inl List.mem_cons_self
      · rw [ite_eq_right hk] at h'
        exact Or.inr h'

theorem trieOf_mem {α : Type} {l : List (ℕ × α)} {k : ℕ} {v : α} (hb : ∀ p ∈ l, p.1 + 1 < 2 ^ Exec.indexDepth)
    (h : getF (trieOf l) k = some v) : (k, v) ∈ l := by
  rcases trieGo_mem l .nil hb h with h | h
  · exact h
  · simp [Check.getF_eq] at h

end

end LeanVM.Guest.Bridge
