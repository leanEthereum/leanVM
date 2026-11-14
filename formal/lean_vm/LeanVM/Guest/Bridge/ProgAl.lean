/-
  LeanVM.Guest.Bridge.ProgAl

  The deployed guest's functions align: `ProgAl guestProgram coreProgram alignA`, with `main` entered at `mainEntry`, the premises of `trace_deployed` on the program.
-/

module

public import LeanVM.Guest.Bridge.ProgAl.All
public import LeanVM.Guest.B2C.FrameAll
public import LeanVM.Guest.B2C.CplWalk
public import LeanVM.Guest.B2C.CplRun
public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.CheckSplit
public import LeanVM.Guest.Exec
public import LeanVM.Guest.JumpTable

/-!
# The deployed guest's alignment

`progAl`: every function of `coreProgram`, of compiled index `j` (`fn_of_idx`), passes its check (`ProgAl.fnAlOk_all`) on its body, its code is fetched at its entry (`guest_fetches`), its halting pc is the last slot. A callee a check names by entry (`AlignCtx.entOk`) is in its table of callees (`trieOf_mem`), a compiled function `c` (`calleesOk`) named `(coreOf c).name`, so `alignA` reads it at index `c` (`idxOf_coreOf`) with that entry. `alignA_main`: `main` is entered at `mainEntry`.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core
open LeanVM.Guest.Exec (Trie)
open LeanVM.Guest.Check (getF)
open LeanVM.Guest.End (mainEntry)

@[expose] public section

/-- Every value of a trie passes `p`. -/
noncomputable def trieAll {α : Type} (p : α → Bool) : Trie α → Bool :=
  Trie.rec (motive := fun _ ↦ Bool) true (fun v _ _ al ar ↦ v.all p && al && ar)

end

public section

theorem trieAll_get {α : Type} {p : α → Bool} :
    ∀ {t : Trie α} {n : ℕ} {v : α}, trieAll p t = true → t.get n = some v → p v = true
  | .nil, _, _, _, h => by simp at h
  | .node w l r, n, v, ha, h => by
    have ha' : w.all p = true ∧ trieAll p l = true ∧ trieAll p r = true := by
      simpa [trieAll, Bool.and_eq_true, and_assoc] using ha
    rw [Exec.Trie.get_node] at h
    split at h
    · subst h; simpa using ha'.1
    · split at h
      · exact trieAll_get ha'.2.1 h
      · exact trieAll_get ha'.2.2 h

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
  have h2 : Data.codeLen < 524287 := codeLen_lt
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

/-- **A callee a check names by entry is entered there.** -/
theorem alignA_ent {f g : String} {t : ℕ} (h : (alignA f).X.entOk t g = true) : (alignA g).X.entry = t := by
  generalize hj : (B2C.idxOf f).getD 0 = j at h
  simp only [alignA, hj, fnAl, ctxOf, AlignCtx.ofData, AlignCtx.entOk] at h
  have hb : ∀ p ∈ (entsOf j).map (fun e ↦ (e.2, e.1)), p.1 + 1 < 2 ^ Exec.indexDepth := by
    intro p hp
    simp only [entsOf, List.map_map, List.mem_map, Function.comp_apply] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    exact entry_key (calleesOf_mem hc).2
  split at h
  · rename_i g' hg
    have hgg : g' = g := by simpa using h
    subst hgg
    have hm := trieOf_mem hb hg
    simp only [entsOf, List.map_map, List.mem_map, Function.comp_apply, Prod.mk.injEq] at hm
    obtain ⟨c, hc, rfl, rfl⟩ := hm
    obtain ⟨h1, h2⟩ := calleesOf_mem hc
    rw [alignA_of (B2C.idxOf_coreOf h1 h2)]
    rfl
  · cases h

theorem alignA_halt : regs alignHalt 0 = Registers.final guestProgram := by
  simp only [regs, Registers.final, LeanIsaProgram.pcFinal, guest_logSize, Exec.gpow_zero', alignHalt]
  rfl

private theorem idxOf_main : B2C.idxOf "main" = some 1 := by decide +kernel

/-- **`main` is entered at `mainEntry`.** -/
theorem alignA_main : entOf alignA "main" = mainEntry := by
  rw [entOf, alignA_of idxOf_main]
  decide +kernel

/-- **The deployed guest's functions align.** -/
theorem progAl : ProgAl guestProgram coreProgram alignA where
  ok f fn hf := by
    obtain ⟨j, hj⟩ := B2C.idxOf_of_find hf
    obtain ⟨-, -, -, -, -, -, -, -, h1, h2⟩ := B2C.fn_of_idx hj
    rw [alignA_of hj]
    exact ProgAl.fnAlOk_all j h1 (by have : nFns = 1602 := rfl; omega)
  body f fn hf := by
    obtain ⟨j, hj⟩ := B2C.idxOf_of_find hf
    obtain ⟨i, -, hi, -, hfi, hc, -⟩ := B2C.fn_of_idx hj
    rw [alignA_of hj, fnAl, hc, ← Option.some.inj (hfi.symm.trans hf)]
  fetch f fn hf off ins h := by
    obtain ⟨j, hj⟩ := B2C.idxOf_of_find hf
    obtain ⟨-, -, -, -, -, -, -, -, -, h2⟩ := B2C.fn_of_idx hj
    rw [alignA_of hj] at h ⊢
    exact (Exec.guest_fetches (B2C.fnOf_memC h2) off ins h).1
  ent f fn t g _ h := alignA_ent h
  halt f fn _ _ := alignA_halt

end

end LeanVM.Guest.Bridge
