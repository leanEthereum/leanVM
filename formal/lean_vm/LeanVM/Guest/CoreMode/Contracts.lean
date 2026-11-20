module

public import LeanVM.Guest.CoreMode.Core

/-!
# The heap contracts' table

Which functions take their own heap signature as their contract (`CFun.hc`) is a table (`HcEnt`, one per such
function: its entry, heap signature, entry and return frame cells, parameter and returned word counts), generated as
`hcTab` (`Gen/HcTab.lean`). The contracts at every entry are the table's (`ctOf`), and two decidable checks tie the
table to each function's view: a function names, at its own entry and at each callee entry of its environment, the
contract the table holds there (`ctB`, giving `CtOk`). `Trie.entries` lists a trie's entries, so that the signatures an
environment holds are a list (`mem_entries`).
-/

namespace LeanVM.Guest.Exec.Trie

@[expose] public section

variable {α : Type}

/-- A trie's entries with their keys: key `0` at the root, `2m+1` at key `m` of the left child,
`2m+2` at the right one's. -/
def entries : Trie α → List (ℕ × α)
  | nil => []
  | node v l r => (v.map fun a ↦ (0, a)).toList ++ (l.entries.map fun p ↦ (2 * p.1 + 1, p.2)) ++
      (r.entries.map fun p ↦ (2 * p.1 + 2, p.2))

theorem mem_entries : ∀ {t : Trie α} {n : ℕ} {a : α}, t.get n = some a → (n, a) ∈ t.entries
  | nil, n, a, h => by rw [get_eq_getC] at h; cases h
  | node v l r, n, a, h => by
    rw [get_eq_getC] at h
    simp only [getC] at h
    simp only [entries, List.mem_append, List.mem_map]
    by_cases h0 : n = 0
    · subst h0
      simp only [BEq.rfl, Bool.cond_true] at h
      subst h
      exact Or.inl (Or.inl (by simp))
    · have hb : (n == 0) = false := by simpa using h0
      rw [hb, Bool.cond_false] at h
      by_cases h1 : n % 2 = 1
      · rw [show (n % 2 == 1) = true by simpa using h1, Bool.cond_true, ← get_eq_getC] at h
        exact Or.inl (Or.inr ⟨(n / 2, a), mem_entries h, by simp only [Prod.mk.injEq, and_true]; omega⟩)
      · rw [show (n % 2 == 1) = false by simpa using h1, Bool.cond_false, ← get_eq_getC] at h
        exact Or.inr ⟨(n / 2 - 1, a), mem_entries h, by simp only [Prod.mk.injEq, and_true]; omega⟩

end

end LeanVM.Guest.Exec.Trie

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Check (getF)

variable {κ : ℕ}

@[expose] public section

/-- **A heap contract's entry in the table**: the function's entry pc, its heap signature, its entry and return
frame cells, its parameter and returned word counts. -/
structure HcEnt where
  entry : ℕ
  h : HSig
  ent : List ℕ
  ret : List ℕ
  np : ℕ
  nr : ℕ
  deriving DecidableEq

/-- The table's entry of core data on its own heap contract. -/
noncomputable def hcEnt (Cf : CFun) : HcEnt :=
  ⟨Cf.frame.entry, Cf.H.sig, Cf.frame.sig.entry, Cf.frame.sig.ret, Cf.fn.params.length, retN Cf.fn.body⟩

/-- The table's entry at pc `t`, if any. -/
def hcFind (tab : List HcEnt) (t : ℕ) : Option HcEnt := tab.find? fun e ↦ e.entry == t

/-- No entry of the table at pc `t`. -/
def hcNone (tab : List HcEnt) (t : ℕ) : Bool := tab.all fun e ↦ e.entry != t

/-- **The contracts of the table**: at a table entry its heap contract, elsewhere the mode signature's. -/
noncomputable def ctOf (img : MemoryImage κ) (tab : List HcEnt) : Mode.Cts := fun t ↦
  (hcFind tab t).map fun e ↦ heapCtrL img e.h e.ent e.ret e.np e.nr

/-- **Core data `Cf` of `K` agrees with the table**: at its own entry the table holds its heap contract iff
`Cf.hc`; at each callee entry of its environment the table holds the callee's heap contract iff `Cf.hcs` names
the callee, at the signature `Cf` assumes of it. -/
noncomputable def ctB (tab : List HcEnt) (K : Mode.Cert) (Cf : CFun) : Bool :=
  (bif Cf.hc then decide (hcFind tab K.F.entry = some ⟨K.F.entry, Cf.H.sig, K.F.sig.entry, K.F.sig.ret,
    Cf.fn.params.length, retN Cf.fn.body⟩) else hcNone tab K.F.entry) &&
  bif Cf.hcs.isEmpty then tab.all (fun e ↦ (K.E.sigs.get e.entry).isNone)
  else K.E.sigs.entries.all fun p ↦
    match (getF Cf.X.ents p.1).bind (fun f ↦ (Cf.hcs.lookup f).map fun q ↦ (f, q)) with
    | some (f, q) => decide (hcFind tab p.1 = some ⟨p.1, Cf.sigOf f, p.2.entry, p.2.ret, q.1, q.2⟩)
    | none => hcNone tab p.1

theorem hcFind_none {tab : List HcEnt} {t : ℕ} (h : hcNone tab t = true) : hcFind tab t = none := by
  unfold hcFind
  rw [List.find?_eq_none]
  intro e he
  have := List.all_eq_true.mp h e he
  simpa using this

theorem hcFind_some {tab : List HcEnt} {t : ℕ} {e : HcEnt} (h : hcFind tab t = some e) : e ∈ tab ∧ e.entry = t :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem hcFind_get {tab : List HcEnt} {t : ℕ} {sigs : Trie Mode.Sig}
    (h : (tab.all fun e ↦ (sigs.get e.entry).isNone) = true) {G : Mode.Sig} (hG : sigs.get t = some G) :
    hcFind tab t = none := by
  cases hf : hcFind tab t with
  | none => rfl
  | some e =>
    obtain ⟨he, het⟩ := hcFind_some hf
    have := List.all_eq_true.mp h e he
    rw [het, hG] at this
    cases this

theorem ctOf_none {img : MemoryImage κ} {tab : List HcEnt} {t : ℕ} (h : hcFind tab t = none) :
    ctOf img tab t = none := by
  simp [ctOf, h]

/-- **The table's contracts are the ones core data agreeing with it assumes.** -/
theorem ctOk_of_ctB {img : MemoryImage κ} {tab : List HcEnt} {K : Mode.Cert} {Cf : CFun} (h : ctB tab K Cf = true) :
    CtOk img (ctOf img tab) K Cf := by
  unfold ctB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun t G hG ↦ ?_⟩
  · cases hc : Cf.hc
    · rw [hc, Bool.cond_false] at h1
      rw [Bool.cond_false]
      exact ctOf_none (hcFind_none h1)
    · rw [hc, Bool.cond_true, decide_eq_true_iff] at h1
      simp only [ctOf, h1, Option.map_some]
      rfl
  · cases hs : Cf.hcs.isEmpty
    · rw [hs, Bool.cond_false, List.all_eq_true] at h2
      have hp := h2 (t, G) (Trie.mem_entries hG)
      simp only at hp
      cases hb : (getF Cf.X.ents t).bind (fun f ↦ (Cf.hcs.lookup f).map fun q ↦ (f, q)) with
      | none =>
        rw [hb] at hp
        rw [ctOf_none (hcFind_none hp)]
        cases hg : getF Cf.X.ents t with
        | none => rfl
        | some f =>
          rw [hg, Option.bind_some] at hb
          simp only [Option.map_eq_none_iff] at hb
          simp [hcAt, hb]
      | some fq =>
        obtain ⟨f, q⟩ := fq
        rw [hb, decide_eq_true_iff] at hp
        rw [Option.bind_eq_some_iff] at hb
        obtain ⟨f', hf', hq⟩ := hb
        rw [Option.map_eq_some_iff] at hq
        obtain ⟨q', hq', hqe⟩ := hq
        simp only [Prod.mk.injEq] at hqe
        obtain ⟨rfl, rfl⟩ := hqe
        simp only [ctOf, hp, Option.map_some, hf', Option.bind_some, hcAt, hq']
        rfl
    · rw [hs, Bool.cond_true] at h2
      rw [ctOf_none (hcFind_get h2 hG)]
      have hn : Cf.hcs = [] := List.isEmpty_iff.mp hs
      cases getF Cf.X.ents t <;> simp [hcAt, hn]

end

end LeanVM.Guest.CoreMode
