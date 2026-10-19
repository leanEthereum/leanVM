/-
  LeanVM.Guest.B1.Main.Restrict

  Layouts of buffers in memory; the restricted readers, from `Memory/Restrict.lean`.
-/

module

public import LeanVM.Guest.Memory.Restrict
public import LeanVM.Guest.B1.Main.Basic

/-!
# Layouts

Buffers at given addresses (`Layout`), a memory holding them (`MemL`) and their addresses
(`RegionL`). The restricted readers and the pure-function lemmas are `Memory/Restrict.lean`'s,
exported here under their names.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

export LeanVM.Guest.Memory (restrict restrict_supp restrict_of loadHolds_restrict loads_of_supp
  loadsR_of_supp loadsRKids_of_supp relIn_of_rel_supp restrict_supp' atomEqns_read_pure eqns_read_pure
  eqnsKids_read_pure relAtIn_uniform_of_supp)

/-! ## Layouts -/

/-- Buffers at `g^b` holding `xs`. -/
abbrev Layout : Type := List (ℕ × List E)

/-- The memory holds a layout. -/
def MemL (rd : Reader) (L : Layout) : Prop := ∀ q ∈ L, ReadsAt rd (ofK (gpow q.1)) q.2

/-- The addresses of a layout. -/
def RegionL (L : Layout) (i : ℕ) : Prop := ∃ q ∈ L, q.1 ≤ i ∧ i < q.1 + q.2.length

theorem addr_ofK (b k : ℕ) : (ofK (gpow b)).limb 0 * gpow k = gpow (b + k) := by
  rw [limb_ofK]; exact (pow_add _ _ _).symm

theorem memL_append {rd : Reader} {L L' : Layout} : MemL rd (L ++ L') ↔ MemL rd L ∧ MemL rd L' := by
  simp only [MemL, List.mem_append]
  exact ⟨fun h => ⟨fun q hq => h q (Or.inl hq), fun q hq => h q (Or.inr hq)⟩,
    fun h q hq => hq.elim (h.1 q) (h.2 q)⟩

theorem memL_nil {rd : Reader} : MemL rd [] ↔ True := by simp [MemL]

theorem memL_cons {rd : Reader} {q : ℕ × List E} {L : Layout} :
    MemL rd (q :: L) ↔ ReadsAt rd (ofK (gpow q.1)) q.2 ∧ MemL rd L := by
  simp only [MemL, List.mem_cons, forall_eq_or_imp]

/-- **A layout held survives restricting the memory to it.** -/
theorem memL_restrict {rd : Reader} {L : Layout} {S : ℕ → Prop} (h : MemL rd L)
    (hS : ∀ i, RegionL L i → S i) : MemL (restrict rd S) L := fun q hq k hk =>
  loadHolds_restrict (h q hq k hk) ⟨q.1 + k, addr_ofK _ _, hS _ ⟨q, hq, by omega, by omega⟩⟩

/-- **Two memories holding a layout agree on it.** -/
theorem memL_agree {rd rd' : Reader} {L : Layout} (h : MemL rd L) (h' : MemL rd' L) :
    ∀ i, RegionL L i → rd (gpow i) = rd' (gpow i) := by
  rintro i ⟨q, hq, h1, h2⟩
  have a := (h q hq (i - q.1) (by omega)).2
  have b := (h' q hq (i - q.1) (by omega)).2
  rw [addr_ofK, show q.1 + (i - q.1) = i by omega] at a b
  rw [a, b]

/-! ## Reading a layout's buffers -/

theorem readsAt_append' {rd : Reader} {p : E} {xs ys : List E} :
    ReadsAt rd p (xs ++ ys) ↔ ReadsAt rd p xs ∧ ReadsAt rd (p * gen ^ xs.length) ys := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · have := h k (by simp; omega)
      rwa [List.getElem_append_left hk] at this
    · have := h (xs.length + k) (by simp; omega)
      rw [List.getElem_append_right (by omega)] at this
      simp only [Nat.add_sub_cancel_left] at this
      rw [loadHolds_mul_gen_pow]; exact this
  · rintro ⟨h1, h2⟩ k hk
    rcases Nat.lt_or_ge k xs.length with hk' | hk'
    · rw [List.getElem_append_left hk']; exact h1 k hk'
    · rw [List.getElem_append_right hk']
      have := h2 (k - xs.length) (by simp at hk; omega)
      rw [loadHolds_mul_gen_pow, show xs.length + (k - xs.length) = k by omega] at this
      exact this

theorem readsAt_flatMap_of {α : Type} {rd : Reader} {f : α → List E} {w : ℕ} :
    ∀ (l : List α) {p : E}, (∀ a ∈ l, (f a).length = w) → ReadsAt rd p (l.flatMap f) →
      ∀ c (hc : c < l.length), ReadsAt rd (p * gen ^ (w * c)) (f l[c])
  | [], _, _, _, c, hc => absurd hc (by simp)
  | a :: l, p, hw, h, c, hc => by
    rw [List.flatMap_cons, readsAt_append'] at h
    rcases c with _ | c
    · simpa using h.1
    · have := readsAt_flatMap_of l (fun b hb => hw b (List.mem_cons_of_mem _ hb)) h.2 c
        (by simpa using hc)
      rw [hw a List.mem_cons_self, mul_assoc, ← pow_add, show w + w * c = w * (c + 1) by ring]
        at this
      simpa using this

theorem readsAt_range_flatMap {rd : Reader} {p : E} {m w : ℕ} {f : ℕ → List E}
    (hw : ∀ c < m, (f c).length = w) (h : ReadsAt rd p ((List.range m).flatMap f)) :
    ∀ c < m, ∀ k < w, LoadHolds rd p (w * c + k) ((f c).getD k 0) := by
  intro c hc k hk
  have := readsAt_flatMap_of (List.range m) (fun a ha => hw a (List.mem_range.mp ha)) h c
    (by simpa using hc)
  simp only [List.getElem_range] at this
  rw [← loadHolds_mul_gen_pow, List.getD_eq_getElem _ _ (by rw [hw c hc]; exact hk)]
  exact this k (by rw [hw c hc]; exact hk)

/-! ## Pure subtrees, uniformly -/


end
end LeanVM.Guest.B1.Main
