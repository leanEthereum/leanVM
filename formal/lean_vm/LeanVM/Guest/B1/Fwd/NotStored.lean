/-
  LeanVM.Guest.B1.Fwd.NotStored

  Whether a read is one of a function's stores, decided fast: by its numbers, its pointer first.
-/

module

public import LeanVM.Guest.Renumber

/-!
# A read that is not a store

A kernel check `a ∉ SL` (a function's stores, `vtSL`, `vsSL`) through the derived
`DecidableEq Atom` compares `a` with every store structurally, about half a millisecond each, and
recomputes `SL` when it is computed: `∀ r < 54, ∀ a ∈ reads r, a ∉ vtSL` took minutes. `notStoredB
ptrs SL` decides a read `.load (.n d) (.n p) off` by numbers: no store goes through `p` (`ptrs`, a
list of the stores' pointers checked once, `SL.all (ptrInB ptrs)`), or none is the read, by its
three numbers (`notStoredB_iff`). A function's store list gets a `Decidable (a ∉ SL)` instance of
high priority from it, so that every `decide` of `a ∉ SL` uses it unchanged (`VtC/NotStored.lean`,
`VerifySub/C/Hon.lean`).
-/

namespace LeanVM.Guest.B1.Fwd

open LeanVM.Guest.Core

@[expose] public section

/-- A store's pointer is among `ptrs`. -/
def ptrInB (ptrs : List ℕ) : Atom → Bool
  | .load _ (.n q) _ => ptrs.contains q
  | _ => false

/-- A store is not the read `.load (.n d) (.n p) off`, by the numbers. -/
def otherLoadB (d p off : ℕ) : Atom → Bool
  | .load (.n d') (.n p') off' => !(p' == p && d' == d && off' == off)
  | _ => true

/-- `a` is none of the stores `SL` whose pointers are among `ptrs`: a read by its numbers, another
atom structurally. -/
def notStoredB (ptrs : List ℕ) (SL : List Atom) : Atom → Bool
  | .load (.n d) (.n p) off => !ptrs.contains p || SL.all (otherLoadB d p off)
  | a => decide (a ∉ SL)

theorem otherLoadB_iff (d p off : ℕ) (b : Atom) :
    otherLoadB d p off b = true ↔ b ≠ .load (.n d) (.n p) off := by
  unfold otherLoadB
  split
  · simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
      Atom.load.injEq, V.mk.injEq, true_and, not_and]
    omega
  · rename_i h
    simp only [true_iff]
    rintro rfl
    exact h d p off rfl

theorem notStoredB_iff {ptrs : List ℕ} {SL : List Atom} (hp : SL.all (ptrInB ptrs) = true)
    (a : Atom) : notStoredB ptrs SL a = true ↔ a ∉ SL := by
  unfold notStoredB
  split
  · rename_i d p off
    rw [Bool.or_eq_true, List.all_eq_true]
    simp only [otherLoadB_iff, Bool.not_eq_true']
    refine ⟨fun h hm ↦ h.elim (fun hc ↦ ?_) (fun h ↦ h _ hm rfl),
      fun h ↦ .inr fun b hb e ↦ h (e ▸ hb)⟩
    have := List.all_eq_true.mp hp _ hm
    simp only [ptrInB] at this
    rw [this] at hc
    exact Bool.false_ne_true hc.symm
  · exact decide_eq_true_iff

end
end LeanVM.Guest.B1.Fwd
