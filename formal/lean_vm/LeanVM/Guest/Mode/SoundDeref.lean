module

public import LeanVM.Guest.Mode.SoundOp

/-!
# A pointer's word and folds of the walk's state

`names_ofK`, `own_names`: the word a frame cell's pointer names. `Holds.foldl`, `Holds.foldlA`: a fold
of facts each sound is sound.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

theorem names_ofK {n X : ℕ} (hn : n < 2 ^ 63) (h : Names (ofK (g ^ n)) X) : X = n :=
  gpow_inj (by have := h.2; unfold maxCells at this; omega) hn (by simpa using h.1.symm)

/-- The frame cell an own product names. -/
theorem own_names {s : St} (hfp : s.fp < maxCells) {k : Mono} {d : ℕ} (hd : k.ownCell = some d)
    {v : E} (hk : MonoVal s k v) {X : ℕ} (hX : Names v X) : X = s.fp + d := by
  obtain ⟨rfl, hd'⟩ := Mono.ownCell_eq hd
  obtain rfl := hk.unique (MonoVal.own d)
  exact names_ofK (by unfold maxCells at hfp; omega) hX

theorem Holds.foldl {s : St} {α : Type} (f : Abs → α → Abs) :
    ∀ (l : List α) {A : Abs}, Holds s A → (∀ A a, a ∈ l → Holds s A → Holds s (f A a)) →
      Holds s (l.foldl f A)
  | [], _, h, _ => h
  | a :: l, A, h, hf => Holds.foldl f l (hf A a (List.mem_cons_self ..) h)
      fun A' a' hm h' ↦ hf A' a' (List.mem_cons_of_mem _ hm) h'

theorem Holds.foldlA {s : St} {α : Type} (f : Abs → α → Abs) (l : List α) {A : Abs} (h : Holds s A)
    (hf : ∀ A a, a ∈ l → Holds s A → Holds s (f A a)) : Holds s (Mode.foldlA f A l) := by
  rw [foldlA_eq]
  exact Holds.foldl f l h hf

end

end LeanVM.Guest.Mode
