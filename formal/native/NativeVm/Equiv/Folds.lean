module

public import NativeVm.Equiv.Field

/-!
# Folds under a map

The model's loops are `Array.foldl`s over words where the statement's are `List.foldl`s over field
elements. `foldl_hom` (`Equiv/Field.lean`) carries a fold through a map of the accumulator and of
the elements; `foldl_forall₂` does the same over two lists related pointwise. `getD_map` reads an entry through a map.
-/

@[expose] public section

namespace NativeVm.Equiv

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-! ## Folds -/

theorem foldl_forall₂ {α β α' β' : Type} (φ : α → α') {Q : β → β' → Prop} {f : α → β → α}
    {f' : α' → β' → α'} (h : ∀ a b b', Q b b' → φ (f a b) = f' (φ a) b') :
    ∀ {l : List β} {l' : List β'}, List.Forall₂ Q l l' → ∀ a,
      φ (l.foldl f a) = l'.foldl f' (φ a)
  | [], [], .nil, _ => rfl
  | _ :: _, _ :: _, .cons hb hl, a => by
    rw [List.foldl_cons, List.foldl_cons, ← h _ _ _ hb]
    exact foldl_forall₂ φ h hl _

theorem getD_map {α β : Type} (φ : α → β) (a : Array α) (i : ℕ) (d : α) :
    φ (a.getD i d) = (a.toList.map φ).getD i (φ d) := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem forall₂_map_left {α β γ : Type} {Q : β → γ → Prop} (φ : α → β) {l : List α}
    {l' : List γ} (h : List.Forall₂ (fun a c ↦ Q (φ a) c) l l') :
    List.Forall₂ Q (l.map φ) l' :=
  List.forall₂_map_left_iff.mpr h

end NativeVm.Equiv
