/-
  LeanVM.Guest.B1.Main.Cover

  The coverage argument of `main` (G:3207-3291): `T` writers marking `T` slots of a write-once
  table with distinct marks fill every slot, and each slot's writer certifies it.
-/

module

public import LeanVM.Guest.B1.Main.Children

/-!
# Coverage

`main` gives every one of its `T` writers (raw signatures, the direct DA, every child's claims) a
distinct mark `g^e`, `e < T`, which it stores in its slot of the coverage table, below `T`; the
running count ends at `T` (`written[n_children] == n_total`). A memory holds one word per address,
so the slots are distinct, and `T` of them fill the table (`Pigeonhole.cover_of_writeOnce`):
whatever a writer certifies of its slot holds of every slot (`cover_all`).

`exists_segment` places a mark in the children's partition of the counts; `exists_list` and
`exists_forall₂` build the witness's lists by choice.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- **The coverage table**: if each mark `g^e`, `e < T`, sits in a slot below `T` that it
certifies, every slot below `T` is certified. -/
theorem cover_all {rd : Reader} {cover : E} {T : ℕ} (hT : T < 2 ^ 34) {Good : ℕ → Prop}
    (hw : ∀ e < T, ∃ s < T, LoadHolds rd cover s (gen ^ e) ∧ Good s) : ∀ s < T, Good s := by
  classical
  choose! slot hslot hload hgood using hw
  have hcov := cover_of_writeOnce (N := T) (M := T) (slot := slot) (mark := fun e => gen ^ e)
    (mem := fun s => cellAt rd cover s) hslot
    (fun i hi j hj h => gen_pow_inj' (by omega) (by omega) h)
    (fun i hi => cellAt_of_load (hload i hi)) le_rfl
  intro s hs
  obtain ⟨e, ⟨he, hse⟩, -⟩ := hcov s hs
  rw [← hse]
  exact hgood e he

/-- A mark between the first and the last count lies in one child's segment. -/
theorem exists_segment (b : ℕ → ℕ) (hmono : ∀ c, b c ≤ b (c + 1)) {e : ℕ} (h1 : b 0 ≤ e) :
    ∀ m, e < b m → ∃ c < m, b c ≤ e ∧ e < b (c + 1)
  | 0, h2 => absurd h1 (by omega)
  | m + 1, h2 => by
    by_cases h : e < b m
    · obtain ⟨c, hc, h3, h4⟩ := exists_segment b hmono h1 m h
      exact ⟨c, by omega, h3, h4⟩
    · exact ⟨m, by omega, by omega, h2⟩

/-- Choices below `m` as a list. -/
theorem exists_list {α : Type} {P : ℕ → α → Prop} {m : ℕ} (h : ∀ j < m, ∃ v, P j v) :
    ∃ l : List α, l.length = m ∧ ∀ j (hj : j < l.length), P j l[j] := by
  classical
  refine ⟨List.ofFn fun j : Fin m => Classical.choose (h j j.2), by simp, fun j hj => ?_⟩
  have hj' : j < m := by simpa using hj
  simp only [List.getElem_ofFn]
  exact Classical.choose_spec (h j hj')

/-- A relation every element has a partner in relates the list to a list. -/
theorem exists_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ (l : List α), (∀ a ∈ l, ∃ b, R a b) → ∃ hs : List β, List.Forall₂ R l hs
  | [], _ => ⟨[], List.Forall₂.nil⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (by simp)
    obtain ⟨hs, hhs⟩ := exists_forall₂ l fun x hx => h x (by simp [hx])
    exact ⟨b :: hs, List.Forall₂.cons hb hhs⟩

end
end LeanVM.Guest.B1.Main
