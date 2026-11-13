/-
  LeanVM.Guest.B1.Common.MemSize

  A memory image's size from the words it holds at one pointer.
-/

module

public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.CoreData

/-!
# The memory's size

`mem_size`: a memory image holding `n` words at one pointer has at least `n` words;
`winTabBits_le_of_winTabs`: one holding the window tables has at least `2^winTabBits`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **A memory image holding `n` words at one pointer has at least `n` words.** -/
theorem mem_size_big {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {p : E} {n : ℕ} (hn : n ≤ 2 ^ 33)
    (h : ∀ j < n, ∃ v, LoadHolds L.read p j v) : n ≤ 2 ^ κ := by
  have hκ64 : κ < 64 := by omega
  have hidx : ∀ j : Fin n, ∃ i : Fin (2 ^ κ), p.limb 0 * Parameters.addressOfIndex j =
      Parameters.addressOfIndex i := by
    intro j
    obtain ⟨v, -, hv⟩ := h j j.isLt
    obtain ⟨i, hi, -⟩ := (read_some_iff hκ64 L _ _).mp hv
    exact ⟨i, hi⟩
  choose f hf using hidx
  have hinj : Function.Injective f := by
    intro a b hab
    have ea := hf a
    have eb := hf b
    rw [hab, ← eb] at ea
    have hp : p.limb 0 ≠ 0 := by
      intro h0
      have := hf a
      rw [h0, zero_mul] at this
      exact Parameters.gpow_ne_zero _ this.symm
    have := mul_left_cancel₀ hp ea
    have hlt : ∀ x : Fin n, (x : ℕ) < 2 ^ 64 - 1 := fun x ↦ by have := x.isLt; omega
    exact Fin.ext (gpow_injOn (hlt a) (hlt b) this)
  simpa using Fintype.card_le_of_injective f hinj

theorem mem_size {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {p : E} {n : ℕ} (hn : n ≤ 2 ^ 32)
    (h : ∀ j < n, ∃ v, LoadHolds L.read p j v) : n ≤ 2 ^ κ :=
  mem_size_big hκ L (by omega) h

/-- **A memory image holding the window tables has at least `2^11` words.** -/
theorem winTabBits_le_of_winTabs {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {tabs : E}
    (h : WinTabs L.read tabs) : winTabBits ≤ κ := by
  have hn := mem_size hκ L (p := tabs) (n := 2 ^ 11) (by norm_num) fun j hj ↦ ⟨_, h.lt hj⟩
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hn

end
end LeanVM.Guest.B1
