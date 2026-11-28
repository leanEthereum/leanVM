/-
  LeanVM.Guest.B1.VsC.FreeBlock

  A callee's own buffer placed clear of its caller's arrays.
-/

module

public import LeanVM.Parameters.Generator

/-!
# A free block

`CallCompletes` lets a callee place its own words anywhere in `[b, b + n)`, `n` chosen after `b`
and the arguments. A callee storing into a caller's array and into its own `HeapBuf` needs them
apart; the caller's array is known before the callee places its buffer, so the callee takes, among
`F.length + 1` consecutive blocks of `s` indices from `b`, one holding no address of the list `F` of
the caller's addresses (`exists_free_block`): each address lies in at most one block.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters

@[expose] public section

theorem addressOfIndex_add_inj {b u u' : ℕ} (hu : u < 2 ^ 64 - 1) (hu' : u' < 2 ^ 64 - 1)
    (h : addressOfIndex (b + u) = addressOfIndex (b + u')) : u = u' := by
  simp only [addressOfIndex, pow_add] at h
  exact gpow_injOn hu hu' (mul_left_cancel₀ (pow_ne_zero b g_ne_zero) h)

/-- **Among `F.length + 1` blocks of `s` indices from `b`, one avoids every address of `F`.** -/
theorem exists_free_block (F : List K) (b s : ℕ) (h : (F.length + 1) * s ≤ 2 ^ 64 - 1) :
    ∃ t ≤ F.length, ∀ i < s, addressOfIndex (b + t * s + i) ∉ F := by
  by_contra hne
  push Not at hne
  choose i hi hx using hne
  -- each block `t` meets the address at index `φ t` of `F`
  have hφ : ∀ t (ht : t ≤ F.length), ∃ j : Fin F.length, F[j] = addressOfIndex (b + t * s + i t ht) := by
    intro t ht
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem (hx t ht)
    exact ⟨⟨j, hj⟩, e⟩
  choose φ hφe using hφ
  let ψ : Fin (F.length + 1) → Fin F.length := fun t => φ t.1 (Nat.lt_succ_iff.mp t.2)
  have hinj : Function.Injective ψ := by
    intro t t' he
    have e1 := hφe t.1 (Nat.lt_succ_iff.mp t.2)
    have e2 := hφe t'.1 (Nat.lt_succ_iff.mp t'.2)
    simp only [ψ] at he
    rw [he] at e1
    rw [e1, add_assoc, add_assoc] at e2
    have ht := t.2
    have ht' := t'.2
    have hi1 := hi t.1 (Nat.lt_succ_iff.mp t.2)
    have hi2 := hi t'.1 (Nat.lt_succ_iff.mp t'.2)
    have b1 : t.1 * s + i t.1 (Nat.lt_succ_iff.mp t.2) < (F.length + 1) * s := by
      have : (t.1 + 1) * s ≤ (F.length + 1) * s := Nat.mul_le_mul_right _ ht
      nlinarith
    have b2 : t'.1 * s + i t'.1 (Nat.lt_succ_iff.mp t'.2) < (F.length + 1) * s := by
      have : (t'.1 + 1) * s ≤ (F.length + 1) * s := Nat.mul_le_mul_right _ ht'
      nlinarith
    have heq := addressOfIndex_add_inj (by omega) (by omega) e2.symm
    -- the same index in two blocks: the same block
    apply Fin.ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have : (t.1 + 1) * s ≤ t'.1 * s := Nat.mul_le_mul_right _ hlt
      nlinarith
    · have : (t'.1 + 1) * s ≤ t.1 * s := Nat.mul_le_mul_right _ hlt
      nlinarith
  have := Fintype.card_le_of_injective ψ hinj
  simp at this

end
end LeanVM.Guest.B1.VsC
