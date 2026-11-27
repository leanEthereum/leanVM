/-
  LeanVM.Guest.Bridge.PairFast

  The computed hints' data check over the certificate's cells packed in a trie, for the kernel: equal to
  `pairChk`, whose cell map walks the certificate's cell list at every lookup.
-/

module

public import LeanVM.Guest.Bridge.PairDefs
public import LeanVM.Guest.Bridge.JumpCellsPack

/-!
# The computed hints' check, by a trie

`pairChk extra locs n body` reads a value's cell as `locs.getD v.idx 0`, a walk of the certificate's cell
list. `pairChkF` packs the list once into the trie the alignment context uses (`buildT`, `packGo`) and reads
each cell from it (`locT`), after checking that every cell fits its digit; `pairChk_of_fast` gives
`pairChk` from it, so that the generated checks (`Bridge/PairChk/`) run the trie's.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Guest.Core
open LeanVM.Guest.Exec (Trie)

@[expose] public section

/-- **The computed hints' check, by a trie**: every certificate cell fits its digit, and `pairChkAt` over the
packed cells' trie. -/
noncomputable def pairChkF (extra : List (ℕ × ℕ)) (locs : List ℕ) (n : ℕ) (body : List Stmt) : Bool :=
  locs.all (fun c ↦ Nat.blt c (2 ^ cellBits)) &&
    (buildT 32 (packGo locs 0 0)).seq fun t ↦ pairChkAt extra (locT t) n body

end

public section

private theorem pairChkAt_congr {extra : List (ℕ × ℕ)} {loc₁ loc₂ : ℕ → ℕ} {n : ℕ} (body : List Stmt)
    (h : ∀ v, cellOk extra loc₁ n v = cellOk extra loc₂ n v) :
    pairChkAt extra loc₁ n body = pairChkAt extra loc₂ n body := by
  have : pairAtomOk extra loc₁ n (spine body) = pairAtomOk extra loc₂ n (spine body) := by
    funext a
    cases a <;> simp only [pairAtomOk, bufOk, h]
  rw [pairChkAt, pairChkAt, this]

/-- **`pairChk` from the trie's check.** -/
theorem pairChk_of_fast {extra : List (ℕ × ℕ)} {locs : List ℕ} {n : ℕ} {body : List Stmt}
    (h : pairChkF extra locs n body = true) : pairChk extra locs n body = true := by
  simp only [pairChkF, Trie.seq_eq, Bool.and_eq_true] at h
  have hc : ∀ v, cellOk extra (locT (buildT 32 (packGo locs 0 0))) n v = cellOk extra (locs.getD · 0) n v := by
    intro v
    simp only [cellOk]
    by_cases hi : v.idx < 2 ^ 30
    · rw [locT_buildT h.1 hi]
    · have hb : Nat.blt v.idx (2 ^ 30) = false := Bool.eq_false_iff.mpr fun h' ↦ hi (by simpa using h')
      simp only [hb, Bool.and_false, Bool.false_and]
  rw [pairChk, ← pairChkAt_congr body hc]
  exact h.2

end

end LeanVM.Guest.Bridge
