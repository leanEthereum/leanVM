/-
  LeanVM.Guest.B2C.FsAgree

  The deployed frame sizes agree with the compiler's on every function but `main`, so the words
  bounds at `fsOf` hold at `fs` (`fsAgree_fs`).
-/

module

public import LeanVM.Guest.B2C.Defs
public import LeanVM.Guest.Memory.GuestBoundsAt

namespace LeanVM.Guest.B2C

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- Every frame size past `main`'s is at least the header's two cells. -/
theorem frameSizes_ge_two : (Data.frameSizes.drop 2).all (2 ≤ ·) = true := by decide +kernel

theorem two_le_fsAt {i : ℕ} (hi : i + 2 < Data.frameSizes.length) : 2 ≤ fsAt (i + 2) := by
  have hl : i < (Data.frameSizes.drop 2).length := by simp; omega
  have hm : (Data.frameSizes.drop 2)[i] ∈ Data.frameSizes.drop 2 := List.getElem_mem hl
  have h := List.all_eq_true.mp frameSizes_ge_two _ hm
  simp only [decide_eq_true_eq, List.getElem_drop] at h
  rw [fsAt, List.getD_eq_getElem _ _ hi]
  simpa [Nat.add_comm] using h

/-- **`fs` agrees with `fsOf` on every function of the guest but `main`.** -/
theorem fsAgree_fs : FsAgree fs := by
  intro g hg fn hfn
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (List.mem_of_find?_eq_some hfn)
  have hn : coreProgram[j].name = g := by simpa using List.find?_some hfn
  subst hn
  have hidx := coreProgram_indexOf?_getElem hj
  have hj0 : j ≠ 0 := by
    rintro rfl
    have h0 : (coreProgram[0]'(by rw [coreProgram_length]; decide)).name = "main" := by decide +kernel
    exact hg h0
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hlen : coreProgram.length = 1043 := coreProgram_length
  have h2 := two_le_fsAt (i := i) (by rw [frameSizes_length]; omega)
  unfold fsOf fs
  rw [hidx]
  exact (Nat.max_eq_right h2).symm

end
end LeanVM.Guest.B2C
