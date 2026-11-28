module

public import LeanVM.Guest.Complete.Agg.Compose

/-!
# `aggregate_claims`' callees' regions

Each callee's region at the honest data lies in `main`'s buffers or the node's own buffers
(`AReg`): `agg_reg0`, `agg_reg1`, `agg_reg2`, `agg_regbs`, `agg_reg3`, by `own_aB` and `mBase_lt`.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Node LeanVM.Guest.B1.Main

@[expose] public section

section
variable {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {cover : List E} {c fp : ℕ}

theorem aReg_own {j i : ℕ} (hj : j < 11) (hl : aB c w.children.length j ≤ i)
    (ho : i < aB c w.children.length j + (aBufs w.children.length).getD j 0) : AReg al s w cover c fp i := by
  have := own_aB (c := c) (m := w.children.length) (cert := B2C.cert) (fp := fp) (f := "aggregate_claims")
    (es := aEs (aV al s w cover c)) hj (o := i - aB c w.children.length j) (by omega)
  exact Or.inr (by rwa [Nat.add_sub_cancel' hl] at this)

theorem aReg_main {j i : ℕ} (hj : j < 10) (hl : mBase (mainCounts s w) j ≤ i)
    (ho : i < mBase (mainCounts s w) j + (mainCounts s w).bufs.getD j 0) : AReg al s w cover c fp i := by
  have := mBase_lt (m := mainCounts s w) hj (o := i - mBase (mainCounts s w) j) (by omega)
  exact Or.inl (Or.inl (by rwa [Nat.add_sub_cancel' hl] at this))

theorem aBufs_getD (m : ℕ) : (aBufs m).getD 1 0 = m ∧ (aBufs m).getD 2 0 = m ∧
    (aBufs m).getD 3 0 = 13 * (m + 1) ∧ (aBufs m).getD 5 0 = 126 ∧ (aBufs m).getD 6 0 = m ∧
    (aBufs m).getD 7 0 = 2 * (m + 1) ∧ (aBufs m).getD 0 0 = 51 ∧ (aBufs m).getD 8 0 = 25 ∧
    (aBufs m).getD 9 0 = 25 ∧ (aBufs m).getD 10 0 = m + 1 := by
  simp [aBufs]

theorem mBufs_getD : (mainCounts s w).bufs.getD 5 0 = 2 * w.children.length ∧
    (mainCounts s w).bufs.getD 6 0 = 55 * w.children.length ∧
    (mainCounts s w).bufs.getD 7 0 = 26 * w.children.length := by
  simp [MainCounts.bufs, mainCounts]

theorem agg_reg0 : ∀ j < w.children.length, ∀ i, A0Reg (aB c w.children.length 3) (mBase (mainCounts s w) 5 + 0)
    (mBase (mainCounts s w) 6 + 0) (aB c w.children.length 1) (mBase (mainCounts s w) 7 + 0)
    (aB c w.children.length 2) j i → AReg al s w cover c fp i := by
  intro j hj i h
  obtain ⟨b1, b2, b3, -⟩ := aBufs_getD w.children.length
  obtain ⟨m5, m6, m7⟩ := mBufs_getD (s := s) (w := w)
  rcases h with h | h | h | h | h | h
  · exact aReg_own (j := 3) (by norm_num) (by omega) (by rw [b3]; omega)
  · exact aReg_main (j := 5) (by norm_num) (by omega) (by rw [m5]; omega)
  · exact aReg_main (j := 6) (by norm_num) (by omega) (by rw [m6]; omega)
  · exact aReg_own (j := 1) (by norm_num) (by omega) (by rw [b1]; omega)
  · exact aReg_main (j := 7) (by norm_num) (by omega) (by rw [m7]; omega)
  · exact aReg_own (j := 2) (by norm_num) (by omega) (by rw [b2]; omega)

theorem agg_reg1 : ∀ j < w.children.length, ∀ i, A1Reg (aB c w.children.length 1) (aB c w.children.length 5 + 62)
    (mBase (mainCounts s w) 6 + 55 * j) (aB c w.children.length 6) j i → AReg al s w cover c fp i := by
  intro j hj i h
  obtain ⟨b1, -, -, b5, b6, -⟩ := aBufs_getD w.children.length
  obtain ⟨-, m6, -⟩ := mBufs_getD (s := s) (w := w)
  rcases h with h | h | h | h
  · exact aReg_own (j := 1) (by norm_num) (by omega) (by rw [b1]; omega)
  · exact aReg_own (j := 5) (by norm_num) (by omega) (by rw [b5]; omega)
  · exact aReg_main (j := 6) (by norm_num) (by omega) (by rw [m6]; omega)
  · exact aReg_own (j := 6) (by norm_num) (by omega) (by rw [b6]; omega)

theorem agg_reg2 : ∀ j < w.children.length, ∀ i, A2Reg (aB c w.children.length 7) (aB c w.children.length 1)
    (aB c w.children.length 2) (aB c w.children.length 6) (mBase (mainCounts s w) 7 + 26 * j) j i →
    AReg al s w cover c fp i := by
  intro j hj i h
  obtain ⟨b1, b2, -, -, b6, b7, -⟩ := aBufs_getD w.children.length
  obtain ⟨-, -, m7⟩ := mBufs_getD (s := s) (w := w)
  rcases h with h | h | h | h | h
  · exact aReg_own (j := 7) (by norm_num) (by omega) (by rw [b7]; omega)
  · exact aReg_own (j := 1) (by norm_num) (by omega) (by rw [b1]; omega)
  · exact aReg_own (j := 2) (by norm_num) (by omega) (by rw [b2]; omega)
  · exact aReg_own (j := 6) (by norm_num) (by omega) (by rw [b6]; omega)
  · exact aReg_main (j := 7) (by norm_num) (by omega) (by rw [m7]; omega)

theorem agg_regbs : ∀ i, bsReg (aB c w.children.length 0 + 1) (aB c w.children.length 8) i →
    AReg al s w cover c fp i := by
  intro i h
  obtain ⟨-, -, -, -, -, -, b0, b8, -⟩ := aBufs_getD w.children.length
  rcases h with h | h
  · exact aReg_own (j := 0) (by norm_num) (by omega) (by rw [b0]; omega)
  · exact aReg_own (j := 8) (by norm_num) (by omega) (by rw [b8]; omega)

theorem agg_reg3 : ∀ j < w.children.length, ∀ i, A3Reg (aB c w.children.length 1) (aB c w.children.length 2)
    (aB c w.children.length 10) (aB c w.children.length 7) (mBase (mainCounts s w) 6 + 55 * j)
    (mBase (mainCounts s w) 7 + 26 * j) (aB c w.children.length 9) j i → AReg al s w cover c fp i := by
  intro j hj i h
  obtain ⟨b1, b2, -, -, -, b7, -, -, b9, b10⟩ := aBufs_getD w.children.length
  obtain ⟨-, m6, m7⟩ := mBufs_getD (s := s) (w := w)
  rcases h with h | h | h | h | h | h | h
  · exact aReg_own (j := 1) (by norm_num) (by omega) (by rw [b1]; omega)
  · exact aReg_own (j := 2) (by norm_num) (by omega) (by rw [b2]; omega)
  · exact aReg_own (j := 10) (by norm_num) (by omega) (by rw [b10]; omega)
  · exact aReg_own (j := 7) (by norm_num) (by omega) (by rw [b7]; omega)
  · exact aReg_main (j := 6) (by norm_num) (by omega) (by rw [m6]; omega)
  · exact aReg_main (j := 7) (by norm_num) (by omega) (by rw [m7]; omega)
  · exact aReg_own (j := 9) (by norm_num) (by omega) (by rw [b9]; omega)

end

end
end LeanVM.Guest.Complete.Agg
