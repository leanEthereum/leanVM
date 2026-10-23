/-
  LeanVM.Guest.B2C.KTempsBase

  The check that a function's temporaries have distinct certificate cells within its frame, and
  its ranges of functions.
-/

module

public import LeanVM.Guest.B2C.Cells

/-!
# The temporaries' cells, checked

`tmpScan M n L 0 0` walks the certificate's cells `L` once: the cell of every value whose index
is a bit of `M` lies in `[2, n)`, no two such cells are equal (the bit set `seen` of the cells
so far), and no bit of `M` lies past `L` (`tmpScan_spec`). `tmpCellsB j ix`: the indices `ix`
are distinct and the scan of compiled function `j`'s cells passes on their bit set.
`TmpsRange a n`: the check holds of the temporaries of the `n` core functions from the `a`-th,
evaluated by the kernel on ranges spread over modules (`KTemps/Part*.lean`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- The scan of the cells `L` from index `k`, the cells of the bits of `M` so far in `seen`. -/
def tmpScan (M n : ℕ) : List ℕ → ℕ → ℕ → Bool
  | [], k, _ => M >>> k == 0
  | c :: cs, k, seen =>
    bif M.testBit k then
      Nat.ble 2 c && Nat.blt c n && !seen.testBit c && tmpScan M n cs (k + 1) (seen ||| 1 <<< c)
    else tmpScan M n cs (k + 1) seen

private theorem testBit_one_shiftLeft (c x : ℕ) : (1 <<< c).testBit x = decide (c = x) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

/-- **What the scan checks**: every bit of `M` from `k` indexes `L`, its cell lies in `[2, n)`
and is not in `seen`, and no other bit's cell is the same. -/
theorem tmpScan_spec {M n : ℕ} : ∀ {L : List ℕ} {k seen : ℕ}, tmpScan M n L k seen = true →
    ∀ x, M.testBit (k + x) = true → ∃ hx : x < L.length, 2 ≤ L[x] ∧ L[x] < n ∧
      seen.testBit L[x] = false ∧
      ∀ x' (hx' : x' < L.length), M.testBit (k + x') = true → L[x'] = L[x] → x' = x
  | [], k, seen, h, x, hb => by
    simp only [tmpScan, beq_iff_eq] at h
    have := Nat.testBit_shiftRight (i := k) (j := x) M
    rw [h, hb] at this
    simp at this
  | c :: cs, k, seen, h, x, hb => by
    cases hk : M.testBit k
    · simp only [tmpScan, hk, Bool.cond_false] at h
      cases x with
      | zero => simp [hk] at hb
      | succ x =>
        obtain ⟨hx, h1, h2, h3, h4⟩ := tmpScan_spec h x (by rwa [show k + 1 + x = k + (x + 1) by omega])
        refine ⟨by simp; omega, h1, h2, h3, fun x' hx' hb' he ↦ ?_⟩
        cases x' with
        | zero => simp [hk] at hb'
        | succ x' =>
          have := h4 x' (by simp at hx'; omega) (by rwa [show k + 1 + x' = k + (x' + 1) by omega]) he
          omega
    · simp only [tmpScan, hk, Bool.cond_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Bool.not_eq_true'] at h
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
      have key : ∀ y, M.testBit (k + 1 + y) = true → ∃ hy : y < cs.length, cs[y] ≠ c ∧
          seen.testBit cs[y] = false := by
        intro y hy
        obtain ⟨hyl, -, -, hs, -⟩ := tmpScan_spec h4 y hy
        simp only [Nat.testBit_or, testBit_one_shiftLeft, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hs
        exact ⟨hyl, fun he ↦ hs.2 he.symm, hs.1⟩
      cases x with
      | zero =>
        refine ⟨by simp, h1, h2, h3, fun x' hx' hb' he ↦ ?_⟩
        cases x' with
        | zero => rfl
        | succ x' =>
          obtain ⟨_, hne, _⟩ := key x' (by rwa [show k + 1 + x' = k + (x' + 1) by omega])
          exact absurd he hne
      | succ x =>
        have hb1 : M.testBit (k + 1 + x) = true := by rwa [show k + 1 + x = k + (x + 1) by omega]
        obtain ⟨hx, g1, g2, -, g4⟩ := tmpScan_spec h4 x hb1
        obtain ⟨_, hne, hs⟩ := key x hb1
        refine ⟨by simp; omega, g1, g2, hs, fun x' hx' hb' he ↦ ?_⟩
        cases x' with
        | zero => exact absurd he.symm hne
        | succ x' =>
          have := g4 x' (by simp at hx'; omega) (by rwa [show k + 1 + x' = k + (x' + 1) by omega]) he
          omega

/-- The temporaries of indices `ix` of compiled function `j` are distinct and have distinct cells
in its frame past the header. -/
noncomputable def tmpCellsB (j : ℕ) (ix : List ℕ) : Bool :=
  idxNodup (ix.map V.n) 0 && tmpScan (idxMask (ix.map V.n)) (fsN j) (certOf j).locs 0 0

/-- The check of core function `i`'s temporaries. -/
noncomputable def TmpsOk (i : ℕ) : Prop :=
  tmpCellsB (i + 1) ((Stmt.tmpsList (coreOf (i + 1)).body).map V.idx) = true

/-- The check of the temporaries of the `n` core functions from the `a`-th. -/
noncomputable def TmpsRange (a n : ℕ) : Prop :=
  ((List.range' a n).all fun i => tmpCellsB (i + 1) ((Stmt.tmpsList (coreOf (i + 1)).body).map V.idx)) = true

theorem TmpsRange.ok {a n : ℕ} (h : TmpsRange a n) {i : ℕ} (h1 : a ≤ i) (h2 : i < a + n) : TmpsOk i := by
  unfold TmpsRange at h
  rw [List.all_eq_true] at h
  exact h i (List.mem_range'_1.mpr ⟨h1, h2⟩)

end
end LeanVM.Guest.B2C
