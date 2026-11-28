/-
  LeanVM.Guest.B1.VsC.StackOrder

  The honest order of the stack's block groups passes `certify_stack`'s checks.
-/

module

public import Statement.LeanVmGuestProver
public import Mathlib.Data.List.Sort

/-!
# The honest block group order

The honest prover pushes the stack's block groups in the stack's order (`stackHints`,
`Statement/LeanVmGuestProver.lean`): `mergeSort` of the group indices by size down, then by first
block up. `certify_stack` reads them as `g^gi`, checks `gi < N_STK_GROUPS`, writes each group's
offset once (a repeated group would collide), and checks the rank keys `STK_STRIDE·κ - b0` strictly
falling, each step below `STK_KEY_BOUND = SIZE_BITS·STK_STRIDE`.

`honestOrder_ok`: for any sizes at most `SIZE_BITS - 1 = 33` and first blocks distinct and below
`STK_STRIDE = 53`, the order is a permutation of the groups, and of two consecutive groups `a`, `b`
the keys satisfy `key b < key a` with `key a - key b - 1 < 1802`, stated without subtraction.
-/

namespace LeanVM.Guest.B1.VsC

@[expose] public section

/-- The comparison `stackHints` sorts the groups by: size down, then first block up. -/
def grpCmp (size start : ℕ → ℕ) (g h : ℕ) : Bool :=
  decide (size h < size g) || (decide (size g = size h) && decide (start g ≤ start h))

theorem grpCmp_trans (size start : ℕ → ℕ) (a b c : ℕ) (h1 : grpCmp size start a b)
    (h2 : grpCmp size start b c) : grpCmp size start a c := by
  simp only [grpCmp, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at *
  omega

theorem grpCmp_total (size start : ℕ → ℕ) (a b : ℕ) : grpCmp size start a b || grpCmp size start b a := by
  simp only [grpCmp, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- **The honest order passes `certify_stack`'s checks**: a permutation of the `n` groups, and of
consecutive groups `a` then `b`, `53·size b + start a < 53·size a + start b` (the key `53κ - b0`
falls) and `53·size a + start b < 53·size b + start a + 1 + 1802` (the step is below the bound). -/
theorem honestOrder_ok (n : ℕ) (size start : ℕ → ℕ) (hsz : ∀ g < n, size g ≤ 33)
    (hst : ∀ g < n, start g < 53) (hinj : ∀ g < n, ∀ h < n, start g = start h → g = h) :
    ((List.range n).mergeSort (grpCmp size start)).Perm (List.range n) ∧
      ∀ i (hi : i + 1 < ((List.range n).mergeSort (grpCmp size start)).length),
        let o := (List.range n).mergeSort (grpCmp size start)
        53 * size o[i + 1] + start o[i] < 53 * size o[i] + start o[i + 1] ∧
          53 * size o[i] + start o[i + 1] < 53 * size o[i + 1] + start o[i] + 1 + 1802 := by
  set o := (List.range n).mergeSort (grpCmp size start) with ho
  have hperm : o.Perm (List.range n) := List.mergeSort_perm _ _
  have hsorted : o.Pairwise fun a b ↦ grpCmp size start a b :=
    List.pairwise_mergeSort (grpCmp_trans size start) (grpCmp_total size start) _
  have hnd : o.Nodup := hperm.nodup_iff.mpr (List.nodup_range)
  refine ⟨hperm, fun i hi0 ↦ ?_⟩
  have hi : i + 1 < o.length := hi0
  show 53 * size o[i + 1] + start o[i] < 53 * size o[i] + start o[i + 1] ∧
    53 * size o[i] + start o[i + 1] < 53 * size o[i + 1] + start o[i] + 1 + 1802
  have hmem : ∀ j (hj : j < o.length), o[j] < n := fun j hj ↦
    List.mem_range.mp (hperm.subset (List.getElem_mem hj))
  have ha := hmem i (by omega)
  have hb := hmem (i + 1) hi
  have hc : grpCmp size start o[i] o[i + 1] :=
    List.pairwise_iff_getElem.mp hsorted i (i + 1) (by omega) hi (by omega)
  have hne : o[i] ≠ o[i + 1] := fun h ↦ by
    have := (List.Nodup.getElem_inj_iff hnd).mp h
    omega
  have hsne : start o[i] ≠ start o[i + 1] := fun h ↦ hne (hinj _ ha _ hb h)
  have h1 := hsz _ ha
  have h2 := hsz _ hb
  have h3 := hst _ ha
  have h4 := hst _ hb
  simp only [grpCmp, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
  constructor <;> omega

/-- **The stack's block groups**: eight first blocks, distinct, below `STK_STRIDE = 53`, so
`honestOrder_ok` applies to `stackHints`' order at `start g = (stackBlockGroups stackBlocks).getD g 0`. -/
theorem stackGroups_facts :
    (Prover.stackBlockGroups Protocol.Verifier.stackBlocks).length = 8 ∧
      (Prover.stackBlockGroups Protocol.Verifier.stackBlocks).Nodup ∧
      ∀ s ∈ Prover.stackBlockGroups Protocol.Verifier.stackBlocks, s < 53 := by
  decide +kernel

end
end LeanVM.Guest.B1.VsC
