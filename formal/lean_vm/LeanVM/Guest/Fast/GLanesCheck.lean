module

public import LeanVM.Guest.Fast.GLanes
public import LeanVM.Guest.Word

/-!
# `gLanes`, checked

`gLanes_eq`: `gLanes[k]` is the lane of `g^k` (`gpowK`), by kernel evaluation of the successive
powers (`lanesFrom`), a product each. This module imports the table and `Guest/Word.lean` alone (`Fast/Firewall.lean`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters

@[expose] public section

/-- The lanes of `x, x·g, x·g², …`, `n` of them: a product each. -/
def lanesFrom : ℕ → K → List ℕ
  | 0, _ => []
  | n + 1, x => x.lane.toNat :: lanesFrom n (x * g)

theorem lanesFrom_pow : ∀ (n a : ℕ),
    lanesFrom n (g ^ a) = (List.range' a n).map fun k ↦ (g ^ k).lane.toNat
  | 0, _ => rfl
  | n + 1, a => by
      rw [lanesFrom, ← pow_succ, lanesFrom_pow n (a + 1), List.range'_succ, List.map_cons]

theorem gLanes_eq : gLanes = (List.range 256).map fun k ↦ (gpowK k).lane.toNat := by
  have h : gLanes = lanesFrom 256 1 := by decide +kernel
  have h0 := lanesFrom_pow 256 0
  rw [pow_zero] at h0
  rw [h, h0, List.range_eq_range']
  refine List.map_congr_left fun k hk => ?_
  rw [List.mem_range'_1] at hk
  rw [gpowK, powBin_eq 128 g 1 k (by omega), one_mul]

end
end LeanVM.Guest.Fast
