module

public import NativeVm.Code.Phase3.FormsBlocks
public import NativeVm.Code.Phase3.FormsCode

/-!
# The bus forms of a side: the data's bounds

`dOk side D`, checked for each side's data by `decide +kernel` (`dOk_sideD`): every block's owner is a
table, it has at most `31` entries, each with a slot of the side's weights, a monomial of degree at
most two in columns below `92` (below `KECCAK`'s output lanes for the other tables) and a coefficient
below `2^31`; at most `51` blocks; every owner's form has at most `formCap` monomials; the data's
words fit the scratch, each below `2^31`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open NativeVm.Model LeanVM.Parameters

/-- The side's slot weights' count. -/
def slotN (side : Nat) : Nat := if side = 2 then 1 else 16

/-- An entry's bounds, in a block of owner `o`. -/
def entOk (side o : Nat) (e : DEnt) : Bool :=
  decide (e.1 < slotN side) && decide (e.2.1.length ≤ 2) &&
    e.2.1.all (fun a ↦ decide (a < 92) && (decide (o = 5) || decide (a < 40))) &&
    decide (e.2.2 < 2 ^ 31)

/-- A block's bounds. -/
def blkOk (side : Nat) (b : DBlk) : Bool :=
  decide (b.1 < 6) && decide (b.2.length ≤ 31) && b.2.all (entOk side b.1)

/-- The data's bounds. -/
def dOk (side : Nat) (D : List DBlk) : Bool :=
  D.all (blkOk side) && decide (D.length ≤ 51) &&
    (List.range 6).all (fun o ↦ decide ((ownerShape D o).length ≤ formCap)) &&
    decide ((encode side D).length ≤ 4096) && (encode side D).all (fun w ↦ decide (w < 2 ^ 31))

theorem dOk_push : dOk 0 pushD = true := by decide +kernel
theorem dOk_pull : dOk 1 pullD = true := by decide +kernel
theorem dOk_count : dOk 2 countD = true := by decide +kernel

theorem dOk_sideD {side : Nat} (h : side < 3) : dOk side (sideD side) = true := by
  unfold sideD
  rcases (show side = 0 ∨ side = 1 ∨ side = 2 by omega) with rfl | rfl | rfl
  · exact dOk_push
  · exact dOk_pull
  · exact dOk_count

end NativeVm.Code.P3
