module

public import LeanVM.Guest.Fast.XmssTables
public import LeanVM.Guest.B1.Sig.XmssSegT
public import LeanVM.Guest.B1.Sig.WotsSound

/-!
# leanXMSS's tables, checked

The literal tables of `Fast/XmssTables.lean` are the template's numbers, by kernel evaluation.
The arms of a codeword group (`armM`, `B1/Sig/XmssSegT.lean`) take a number of values that
depends on the step's size, the group's digits and whether it folds the encoding alone, so their
bases from the group's (`lxArmOff`, one pass over the `256` arms: `lxRowAux`) and the chain starts
in them (`lxStartRel`, `armStart`'s cell) are numbers relative to the group's base: the tables are
those rows (`lxFold_eq`, `lxRest_eq`, `lxTail_eq`), the groups' sizes `2829` and `2573`
(`lxGroup0_size`, `lxGroup_size`), and the check's layer and window bases are the reader's
(`lxLayer0_end`, `lxLeafK0`, …).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Sig

@[expose] public section

/-- The base after arm `k` from `b` in a group of `n` digits, the step's size `s` (`armM`'s next
base, plus the two outputs arm `0` allocates: `armsM`). -/
def lxArmNext (s n : ℕ) (fold : Bool) (k b : ℕ) : ℕ :=
  let e := walkBase (if k = 0 then s + 1 else s) k 0 n (if fold then b + 1 else b)
  let e := if k % 4 ^ n = 0 then e else e + 1
  if k = 0 then e + 2 else e

/-- The base of arm `k + j`, arm `k` at `b` (`armBaseM`'s). -/
def lxArmOff (s n : ℕ) (fold : Bool) : ℕ → ℕ → ℕ → ℕ
  | _, 0, b => b
  | k, j + 1, b => lxArmOff s n fold (k + 1) j (lxArmNext s n fold k b)

/-- Chain `r`'s start in arm `k` at `a`, relative to the group's base (`armStart`'s cell). -/
def lxStartRel (s : ℕ) (fold : Bool) (k a r : ℕ) : ℕ :=
  if k / 4 ^ r % 4 = 3 then
    6 + (if fold then 1 else 0) + (1 + 3 * (s + 1)) * r + 1 + (s + 1) * 2 + s
  else walkBase (if k = 0 then s + 1 else s) k 0 r (if fold then a + 1 else a)

/-- Row `r` of a group's chain starts, arms `k ..< k + m`, arm `k` at `a`. -/
def lxRowAux (s n : ℕ) (fold : Bool) (r : ℕ) : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | m + 1, k, a => lxStartRel s fold k a r :: lxRowAux s n fold r m (k + 1) (lxArmNext s n fold k a)

/-- A group's table of chain starts: `n` rows over the `256` arms, arm `0` at `6`. -/
def lxRows (n : ℕ) (fold : Bool) : List (List ℕ) :=
  (List.range n).map fun r ↦ lxRowAux 1 n fold r 256 0 6

theorem lxFold_eq : lxFold = lxRows 4 true := by decide +kernel

theorem lxRest_eq : lxRest = lxRows 4 false := by decide +kernel

theorem lxTail_eq : lxTail = lxRows 2 false := by decide +kernel

theorem lxGroup0_size : lxArmOff 1 4 true 0 256 6 = 2829 + 6 := by decide +kernel

theorem lxGroup_size : lxArmOff 1 4 false 0 256 6 = 2573 + 6 := by decide +kernel

theorem lxLayer0_end : (sLayer 0 88 (.n 0)).2.1 = 62605 := by decide +kernel

theorem lxLeafK0 : (sLeafK 0 88).2.1 = 38021 := by decide +kernel

theorem lxWin00 : (sWin0 0 88).2.1 = 50313 := by decide +kernel

theorem lxLeafK1 : (sLeafK 1 62605).2.1 = 100529 := by decide +kernel

theorem lxWin01 : (sWin0 1 62605).2.1 = 112821 := by decide +kernel

end
end LeanVM.Guest.Fast
