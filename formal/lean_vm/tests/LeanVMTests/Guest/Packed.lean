import LeanVM.Guest.Packed.NatLit
import LeanVM.Guest.Packed.PTree
import LeanVM.Guest.Packed.Chunks

/-!
# Packed vectors and maps

`nat_hex%` against Lean's numerals, and the whole-vector tests and the packed map evaluated by the
kernel, on small cases and on vectors of `2^18` lanes of 32 bits built by the kernel; the trees
of packed maps and the chunked vectors on small cases.
-/

namespace LeanVMTests.Guest.Packed

open LeanVM.Guest.Packed LeanVM.Guest.Packed.PMap

example : (nat_hex% "0" : ℕ) = 0 := rfl
example : (nat_hex% "fF" : ℕ) = 255 := rfl
example : (nat_hex% "123456789abcdef0123456789ABCDEF0f" : ℕ) =
    0x123456789abcdef0123456789ABCDEF0f := by decide

-- Long enough to be read in halves.
#guard (nat_hex% "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd" : ℕ) =
    16 ^ 96 - 3

/-- error: nat_hex%: not a string of hexadecimal digits -/
#guard_msgs in
example : (nat_hex% "1_0" : ℕ) = 16 := rfl

/-- error: nat_hex%: not a string of hexadecimal digits -/
#guard_msgs in
example : (nat_hex% "1é" : ℕ) = 16 := rfl

example : lane 0x9a3c 4 2 = 0xa := by decide +kernel
example : fits 4 2 0xff = true := by decide +kernel
example : fits 4 2 0x100 = false := by decide +kernel
example : eqOn 4 1 3 0x1234 0x9235 = true := by decide +kernel
example : eqOn 4 1 3 0x1234 0x9225 = false := by decide +kernel
example : shiftEq 4 3 0x123 0x412 = true := by decide +kernel
example : guarded 4 3 0x777 = true := by decide +kernel
example : guarded 4 3 0x787 = false := by decide +kernel
example : le 4 3 0x123 0x323 = true := by decide +kernel
example : le 4 3 0x124 0x323 = false := by decide +kernel
example : addEq 0x123 0x456 0x579 = true := by decide +kernel
example : rep 8 3 5 = 0x050505 := by decide +kernel
example : mask 4 1 3 = 0xff0 := by decide +kernel
example : nonzero 4 3 0x302 = 0x808 := by decide +kernel

example : get 8 (set 8 (set 8 empty 3 7) 5 9) 3 = some 7 := by decide +kernel
example : get 8 (set 8 (set 8 empty 3 7) 3 9) 3 = some 9 := by decide +kernel
example : get 8 (set 8 empty 3 7) 4 = none := by decide +kernel
example : sub 8 6 (set 8 empty 3 7) (set 8 (set 8 empty 3 7) 5 9) = true := by decide +kernel
example : sub 8 6 (set 8 empty 3 7) (set 8 empty 3 8) = false := by decide +kernel
example : inter 8 6 (set 8 (set 8 empty 3 7) 5 9) (set 8 (set 8 empty 3 7) 5 8) >>> 64 =
    set 8 empty 3 7 >>> 64 := by decide +kernel

example : PTree.get 8 (PTree.set 8 (PTree.set 8 (PTree.full 3) 13 7) 5 9) 13 = some 7 := by decide +kernel
example : PTree.get 8 (PTree.set 8 (PTree.set 8 (PTree.full 3) 13 7) 5 9) 5 = some 9 := by decide +kernel
example : PTree.get 8 (PTree.set 8 (PTree.full 3) 13 7) 21 = none := by decide +kernel
example : PTree.get 8 (.node (.leaf (nat_hex% "50000000000000000")) (.leaf 0)) 0 = some 4 := by decide +kernel

example : Chunks.lane [0x1234, 0x5678] 4 4 5 = 7 := by decide +kernel
example : Chunks.all (guarded 4 4) [0x1234, 0x5677] = true := by decide +kernel
example : Chunks.all (guarded 4 4) [0x1234, 0x5687] = false := by decide +kernel
example : Chunks.all2 (eqOn 4 0 4) [0x1234, 0x5678] [0x1234, 0x5678] = true := by decide +kernel
example : Chunks.all2 (eqOn 4 0 4) [0x1234, 0x5678] [0x1234] = false := by decide +kernel
example : Chunks.all2 (le 4 4) [0x1234, 0x5677] [0x1234, 0x5777] = true := by decide +kernel

/-! At scale: `2^18` lanes of 32 bits, a megabyte each. -/

def n : ℕ := 2 ^ 18
def a : ℕ := rep 32 n 0x1234567
def b : ℕ := a + rep 32 n 0x89

example : fits 32 n b && guarded 32 n a && guarded 32 n b && le 32 n a b &&
    addEq a (rep 32 n 0x89) b && eqOn 32 0 n a a && shiftEq 32 n b b = true := by decide +kernel

example : le 32 n b a = false := by decide +kernel

end LeanVMTests.Guest.Packed
