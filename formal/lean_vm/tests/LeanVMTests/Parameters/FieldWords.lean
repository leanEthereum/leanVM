module

public import LeanVM.Parameters.Field
meta import LeanVM.Parameters.Field

/-!
# Tests: the field arithmetic as compiled

`LeanVM.Spec.Fast.FieldWords` and `LeanVM.Spec.Fast.CubicExt` change what `K` and `E`
arithmetic compiles to, never what it is: `mul_eq_mulWords` and `instMul_eq_instMulFast` are
theorems. The compiled checks (`#guard`) below run the word-level product, inverse and the
unrolled cubic product against vectors computed independently (Python's integers: the
carry-less product reduced by `x^64 + x^4 + x^3 + x + 1`, and `y^3 = y + 1`), including the
operands that stop the loop early (`1`) or run it in full (`2^64 - 1`, a top bit). The kernel
checks evaluate `mulWords` and CompPoly's `BF64.mul` on the same words, independently of the
compiler. A wrong vector is a mutation each check rejects (`K.ofBits 0x1A ≠ …` below).
-/

namespace LeanVMTests.Parameters.FieldWords

open LeanVM.Parameters

public section

/-! ## `K` -/

#guard K.ofBits 0xDEADBEEFCAFEBABE * K.ofBits 0x0123456789ABCDEF = K.ofBits 0xFBB6712092FD6A8C
#guard K.ofBits 0xFFFFFFFFFFFFFFFF * K.ofBits 0xFFFFFFFFFFFFFFFF = K.ofBits 0x5555555555555513
#guard K.ofBits 0xDEADBEEFCAFEBABE * 1 = K.ofBits 0xDEADBEEFCAFEBABE
#guard 1 * K.ofBits 0xDEADBEEFCAFEBABE = K.ofBits 0xDEADBEEFCAFEBABE
#guard K.ofBits 0x8000000000000000 * K.ofBits 2 = K.ofBits 0x1B
#guard K.ofBits 0x8000000000000000 * K.ofBits 2 ≠ K.ofBits 0x1A
#guard K.ofBits 0xDEADBEEFCAFEBABE * 0 = 0
#guard (K.ofBits 0xDEADBEEFCAFEBABE)⁻¹ = K.ofBits 0x83958A61CC075A9F
#guard K.ofBits 0xDEADBEEFCAFEBABE * (K.ofBits 0xDEADBEEFCAFEBABE)⁻¹ = 1
#guard (0 : K)⁻¹ = 0

/-- The word-level product and CompPoly's agree in the kernel on a full-length operand. -/
example : BF64.mulWords (K.ofBits 0xDEADBEEFCAFEBABE) (K.ofBits 0x0123456789ABCDEF) =
    BF64.mul (K.ofBits 0xDEADBEEFCAFEBABE) (K.ofBits 0x0123456789ABCDEF) := by
  decide +kernel

/-- … and on the reduction's edge: the top bit times `x`. -/
example : BF64.mulWords (K.ofBits 0x8000000000000000) (K.ofBits 2) = K.ofBits 0x1B := by
  decide +kernel

/-! ## `E` -/

/-- Two words of `E` with limbs that are bignums, small, and all ones. -/
def x : E := E.ofLimbs (K.ofBits 0xDEADBEEFCAFEBABE) (K.ofBits 0x0123456789ABCDEF)
  (K.ofBits 0xFFFFFFFFFFFFFFFF)

/-- See `x`. -/
def z : E := E.ofLimbs (K.ofBits 0x8000000000000001) (K.ofBits 0x1B) (K.ofBits 7)

#guard x * z = E.ofLimbs (K.ofBits 0xE765098025230367) (K.ofBits 0x0951636A4B95918E)
  (K.ofBits 0x010B8A6339E7C2E4)
#guard x * z ≠ E.ofLimbs (K.ofBits 0xE765098025230366) (K.ofBits 0x0951636A4B95918E)
  (K.ofBits 0x010B8A6339E7C2E4)
#guard x * z = z * x
#guard x * 1 = x
#guard x * x⁻¹ = 1
#guard x / x = 1
#guard x ^ 3 = x * x * x
#guard x + z = E.ofLimbs (K.ofBits 0xDEADBEEFCAFEBABE + K.ofBits 0x8000000000000001)
  (K.ofBits 0x0123456789ABCDEF + K.ofBits 0x1B) (K.ofBits 0xFFFFFFFFFFFFFFFF + K.ofBits 7)
#guard y * y * y = y + 1

end
end LeanVMTests.Parameters.FieldWords
