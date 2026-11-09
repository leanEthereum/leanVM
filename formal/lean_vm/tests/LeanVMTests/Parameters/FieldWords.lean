module

public import LeanVM.Parameters.Field
meta import LeanVM.Parameters.Field

/-!
# Tests: the field arithmetic as compiled

`Statement.Fast.FieldWords` and `Statement.Fast.QuadExt` change what `K` and `E`
arithmetic compiles to, never what it is: `mul_eq_mulWords` and `instMul_eq_instMulFast` are
theorems. The compiled checks (`#guard`) below run the word-level product, inverse and the
unrolled quadratic product against vectors computed independently (arbitrary-precision integers: the
carry-less product reduced by `x^64 + x^4 + x^3 + x + 1`, and `y^2 = x·y + 1`), including the
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
def x : E := E.ofLimbs (K.ofBits 0xDEADBEEFCAFEBABE) (K.ofBits 0xFFFFFFFFFFFFFFFF)

/-- See `x`. -/
def z : E := E.ofLimbs (K.ofBits 0x8000000000000001) (K.ofBits 0x1B)

#guard x * z = E.ofLimbs (K.ofBits 0xE08DD3B6997062EA) (K.ofBits 0x83BF254D58E24F32)
#guard x * z ≠ E.ofLimbs (K.ofBits 0xE08DD3B6997062EB) (K.ofBits 0x83BF254D58E24F32)
#guard x * z = z * x
#guard x * 1 = x
#guard x * x⁻¹ = 1
#guard x / x = 1
#guard x ^ 3 = x * x * x
#guard x + z = E.ofLimbs (K.ofBits 0xDEADBEEFCAFEBABE + K.ofBits 0x8000000000000001)
  (K.ofBits 0xFFFFFFFFFFFFFFFF + K.ofBits 0x1B)
#guard y * y = ofK g * y + 1
-- The vector of `crates/primitives/src/field/gf2_64x2.rs`'s tests (`VECTORS[0]`).
#guard E.ofLimbs (K.ofBits 0x8a1d921ca352a3c3) (K.ofBits 0xa10d04b240699a83) *
    E.ofLimbs (K.ofBits 0x936d4747ab0e6d1c) (K.ofBits 0xe46ab5adb68f9c7d) =
  E.ofLimbs (K.ofBits 0xfbbffa3000b331c0) (K.ofBits 0xbf494d14ce4eadf8)

end
end LeanVMTests.Parameters.FieldWords
