module

public import NativeRustcX64.SphincsVerify.Digest.LeafA
public import NativeRustcX64.SphincsVerify.Digest.LeafB
public import NativeRustcX64.SphincsVerify.Digest.LeafC
public import NativeRustcX64.SphincsVerify.Digest.LeafD
public import NativeRustc.Sphincs.Model

/-!
# The bit loop's leaf is `digest_fields`' (x86-64)

Turn `c < 24` of `b55` stores leaf `c` of `digest_fields` of `H`, the bytes region 0 holds
(`leaf_eval`): `leafOf H c`.
-/

namespace NativeRustcX64.SphincsVerifyProof.Digest

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym

@[expose] public section

/-- Leaf `i` of `digest_fields` of `H`. -/
def leafOf (H : List UInt8) (i : Nat) : Nat :=
  (List.range 10).foldl (fun v j ↦ v <<< 1 ||| digestBit H (10 * i + j)) 0

end

public section

/-- `digest_fields`' bit, by division. -/
theorem digestBit_eq (d : List UInt8) (p : Nat) :
    digestBit d p = (d.getD (p / 8) 0).toNat / 2 ^ (7 - p % 8) % 2 := by
  have hs : (7 - p % 8) < 8 := by omega
  simp only [digestBit, UInt8.toNat_and, UInt8.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  rw [show (1 : UInt8).toNat = 1 from rfl, Nat.and_one_is_mod]
  congr 3
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem ofNat_shiftLeft_one (v : Nat) :
    BitVec.ofNat 64 (v <<< 1) = BitVec.ofNat 64 v <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- `bitsVal` of bits given as numbers is the number they make. -/
theorem ofNat_bitsVal (f : Nat → Nat) :
    BitVec.ofNat 64 ((List.range 10).foldl (fun v j ↦ v <<< 1 ||| f j) 0) =
      bitsVal fun j ↦ BitVec.ofNat 64 (f j) := by
  simp only [bitsVal, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil, BitVec.ofNat_or, ofNat_shiftLeft_one]
  rfl

theorem bitsVal_congr {b b' : Nat → BitVec 64} (h : ∀ j < 10, b j = b' j) :
    bitsVal b = bitsVal b' := by
  unfold bitsVal
  exact List.foldl_ext _ _ _ fun v j hj ↦ by rw [h j (List.mem_range.mp hj)]

/-- A byte's bit, as the loop extracts it. -/
theorem bit_eq (x : UInt8) (s : Nat) :
    (BitVec.setWidth 64 x.toBitVec >>> s) &&& 1 = BitVec.ofNat 64 (x.toNat / 2 ^ s % 2) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.toNat_lt
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, UInt8.toNat_toBitVec]
  rw [show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]
  have : x.toNat / 2 ^ s % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [Nat.mod_eq_of_lt (show x.toNat < 2 ^ 64 by omega)]
  omega

/-- **Turn `c` of the loop stores leaf `c`** of `digest_fields` of `H`. -/
theorem leaf_eval [Labels] (env : Env) (H : List UInt8) {c : Nat} (hc : c < 24)
    (hx : env.regs .r12 = BitVec.ofNat 64 (10 * c))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.setWidth 64 (H.getD k 0).toBitVec) :
    leafSym.eval env = BitVec.ofNat 64 (leafOf H c) := by
  have e : leafSym.eval env = bitsVal fun j ↦
      (BitVec.setWidth 64 (H.getD ((10 * c + j) / 8) 0).toBitVec >>> (7 - (10 * c + j) % 8)) &&& 1 := by
    by_cases h1 : c < 6
    · exact leaf_A env (fun k ↦ (H.getD k 0).toBitVec) (Nat.zero_le c) h1 hx hb
    by_cases h2 : c < 12
    · exact leaf_B env (fun k ↦ (H.getD k 0).toBitVec) (by omega) h2 hx hb
    by_cases h3 : c < 18
    · exact leaf_C env (fun k ↦ (H.getD k 0).toBitVec) (by omega) h3 hx hb
    · exact leaf_D env (fun k ↦ (H.getD k 0).toBitVec) (by omega) hc hx hb
  rw [e, leafOf, ofNat_bitsVal]
  apply bitsVal_congr
  intro j _
  rw [digestBit_eq, bit_eq]

end

end NativeRustcX64.SphincsVerifyProof.Digest
