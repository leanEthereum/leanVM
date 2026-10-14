module

public import Mathlib.Tactic
-- Reference bodies, not runtime implementations, so that the kernel can evaluate the test vector.
import all Init.Data.Array.Basic
import all Init.Data.Vector.Basic

@[expose] public section

/-!
The BLAKE2s compression function F of RFC 7693, written from the RFC's pseudocode and nothing else.

Words are `BitVec 32`, so `+` is addition modulo `2^32`, `^^^` is XOR and `rotateRight` is the RFC's `>>>`.
-/

namespace LeanVMCircuits.Blake2s.Rfc7693

abbrev Word := BitVec 32

/-- Section 2.6: the initialization vector of BLAKE2s. -/
def IV : Vector Word 8 :=
  #v[0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]

/-- Section 2.7: the message schedule. -/
def SIGMA : Vector (Vector (Fin 16) 16) 10 := #v[
  #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  #v[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
  #v[11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
  #v[7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
  #v[9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
  #v[2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
  #v[12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
  #v[13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
  #v[6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
  #v[10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

/-- Section 3.1: the mixing function G, with BLAKE2s's rotations `(R1, R2, R3, R4) = (16, 12, 8, 7)`. -/
def G (v : Vector Word 16) (a b c d : Fin 16) (x y : Word) : Vector Word 16 :=
  let v := v.set a (v[a] + v[b] + x)
  let v := v.set d ((v[d] ^^^ v[a]).rotateRight 16)
  let v := v.set c (v[c] + v[d])
  let v := v.set b ((v[b] ^^^ v[c]).rotateRight 12)
  let v := v.set a (v[a] + v[b] + y)
  let v := v.set d ((v[d] ^^^ v[a]).rotateRight 8)
  let v := v.set c (v[c] + v[d])
  v.set b ((v[b] ^^^ v[c]).rotateRight 7)

/-- Section 3.2: one round of F, its message words picked by `s = SIGMA[i mod 10]`. -/
def round (v : Vector Word 16) (m : Vector Word 16) (s : Vector (Fin 16) 16) : Vector Word 16 :=
  let v := G v 0 4 8 12 m[s[0]] m[s[1]]
  let v := G v 1 5 9 13 m[s[2]] m[s[3]]
  let v := G v 2 6 10 14 m[s[4]] m[s[5]]
  let v := G v 3 7 11 15 m[s[6]] m[s[7]]
  let v := G v 0 5 10 15 m[s[8]] m[s[9]]
  let v := G v 1 6 11 12 m[s[10]] m[s[11]]
  let v := G v 2 7 8 13 m[s[12]] m[s[13]]
  G v 3 4 9 14 m[s[14]] m[s[15]]

/-- Section 3.2: the compression function F of BLAKE2s (`r = 10`, `w = 32`), the counter `t` a 64-bit word. -/
def F (h : Vector Word 8) (m : Vector Word 16) (t : BitVec 64) (f : Bool) : Vector Word 8 :=
  let v := h ++ IV
  let v := v.set 12 (v[12] ^^^ t.setWidth 32)
  let v := v.set 13 (v[13] ^^^ (t >>> 32).setWidth 32)
  let v := if f then v.set 14 (v[14] ^^^ BitVec.allOnes 32) else v
  let v := (List.finRange 10).foldl (fun v i => round v m SIGMA[i]) v
  Vector.ofFn fun i : Fin 8 => h[i] ^^^ v[i] ^^^ v[i.val + 8]

/-- Appendix B of RFC 7693: the one compression of BLAKE2s-256("abc"), whose result is the published digest. -/
theorem abc :
    (F (IV.set 0 (IV[0] ^^^ 0x01010020)) #v[0x00636261, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 true).toList =
      [0x8C5E8C50, 0xE2147C32, 0xA32BA7E1, 0x2F45EB4E, 0x208B4537, 0x293AD69E, 0x4C9B994D, 0x82596786] := by
  decide +kernel

end LeanVMCircuits.Blake2s.Rfc7693
