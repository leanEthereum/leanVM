module

public import NativeRustcArm.WotsLeaf.Digest.Region
public import NativeRustc.Digest

/-!
# The digest as a number

The digest's first 16 bytes (`Run.digest16`, the message digest `messageDigest`), its two words as
the machine loads them (`Run.lo`, `Run.hiW`), and the little-endian number they make
(`Run.dNum`, `leNat_digest16`).
-/

namespace NativeRustcArm.WotsLeafProof

open NativeRustc NativeRustc.Keccak NativeRustc.Xmss NativeRustcArm.Sym

@[expose] public section

namespace Run
variable (r : Run)

/-- The message digest: the first 16 bytes. -/
def digest16 : List UInt8 := r.digest32.take 16

/-- The digest's low word as loaded. -/
def lo : BitVec 64 := BitVec.ofInt 64 (Int.ofBytes (r.digest32.take 8))

/-- The digest's high word as loaded. -/
def hiW : BitVec 64 := BitVec.ofInt 64 (Int.ofBytes ((r.digest32.drop 8).take 8))

/-- The digest's number. -/
def dNum : Nat := 2 ^ 64 * r.hiW.toNat + r.lo.toNat

end Run

end

public section

theorem natOfBytes_eq_leNat : ∀ bs : List UInt8, Nat.ofBytes bs = leNat bs
  | [] => rfl
  | b :: bs => by
    show Nat.ofBytes bs * 256 + b.toNat = b.toNat + 256 * leNat bs
    rw [natOfBytes_eq_leNat bs]
    omega

theorem toNat_ofInt_ofBytes' {bs : List UInt8} (hn : bs.length ≤ 8) :
    (BitVec.ofInt 64 (Int.ofBytes bs)).toNat = leNat bs := by
  have := Sym.toNat_ofInt_ofBytes bs hn
  have e : Int.ofBytes bs = (leNat bs : Int) := by rw [Sym.ofBytes_natCast, natOfBytes_eq_leNat]
  rw [e] at this ⊢
  exact_mod_cast this

/-- The message digest is the digest's first 16 bytes. -/
theorem messageDigest_eq (r : Run) :
    messageDigest r.pp r.layer r.e r.rnd r.msg = r.digest16 := rfl

/-- **The digest's number** is the little-endian number of its 16 bytes. -/
theorem leNat_digest16 (r : Run) : leNat r.digest16 = r.dNum := by
  have hl := length_digest32 r
  have h16 : r.digest16 = r.digest32.take 8 ++ (r.digest32.drop 8).take 8 := by
    rw [Run.digest16, show 16 = 8 + 8 from rfl, List.take_add]
  rw [h16, leNat_append, Run.dNum, Run.lo, Run.hiW, toNat_ofInt_ofBytes' (by simp),
    toNat_ofInt_ofBytes' (by simp), List.length_take, hl]
  norm_num
  ring

end

end NativeRustcArm.WotsLeafProof
