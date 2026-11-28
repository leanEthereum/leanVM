module

public import NativeRustcArm.WotsLeaf.Codeword.Loop
public import NativeRustcArm.WotsLeaf.Finish

/-!
# The codeword region's facts

The digest's words as loaded (`load_lo`, `load_hi`), the result without a codeword
(`result_none_top`, `result_none`) and the codeword (`codeword_some`), `lsl #1` (`lsl1`), the
chain loop's state (`Run.AtChain`).
-/

namespace NativeRustcArm.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcArm.Sym LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The chain loop's slots: `out`, the values' address, `hi >> 16`, `e`, `hi`, the codeword `x`,
the ends so far `E`. -/
def Run.chainSlots (r : Run) (x E : List UInt8) : List Slot :=
  [(0, 8, wordBytes r.m0.regs.X0), (8, 8, wordBytes r.m0.regs.X7), (20, 4, u32Bytes (r.hi >>> 16)),
    (24, 4, u32Bytes r.e), (28, 4, u32Bytes r.hi), (380, 58, x), (440, E.length, E)]

/-- **At `b14`, chain `i`** (`.LWotsLeaf_8`): the codeword `x` at 380, the ends of chains
`0 .. i - 1` (`E`, `16 i` bytes) at 440; X28 `i`, X9 the codeword's address, X19 `136`, X21 and
X23 the hashers' buffers, X20 `P`'s address, X22 the chain values'. -/
def Run.AtChain (r : Run) (x : List UInt8) (i : Nat) (E : List UInt8) (m : MachineData) : Prop :=
  i ≤ 58 ∧ E.length = 16 * i ∧ Keep r (r.chainSlots x E) m ∧
    Run.RegIs m .X28 (BitVec.ofNat 64 i) ∧ Run.RegIs m .X9 (r.off 380) ∧
    Run.RegIs m .X19 (BitVec.ofNat 64 136) ∧ Run.RegIs m .X21 (r.off 1976) ∧
    Run.RegIs m .X23 (r.off 1632) ∧ Run.RegIs m .X20 r.m0.regs.X1.toBitVec ∧
    Run.RegIs m .X22 r.m0.regs.X7.toBitVec

end

public section

theorem lsl1 (x : BitVec 64) : UnOp.apply (.ubfm 63 62) .W64 x = x <<< 1 := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  apply BitVec.eq_of_toNat_eq
  simp [evalUBFM, toNat_take'', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem digitsPre_58 (r : Run) : r.digitsPre 58 = digits r.dNum := rfl

theorem digitsPre_56_2 (r : Run) : r.digitsPre 58 = r.digitsPre 56 ++
    [UInt8.ofNat (r.dNum >>> (2 * 56) &&& 3), UInt8.ofNat (r.dNum >>> (2 * 57) &&& 3)] := by
  simp [Run.digitsPre, List.range_succ]

/-- Without the top 12 bits zero, no codeword. -/
theorem result_none_top (r : Run) (h : ¬ r.hiW.toNat < 2 ^ 52) : r.result = none := by
  have hc : codeword r.digest16 = none := by
    rw [codeword, leNat_digest16, Run.dNum, Swar.isCodeword_top _ _ h]
    rfl
  simp only [Run.result, wotsLeaf, messageDigest_eq, hc]

/-- Not a codeword: no result. -/
theorem result_none (r : Run) (h : isCodeword r.dNum = false) : r.result = none := by
  have hc : codeword r.digest16 = none := by
    rw [codeword, leNat_digest16, h]
    rfl
  simp only [Run.result, wotsLeaf, messageDigest_eq, hc]

/-- A codeword: its digits. -/
theorem codeword_some (r : Run) (h : isCodeword r.dNum = true) :
    codeword r.digest16 = some (digits r.dNum) := by
  rw [codeword, leNat_digest16, h]
  rfl

variable {r : Run}

/-- The digest's words as the code loads them. -/
theorem load_lo {m : MachineData} (h : BytesAt m.dmem (r.off 1776) r.digest32) :
    (r.env m).load 0 1776 8 = r.lo := by
  have hs := BytesAt.slice h 0 8
  rw [List.drop_zero] at hs
  exact Env.load_of_bytesAt (by simp [length_digest32]) (BytesAt.zero hs)

theorem load_hi {m : MachineData} (h : BytesAt m.dmem (r.off 1776) r.digest32) :
    (r.env m).load 0 1784 8 = r.hiW := by
  have hs := BytesAt.slice h 8 8
  rw [Run.off, addr_add_add] at hs
  exact Env.load_of_bytesAt (by simp [length_digest32]) hs

end

end NativeRustcArm.WotsLeafProof
