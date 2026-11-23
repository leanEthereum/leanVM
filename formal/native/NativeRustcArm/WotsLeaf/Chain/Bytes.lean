module

public import NativeRustcArm.WotsLeaf.Chain.Basic

/-!
# A step's address and payload, as `b15` writes them

`b15` builds the step's address at `2504` from the frame's `e` (24), `hi` (28) and `hi >> 16`
(20), the type and step byte `1 | pos << 5` and eight zeros (`addr_bytes`), and the payload at
`1400` from the chain's value at `1384`, the chain's index X28 and eight zeros
(`payload_bytes`), given what its literal post-state writes there.
-/

namespace NativeRustcArm.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcArm.Sym LeanVM.Protocol.KeccakHash

public section

variable {r : Run} [Labels]

/-- **The step's address** at `2504`. -/
theorem addr_bytes {x E : List UInt8} {m m' : MachineData} {S : SState}
    (hm : Match (r.env m) S m') (hK : r.CK x E m) {pos : Nat} (hpos : pos ≤ 2)
    (h22 : Run.RegIs m .X22 (BitVec.ofNat 64 pos))
    (w1 : covers S.mem 0 2504 4 (.load 0 24 4) = true)
    (w2 : covers S.mem 0 2508 2 (.load 0 28 4) = true)
    (w3 : covers S.mem 0 2510 1 (.load 0 20 4) = true)
    (w4 : covers S.mem 0 2511 1 (.bin .orr .W32 (.lit 1) (.un (.shift .LSL 5) .W32 (.reg .X22))) =
      true)
    (w5 : covers S.mem 0 2512 8 (.lit 0) = true) :
    BytesAt m'.dmem (r.off 2504) (r.addr 1 pos) := by
  have a1 : BytesAt m'.dmem (r.off 2504) (u32Bytes r.e) :=
    frame_write_load hm (o := 2504) (o' := 24) (n := 4) (by decide) w1 (length_u32Bytes _)
      (by decide) (CK.slot24 hK)
  have a2 : BytesAt m'.dmem (r.off 2508) ((u32Bytes r.hi).take 2) :=
    bytesAt_write_loadTake hm (r := 0) (o := 2508) (n := 2) (b := r.base) (sz := 2752) rfl
      (by decide) (r' := 0) (o' := 28) (k := 4) w2 (bs := u32Bytes r.hi) (length_u32Bytes _)
      (by decide) (by decide) (CK.slot28 hK)
  have a3 : BytesAt m'.dmem (r.off 2510) ((u32Bytes (r.hi >>> 16)).take 1) :=
    bytesAt_write_loadTake hm (r := 0) (o := 2510) (n := 1) (b := r.base) (sz := 2752) rfl
      (by decide) (r' := 0) (o' := 20) (k := 4) w3 (bs := u32Bytes (r.hi >>> 16))
      (length_u32Bytes _) (by decide) (by decide) (CK.slot20 hK)
  rw [take_hi16] at a3
  have a4 : BytesAt m'.dmem (r.off 2511) [(1 : UInt8) ||| pos.toUInt8 <<< 5] := by
    have := bytesAt_write_val hm (b := r.base) (sz := 2752) rfl (o := 2511) (n := 1) (by decide) w4
    have e22 : (r.env m).regs .X22 = BitVec.ofNat 64 pos := h22
    rw [← byte_tstep hpos, ← e22]
    exact this
  have a5 : BytesAt m'.dmem (r.off 2512) (List.replicate 8 0) := by
    have := bytesAt_write_val hm (b := r.base) (sz := 2752) rfl (o := 2512) (n := 8) (by decide) w5
    rw [← bytes_zero]
    exact this
  rw [Run.addr_eq]
  refine BytesAt.cat a1 (BytesAt.cat a2 (BytesAt.cat a3 (BytesAt.cat a4 a5 rfl) ?_) ?_) ?_
  · rw [List.length_take, List.length_drop, length_u32Bytes]; decide
  · rw [List.length_take, length_u32Bytes]; decide
  · rw [length_u32Bytes]

/-- **The step's payload** at `1400`: the chain's value and the chain's index as a `u128`. -/
theorem payload_bytes {m m' : MachineData} {S : SState} (hm : Match (r.env m) S m') {i : Nat}
    (h28 : Run.RegIs m .X28 (BitVec.ofNat 64 i)) {v : List UInt8} (hv : v.length = 16)
    (hval : BytesAt m.dmem (r.off 1384) v)
    (w1 : covers S.mem 0 1400 8 (.load 0 1384 8) = true)
    (w2 : covers S.mem 0 1408 8 (.load 0 1392 8) = true)
    (w3 : covers S.mem 0 1416 8 (.reg .X28) = true) (w4 : covers S.mem 0 1424 8 (.lit 0) = true) :
    BytesAt m'.dmem (r.off 1400) (v ++ u128Bytes i) := by
  have p1 := frame_copy16 hm (o := 1400) (o' := 1384) (by decide) w1 w2 hv hval
  have p2 : BytesAt m'.dmem (r.off 1416) (wordBytes i.toUInt64) := by
    have := bytesAt_write_val hm (b := r.base) (sz := 2752) rfl (o := 1416) (n := 8) (by decide) w3
    have e28 : (r.env m).regs .X28 = BitVec.ofNat 64 i := h28
    rw [← bytes_word, ← e28]
    exact this
  have p3 : BytesAt m'.dmem (r.off 1424) (List.replicate 8 0) := by
    have := bytesAt_write_val hm (b := r.base) (sz := 2752) rfl (o := 1424) (n := 8) (by decide) w4
    rw [← bytes_zero]
    exact this
  exact BytesAt.cat p1 (BytesAt.cat p2 p3 (by rw [length_wordBytes])) (by rw [hv])

end

end NativeRustcArm.WotsLeafProof
