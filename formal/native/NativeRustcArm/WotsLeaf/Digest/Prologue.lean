module

public import NativeRustcArm.WotsLeaf.Digest.Exec
public import NativeRustcArm.WotsLeaf.Input
public import NativeRustcArm.WotsLeaf.Addr
public import NativeRustcArm.Hasher.Bytes

/-!
# The prologue's facts

From the entry's machine and the prologue `b0` run in the frame: the frame's invariant
(`frame_of_entry`: SP the base, X29, the saved registers' bytes written (`saved_of_covers`), the
writes in the frame, the mapped bytes kept), the slots `e`, `hi` and the message digest's
address (`prologueSlots`).
-/

namespace NativeRustcArm.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcArm.Sym LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The registers the prologue saves, in the frame's order. -/
def savedRegs : List XReg := [.X29, .X30, .X28, .X27, .X26, .X25, .X24, .X23, .X22, .X21, .X20, .X19]

/-- Each saved register's 8 bytes are a write of it (decided on the literal state). -/
def savedOK (S : SState) : Bool :=
  (List.range 12).all fun k ↦ covers S.mem 0 (2656 + 8 * k) 8 (.reg (savedRegs.getD k .X0))

/-- The writes are in the frame (region 0). -/
def inFrame (S : SState) : Bool := S.mem.all fun w ↦ w.r == 0 && decide (w.off + w.n ≤ 2752)

/-- The prologue's slots: `e` at 24, `hi` at 28 (`L1`), the message digest's address at 1776. -/
def Run.prologueSlots (r : Run) : List Slot := [(24, 4, u32Bytes r.e), (28, 4, u32Bytes r.hi)]

end

public section

/-- Words' bytes in memory, a word at a time. -/
theorem bytesAt_words {d : DataMem} :
    ∀ (ws : List UInt64) (a : BitVec 64),
      (∀ k (hk : k < ws.length), BytesAt d (a + BitVec.ofNat 64 (8 * k)) (wordBytes ws[k])) →
      BytesAt d a (Native.Keccak.wordsBytes ws)
  | [], _, _ => fun _ h ↦ absurd h (by simp [Native.Keccak.wordsBytes])
  | w :: ws, a, h => by
    rw [show Native.Keccak.wordsBytes (w :: ws) = wordBytes w ++ Native.Keccak.wordsBytes ws from rfl]
    refine BytesAt.append (BytesAt.zero (h 0 (by simp))) ?_
    rw [length_wordBytes]
    refine bytesAt_words ws _ fun k hk ↦ ?_
    rw [addr_add_add, show 8 + 8 * k = 8 * (k + 1) by omega]
    exact h (k + 1) (by simp; omega)

variable {r : Run} [Labels]

/-- The bytes of a register's value: its word's. -/
theorem bytes_reg (m : MachineData) (x : XReg) :
    (List.range 8).map (byteOf ((Sym.reg x).eval (r.env m))) = wordBytes (m.regs.getXReg x) := by
  rw [Hasher.wordBytes_ofBitVec]
  rfl

/-- **The saved registers' bytes** a block wrote. -/
theorem saved_of_covers {m₀ m : MachineData} {S : SState} (hm : Match (r.env m₀) S m)
    (h : savedOK S = true) (hm₀ : ∀ x, m₀.regs.getXReg x = r.m0.regs.getXReg x) :
    BytesAt m.dmem (r.off 2656) (savedBytes r.m0) := by
  unfold savedBytes
  refine bytesAt_words _ _ fun k hk ↦ ?_
  simp only [List.length_map] at hk
  have hk' : k < 12 := by simpa using hk
  have hc : covers S.mem 0 (2656 + 8 * k) 8 (.reg (savedRegs.getD k .X0)) = true :=
    List.all_eq_true.mp h k (List.mem_range.mpr hk')
  have hb := bytesAt_write_val hm (b := r.base) (sz := 2752) rfl (by omega) hc
  rw [bytes_reg, hm₀] at hb
  rw [Run.off, addr_add_add, List.getElem_map]
  convert hb using 3
  rw [savedRegs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]

/-- A write of the frame is in the stack area. -/
theorem stackArea_of_inFrame (hpre : r.Pre) {m₀ : MachineData} {S : SState}
    (h : inFrame S = true) {p : BitVec 64} (hp : Written (r.env m₀) S p) : r.StackArea p := by
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hp
  have := List.all_eq_true.mp h w hw
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  obtain ⟨hr, hn⟩ := this
  rw [hr] at hb
  simp only [Run.env, Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  rw [r.stackArea_iff hpre]
  omega

/-- **The frame's invariant after the prologue.** -/
theorem frame_of_entry (hpre : r.Pre) {m : MachineData} {S : SState}
    (hm : Match (r.env r.m0) S m) (hwf : (r.env r.m0).WF) (hsp : S.sp = .ptr 0 0)
    (hx29 : S.reg .X29 = some (.ptr 0 2656)) (hin : inFrame S = true) (hsv : savedOK S = true) :
    r.Frame m := by
  refine ⟨?_, ?_, saved_of_covers hm hsv fun _ ↦ rfl, fun p hp ↦ ?_, hm.kept hwf⟩
  · rw [hm.sp, hsp]
    show r.base + BitVec.ofInt 64 0 = r.base
    simp
  · rw [hm.regs .X29 _ hx29]
    exact eval_ptr0 _ _ _
  · exact hm.get?_mem0 hwf fun hw ↦ hp (stackArea_of_inFrame hpre hin hw)

/-- The frame's bytes written with `v` (decided on the literal state). -/
theorem frame_covers {m m' : MachineData} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (r.env m vars) S m') {o n : Nat} (ho : o + n ≤ 2752) {v : Sym}
    (hc : covers S.mem 0 o n v = true) :
    BytesAt m'.dmem (r.off o) ((List.range n).map (byteOf (v.eval (r.env m vars)))) :=
  bytesAt_write_val hm (b := r.base) (sz := 2752) rfl ho hc

omit [Labels] in
theorem range_take (f : Nat → UInt8) (n k : Nat) :
    ((List.range n).map f).take k = (List.range (min k n)).map f := by
  rw [← List.map_take, List.take_range]

/-- **The prologue's slots and the message digest's address** from its writes. -/
theorem prologue_slots {m : MachineData} {S : SState} (hm : Match (r.env r.m0) S m)
    (h24 : covers S.mem 0 24 4 (.reg .X3) = true)
    (h28 : covers S.mem 0 28 4 (.un (.ubfm 9 8) .W32 (.reg .X2)) = true)
    (h1 : covers S.mem 0 1776 4 (.reg .X3) = true)
    (h2 : covers S.mem 0 1780 2 (.un (.ubfm 9 8) .W32 (.reg .X2)) = true)
    (h3 : covers S.mem 0 1782 1 (.un (.ubfm 25 24) .W32 (.reg .X2)) = true)
    (h4 : covers S.mem 0 1783 1 (.lit 12) = true) (h5 : covers S.mem 0 1784 8 (.lit 0) = true) :
    SlotsAt r m (r.prologueSlots ++ [(1776, 16, r.addr 12 0)]) := by
  have e24 := frame_covers hm (by decide) h24
  have e28 := frame_covers hm (by decide) h28
  have e1 := frame_covers hm (by decide) h1
  have e2 := frame_covers hm (by decide) h2
  have e3 := frame_covers hm (by decide) h3
  have e4 := frame_covers hm (by decide) h4
  have e5 := frame_covers hm (by decide) h5
  have hE : (List.range 4).map (byteOf ((Sym.reg .X3).eval (r.env r.m0))) = u32Bytes r.e :=
    bytes_e _
  have hH : (List.range 4).map (byteOf ((Sym.un (.ubfm 9 8) .W32 (.reg .X2)).eval (r.env r.m0))) =
      u32Bytes r.hi := bytes_hi _
  rw [hE] at e24 e1
  rw [hH] at e28
  have e2' : BytesAt m.dmem (r.off 1780) ((u32Bytes r.hi).take 2) := by
    rw [← hH, range_take]
    exact e2
  have e3' : BytesAt m.dmem (r.off 1782) (((u32Bytes r.hi).drop 2).take 1) := by
    rw [show r.hi = layerHi (r.m0.regs.getXReg .X2).toBitVec.toNat 0 from rfl, ← byte_hi2]
    exact e3
  rw [show (Sym.lit 12).eval (r.env r.m0) = BitVec.ofNat 64 12 from rfl, bytes_byte] at e4
  rw [show (Sym.lit 0).eval (r.env r.m0) = BitVec.ofNat 64 0 from rfl, bytes_zero] at e5
  refine ⟨⟨rfl, by norm_num, e24⟩, ⟨rfl, by norm_num, e28⟩,
    ⟨by simp [Run.addr, address, length_u32Bytes], by norm_num, ?_⟩, trivial⟩
  rw [Run.addr_eq]
  refine BytesAt.append e1 ?_
  rw [length_u32Bytes, r.off_add]
  refine BytesAt.append e2' ?_
  rw [List.length_take, length_u32Bytes, r.off_add]
  refine BytesAt.append e3' ?_
  rw [List.length_take, List.length_drop, length_u32Bytes, r.off_add]
  refine BytesAt.append ?_ ?_
  · exact e4
  · rw [List.length_singleton, r.off_add]
    exact e5

end

end NativeRustcArm.WotsLeafProof
