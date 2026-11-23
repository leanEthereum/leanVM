module

public import NativeRustcX64.WotsLeaf.Digest.Exec
public import NativeRustcX64.WotsLeaf.Input
public import NativeRustcX64.Hasher.Bytes

/-!
# The prologue's facts

From the entry's machine and the prologue `b0` run from it (to `memset`'s entry): the frame's
invariant at the callee's entry (`frame_of_entry`: RSP 8 below the base, the saved registers'
bytes written (`saved_of_covers`), the writes in the stack area, the mapped bytes kept), the
slots of the layer, `e` and `out` (`Run.prologueSlots`) and the message digest's address at `112`
(`prologue_slots`).
-/

namespace NativeRustcX64.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcX64.Sym LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The registers the prologue pushes, from the frame's byte `2712` up. -/
def savedRegs : List Reg64 := [.rbx, .r12, .r13, .r14, .r15, .rbp]

/-- Each saved register's 8 bytes are a write of it (decided on the literal state). -/
def savedOK (S : SState) : Bool :=
  (List.range 6).all fun k ↦ covers S.mem 0 (2712 + 8 * k) 8 (.reg (savedRegs.getD k .rax))

/-- The writes are in the frame below the return address or in the call's return slot. -/
def entryWrites (S : SState) : Bool :=
  S.mem.all fun w ↦ (w.r == 0 && decide (w.off + w.n ≤ 2760)) || (w.r == 1 && decide (w.off + w.n ≤ 8))

/-- A 64-bit value's 8 bytes. -/
def regBytes (v : BitVec 64) : List UInt8 := (List.range 8).map (byteOf v)

/-- The prologue's slots: the layer at `8`, `e` at `52`, `out` at `96`. -/
def Run.prologueSlots (r : Run) : List Slot :=
  [(8, 8, regBytes (reg r.m0 .rdx)), (52, 4, u32Bytes r.e), (96, 8, regBytes r.out)]

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

theorem length_regBytes (v : BitVec 64) : (regBytes v).length = 8 := by simp [regBytes]

theorem toNat_take' {w : Nat} (x : BitVec w) (n : Nat) : (x.take n).toNat = x.toNat % 2 ^ n := by
  simp [BitVec.take, BitVec.extractLsb'_toNat]

theorem byteOf_toNat (x : BitVec 64) (t : Nat) :
    (byteOf x t).toNat = x.toNat / 2 ^ (8 * t) % 256 := by
  simp [byteOf]

theorem u8_ext {a b : UInt8} (h : a.toNat = b.toNat) : a = b := UInt8.toNat_inj.mp h

/-- `e`'s bytes: a 32-bit store of ECX. -/
theorem bytes_e (x : BitVec 64) :
    (List.range 4).map (byteOf (UnOp.apply .trunc .W32 x)) =
      u32Bytes (UInt32.ofBitVec (x.setWidth 32)) := by
  have h : (UnOp.apply .trunc .W32 x).toNat = x.toNat % 2 ^ 32 := by
    simp only [UnOp.apply, toNat_ext, toNat_low]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    u32Bytes, Native.XmssVerifier.bytes, List.cons_append, List.cons.injEq, and_true]
  refine ⟨u8_ext ?_, u8_ext ?_, u8_ext ?_, u8_ext ?_⟩ <;> simp [byteOf_toNat, h]

theorem layerHi_toNat' (l : Nat) : (layerHi l 0).toNat = l % 512 * 2 ^ 23 := by
  simp [layerHi, top]
  omega

/-- The third byte of `layer_hi(layer, 0)`: a byte store of `layer << 7`. -/
theorem byte_hi2 (x : BitVec 64) :
    (List.range 1).map (byteOf (UnOp.apply .trunc .W8 (BinOp.apply .shl .W32 x
      (BitVec.ofNat 64 7)))) = ((u32Bytes (layerHi x.toNat 0)).drop 2).take 1 := by
  have h1 : (UnOp.apply .trunc .W8 (BinOp.apply .shl .W32 x (BitVec.ofNat 64 7))).toNat =
      x.toNat * 128 % 2 ^ 32 % 256 := by
    have hs : shiftCount .W32 (BitVec.ofNat 64 7) = 7 := by decide
    simp only [UnOp.apply, BinOp.apply, toNat_ext, toNat_low, BitVec.toNat_shiftLeft, hs,
      Width.bits, Nat.shiftLeft_eq]
    omega
  have h2 := layerHi_toNat' x.toNat
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    u32Bytes, Native.XmssVerifier.bytes, List.cons_append, List.drop_succ_cons, List.drop_zero,
    List.take_succ_cons, List.take_zero, List.cons.injEq, and_true]
  apply u8_ext
  simp [byteOf_toNat, h1, h2]
  omega

/-- The two low bytes of `layer_hi(layer, 0)`. -/
theorem hi_take2 (l : Nat) : (u32Bytes (layerHi l 0)).take 2 = [0, 0] := by
  have h2 := layerHi_toNat' l
  apply List.ext_getElem (by simp [length_u32Bytes])
  intro i h1 _
  simp only [List.length_take, length_u32Bytes] at h1
  rw [List.getElem_take]
  simp only [u32Bytes, Native.XmssVerifier.bytes, List.getElem_map, List.getElem_range]
  apply u8_ext
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> first | (simp [h2]; done) | (simp [h2]; omega)

/-- `0`'s bytes. -/
theorem bytes_zero (n : Nat) :
    (List.range n).map (byteOf (BitVec.ofNat 64 0)) = List.replicate n 0 := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [byteOf]

/-- A byte literal. -/
theorem bytes_byte (c : Nat) :
    (List.range 1).map (byteOf (BitVec.ofNat 64 c)) = [UInt8.ofNat c] := by
  simp only [List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  apply u8_ext
  simp [byteOf_toNat]

/-- **A hash's address in pieces**: `e`, `hi`'s low two bytes, its third, the type and step,
eight zeros. -/
theorem Run.addr_eq (r : Run) (t : UInt8) (step : Nat) :
    r.addr t step = u32Bytes r.e ++ ((u32Bytes r.hi).take 2 ++ (((u32Bytes r.hi).drop 2).take 1 ++
      ([t ||| step.toUInt8 <<< 5] ++ List.replicate 8 0))) := by
  have : (u32Bytes r.hi).take 3 = (u32Bytes r.hi).take 2 ++ ((u32Bytes r.hi).drop 2).take 1 := by
    simp [u32Bytes, Native.XmssVerifier.bytes, List.range_succ]
  simp only [Run.addr, address, tweak, Tweak.withStep, this, List.append_assoc]

variable {r : Run} [Labels]

/-- The bytes of a register's value: its word's. -/
theorem bytes_reg (m : MachineData) (extra : List (BitVec 64 × Nat)) (ret : BitVec 64) (x : Reg64) :
    (List.range 8).map (byteOf ((Sym.reg x).eval (r.envR m extra ret))) =
      wordBytes (UInt64.ofBitVec (reg m x)) := by
  rw [Hasher.wordBytes_ofBitVec]
  rfl

/-- The frame's bytes written with `v` (decided on the literal state). -/
theorem frame_covers {m m' : MachineData} {extra : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {S : SState} (hm : Match (r.envR m extra ret) S m') {o n : Nat} (ho : o + n ≤ 2784) {v : Sym}
    (hc : covers S.mem 0 o n v = true) :
    BytesAt m'.dmem (r.off o) ((List.range n).map (byteOf (v.eval (r.envR m extra ret)))) :=
  bytesAt_write_val hm (b := r.base) (sz := 2784) rfl ho hc

/-- **The saved registers' bytes** a block wrote. -/
theorem saved_of_covers {m₀ m : MachineData} {ret : BitVec 64} {S : SState}
    (hm : Match (r.envR m₀ [] ret) S m) (h : savedOK S = true) (hm₀ : ∀ x, reg m₀ x = reg r.m0 x) :
    BytesAt m.dmem (r.off 2712) (savedBytes r.m0) := by
  unfold savedBytes
  refine bytesAt_words _ _ fun k hk ↦ ?_
  simp only [List.length_map] at hk
  have hk' : k < 6 := by simpa using hk
  have hc : covers S.mem 0 (2712 + 8 * k) 8 (.reg (savedRegs.getD k .rax)) = true :=
    List.all_eq_true.mp h k (List.mem_range.mpr hk')
  have hb := frame_covers hm (by omega) hc
  rw [bytes_reg, hm₀] at hb
  rw [Run.off, addr_add_add, List.getElem_map]
  convert hb using 3
  all_goals obtain _ | _ | _ | _ | _ | _ | k := k <;> first | rfl | (exfalso; omega)

/-- A write of the prologue is in the stack area. -/
theorem stackArea_of_entryWrites (hpre : r.Pre) {m₀ : MachineData} {ret : BitVec 64} {S : SState}
    (h : entryWrites S = true) {p : BitVec 64} (hp : Written (r.envR m₀ [] ret) S p) :
    r.StackArea p := by
  have hc := r.callSp_toNat hpre
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hp
  have := List.all_eq_true.mp h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  rw [r.stackArea_iff hpre]
  rcases this with ⟨hr, hn⟩ | ⟨hr, hn⟩
  · rw [hr] at hb
    cases hb
    omega
  · rw [hr] at hb
    cases hb
    omega

/-- **The frame's invariant after the prologue**, at `memset`'s entry. -/
theorem frame_of_entry (hpre : r.Pre) {m : MachineData} {ret : BitVec 64} {S : SState}
    (hm : Match (r.envR r.m0 [] ret) S m) (hwf : (r.envR r.m0 [] ret).WF)
    (hsp : S.reg .rsp = some (.ptr 0 (-8))) (hin : entryWrites S = true)
    (hsv : savedOK S = true) : r.CallFrame m := by
  refine ⟨?_, saved_of_covers hm hsv fun _ ↦ rfl, fun p hp ↦ ?_, hm.kept hwf⟩
  · unfold reg
    rw [hm.regs .rsp _ hsp, eval_ptr_neg8]
  · exact hm.get?_mem0 hwf fun hw ↦ hp (stackArea_of_entryWrites hpre hin hw)

omit [Labels] in
theorem range_take (f : Nat → UInt8) (n k : Nat) :
    ((List.range n).map f).take k = (List.range (min k n)).map f := by
  rw [← List.map_take, List.take_range]

/-- **The prologue's slots and the message digest's address** from its writes. -/
theorem prologue_slots {m : MachineData} {ret : BitVec 64} {S : SState}
    (hm : Match (r.envR r.m0 [] ret) S m)
    (h8 : covers S.mem 0 8 8 (.reg .rdx) = true)
    (h52 : covers S.mem 0 52 4 (.un .trunc .W32 (.reg .rcx)) = true)
    (h96 : covers S.mem 0 96 8 (.reg .rdi) = true)
    (h1 : covers S.mem 0 112 4 (.un .trunc .W32 (.reg .rcx)) = true)
    (h2 : covers S.mem 0 116 2 (.lit 0) = true)
    (h3 : covers S.mem 0 118 1 (.un .trunc .W8 (.bin .shl .W32 (.reg .rdx) (.lit 7))) = true)
    (h4 : covers S.mem 0 119 1 (.lit 12) = true) (h5 : covers S.mem 0 120 8 (.lit 0) = true) :
    SlotsAt r m (r.prologueSlots ++ [(112, 16, r.addr 12 0)]) := by
  have e8 := frame_covers hm (by decide) h8
  have e52 := frame_covers hm (by decide) h52
  have e96 := frame_covers hm (by decide) h96
  have e1 := frame_covers hm (by decide) h1
  have e2 := frame_covers hm (by decide) h2
  have e3 := frame_covers hm (by decide) h3
  have e4 := frame_covers hm (by decide) h4
  have e5 := frame_covers hm (by decide) h5
  have hE : (List.range 4).map (byteOf ((Sym.un .trunc .W32 (.reg .rcx)).eval
      (r.envR r.m0 [] ret))) = u32Bytes r.e := bytes_e _
  rw [hE] at e52 e1
  rw [show (Sym.lit 12).eval (r.envR r.m0 [] ret) = BitVec.ofNat 64 12 from rfl, bytes_byte] at e4
  rw [show (Sym.lit 0).eval (r.envR r.m0 [] ret) = BitVec.ofNat 64 0 from rfl, bytes_zero] at e5 e2
  have e3' : BytesAt m.dmem (r.off 118) (((u32Bytes r.hi).drop 2).take 1) := by
    rw [show r.hi = layerHi (reg r.m0 .rdx).toNat 0 from rfl, ← byte_hi2]
    exact e3
  refine ⟨⟨length_regBytes _, by norm_num, e8⟩, ⟨by simp [u32Bytes, Native.XmssVerifier.bytes],
    by norm_num, e52⟩, ⟨length_regBytes _, by norm_num, e96⟩,
    ⟨by simp [Run.addr, address, length_u32Bytes], by norm_num, ?_⟩, trivial⟩
  rw [Run.addr_eq, show r.hi = layerHi (reg r.m0 .rdx).toNat 0 from rfl, hi_take2,
    ← show r.hi = layerHi (reg r.m0 .rdx).toNat 0 from rfl]
  refine BytesAt.append e1 ?_
  rw [length_u32Bytes, r.off_add]
  refine BytesAt.append e2 ?_
  rw [show ([0, 0] : List UInt8).length = 2 from rfl, r.off_add]
  refine BytesAt.append e3' ?_
  rw [List.length_take, List.length_drop, length_u32Bytes, r.off_add]
  refine BytesAt.append ?_ ?_
  · exact e4
  · rw [List.length_singleton, r.off_add]
    exact e5

end

end NativeRustcX64.WotsLeafProof
