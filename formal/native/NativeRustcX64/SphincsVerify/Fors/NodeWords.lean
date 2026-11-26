module

public import NativeRustcX64.SphincsVerify.Fors.State
public import NativeRustcX64.Sym.Sound.Shift

/-!
# A FORS node's words (x86-64)

What `b56` computes for a node at height `z < 10` of tree `c < 24` from the leaf index `l < 1024`:
the bit that orders the children (`bit_eval`: the carry from `btq`), the height's
word (`bytes_height`), the node's index word (`bytes_nodeIndex`: `c << (9 - z)` plus `l >> (z + 1)`,
the shift count `9 - z` from `movb $9, %cl; subb %dl, %cl`), the node's address in the pieces
`b56` writes (`nodeAdrs_eq`); a load's bytes (`bytes_load`) and 16 bytes stored by two 8-byte
writes of loaded values (`write16`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Fors

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym LeanVM.Protocol.KeccakHash

/-- The carry ordering a node's children: bit `z` (RCX) of the leaf index (`72(%rsp)`). -/
@[expose] public def bitC : SBool :=
  .cmp .bit .W64 (.load 0 72 8) (.reg .rcx)

public section

theorem testBit_eq (l z : Nat) : l.testBit z = !decide (l >>> z &&& 1 = 0) := by
  rw [Nat.testBit, Nat.and_comm]
  cases h : (1 &&& l >>> z) == 0 <;> simp_all

/-- **The bit ordering a node's children**: the carry from `btq`. -/
theorem bit_eval [Labels] {env : Env} {l z : Nat} (hz : z < 10)
    (hl : env.load 0 72 8 = BitVec.ofNat 64 l)
    (hc : env.regs .rcx = BitVec.ofNat 64 z) :
    bitC.eval env = !decide (l >>> z &&& 1 = 0) := by
  simp only [bitC, SBool.eval, Sym.eval, CmpOp.apply, low_W64, hc, hl, Width.bits]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show z < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show z < 64 by omega), BitVec.getLsbD_ofNat]
  simpa [show z < 64 by omega] using testBit_eq l z

/-- The height's word, as `b56` computes it. -/
theorem bytes_height (z : Nat) :
    (List.range 4).map (byteOf (UnOp.apply .trunc .W32 (UnOp.apply .bswap .W32
      (UnOp.apply .trunc .W32 (BinOp.apply .add .W64 (BitVec.ofNat 64 z) (BitVec.ofNat 64 1)))))) =
      be32 (z + 1).toUInt32 := by
  rw [bytes4_trunc, bytes_bswap32]
  congr 1
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat', Nat.toUInt32_eq, UInt32.toNat_ofNat']
  simp only [BinOp.apply, UnOp.apply, low, ext, BitVec.toNat_setWidth, BitVec.toNat_add,
    BitVec.toNat_ofNat, Width.bits]
  omega

/-- The node's index's shift count, from `movb $9, %cl; subb %dl, %cl`. -/
@[expose] def clW (z : Nat) : BitVec 64 :=
  BinOp.apply .merge .W8
    (BinOp.apply .merge .W8 (BinOp.apply .add .W64 (BitVec.ofNat 64 z) (BitVec.ofNat 64 1))
      (BitVec.ofNat 64 9))
    (BinOp.apply .sub .W8
      (BinOp.apply .merge .W8 (BinOp.apply .add .W64 (BitVec.ofNat 64 z) (BitVec.ofNat 64 1))
        (BitVec.ofNat 64 9))
      (UnOp.apply .trunc .W32 (BitVec.ofNat 64 z)))

/-- `c << (9 - z)`, as `b56` computes it. -/
theorem shl_cl : ∀ c < 24, ∀ z < 10,
    (BinOp.apply .shl .W32 (BitVec.ofNat 64 c) (clW z)).toNat =
      c * 2 ^ (9 - z) := by
  decide +kernel

/-- **The node's index word**, as `b56` computes it. -/
theorem bytes_nodeIndex {c z l : Nat} (hc : c < 24) (hz : z < 10) (hl : l < 1024) :
    (List.range 4).map (byteOf (UnOp.apply .trunc .W32 (UnOp.apply .bswap .W32
      (BinOp.apply .add .W32 (BinOp.apply .shl .W32 (BitVec.ofNat 64 c)
          (clW z))
        (BinOp.apply .shr .W64 (BitVec.ofNat 64 l)
          (BinOp.apply .add .W64 (BitVec.ofNat 64 z) (BitVec.ofNat 64 1))))))) =
      be32 ((c <<< (10 - (z + 1))) + (l >>> (z + 1))).toUInt32 := by
  have hshr : (BinOp.apply .shr .W64 (BitVec.ofNat 64 l)
      (BinOp.apply .add .W64 (BitVec.ofNat 64 z) (BitVec.ofNat 64 1))).toNat = l / 2 ^ (z + 1) := by
    simp only [BinOp.apply, low_W64, ext_W64]
    rw [← BitVec.ofNat_add, shiftCount_lit .W64 (z + 1) (by simp [Width.bits]; omega)]
    show (BitVec.ofNat 64 l >>> (z + 1)).toNat = _
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega)]
  rw [bytes4_trunc, bytes_bswap32]
  congr 1
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat', Nat.toUInt32_eq, UInt32.toNat_ofNat', toNat_add32, shl_cl c hc z hz,
    hshr,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  interval_cases z <;> omega

/-- A node's address, in the pieces `b56` writes. -/
theorem nodeAdrs_eq (r : Run) (c z : Nat) :
    r.nodeAdrsOf c z = (be32 0 ++ be32 0) ++ (be64 (r.key 0).tree ++ (be32 3 ++
      (be32 (r.key 0).leaf ++ (be32 (z + 1).toUInt32 ++
        be32 ((c <<< (10 - (z + 1))) + (r.leafOf c >>> (z + 1))).toUInt32)))) := by
  rw [Run.nodeAdrsOf, forsNodeAdrs_eq, adrsBytes, List.append_assoc]
  rfl

variable [Labels]

omit [Labels] in
/-- **A load's bytes**: the `n ≤ 8` bytes loaded are those in memory. -/
theorem bytes_load {env : Env} {k o n : Nat} {bs : List UInt8}
    (h : BytesAt env.mem0 (env.base k + BitVec.ofNat 64 o) bs) (hl : bs.length = n) (hn : n ≤ 8) :
    (List.range n).map (byteOf (env.load k o n)) = bs := by
  apply List.ext_getElem (by simp [hl])
  intro t h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [byteOf_load (by simpa using h1) hn, ← Chains.addr_add_add, h t h2]
  rfl

omit [Labels] in
/-- **A 4-byte load's bytes**, zero-extended. -/
theorem bytes_load4 {env : Env} {k o : Nat} {bs : List UInt8}
    (h : BytesAt env.mem0 (env.base k + BitVec.ofNat 64 o) bs) (hl : bs.length = 4) :
    (List.range 8).map (byteOf (env.load k o 4)) = bs ++ [0, 0, 0, 0] := by
  have hlt : (env.load k o 4).toNat < 2 ^ 32 := by
    unfold Env.load
    have := natOfBytes_lt ((List.range 4).map fun i =>
      (env.mem0.get? (env.base k + BitVec.ofNat 64 (o + i))).getD 0)
    simp only [List.length_map, List.length_range] at this
    rw [ofBytes_natCast, BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact this
  apply List.ext_getElem (by simp [hl])
  intro t h1 h2
  simp only [List.getElem_map, List.getElem_range]
  by_cases ht : t < 4
  · rw [List.getElem_append_left (by omega), byteOf_load ht (by decide), ← Chains.addr_add_add,
      h t (by omega)]
    rfl
  · rw [List.getElem_append_right (by omega)]
    have h8 : 2 ^ 32 ≤ 2 ^ (8 * t) := Nat.pow_le_pow_right (by decide) (by omega)
    simp only [byteOf, Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hlt h8)]
    show UInt8.ofNat 0 = (List.replicate 4 (0 : UInt8))[t - bs.length]'(by simp at h1; simp; omega)
    rw [List.getElem_replicate]
    rfl

/-- **16 bytes stored** by two 8-byte writes of values loaded from 16 bytes `bs`. -/
theorem write16 {env : Env} {S : SState} {m' : MachineData} (hm : Match env S m') {j : Nat}
    {b : BitVec 64} {sz : Nat} (hb : env.regions[j]? = some (b, sz)) {o : Nat}
    (ho : o + 16 ≤ sz) {v₁ v₂ : Sym} (hw₁ : Chains.covers S.mem j o 8 v₁ = true)
    (hw₂ : Chains.covers S.mem j (o + 8) 8 v₂ = true) {k o' : Nat}
    (h₁ : v₁.eval env = env.load k o' 8) (h₂ : v₂.eval env = env.load k (o' + 8) 8)
    {bs : List UInt8} (hl : bs.length = 16)
    (h : BytesAt env.mem0 (env.base k + BitVec.ofNat 64 o') bs) :
    BytesAt m'.dmem (b + BitVec.ofNat 64 o) bs := by
  rw [← List.take_append_drop 8 bs]
  have a₁ := Chains.bytesAt_write_val hm hb (by omega) hw₁
  rw [h₁, bytes_load (bs := bs.take 8) (by simpa using Chains.BytesAt.slice h 0 8)
    (by simp [hl]) (by decide)] at a₁
  have a₂ := Chains.bytesAt_write_val hm hb (by omega) hw₂
  rw [h₂, bytes_load (bs := bs.drop 8) (by
    have := Chains.BytesAt.slice h 8 8
    rwa [Chains.addr_add_add, List.take_of_length_le (by simp [hl])] at this)
    (by simp [hl]) (by decide)] at a₂
  refine Chains.BytesAt.append a₁ ?_
  rw [List.length_take, Nat.min_eq_left (by omega), Chains.addr_add_add]
  exact a₂

end

end NativeRustcX64.SphincsVerifyProof.Fors
