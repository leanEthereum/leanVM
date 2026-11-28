module

public import NativeRustcX64.Code.Common.Memset.Names

public import NativeRustcX64.SphincsVerify.Tree.Entry
public import NativeRustcX64.SphincsVerify.InlineTh.ByteNF

/-!
# The fold's node: the loop head (x86-64)

At the loop head `b152` with `z` steps done (`AtNode`): the node's children (`Run.children`) go
to `11368`, its address (`Run.nodeAdrs`) to `3048`, `z + 1` to `64`, then `memset` zeroes hasher A
(`nodeA`, to `AtN2`). The node's spills (`NW`: `z + 1`, the path's address, the layer's word)
through a block and a call (`NW.of_match`, `NW.of_call`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcX64.Sym
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcX64.Sphincs.SphincsVerify

public section

/-! ## Bytes -/

/-- A stored truncated `BSWAP` (32-bit) is the big-endian bytes of the low word. -/
theorem bytes_trunc_bswap (x : BitVec 64) :
    (List.range 4).map (byteOf (UnOp.apply .trunc .W32 (UnOp.apply .bswap .W32 x))) =
      be32 (UInt32.ofNat x.toNat) := by
  rw [← bytes_bswap32]
  apply List.map_congr_left
  intro t ht
  exact InlineTh.byteOf_ext_low .W32 _ (by simpa using ht)

/-- The 32-bit word `l << 24` in memory is `be32 l`. -/
theorem bytes_layer {l : Nat} (hl : l < 3) :
    (List.range 4).map (byteOf (UnOp.apply .trunc .W32 (l * 16777216).toUInt64.toBitVec)) =
      be32 l.toUInt32 := by
  interval_cases l <;> decide

/-! ## The node's spills -/

section
variable (r : Run)

/-- **The node's spills**: `z + 1` (`64`), the path's address (`72`), the layer's word (`96`). -/
@[expose] def NW (l z : Nat) (m : MachineData) : Prop :=
  r.WordAt m 56 (z + 1).toUInt64 ∧ r.WordAt m 72 (r.addr (17004 + 16 * pathStart l)) ∧
    r.WordAt m 96 (l * 16777216).toUInt64

end

section
variable {r : Run} [Labels]

/-- **The node's spills after a block** that writes none of `64 .. 104`. -/
theorem NW.of_match (hpre : r.Pre) {l z : Nat} {m m' : MachineData} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (h : NW r l z m) (hm : Match (r.env m vars ret) S m')
    (hwf : (r.env m vars ret).WF) (hn : Run.noWriteIn S 56 48 = true) : NW r l z m' := by
  have n : ∀ o, 56 ≤ o → o + 8 ≤ 104 → Run.noWriteIn S o 8 = true := fun o h1 h2 ↦ by
    simp only [Run.noWriteIn, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hn ⊢
    intro w hw'
    rcases hn w hw' with ⟨h0, h | h⟩ | h
    · exact Or.inl ⟨h0, Or.inl (by omega)⟩
    · exact Or.inl ⟨h0, Or.inr (by omega)⟩
    · exact Or.inr h
  have k := fun {o : Nat} {v : UInt64} (ho : 56 ≤ o) (ho' : o + 8 ≤ 104) (hb : r.WordAt m o v) ↦
    r.bytesAt_kept hpre hm hwf (by rw [length_wordBytes]; omega) hb
      (by rw [length_wordBytes]; exact n o ho ho')
  exact ⟨k (by decide) (by decide) h.1, k (by decide) (by decide) h.2.1,
    k (by decide) (by decide) h.2.2⟩

/-- **The node's spills after a call** above them. -/
theorem NW.of_call (hpre : r.Pre) {l z : Nat} {m m' : MachineData} (hc : r.AtCall m) {a n N : Nat}
    (ha : 560 ≤ a) (han : a + n ≤ 21624) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) (h : NW r l z m) : NW r l z m' :=
  have k := fun {o : Nat} {v : UInt64} (ho : o + 8 ≤ 560) (hb : r.WordAt m o v) ↦
    r.bytesAt_of_call hpre hc han hN hout (by rw [length_wordBytes]; omega)
      (by rw [length_wordBytes]; omega) hb
  ⟨k (by decide) h.1, k (by decide) h.2.1, k (by decide) h.2.2⟩

end

/-! ## The loop head -/

section
variable (r : Run)

/-- **After the node's `memset`**: `NW`, R12 hasher A; hasher A zero, the address at `3048`, the
children at `11368`. -/
@[expose] def AtN2 [Labels] (l : Nat) (e : List (List UInt8)) (z : Nat) (m : MachineData) : Prop :=
  Base r l m ∧ z < heightOf l ∧ NW r l z m ∧ Run.RegIs m .r12 (r.off 4072) ∧
    BytesAt m.dmem (r.off 4072) (List.replicate 344 0) ∧
    BytesAt m.dmem (r.off 3048) (r.nodeAdrs l z) ∧
    BytesAt m.dmem (r.off 11368) (r.children l (r.foldUpTo l e z) z)

end

/-- The bit test of `b152`. -/
@[expose] def bitC : SBool :=
  .cmp .eq .W32 (.bin .and .W32 (.bin .shl .W64 (.lit 1) (.reg .rcx)) (.load 0 208 8)) (.lit 0)

/-- The sibling's index of `b152`. -/
@[expose] def idxS : Sym := .bin .shl .W64 (.reg .rcx) (.lit 4)

variable [Host] {r : Run}

theorem eval_idx {m : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64} {z : Nat}
    (h : Run.RegIs m .rcx (BitVec.ofNat 64 z)) (hz : z < 10) :
    (idxS.eval (r.env m vars ret)).toNat = 16 * z := by
  simp only [idxS, Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
  rw [show m.regs.get64 .rcx = BitVec.ofNat 64 z from h]
  show (BitVec.ofNat 64 z <<< shiftCount .W64 (BitVec.ofNat 64 4)).toNat = 16 * z
  rw [show shiftCount .W64 (BitVec.ofNat 64 4) = 4 by decide, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  omega

omit [Host] in
theorem two_pow_and_eq_zero (n z : Nat) : (2 ^ z &&& n = 0) ↔ n.testBit z = false := by
  constructor
  · intro h
    have := congrArg (fun v ↦ Nat.testBit v z) h
    simpa [Nat.testBit_and, Nat.testBit_two_pow_self] using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hi : z = i
    · subst hi; simp [h]
    · simp [hi]

omit [Host] in
theorem shr_and_one (n z : Nat) : (n >>> z &&& 1 = 0) ↔ n.testBit z = false := by
  rw [Nat.testBit, Nat.and_comm]
  cases h : 1 &&& n >>> z == 0 <;> simp_all

omit [Host] in
/-- The 32-bit test of bit `z` of a `u32`. -/
theorem bit32 (x : UInt32) {z : Nat} (hz : z < 32) :
    (low .W32 (ext .W32 (low .W32 (ext .W64 (low .W64 (BitVec.ofNat 64 1) <<< z)) &&&
      low .W32 x.toUInt64.toBitVec)) == low .W32 (BitVec.ofNat 64 0)) =
      decide (x.toNat >>> z &&& 1 = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj]
  simp only [ext, low, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, UInt64.toNat_toBitVec, UInt32.toNat_toUInt64, Nat.zero_mod,
    show Width.W64.bits = 64 from rfl, show Width.W32.bits = 32 from rfl]
  have hx := x.toNat_lt
  have hz2 : 2 ^ z < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hz
  rw [Nat.shiftLeft_eq, show 1 % 2 ^ 64 % 2 ^ 64 = 1 from rfl, Nat.one_mul,
    Nat.mod_eq_of_lt (a := 2 ^ z) (by omega), Nat.mod_eq_of_lt (a := 2 ^ z) (by omega),
    Nat.mod_eq_of_lt (a := 2 ^ z) (by omega), Nat.mod_eq_of_lt (a := x.toNat) (by omega),
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left (by omega)),
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left (by omega)), shr_and_one,
    two_pow_and_eq_zero]

theorem eval_bitC {m : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64} {z : Nat} {l : Nat}
    (h : Run.RegIs m .rcx (BitVec.ofNat 64 z)) (hz : z < 10)
    (h216 : (r.env m vars ret).load 0 208 8 = (r.key l).leaf.toUInt64.toBitVec) :
    bitC.eval (r.env m vars ret) = decide ((r.key l).leaf.toNat >>> z &&& 1 = 0) := by
  simp only [bitC, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, Env.ofMachine_regs, h216]
  rw [show m.regs.get64 .rcx = BitVec.ofNat 64 z from h,
    show shiftCount .W64 (BitVec.ofNat 64 z) = z by interval_cases z <;> decide]
  exact bit32 _ (by omega)

/-- **A block of the region ending in a call, and the call**: `Base` again, from the block's
facts and the call's change (the frame's bytes `a .. a + n` above the spills). -/
theorem Base.call (hpre : r.Pre) {l : Nat} {m m₁ m' : MachineData} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hB : Base r l m) (hm : Match (r.env m vars ret) S m₁)
    (hwf : (r.env m vars ret).WF) (hsp : S.reg .rsp = some (.ptr 0 (-8)))
    (hw : Run.frameWrites S = true) (hk : keepW S = true) (hbp : S.reg .rbp = some (.ptr 0 560))
    (hS : Saved m₁ m') (hsp' : rspOf m' = rspOf m₁ + 8#64) {a n N : Nat} (ha : 560 ≤ a)
    (han : a + n ≤ 12780) (hN : N ≤ finalizeStack)
    (hout : SameOutside m₁.dmem m'.dmem (r.CallOut m₁ a n N))
    (h14 : S.reg .r14 = some (.label "memcpy") := by rfl) : Base r l m' :=
  Base.of_call hpre hB.1 (hB.atCall hpre hm hwf hsp hw) (hB.2.2.1.of_match hpre hm hwf hk)
    ((hm.regs _ _ hbp).trans (eval_ptr 560)) (hm.regs .r14 _ h14) hS hsp' ha han hN hout


/-- The node's address, from `b152`'s writes. -/
theorem nodeA_adrs {l z : Nat} {m m' : MachineData}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S' : SState} (hm : Match (r.env m vars ret) S' m')
    (hl : l < 3) (hz : z < heightOf l) (h88 : BytesAt m.dmem (r.off 88) (be64 (r.key l).tree))
    (hld96 : (r.env m vars ret).load 0 96 8 = (l * 16777216).toUInt64.toBitVec)
    (hld216 : (r.env m vars ret).load 0 208 8 = (r.key l).leaf.toUInt64.toBitVec)
    (hz1 : (Sym.bin .add .W64 (.reg .rcx) (.lit 1)).eval (r.env m vars ret) =
      BitVec.ofNat 64 (z + 1))
    (wA0 : ∀ i < 4, findWrite 0 (3048 + i) S'.mem = some (.un .trunc .W32 (.load 0 96 8), i))
    (wA1 : ∀ i < 4, findWrite 0 (3052 + i) S'.mem = some (.lit 0, i))
    (wA2 : ∀ i < 8, findWrite 0 (3056 + i) S'.mem = some (.load 0 88 8, i))
    (wA3 : ∀ i < 8, findWrite 0 (3064 + i) S'.mem = some (.lit 33554432, i))
    (wA4 : ∀ i < 4, findWrite 0 (3072 + i) S'.mem =
      some (.un .trunc .W32 (.un .bswap .W32 (.bin .add .W64 (.reg .rcx) (.lit 1))), i))
    (wA5 : ∀ i < 4, findWrite 0 (3076 + i) S'.mem = some (.un .trunc .W32 (.un .bswap .W32
      (.bin .shr .W64 (.load 0 208 8) (.bin .add .W64 (.reg .rcx) (.lit 1)))), i)) :
    BytesAt m'.dmem (r.off 3048) (r.nodeAdrs l z) := by
  have hh := heightOf_le hl
  rw [Run.nodeAdrs, nodeAdrs_eq, show (r.key l).layer = l from rfl]
  refine bytesAt_cat rfl (write_eval hm (by decide) wA0 rfl (by
    simp only [Sym.eval, hld96]; exact bytes_layer hl)) ?_
  refine bytesAt_cat rfl (write_eval hm (by decide) wA1 rfl (by simp only [Sym.eval]; decide)) ?_
  refine bytesAt_cat rfl (write_eval hm (by decide) wA2 rfl (bytes_load h88 rfl (by decide))) ?_
  rw [← List.append_assoc]
  refine bytesAt_cat rfl (write_eval hm (by decide) wA3 rfl (by simp only [Sym.eval]; decide)) ?_
  refine bytesAt_cat rfl (write_eval hm (by decide) wA4 rfl (by
    show (List.range 4).map (byteOf (UnOp.apply .trunc .W32 (UnOp.apply .bswap .W32
      ((Sym.bin .add .W64 (.reg .rcx) (.lit 1)).eval _)))) = _
    rw [hz1, bytes_trunc_bswap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])) ?_
  refine write_eval hm (by decide) wA5 rfl ?_
  show (List.range 4).map (byteOf (UnOp.apply .trunc .W32 (UnOp.apply .bswap .W32
    (BinOp.apply .shr .W64 ((r.env m _ _).load 0 208 8)
      ((Sym.bin .add .W64 (.reg .rcx) (.lit 1)).eval _))))) = _
  rw [hz1, hld216, bytes_trunc_bswap]
  congr 2
  simp only [BinOp.apply, low_W64, ext_W64]
  have hz10 : z < 10 := by omega
  rw [show shiftCount .W64 (BitVec.ofNat 64 (z + 1)) = z + 1 by interval_cases z <;> decide]
  have key : ∀ (x : BitVec 64) (n : Nat), (x.ushiftRight n).toNat = x.toNat >>> n :=
    fun x n ↦ BitVec.toNat_ushiftRight x n
  rw [key, UInt64.toNat_toBitVec, UInt32.toNat_toUInt64]

/-- The node's children, from `b152`'s writes. -/
theorem nodeA_children {l z p : Nat} {e : List (List UInt8)} {m m' : MachineData}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S' : SState} (hm : Match (r.env m vars ret) S' m')
    (hl : l < 3) (hz : z < heightOf l) (hpp : pathStart l = p)
    (hsig : BytesAt m.dmem (r.off 12780) (sigMem r.sig))
    (hV : BytesAt m.dmem (r.off 8296) (r.foldUpTo l e z))
    (hrcx : Run.RegIs m .rcx (BitVec.ofNat 64 z))
    (hld216 : (r.env m vars ret).load 0 208 8 = (r.key l).leaf.toUInt64.toBitVec)
    (wC0 : ∀ i < 8, findWrite 0 (11368 + i) S'.mem = some (.ite bitC (.load 0 8296 8)
      (.loadx 0 (17004 + 16 * p) idxS 8), i))
    (wC1 : ∀ i < 8, findWrite 0 (11368 + 8 + i) S'.mem = some (.ite bitC (.load 0 8304 8)
      (.loadx 0 (17012 + 16 * p) idxS 8), i))
    (wC2 : ∀ i < 8, findWrite 0 (11384 + i) S'.mem = some (.ite (.not bitC) (.load 0 8296 8)
      (.loadx 0 (17004 + 16 * p) idxS 8), i))
    (wC3 : ∀ i < 8, findWrite 0 (11384 + 8 + i) S'.mem = some (.ite (.not bitC) (.load 0 8304 8)
      (.loadx 0 (17012 + 16 * p) idxS 8), i)) :
    BytesAt m'.dmem (r.off 11368) (r.children l (r.foldUpTo l e z) z) := by
  have hh := heightOf_le hl
  have hcur := length_foldUpTo r l e z
  have hsib := length_sibling r hl hz
  have hsibB : BytesAt m.dmem (r.off (17004 + 16 * (p + z))) (r.sibling l z) := by
    have hs := bytesAt_sub hsig (4224 + 16 * (pathStart l + z)) 16
    rw [sig_eq, SigMemBytes.sigMem_node r.sigB r.hsig (by have := pathStart_lt hl; omega), ← sig_eq,
      ← sibling_eq r hz, show 12780 + (4224 + 16 * (pathStart l + z)) = 17004 + 16 * (p + z) by
        rw [hpp]; omega] at hs
    exact hs
  have hbit := eval_bitC (r := r) (vars := vars) (ret := ret) hrcx (by omega) hld216
  have hix := eval_idx (r := r) (vars := vars) (ret := ret) hrcx (by omega)
  have sLo : (List.range 8).map (byteOf ((Sym.loadx 0 (17004 + 16 * p) idxS 8).eval
      (r.env m vars ret))) =
      (r.sibling l z).take 8 := by
    show (List.range 8).map (byteOf ((r.env m _ _).load 0 (17004 + 16 * p +
      (idxS.eval _).toNat) 8)) = _
    rw [hix, show 17004 + 16 * p + 16 * z = 17004 + 16 * (p + z) by omega]
    exact load_lo hsibB hsib
  have sHi : (List.range 8).map (byteOf ((Sym.loadx 0 (17012 + 16 * p) idxS 8).eval
      (r.env m vars ret))) =
      (r.sibling l z).drop 8 := by
    show (List.range 8).map (byteOf ((r.env m _ _).load 0 (17012 + 16 * p +
      (idxS.eval _).toNat) 8)) = _
    rw [hix, show 17012 + 16 * p + 16 * z = 17004 + 16 * (p + z) + 8 by omega]
    exact load_hi hsibB hsib
  have cLo := load_lo (vars := vars) (ret := ret) hV hcur
  have cHi := load_hi (vars := vars) (ret := ret) hV hcur
  unfold Run.children
  by_cases hb : (r.key l).leaf.toNat >>> z &&& 1 = 0
  · rw [Sym.ite_pos hb]
    have hct : bitC.eval (r.env m vars ret)
        = true := by rw [hbit]; exact decide_eq_true hb
    refine bytesAt_cat (by rw [hcur]) (write_16 hm (by decide) hcur wC0 wC1
      (by simp only [Sym.eval, hct, ite_true]; exact cLo)
      (by simp only [Sym.eval, hct, ite_true]; exact cHi)) ?_
    exact write_16 hm (by decide) hsib wC2 wC3
      (by simp only [Sym.eval, SBool.eval, hct, Bool.not_true]; exact sLo)
      (by simp only [Sym.eval, SBool.eval, hct, Bool.not_true]; exact sHi)
  · rw [Sym.ite_neg hb]
    have hcf : bitC.eval (r.env m vars ret)
        = false := by rw [hbit]; exact decide_eq_false hb
    refine bytesAt_cat (by rw [hsib]) (write_16 hm (by decide) hsib wC0 wC1
      (by simp only [Sym.eval, hcf]; exact sLo)
      (by simp only [Sym.eval, hcf]; exact sHi)) ?_
    exact write_16 hm (by decide) hcur wC2 wC3
      (by simp only [Sym.eval, SBool.eval, hcf, Bool.not_false, ite_true]; exact cLo)
      (by simp only [Sym.eval, SBool.eval, hcf, Bool.not_false, ite_true]; exact cHi)

/-- **`b152` and `memset`**, from the symbolic run's facts. -/
theorem nodeA_gen (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtNode r l e z m) {p : Nat}
    (hpp : pathStart l = p) {S' : SState}
    (hrun : exec b152 (nodeS p) = some (S', .call NativeRustcX64.Common.Memset.entryLabel))
    (hsp : S'.reg .rsp = some (.ptr 0 (-8))) (hfw : Run.frameWrites S' = true)
    (hk : keepW S' = true) (hbp : S'.reg .rbp = some (.ptr 0 560))
    (h12 : S'.reg .r12 = some (.ptr 0 4072)) (hx0 : S'.reg .rdi = some (.ptr 0 4072))
    (hx1 : S'.reg .rsi = some (.lit 0)) (hx2 : S'.reg .rdx = some (.lit 344))
    (wA0 : ∀ i < 4, findWrite 0 (3048 + i) S'.mem = some (.un .trunc .W32 (.load 0 96 8), i))
    (wA1 : ∀ i < 4, findWrite 0 (3052 + i) S'.mem = some (.lit 0, i))
    (wA2 : ∀ i < 8, findWrite 0 (3056 + i) S'.mem = some (.load 0 88 8, i))
    (wA3 : ∀ i < 8, findWrite 0 (3064 + i) S'.mem = some (.lit 33554432, i))
    (wA4 : ∀ i < 4, findWrite 0 (3072 + i) S'.mem =
      some (.un .trunc .W32 (.un .bswap .W32 (.bin .add .W64 (.reg .rcx) (.lit 1))), i))
    (wA5 : ∀ i < 4, findWrite 0 (3076 + i) S'.mem = some (.un .trunc .W32 (.un .bswap .W32
      (.bin .shr .W64 (.load 0 208 8) (.bin .add .W64 (.reg .rcx) (.lit 1)))), i))
    (w64 : ∀ i < 8, findWrite 0 (56 + i) S'.mem = some (.bin .add .W64 (.reg .rcx) (.lit 1), i))
    (hnw : Run.noWriteIn S' 72 32 = true)
    (wC0 : ∀ i < 8, findWrite 0 (11368 + i) S'.mem = some (.ite bitC (.load 0 8296 8)
      (.loadx 0 (17004 + 16 * p) idxS 8), i))
    (wC1 : ∀ i < 8, findWrite 0 (11368 + 8 + i) S'.mem = some (.ite bitC (.load 0 8304 8)
      (.loadx 0 (17012 + 16 * p) idxS 8), i))
    (wC2 : ∀ i < 8, findWrite 0 (11384 + i) S'.mem = some (.ite (.not bitC) (.load 0 8296 8)
      (.loadx 0 (17004 + 16 * p) idxS 8), i))
    (wC3 : ∀ i < 8, findWrite 0 (11384 + 8 + i) S'.mem = some (.ite (.not bitC) (.load 0 8304 8)
      (.loadx 0 (17012 + 16 * p) idxS 8), i))
    (h14 : S'.reg .r14 = some (.label "memcpy") := by rfl) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b153Offset ∧ AtN2 r l e z st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b152Offset⟩ := by
  obtain ⟨hB, hz, hrcx, hr12, h72, h96, hV, hbx⟩ := h
  have hl := hB.1
  have hh := heightOf_le hl
  have ret := (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b152Offset + b152.length)).toBitVec
  have hwf := frame_wf' hpre hB (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b152Offset + b152.length)).toBitVec
  have hld72 : (r.env m (fun _ ↦ 0) (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b152Offset + b152.length)).toBitVec).load 0 72 8 =
      r.off (17004 + 16 * p) := by rw [load_word h72, ← hpp]; rfl
  have hm0 : Match (r.env m (fun _ ↦ 0) (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b152Offset + b152.length)).toBitVec)
      (nodeS p) m := r.match_frame hpre hB.2.1
    (show AllOf _ [(Reg64.r14, Sym.label "memcpy"), (.r12, .ptr 0 4072),
      (.rbp, .ptr 0 560), (.rcx, .reg .rcx), (.rbx, .label "memset")] from
      ⟨hB.2.2.2.2, hr12.trans (eval_ptr 4072).symm,
        hB.2.2.2.1.trans (eval_ptr 560).symm, rfl, hbx, trivial⟩) trivial
    ⟨by show (idxS.eval _).toNat < 145; rw [eval_idx hrcx (by omega)]; omega, trivial⟩
    ⟨by show (Sym.load 0 72 8).eval _ = _; rw [Sym.eval, hld72, ← eval_ptr]; rfl, trivial⟩
  refine exec_then (hb161 hp) hrun hwf (fun _ _ ↦ rfl) hm0 fun st hm hpc ↦ ?_
  have hc1 := hB.atCall hpre hm hwf hsp hfw
  have h0 : Run.RegIs st.data .rdi (r.off 4072) := (hm.regs .rdi _ hx0).trans (eval_ptr 4072)
  have h1 : reg st.data .rsi = 0 := hm.regs .rsi _ hx1
  have h2 : (reg st.data .rdx).toNat = 344 := regIs_toNat (hm.regs .rdx _ hx2) (by decide)
  obtain ⟨-, h88, -, -, -, h216, -⟩ := hB.2.2.1
  have hld216 := load_word (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b152Offset + b152.length)).toBitVec) h216
  have hld96 := load_word (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b152Offset + b152.length)).toBitVec) h96
  have hrc : m.regs.get64 .rcx = BitVec.ofNat 64 z := hrcx
  have hz1 : (Sym.bin .add .W64 (.reg .rcx) (.lit 1)).eval
      (r.env m (fun _ ↦ 0) (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b152Offset + b152.length)).toBitVec) =
      BitVec.ofNat 64 (z + 1) := by
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, hrc]
    rw [BitVec.ofNat_add]
  have hA := nodeA_adrs hm hl hz h88 hld96 hld216 hz1 wA0 wA1 wA2 wA3 wA4 wA5
  have hC := nodeA_children hm hl hz hpp hB.2.2.1.1.2 hV hrcx hld216 wC0 wC1 wC2 wC3
  -- the spills
  have h64 : r.WordAt st.data 56 (z + 1).toUInt64 :=
    write_eval hm (by decide) w64 hz1 (by rw [bytes_word]; rfl)
  have h72' := r.bytesAt_kept hpre hm hwf (by rw [length_wordBytes]; decide) h72
    (by rw [length_wordBytes]; simp only [Run.noWriteIn, List.all_eq_true] at hnw ⊢; exact
      fun w hw' ↦ by have := hnw w hw'; simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at this ⊢; omega)
  have h96' := r.bytesAt_kept hpre hm hwf (by rw [length_wordBytes]; decide) h96
    (by rw [length_wordBytes]; simp only [Run.noWriteIn, List.all_eq_true] at hnw ⊢; exact
      fun w hw' ↦ by have := hnw w hw'; simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at this ⊢; omega)
  have h12' : Run.RegIs st.data .r12 (r.off 4072) := (hm.regs .r12 _ h12).trans (eval_ptr 4072)
  -- the call
  refine call_then hpc hc.2.1 (r.memset_pre hpre hc1 h0 h2 (by decide))
    fun st' hpc' hsp' hpost ↦ ?_
  obtain ⟨hz0, hout, hS⟩ := r.memset_out h0 h2 hpost
  have kc := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21624)
    (hd : o + bs.length ≤ 4072 ∨ 4072 + 344 ≤ o) (hb : BytesAt st.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hc1 (by decide) (by decide) hout ho hd hb
  have hlc := length_children r (cur := r.foldUpTo l e z) hl hz (length_foldUpTo r l e z)
  have hla := length_nodeAdrs r l z
  have hA' := kc (bs := r.nodeAdrs l z) (by omega) (by omega) hA
  have hC' := kc (bs := r.children l (r.foldUpTo l e z) z) (by omega) (by omega) hC
  have hB' := Base.call hpre hB hm hwf hsp hfw hk hbp hS hsp' (a := 4072) (n := 344) (N := 0)
    (by decide) (by decide) (Nat.zero_le _) hout h14
  have hN' : NW r l z st'.data :=
    NW.of_call hpre hc1 (a := 4072) (n := 344) (N := 0) (by decide) (by decide) (Nat.zero_le _)
      hout ⟨h64, h72', h96'⟩
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcX64.Sphincs.SphincsVerify.b152_next), hB', hz, hN',
    regIs_of_saved rfl h12' hS, ?_, hA', hC'⟩
  rw [h1] at hz0
  exact hz0

/-- **`b152` and `memset`**: from the loop head to `b153`. -/
theorem nodeA (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtNode r l e z m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b153Offset ∧ AtN2 r l e z st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b152Offset⟩ := by
  rcases pathStart_cases h.1.1 with hpp | hpp | hpp
  · exact nodeA_gen hp hc hpre h hpp run_b161_0 rfl (by decide) (by decide) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact nodeA_gen hp hc hpre h hpp run_b161_8 rfl (by decide) (by decide) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact nodeA_gen hp hc hpre h hpp run_b161_16 rfl (by decide) (by decide) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)

end

end NativeRustcX64.SphincsVerifyProof.Tree
