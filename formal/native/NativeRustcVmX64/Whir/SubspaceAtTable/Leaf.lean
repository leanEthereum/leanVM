module

public import NativeRustcVmX64.Whir.MathFrame

/-!
# What the x86-64 proofs of `subspace_at_table`, `subspace_table`, `novel_eval`, `fold_row` and
`glued_eval` share

Besides `NativeRustcVmX64.Whir.MathFrame`'s bodies (`Frame`): the executor's 64-bit operations
(`add64`, …), a byte of the frame by its offset (`fb_toNat`, `inRange_fb_iff`), bytes a block
or a callee kept (`bytesAt_block`, `bytesAt_callee`), the first bytes `bytesOf` reads
(`bytesOf_take`).
-/

namespace NativeRustcVmX64.Whir.Leaf

open NativeRustcX64 NativeRustcX64.Sym
open NativeRustcVm (Region InAny)

public section

/-! ## The executor's operations -/

theorem add64 (x y : BitVec 64) : BinOp.apply .add .W64 x y = x + y := by
  simp only [BinOp.apply, low_W64, ext_W64]

theorem sub64 (x y : BitVec 64) : BinOp.apply .sub .W64 x y = x - y := by
  simp only [BinOp.apply, low_W64, ext_W64]

theorem mul64 (x y : BitVec 64) : BinOp.apply .mul .W64 x y = x * y := by
  simp only [BinOp.apply, low_W64, ext_W64]

theorem xor64 (x y : BitVec 64) : BinOp.apply .xor .W64 x y = x ^^^ y := by
  simp only [BinOp.apply, low_W64, ext_W64]

/-- `ja`: the unsigned `a > b`. -/
theorem gt_eval [Labels] (env : Env) (a b : Sym) :
    (SBool.and (.not (.cmp .ult .W64 a b)) (.not (.cmp .eq .W64 a b))).eval env =
      decide ((b.eval env).toNat < (a.eval env).toNat) := by
  simp only [SBool.eval, CmpOp.apply, low_W64, bv_ult_toNat, bv_beq_toNat]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  omega

theorem ofInt_ofNat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n :=
  BitVec.ofInt_natCast 64 n

theorem toNat_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

/-- A register's number as a word is the register. -/
theorem toUInt64_toNat (x : BitVec 64) : x.toNat.toUInt64 = UInt64.ofBitVec x :=
  UInt64.toNat.inj ((toNat_toUInt64 x.isLt).trans rfl)

/-! ## The frame by offsets -/

/-- **Bytes a block kept**: in region `r`, a range no write of the block touches. -/
theorem bytesAt_block [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    (hwf : env.WF) {r : Nat} {b : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (b, sz))
    {o : Nat} {bs : List UInt8} (hle : o + bs.length ≤ sz)
    (hall : ∀ w ∈ S.mem, w.r = r ∧ (w.off + w.n ≤ o ∨ o + bs.length ≤ w.off))
    (h : NativeRustcVm.BytesAt env.mem0 (b + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt m.dmem (b + BitVec.ofNat 64 o) bs := fun i hi ↦ by
  rw [addr_add, Match.keep hm hwf hb hle hall i hi, ← addr_add]
  exact h i hi

section
variable {m0 : MachineData} {F S : Nat}

/-- The frame's byte `j` as a number. -/
theorem fb_toNat (hS : StackOk m0 S) (hF : F ≤ S) {j : Nat} (hj : j < F + 8) :
    (stackBelow m0 F + BitVec.ofNat 64 j).toNat = (rspOf m0).toNat - F + j := by
  have h1 := hS.1
  have h2 := hS.2.1
  rw [toNat_add_ofNat _ _ (by rw [Arrays.stackBelow_toNat (by omega)]; omega),
    Arrays.stackBelow_toNat (by omega)]

/-- A byte of the frame in a range of the frame, by offsets. -/
theorem inRange_fb_iff (hS : StackOk m0 S) (hF : F ≤ S) {c n j : Nat} (hc : c < F + 8)
    (hcn : c + n ≤ F + 8) (hj : j < F + 8) :
    InRange (stackBelow m0 F + BitVec.ofNat 64 c) n (stackBelow m0 F + BitVec.ofNat 64 j) ↔
      c ≤ j ∧ j < c + n := by
  have hct := fb_toNat hS hF hc
  have h1 := hS.1
  have h2 := hS.2.1
  rw [Sym.inRange_iff (by rw [hct]; omega), hct, fb_toNat hS hF hj]
  omega

/-- A range of the frame below `L` is among the stack's bytes. -/
theorem inRange_stack_of (hS : StackOk m0 S) (hF : F ≤ S) {c n L : Nat} (hL : L ≤ F)
    (hcn : c + n ≤ L) {p : BitVec 64} (h : InRange (stackBelow m0 F + BitVec.ofNat 64 c) n p) :
    InRange (stackBelow m0 S) S p := by
  have hnw := (frame_ok hS hF).2.1
  exact inRange_frame hS hF hL (Arrays.inRange_sub (NativeRustcVm.NoWrap.mono hnw (by omega))
    hcn h)

/-- A range of the frame below `L` within the first `L` bytes. -/
theorem inRange_low_of (hS : StackOk m0 S) (hF : F ≤ S) {c n L : Nat} (hL : L ≤ F + 8)
    (hcn : c + n ≤ L) {p : BitVec 64} (h : InRange (stackBelow m0 F + BitVec.ofNat 64 c) n p) :
    InRange (stackBelow m0 F) L p := by
  have hnw := (frame_ok hS hF).2.1
  exact Arrays.inRange_sub (NativeRustcVm.NoWrap.mono hnw hL) hcn h

/-- The slots are not in a range of the frame below them. -/
theorem slot_not_in (hS : StackOk m0 S) (hF : F ≤ S) {slots : List (Nat × Reg64)} {c n L : Nat}
    (hcn : c + n ≤ L) (hc : c < F + 8) (hsl : ∀ q ∈ slots, L ≤ q.1 ∧ q.1 + 8 ≤ F) :
    ∀ q ∈ slots, ∀ i < 8,
      ¬InRange (stackBelow m0 F + BitVec.ofNat 64 c) n
        (stackBelow m0 F + BitVec.ofNat 64 q.1 + BitVec.ofNat 64 i) := by
  intro q hq i hi
  have := hsl q hq
  rw [addr_add, inRange_fb_iff hS hF hc (by omega) (by omega)]
  omega

/-- **Bytes a callee kept**: the frame's, above its stack. -/
theorem bytesAt_callee {d d' : MachineData} {N o : Nat} {bs : List UInt8} (hS : StackOk m0 S)
    (hsp : rspOf d = stackBelow m0 F) (hle : F + N ≤ S)
    (hs : SameOutside d.dmem d'.dmem (InRange (stackBelow d N) N)) (ho : o + bs.length ≤ F + 8)
    (h : NativeRustcVm.BytesAt d.dmem (stackBelow m0 F + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt d'.dmem (stackBelow m0 F + BitVec.ofNat 64 o) bs :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi ↦ by
    rw [addr_add]
    exact not_inRange_callee hS hsp hle (by omega)

/-- **An argument off the stack is apart from the frame**. -/
theorem apart_frame' (hS : StackOk m0 S) (hF : F ≤ S) {a : BitVec 64} {n : Nat}
    (ho : OffStack m0 a n S) : Apart a n (stackBelow m0 F) (F + 8) := by
  have h1 := hS.1
  unfold OffStack Apart at ho
  unfold Apart
  rw [Arrays.stackBelow_toNat h1] at ho
  rw [Arrays.stackBelow_toNat (by omega)]
  omega

/-- **An argument's bytes are kept by a block writing the frame** (region 0, its first `F + 8`
bytes). -/
theorem get?_of_frame [Labels] {env : Env} {Sy : SState} {m : MachineData} (hm : Match env Sy m)
    (hwf : env.WF) {rs : List (BitVec 64 × Nat)}
    (hr : env.regions = (stackBelow m0 F, F + 8) :: rs)
    (hall : ∀ w ∈ Sy.mem, w.r = 0 ∧ w.off + w.n ≤ F + 8) (hS : StackOk m0 S) (hF : F ≤ S)
    {a : BitVec 64} {n : Nat} (ho : OffStack m0 a n S) (hna : NoWrap a n) :
    ∀ j < n, m.dmem.get? (a + BitVec.ofNat 64 j) = env.mem0.get? (a + BitVec.ofNat 64 j) :=
  fun _ hj ↦ hm.get?_mem0 hwf fun h ↦
    Arrays.not_inRange_of_apart (apart_frame' hS hF ho) hna (frame_ok hS hF).2.1 hj
      (Arrays.written_region0 hr hwf le_rfl hall h)

/-- **A frame byte is kept by a callee whose changes are in an output off the stack and its
stack**. -/
theorem frame_callee {d d' : MachineData} {N : Nat} {outs : List Region}
    (hS : StackOk m0 S) (hF : F ≤ S) (hsp : rspOf d = stackBelow m0 F) (hle : F + N ≤ S)
    (hout : ∀ r ∈ outs, OffStack m0 r.addr r.size S ∧ NoWrap r.addr r.size)
    (hs : SameOutside d.dmem d'.dmem (fun p ↦ InAny outs p ∨ InRange (stackBelow d N) N p))
    {j : Nat} (hj : j < F + 8) :
    d'.dmem.get? (stackBelow m0 F + BitVec.ofNat 64 j) =
      d.dmem.get? (stackBelow m0 F + BitVec.ofNat 64 j) :=
  hs _ fun h ↦ h.elim (not_inAny_frame hS hF hout hj) (not_inRange_callee hS hsp hle hj)

/-- **Frame bytes kept by a block ending in a call and the call**: the block writes the frame's
first 8 bytes (the return address), the callee its stack below the frame. -/
theorem keep_call [Labels] {env : Env} {Sy : SState} {d d1 d2 : MachineData} {N o : Nat}
    {bs : List UInt8} (hm : Match env Sy d1) (hwf : env.WF)
    (hr0 : env.regions[0]? = some (stackBelow m0 F, F + 8)) (hd : env.mem0 = d.dmem)
    (hw : ∀ w ∈ Sy.mem, w.r = 0 ∧ w.off + w.n ≤ 8) (hS : StackOk m0 S)
    (hsp : rspOf d1 = stackBelow m0 F) (hle : F + N ≤ S)
    (hso : SameOutside d1.dmem d2.dmem (InRange (stackBelow d1 N) N)) (h8 : 8 ≤ o)
    (hlen : o + bs.length ≤ F + 8)
    (h : NativeRustcVm.BytesAt d.dmem (stackBelow m0 F + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt d2.dmem (stackBelow m0 F + BitVec.ofNat 64 o) bs :=
  bytesAt_callee hS hsp hle hso hlen (bytesAt_block hm hwf hr0 hlen (fun w hw' ↦
    ⟨(hw w hw').1, .inl (by have := (hw w hw').2; omega)⟩) (hd ▸ h))

/-- **Frame bytes kept by a block writing a range of the frame** apart from them. -/
theorem keep_write [Labels] {env : Env} {Sy : SState} {d d1 : MachineData} {c n o : Nat}
    {bs : List UInt8} (hm : Match env Sy d1) (hwf : env.WF)
    (hr0 : env.regions[0]? = some (stackBelow m0 F + BitVec.ofNat 64 c, n))
    (hd : env.mem0 = d.dmem) (hw : ∀ w ∈ Sy.mem, w.r = 0 ∧ w.off + w.n ≤ n)
    (hS : StackOk m0 S) (hF : F ≤ S) (hc : c + n ≤ F + 8) (hlen : o + bs.length ≤ F + 8)
    (hap : o + bs.length ≤ c ∨ c + n ≤ o)
    (h : NativeRustcVm.BytesAt d.dmem (stackBelow m0 F + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt d1.dmem (stackBelow m0 F + BitVec.ofNat 64 o) bs :=
  NativeRustcVm.BytesAt.of_sameOutside (hd ▸ h) (same_region_le hm hwf hr0 le_rfl hw)
    fun j hj ↦ by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; intro hin; unfold InRange at hin; omega
      rw [addr_add, inRange_fb_iff hS hF (by omega) hc (by omega)]
      omega

/-- A body that wrote no output is a body of any outputs. -/
theorem frame_mono {st : MachineData} {slots : List (Nat × Reg64)} {outs : List Region}
    (hb : Frame m0 F S slots [] st) : Frame m0 F S slots outs st :=
  ⟨hb.rsp, hb.frame, hb.regs, ChangesIn.mono hb.same fun _ hr ↦ absurd hr List.not_mem_nil,
    hb.kept⟩

/-- No output: none off the stack. -/
theorem out_nil {S : Nat} :
    ∀ r ∈ ([] : List Region), OffStack m0 r.addr r.size S ∧ NoWrap r.addr r.size :=
  fun _ hr ↦ absurd hr List.not_mem_nil

end

/-- The first `j` of the `n` bytes `bytesOf` reads. -/
theorem bytesOf_take (d : DataMem) (a : BitVec 64) {j n : Nat} (h : j ≤ n) :
    (NativeRustcX64.bytesOf d a n).take j = NativeRustcX64.bytesOf d a j := by
  simp [NativeRustcX64.bytesOf, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-- One output region apart from the stack. -/
theorem out_one {m0 : MachineData} {S : Nat} {o : BitVec 64} {n : Nat}
    (h : WhirIn m0 o n S) :
    ∀ r ∈ [(⟨o, n⟩ : Region)], OffStack m0 r.addr r.size S ∧ NoWrap r.addr r.size := by
  intro r hr
  rw [List.mem_singleton] at hr
  subst hr
  exact ⟨h.2, h.1.2⟩

/-- A byte of the one output region. -/
theorem inAny_one {o p : BitVec 64} {n : Nat} (h : InRange o n p) :
    InAny [(⟨o, n⟩ : Region)] p := ⟨_, List.mem_singleton_self _, h⟩

end

end NativeRustcVmX64.Whir.Leaf
