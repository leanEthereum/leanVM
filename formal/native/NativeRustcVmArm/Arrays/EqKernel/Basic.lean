module

public import NativeRustcVmArm.Code.Vm.EqKernel.Names
public import NativeRustcVmArm.Arrays.EqKernel.Exec
public import NativeRustcVmArm.Arrays.BufEW
public import NativeRustcVm.Arrays.EqKernel

/-!
# `eq_kernel` on AArch64: the state

`out`'s kernel `K i` of the first `i` coordinates, the size and `point`'s end in the frame
(`Frame`), the body kept by stores into `out` and by `EW::mul`, the loops' invariants (`OInv` at a
round's head, `IInv` at a pair's, `RInv` at a round's end), the blocks' places.
-/

namespace NativeRustcVmArm.Arrays.EqKernel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.EqKernel NativeVm.Model
open NativeRustcVm (ewsOf ewOf EWsAt EWAt WordAt half1)

public section

/-- `point`. -/
abbrev pt (m : MachineData) : BitVec 64 := m.regs.X0.toBitVec
/-- `|point|`. -/
abbrev np (m : MachineData) : Nat := m.regs.X1.toNat
/-- `out`. -/
abbrev out (m : MachineData) : BitVec 64 := m.regs.X2.toBitVec
/-- `|out|`. -/
abbrev len (m : MachineData) : Nat := m.regs.X3.toNat
/-- `point`'s coordinates. -/
abbrev pts (m : MachineData) : List EW := ewsOf m.dmem (pt m) (np m)
/-- The frame's base. -/
abbrev fb (m : MachineData) : BitVec 64 := m.regs.SP.toBitVec - BitVec.ofNat 64 112
/-- The kernel of the first `i` coordinates. -/
abbrev K (m : MachineData) (i : Nat) : List EW := (eqKernel ((pts m).take i).toArray).toList
/-- The body's state. -/
abbrev B (m0 : MachineData) : MachineData → Prop :=
  Body m0 112 eqKernelStack slots (out m0) (16 * len m0)

theorem length_K (m : MachineData) {i : Nat} (h : i ≤ np m) : (K m i).length = 2 ^ i := by
  simp only [K, Array.length_toList, NativeRustcVm.size_eqKernel, List.size_toArray,
    List.length_take, NativeRustcVm.length_ewsOf, Nat.min_eq_left h]

theorem K_zero (m : MachineData) : K m 0 = [1] := rfl

/-- Coordinate `i`. -/
abbrev rr (m : MachineData) (i : Nat) : EW := (pts m).getD i 0

theorem rr_eq (m : MachineData) {i : Nat} (h : i < np m) :
    rr m i = (pts m)[i]'(by simp; exact h) := by
  simp only [rr, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < (pts m).length by simp; exact h), Option.getD_some]

theorem K_succ (m : MachineData) {i : Nat} (h : i < np m) :
    K m (i + 1) = (K m i).map (· * (1 + rr m i)) ++ (K m i).map (· * rr m i) := by
  rw [rr_eq m h]
  exact NativeRustcVm.eqKernel_take_succ _ _

theorem K_np (m : MachineData) : K m (np m) = (eqKernel (slice m m.regs.X0 m.regs.X1)).toList := by
  simp only [K, slice]
  rw [List.take_of_length_le (by simp)]

/-- The size and `point`'s end, stored at `[sp]`, `[sp, #8]`. -/
structure Frame (m0 s : MachineData) : Prop where
  size : WordAt s.dmem (fb m0) (UInt64.ofNat (2 ^ np m0))
  pend : WordAt s.dmem (fb m0 + BitVec.ofNat 64 8)
    (UInt64.ofBitVec (pt m0 + BitVec.ofNat 64 (16 * np m0)))

theorem Frame.of_same {m0 s s' : MachineData} (hf : Frame m0 s)
    (h : ∀ j < 16, s'.dmem.get? (fb m0 + BitVec.ofNat 64 j) = s.dmem.get? (fb m0 + BitVec.ofNat 64 j)) :
    Frame m0 s' :=
  ⟨bytesAt_congr hf.size fun j hj ↦ h j (by rw [NativeRustcVm.length_wordBytes] at hj; omega),
    bytesAt_congr hf.pend fun j hj ↦ by
      rw [NativeRustcVm.length_wordBytes] at hj
      rw [NativeRustcVm.addr_add]
      exact h _ (by omega)⟩

theorem Frame.of_dmem {m0 s s' : MachineData} (hf : Frame m0 s) (h : s'.dmem = s.dmem) :
    Frame m0 s' :=
  hf.of_same fun _ _ ↦ by rw [h]

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 112 := by decide

theorem all_slotted (r : XReg) (h : calleeSaved r = true) : r ∈ slots.map (·.2) := by
  cases r <;> simp_all [calleeSaved, slots]

theorem eqKernelStack_eq : eqKernelStack = 704 := rfl

/-- A byte of the frame is not one of `out`'s. -/
theorem frame_not_out {m0 : MachineData} (hpre : EqKernelPre m0) {j : Nat} (hj : j < 112) :
    ¬InRange (out m0) (16 * len m0) (fb m0 + BitVec.ofNat 64 j) := by
  obtain ⟨hS, -, -, ⟨⟨-, hnO⟩, hoO⟩, -⟩ := hpre
  have hSle : eqKernelStack ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  rw [eqKernelStack_eq] at hSle
  have e : fb m0 + BitVec.ofNat 64 j = stackBelow m0 eqKernelStack + BitVec.ofNat 64 (592 + j) := by
    unfold stackBelow fb
    rw [eqKernelStack_eq]
    bv_omega
  rw [e]
  exact not_inRange_of_apart (Or.symm hoO) (stack_noWrap hS) hnO
    (by rw [eqKernelStack_eq]; omega)

/-- **Memory changed in `out` only** keeps the body. -/
theorem B.of_out {m0 st st' : MachineData} (hpre : EqKernelPre m0) (hb : B m0 st)
    (hsp : st'.regs.SP = st.regs.SP)
    (hsame : ∀ p, ¬InRange (out m0) (16 * len m0) p → st'.dmem.get? p = st.dmem.get? p)
    (hk : Kept st.dmem st'.dmem) : B m0 st' :=
  ⟨by rw [hsp]; exact hb.sp, fun p hp i hi ↦ by
      simp only [List.length_map, List.length_range] at hi
      rw [NativeRustcVm.addr_add, hsame _ (frame_not_out hpre (by have := slots_le p hp; omega)),
        ← NativeRustcVm.addr_add]
      exact hb.frame p hp i (by simpa using hi),
    fun r hr hn ↦ absurd (all_slotted r hr) hn,
    fun p hp ↦ by rw [hsame p fun h ↦ hp (Or.inl h)]; exact hb.same p hp,
    fun p h ↦ hk p (hb.kept p h)⟩

theorem Frame.of_out {m0 st st' : MachineData} (hpre : EqKernelPre m0) (hf : Frame m0 st)
    (hsame : ∀ p, ¬InRange (out m0) (16 * len m0) p → st'.dmem.get? p = st.dmem.get? p) :
    Frame m0 st' :=
  hf.of_same fun _ hj ↦ hsame _ (frame_not_out hpre (by omega))

/-- **A call of `EW::mul`** keeps the frame. -/
theorem Frame.call {m0 st st' : MachineData} (hb : B m0 st) (hf : Frame m0 st)
    (hpost : EWMulPost st st') : Frame m0 st' :=
  hf.of_same fun j hj ↦ hpost.2.2.1 _ fun h ↦ by
    unfold stackBelow at h
    rw [hb.sp] at h
    have h592 : ewMulStack = 592 := rfl
    exact not_inRange_below (by rw [h592]; omega) h

/-- **A call of `EW::mul`** keeps `out`. -/
theorem out_call {m0 st st' : MachineData} (hpre : EqKernelPre m0) (hb : B m0 st)
    (hpost : EWMulPost st st') :
    ∀ p, InRange (out m0) (16 * len m0) p → st'.dmem.get? p = st.dmem.get? p := by
  obtain ⟨hS, -, -, ⟨⟨-, hnO⟩, hoO⟩, -⟩ := hpre
  intro p hp'
  refine hpost.2.2.1 p fun h ↦ ?_
  unfold stackBelow at h
  rw [hb.sp] at h
  have h' := inRange_stack (n := ewMulStack) (F := 112) (S := eqKernelStack) (by decide) hS.2.1 h
  have hsnw : NoWrap (m0.regs.SP.toBitVec - BitVec.ofNat 64 eqKernelStack) eqKernelStack :=
    stack_noWrap hS
  have hSle : eqKernelStack ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  rw [inRange_iff hnO] at hp'
  rw [inRange_iff hsnw, toNat_sub_ofNat hSle] at h'
  unfold OffStack Apart stackBelow at hoO
  rw [toNat_sub_ofNat hSle] at hoO
  omega

/-- A word in region 0 loaded. -/
theorem load_word [Labels] {st : MachineData} {a : BitVec 64} {n o : Nat}
    {rs : List (BitVec 64 × Nat)} {w : UInt64} (h : WordAt st.dmem (a + BitVec.ofNat 64 o) w) :
    (Env.ofMachine st ((a, n) :: rs)).load 0 o 8 = w.toBitVec := by
  rw [Env.load_of_bytesAt (bs := (List.range 8).map (byteOf w.toBitVec)) (by simp)
    (by rw [byteOf_wordBytes]; exact h), ofInt_ofBytes_byteOf]

/-- `lsl #1` as rustc writes it (`ubfm #63, #62`): the double. -/
theorem lsl1 (x : BitVec 64) : UnOp.apply (.ubfm 63 62) .W64 x = BitVec.ofNat 64 (2 * x.toNat) := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  apply BitVec.eq_of_toNat_eq
  simp [evalUBFM, toNat_take', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- **The entry block**, writing into the frame (region 0) and `out[0]` (region 1). -/
theorem Body.of_entry2 [Labels] {m0 st : MachineData} {F S : Nat} {slots : List (Nat × XReg)}
    {oa : BitVec 64} {on : Nat} {o : BitVec 64} {n : Nat} {S' : SState} (hS : StackOk m0 S)
    (hF : F ≤ S)
    (hwf : (Env.ofMachine m0 [(m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F), (o, n)]).WF)
    (hm : Match (Env.ofMachine m0 [(m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F), (o, n)]) S' st)
    (hsp : S'.sp = .ptr 0 0)
    (hw : ∀ p ∈ slots, p.1 + 8 ≤ F ∧ ∀ i < 8, findWrite 0 (p.1 + i) S'.mem = some (.reg p.2, i))
    (hregs : ∀ r ∈ calleeRegs, inSlots slots r = false → S'.reg r = some (.reg r))
    (hmem : ∀ w ∈ S'.mem, (w.r = 0 ∧ w.off + w.n ≤ F) ∨ (w.r = 1 ∧ w.off + w.n ≤ n))
    (hin : ∀ p, InRange o n p → InRange oa on p) : Body m0 F S slots oa on st := by
  have hSle : S ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  refine ⟨?_, slotsAt_of_writes hm hw, fun r hr hn ↦ ?_, fun p hp ↦ ?_, hm.kept hwf⟩
  · rw [hm.sp, hsp]; simp [Sym.eval]
  · apply UInt64.toBitVec_inj.mp
    rw [hm.regs r _ (hregs r (mem_calleeRegs hr) (inSlots_false hn))]
    rfl
  · refine BufEW.same_of_regions01 hm hwf hmem p (fun h ↦ hp (Or.inr ?_)) (fun h ↦ hp (Or.inl (hin p h)))
    exact inRange_stack (F := 0) (n := F) (by omega) hSle (by simpa using h)

/-- `EWsAt` kept where memory is unchanged. -/
theorem ewsAt_keep {d d' : DataMem} {O : BitVec 64} {c : Nat} {xs : List EW}
    (h : EWsAt d (O + BitVec.ofNat 64 c) xs)
    (he : ∀ t, c ≤ t → t < c + 16 * xs.length →
      d'.get? (O + BitVec.ofNat 64 t) = d.get? (O + BitVec.ofNat 64 t)) :
    EWsAt d' (O + BitVec.ofNat 64 c) xs :=
  bytesAt_congr h fun t ht ↦ by
    rw [length_flatMap_ewBytes] at ht
    rw [NativeRustcVm.addr_add]
    exact he _ (by omega) (by omega)

/-- A byte of `out` outside element `y`. -/
theorem not_in_elem {O : BitVec 64} {L x y : Nat} (hO : O.toNat + 16 * L ≤ 2 ^ 64)
    (hx : x < 16 * L) (hy : y < L) (h : x < 16 * y ∨ 16 * y + 16 ≤ x) :
    ¬InRange (O + BitVec.ofNat 64 (16 * y)) 16 (O + BitVec.ofNat 64 x) := by
  rw [inRange_iff (show (O + BitVec.ofNat 64 (16 * y)).toNat + 16 ≤ 2 ^ 64 by
    rw [toNat_add_ofNat' (by omega)]; omega), toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega)]
  omega

/-- `1 << y` as the executor evaluates `lsl`, for `y < 64`. -/
theorem one_shl_toNat (y : BitVec 64) (hy : y.toNat < 64) :
    (1#64 <<< (y.toNat % RegWidth.W64.bits)).toNat = 2 ^ y.toNat := by
  rw [show y.toNat % RegWidth.W64.bits = y.toNat from Nat.mod_eq_of_lt hy]
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) hy)]

/-- The size stored at `[sp]`. -/
theorem size_eval [Labels] {m0 : MachineData} (h64 : np m0 < 64) (rs : List (BitVec 64 × Nat)) :
    sizeSym.eval (Env.ofMachine m0 rs) = BitVec.ofNat 64 (2 ^ np m0) := by
  apply BitVec.eq_of_toNat_eq
  simp only [sizeSym]
  sym_simp
  simp only [Env.ofMachine_regs]
  rw [one_shl_toNat (m0.regs.getXReg .X1).toBitVec h64, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) h64)]
  rfl

/-- `point`'s end, stored at `[sp, #8]`. -/
theorem end_eval [Labels] {m0 : MachineData} (rs : List (BitVec 64 × Nat)) :
    UInt64.ofBitVec (endSym.eval (Env.ofMachine m0 rs)) =
      UInt64.ofBitVec (pt m0 + BitVec.ofNat 64 (16 * np m0)) := by
  simp only [endSym, Sym.eval, Env.ofMachine_regs, UnOp.apply, shiftW, Sym.ext_W64, Sym.low_W64,
    shl4, BinOp.apply]
  rfl

/-- `out[0] = 1`, stored by the prologue in region 1. -/
theorem out0_of [Labels] {m0 st : MachineData} {S : SState} {a : BitVec 64} {n : Nat}
    (hm : Match (Env.ofMachine m0 [(a, n), (out m0, 16)]) S st)
    (h0 : ∀ i < 8, findWrite 1 (0 + i) S.mem = some (.lit 1, i))
    (h8 : ∀ i < 8, findWrite 1 (8 + i) S.mem = some (.lit 0, i)) :
    EWsAt st.dmem (out m0) (K m0 0) := by
  rw [K_zero, NativeRustcVm.ewsAt_singleton, NativeRustcVm.ewAt_iff]
  have a0 := BufEW.wordAt_of_writeSym hm (r := 1) (o := 0) rfl (by decide) h0
  have a1 := BufEW.wordAt_of_writeSym hm (r := 1) (o := 8) rfl (by decide) h8
  rw [add_ofNat_zero] at a0
  exact ⟨a0, a1⟩

theorem pow_facts {m0 : MachineData} (hle : 2 ^ np m0 ≤ len m0) {i : Nat} (h : i < np m0) :
    0 < 2 ^ i ∧ 2 * 2 ^ i ≤ len m0 := by
  have := Nat.pow_le_pow_right (by decide : 0 < 2) (show i + 1 ≤ np m0 from h)
  rw [Nat.pow_succ] at this
  exact ⟨Nat.two_pow_pos i, by omega⟩

/-! ## The invariants -/

/-- **The outer loop's head** `.LEqKernel_5`, `i` coordinates done. -/
structure OInv (m0 : MachineData) (i : Nat) (s : MachineData) : Prop where
  body : B m0 s
  frame : Frame m0 s
  lt : i < np m0
  x29 : s.regs.X29.toNat = 2 ^ i
  x22 : s.regs.X22.toBitVec = pt m0 + BitVec.ofNat 64 (16 * i)
  x20 : s.regs.X20 = m0.regs.X3
  x27 : s.regs.X27.toBitVec = out m0 + BitVec.ofNat 64 8
  ker : EWsAt s.dmem (out m0) (K m0 i)

/-- **The inner loop's head** `.LEqKernel_8`, `j` pairs of round `i` done. -/
structure IInv (m0 : MachineData) (i j : Nat) (s : MachineData) : Prop where
  body : B m0 s
  frame : Frame m0 s
  lt : i < np m0
  jlt : j < 2 ^ i
  x29 : s.regs.X29.toNat = 2 ^ i
  x22 : s.regs.X22.toBitVec = pt m0 + BitVec.ofNat 64 (16 * i)
  x20 : s.regs.X20 = m0.regs.X3
  x27 : s.regs.X27.toBitVec = out m0 + BitVec.ofNat 64 8
  x19 : s.regs.X19.toNat = 2 ^ i - j
  x28 : s.regs.X28.toBitVec = out m0 + BitVec.ofNat 64 (16 * j + 8)
  x21 : s.regs.X21.toBitVec = out m0 + BitVec.ofNat 64 (16 * (2 ^ i + j) + 8)
  r : (⟨s.regs.X23, s.regs.X24⟩ : EW) = rr m0 i
  lo : EWsAt s.dmem (out m0) (half1 (K m0 i) (rr m0 i) j)
  hi : EWsAt s.dmem (out m0 + BitVec.ofNat 64 (16 * 2 ^ i)) (((K m0 i).take j).map (· * rr m0 i))

/-- **Round `i` done**, at `b .LEqKernel_4`. -/
structure RInv (m0 : MachineData) (i : Nat) (s : MachineData) : Prop where
  body : B m0 s
  frame : Frame m0 s
  lt : i < np m0
  x29 : s.regs.X29.toNat = 2 ^ i
  x22 : s.regs.X22.toBitVec = pt m0 + BitVec.ofNat 64 (16 * i)
  x20 : s.regs.X20 = m0.regs.X3
  x27 : s.regs.X27.toBitVec = out m0 + BitVec.ofNat 64 8
  ker : EWsAt s.dmem (out m0) (K m0 (i + 1))

/-- The postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ EqKernelPost m0 s.data

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EqKernel.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EqKernel.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EqKernel.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EqKernel.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EqKernel.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EqKernel.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EqKernel.b6Offset) :=
  b6_in_code.trans hp.1 (by simp [b6])
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EqKernel.b7Offset) :=
  b7_in_code.trans hp.1 (by simp [b7])
theorem hb8 (hp : Placed code k) : b8.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EqKernel.b8Offset) :=
  b8_in_code.trans hp.1 (by simp [b8])
theorem hb9 (hp : Placed code k) : b9.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EqKernel.b9Offset) :=
  b9_in_code.trans hp.1 (by simp [b9])
theorem hb10 (hp : Placed code k) : b10.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EqKernel.b10Offset) :=
  b10_in_code.trans hp.1 (by simp [b10])
theorem hb12 (hp : Placed code k) : b12.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EqKernel.b12Offset) :=
  b12_in_code.trans hp.1 (by simp [b12])
theorem hb13 (hp : Placed code k) : b13.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EqKernel.b13Offset) :=
  b13_in_code.trans hp.1 (by simp [b13])

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.EqKernel.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.EqKernel.b0Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.EqKernel.entryOffset) NativeRustcVmArm.Vm.EqKernel.entry_at
theorem lbl_2 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.EqKernel.label_2 = Host.addrOf (k + NativeRustcVmArm.Vm.EqKernel.b2Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.EqKernel.b2Offset) NativeRustcVmArm.Vm.EqKernel.label_2_at
theorem lbl_4 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.EqKernel.label_4 = Host.addrOf (k + NativeRustcVmArm.Vm.EqKernel.b4Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.EqKernel.b4Offset) NativeRustcVmArm.Vm.EqKernel.label_4_at
theorem lbl_5 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.EqKernel.label_5 = Host.addrOf (k + NativeRustcVmArm.Vm.EqKernel.b5Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.EqKernel.b5Offset) NativeRustcVmArm.Vm.EqKernel.label_5_at
theorem lbl_8 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.EqKernel.label_8 = Host.addrOf (k + NativeRustcVmArm.Vm.EqKernel.b8Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.EqKernel.b8Offset) NativeRustcVmArm.Vm.EqKernel.label_8_at
theorem lbl_10 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.EqKernel.label_10 = Host.addrOf (k + NativeRustcVmArm.Vm.EqKernel.b12Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.EqKernel.b12Offset) NativeRustcVmArm.Vm.EqKernel.label_10_at
theorem lbl_11 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.EqKernel.label_11 = Host.addrOf (k + NativeRustcVmArm.Vm.EqKernel.b13Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.EqKernel.b13Offset) NativeRustcVmArm.Vm.EqKernel.label_11_at

end

end NativeRustcVmArm.Arrays.EqKernel
