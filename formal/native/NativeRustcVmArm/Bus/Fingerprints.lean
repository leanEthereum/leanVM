module

public import NativeRustcVmArm.Code.Vm.Dot.Names
public import NativeRustcVmArm.Code.Vm.Fingerprints.Names
public import NativeRustcVmArm.Code.Vm.IndexMleFrom.Names
public import NativeRustcVmArm.Code.Vm.Kpow.Names
public import NativeRustcVmArm.Bus.Fingerprints.Exec
public import NativeRustcVmArm.Bus.Common

/-!
# `fingerprints`

`b0` saves the registers in its 320-byte frame and copies the stack arguments (the bytecode count
at `sp + 16`, the share at `sp + 32`); then three fingerprints, each a `dot` of the first weights
with an array the function builds in its frame (`b1`, `b3`, `b6`), around `kpow` (`gpow 0`,
`gpow 2`) and `index_mle_from`; `b7` writes them, the third plus the share, and returns
(`fingerprints_spec`).
-/

namespace NativeRustcVmArm.Bus.Fingerprints

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Fingerprints
open NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVmArm.Layout (infix_of)
open NativeRustcVm (ewsOf wordOf)

public section

/-- The frame's saved registers. -/
abbrev slots : List (Nat × XReg) :=
  [(224, .X29), (232, .X30), (240, .X28), (248, .X27), (256, .X26), (264, .X25), (272, .X24),
    (280, .X23), (288, .X22), (296, .X21), (304, .X20), (312, .X19)]

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 320 := by decide

theorem nil_callee : ∀ r ∈ ([] : List XReg), calleeSaved r = true := by decide

/-- The first `k` of `n` elements read. -/
theorem ewsOf_take (d : DataMem) (a : BitVec 64) {k n : Nat} (h : k ≤ n) :
    (ewsOf d a n).take k = ewsOf d a k := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp

theorem extract_ewsOf (d : DataMem) (a : BitVec 64) {k n : Nat} (h : k ≤ n) :
    (ewsOf d a n).toArray.extract 0 k = (ewsOf d a k).toArray := by
  apply Array.ext'
  simp [ewsOf_take d a h]

/-- The registers `b0` sets that keep their values to the end. -/
abbrev Lfix : List XReg := [.X19, .X20, .X21, .X22, .X23, .X29]

theorem stack_le : 320 + kpowStack ≤ fingerprintsStack ∧ 320 + dotStack ≤ fingerprintsStack ∧
    320 + indexMleFromStack ≤ fingerprintsStack := by decide

/-- A readable range of `n` bytes holds its first `k`. -/
theorem readable_mono {m : MachineData} {a : BitVec 64} {n k : Nat} (h : Readable m a n)
    (hk : k ≤ n) : Readable m a k :=
  ⟨NativeRustcVm.Mapped.mono h.1 hk, NativeRustcVm.NoWrap.mono h.2 hk⟩

theorem offStack_mono {m : MachineData} {a : BitVec 64} {n k s : Nat} (h : OffStack m a n s)
    (hk : k ≤ n) : OffStack m a k s := by
  unfold OffStack Apart at *; omega

/-- A stack argument as the entry's frame region loads it. -/
theorem load_stackArg [Labels] (m0 : MachineData) {F sz k : Nat} (rs : List (BitVec 64 × Nat)) :
    (Sym.load 0 (F + k) 8).eval (Env.ofMachine m0 ((base m0 F, sz) :: rs)) =
      (stackArg m0 k).toBitVec := by
  show Env.load _ 0 (F + k) 8 = _
  rw [load_eq_wordOf]
  simp only [Env.ofMachine_mem0, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
    Option.getD_some, stackArg]
  rw [← NativeRustcVm.addr_add_add, base_add_eq]

theorem toBitVec_ofBitVec (x : BitVec 64) : (UInt64.ofBitVec x).toBitVec = x := rfl

/-- A slice of the frame holding `xs` reads `xs`. -/
theorem slice_of_ewsAt {m : MachineData} {a : BitVec 64} {xs : List EW}
    (h : NativeRustcVm.EWsAt m.dmem a xs) (n : UInt64) (hn : n.toNat = xs.length) :
    slice m (UInt64.ofBitVec a) n = xs.toArray := by
  unfold slice
  rw [hn]
  exact congrArg List.toArray (NativeRustcVm.ewsOf_of_ewsAt h)

/-- A slice of the entry's argument `a`, `k` of its `n` elements, for a callee. -/
theorem sliceOk_arg {m0 m : MachineData} {F N N' : Nat} {slots : List (Nat × XReg)}
    {keep : List XReg} {outs : BitVec 64 → Prop} (h : Fr m0 F N slots keep outs m)
    (hS : StackOk m0 N) {a : UInt64} {n k : Nat} (ha : EWsOk m0 a.toBitVec n N) (hk : k ≤ n)
    (hle : F + N' ≤ N) (kk : UInt64) (hkk : kk.toNat = k) : SliceOk m a kk N' := by
  rw [SliceOk, hkk]
  exact ⟨Bus.Fr.readable h (readable_mono ha.1 (by omega)),
    Bus.Fr.offStack h hS (offStack_mono ha.2 (by omega)) hle⟩

variable [Host] {k : Nat}

/-- **`fingerprints`' contract.** -/
theorem fingerprints_spec (hp : Placed code k)
    (hkpow : Spec (Labels.label NativeRustcVmArm.Vm.Kpow.entryLabel) KpowPre KpowPost)
    (hdot : Spec (Labels.label NativeRustcVmArm.Vm.Dot.entryLabel) DotPre DotPost)
    (himf : Spec (Labels.label NativeRustcVmArm.Vm.IndexMleFrom.entryLabel) IndexMleFromPre IndexMleFromPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.Fingerprints.entryLabel) FingerprintsPre FingerprintsPost := by
  rintro m0 ⟨hS, hW, hM, hML, hBL, hSP, hOR, hOS⟩
  have hN : fingerprintsStack ≤ m0.regs.SP.toNat := hS.2.1
  obtain ⟨hlk, hld, hli⟩ := stack_le
  have hF : 320 ≤ fingerprintsStack := by omega
  have hspb : base m0 320 + BitVec.ofNat 64 320 = m0.regs.SP.toBitVec := base_add_eq
  have hbase : (base m0 320).toNat = m0.regs.SP.toNat - 320 := base_toNat (by omega)
  -- The entry: the frame and the stack arguments.
  have hwf0 : (Env.ofMachine m0 [(base m0 320, 320 + 48)]).WF := by
    refine Env.wf_of ⟨⟨fun i hi ↦ ?_, ?_⟩, trivial⟩ (List.pairwise_singleton _ _)
    · by_cases h : i < 320
      · exact (Bus.frame_mapped hS hF).1 i h
      · have := hSP.1 (i - 320) (by omega)
        rwa [← hspb, NativeRustcVm.addr_add_add, show 320 + (i - 320) = i by omega] at this
    · have := hSP.2
      unfold NoWrap at this ⊢
      rw [hbase]
      have : m0.regs.SP.toBitVec.toNat = m0.regs.SP.toNat := rfl
      omega
  have hm0 : Match (Env.ofMachine m0 [(base m0 320, 320 + 48)]) s0 m0 :=
    match_ofMachine (sregions := [(368, true)]) (regions := [(base m0 320, 320 + 48)])
      ⟨rfl, fun _ ↦ Bus.base_aligned hS hF rfl, trivial⟩
      (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
            Option.getD_some]
          rw [show BitVec.ofInt 64 320 = BitVec.ofNat 64 320 from rfl]; exact hspb.symm)
      trivial trivial trivial trivial
  rw [show Labels.label NativeRustcVmArm.Vm.Fingerprints.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.Fingerprints.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.Fingerprints.entryOffset) NativeRustcVmArm.Vm.Fingerprints.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 hm0 fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : Fr m0 320 fingerprintsStack slots [] (fun _ ↦ False) st1.data :=
    Bus.Fr.ofPrologue' hN hF hm1 hwf0 rfl (by decide) slots_le (by decide) (by decide)
  have L : ∀ k, (Sym.load 0 (320 + k) 8).eval (Env.ofMachine m0 [(base m0 320, 320 + 48)]) =
      (stackArg m0 k).toBitVec := fun _ ↦ load_stackArg m0 []
  have L0 : (Sym.load 0 320 8).eval (Env.ofMachine m0 [(base m0 320, 320 + 48)]) =
      (stackArg m0 0).toBitVec := L 0
  have L8 : (Sym.load 0 328 8).eval (Env.ofMachine m0 [(base m0 320, 320 + 48)]) =
      (stackArg m0 8).toBitVec := L 8
  have L16 : (Sym.load 0 336 8).eval (Env.ofMachine m0 [(base m0 320, 320 + 48)]) =
      (stackArg m0 16).toBitVec := L 16
  have L24 : (Sym.load 0 344 8).eval (Env.ofMachine m0 [(base m0 320, 320 + 48)]) =
      (stackArg m0 24).toBitVec := L 24
  have L32 : (Sym.load 0 352 8).eval (Env.ofMachine m0 [(base m0 320, 320 + 48)]) =
      (stackArg m0 32).toBitVec := L 32
  have L40 : (Sym.load 0 360 8).eval (Env.ofMachine m0 [(base m0 320, 320 + 48)]) =
      (stackArg m0 40).toBitVec := L 40
  have hFW1 : Bus.FrameWords st1.data.dmem (base m0 320)
      [(16, stackArg m0 32), (24, stackArg m0 40), (32, stackArg m0 0), (40, m0.regs.X7)] := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · have := Bus.wordAt_write hm1 (r := 0) (o := 16) rfl (by omega) (v := .load 0 352 8)
        (by decide)
      rwa [L32] at this
    · have := Bus.wordAt_write hm1 (r := 0) (o := 24) rfl (by omega) (v := .load 0 360 8)
        (by decide)
      rwa [L40] at this
    · have := Bus.wordAt_write hm1 (r := 0) (o := 32) rfl (by omega) (v := .load 0 320 8)
        (by decide)
      rwa [L0] at this
    · exact Bus.wordAt_write hm1 (r := 0) (o := 40) rfl (by omega) (v := .reg .X7) (by decide)
  have e1x20 : st1.data.regs.getXReg .X20 = m0.regs.X0 := UInt64.toBitVec_inj.mp (hm1.regs .X20 _ rfl)
  have e1x29 : st1.data.regs.getXReg .X29 = stackArg m0 16 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X29 _ rfl).trans L16)
  have e1x19 : st1.data.regs.getXReg .X19 = stackArg m0 24 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X19 _ rfl).trans L24)
  have e1x22 : st1.data.regs.getXReg .X22 = m0.regs.X6 := UInt64.toBitVec_inj.mp (hm1.regs .X22 _ rfl)
  have e1x23 : st1.data.regs.getXReg .X23 = m0.regs.X5 := UInt64.toBitVec_inj.mp (hm1.regs .X23 _ rfl)
  have e1x26 : st1.data.regs.getXReg .X26 = m0.regs.X4 := UInt64.toBitVec_inj.mp (hm1.regs .X26 _ rfl)
  have e1x24 : st1.data.regs.getXReg .X24 = stackArg m0 8 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X24 _ rfl).trans L8)
  have e1x27 : st1.data.regs.getXReg .X27 = m0.regs.X3 := UInt64.toBitVec_inj.mp (hm1.regs .X27 _ rfl)
  have e1x28 : st1.data.regs.getXReg .X28 = m0.regs.X2 := UInt64.toBitVec_inj.mp (hm1.regs .X28 _ rfl)
  have e1x21 : st1.data.regs.getXReg .X21 = m0.regs.X1 := UInt64.toBitVec_inj.mp (hm1.regs .X21 _ rfl)
  have e1x0 : st1.data.regs.X0 = 0 := UInt64.toBitVec_inj.mp (hm1.regs .X0 _ rfl)
  -- `kpow(0)`.
  have hsl : ∀ q, (fun _ ↦ False : BitVec 64 → Prop) q → ¬InRange (base m0 320) 320 q :=
    fun _ h ↦ h.elim
  have hQ : ∀ {P : MachineData → MachineData → Prop} {N' : Nat},
      (∀ m m', P m m' → SameOutside m.dmem m'.dmem (InRange (stackBelow m N') N') ∧ Saved m m') →
      ∀ m m', P m m' → SameOutside m.dmem m'.dmem (fun q ↦ InRange (stackBelow m N') N' q ∨
        (fun _ ↦ False : BitVec 64 → Prop) q) ∧ Saved m m' :=
    fun h m m' hp ↦ ⟨NativeRustcVm.SameOutside.mono (h m m' hp).1 fun _ h ↦ .inl h, (h m m' hp).2⟩
  refine Fr.leaf hfr1 hN hlk nil_callee slots_le hsl hkpow
    (hQ fun _ _ h ↦ ⟨h.2.1, h.2.2⟩) hpc1 (hfr1.stackOk hS rfl hlk) fun m2 hfr2 hq2 hcs2 ↦ ?_
  have hFW2 := Bus.FrameWords.call hFW1 hfr1.sp (by omega) (by simp) hsl
    ((hQ fun _ _ h ↦ ⟨h.2.1, h.2.2⟩) _ _ hq2).1
  have e2x0 : m2.regs.X0 = gpowK 0 := by rw [hq2.1, e1x0]; rfl
  -- `b1`: `[1, pc, gpow 0]` at `sp + 48`, `dot` with the first three weights.
  have hwf2 := Bus.wf_frame (F := 320) hS hF hfr2.kept
  have hm2 := Bus.match_frame (m := m2) hS hF rfl hfr2.sp
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf2 rfl hm2
    fun st3 hm3 hpc3 ↦ ?_
  have hfr3 := Bus.Fr.block hfr2 hN hF hm3 hwf2 rfl (by decide) (by decide) slots_le
  have hFW3 := Bus.FrameWords.block hFW2 hm3 (by simp; decide)
  have e3x0 : st3.data.regs.X0 = m0.regs.X1 :=
    (UInt64.toBitVec_inj.mp (hm3.regs .X0 _ rfl)).trans ((hcs2 .X21 rfl).trans e1x21)
  have e3x2 : st3.data.regs.X2 = UInt64.ofBitVec (base m0 320 + BitVec.ofNat 64 48) :=
    UInt64.toBitVec_inj.mp (hm3.regs .X2 _ rfl)
  have e3x1 : st3.data.regs.X1 = 3 := UInt64.toBitVec_inj.mp (hm3.regs .X1 _ rfl)
  have e3x3 : st3.data.regs.X3 = 3 := UInt64.toBitVec_inj.mp (hm3.regs .X3 _ rfl)
  have hA1 : NativeRustcVm.EWsAt st3.data.dmem (base m0 320 + BitVec.ofNat 64 48)
      [⟨1, 0⟩, ⟨stackArg m0 8, 0⟩, ⟨gpowK 0, 0⟩] := by
    refine Bus.ewsAt_of_words _ fun i hi ↦ ?_
    simp only [List.length_cons, List.length_nil] at hi
    simp only [NativeRustcVm.addr_add_add]
    match i, hi with
    | 0, _ => exact ⟨Bus.wordAt_write hm3 (r := 0) (o := 48) rfl (by omega) (v := .lit 1) (by decide),
        Bus.wordAt_write hm3 (r := 0) (o := 56) rfl (by omega) (v := .lit 0) (by decide)⟩
    | 1, _ =>
      refine ⟨?_, Bus.wordAt_write hm3 (r := 0) (o := 72) rfl (by omega) (v := .lit 0) (by decide)⟩
      have := Bus.wordAt_write hm3 (r := 0) (o := 64) rfl (by omega) (v := .reg .X24) (by decide)
      simp only [Sym.eval, Env.ofMachine_regs, hcs2 .X24 rfl, e1x24] at this
      exact this
    | 2, _ =>
      refine ⟨?_, Bus.wordAt_write hm3 (r := 0) (o := 88) rfl (by omega) (v := .lit 0) (by decide)⟩
      have := Bus.wordAt_write hm3 (r := 0) (o := 80) rfl (by omega) (v := .reg .X0) (by decide)
      simp only [Sym.eval, Env.ofMachine_regs] at this
      rw [show m2.regs.getXReg .X0 = m2.regs.X0 from rfl, e2x0] at this
      exact this
  have hpre3 : DotPre st3.data := by
    refine ⟨hfr3.stackOk hS rfl hld, ?_, ?_⟩
    · rw [e3x0, e3x1]; exact sliceOk_arg hfr3 hS hW (by decide : 3 ≤ 5) hld 3 rfl
    · rw [e3x2, e3x3, SliceOk]
      exact Bus.local_ok hS hld (by omega : 48 + 16 * 3 ≤ 320) hfr3.kept hfr3.sp
  have hW3 : SliceOk m0 m0.regs.X1 3 fingerprintsStack :=
    ⟨readable_mono hW.1 (by decide), offStack_mono hW.2 (by decide)⟩
  have hWs : ∀ (m : MachineData), Fr m0 320 fingerprintsStack slots [] (fun _ ↦ False) m →
      slice m m0.regs.X1 3 = (ewsOf m0.dmem m0.regs.X1.toBitVec 3).toArray :=
    fun m h ↦ Bus.Fr.slice_eq h hS hW3 fun _ _ h ↦ h
  refine Fr.leaf hfr3 hN hld nil_callee slots_le hsl hdot
    (fun _ _ h ↦ ⟨Bus.changes_zero h.2.1, h.2.2⟩) hpc3 hpre3 fun m4 hfr4 hq4 hcs4 ↦ ?_
  have hFW4 := Bus.FrameWords.call hFW3 hfr3.sp (by omega) (by simp) hsl
    (Bus.changes_zero hq4.2.1)
  have hd1 : ewRet m4 = dot (ewsOf m0.dmem m0.regs.X1.toBitVec 3).toArray
      #[⟨1, 0⟩, ⟨stackArg m0 8, 0⟩, ⟨gpowK 0, 0⟩] := by
    rw [hq4.1, e3x0, e3x1, e3x2, e3x3, slice_of_ewsAt hA1 3 rfl, hWs _ hfr3]
  -- The registers `b0` set and nothing changes afterwards.
  have K1 : Bus.KeepRegs Lfix st1.data m2 := Bus.KeepRegs.of_call hcs2 rfl
  have K3 : Bus.KeepRegs Lfix st1.data st3.data := K1.trans (Bus.KeepRegs.of_block hm3 rfl)
  have K4 : Bus.KeepRegs Lfix st1.data m4 := K3.trans (Bus.KeepRegs.of_call hcs4 rfl)
  -- `b2`: `index_mle_from(memory_low)`.
  have hwf4 := Bus.wf_frame (F := 320) hS hF hfr4.kept
  have hm4 := Bus.match_frame (m := m4) hS hF rfl hfr4.sp
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf4 rfl hm4
    fun st5 hm5 hpc5 ↦ ?_
  have hfr5 := Bus.Fr.block hfr4 hN hF hm5 hwf4 rfl (by decide) (by decide) slots_le
  have hFW5 := Bus.FrameWords.block hFW4 hm5 (by simp [findWrite])
  have K5 : Bus.KeepRegs Lfix st1.data st5.data := K4.trans (Bus.KeepRegs.of_block hm5 rfl)
  have e5x24 : st5.data.regs.getXReg .X24 = m4.regs.X0 := UInt64.toBitVec_inj.mp (hm5.regs .X24 _ rfl)
  have e5x25 : st5.data.regs.getXReg .X25 = m4.regs.X1 := UInt64.toBitVec_inj.mp (hm5.regs .X25 _ rfl)
  have e5x0 : st5.data.regs.X0 = m0.regs.X3 :=
    (UInt64.toBitVec_inj.mp (hm5.regs .X0 _ rfl)).trans ((hcs4 .X27 rfl).trans
      ((Bus.keep_reg hm3 rfl).trans ((hcs2 .X27 rfl).trans e1x27)))
  have e5x1 : st5.data.regs.X1 = m0.regs.X4 :=
    (UInt64.toBitVec_inj.mp (hm5.regs .X1 _ rfl)).trans ((hcs4 .X26 rfl).trans
      ((Bus.keep_reg hm3 rfl).trans ((hcs2 .X26 rfl).trans e1x26)))
  have e5x28 : st5.data.regs.getXReg .X28 = m0.regs.X2 :=
    (Bus.keep_reg hm5 rfl).trans ((hcs4 .X28 rfl).trans
      ((Bus.keep_reg hm3 rfl).trans ((hcs2 .X28 rfl).trans e1x28)))
  have hpre5 : IndexMleFromPre st5.data := by
    refine ⟨hfr5.stackOk hS rfl hli, ?_⟩
    rw [e5x0, e5x1]
    exact ⟨Bus.Fr.readable hfr5 hML.1, Bus.Fr.offStack hfr5 hS hML.2 hli⟩
  refine Fr.leaf hfr5 hN hli nil_callee slots_le hsl himf
    (fun _ _ h ↦ ⟨Bus.changes_zero h.2.1, h.2.2⟩) hpc5 hpre5 fun m6 hfr6 hq6 hcs6 ↦ ?_
  have hFW6 := Bus.FrameWords.call hFW5 hfr5.sp (by omega) (by simp) hsl
    (Bus.changes_zero hq6.2.1)
  have K6 : Bus.KeepRegs Lfix st1.data m6 := K5.trans (Bus.KeepRegs.of_call hcs6 rfl)
  have himl : ewRet m6 = indexMleFrom gen (slice m0 m0.regs.X3 m0.regs.X4) := by
    rw [hq6.1, e5x0, e5x1, Bus.Fr.slice_eq hfr5 hS hML fun _ _ h ↦ h]
  -- `b3`: `[g, index_mle(memory_low), memory_count, memory[0], memory[1]]` at `sp + 96`.
  have e6x28 : m6.regs.getXReg .X28 = m0.regs.X2 := (hcs6 .X28 rfl).trans e5x28
  have hwf6 := Bus.wf_frame2 (F := 320) hS hF hfr6.kept (a := m0.regs.X2.toBitVec) (n := 32)
    hM.1 hM.2
  have hm6 := Bus.match_frame2 (m := m6) (r := .X28) (n := 32) hS hF rfl hfr6.sp
  rw [e6x28] at hm6
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf6 rfl hm6
    fun st7 hm7 hpc7 ↦ ?_
  have hfr7 := Bus.Fr.block hfr6 hN hF hm7 hwf6 rfl (by decide) (by decide) slots_le
  have hFW7 := Bus.FrameWords.block hFW6 hm7 (by simp; decide)
  have K7 : Bus.KeepRegs Lfix st1.data st7.data := K6.trans (Bus.KeepRegs.of_block hm7 rfl)
  have e7x0 : st7.data.regs.X0 = m0.regs.X1 :=
    (UInt64.toBitVec_inj.mp (hm7.regs .X0 _ rfl)).trans ((K6 .X21 (by simp)).trans e1x21)
  have e7x1 : st7.data.regs.X1 = 5 := UInt64.toBitVec_inj.mp (hm7.regs .X1 _ rfl)
  have e7x2 : st7.data.regs.X2 = UInt64.ofBitVec (base m0 320 + BitVec.ofNat 64 96) :=
    UInt64.toBitVec_inj.mp (hm7.regs .X2 _ rfl)
  have e7x3 : st7.data.regs.X3 = 5 := UInt64.toBitVec_inj.mp (hm7.regs .X3 _ rfl)
  have hmem6 : ewsOf m6.dmem m0.regs.X2.toBitVec 2 = ewsOf m0.dmem m0.regs.X2.toBitVec 2 :=
    Bus.Fr.ewsOf_eq hfr6 hS hM.1.2 hM.2 fun _ _ h ↦ h
  have L1 := Bus.load_r1 m6 (base m0 320) m0.regs.X2.toBitVec 320 32
  have hA2 : NativeRustcVm.EWsAt st7.data.dmem (base m0 320 + BitVec.ofNat 64 96)
      (gen :: ewRet m6 :: ⟨stackArg m0 16, stackArg m0 24⟩ ::
        ewsOf m6.dmem m0.regs.X2.toBitVec 2) := by
    rw [Bus.ewsOf_two]
    refine Bus.ewsAt_of_words _ fun i hi ↦ ?_
    simp only [List.length_cons, List.length_nil] at hi
    simp only [NativeRustcVm.addr_add_add]
    match i, hi with
    | 0, _ =>
      exact ⟨Bus.wordAt_write hm7 (r := 0) (o := 96) rfl (by omega) (v := .lit 2) (by decide),
        Bus.wordAt_write hm7 (r := 0) (o := 104) rfl (by omega) (v := .lit 0) (by decide)⟩
    | 1, _ =>
      exact ⟨Bus.wordAt_write hm7 (r := 0) (o := 112) rfl (by omega) (v := .reg .X0)
          (by decide),
        Bus.wordAt_write hm7 (r := 0) (o := 120) rfl (by omega) (v := .reg .X1) (by decide)⟩
    | 2, _ =>
      have h1 := Bus.wordAt_write hm7 (r := 0) (o := 128) rfl (by omega) (v := .reg .X29)
        (by decide)
      have h2 := Bus.wordAt_write hm7 (r := 0) (o := 136) rfl (by omega) (v := .reg .X19)
        (by decide)
      simp only [Sym.eval, Env.ofMachine_regs, (K6 .X29 (by simp)), (K6 .X19 (by simp)), e1x29,
        e1x19] at h1 h2
      exact ⟨h1, h2⟩
    | 3, _ =>
      have h1 := Bus.wordAt_write hm7 (r := 0) (o := 144) rfl (by omega) (v := .load 1 0 8)
        (by decide)
      have h2 := Bus.wordAt_write hm7 (r := 0) (o := 152) rfl (by omega) (v := .load 1 8 8)
        (by decide)
      rw [L1] at h1 h2
      exact ⟨h1, h2⟩
    | 4, _ =>
      have h1 := Bus.wordAt_write hm7 (r := 0) (o := 160) rfl (by omega) (v := .load 1 16 8)
        (by decide)
      have h2 := Bus.wordAt_write hm7 (r := 0) (o := 168) rfl (by omega) (v := .load 1 24 8)
        (by decide)
      rw [L1] at h1 h2
      exact ⟨h1, h2⟩
    | n + 5, h => exact absurd h (by omega)
  have hpre7 : DotPre st7.data := by
    refine ⟨hfr7.stackOk hS rfl hld, ?_, ?_⟩
    · rw [e7x0, e7x1]; exact sliceOk_arg hfr7 hS hW (by decide : 5 ≤ 5) hld 5 rfl
    · rw [e7x2, e7x3, SliceOk]
      exact Bus.local_ok hS hld (by omega : 96 + 16 * 5 ≤ 320) hfr7.kept hfr7.sp
  have hW5 : SliceOk m0 m0.regs.X1 5 fingerprintsStack :=
    ⟨readable_mono hW.1 (by decide), offStack_mono hW.2 (by decide)⟩
  have hWs5 : ∀ (m : MachineData), Fr m0 320 fingerprintsStack slots [] (fun _ ↦ False) m →
      slice m m0.regs.X1 5 = (ewsOf m0.dmem m0.regs.X1.toBitVec 5).toArray :=
    fun m h ↦ Bus.Fr.slice_eq h hS hW5 fun _ _ h ↦ h
  refine Fr.leaf hfr7 hN hld nil_callee slots_le hsl hdot
    (fun _ _ h ↦ ⟨Bus.changes_zero h.2.1, h.2.2⟩) hpc7 hpre7 fun m8 hfr8 hq8 hcs8 ↦ ?_
  have hFW8 := Bus.FrameWords.call hFW7 hfr7.sp (by omega) (by simp) hsl
    (Bus.changes_zero hq8.2.1)
  have K8 : Bus.KeepRegs Lfix st1.data m8 := K7.trans (Bus.KeepRegs.of_call hcs8 rfl)
  have hd2 : ewRet m8 = dot (ewsOf m0.dmem m0.regs.X1.toBitVec 5).toArray
      (gen :: ewRet m6 :: ⟨stackArg m0 16, stackArg m0 24⟩ ::
        ewsOf m0.dmem m0.regs.X2.toBitVec 2).toArray := by
    rw [hq8.1, e7x0, e7x1, e7x2, e7x3, slice_of_ewsAt hA2 5 (by simp), hWs5 _ hfr7, hmem6]
  -- `b4`: `kpow(2)`.
  have hwf8 := Bus.wf_frame (F := 320) hS hF hfr8.kept
  have hm8 := Bus.match_frame (m := m8) hS hF rfl hfr8.sp
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf8 rfl hm8
    fun st9 hm9 hpc9 ↦ ?_
  have hfr9 := Bus.Fr.block hfr8 hN hF hm9 hwf8 rfl (by decide) (by decide) slots_le
  have hFW9 := Bus.FrameWords.block hFW8 hm9 (by simp [findWrite])
  have K9 : Bus.KeepRegs Lfix st1.data st9.data := K8.trans (Bus.KeepRegs.of_block hm9 rfl)
  have e9x0 : st9.data.regs.X0 = 2 := UInt64.toBitVec_inj.mp (hm9.regs .X0 _ rfl)
  have e9x26 : st9.data.regs.getXReg .X26 = m8.regs.X0 :=
    UInt64.toBitVec_inj.mp (hm9.regs .X26 _ rfl)
  have e9x27 : st9.data.regs.getXReg .X27 = m8.regs.X1 :=
    UInt64.toBitVec_inj.mp (hm9.regs .X27 _ rfl)
  refine Fr.leaf hfr9 hN hlk nil_callee slots_le hsl hkpow
    (hQ fun _ _ h ↦ ⟨h.2.1, h.2.2⟩) hpc9 (hfr9.stackOk hS rfl hlk) fun m10 hfr10 hq10 hcs10 ↦ ?_
  have hFW10 := Bus.FrameWords.call hFW9 hfr9.sp (by omega) (by simp) hsl
    ((hQ fun _ _ h ↦ ⟨h.2.1, h.2.2⟩) _ _ hq10).1
  have K10 : Bus.KeepRegs Lfix st1.data m10 := K9.trans (Bus.KeepRegs.of_call hcs10 rfl)
  have e10x0 : m10.regs.X0 = gpowK 2 := by rw [hq10.1, e9x0]; rfl
  -- `b5`: `index_mle_from(bytecode_low)`.
  have hwf10 := Bus.wf_frame (F := 320) hS hF hfr10.kept
  have hm10 := Bus.match_frame (m := m10) hS hF rfl hfr10.sp
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf10 rfl hm10
    fun st11 hm11 hpc11 ↦ ?_
  have hfr11 := Bus.Fr.block hfr10 hN hF hm11 hwf10 rfl (by decide) (by decide) slots_le
  have hFW11 := Bus.FrameWords.block hFW10 hm11 (by simp [findWrite])
  have K11 : Bus.KeepRegs Lfix st1.data st11.data := K10.trans (Bus.KeepRegs.of_block hm11 rfl)
  have e11x28 : st11.data.regs.getXReg .X28 = gpowK 2 :=
    (UInt64.toBitVec_inj.mp (hm11.regs .X28 _ rfl)).trans e10x0
  have e11x0 : st11.data.regs.X0 = m0.regs.X5 :=
    (UInt64.toBitVec_inj.mp (hm11.regs .X0 _ rfl)).trans ((K10 .X23 (by simp)).trans e1x23)
  have e11x1 : st11.data.regs.X1 = m0.regs.X6 :=
    (UInt64.toBitVec_inj.mp (hm11.regs .X1 _ rfl)).trans ((K10 .X22 (by simp)).trans e1x22)
  have hpre11 : IndexMleFromPre st11.data := by
    refine ⟨hfr11.stackOk hS rfl hli, ?_⟩
    rw [e11x0, e11x1]
    exact ⟨Bus.Fr.readable hfr11 hBL.1, Bus.Fr.offStack hfr11 hS hBL.2 hli⟩
  refine Fr.leaf hfr11 hN hli nil_callee slots_le hsl himf
    (fun _ _ h ↦ ⟨Bus.changes_zero h.2.1, h.2.2⟩) hpc11 hpre11 fun m12 hfr12 hq12 hcs12 ↦ ?_
  have hFW12 := Bus.FrameWords.call hFW11 hfr11.sp (by omega) (by simp) hsl
    (Bus.changes_zero hq12.2.1)
  have K12 : Bus.KeepRegs Lfix st1.data m12 := K11.trans (Bus.KeepRegs.of_call hcs12 rfl)
  have himl2 : ewRet m12 = indexMleFrom gen (slice m0 m0.regs.X5 m0.regs.X6) := by
    rw [hq12.1, e11x0, e11x1, Bus.Fr.slice_eq hfr11 hS hBL fun _ _ h ↦ h]
  -- `b6`: `[g², index_mle(bytecode_low), bytecode_count]` at `sp + 176`, `dot`.
  have hwf12 := Bus.wf_frame (F := 320) hS hF hfr12.kept
  have hm12 := Bus.match_frame (m := m12) hS hF rfl hfr12.sp
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf12 rfl hm12
    fun st13 hm13 hpc13 ↦ ?_
  have hfr13 := Bus.Fr.block hfr12 hN hF hm13 hwf12 rfl (by decide) (by decide) slots_le
  have hFW13 := Bus.FrameWords.block hFW12 hm13 (by simp; decide)
  have K13 : Bus.KeepRegs Lfix st1.data st13.data := K12.trans (Bus.KeepRegs.of_block hm13 rfl)
  have e12x28 : m12.regs.getXReg .X28 = gpowK 2 := (hcs12 .X28 rfl).trans e11x28
  have e13x0 : st13.data.regs.X0 = m0.regs.X1 :=
    (UInt64.toBitVec_inj.mp (hm13.regs .X0 _ rfl)).trans ((K12 .X21 (by simp)).trans e1x21)
  have e13x1 : st13.data.regs.X1 = 3 := UInt64.toBitVec_inj.mp (hm13.regs .X1 _ rfl)
  have e13x2 : st13.data.regs.X2 = UInt64.ofBitVec (base m0 320 + BitVec.ofNat 64 176) :=
    UInt64.toBitVec_inj.mp (hm13.regs .X2 _ rfl)
  have e13x3 : st13.data.regs.X3 = 3 := UInt64.toBitVec_inj.mp (hm13.regs .X3 _ rfl)
  have hL16 : (Sym.load 0 16 8).eval (Env.ofMachine m12 [(base m0 320, 320)]) =
      (stackArg m0 32).toBitVec := load_word (hFW12 (16, stackArg m0 32) (by simp))
  have hL24 : (Sym.load 0 24 8).eval (Env.ofMachine m12 [(base m0 320, 320)]) =
      (stackArg m0 40).toBitVec := load_word (hFW12 (24, stackArg m0 40) (by simp))
  have hA3 : NativeRustcVm.EWsAt st13.data.dmem (base m0 320 + BitVec.ofNat 64 176)
      [⟨gpowK 2, 0⟩, ewRet m12, ⟨stackArg m0 32, stackArg m0 40⟩] := by
    refine Bus.ewsAt_of_words _ fun i hi ↦ ?_
    simp only [List.length_cons, List.length_nil] at hi
    simp only [NativeRustcVm.addr_add_add]
    match i, hi with
    | 0, _ =>
      have h1 := Bus.wordAt_write hm13 (r := 0) (o := 176) rfl (by omega) (v := .reg .X28)
        (by decide)
      simp only [Sym.eval, Env.ofMachine_regs, e12x28] at h1
      exact ⟨h1, Bus.wordAt_write hm13 (r := 0) (o := 184) rfl (by omega) (v := .lit 0)
        (by decide)⟩
    | 1, _ =>
      exact ⟨Bus.wordAt_write hm13 (r := 0) (o := 192) rfl (by omega) (v := .reg .X0)
          (by decide),
        Bus.wordAt_write hm13 (r := 0) (o := 200) rfl (by omega) (v := .reg .X1) (by decide)⟩
    | 2, _ =>
      have h1 := Bus.wordAt_write hm13 (r := 0) (o := 208) rfl (by omega) (v := .load 0 16 8)
        (by decide)
      have h2 := Bus.wordAt_write hm13 (r := 0) (o := 216) rfl (by omega) (v := .load 0 24 8)
        (by decide)
      rw [hL16] at h1
      rw [hL24] at h2
      exact ⟨h1, h2⟩
    | n + 3, h => exact absurd h (by omega)
  have hpre13 : DotPre st13.data := by
    refine ⟨hfr13.stackOk hS rfl hld, ?_, ?_⟩
    · rw [e13x0, e13x1]; exact sliceOk_arg hfr13 hS hW (by decide : 3 ≤ 5) hld 3 rfl
    · rw [e13x2, e13x3, SliceOk]
      exact Bus.local_ok hS hld (by omega : 176 + 16 * 3 ≤ 320) hfr13.kept hfr13.sp
  refine Fr.leaf hfr13 hN hld nil_callee slots_le hsl hdot
    (fun _ _ h ↦ ⟨Bus.changes_zero h.2.1, h.2.2⟩) hpc13 hpre13 fun m14 hfr14 hq14 hcs14 ↦ ?_
  have hFW14 := Bus.FrameWords.call hFW13 hfr13.sp (by omega) (by simp) hsl
    (Bus.changes_zero hq14.2.1)
  have K14 : Bus.KeepRegs Lfix st1.data m14 := K13.trans (Bus.KeepRegs.of_call hcs14 rfl)
  have hd3 : ewRet m14 = dot (ewsOf m0.dmem m0.regs.X1.toBitVec 3).toArray
      #[⟨gpowK 2, 0⟩, ewRet m12, ⟨stackArg m0 32, stackArg m0 40⟩] := by
    rw [hq14.1, e13x0, e13x1, e13x2, e13x3, slice_of_ewsAt hA3 3 rfl, hWs _ hfr13]
  have KA : Bus.KeepRegs [.X24, .X25] st5.data m14 :=
    (Bus.KeepRegs.of_call hcs6 rfl).trans <| (Bus.KeepRegs.of_block hm7 rfl).trans <|
      (Bus.KeepRegs.of_call hcs8 rfl).trans <| (Bus.KeepRegs.of_block hm9 rfl).trans <|
      (Bus.KeepRegs.of_call hcs10 rfl).trans <| (Bus.KeepRegs.of_block hm11 rfl).trans <|
      (Bus.KeepRegs.of_call hcs12 rfl).trans <| (Bus.KeepRegs.of_block hm13 rfl).trans
      (Bus.KeepRegs.of_call hcs14 rfl)
  have KB : Bus.KeepRegs [.X26, .X27] st9.data m14 :=
    (Bus.KeepRegs.of_call hcs10 rfl).trans <| (Bus.KeepRegs.of_block hm11 rfl).trans <|
      (Bus.KeepRegs.of_call hcs12 rfl).trans <| (Bus.KeepRegs.of_block hm13 rfl).trans
      (Bus.KeepRegs.of_call hcs14 rfl)
  -- `b7`: the three fingerprints at `out`, the third plus the share; the epilogue.
  have e14x20 : m14.regs.getXReg .X20 = m0.regs.X0 := (K14 .X20 (by simp)).trans e1x20
  have hwf14 := Bus.wf_frame2 (F := 320) hS hF hfr14.kept (a := m0.regs.X0.toBitVec) (n := 48)
    hOR hOS
  have hm14 := Bus.match_frame2 (m := m14) (r := .X20) (n := 48) hS hF rfl hfr14.sp
  rw [e14x20] at hm14
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) run_b7 hwf14 rfl hm14
    fun st15 hm15 hpc15 ↦ ?_
  obtain ⟨hret, hsaved⟩ := hfr14.exit hm15 hwf14 (by decide)
  have hL40 : (Sym.load 0 40 8).eval
      (Env.ofMachine m14 [(base m0 320, 320), (m0.regs.X0.toBitVec, 48)]) =
      m0.regs.X7.toBitVec := load_word (hFW14 (40, m0.regs.X7) (by simp))
  have hL32 : (Sym.load 0 32 8).eval
      (Env.ofMachine m14 [(base m0 320, 320), (m0.regs.X0.toBitVec, 48)]) =
      (stackArg m0 0).toBitVec := load_word (hFW14 (32, stackArg m0 0) (by simp))
  have hOut : NativeRustcVm.EWsAt st15.data.dmem m0.regs.X0.toBitVec
      [ewRet m4, ewRet m8, ewRet m14 + ⟨m0.regs.X7, stackArg m0 0⟩] := by
    refine Bus.ewsAt_of_words _ fun i hi ↦ ?_
    simp only [List.length_cons, List.length_nil] at hi
    match i, hi with
    | 0, _ =>
      have h1 := Bus.wordAt_write hm15 (r := 1) (o := 0) rfl (by omega) (v := .reg .X24)
        (by decide)
      have h2 := Bus.wordAt_write hm15 (r := 1) (o := 8) rfl (by omega) (v := .reg .X25)
        (by decide)
      simp only [Sym.eval, Env.ofMachine_regs, (KA .X24 (by simp)), (KA .X25 (by simp)), e5x24,
        e5x25] at h1 h2
      exact ⟨h1, h2⟩
    | 1, _ =>
      have h1 := Bus.wordAt_write hm15 (r := 1) (o := 16) rfl (by omega) (v := .reg .X26)
        (by decide)
      have h2 := Bus.wordAt_write hm15 (r := 1) (o := 24) rfl (by omega) (v := .reg .X27)
        (by decide)
      simp only [Sym.eval, Env.ofMachine_regs, (KB .X26 (by simp)), (KB .X27 (by simp)), e9x26,
        e9x27] at h1 h2
      exact ⟨h1, h2⟩
    | 2, _ =>
      have h1 := Bus.wordAt_write hm15 (r := 1) (o := 32) rfl (by omega)
        (v := .bin .eor .W64 (.reg .X0) (.load 0 40 8)) (by decide)
      have h2 := Bus.wordAt_write hm15 (r := 1) (o := 40) rfl (by omega)
        (v := .bin .eor .W64 (.reg .X1) (.load 0 32 8)) (by decide)
      rw [Bus.eval_eor _ _ _ _ hL40] at h1
      rw [Bus.eval_eor _ _ _ _ hL32] at h2
      exact ⟨h1, h2⟩
    | n + 3, h => exact absurd h (by omega)
  refine .done _ ⟨by simp only [PcOk] at hpc15; rw [hpc15, hret], ?_, ?_, hsaved⟩
  · have hfp : fingerprints (ewsOf m0.dmem m0.regs.X1.toBitVec 5).toArray
        (ewsOf m0.dmem m0.regs.X2.toBitVec 2).toArray (slice m0 m0.regs.X3 m0.regs.X4)
        (slice m0 m0.regs.X5 m0.regs.X6) ⟨m0.regs.X7, stackArg m0 0⟩ (EW.ofK (stackArg m0 8))
        ⟨stackArg m0 16, stackArg m0 24⟩ ⟨stackArg m0 32, stackArg m0 40⟩ =
        #[ewRet m4, ewRet m8, ewRet m14 + ⟨m0.regs.X7, stackArg m0 0⟩] := by
      rw [hd1, hd2, hd3, himl, himl2]
      simp only [fingerprints, extract_ewsOf _ _ (show 3 ≤ 5 by omega),
        extract_ewsOf _ _ (Nat.le_refl 5), List.append_toArray, List.cons_append,
        List.nil_append]
      rfl
    show NativeRustcVm.EWsAt st15.data.dmem m0.regs.X0.toBitVec
      (fingerprints (ewsOf m0.dmem m0.regs.X1.toBitVec 5).toArray
        (ewsOf m0.dmem m0.regs.X2.toBitVec 2).toArray (slice m0 m0.regs.X3 m0.regs.X4)
        (slice m0 m0.regs.X5 m0.regs.X6) ⟨m0.regs.X7, stackArg m0 0⟩ (EW.ofK (stackArg m0 8))
        ⟨stackArg m0 16, stackArg m0 24⟩ ⟨stackArg m0 32, stackArg m0 40⟩).toList
    rw [hfp]
    exact hOut
  · refine NativeRustcVm.SameOutside.mono (NativeRustcVm.SameOutside.trans hfr14.same (hm15.sameOutside hwf14))
      fun q hq ↦ ?_
    rcases hq with (hq | hq) | hq
    · exact .inr hq
    · exact hq.elim
    · exact .inl (Bus.Written.inRange (r := 1) rfl hOR.2 (by decide) hq)
