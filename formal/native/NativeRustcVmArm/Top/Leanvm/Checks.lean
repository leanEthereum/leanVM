module

public import NativeRustcVmArm.Top.Leanvm.Cond

/-!
# `leanvm_verify`: the prologue and the checks

From the entry, `b0` saves the registers and reads the counts, whose checks pass (`cond0`); `b3`
to `b9` read the areas' addresses, which pass the alignment checks (`Aligned`), and the public
input's words: `checks`, to `C1` at `.LLeanvmVerify_10`.
-/

namespace NativeRustcVmArm.Top.Leanvm

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.LeanvmVerify NativeVm
open NativeRustcVm (WordAt WordsAt Region)
open NativeRustcVm.Top (workAreaBytes usedRegions ApartFrom Aligned)
open NativeVm.Transcript (wd)

/-- After the checks: the frame's body; the counts, the areas' addresses and the public input in
registers. -/
public structure C1 (a : NativeVm.Entry.Areas) (bytes : List UInt8) (bytecode : List UInt64)
    (pub : Vector UInt64 4) (m0 st : MachineData) : Prop where
  body : Body m0 128 slots (InStack m0 leanvmVerifyStack) st
  x9 : st.regs.X9 = a.wire
  x10 : st.regs.X10 = pub[3]
  x11 : st.regs.X11 = pub[2]
  x12 : st.regs.X12 = pub[1]
  x13 : st.regs.X13 = pub[0]
  x19 : st.regs.X19 = bytes.length.toUInt64
  x20 : st.regs.X20 = bytecode.length.toUInt64
  x21 : st.regs.X21 = (decodedWords bytes.length).toUInt64
  x22 : st.regs.X22 = a.work
  x23 : st.regs.X23 = a.decoded
  x24 : st.regs.X24 = a.bytecode

public section

/-- A block without writes keeps a body. -/
theorem bodyNo [Labels] {m0 st st' : MachineData} {R : BitVec 64 → Prop} {env : Env}
    {S₀ S₁ : SState} (hB : Body m0 128 slots R st) (hs : 128 ≤ m0.regs.SP.toBitVec.toNat)
    (hm₀ : Match env S₀ st) (hm : Match env S₁ st') (hwf : env.WF) (hd : st.dmem = env.mem0)
    (hk : keepsRegs S₀ S₁ nonslots = true) (hmem : S₁.mem = []) : Body m0 128 slots R st' :=
  hB.block' slotsIn hs hm₀ hm hwf hd hk (fun _ hr hn ↦ nonslot hr hn)
    fun p ⟨w, hw, _⟩ ↦ by rw [hmem] at hw; cases hw

/-- A register a block keeps. -/
theorem keepReg [Labels] {env : Env} {S : SState} {st : MachineData} {r : XReg}
    (hm : Match env S st) (h : S.reg r = some (.reg r)) :
    st.regs.getXReg r = UInt64.ofBitVec (env.regs r) :=
  UInt64.toBitVec_inj.mp (hm.regs r _ h)

variable [Host] {k : Nat}

/-- **The prologue and the counts' checks.** -/
theorem stage0 (hp : Placed code k) {a : NativeVm.Entry.Areas} {bytes : List UInt8}
    {bytecode : List UInt64} {pub : Vector UInt64 4} {m0 : MachineData}
    (hpre : LeanvmVerifyPre a bytes bytecode pub m0) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b3Offset) ∧
      Body m0 128 slots (InStack m0 leanvmVerifyStack) st.data ∧
      Mapped st.data.dmem m0.regs.X0.toBitVec 96 ∧
      st.data.regs.X0 = m0.regs.X0 ∧ st.data.regs.X19 = bytes.length.toUInt64 ∧
      st.data.regs.X20 = bytecode.length.toUInt64 ∧
      st.data.regs.X21 = (decodedWords bytes.length).toUInt64) ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b0Offset)⟩ := by
  have g := geo_of hpre
  obtain ⟨⟨-, -, hmap⟩, -, hin, -, -, -⟩ := hpre
  have hs := g.s
  have hF := g.F
  have hsb : (m0.regs.SP.toBitVec - BitVec.ofNat 64 leanvmVerifyStack).toNat =
      m0.regs.SP.toBitVec.toNat - 19344 := g.sb
  have hS := leanvmVerifyStack_eq
  have hsl := m0.regs.SP.toBitVec.isLt
  have hce : NativeVm.Entry.ctxWords = 12 := (rfl)
  have gc := g.ctx
  have gcN := g.ctxN
  have e0 : m0.regs.X0.toNat = m0.regs.X0.toBitVec.toNat := rfl
  have hFm : Mapped m0.dmem (frameOf m0) 128 :=
    Mapped.within hmap (by rw [hsb]; omega) (by rw [hsb, hF]; omega) (by rw [hsb, hF]; omega)
  have hcM : Mapped m0.dmem m0.regs.X0.toBitVec 96 :=
    NativeRustcVm.Mapped.mono (NativeRustcVm.mapped_of_wordView hin.ctxSome) (by omega)
  have hcF : (frameOf m0).toNat + 128 ≤ m0.regs.X0.toBitVec.toNat ∨
      m0.regs.X0.toBitVec.toNat + 96 ≤ (frameOf m0).toNat := by omega
  have hwf : (Env.ofMachine m0 [(frameOf m0, 128), (m0.regs.X0.toBitVec, 96)]).WF :=
    Env.wf_of ⟨⟨hFm, show (frameOf m0).toNat + 128 ≤ 2 ^ 64 by omega⟩,
      ⟨hcM, show m0.regs.X0.toBitVec.toNat + 96 ≤ 2 ^ 64 by omega⟩, trivial⟩
      (List.pairwise_pair.mpr hcF)
  have hm : Match (Env.ofMachine m0 [(frameOf m0, 128), (m0.regs.X0.toBitVec, 96)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ show (frameOf m0).toNat % 16 = 0 by have := g.al; omega, rfl,
      fun h ↦ absurd h (by decide), trivial⟩
      (show m0.regs.SP.toBitVec = frameOf m0 + BitVec.ofInt 64 128 by
        rw [show BitVec.ofInt 64 128 = BitVec.ofNat 64 128 from rfl, frameOf,
          BitVec.sub_add_cancel])
      ⟨show (m0.regs.getXReg .X0).toBitVec = m0.regs.X0.toBitVec + BitVec.ofInt 64 0 by
        rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; rfl,
        trivial⟩
      trivial trivial trivial
  have hld : ∀ {i : Nat} {v : UInt64},
      NativeRustcVm.wordView m0.dmem (wd m0.regs.X0 i) = some v →
      (Env.ofMachine m0 [(frameOf m0, 128), (m0.regs.X0.toBitVec, 96)]).load 1 (8 * i) 8 =
        v.toBitVec := fun h ↦ load_wordAt (r := 1) (ctxWord h)
  obtain ⟨v9, h9, hv9⟩ := hin.decLen
  obtain ⟨v11, h11, hv11⟩ := hin.workLen
  have hww : 61944 ≤ v11.toNat := by
    have := NativeRustcVm.Top.workAreaWords_le
    unfold NativeRustcVm.Top.workAreaWords at this; omega
  have hn : bytecode.length ≤ 536870910 := by have := hin.bcSmall; omega
  refine exec_then (hb NativeRustcVmArm.Vm.LeanvmVerify.b0Offset hp b0_in_code (by simp [b0])) run_b0 hwf hm fun st1 hm1 hpc1 ↦ ?_
  have hB1 : Body m0 128 slots (InStack m0 leanvmVerifyStack) st1.data := by
    refine ⟨?_, fun p hp' ↦ ?_, fun r hr hn' ↦ ?_, fun q hq ↦ ?_, hm1.kept hwf⟩
    · rw [hm1.sp]; show frameOf m0 + BitVec.ofInt 64 0 = _; simp [frameOf]
    · have hw := b0_slots p hp'
      rw [after_eq run_b0] at hw
      have hsl' : p.1 + 8 ≤ 128 := by
        simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp'
        rcases hp' with h | h | h | h | h | h | h <;> rw [h] <;> decide
      exact hm1.bytesAt_write (r := 0) (b := frameOf m0) (sz := 128) rfl hsl' hw
    · have h := b0_regs r (nonslot hr hn')
      rw [after_eq run_b0] at h
      exact UInt64.toBitVec_inj.mp (hm1.regs r _ h)
    · refine hm1.get?_mem0 hwf fun hw ↦ hq ?_
      have hb0m := b0_mem
      rw [after_eq run_b0] at hb0m
      have := written_sub (r := 0) rfl hb0m hw
      unfold InStack
      rw [leanvmVerifyStack_eq]
      omega
  have hX0 : st1.data.regs.X0 = m0.regs.X0 := by
    apply UInt64.toBitVec_inj.mp
    show (st1.data.regs.getXReg .X0).toBitVec = _
    rw [hm1.regs .X0 _ rfl]
    show m0.regs.X0.toBitVec + BitVec.ofInt 64 0 = _
    simp
  have l8 := hld (i := 1) hin.wireLen
  have l24 := hld (i := 3) hin.bcLen
  have l72 := hld (i := 9) h9
  have l88 := hld (i := 11) h11
  have hX19 : st1.data.regs.X19 = bytes.length.toUInt64 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X19 _ rfl).trans l8)
  have hX20 : st1.data.regs.X20 = bytecode.length.toUInt64 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X20 _ rfl).trans l24)
  have hX21 : st1.data.regs.X21 = (decodedWords bytes.length).toUInt64 := by
    apply UInt64.toBitVec_inj.mp
    rw [show st1.data.regs.X21.toBitVec = (st1.data.regs.getXReg .X21).toBitVec from rfl,
      hm1.regs .X21 _ rfl]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64,
      NativeRustcVmArm.Field.ubfm_lsr _ _ (show 3 < 64 by decide)]
    rw [show (Env.ofMachine m0 [(frameOf m0, 128), (m0.regs.X0.toBitVec, 96)]).load 1 8 8 =
      BitVec.ofNat 64 bytes.length from l8]
    apply BitVec.eq_of_toNat_eq
    rw [dw_toNat hin.L32]
    show _ = (decodedWords bytes.length) % 2 ^ 64
    have := g.decN
    omega
  simp only [PcOk] at hpc1
  rw [ite_eq_left (cond0 _ l8 l24 l72 l88 hin.L32 hn hv9 hww), lbl_3 hp] at hpc1
  exact Eventually.done _ ⟨hpc1, hB1, Mapped.kept hcM hB1.kept, hX0, hX19, hX20, hX21⟩

omit [Host] in
/-- A register a block keeps, in an environment of the state before it. -/
theorem keepReg' [Labels] (r : XReg) {st st' : MachineData} {regions : List (BitVec 64 × Nat)}
    {S : SState} (hm : Match (Env.ofMachine st regions) S st')
    (h : S.reg r = some (.reg r)) : st'.regs.getXReg r = st.regs.getXReg r :=
  UInt64.toBitVec_inj.mp (hm.regs r _ h)

omit [Host] in
/-- X0 after a block run with the context as region 1. -/
theorem x0_ctx [Labels] {st st' m0 : MachineData} {F : BitVec 64} {S : SState}
    (hm : Match (Env.ofMachine st [(F, 128), (m0.regs.X0.toBitVec, 96)]) S st')
    (h : S.reg .X0 = some (.ptr 1 0)) : st'.regs.X0 = m0.regs.X0 := by
  apply UInt64.toBitVec_inj.mp
  show (st'.regs.getXReg .X0).toBitVec = _
  rw [hm.regs .X0 _ h]
  show m0.regs.X0.toBitVec + BitVec.ofInt 64 0 = _
  rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]

omit [Host] in
theorem evalRegNat0 [Labels] (env : Env) {r : XReg} {x : Nat}
    (h : env.regs r = BitVec.ofNat 64 x) (hx : x < 2 ^ 64) :
    (SBool.cmp .eq .W64 (.reg r) (.lit 0)).eval env = decide (x = 0) := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, h]
  exact ofNat_beq hx (by decide)

omit [Host] in
/-- `C1` across a block without memory that keeps its registers. -/
theorem C1.step [Labels] {a : NativeVm.Entry.Areas} {bytes : List UInt8} {bytecode : List UInt64}
    {pub : Vector UInt64 4} {m0 st st' : MachineData} {S : SState}
    (h : C1 a bytes bytecode pub m0 st) (hs : 128 ≤ m0.regs.SP.toBitVec.toNat)
    (hm : Match (Env.ofMachine st []) S st') (hk : keepsRegs noneS S nonslots = true)
    (hmem : S.mem = []) (r9 : S.reg .X9 = some (.reg .X9))
    (r10 : S.reg .X10 = some (.reg .X10)) (r11 : S.reg .X11 = some (.reg .X11))
    (r12 : S.reg .X12 = some (.reg .X12)) (r13 : S.reg .X13 = some (.reg .X13))
    (r19 : S.reg .X19 = some (.reg .X19)) (r20 : S.reg .X20 = some (.reg .X20))
    (r21 : S.reg .X21 = some (.reg .X21)) (r22 : S.reg .X22 = some (.reg .X22))
    (r23 : S.reg .X23 = some (.reg .X23)) (r24 : S.reg .X24 = some (.reg .X24)) :
    C1 a bytes bytecode pub m0 st' :=
  ⟨bodyNo h.body hs (match_nil _) hm (Env.wf_nil _) rfl hk hmem,
    (keepReg' _ hm r9).trans h.x9, (keepReg' _ hm r10).trans h.x10,
    (keepReg' _ hm r11).trans h.x11, (keepReg' _ hm r12).trans h.x12,
    (keepReg' _ hm r13).trans h.x13, (keepReg' _ hm r19).trans h.x19,
    (keepReg' _ hm r20).trans h.x20, (keepReg' _ hm r21).trans h.x21,
    (keepReg' _ hm r22).trans h.x22, (keepReg' _ hm r23).trans h.x23,
    (keepReg' _ hm r24).trans h.x24⟩

omit [Host] in
/-- The frame and the context as a block's regions. -/
theorem ctxEnv [Labels] {a : NativeVm.Entry.Areas} {L n : Nat} {m0 st : MachineData}
    {R : BitVec 64 → Prop} (g : Geo a L n m0) (hB : Body m0 128 slots R st)
    (hcM : Mapped st.dmem m0.regs.X0.toBitVec 96) (hx0 : st.regs.X0 = m0.regs.X0)
    (hFm : Mapped st.dmem (frameOf m0) 128) :
    (Env.ofMachine st [(frameOf m0, 128), (m0.regs.X0.toBitVec, 96)]).WF ∧
      Match (Env.ofMachine st [(frameOf m0, 128), (m0.regs.X0.toBitVec, 96)]) ctxS st := by
  have hs := g.s
  have hF := g.F
  have hsl := m0.regs.SP.toBitVec.isLt
  have hce : NativeVm.Entry.ctxWords = 12 := (rfl)
  have gc := g.ctx
  have gcN := g.ctxN
  have e0 : m0.regs.X0.toNat = m0.regs.X0.toBitVec.toNat := rfl
  have hcF : (frameOf m0).toNat + 128 ≤ m0.regs.X0.toBitVec.toNat ∨
      m0.regs.X0.toBitVec.toNat + 96 ≤ (frameOf m0).toNat := by omega
  refine ⟨Env.wf_of ⟨⟨hFm, show (frameOf m0).toNat + 128 ≤ 2 ^ 64 by omega⟩,
      ⟨hcM, show m0.regs.X0.toBitVec.toNat + 96 ≤ 2 ^ 64 by omega⟩, trivial⟩
      (List.pairwise_pair.mpr hcF), ?_⟩
  exact match_ofMachine ⟨rfl, fun _ ↦ show (frameOf m0).toNat % 16 = 0 by have := g.al; omega,
      rfl, fun h ↦ absurd h (by decide), trivial⟩
      (show st.regs.SP.toBitVec = frameOf m0 + BitVec.ofInt 64 0 by rw [hB.sp]; simp [frameOf])
      ⟨show (st.regs.getXReg .X0).toBitVec = m0.regs.X0.toBitVec + BitVec.ofInt 64 0 by
        rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
        exact congrArg UInt64.toBitVec hx0, trivial⟩
      trivial trivial trivial

/-- **The areas' checks**, from `.LLeanvmVerify_3` to `.LLeanvmVerify_10`. -/
theorem stage1 (hp : Placed code k) {a : NativeVm.Entry.Areas} {bytes : List UInt8}
    {bytecode : List UInt64} {pub : Vector UInt64 4} {m0 : MachineData}
    (hpre : LeanvmVerifyPre a bytes bytecode pub m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b3Offset))
    (hB : Body m0 128 slots (InStack m0 leanvmVerifyStack) st.data)
    (hcM : Mapped st.data.dmem m0.regs.X0.toBitVec 96) (hx0 : st.data.regs.X0 = m0.regs.X0)
    (hx19 : st.data.regs.X19 = bytes.length.toUInt64)
    (hx20 : st.data.regs.X20 = bytecode.length.toUInt64)
    (hx21 : st.data.regs.X21 = (decodedWords bytes.length).toUInt64) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b10Offset) ∧
      C1 a bytes bytecode pub m0 st'.data) st := by
  have g := geo_of hpre
  obtain ⟨⟨-, -, hmap⟩, -, hin, hal, -, -⟩ := hpre
  have hs := g.s
  have hF := g.F
  have hsb : (m0.regs.SP.toBitVec - BitVec.ofNat 64 leanvmVerifyStack).toNat =
      m0.regs.SP.toBitVec.toNat - 19344 := g.sb
  have hS := leanvmVerifyStack_eq
  have hsl := m0.regs.SP.toBitVec.isLt
  have hce : NativeVm.Entry.ctxWords = 12 := (rfl)
  have gc := g.ctx
  have gcN := g.ctxN
  have e0 : m0.regs.X0.toNat = m0.regs.X0.toBitVec.toNat := rfl
  have hs128 : 128 ≤ m0.regs.SP.toBitVec.toNat := by omega
  have hFm : Mapped st.data.dmem (frameOf m0) 128 :=
    Mapped.kept (Mapped.within hmap (by rw [hsb]; omega) (by rw [hsb, hF]; omega)
      (by rw [hsb, hF]; omega)) hB.kept
  -- The context's words, kept.
  have hW : ∀ {i : Nat} {v : UInt64}, i < 12 →
      NativeRustcVm.wordView m0.dmem (wd m0.regs.X0 i) = some v →
      WordAt st.data.dmem (m0.regs.X0.toBitVec + BitVec.ofNat 64 (8 * i)) v := fun hi h ↦
    bytesAt_keep (ctxWord h) hB.same (by
        rw [NativeRustcVm.length_wordBytes, toNat_addr (by omega)]; omega) fun q hq ↦ by
      rw [NativeRustcVm.length_wordBytes, toNat_addr (by omega)]
      unfold InStack at hq; rw [hS] at hq; omega
  -- `b3`: the decoded area's address.
  obtain ⟨hwf3, hm3⟩ := ctxEnv g hB hcM hx0 hFm
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b3Offset hp b3_in_code (by simp [b3])) run_b3 hwf3 hpc hm3 fun st3 hm3' hpc3 ↦ ?_
  have hk3 := ctx_keeps.1
  rw [after_eq run_b3] at hk3
  have hB3 := bodyNo hB hs128 hm3 hm3' hwf3 rfl hk3.1 hk3.2
  have hd3 : st3.data.dmem = st.data.dmem := hm3'.dmem_eq hwf3 hk3.2
  have l64 := load_wordAt (r := 1) (env := Env.ofMachine st.data
    [(frameOf m0, 128), (m0.regs.X0.toBitVec, 96)]) (hW (i := 8) (by decide) hin.decPtr)
  have hX23 : st3.data.regs.X23 = a.decoded :=
    UInt64.toBitVec_inj.mp ((hm3'.regs .X23 _ rfl).trans l64)
  simp only [PcOk, evalLoad0 _ l64, hal.dec.1, decide_false, Bool.false_eq_true,
    ite_false, show k + NativeRustcVmArm.Vm.LeanvmVerify.b3Offset + b3.length = k + NativeRustcVmArm.Vm.LeanvmVerify.b4Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b3_next]] at hpc3
  -- `b4`: its alignment.
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b4Offset hp b4_in_code (by simp [b4])) run_b4 (Env.wf_nil _) hpc3 (match_nil _)
    fun st4 hm4 hpc4 ↦ ?_
  have hk4 := none_keeps b4 (by simp)
  rw [after_eq run_b4] at hk4
  have hB4 := bodyNo hB3 hs128 (match_nil _) hm4 (Env.wf_nil _) rfl hk4.1 hk4.2
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq (Env.wf_nil _) hk4.2
  simp only [PcOk, evalAnd7 (Env.ofMachine st3.data []) (r := .X23) (x := a.decoded)
    (congrArg UInt64.toBitVec hX23), hal.dec.2,
    decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
    show k + NativeRustcVmArm.Vm.LeanvmVerify.b4Offset + b4.length = k + NativeRustcVmArm.Vm.LeanvmVerify.b5Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b4_next]] at hpc4
  -- `b5`: the working area's address.
  obtain ⟨hwf5, hm5⟩ := ctxEnv g hB4 (by rw [hd4, hd3]; exact hcM)
    ((keepReg' .X0 hm4 rfl).trans (x0_ctx hm3' rfl))
    (by rw [hd4, hd3]; exact hFm)
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b5Offset hp b5_in_code (by simp [b5])) run_b5 hwf5 hpc4 hm5 fun st5 hm5' hpc5 ↦ ?_
  have hk5 := ctx_keeps.2.1
  rw [after_eq run_b5] at hk5
  have hB5 := bodyNo hB4 hs128 hm5 hm5' hwf5 rfl hk5.1 hk5.2
  have hd5 : st5.data.dmem = st4.data.dmem := hm5'.dmem_eq hwf5 hk5.2
  have l80 := load_wordAt (r := 1) (env := Env.ofMachine st4.data
    [(frameOf m0, 128), (m0.regs.X0.toBitVec, 96)]) (by
      show WordAt st4.data.dmem _ _
      rw [hd4, hd3]; exact hW (i := 10) (by decide) hin.workPtr)
  have hX22 : st5.data.regs.X22 = a.work :=
    UInt64.toBitVec_inj.mp ((hm5'.regs .X22 _ rfl).trans l80)
  simp only [PcOk, evalLoad0 _ l80, hal.work.1, decide_false,
    Bool.false_eq_true, ite_false, show k + NativeRustcVmArm.Vm.LeanvmVerify.b5Offset + b5.length = k + NativeRustcVmArm.Vm.LeanvmVerify.b6Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b5_next]] at hpc5
  -- `b6`: its alignment.
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b6Offset hp b6_in_code (by simp [b6])) run_b6 (Env.wf_nil _) hpc5 (match_nil _)
    fun st6 hm6 hpc6 ↦ ?_
  have hk6 := none_keeps b6 (by simp)
  rw [after_eq run_b6] at hk6
  have hB6 := bodyNo hB5 hs128 (match_nil _) hm6 (Env.wf_nil _) rfl hk6.1 hk6.2
  have hd6 : st6.data.dmem = st5.data.dmem := hm6.dmem_eq (Env.wf_nil _) hk6.2
  simp only [PcOk, evalAnd7 (Env.ofMachine st5.data []) (r := .X22) (x := a.work)
    (congrArg UInt64.toBitVec hX22), hal.work.2,
    decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
    show k + NativeRustcVmArm.Vm.LeanvmVerify.b6Offset + b6.length = k + NativeRustcVmArm.Vm.LeanvmVerify.b7Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b6_next]] at hpc6
  -- `b7`: the wire's and the bytecode's addresses, the public input.
  have hd60 : st6.data.dmem = st.data.dmem := by rw [hd6, hd5, hd4, hd3]
  obtain ⟨hwf7, hm7⟩ := ctxEnv g hB6 (by rw [hd60]; exact hcM)
    ((keepReg' .X0 hm6 rfl).trans (x0_ctx hm5' rfl)) (by rw [hd60]; exact hFm)
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b7Offset hp b7_in_code (by simp [b7])) run_b7 hwf7 hpc6 hm7 fun st7 hm7' hpc7 ↦ ?_
  have hk7 := ctx_keeps.2.2
  rw [after_eq run_b7] at hk7
  have hB7 := bodyNo hB6 hs128 hm7 hm7' hwf7 rfl hk7.1 hk7.2
  have lw : ∀ {i : Nat} {v : UInt64}, i < 12 →
      NativeRustcVm.wordView m0.dmem (wd m0.regs.X0 i) = some v →
      (Env.ofMachine st6.data [(frameOf m0, 128), (m0.regs.X0.toBitVec, 96)]).load 1 (8 * i) 8 =
        v.toBitVec := fun hi h ↦ load_wordAt (r := 1) (by
      show WordAt st6.data.dmem _ _
      rw [hd60]; exact hW hi h)
  have h7 : C1 a bytes bytecode pub m0 st7.data :=
    ⟨hB7,
      UInt64.toBitVec_inj.mp ((hm7'.regs .X9 _ rfl).trans (lw (i := 0) (by decide) hin.wirePtr)),
      UInt64.toBitVec_inj.mp ((hm7'.regs .X10 _ rfl).trans
        (lw (i := 7) (by decide) (hin.pubWords 3 (by decide)))),
      UInt64.toBitVec_inj.mp ((hm7'.regs .X11 _ rfl).trans
        (lw (i := 6) (by decide) (hin.pubWords 2 (by decide)))),
      UInt64.toBitVec_inj.mp ((hm7'.regs .X12 _ rfl).trans
        (lw (i := 5) (by decide) (hin.pubWords 1 (by decide)))),
      UInt64.toBitVec_inj.mp ((hm7'.regs .X13 _ rfl).trans
        (lw (i := 4) (by decide) (hin.pubWords 0 (by decide)))),
      (keepReg' .X19 hm7' rfl).trans ((keepReg' .X19 hm6 rfl).trans
        ((keepReg' .X19 hm5' rfl).trans ((keepReg' .X19 hm4 rfl).trans
        ((keepReg' .X19 hm3' rfl).trans hx19)))),
      (keepReg' .X20 hm7' rfl).trans ((keepReg' .X20 hm6 rfl).trans
        ((keepReg' .X20 hm5' rfl).trans ((keepReg' .X20 hm4 rfl).trans
        ((keepReg' .X20 hm3' rfl).trans hx20)))),
      (keepReg' .X21 hm7' rfl).trans ((keepReg' .X21 hm6 rfl).trans
        ((keepReg' .X21 hm5' rfl).trans ((keepReg' .X21 hm4 rfl).trans
        ((keepReg' .X21 hm3' rfl).trans hx21)))),
      (keepReg' .X22 hm7' rfl).trans ((keepReg' .X22 hm6 rfl).trans hX22),
      (keepReg' .X23 hm7' rfl).trans ((keepReg' .X23 hm6 rfl).trans
        ((keepReg' .X23 hm5' rfl).trans ((keepReg' .X23 hm4 rfl).trans hX23))),
      UInt64.toBitVec_inj.mp ((hm7'.regs .X24 _ rfl).trans (lw (i := 2) (by decide) hin.bcPtr))⟩
  have hn32 := hin.bcSmall
  have hx20' : (Env.ofMachine st6.data [(frameOf m0, 128), (m0.regs.X0.toBitVec, 96)]).regs .X20 =
      BitVec.ofNat 64 bytecode.length :=
    congrArg UInt64.toBitVec ((keepReg' .X20 hm6 rfl).trans ((keepReg' .X20 hm5' rfl).trans
      ((keepReg' .X20 hm4 rfl).trans ((keepReg' .X20 hm3' rfl).trans hx20))))
  simp only [PcOk, evalRegNat0 _ hx20' (by omega)] at hpc7
  by_cases hn0 : bytecode.length = 0
  · simp only [hn0, decide_true, ite_true] at hpc7
    rw [lbl_10 hp] at hpc7
    exact Eventually.done _ ⟨hpc7, h7⟩
  simp only [hn0, decide_false, Bool.false_eq_true, ite_false,
    show k + NativeRustcVmArm.Vm.LeanvmVerify.b7Offset + b7.length = k + NativeRustcVmArm.Vm.LeanvmVerify.b8Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b7_next]] at hpc7
  have hbc := hal.bytecode (by omega)
  -- `b8`, `b9`: the bytecode's address nonzero and aligned.
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b8Offset hp b8_in_code (by simp [b8])) run_b8 (Env.wf_nil _) hpc7 (match_nil _)
    fun st8 hm8 hpc8 ↦ ?_
  have hk8 := none_keeps b8 (by simp)
  rw [after_eq run_b8] at hk8
  have h8 := h7.step hs128 hm8 hk8.1 hk8.2 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  simp only [PcOk, evalReg0 (Env.ofMachine st7.data []) (r := .X24) (x := a.bytecode)
    (congrArg UInt64.toBitVec h7.x24), hbc.1,
    decide_false, Bool.false_eq_true, ite_false, show k + NativeRustcVmArm.Vm.LeanvmVerify.b8Offset + b8.length = k + NativeRustcVmArm.Vm.LeanvmVerify.b9Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b8_next]] at hpc8
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b9Offset hp b9_in_code (by simp [b9])) run_b9 (Env.wf_nil _) hpc8 (match_nil _)
    fun st9 hm9 hpc9 ↦ ?_
  have hk9 := none_keeps b9 (by simp)
  rw [after_eq run_b9] at hk9
  have h9 := h8.step hs128 hm9 hk9.1 hk9.2 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  simp only [PcOk, evalAnd7 (Env.ofMachine st8.data []) (r := .X24) (x := a.bytecode)
    (congrArg UInt64.toBitVec h8.x24), hbc.2,
    decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
    show k + NativeRustcVmArm.Vm.LeanvmVerify.b9Offset + b9.length = k + NativeRustcVmArm.Vm.LeanvmVerify.b10Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b9_next]] at hpc9
  exact Eventually.done _ ⟨hpc9, h9⟩

end

end NativeRustcVmArm.Top.Leanvm
