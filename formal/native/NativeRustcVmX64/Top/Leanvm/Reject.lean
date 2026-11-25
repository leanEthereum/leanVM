module

public import NativeRustcVmX64.Top.Leanvm.Stage2

namespace NativeRustcVmX64.Top.Leanvm

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.LeanvmVerify
open NativeRustcVmX64.Transcript NativeRustcVmX64.Top NativeVm
open NativeRustcVm.Transcript
open NativeRustcVm.Top (Aligned)
open NativeVm.Transcript (wd)

public section

variable [Labels]

omit [Labels] in
private theorem and7_ne {x : BitVec 64} (h : x.toNat % 8 ≠ 0) :
    CmpOp.apply .eq .W8 (BinOp.apply .and .W8 x (BitVec.ofNat 64 7))
      (BitVec.ofNat 64 0) = false := by
  simp only [CmpOp.apply, BinOp.apply, low_ext, beq_eq_false_iff_ne]
  intro he
  have he := congrArg BitVec.toNat he
  rw [BitVec.toNat_and, low8_toNat, low8_toNat] at he
  have e : (BitVec.ofNat 64 7).toNat % 256 = 2 ^ 3 - 1 := by decide
  rw [e, Nat.and_two_pow_sub_one_eq_mod] at he
  simp only [low8_toNat, BitVec.toNat_ofNat] at he
  omega

private theorem reject_b0 (env : Env) {L : Nat}
    (h : env.load 1 8 8 = BitVec.ofNat 64 L) (hL : ¬ L < 2 ^ 32) (h64 : L < 2 ^ 64) :
    (SBool.cmp .eq .W64 (.bin .shr .W64 (.load 1 8 8) (.lit 32)) (.lit 0)).not.eval env = true := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, h,
    shiftCount, shiftMask, Bool.not_eq_true', beq_eq_false_iff_ne]
  intro he
  have he := congrArg BitVec.toNat he
  have e : (low .W8 (BitVec.ofNat 64 32)).toNat &&& 63 = 32 := by decide
  rw [e, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt h64] at he
  change L / 4294967296 = 0 at he
  omega

private theorem reject_b1 (env : Env) {n : Nat}
    (h : env.load 1 24 8 = BitVec.ofNat 64 n) (hn : ¬ n ≤ 536870910) (h64 : n < 2 ^ 64) :
    ((SBool.cmp .ult .W64 (.load 1 24 8) (.lit 536870910)).not.and
      (SBool.cmp .eq .W64 (.load 1 24 8) (.lit 536870910)).not).eval env = true := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, h, Bool.and_eq_true,
    Bool.not_eq_true']
  constructor
  · simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, decide_eq_false_iff_not]
    change ¬ n < 536870910
    omega
  · simp only [beq_eq_false_iff_ne]
    intro he
    have he := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64] at he
    omega

private theorem reject_b2 (env : Env) {L : Nat} {db : BitVec 64}
    (h72 : env.load 1 72 8 = db) (hrbx : env.regs .rbx = BitVec.ofNat 64 L)
    (hL : L < 2 ^ 32) (hd : ¬ decodedWords L ≤ db.toNat) :
    (SBool.cmp .ult .W64 (.load 1 72 8) (.bin .add .W64 (.lit 395289)
      (.bin .or .W64 (.bin .shr .W64 (.reg .rbx) (.lit 3)) (.lit 1)))).eval env = true := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, h72, hrbx]
  have he := dw_toNat (x := BitVec.ofNat 64 L) (by rw [BitVec.toNat_ofNat]; omega) hL
  simp only [BitVec.ult, he, decide_eq_true_eq]
  omega

private theorem reject_b3 (env : Env) {wb : BitVec 64}
    (h88 : env.load 1 88 8 = wb) (hw : ¬ 61944 ≤ wb.toNat) :
    (SBool.cmp .ult .W64 (.load 1 88 8) (.lit 61944)).eval env = true := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, h88, BitVec.ult,
    BitVec.toNat_ofNat, decide_eq_true_eq]
  change wb.toNat < 61944
  omega

private theorem reject_area (env : Env) {o : Nat} {x : BitVec 64}
    (h : env.load 1 o 8 = x) (hbad : ¬ (x ≠ 0 ∧ x.toNat % 8 = 0)) :
    (SBool.cmp .eq .W8 (.bin .or .W8 (.bin .merge .W8 (.reg .rcx)
      (.ite (SBool.cmp .eq .W8 (.bin .and .W8 (.load 1 o 8) (.lit 7)) (.lit 0)).not (.lit 1) (.lit 0)))
      (.bin .merge .W8 (.reg .rax) (.ite (SBool.cmp .eq .W64 (.bin .and .W64 (.load 1 o 8)
        (.load 1 o 8)) (.lit 0)) (.lit 1) (.lit 0)))) (.lit 0)).not.eval env = true := by
  by_cases h0 : x = 0
  · simp only [SBool.eval, Sym.eval, h, h0]
    simp only [CmpOp.apply, BinOp.apply, low_ext, low8_replaceLow, low_W64, ext_W64]
    decide
  · have h8 : x.toNat % 8 ≠ 0 := fun h8 ↦ hbad ⟨h0, h8⟩
    simp only [SBool.eval, Sym.eval, h, and7_ne h8, nz_eq h0, Bool.not_false,
      Bool.false_eq_true, ↓reduceIte]
    simp only [CmpOp.apply, BinOp.apply, low_ext, low8_replaceLow]
    decide

private theorem reject_b7 (env : Env) {x : BitVec 64} (h : env.regs .rbp = x)
    (hbad : ¬ (x ≠ 0 ∧ x.toNat % 8 = 0)) :
    (SBool.cmp .eq .W8 (.bin .and .W8 (.bin .merge .W8 (.reg .rdi)
      (.ite (SBool.cmp .eq .W64 (.bin .and .W64 (.reg .rbp) (.reg .rbp)) (.lit 0)).not (.lit 1)
        (.lit 0)))
      (.bin .merge .W8 (.reg .r9) (.ite (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rbp) (.lit 7))
        (.lit 0)) (.lit 1) (.lit 0)))) (.lit 0)).eval env = true := by
  by_cases h0 : x = 0
  · simp only [SBool.eval, Sym.eval, h, h0]
    simp only [CmpOp.apply, BinOp.apply, low_ext, low8_replaceLow, low_W64, ext_W64]
    decide
  · have h8 : x.toNat % 8 ≠ 0 := fun h8 ↦ hbad ⟨h0, h8⟩
    simp only [SBool.eval, Sym.eval, h, and7_ne h8, nz_eq h0, Bool.not_false,
      Bool.false_eq_true, ↓reduceIte]
    simp only [CmpOp.apply, BinOp.apply, low_ext, low8_replaceLow]
    decide

omit [Labels] in
private theorem zero_b0 : (after b0 entryS).reg .rax = some (.lit 0) := by decide +kernel

omit [Labels] in
private theorem zero_b1 : (after b1 ctxS).reg .rax = some (.reg .rax) := by decide +kernel

omit [Labels] in
private theorem zero_b2 : (after b2 ctxS).reg .rax = some (.reg .rax) := by decide +kernel

omit [Labels] in
private theorem zero_b3 : (after b3 ctxS).reg .rax = some (.reg .rax) := by decide +kernel

end

end NativeRustcVmX64.Top.Leanvm

namespace NativeRustcVmX64.Top.Leanvm

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.LeanvmVerify
open NativeRustcVmX64.Transcript NativeRustcVmX64.Top NativeVm
open NativeRustcVm.Transcript
open NativeRustcVm.Top (Aligned)
open NativeVm.Transcript (wd)

public section

variable [Host] {k : Nat}

/-- A failed entry check returns zero without accessing any caller area beyond the context. -/
theorem reject (hp : Placed code k) {a : NativeVm.Entry.Areas} {bytes : List UInt8}
    {bytecode : List UInt64} {pub : Vector UInt64 4} {m0 : MachineData}
    (hin : NativeVm.Entry.ContextAt m0.dmem (ctxOf m0) a bytes bytecode pub)
    (hst : StackOk m0 leanvmVerifyStack)
    (hctx : NativeRustcVm.Apart (ctxOf m0).toBitVec 96
      (stackBelow m0 leanvmVerifyStack) (leanvmVerifyStack + 8))
    (hbad : ¬ NativeRustcVm.Top.Checks a bytes.length bytecode.length) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m0 ∧
      rspOf st.data = rspOf m0 + 8#64 ∧ reg st.data .rax = 0#64 ∧
      NativeRustcVm.SameOutside m0.dmem st.data.dmem
        (NativeRustcVm.InRange (stackBelow m0 leanvmVerifyStack) leanvmVerifyStack) ∧
      Saved m0 st.data)
      ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.LeanvmVerify.b0Offset)⟩ := by
  have hce : NativeVm.Entry.ctxWords = 12 := rfl
  have hc : (ctxOf m0).toNat = (reg m0 .rdi).toNat := rfl
  have hS : leanvmVerifyStack = 18816 := rfl
  have hR : (rspOf m0).toNat = lsb m0 + 18816 := by
    have hs := hst.1
    rw [hS] at hs
    rw [lsb, stackBelow_toNat hs]
    omega
  have h8 : lsb m0 + 18824 ≤ 2 ^ 64 := by have := hst.2.1; omega
  have hBn : (stackBelow m0 112).toNat = lsb m0 + 18704 := by
    rw [stackBelow_toNat (by omega)]
    omega
  have gcN : (ctxOf m0).toNat + 8 * NativeVm.Entry.ctxWords ≤ 2 ^ 64 := hin.fitCtx
  have gc : (ctxOf m0).toNat + 8 * NativeVm.Entry.ctxWords ≤ lsb m0 ∨
      lsb m0 + 18824 ≤ (ctxOf m0).toNat := by
    unfold NativeRustcVm.Apart at hctx
    rw [hS, lsb_eq] at hctx
    simpa only [UInt64.toNat_toBitVec, hce] using hctx
  have finish : ∀ {st : MachineState},
      st.pc = Labels.label NativeRustcVmX64.Vm.LeanvmVerify.label_17 →
      Frame m0 112 slots 8 st.data →
      NativeRustcVm.SameOutside m0.dmem st.data.dmem
        (NativeRustcVm.InRange (stackBelow m0 112) 112) →
      Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
        rspOf st'.data = rspOf m0 + 8#64 ∧ reg st'.data .rax = 0#64 ∧
        NativeRustcVm.SameOutside m0.dmem st'.data.dmem
          (NativeRustcVm.InRange (stackBelow m0 leanvmVerifyStack) leanvmVerifyStack) ∧
        Saved m0 st'.data) st := by
    intro st hpc hf hs
    refine Eventually.mono (exit12 hp hst (hpc.trans (lbl_17 hp)) hf)
      fun s ⟨hpc, hrsp, hrax, hmem, hsaved⟩ ↦ ⟨hpc, hrsp, hrax, ?_, hsaved⟩
    rw [hmem]
    intro q hq
    apply hs q
    intro hq'
    apply hq
    rw [inR (frame_noWrap (F := 112) hst (by decide) |>.mono (by decide)), hBn] at hq'
    rw [hS, inR (by unfold NativeRustcVm.NoWrap; rw [lsb_eq]; omega), lsb_eq]
    omega
  have finishZero : ∀ {st : MachineState},
      st.pc = Labels.label NativeRustcVmX64.Vm.LeanvmVerify.label_18 →
      Frame m0 112 slots 8 st.data →
      NativeRustcVm.SameOutside m0.dmem st.data.dmem
        (NativeRustcVm.InRange (stackBelow m0 112) 112) →
      reg st.data .rax = 0#64 →
      Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
        rspOf st'.data = rspOf m0 + 8#64 ∧ reg st'.data .rax = 0#64 ∧
        NativeRustcVm.SameOutside m0.dmem st'.data.dmem
          (NativeRustcVm.InRange (stackBelow m0 leanvmVerifyStack) leanvmVerifyStack) ∧
        Saved m0 st'.data) st := by
    intro st hpc hf hs hz
    refine Eventually.mono (exit13 hp hst (hpc.trans (lbl_18 hp)) hf)
      fun s ⟨hpc, hrsp, hrax, hmem, hsaved⟩ ↦ ⟨hpc, hrsp, hrax.trans hz, ?_, hsaved⟩
    rw [hmem]
    intro q hq
    apply hs q
    intro hq'
    apply hq
    rw [inR (frame_noWrap (F := 112) hst (by decide) |>.mono (by decide)), hBn] at hq'
    rw [hS, inR (by unfold NativeRustcVm.NoWrap; rw [lsb_eq]; omega), lsb_eq]
    omega
  have hfnw := frame_noWrap (F := 112) hst (by decide)
  have hFm : ∀ d : MachineData, Kept m0.dmem d.dmem →
      NativeRustcVm.Mapped d.dmem (stackBelow m0 112) (112 + 8) :=
    fun d hk ↦ Mapped.keeps (frame_mapped hst (by decide)) hk
  have hcM : NativeRustcVm.Mapped m0.dmem (reg m0 .rdi) 96 :=
    NativeRustcVm.Mapped.mono (NativeRustcVm.mapped_of_wordView hin.ctxSome) (by omega)
  have hcN : NativeRustcVm.NoWrap (reg m0 .rdi) 96 := by
    unfold NativeRustcVm.NoWrap; omega
  have hap : ((stackBelow m0 112, 112 + 8) :: [(reg m0 .rdi, 96)]).Pairwise
      fun x y ↦ NativeRustcVm.Apart x.1 x.2 y.1 y.2 :=
    List.pairwise_pair.mpr (by unfold NativeRustcVm.Apart; dsimp only; rw [hBn]; omega)
  -- the context's words, kept where only the frame changed
  have ldk : ∀ (d : MachineData) (ret : BitVec 64),
      NativeRustcVm.SameOutside m0.dmem d.dmem (NativeRustcVm.InRange (stackBelow m0 112) 112) →
      ∀ {i : Nat} {v : UInt64}, i < 12 → NativeRustcVm.wordView m0.dmem (wd (ctxOf m0) i) = some v →
      (frameEnv m0 d 112 [(reg m0 .rdi, 96)] (fun _ ↦ 0) ret).load 1 (8 * i) 8 = v.toBitVec := by
    intro d ret hs i v hi h
    refine load_ofMachine (r := 1) (b := reg m0 .rdi) (n := 96) rfl ?_
    refine keep_off (ctxWord h) hs fun j h1 h2 hq ↦ ?_
    rw [NativeRustcVm.length_wordBytes] at h2
    rw [inR (by unfold NativeRustcVm.NoWrap; omega), hBn, toNat_off (by omega)] at hq
    omega
  -- `b0`: the prologue, `L`.
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 112) (rest := [(reg m0 .rdi, 96)])
    (vars := fun _ ↦ 0) (ret := 0) ⟨frame_mapped hst (by decide), hfnw⟩
    (fun x hx ↦ by rw [List.mem_singleton] at hx; subst hx; exact ⟨hcM, hcN⟩) hap
  have hs0 : NativeRustcVm.SameOutside m0.dmem m0.dmem
      (NativeRustcVm.InRange (stackBelow m0 112) 112) := fun _ _ ↦ rfl
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 nofun
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, known_ptr rfl rfl, trivial⟩ trivial trivial
      trivial) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hw1, hrbx1, hrdi1⟩ := after_eq run_b0 ▸ ok_b0
  have hz1 : reg st1.data .rax = 0#64 := hm1.regs .rax (.lit 0) (after_eq run_b0 ▸ zero_b0)
  have hf1 : Frame m0 112 slots 8 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le slots_cs
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 112) 112) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hw1
  have hL1 := ldk m0 0 hs0 (i := 1) (by decide) hin.wireLen
  by_cases hL : bytes.length < 2 ^ 32
  swap
  · simp only [PcOk] at hpc1
    rw [reject_b0 _ hL1 hL hin.L64] at hpc1
    simp only [↓reduceIte] at hpc1
    exact finishZero hpc1 hf1 hs1 hz1
  simp only [PcOk] at hpc1
  rw [cond_b0 _ hL1 hL] at hpc1
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
  have eRbx1 : reg st1.data .rbx = BitVec.ofNat 64 bytes.length :=
    (hm1.regs .rbx _ hrbx1).trans hL1
  have eRdi1 : reg st1.data .rdi = reg m0 .rdi := (hm1.regs .rdi _ hrdi1).trans (eval_ptr rfl)
  -- `b1` to `b6`: no write, the context's values.
  have envOk : ∀ d : MachineData, Frame m0 112 slots 8 d →
      NativeRustcVm.SameOutside m0.dmem d.dmem (NativeRustcVm.InRange (stackBelow m0 112) 112) →
      reg d .rdi = reg m0 .rdi →
      (frameEnv m0 d 112 [(reg m0 .rdi, 96)] (fun _ ↦ 0) 0).WF ∧
        Match (frameEnv m0 d 112 [(reg m0 .rdi, 96)] (fun _ ↦ 0) 0) ctxS d := by
    intro d hf hs hrdi
    refine ⟨frame_wf ⟨hFm _ hf.kept, hfnw⟩ (fun x hx ↦ by
      rw [List.mem_singleton] at hx; subst hx; exact ⟨Mapped.keeps hcM hf.kept, hcN⟩) hap,
      match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.rsp_eval, known_ptr rfl hrdi, trivial⟩ trivial
        trivial trivial⟩
  -- `b1`: `n`.
  obtain ⟨hwf1, hm1'⟩ := envOk _ hf1 hs1 eRdi1
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf1 nofun
    (hpc1.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b0Offset + b0.length = k + NativeRustcVmX64.Vm.LeanvmVerify.b1Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b0_next]])) hm1' fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid2, hmem2, hr142, hrbx2, hrdi2⟩ := after_eq run_b1 ▸ ok_b1
  have hn1 := ldk st1.data 0 hs1 (i := 3) (by decide) hin.bcLen
  have hf2 : Frame m0 112 slots 8 st2.data := Frame.of_block hf1 hwf1 hm2 hmid2 slots_le
  have hs2 : NativeRustcVm.SameOutside m0.dmem st2.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 112) 112) := by
    rw [hm2.dmem_eq hwf1 hmem2]; exact hs1
  have hz2 : reg st2.data .rax = 0#64 :=
    (hm2.regs .rax (.reg .rax) (after_eq run_b1 ▸ zero_b1)).trans hz1
  by_cases hn : bytecode.length ≤ 536870910
  swap
  · simp only [PcOk] at hpc2
    rw [reject_b1 _ hn1 hn hin.bc64] at hpc2
    simp only [↓reduceIte] at hpc2
    exact finishZero hpc2 hf2 hs2 hz2
  simp only [PcOk] at hpc2
  rw [cond_b1 _ hn1 hn] at hpc2
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc2
  have eR142 : reg st2.data .r14 = BitVec.ofNat 64 bytecode.length := (hm2.regs .r14 _ hr142).trans hn1
  have eRbx2 : reg st2.data .rbx = BitVec.ofNat 64 bytes.length := (hm2.regs .rbx _ hrbx2).trans eRbx1
  have eRdi2 : reg st2.data .rdi = reg m0 .rdi := (hm2.regs .rdi _ hrdi2).trans (eval_ptr rfl)
  -- `b2`: the decoded area's count.
  obtain ⟨hwf2, hm2'⟩ := envOk _ hf2 hs2 eRdi2
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf2 nofun
    (hpc2.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b1Offset + b1.length = k + NativeRustcVmX64.Vm.LeanvmVerify.b2Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b1_next]])) hm2' fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hmem3, hr153, hrbx3, hr143, hrdi3⟩ := after_eq run_b2 ▸ ok_b2
  have h72 := ldk st2.data 0 hs2 (i := 9) (by decide) hin.decCount
  have hf3 : Frame m0 112 slots 8 st3.data := Frame.of_block hf2 hwf2 hm3 hmid3 slots_le
  have hs3 : NativeRustcVm.SameOutside m0.dmem st3.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 112) 112) := by
    rw [hm3.dmem_eq hwf2 hmem3]; exact hs2
  have hz3 : reg st3.data .rax = 0#64 :=
    (hm3.regs .rax (.reg .rax) (after_eq run_b2 ▸ zero_b2)).trans hz2
  by_cases hv9 : decodedWords bytes.length ≤ a.decCount.toNat
  swap
  · simp only [PcOk] at hpc3
    rw [reject_b2 _ h72 eRbx2 hL hv9] at hpc3
    simp only [↓reduceIte] at hpc3
    exact finishZero hpc3 hf3 hs3 hz3
  simp only [PcOk] at hpc3
  rw [cond_b2 _ h72 eRbx2 hL hv9] at hpc3
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc3
  have eR153 : reg st3.data .r15 = BitVec.ofNat 64 (decodedWords bytes.length) := by
    rw [show reg st3.data .r15 = _ from hm3.regs .r15 _ hr153]
    apply BitVec.eq_of_toNat_eq
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [show st2.data.regs.get64 .rbx = _ from eRbx2,
      dw_toNat (x := BitVec.ofNat 64 bytes.length) (by rw [BitVec.toNat_ofNat]; omega) hL,
      BitVec.toNat_ofNat]
    have : decodedWords bytes.length < 2 ^ 64 := by
      have := a.decCount.toNat_lt
      omega
    omega
  have eRbx3 : reg st3.data .rbx = BitVec.ofNat 64 bytes.length := (hm3.regs .rbx _ hrbx3).trans eRbx2
  have eR143 : reg st3.data .r14 = BitVec.ofNat 64 bytecode.length := (hm3.regs .r14 _ hr143).trans eR142
  have eRdi3 : reg st3.data .rdi = reg m0 .rdi := (hm3.regs .rdi _ hrdi3).trans (eval_ptr rfl)
  -- `b3`: the working area's count.
  obtain ⟨hwf3, hm3'⟩ := envOk _ hf3 hs3 eRdi3
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf3 nofun
    (hpc3.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b2Offset + b2.length = k + NativeRustcVmX64.Vm.LeanvmVerify.b3Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b2_next]])) hm3' fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid4, hmem4, hrbx4, hr144, hr154, hrdi4⟩ := after_eq run_b3 ▸ ok_b3
  have h88 := ldk st3.data 0 hs3 (i := 11) (by decide) hin.workCount
  have hf4 : Frame m0 112 slots 8 st4.data := Frame.of_block hf3 hwf3 hm4 hmid4 slots_le
  have hs4 : NativeRustcVm.SameOutside m0.dmem st4.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 112) 112) := by
    rw [hm4.dmem_eq hwf3 hmem4]; exact hs3
  have hz4 : reg st4.data .rax = 0#64 :=
    (hm4.regs .rax (.reg .rax) (after_eq run_b3 ▸ zero_b3)).trans hz3
  by_cases hww : 61944 ≤ a.workCount.toNat
  swap
  · simp only [PcOk] at hpc4
    rw [reject_b3 _ h88 hww] at hpc4
    simp only [↓reduceIte] at hpc4
    exact finishZero hpc4 hf4 hs4 hz4
  simp only [PcOk] at hpc4
  rw [cond_b3 _ h88 hww] at hpc4
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc4
  have eRbx4 := (hm4.regs .rbx _ hrbx4).trans eRbx3
  have eR144 := (hm4.regs .r14 _ hr144).trans eR143
  have eR154 := (hm4.regs .r15 _ hr154).trans eR153
  have eRdi4 : reg st4.data .rdi = reg m0 .rdi := (hm4.regs .rdi _ hrdi4).trans (eval_ptr rfl)
  -- `b4`: the decoded area.
  obtain ⟨hwf4, hm4'⟩ := envOk _ hf4 hs4 eRdi4
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf4 nofun
    (hpc4.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b3Offset + b3.length = k + NativeRustcVmX64.Vm.LeanvmVerify.b4Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b3_next]])) hm4' fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hmid5, hmem5, hr125, hrbx5, hr145, hr155, hrdi5⟩ := after_eq run_b4 ▸ ok_b4
  have h64 := ldk st4.data 0 hs4 (i := 8) (by decide) hin.decPtr
  have hf5 : Frame m0 112 slots 8 st5.data := Frame.of_block hf4 hwf4 hm5 hmid5 slots_le
  have hs5 : NativeRustcVm.SameOutside m0.dmem st5.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 112) 112) := by
    rw [hm5.dmem_eq hwf4 hmem5]; exact hs4
  by_cases hdec : a.decoded ≠ 0 ∧ a.decoded.toNat % 8 = 0
  swap
  · simp only [PcOk] at hpc5
    rw [reject_area _ h64 (fun h ↦ hdec
      ⟨fun hz ↦ h.1 (congrArg UInt64.toBitVec hz), h.2⟩)] at hpc5
    simp only [↓reduceIte] at hpc5
    exact finish hpc5 hf5 hs5
  simp only [PcOk] at hpc5
  rw [cond_area _ h64 (fun h ↦ hdec.1 (UInt64.toBitVec_inj.mp h)) hdec.2] at hpc5
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc5
  have eR125 : reg st5.data .r12 = a.decoded.toBitVec := (hm5.regs .r12 _ hr125).trans h64
  have eRbx5 := (hm5.regs .rbx _ hrbx5).trans eRbx4
  have eR145 := (hm5.regs .r14 _ hr145).trans eR144
  have eR155 := (hm5.regs .r15 _ hr155).trans eR154
  have eRdi5 : reg st5.data .rdi = reg m0 .rdi := (hm5.regs .rdi _ hrdi5).trans (eval_ptr rfl)
  -- `b5`: the working area.
  obtain ⟨hwf5, hm5'⟩ := envOk _ hf5 hs5 eRdi5
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf5 nofun
    (hpc5.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b4Offset + b4.length = k + NativeRustcVmX64.Vm.LeanvmVerify.b5Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b4_next]])) hm5' fun st6 hm6 hpc6 ↦ ?_
  obtain ⟨hmid6, hmem6, hr136, hr126, hrbx6, hr146, hr156, hrdi6⟩ := after_eq run_b5 ▸ ok_b5
  have h80 := ldk st5.data 0 hs5 (i := 10) (by decide) hin.workPtr
  have hf6 : Frame m0 112 slots 8 st6.data := Frame.of_block hf5 hwf5 hm6 hmid6 slots_le
  have hs6 : NativeRustcVm.SameOutside m0.dmem st6.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 112) 112) := by
    rw [hm6.dmem_eq hwf5 hmem6]; exact hs5
  by_cases hwork : a.work ≠ 0 ∧ a.work.toNat % 8 = 0
  swap
  · simp only [PcOk] at hpc6
    rw [reject_area _ h80 (fun h ↦ hwork
      ⟨fun hz ↦ h.1 (congrArg UInt64.toBitVec hz), h.2⟩)] at hpc6
    simp only [↓reduceIte] at hpc6
    exact finish hpc6 hf6 hs6
  simp only [PcOk] at hpc6
  rw [cond_area _ h80 (fun h ↦ hwork.1 (UInt64.toBitVec_inj.mp h)) hwork.2] at hpc6
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc6
  have eR136 : reg st6.data .r13 = a.work.toBitVec := (hm6.regs .r13 _ hr136).trans h80
  have eR126 := (hm6.regs .r12 _ hr126).trans eR125
  have eRbx6 := (hm6.regs .rbx _ hrbx6).trans eRbx5
  have eR146 := (hm6.regs .r14 _ hr146).trans eR145
  have eR156 := (hm6.regs .r15 _ hr156).trans eR155
  have eRdi6 : reg st6.data .rdi = reg m0 .rdi := (hm6.regs .rdi _ hrdi6).trans (eval_ptr rfl)
  -- `b6`: the wire's and the bytecode's addresses, the public input.
  obtain ⟨hwf6, hm6'⟩ := envOk _ hf6 hs6 eRdi6
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf6 nofun
    (hpc6.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b5Offset + b5.length = k + NativeRustcVmX64.Vm.LeanvmVerify.b6Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b5_next]])) hm6' fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨hmid7, hmem7, hrax7, hrbp7, hr87, hrsi7, hrdx7, hrcx7, hr127, hr137, hrbx7, hr147,
    hr157⟩ := after_eq run_b6 ▸ ok_b6
  have hf7 : Frame m0 112 slots 8 st7.data := Frame.of_block hf6 hwf6 hm7 hmid7 slots_le
  have hs7 : NativeRustcVm.SameOutside m0.dmem st7.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 112) 112) := by
    rw [hm7.dmem_eq hwf6 hmem7]; exact hs6
  have hC : C1 a bytes bytecode pub m0 st7.data :=
    ⟨hf7, hs7, (hm7.regs .rax _ hrax7).trans (ldk st6.data 0 hs6 (i := 0) (by decide) hin.wirePtr),
      (hm7.regs .rbx _ hrbx7).trans eRbx6,
      (hm7.regs .rbp _ hrbp7).trans (ldk st6.data 0 hs6 (i := 2) (by decide) hin.bcPtr),
      (hm7.regs .r8 _ hr87).trans (ldk st6.data 0 hs6 (i := 4) (by decide) (hin.pubWords 0 (by decide))),
      (hm7.regs .rsi _ hrsi7).trans (ldk st6.data 0 hs6 (i := 5) (by decide) (hin.pubWords 1 (by decide))),
      (hm7.regs .rdx _ hrdx7).trans (ldk st6.data 0 hs6 (i := 6) (by decide) (hin.pubWords 2 (by decide))),
      (hm7.regs .rcx _ hrcx7).trans (ldk st6.data 0 hs6 (i := 7) (by decide) (hin.pubWords 3 (by decide))),
      (hm7.regs .r12 _ hr127).trans eR126, (hm7.regs .r13 _ hr137).trans eR136,
      (hm7.regs .r14 _ hr147).trans eR146, (hm7.regs .r15 _ hr157).trans eR156⟩
  have next : ∀ (st : MachineState),
      st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LeanvmVerify.b8Offset) →
      C1 a bytes bytecode pub m0 st.data →
      (0 < bytecode.length → a.bytecode ≠ 0 ∧ a.bytecode.toNat % 8 = 0) →
      Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
        rspOf st'.data = rspOf m0 + 8#64 ∧ reg st'.data .rax = 0#64 ∧
        NativeRustcVm.SameOutside m0.dmem st'.data.dmem
          (NativeRustcVm.InRange (stackBelow m0 leanvmVerifyStack) leanvmVerifyStack) ∧
        Saved m0 st'.data) st := by
    intro st hpc hC hbc
    have hwbad : ¬ (0 < bytes.length → a.wire ≠ 0) := by
      intro hw
      exact hbad ⟨⟨hL, by omega, hv9, hww⟩, ⟨hdec, hwork, hbc, hw⟩⟩
    have hLpos : 0 < bytes.length := by
      by_contra hh
      exact hwbad (fun h ↦ False.elim (hh h))
    have hwzero : a.wire = 0 := by
      by_contra hh
      exact hwbad (fun _ ↦ hh)
    have envBody : ∀ (d : MachineData), Frame m0 112 slots 8 d →
        (frameEnv m0 d 112 [] (fun _ ↦ 0) 0).WF ∧
        Match (frameEnv m0 d 112 [] (fun _ ↦ 0) 0) bodyS d := by
      intro d hf
      exact ⟨frame_wf ⟨hFm _ hf.kept, hfnw⟩ (by simp) (List.pairwise_singleton _ _),
        match_ofMachine ⟨rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial trivial⟩
    obtain ⟨hwf8, hm8⟩ := envBody _ hC.frame
    refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8 hwf8 nofun hpc hm8
      fun st9 hm9 hpc9 ↦ ?_
    obtain ⟨hmid9, hmem9, hk9⟩ := after_eq run_b8 ▸ ok_b8
    have hC9 := C1.block hC hwf8 hm9 hmid9 hmem9 hk9
    simp only [PcOk] at hpc9
    rw [cond_zero _ hC.rbx] at hpc9
    have hne : (BitVec.ofNat 64 bytes.length == 0) = false := by
      rw [show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl,
        ofNat_beq (X := bytes.length) (k := 0) hin.L64 (by decide)]
      simpa using (show bytes.length ≠ 0 by omega)
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at hpc9
    obtain ⟨hwf9, hm9'⟩ := envBody _ hC9.frame
    refine exec_at (infix_of b9_in_code (by simp [b9]) hp) run_b9 hwf9 nofun
      (hpc9.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b8Offset + b8.length =
        k + NativeRustcVmX64.Vm.LeanvmVerify.b9Offset from by
          rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b8_next]])) hm9'
      fun st10 hm10 hpc10 ↦ ?_
    obtain ⟨hmid10, hmem10, hk10⟩ := after_eq run_b9 ▸ ok_b9
    have hC10 := C1.block hC9 hwf9 hm10 hmid10 hmem10 hk10
    simp only [PcOk] at hpc10
    rw [cond_zero _ hC9.rax, hwzero] at hpc10
    simp only [UInt64.toBitVec_zero] at hpc10
    exact finish hpc10 hC10.frame hC10.same
  simp only [PcOk] at hpc7
  rw [cond_zero _ eR146] at hpc7
  rcases Nat.eq_zero_or_pos bytecode.length with hn0 | hn0
  · rw [hn0] at hpc7
    simp only [show (BitVec.ofNat 64 0 == 0) = true from rfl, ↓reduceIte] at hpc7
    exact next st7 (hpc7.trans (lbl_8 hp)) hC (fun h ↦ by omega)
  · have hne : (BitVec.ofNat 64 bytecode.length == 0) = false := by
      rw [show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl,
        ofNat_beq (X := bytecode.length) (k := 0) hin.bc64 (by decide)]
      simpa using (show bytecode.length ≠ 0 by omega)
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at hpc7
    have hwf7 := frame_wf (m0 := m0) (d := st7.data) (F := 112) (rest := []) (vars := fun _ ↦ 0)
      (ret := 0) ⟨hFm _ hf7.kept, hfnw⟩ (by simp) (List.pairwise_singleton _ _)
    refine exec_at (infix_of b7_in_code (by simp [b7]) hp) run_b7 hwf7 nofun
      (hpc7.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b6Offset + b6.length =
        k + NativeRustcVmX64.Vm.LeanvmVerify.b7Offset from by
          rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b6_next]]))
      (match_ofMachine ⟨rfl, trivial⟩ ⟨hf7.rsp_eval, trivial⟩ trivial trivial trivial)
      fun st8 hm8 hpc8 ↦ ?_
    obtain ⟨hmid8, hmem8, hk8⟩ := after_eq run_b7 ▸ ok_b7
    have hC8 := C1.block hC hwf7 hm8 hmid8 hmem8 hk8
    simp only [PcOk] at hpc8
    by_cases hb : a.bytecode ≠ 0 ∧ a.bytecode.toNat % 8 = 0
    · rw [cond_b7 _ hC.rbp (fun h ↦ hb.1 (UInt64.toBitVec_inj.mp h)) hb.2] at hpc8
      simp only [Bool.false_eq_true, ↓reduceIte] at hpc8
      exact next st8
        (hpc8.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b7Offset + b7.length =
          k + NativeRustcVmX64.Vm.LeanvmVerify.b8Offset from by
            rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b7_next]])) hC8 (fun _ ↦ hb)
    · rw [reject_b7 _ hC.rbp (fun h ↦ hb
        ⟨fun hz ↦ h.1 (congrArg UInt64.toBitVec hz), h.2⟩)] at hpc8
      simp only [↓reduceIte] at hpc8
      exact finish hpc8 hC8.frame hC8.same

#print axioms reject

end

end NativeRustcVmX64.Top.Leanvm
