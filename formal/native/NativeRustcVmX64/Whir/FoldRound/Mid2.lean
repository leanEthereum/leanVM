module

public import NativeRustcVmX64.Whir.FoldRound.Mid1
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `fold_round` on x86-64: the last products

`s5_mul` (`b14`, `EW::mul`: `p3`), `s6_mul` (`b15`, `EW::mul`: `p4`), `s7_mul` (`b16`, `EW::mul`: `α β`),
`s8_mul` (`b17`, `EW::mul`: `p6`): on to `b18` with the products in the frame and the registers.
-/

namespace NativeRustcVmX64.Whir.FoldRound

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.FoldRound
open NativeRustcVmX64.Transcript (Frame frameEnv MidOk)
open NativeRustcVmX64.Whir.SampleQueries (wr0 miss wrote kept wrote_spec kept_spec wr0_spec
  miss_spec midOk_writesIn miss_of_wr0)
open NativeRustcVm (WordAt EWAt EWsAt)

public section

variable [Host] {k : Nat} {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData}
  {x1 x2 x3 x4 : EW} {s5 : TState}

/-- **`b14`, `EW::mul`**: `p3` in RAX, RDX. -/
theorem s5_mul (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b14Offset))
    (hP : Pt a s0 w m0 x1 x2 x3 x4 s5 (sq (sq s5).2).2
      [(96, (p1 w s5 x1).c0), (104, (p1 w s5 x1).c1), (48, (beA s5).c0), (40, (beA s5).c1),
        (56, (alA s5).c0), (32, (alA s5).c1), (64, x2.c1), (72, x3.c0), (80, x3.c1),
        (120, x4.c0), (112, x4.c1)] st.data)
    (h15 : reg st.data .r15 = x2.c0.toBitVec)
    (hax : reg st.data .rax = (aa s5).c0.toBitVec) (hdx : reg st.data .rdx = (aa s5).c1.toBitVec)
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b15Offset) →
      Pt a s0 w m0 x1 x2 x3 x4 s5 (sq (sq s5).2).2
        [(96, (p1 w s5 x1).c0), (104, (p1 w s5 x1).c1), (48, (beA s5).c0), (40, (beA s5).c1),
          (56, (alA s5).c0), (32, (alA s5).c1), (64, x2.c1), (72, x3.c0), (80, x3.c1),
          (120, x4.c0), (112, x4.c1)] st'.data →
      reg st'.data .rax = (p3 s5 x2).c0.toBitVec → reg st'.data .rdx = (p3 s5 x2).c1.toBitVec →
      Eventually (step1 Host.exe) (Goal a s0 w m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 w m0) st := by
  have cx := ctx h
  obtain ⟨hmid, hw0, hdi, hsi, hdx1, hcx1, hk⟩ := after_eq run_b14 ▸ ok_b14
  have hwf := cx.wf0 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b14Offset + b14.length)).toBitVec)
    hP.bd.fr.fr.kept
  refine mulCall hp h hmul hpc hP.bd b14_in_code (by simp [b14]) hwf hP.bd.fr.mid run_b14 hmid
    (wr0_le hw0 (by omega)) (fun st1 hm1 ↦ ⟨hm1.regs .rbx _ (kept_spec hk (by simp [cs])),
      hm1.regs .r14 _ (kept_spec hk (by simp [cs]))⟩)
    fun st1 st' hm1 hpc' hbd hax' hdx' hcs hkeep ↦ ?_
  have kr : ∀ r ∈ cs, reg st1 r = reg st.data r := fun r hr ↦ hm1.regs r _ (kept_spec hk hr)
  have hfw := FW.block hwf hm1 (midOk_writesIn hmid) (miss_of_wr8 hw0 (by simp)) (by simp) hP.fw
  have ea : (⟨.ofBitVec (reg st1 .rdi), .ofBitVec (reg st1 .rsi)⟩ : EW) = aa s5 :=
    ew_of _ ((hm1.regs .rdi _ hdi).trans hax) ((hm1.regs .rsi _ hsi).trans hdx)
  have eb : (⟨.ofBitVec (reg st1 .rdx), .ofBitVec (reg st1 .rcx)⟩ : EW) = x2 :=
    ew_of _ ((hm1.regs .rdx _ hdx1).trans h15) ((hm1.regs .rcx _ hcx1).trans
      (loc_load (hP.fw.get (o := 64) (v := x2.c1) (by simp))))
  rw [ea, eb] at hax' hdx'
  exact cont st' hpc' ⟨hbd, FW.call hkeep (by simp) hfw,
    (hcs .r12 rfl).trans ((kr .r12 (by simp [cs])).trans hP.r12),
    (hcs .rbp rfl).trans ((kr .rbp (by simp [cs])).trans hP.rbp), hP.model⟩ hax' hdx'

/-- **`b15`, `EW::mul`**: `p3` to the frame's words `88`, `64`; `p4` in RAX, RDX. -/
theorem s6_mul (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b15Offset))
    (hP : Pt a s0 w m0 x1 x2 x3 x4 s5 (sq (sq s5).2).2
      [(96, (p1 w s5 x1).c0), (104, (p1 w s5 x1).c1), (48, (beA s5).c0), (40, (beA s5).c1),
        (56, (alA s5).c0), (32, (alA s5).c1), (64, x2.c1), (72, x3.c0), (80, x3.c1),
        (120, x4.c0), (112, x4.c1)] st.data)
    (hax : reg st.data .rax = (p3 s5 x2).c0.toBitVec)
    (hdx : reg st.data .rdx = (p3 s5 x2).c1.toBitVec)
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b16Offset) →
      Pt a s0 w m0 x1 x2 x3 x4 s5 (sq (sq s5).2).2
        [(88, (p3 s5 x2).c0), (64, (p3 s5 x2).c1), (96, (p1 w s5 x1).c0),
          (104, (p1 w s5 x1).c1), (48, (beA s5).c0), (40, (beA s5).c1), (56, (alA s5).c0),
          (32, (alA s5).c1), (72, x3.c0), (80, x3.c1), (120, x4.c0), (112, x4.c1)] st'.data →
      reg st'.data .rax = (p4 s5 x3).c0.toBitVec → reg st'.data .rdx = (p4 s5 x3).c1.toBitVec →
      Eventually (step1 Host.exe) (Goal a s0 w m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 w m0) st := by
  have cx := ctx h
  obtain ⟨hmid, hw0, hw88, hw64, hmiss, hdi, hsi, hdx1, hcx1, hk⟩ := after_eq run_b15 ▸ ok_b15
  have hwf := cx.wf0 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b15Offset + b15.length)).toBitVec)
    hP.bd.fr.fr.kept
  refine mulCall hp h hmul hpc hP.bd b15_in_code (by simp [b15]) hwf hP.bd.fr.mid run_b15 hmid
    (wr0_le hw0 (by omega)) (fun st1 hm1 ↦ ⟨hm1.regs .rbx _ (kept_spec hk (by simp [cs])),
      hm1.regs .r14 _ (kept_spec hk (by simp [cs]))⟩)
    fun st1 st' hm1 hpc' hbd hax' hdx' hcs hkeep ↦ ?_
  have kr : ∀ r ∈ cs, reg st1 r = reg st.data r := fun r hr ↦ hm1.regs r _ (kept_spec hk hr)
  have e88 : WordAt st1.dmem (off (fb m0) 88) (p3 s5 x2).c0 := by
    have := loc_write hm1 (o := 88) (by omega) hw88
    rwa [show (Sym.reg .rax).eval (frameEnv m0 st.data 176 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b15Offset + b15.length)).toBitVec) = (p3 s5 x2).c0.toBitVec from hax,
      UInt64.ofBitVec_toBitVec] at this
  have e64 : WordAt st1.dmem (off (fb m0) 64) (p3 s5 x2).c1 := by
    have := loc_write hm1 (o := 64) (by omega) hw64
    rwa [show (Sym.reg .rdx).eval (frameEnv m0 st.data 176 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b15Offset + b15.length)).toBitVec) = (p3 s5 x2).c1.toBitVec from hdx,
      UInt64.ofBitVec_toBitVec] at this
  have hfw1 := FW.block hwf hm1 (midOk_writesIn hmid) (miss_of_missL hmiss (by simp)) (by simp)
    (hP.fw.sub (L' := [(96, (p1 w s5 x1).c0), (104, (p1 w s5 x1).c1), (48, (beA s5).c0),
      (40, (beA s5).c1), (56, (alA s5).c0), (32, (alA s5).c1), (72, x3.c0), (80, x3.c1),
      (120, x4.c0), (112, x4.c1)]) (by simp))
  have hfw : FW st1.dmem m0 ([(88, (p3 s5 x2).c0), (64, (p3 s5 x2).c1)] ++
      [(96, (p1 w s5 x1).c0), (104, (p1 w s5 x1).c1), (48, (beA s5).c0), (40, (beA s5).c1),
        (56, (alA s5).c0), (32, (alA s5).c1), (72, x3.c0), (80, x3.c1), (120, x4.c0),
        (112, x4.c1)]) := by
    refine FW.append (fun p hp ↦ ?_) hfw1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    exacts [e88, e64]
  have ea : (⟨.ofBitVec (reg st1 .rdi), .ofBitVec (reg st1 .rsi)⟩ : EW) = beA s5 :=
    ew_of _ ((hm1.regs .rdi _ hdi).trans (loc_load (hP.fw.get (o := 48) (v := (beA s5).c0)
      (by simp)))) ((hm1.regs .rsi _ hsi).trans (loc_load (hP.fw.get (o := 40) (v := (beA s5).c1)
      (by simp))))
  have eb : (⟨.ofBitVec (reg st1 .rdx), .ofBitVec (reg st1 .rcx)⟩ : EW) = x3 :=
    ew_of _ ((hm1.regs .rdx _ hdx1).trans (loc_load (hP.fw.get (o := 72) (v := x3.c0)
      (by simp)))) ((hm1.regs .rcx _ hcx1).trans (loc_load (hP.fw.get (o := 80) (v := x3.c1)
      (by simp))))
  rw [ea, eb] at hax' hdx'
  exact cont st' hpc' ⟨hbd, FW.call hkeep (by simp) hfw,
    (hcs .r12 rfl).trans ((kr .r12 (by simp [cs])).trans hP.r12),
    (hcs .rbp rfl).trans ((kr .rbp (by simp [cs])).trans hP.rbp), hP.model⟩ hax' hdx'

/-- **`b16`, `EW::mul`**: `p4` in R15, R13; `α β` in RAX, RDX. -/
theorem s7_mul (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b16Offset))
    (hP : Pt a s0 w m0 x1 x2 x3 x4 s5 (sq (sq s5).2).2
      [(88, (p3 s5 x2).c0), (64, (p3 s5 x2).c1), (96, (p1 w s5 x1).c0),
        (104, (p1 w s5 x1).c1), (48, (beA s5).c0), (40, (beA s5).c1), (56, (alA s5).c0),
        (32, (alA s5).c1), (72, x3.c0), (80, x3.c1), (120, x4.c0), (112, x4.c1)] st.data)
    (hax : reg st.data .rax = (p4 s5 x3).c0.toBitVec)
    (hdx : reg st.data .rdx = (p4 s5 x3).c1.toBitVec)
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b17Offset) →
      Pt a s0 w m0 x1 x2 x3 x4 s5 (sq (sq s5).2).2
        [(88, (p3 s5 x2).c0), (64, (p3 s5 x2).c1), (96, (p1 w s5 x1).c0),
          (104, (p1 w s5 x1).c1), (48, (beA s5).c0), (40, (beA s5).c1), (56, (alA s5).c0),
          (32, (alA s5).c1), (72, x3.c0), (80, x3.c1), (120, x4.c0), (112, x4.c1)] st'.data →
      reg st'.data .r15 = (p4 s5 x3).c0.toBitVec → reg st'.data .r13 = (p4 s5 x3).c1.toBitVec →
      reg st'.data .rax = (ab s5).c0.toBitVec → reg st'.data .rdx = (ab s5).c1.toBitVec →
      Eventually (step1 Host.exe) (Goal a s0 w m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 w m0) st := by
  have cx := ctx h
  obtain ⟨hmid, hw0, h15, h13, hdi, hsi, hdx1, hcx1, hk⟩ := after_eq run_b16 ▸ ok_b16
  have hwf := cx.wf0 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b16Offset + b16.length)).toBitVec)
    hP.bd.fr.fr.kept
  refine mulCall hp h hmul hpc hP.bd b16_in_code (by simp [b16]) hwf hP.bd.fr.mid run_b16 hmid
    (wr0_le hw0 (by omega)) (fun st1 hm1 ↦ ⟨hm1.regs .rbx _ (kept_spec hk (by simp)),
      hm1.regs .r14 _ (kept_spec hk (by simp))⟩)
    fun st1 st' hm1 hpc' hbd hax' hdx' hcs hkeep ↦ ?_
  have hfw := FW.block hwf hm1 (midOk_writesIn hmid) (miss_of_wr8 hw0 (by simp)) (by simp) hP.fw
  have ea : (⟨.ofBitVec (reg st1 .rdi), .ofBitVec (reg st1 .rsi)⟩ : EW) = alA s5 :=
    ew_of _ ((hm1.regs .rdi _ hdi).trans (loc_load (hP.fw.get (o := 56) (v := (alA s5).c0)
      (by simp)))) ((hm1.regs .rsi _ hsi).trans (loc_load (hP.fw.get (o := 32) (v := (alA s5).c1)
      (by simp))))
  have eb : (⟨.ofBitVec (reg st1 .rdx), .ofBitVec (reg st1 .rcx)⟩ : EW) = beA s5 :=
    ew_of _ ((hm1.regs .rdx _ hdx1).trans (loc_load (hP.fw.get (o := 48) (v := (beA s5).c0)
      (by simp)))) ((hm1.regs .rcx _ hcx1).trans (loc_load (hP.fw.get (o := 40) (v := (beA s5).c1)
      (by simp))))
  rw [ea, eb] at hax' hdx'
  exact cont st' hpc' ⟨hbd, FW.call hkeep (by simp) hfw,
    (hcs .r12 rfl).trans ((hm1.regs .r12 _ (kept_spec hk (by simp))).trans hP.r12),
    (hcs .rbp rfl).trans ((hm1.regs .rbp _ (kept_spec hk (by simp))).trans hP.rbp), hP.model⟩
    ((hcs .r15 rfl).trans ((hm1.regs .r15 _ h15).trans hax))
    ((hcs .r13 rfl).trans ((hm1.regs .r13 _ h13).trans hdx)) hax' hdx'

/-- **`b17`, `EW::mul`**: `p6` in RAX, RDX; on to `b18`. -/
theorem s8_mul (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b17Offset))
    (hP : Pt a s0 w m0 x1 x2 x3 x4 s5 (sq (sq s5).2).2
      [(88, (p3 s5 x2).c0), (64, (p3 s5 x2).c1), (96, (p1 w s5 x1).c0),
        (104, (p1 w s5 x1).c1), (48, (beA s5).c0), (40, (beA s5).c1), (56, (alA s5).c0),
        (32, (alA s5).c1), (72, x3.c0), (80, x3.c1), (120, x4.c0), (112, x4.c1)] st.data)
    (h15 : reg st.data .r15 = (p4 s5 x3).c0.toBitVec)
    (h13 : reg st.data .r13 = (p4 s5 x3).c1.toBitVec)
    (hax : reg st.data .rax = (ab s5).c0.toBitVec) (hdx : reg st.data .rdx = (ab s5).c1.toBitVec)
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b18Offset) →
      Pt a s0 w m0 x1 x2 x3 x4 s5 (sq (sq s5).2).2
        [(88, (p3 s5 x2).c0), (64, (p3 s5 x2).c1), (96, (p1 w s5 x1).c0),
          (104, (p1 w s5 x1).c1), (48, (beA s5).c0), (40, (beA s5).c1), (56, (alA s5).c0),
          (32, (alA s5).c1)] st'.data →
      reg st'.data .r15 = (p4 s5 x3).c0.toBitVec → reg st'.data .r13 = (p4 s5 x3).c1.toBitVec →
      reg st'.data .rax = (p6 s5 x3 x4).c0.toBitVec →
      reg st'.data .rdx = (p6 s5 x3 x4).c1.toBitVec →
      Eventually (step1 Host.exe) (Goal a s0 w m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 w m0) st := by
  have cx := ctx h
  obtain ⟨hmid, hw0, hdi, hsi, hdx1, hcx1, hk⟩ := after_eq run_b17 ▸ ok_b17
  have hwf := cx.wf0 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b17Offset + b17.length)).toBitVec)
    hP.bd.fr.fr.kept
  refine mulCall hp h hmul hpc hP.bd b17_in_code (by simp [b17]) hwf hP.bd.fr.mid run_b17 hmid
    (wr0_le hw0 (by omega)) (fun st1 hm1 ↦ ⟨hm1.regs .rbx _ (kept_spec hk (by simp [cs])),
      hm1.regs .r14 _ (kept_spec hk (by simp [cs]))⟩)
    fun st1 st' hm1 hpc' hbd hax' hdx' hcs hkeep ↦ ?_
  have kr : ∀ r ∈ cs, reg st1 r = reg st.data r := fun r hr ↦ hm1.regs r _ (kept_spec hk hr)
  have hfw := FW.block hwf hm1 (midOk_writesIn hmid) (miss_of_wr8 hw0 (by simp)) (by simp)
    (hP.fw.sub (L' := [(88, (p3 s5 x2).c0), (64, (p3 s5 x2).c1), (96, (p1 w s5 x1).c0),
      (104, (p1 w s5 x1).c1), (48, (beA s5).c0), (40, (beA s5).c1), (56, (alA s5).c0),
      (32, (alA s5).c1)]) (by simp))
  have ea : (⟨.ofBitVec (reg st1 .rdi), .ofBitVec (reg st1 .rsi)⟩ : EW) = ab s5 :=
    ew_of _ ((hm1.regs .rdi _ hdi).trans hax) ((hm1.regs .rsi _ hsi).trans hdx)
  have eb : (⟨.ofBitVec (reg st1 .rdx), .ofBitVec (reg st1 .rcx)⟩ : EW) =
      ⟨x4.c0 ^^^ x3.c0, x4.c1 ^^^ x3.c1⟩ := by
    refine ew_of _ ((hm1.regs .rdx _ hdx1).trans ?_) ((hm1.regs .rcx _ hcx1).trans ?_)
    · rw [NativeRustcVmX64.Arrays.eval_xor]
      show (frameEnv m0 st.data 176 [] _ _).load 0 120 8 ^^^
        (frameEnv m0 st.data 176 [] _ _).load 0 72 8 = _
      rw [loc_load (hP.fw.get (o := 120) (v := x4.c0) (by simp)),
        loc_load (hP.fw.get (o := 72) (v := x3.c0) (by simp))]
      rfl
    · rw [NativeRustcVmX64.Arrays.eval_xor]
      show (frameEnv m0 st.data 176 [] _ _).load 0 112 8 ^^^
        (frameEnv m0 st.data 176 [] _ _).load 0 80 8 = _
      rw [loc_load (hP.fw.get (o := 112) (v := x4.c1) (by simp)),
        loc_load (hP.fw.get (o := 80) (v := x3.c1) (by simp))]
      rfl
  rw [ea, eb] at hax' hdx'
  exact cont st' hpc' ⟨hbd, FW.call hkeep (by simp) hfw,
    (hcs .r12 rfl).trans ((kr .r12 (by simp [cs])).trans hP.r12),
    (hcs .rbp rfl).trans ((kr .rbp (by simp [cs])).trans hP.rbp), hP.model⟩
    ((hcs .r15 rfl).trans ((kr .r15 (by simp [cs])).trans h15))
    ((hcs .r13 rfl).trans ((kr .r13 (by simp [cs])).trans h13)) hax' hdx'

end

end NativeRustcVmX64.Whir.FoldRound
