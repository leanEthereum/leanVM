module

public import NativeRustcVmX64.Whir.FoldRound.Check
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names

/-!
# `fold_round` on x86-64: the four reads and the grind

From the entry the prologue and four `read_scalar` calls (`read1` to `read4`, `b0` to `b7`), the
values kept in callee-saved registers and the frame; the grind (`grindStep`, `b8`, `b9`): on to
`b10` with the four scalars and the grind's state (`AtB10`), or the `None` exit. `reads`: the
whole.
-/

namespace NativeRustcVmX64.Whir.FoldRound

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.FoldRound
open NativeRustcVmX64.Transcript (Frame frameEnv MidOk)
open NativeRustcVmX64.Whir.SampleQueries (wr0 miss wrote kept wrote_spec kept_spec wr0_spec
  miss_spec midOk_writesIn)
open NativeRustcVm (WordAt EWAt EWsAt)

@[expose] public section

/-- **At `b10`**: the scalars `x1` to `x4` in R12, RBP, R15 and the frame, the grind's state
`s5`, the round's outcome. -/
structure AtB10 (a : DecArea) (s0 : TState) (w : WhirStateW) (m0 : MachineData) (x1 x2 x3 x4 : EW)
    (s5 : TState) (st : MachineData) : Prop where
  bd : Bd m0 a s5 st
  r13 : reg st .r13 = tA m0
  r12 : reg st .r12 = x1.c0.toBitVec
  rbp : reg st .rbp = x1.c1.toBitVec
  r15 : reg st .r15 = x2.c0.toBitVec
  w64 : WordAt st.dmem (off (fb m0) 64) x2.c1
  w72 : WordAt st.dmem (off (fb m0) 72) x3.c0
  w80 : WordAt st.dmem (off (fb m0) 80) x3.c1
  w120 : WordAt st.dmem (off (fb m0) 120) x4.c0
  w112 : WordAt st.dmem (off (fb m0) 112) x4.c1
  model : (foldRound w).run s0 = some ((foldW w x1 x2 x3 x4 (sq s5).1 (sq (sq s5).2).1,
    ⟨(sq s5).1, (sq (sq s5).2).1⟩), (sq (sq s5).2).2)

end

public section

/-- The low byte test `testb %al, %al; je`. -/
theorem al_zero (x : BitVec 64) :
    CmpOp.apply .eq .W8 (BinOp.apply .and .W8 x x) (BitVec.ofNat 64 0) =
      decide (x.toNat % 256 = 0) := by
  simp only [CmpOp.apply, BinOp.apply, low, ext, BitVec.and_self]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.toNat_eq]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Width.bits]
  omega

variable [Host] {k : Nat} {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData}

/-- **The first read** (`b0`, `b1`). -/
theorem read1 (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (cont : ∀ (x1 : EW) (s1 : TState) (st : MachineState), readScalar.run s0 = some (x1, s1) →
      st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b2Offset) → Bd m0 a s1 st.data →
      WordAt st.data.dmem (off (fb m0) 16) x1.c0 → WordAt st.data.dmem (off (fb m0) 24) x1.c1 →
      reg st.data .r13 = tA m0 → Eventually (step1 Host.exe) (Goal a s0 w m0) st) :
    Eventually (step1 Host.exe) (Goal a s0 w m0) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b0Offset)⟩ := by
  have cx := ctx h
  have hwf := cx.wf0 (d := m0) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b0Offset + b0.length)).toBitVec) (fun _ h ↦ h)
  have hm0 : Match (frameEnv m0 m0 176 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b0Offset + b0.length)).toBitVec)
      entryS m0 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨Transcript.match_rsp, trivial⟩ trivial trivial trivial
  refine exec_then (inf hp b0_in_code (by simp [b0])) run_b0 hwf (fun _ _ ↦ rfl) hm0
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hw0, hdi, hsi, h13, h14, hbx⟩ := after_eq run_b0 ▸ ok_b0
  have hf1 := Frame.of_prologue Frame.entry hwf hm1 hpro slots_le slots_cs
  have hs1 : SameOutside m0.dmem st1.data.dmem (InRange (fb m0) 176) :=
    Transcript.sameOutside_low hwf hm1 (r := 0) rfl (by omega) (wr0_spec hw0)
  have hat : AtCall m0 176 foldRoundStack slots (outs m0) (tA m0) a s0 st1.data :=
    ⟨hf1, fun q hq ↦ hs1 q fun h' ↦ hq (.inr (cx.frame_stack h')),
      cx.ts_frame (hm1.kept hwf) (by omega) hs1 h.2.1⟩
  refine readCheck hp h hrs hat (fun q hq ↦ hs1 q fun h' ↦ hq (.inl (cx.frame_stack h')))
    ((hm1.regs .rdi _ hdi).trans (Transcript.eval_ptr0 8)) (hm1.regs .rsi _ hsi)
    (hm1.regs .rbx _ hbx) (hm1.regs .r14 _ h14) (j := NativeRustcVmX64.Vm.FoldRound.b1Offset) hpc1 b1_in_code (by simp [b1]) run_b1
    (after_eq run_b1 ▸ ok_b1) c_b1 (fun hr ↦ by simp only [foldRound_run, hr, Option.bind_none])
    fun x s' st hr hpc hbd h16 h24 _ hcs ↦
      cont x s' st hr hpc hbd h16 h24 ((hcs .r13 rfl).trans (hm1.regs .r13 _ h13))

/-- **The second read** (`b2`, `b3`): the first scalar in R12, RBP. -/
theorem read2 (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    {x1 : EW} {s1 : TState} {st : MachineState} (h1 : readScalar.run s0 = some (x1, s1))
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b2Offset)) (hb : Bd m0 a s1 st.data)
    (w16 : WordAt st.data.dmem (off (fb m0) 16) x1.c0)
    (w24 : WordAt st.data.dmem (off (fb m0) 24) x1.c1) (h13 : reg st.data .r13 = tA m0)
    (cont : ∀ (x2 : EW) (s2 : TState) (st' : MachineState), readScalar.run s1 = some (x2, s2) →
      st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b4Offset) → Bd m0 a s2 st'.data →
      WordAt st'.data.dmem (off (fb m0) 16) x2.c0 → WordAt st'.data.dmem (off (fb m0) 24) x2.c1 →
      reg st'.data .r13 = tA m0 → reg st'.data .r12 = x1.c0.toBitVec →
      reg st'.data .rbp = x1.c1.toBitVec → Eventually (step1 Host.exe) (Goal a s0 w m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 w m0) st := by
  have cx := ctx h
  have hwf := cx.wf0 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b2Offset + b2.length)).toBitVec)
    hb.fr.fr.kept
  refine exec_at (inf hp b2_in_code (by simp [b2])) run_b2 hwf (fun _ _ ↦ rfl) hpc hb.fr.mid
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hw0, h12, hbp, hdi, hsi, hk⟩ := after_eq run_b2 ▸ ok_b2
  obtain ⟨hat, hs1⟩ := WFr.atCall cx hb.fr hb.ts hwf hm1 hmid slots_le (wr0_le hw0 (by omega))
  have e12 : reg st1.data .r12 = x1.c0.toBitVec := (hm1.regs .r12 _ h12).trans (loc_load w16)
  have ebp : reg st1.data .rbp = x1.c1.toBitVec := (hm1.regs .rbp _ hbp).trans (loc_load w24)
  have e13 : reg st1.data .r13 = tA m0 := (hm1.regs .r13 _ (kept_spec hk (by simp))).trans h13
  refine readCheck hp h hrs hat (mem_trans hb.mem hs1 fun q hq ↦ .inl (cx.frame_stack hq))
    ((hm1.regs .rdi _ hdi).trans (Transcript.eval_ptr0 8)) ((hm1.regs .rsi _ hsi).trans h13)
    ((hm1.regs .rbx _ (kept_spec hk (by simp))).trans hb.rbx)
    ((hm1.regs .r14 _ (kept_spec hk (by simp))).trans hb.r14) (j := NativeRustcVmX64.Vm.FoldRound.b3Offset) hpc1 b3_in_code
    (by simp [b3]) run_b3 (after_eq run_b3 ▸ ok_b3) c_b3
    (fun hr ↦ by simp only [foldRound_run, h1, hr, Option.bind_some, Option.bind_none])
    fun x s' st' hr hpc' hbd h16 h24 _ hcs ↦ cont x s' st' hr hpc' hbd h16 h24
      ((hcs .r13 rfl).trans e13) ((hcs .r12 rfl).trans e12) ((hcs .rbp rfl).trans ebp)

/-- **The third read** (`b4`, `b5`): the second scalar in R15 and the frame's word `64`. -/
theorem read3 (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    {x1 x2 : EW} {s1 s2 : TState} {st : MachineState} (h1 : readScalar.run s0 = some (x1, s1))
    (h2 : readScalar.run s1 = some (x2, s2))
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b4Offset)) (hb : Bd m0 a s2 st.data)
    (w16 : WordAt st.data.dmem (off (fb m0) 16) x2.c0)
    (w24 : WordAt st.data.dmem (off (fb m0) 24) x2.c1) (h13 : reg st.data .r13 = tA m0)
    (h12 : reg st.data .r12 = x1.c0.toBitVec) (hbp : reg st.data .rbp = x1.c1.toBitVec)
    (cont : ∀ (x3 : EW) (s3 : TState) (st' : MachineState), readScalar.run s2 = some (x3, s3) →
      st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b6Offset) → Bd m0 a s3 st'.data →
      WordAt st'.data.dmem (off (fb m0) 16) x3.c0 → WordAt st'.data.dmem (off (fb m0) 24) x3.c1 →
      reg st'.data .r13 = tA m0 → reg st'.data .r12 = x1.c0.toBitVec →
      reg st'.data .rbp = x1.c1.toBitVec → reg st'.data .r15 = x2.c0.toBitVec →
      WordAt st'.data.dmem (off (fb m0) 64) x2.c1 →
      Eventually (step1 Host.exe) (Goal a s0 w m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 w m0) st := by
  have cx := ctx h
  have hwf := cx.wf0 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b4Offset + b4.length)).toBitVec)
    hb.fr.fr.kept
  refine exec_at (inf hp b4_in_code (by simp [b4])) run_b4 hwf (fun _ _ ↦ rfl) hpc hb.fr.mid
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hw0, hw64, h15, hdi, hsi, hk⟩ := after_eq run_b4 ▸ ok_b4
  obtain ⟨hat, hs1⟩ := WFr.atCall cx hb.fr hb.ts hwf hm1 hmid slots_le (wr0_le hw0 (by omega))
  have kr : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14], reg st1.data r = reg st.data r :=
    fun r hr ↦ hm1.regs r _ (kept_spec hk hr)
  have e15 : reg st1.data .r15 = x2.c0.toBitVec := (hm1.regs .r15 _ h15).trans (loc_load w16)
  have e64 : WordAt st1.data.dmem (off (fb m0) 64) x2.c1 := by
    have := loc_write hm1 (o := 64) (by omega) hw64
    rwa [show (Sym.load 0 24 8).eval (frameEnv m0 st.data 176 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b4Offset + b4.length)).toBitVec) = x2.c1.toBitVec from loc_load w24,
      UInt64.ofBitVec_toBitVec] at this
  refine readCheck hp h hrs hat (mem_trans hb.mem hs1 fun q hq ↦ .inl (cx.frame_stack hq))
    ((hm1.regs .rdi _ hdi).trans (Transcript.eval_ptr0 8))
    ((hm1.regs .rsi _ hsi).trans h13)
    ((kr .rbx (by simp)).trans hb.rbx) ((kr .r14 (by simp)).trans hb.r14) (j := 28) hpc1
    b5_in_code (by simp [b5]) run_b5 (after_eq run_b5 ▸ ok_b5) c_b3
    (fun hr ↦ by simp only [foldRound_run, h1, h2, hr, Option.bind_some, Option.bind_none])
    fun x s' st' hr hpc' hbd h16 h24 hkeep hcs ↦ cont x s' st' hr hpc' hbd h16 h24
      ((hcs .r13 rfl).trans ((kr .r13 (by simp)).trans h13))
      ((hcs .r12 rfl).trans ((kr .r12 (by simp)).trans h12))
      ((hcs .rbp rfl).trans ((kr .rbp (by simp)).trans hbp)) ((hcs .r15 rfl).trans e15)
      (hkeep 64 (by omega) (by omega) _ e64)

end

end NativeRustcVmX64.Whir.FoldRound
