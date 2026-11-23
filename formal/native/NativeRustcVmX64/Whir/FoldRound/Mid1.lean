module

public import NativeRustcVmX64.Whir.FoldRound.Env
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names

/-!
# `fold_round` on x86-64: the squeezes and the first products

The challenges `α = alA s5`, `β = beA s5` and the products the code computes (`p1` to `p6`).
`Pt`: a body state with the `TState`, the frame's words `L`, the first scalar in R12, RBP, the
round's outcome. `s1` (`b10`, `squeeze`), `s2` (`b11`, `squeeze`), `s3` (`b12`, `EW::mul`: `p1`),
`s4` (`b13`, `EW::mul`: `α α`).
-/

namespace NativeRustcVmX64.Whir.FoldRound

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.FoldRound
open NativeRustcVmX64.Transcript (Frame frameEnv MidOk)
open NativeRustcVmX64.Whir.SampleQueries (wr0 miss wrote kept wrote_spec kept_spec wr0_spec
  miss_spec midOk_writesIn miss_of_wr0)
open NativeRustcVm (WordAt EWAt EWsAt)

@[expose] public section

/-- `α`, `β` of the round after the grind's state `s5`. -/
abbrev alA (s5 : TState) : EW := (sq s5).1
abbrev beA (s5 : TState) : EW := (sq (sq s5).2).1

/-- The products. -/
def p1 (w : WhirStateW) (s5 : TState) (u0 : EW) : EW :=
  EW.mul (alA s5) ⟨w.claim.c0 ^^^ u0.c0, w.claim.c1 ^^^ u0.c1⟩
def aa (s5 : TState) : EW := EW.mul (alA s5) (alA s5)
def p3 (s5 : TState) (v : EW) : EW := EW.mul (aa s5) v
def p4 (s5 : TState) (c0 : EW) : EW := EW.mul (beA s5) c0
def ab (s5 : TState) : EW := EW.mul (alA s5) (beA s5)
def p6 (s5 : TState) (c0 c1 : EW) : EW := EW.mul (ab s5) ⟨c1.c0 ^^^ c0.c0, c1.c1 ^^^ c0.c1⟩

/-- **A body state of the products**: the `TState` `s`, the frame's words `L`. -/
structure Pt [Labels] (a : DecArea) (s0 : TState) (w : WhirStateW) (m0 : MachineData)
    (x1 x2 x3 x4 : EW) (s5 s : TState) (L : List (Nat × UInt64)) (st : MachineData) : Prop where
  bd : Bd m0 a s st
  fw : FW st.dmem m0 L
  r12 : reg st .r12 = x1.c0.toBitVec
  rbp : reg st .rbp = x1.c1.toBitVec
  model : (foldRound w).run s0 = some ((foldW w x1 x2 x3 x4 (alA s5) (beA s5),
    ⟨alA s5, beA s5⟩), (sq (sq s5).2).2)

end

public section

variable [Host] {k : Nat} {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData}
  {x1 x2 x3 x4 : EW} {s5 : TState}

/-- **`b10`, `squeeze`**: `α` in RAX, RDX. -/
theorem s1 (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b10Offset))
    (hA : AtB10 a s0 w m0 x1 x2 x3 x4 s5 st.data)
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b11Offset) →
      Pt a s0 w m0 x1 x2 x3 x4 s5 (sq s5).2
        [(64, x2.c1), (72, x3.c0), (80, x3.c1), (120, x4.c0), (112, x4.c1)] st'.data →
      reg st'.data .r15 = x2.c0.toBitVec → reg st'.data .r13 = tA m0 →
      reg st'.data .rax = (alA s5).c0.toBitVec → reg st'.data .rdx = (alA s5).c1.toBitVec →
      Eventually (step1 Host.exe) (Goal a s0 w m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 w m0) st := by
  have cx := ctx h
  obtain ⟨hmid, hw0, hdi, hk⟩ := after_eq run_b10 ▸ ok_b10
  have hwf := cx.wf0 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b10Offset + b10.length)).toBitVec)
    hA.bd.fr.fr.kept
  refine sqCall hp h hsq hpc hA.bd b10_in_code (by simp [b10]) run_b10 hmid
    (wr0_le hw0 (by omega)) (kept_sub hk (by simp [cs])) hdi hA.r13
    fun st1 st' hm1 hpc' hbd hax hdx hcs hkeep ↦ ?_
  have kr : ∀ r ∈ cs, reg st1 r = reg st.data r := fun r hr ↦ hm1.regs r _ (kept_spec hk hr)
  have hfw : FW st.data.dmem m0 [(64, x2.c1), (72, x3.c0), (80, x3.c1), (120, x4.c0), (112, x4.c1)] := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    exacts [hA.w64, hA.w72, hA.w80, hA.w120, hA.w112]
  refine cont st' hpc' ⟨hbd, FW.call hkeep (by simp) (FW.block hwf hm1 (midOk_writesIn hmid)
      (miss_of_wr8 hw0 (by simp)) (by simp) hfw),
    (hcs .r12 rfl).trans ((kr .r12 (by simp [cs])).trans hA.r12),
    (hcs .rbp rfl).trans ((kr .rbp (by simp [cs])).trans hA.rbp), hA.model⟩
    ((hcs .r15 rfl).trans ((kr .r15 (by simp [cs])).trans hA.r15))
    ((hcs .r13 rfl).trans ((kr .r13 (by simp [cs])).trans hA.r13)) hax hdx

/-- **`b11`, `squeeze`**: `α` to the frame's words `56`, `32`; `β` in RAX, RDX. -/
theorem s2 (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b11Offset))
    (hP : Pt a s0 w m0 x1 x2 x3 x4 s5 (sq s5).2
      [(64, x2.c1), (72, x3.c0), (80, x3.c1), (120, x4.c0), (112, x4.c1)] st.data)
    (h15 : reg st.data .r15 = x2.c0.toBitVec) (h13 : reg st.data .r13 = tA m0)
    (hax : reg st.data .rax = (alA s5).c0.toBitVec) (hdx : reg st.data .rdx = (alA s5).c1.toBitVec)
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b12Offset) →
      Pt a s0 w m0 x1 x2 x3 x4 s5 (sq (sq s5).2).2
        [(56, (alA s5).c0), (32, (alA s5).c1), (64, x2.c1), (72, x3.c0), (80, x3.c1),
          (120, x4.c0), (112, x4.c1)] st'.data →
      reg st'.data .r15 = x2.c0.toBitVec → reg st'.data .r13 = tA m0 →
      reg st'.data .rax = (beA s5).c0.toBitVec → reg st'.data .rdx = (beA s5).c1.toBitVec →
      Eventually (step1 Host.exe) (Goal a s0 w m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 w m0) st := by
  have cx := ctx h
  obtain ⟨hmid, hw0, hw56, hw32, hmiss, hdi, hk⟩ := after_eq run_b11 ▸ ok_b11
  have hwf := cx.wf0 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b11Offset + b11.length)).toBitVec)
    hP.bd.fr.fr.kept
  refine sqCall hp h hsq hpc hP.bd b11_in_code (by simp [b11]) run_b11 hmid
    (wr0_le hw0 (by omega)) (kept_sub hk (by simp [cs])) hdi h13
    fun st1 st' hm1 hpc' hbd hax' hdx' hcs hkeep ↦ ?_
  have kr : ∀ r ∈ cs, reg st1 r = reg st.data r := fun r hr ↦ hm1.regs r _ (kept_spec hk hr)
  have e56 : WordAt st1.dmem (off (fb m0) 56) (alA s5).c0 := by
    have := loc_write hm1 (o := 56) (by omega) hw56
    rwa [show (Sym.reg .rax).eval (frameEnv m0 st.data 176 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b11Offset + b11.length)).toBitVec) = (alA s5).c0.toBitVec from hax,
      UInt64.ofBitVec_toBitVec] at this
  have e32 : WordAt st1.dmem (off (fb m0) 32) (alA s5).c1 := by
    have := loc_write hm1 (o := 32) (by omega) hw32
    rwa [show (Sym.reg .rdx).eval (frameEnv m0 st.data 176 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b11Offset + b11.length)).toBitVec) = (alA s5).c1.toBitVec from hdx,
      UInt64.ofBitVec_toBitVec] at this
  have hfw1 := FW.block hwf hm1 (midOk_writesIn hmid) (miss_of_missL hmiss (by simp)) (by simp)
    hP.fw
  have hfw : FW st1.dmem m0 ([(56, (alA s5).c0), (32, (alA s5).c1)] ++
      [(64, x2.c1), (72, x3.c0), (80, x3.c1), (120, x4.c0), (112, x4.c1)]) := by
    refine FW.append (fun p hp ↦ ?_) hfw1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    exacts [e56, e32]
  refine cont st' hpc' ⟨hbd, FW.call hkeep (by simp) hfw,
    (hcs .r12 rfl).trans ((kr .r12 (by simp [cs])).trans hP.r12),
    (hcs .rbp rfl).trans ((kr .rbp (by simp [cs])).trans hP.rbp), hP.model⟩
    ((hcs .r15 rfl).trans ((kr .r15 (by simp [cs])).trans h15))
    ((hcs .r13 rfl).trans ((kr .r13 (by simp [cs])).trans h13)) hax' hdx'

/-- **`b12`, `EW::mul`**: `β` to the frame's words `48`, `40`; `p1` in RAX, RDX, `α`'s low limb
in R13. -/
theorem s3 (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b12Offset))
    (hP : Pt a s0 w m0 x1 x2 x3 x4 s5 (sq (sq s5).2).2
      [(56, (alA s5).c0), (32, (alA s5).c1), (64, x2.c1), (72, x3.c0), (80, x3.c1),
        (120, x4.c0), (112, x4.c1)] st.data)
    (h15 : reg st.data .r15 = x2.c0.toBitVec)
    (hax : reg st.data .rax = (beA s5).c0.toBitVec) (hdx : reg st.data .rdx = (beA s5).c1.toBitVec)
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b13Offset) →
      Pt a s0 w m0 x1 x2 x3 x4 s5 (sq (sq s5).2).2
        [(48, (beA s5).c0), (40, (beA s5).c1), (56, (alA s5).c0), (32, (alA s5).c1),
          (64, x2.c1), (72, x3.c0), (80, x3.c1), (120, x4.c0), (112, x4.c1)] st'.data →
      reg st'.data .r15 = x2.c0.toBitVec → reg st'.data .r13 = (alA s5).c0.toBitVec →
      reg st'.data .rax = (p1 w s5 x1).c0.toBitVec → reg st'.data .rdx = (p1 w s5 x1).c1.toBitVec →
      Eventually (step1 Host.exe) (Goal a s0 w m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 w m0) st := by
  obtain ⟨hmid, hw0, hw48, hw40, hmiss, hdi, hsi, hdx1, hcx1, h13, hk⟩ := after_eq run_b12 ▸ ok_b12
  have hwf := st_wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b12Offset + b12.length)).toBitVec) h
    hP.bd.fr.fr.kept
  have hm0 := st_match (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b12Offset + b12.length)).toBitVec)
    hP.bd.fr hP.bd.r14
  have kbx : (after b12 stS).reg .rbx = some (.reg .rbx) := (keptI_spec hk (by simp)).trans rfl
  have kbp : (after b12 stS).reg .rbp = some (.reg .rbp) := (keptI_spec hk (by simp)).trans rfl
  have k12 : (after b12 stS).reg .r12 = some (.reg .r12) := (keptI_spec hk (by simp)).trans rfl
  have k15 : (after b12 stS).reg .r15 = some (.reg .r15) := (keptI_spec hk (by simp)).trans rfl
  have k14 : (after b12 stS).reg .r14 = some (.ptr 1 0) := (keptI_spec hk (by simp)).trans rfl
  have hcl := (ws_of_mem h hP.bd.mem).claim
  rw [ewAt_iff] at hcl
  have l0 : (stEnv m0 st.data (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b12Offset + b12.length)).toBitVec).load 1 0 8 =
      w.claim.c0.toBitVec :=
    Transcript.load_ofMachine (o := 0) rfl (by rw [off_zero]; exact hcl.1)
  have l8 : (stEnv m0 st.data (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b12Offset + b12.length)).toBitVec).load 1 8 8 =
      w.claim.c1.toBitVec :=
    Transcript.load_ofMachine (o := 8) rfl hcl.2
  refine mulCall hp h hmul hpc hP.bd b12_in_code (by simp [b12]) hwf hm0 run_b12 hmid
    (wr0_le hw0 (by omega)) (fun st1 hm1 ↦ ⟨hm1.regs .rbx _ kbx,
      (hm1.regs .r14 _ k14).trans ((Transcript.eval_ptr rfl).trans hP.bd.r14.symm)⟩)
    fun st1 st' hm1 hpc' hbd hax' hdx' hcs hkeep ↦ ?_
  have kr : ∀ r ∈ [Reg64.rbp, .r12, .r15], reg st1 r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hm1.regs _ _ kbp, hm1.regs _ _ k12, hm1.regs _ _ k15]
  have e48 : WordAt st1.dmem (off (fb m0) 48) (beA s5).c0 := by
    have := loc_write hm1 (o := 48) (by omega) hw48
    rwa [show (Sym.reg .rax).eval (stEnv m0 st.data (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b12Offset + b12.length)).toBitVec) = (beA s5).c0.toBitVec from hax,
      UInt64.ofBitVec_toBitVec] at this
  have e40 : WordAt st1.dmem (off (fb m0) 40) (beA s5).c1 := by
    have := loc_write hm1 (o := 40) (by omega) hw40
    rwa [show (Sym.reg .rdx).eval (stEnv m0 st.data (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b12Offset + b12.length)).toBitVec) = (beA s5).c1.toBitVec from hdx,
      UInt64.ofBitVec_toBitVec] at this
  have hfw1 := FW.block hwf hm1 (midOk_writesIn hmid) (miss_of_missL hmiss (by simp)) (by simp)
    hP.fw
  have hfw : FW st1.dmem m0 ([(48, (beA s5).c0), (40, (beA s5).c1)] ++
      [(56, (alA s5).c0), (32, (alA s5).c1), (64, x2.c1), (72, x3.c0), (80, x3.c1),
        (120, x4.c0), (112, x4.c1)]) := by
    refine FW.append (fun p hp ↦ ?_) hfw1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    exacts [e48, e40]
  have ea : (⟨.ofBitVec (reg st1 .rdi), .ofBitVec (reg st1 .rsi)⟩ : EW) = alA s5 :=
    ew_of _ ((hm1.regs .rdi _ hdi).trans (loc_load (hP.fw.get (o := 56) (v := (alA s5).c0)
      (by simp)))) ((hm1.regs .rsi _ hsi).trans (loc_load (hP.fw.get (o := 32) (v := (alA s5).c1)
      (by simp))))
  have ec : (⟨.ofBitVec (reg st1 .rdx), .ofBitVec (reg st1 .rcx)⟩ : EW) =
      ⟨w.claim.c0 ^^^ x1.c0, w.claim.c1 ^^^ x1.c1⟩ := by
    refine ew_of _ ((hm1.regs .rdx _ hdx1).trans ?_) ((hm1.regs .rcx _ hcx1).trans ?_)
    · rw [NativeRustcVmX64.Arrays.eval_xor]
      show (stEnv m0 st.data _ _).load 1 0 8 ^^^ reg st.data .r12 = _
      rw [l0, hP.r12]
      rfl
    · rw [NativeRustcVmX64.Arrays.eval_xor]
      show (stEnv m0 st.data _ _).load 1 8 8 ^^^ reg st.data .rbp = _
      rw [l8, hP.rbp]
      rfl
  rw [ea, ec] at hax' hdx'
  refine cont st' hpc' ⟨hbd, FW.call hkeep (by simp) hfw,
    (hcs .r12 rfl).trans ((kr .r12 (by simp)).trans hP.r12),
    (hcs .rbp rfl).trans ((kr .rbp (by simp)).trans hP.rbp), hP.model⟩
    ((hcs .r15 rfl).trans ((kr .r15 (by simp)).trans h15))
    ((hcs .r13 rfl).trans ((hm1.regs .r13 _ h13).trans (loc_load (hP.fw.get (o := 56)
      (v := (alA s5).c0) (by simp))))) hax' hdx'

/-- **`b13`, `EW::mul`**: `p1` to the frame's words `96`, `104`; `α α` in RAX, RDX. -/
theorem s4 (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b13Offset))
    (hP : Pt a s0 w m0 x1 x2 x3 x4 s5 (sq (sq s5).2).2
      [(48, (beA s5).c0), (40, (beA s5).c1), (56, (alA s5).c0), (32, (alA s5).c1),
        (64, x2.c1), (72, x3.c0), (80, x3.c1), (120, x4.c0), (112, x4.c1)] st.data)
    (h15 : reg st.data .r15 = x2.c0.toBitVec) (h13 : reg st.data .r13 = (alA s5).c0.toBitVec)
    (hax : reg st.data .rax = (p1 w s5 x1).c0.toBitVec)
    (hdx : reg st.data .rdx = (p1 w s5 x1).c1.toBitVec)
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b14Offset) →
      Pt a s0 w m0 x1 x2 x3 x4 s5 (sq (sq s5).2).2
        [(96, (p1 w s5 x1).c0), (104, (p1 w s5 x1).c1), (48, (beA s5).c0), (40, (beA s5).c1),
          (56, (alA s5).c0), (32, (alA s5).c1), (64, x2.c1), (72, x3.c0), (80, x3.c1),
          (120, x4.c0), (112, x4.c1)] st'.data →
      reg st'.data .r15 = x2.c0.toBitVec →
      reg st'.data .rax = (aa s5).c0.toBitVec → reg st'.data .rdx = (aa s5).c1.toBitVec →
      Eventually (step1 Host.exe) (Goal a s0 w m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 w m0) st := by
  have cx := ctx h
  obtain ⟨hmid, hw0, hw96, hw104, hmiss, hdi, hsi, hdx1, hcx1, hk⟩ := after_eq run_b13 ▸ ok_b13
  have hwf := cx.wf0 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b13Offset + b13.length)).toBitVec)
    hP.bd.fr.fr.kept
  refine mulCall hp h hmul hpc hP.bd b13_in_code (by simp [b13]) hwf hP.bd.fr.mid run_b13 hmid
    (wr0_le hw0 (by omega)) (fun st1 hm1 ↦ ⟨hm1.regs .rbx _ (kept_spec hk (by simp [cs])),
      hm1.regs .r14 _ (kept_spec hk (by simp [cs]))⟩)
    fun st1 st' hm1 hpc' hbd hax' hdx' hcs hkeep ↦ ?_
  have kr : ∀ r ∈ cs, reg st1 r = reg st.data r := fun r hr ↦ hm1.regs r _ (kept_spec hk hr)
  have e96 : WordAt st1.dmem (off (fb m0) 96) (p1 w s5 x1).c0 := by
    have := loc_write hm1 (o := 96) (by omega) hw96
    rwa [show (Sym.reg .rax).eval (frameEnv m0 st.data 176 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b13Offset + b13.length)).toBitVec) = (p1 w s5 x1).c0.toBitVec from hax,
      UInt64.ofBitVec_toBitVec] at this
  have e104 : WordAt st1.dmem (off (fb m0) 104) (p1 w s5 x1).c1 := by
    have := loc_write hm1 (o := 104) (by omega) hw104
    rwa [show (Sym.reg .rdx).eval (frameEnv m0 st.data 176 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b13Offset + b13.length)).toBitVec) = (p1 w s5 x1).c1.toBitVec from hdx,
      UInt64.ofBitVec_toBitVec] at this
  have hfw1 := FW.block hwf hm1 (midOk_writesIn hmid) (miss_of_missL hmiss (by simp)) (by simp)
    hP.fw
  have hfw : FW st1.dmem m0 ([(96, (p1 w s5 x1).c0), (104, (p1 w s5 x1).c1)] ++
      [(48, (beA s5).c0), (40, (beA s5).c1), (56, (alA s5).c0), (32, (alA s5).c1),
        (64, x2.c1), (72, x3.c0), (80, x3.c1), (120, x4.c0), (112, x4.c1)]) := by
    refine FW.append (fun p hp ↦ ?_) hfw1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    exacts [e96, e104]
  have l32 := loc_load (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b13Offset + b13.length)).toBitVec) (hP.fw.get (o := 32) (v := (alA s5).c1) (by simp))
  have ea : (⟨.ofBitVec (reg st1 .rdi), .ofBitVec (reg st1 .rsi)⟩ : EW) = alA s5 :=
    ew_of _ ((hm1.regs .rdi _ hdi).trans h13) ((hm1.regs .rsi _ hsi).trans l32)
  have ea' : (⟨.ofBitVec (reg st1 .rdx), .ofBitVec (reg st1 .rcx)⟩ : EW) = alA s5 :=
    ew_of _ ((hm1.regs .rdx _ hdx1).trans h13) ((hm1.regs .rcx _ hcx1).trans l32)
  rw [ea, ea'] at hax' hdx'
  refine cont st' hpc' ⟨hbd, FW.call hkeep (by simp) hfw,
    (hcs .r12 rfl).trans ((kr .r12 (by simp [cs])).trans hP.r12),
    (hcs .rbp rfl).trans ((kr .rbp (by simp [cs])).trans hP.rbp), hP.model⟩
    ((hcs .r15 rfl).trans ((kr .r15 (by simp [cs])).trans h15)) hax' hdx'

end

end NativeRustcVmX64.Whir.FoldRound
