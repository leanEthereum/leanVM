module

public import NativeRustcVmX64.Whir.FoldRound.Reads
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names

/-!
# `fold_round` on x86-64: the fourth read, the grind

`read4` (`b6`, `b7`): the third scalar in the frame's words `72`, `80`. `grindStep` (`b8`, `b9`):
the fourth in the frame's words `120`, `112`, the grind; on `None` the `None` exit, else `b10`
(`AtB10`). `reads`: from the entry to `b10`.
-/

namespace NativeRustcVmX64.Whir.FoldRound

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.FoldRound
open NativeRustcVmX64.Transcript (Frame frameEnv MidOk)
open NativeRustcVmX64.Whir.SampleQueries (wr0 miss wrote kept wrote_spec kept_spec wr0_spec
  miss_spec midOk_writesIn)
open NativeRustcVm (WordAt EWAt EWsAt)

public section

variable [Host] {k : Nat} {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData}

/-- **The fourth read** (`b6`, `b7`): the third scalar in the frame's words `72`, `80`. -/
theorem read4 (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    {x1 x2 x3 : EW} {s1 s2 s3 : TState} {st : MachineState}
    (h1 : readScalar.run s0 = some (x1, s1)) (h2 : readScalar.run s1 = some (x2, s2))
    (h3 : readScalar.run s2 = some (x3, s3))
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b6Offset)) (hb : Bd m0 a s3 st.data)
    (w16 : WordAt st.data.dmem (off (fb m0) 16) x3.c0)
    (w24 : WordAt st.data.dmem (off (fb m0) 24) x3.c1) (h13 : reg st.data .r13 = tA m0)
    (h12 : reg st.data .r12 = x1.c0.toBitVec) (hbp : reg st.data .rbp = x1.c1.toBitVec)
    (h15 : reg st.data .r15 = x2.c0.toBitVec) (w64 : WordAt st.data.dmem (off (fb m0) 64) x2.c1)
    (cont : ∀ (x4 : EW) (s4 : TState) (st' : MachineState), readScalar.run s3 = some (x4, s4) →
      st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b8Offset) → Bd m0 a s4 st'.data →
      WordAt st'.data.dmem (off (fb m0) 16) x4.c0 → WordAt st'.data.dmem (off (fb m0) 24) x4.c1 →
      reg st'.data .r13 = tA m0 → reg st'.data .r12 = x1.c0.toBitVec →
      reg st'.data .rbp = x1.c1.toBitVec → reg st'.data .r15 = x2.c0.toBitVec →
      WordAt st'.data.dmem (off (fb m0) 64) x2.c1 →
      WordAt st'.data.dmem (off (fb m0) 72) x3.c0 → WordAt st'.data.dmem (off (fb m0) 80) x3.c1 →
      Eventually (step1 Host.exe) (Goal a s0 w m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 w m0) st := by
  have cx := ctx h
  have hwf := cx.wf0 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b6Offset + b6.length)).toBitVec)
    hb.fr.fr.kept
  refine exec_at (inf hp b6_in_code (by simp [b6])) run_b6 hwf (fun _ _ ↦ rfl) hpc hb.fr.mid
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hw0, hw72, hw80, hmiss, hdi, hsi, hk⟩ := after_eq run_b6 ▸ ok_b6
  obtain ⟨hat, hs1⟩ := WFr.atCall cx hb.fr hb.ts hwf hm1 hmid slots_le (wr0_le hw0 (by omega))
  have kr : ∀ r ∈ cs, reg st1.data r = reg st.data r := fun r hr ↦ hm1.regs r _ (kept_spec hk hr)
  have e72 : WordAt st1.data.dmem (off (fb m0) 72) x3.c0 := by
    have := loc_write hm1 (o := 72) (by omega) hw72
    rwa [show (Sym.load 0 16 8).eval (frameEnv m0 st.data 176 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b6Offset + b6.length)).toBitVec) = x3.c0.toBitVec from loc_load w16,
      UInt64.ofBitVec_toBitVec] at this
  have e80 : WordAt st1.data.dmem (off (fb m0) 80) x3.c1 := by
    have := loc_write hm1 (o := 80) (by omega) hw80
    rwa [show (Sym.load 0 24 8).eval (frameEnv m0 st.data 176 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b6Offset + b6.length)).toBitVec) = x3.c1.toBitVec from loc_load w24,
      UInt64.ofBitVec_toBitVec] at this
  have e64 := loc_keep hwf hm1 (midOk_writesIn hmid) (o := 64) (by omega)
    (missL_spec hmiss (by simp)) w64
  refine readCheck hp h hrs hat (mem_trans hb.mem hs1 fun q hq ↦ .inl (cx.frame_stack hq))
    ((hm1.regs .rdi _ hdi).trans (Transcript.eval_ptr0 8)) ((hm1.regs .rsi _ hsi).trans h13)
    ((kr .rbx (by simp [cs])).trans hb.rbx) ((kr .r14 (by simp [cs])).trans hb.r14) (j := 37)
    hpc1 b7_in_code (by simp [b7]) run_b7 (after_eq run_b7 ▸ ok_b7) c_b3
    (fun hr ↦ by simp only [foldRound_run, h1, h2, h3, hr, Option.bind_some, Option.bind_none])
    fun x s' st' hr hpc' hbd h16 h24 hkeep hcs ↦ cont x s' st' hr hpc' hbd h16 h24
      ((hcs .r13 rfl).trans ((kr .r13 (by simp [cs])).trans h13))
      ((hcs .r12 rfl).trans ((kr .r12 (by simp [cs])).trans h12))
      ((hcs .rbp rfl).trans ((kr .rbp (by simp [cs])).trans hbp))
      ((hcs .r15 rfl).trans ((kr .r15 (by simp [cs])).trans h15))
      (hkeep 64 (by omega) (by omega) _ e64) (hkeep 72 (by omega) (by omega) _ e72)
      (hkeep 80 (by omega) (by omega) _ e80)

/-- **The grind** (`b8`, `b9`): the fourth scalar in the frame's words `120`, `112`. -/
theorem grindStep (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hgr : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    {x1 x2 x3 x4 : EW} {s1 s2 s3 s4 : TState} {st : MachineState}
    (h1 : readScalar.run s0 = some (x1, s1)) (h2 : readScalar.run s1 = some (x2, s2))
    (h3 : readScalar.run s2 = some (x3, s3)) (h4 : readScalar.run s3 = some (x4, s4))
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b8Offset)) (hb : Bd m0 a s4 st.data)
    (w16 : WordAt st.data.dmem (off (fb m0) 16) x4.c0)
    (w24 : WordAt st.data.dmem (off (fb m0) 24) x4.c1) (h13 : reg st.data .r13 = tA m0)
    (h12 : reg st.data .r12 = x1.c0.toBitVec) (hbp : reg st.data .rbp = x1.c1.toBitVec)
    (h15 : reg st.data .r15 = x2.c0.toBitVec) (w64 : WordAt st.data.dmem (off (fb m0) 64) x2.c1)
    (w72 : WordAt st.data.dmem (off (fb m0) 72) x3.c0)
    (w80 : WordAt st.data.dmem (off (fb m0) 80) x3.c1)
    (cont : ∀ (s5 : TState) (st' : MachineState), st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b10Offset) →
      AtB10 a s0 w m0 x1 x2 x3 x4 s5 st'.data → Eventually (step1 Host.exe) (Goal a s0 w m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 w m0) st := by
  have cx := ctx h
  have hwf := cx.wf0 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b8Offset + b8.length)).toBitVec)
    hb.fr.fr.kept
  refine exec_at (inf hp b8_in_code (by simp [b8])) run_b8 hwf (fun _ _ ↦ rfl) hpc hb.fr.mid
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hw0, hw120, hw112, hmiss, hdi, hsi, hk⟩ := after_eq run_b8 ▸ ok_b8
  obtain ⟨hat, hs1⟩ := WFr.atCall cx hb.fr hb.ts hwf hm1 hmid slots_le (wr0_le hw0 (by omega))
  have kr : ∀ r ∈ cs, reg st1.data r = reg st.data r := fun r hr ↦ hm1.regs r _ (kept_spec hk hr)
  have e120 : WordAt st1.data.dmem (off (fb m0) 120) x4.c0 := by
    have := loc_write hm1 (o := 120) (by omega) hw120
    rwa [show (Sym.load 0 16 8).eval (frameEnv m0 st.data 176 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b8Offset + b8.length)).toBitVec) = x4.c0.toBitVec from loc_load w16,
      UInt64.ofBitVec_toBitVec] at this
  have e112 : WordAt st1.data.dmem (off (fb m0) 112) x4.c1 := by
    have := loc_write hm1 (o := 112) (by omega) hw112
    rwa [show (Sym.load 0 24 8).eval (frameEnv m0 st.data 176 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b8Offset + b8.length)).toBitVec) = x4.c1.toBitVec from loc_load w24,
      UInt64.ofBitVec_toBitVec] at this
  have e64 := loc_keep hwf hm1 (midOk_writesIn hmid) (o := 64) (by omega)
    (missL_spec hmiss (by simp)) w64
  have e72 := loc_keep hwf hm1 (midOk_writesIn hmid) (o := 72) (by omega)
    (missL_spec hmiss (by simp)) w72
  have e80 := loc_keep hwf hm1 (midOk_writesIn hmid) (o := 80) (by omega)
    (missL_spec hmiss (by simp)) w80
  have hmem1 := mem_trans hb.mem hs1 fun q hq ↦ .inl (cx.frame_stack hq)
  have hbits : grindBits st1.data = 7 := by
    unfold grindBits
    rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hsi]
    rfl
  refine hat.grind cx hgr slots_le gr_le ((hm1.regs .rdi _ hdi).trans h13) hbits (by omega) hpc1
    fun st2 hpc2 hw2 hok hnext hcs hso ↦ ?_
  have hR : ∀ x, x < 184 → ¬ ((InRange (stackBelow m0 foldRoundStack) foldRoundStack
      (off (fb m0) x) ∧ ¬ InRange (stackBelow m0 176) (176 + 8) (off (fb m0) x)) ∨
      InRange (tA m0) tstateBytes (off (fb m0) x)) := fun x hx hq ↦
    hq.elim (frame_not_call h hx).1 (frame_not_call h hx).2
  have kw : ∀ {o : Nat} {v : UInt64}, o + 8 ≤ 176 → WordAt st1.data.dmem (off (fb m0) o) v →
      WordAt st2.data.dmem (off (fb m0) o) v := fun ho hv ↦
    frame_keep hso (fun i hi ↦ hR _ (by omega)) hv
  have hmem2 : SameOutside m0.dmem st2.data.dmem (Pre18 m0) :=
    mem_trans hmem1 hso fun q hq ↦ hq.elim (fun h ↦ .inl h.1) .inr
  have hwf2 := cx.wf0 (vars := fun _ ↦ 0) (ret := 0) hw2.fr.kept
  refine exec_at (inf hp b9_in_code (by simp [b9])) run_b9 hwf2 (by intro l h; cases h) hpc2
    hw2.mid fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hmem3, hk3⟩ := after_eq run_b9 ▸ ok_b9
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 hmem3
  have hw3 := WFr.block cx hw2 hwf2 hm3 hmid3 slots_le fun q hq ↦ absurd hq (no_written hmem3)
  have hcs3 : ∀ r, calleeSaved r = true → reg st3.data r = reg st1.data r := fun r hr ↦
    (hm3.regs r _ (kept_spec hk3 (cs_of hr))).trans (hcs r hr)
  simp only [PcOk] at hpc3
  have hal : (reg st2.data .rax).toNat % 256 =
      (okWord ((NativeVm.Model.grind 7).run s4).isSome).toNat := hok
  rw [show (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)).eval
      (frameEnv m0 st2.data 176 [] (fun _ ↦ 0) 0) = decide ((reg st2.data .rax).toNat % 256 = 0)
    from al_zero _, hal] at hpc3
  cases hr : (NativeVm.Model.grind 7).run s4 with
  | none =>
    have e : decide ((okWord (Option.none : Option (Unit × TState)).isSome).toNat = 0) = true := by
      decide
    rw [hr] at hpc3
    simp only [e, ↓reduceIte] at hpc3
    rw [hp.label NativeRustcVmX64.Vm.FoldRound.label_7_at] at hpc3
    exact none20 hp h hpc3 hw3 ((hcs3 .rbx rfl).trans ((kr .rbx (by simp [cs])).trans hb.rbx))
      (by simp only [foldRound_run, h1, h2, h3, h4, hr, Option.bind_some, Option.bind_none])
  | some y =>
    obtain ⟨_, s5⟩ := y
    have e : decide ((okWord true).toNat = 0) = false := by decide
    rw [hr, Option.isSome_some] at hpc3
    simp only [e, Bool.false_eq_true, ↓reduceIte] at hpc3
    refine cont s5 st3 hpc3 ⟨⟨hw3, hd3 ▸ hmem2, hd3 ▸ hnext () s5 hr,
      (hcs3 .rbx rfl).trans ((kr .rbx (by simp [cs])).trans hb.rbx),
      (hcs3 .r14 rfl).trans ((kr .r14 (by simp [cs])).trans hb.r14)⟩,
      (hcs3 .r13 rfl).trans ((kr .r13 (by simp [cs])).trans h13),
      (hcs3 .r12 rfl).trans ((kr .r12 (by simp [cs])).trans h12),
      (hcs3 .rbp rfl).trans ((kr .rbp (by simp [cs])).trans hbp),
      (hcs3 .r15 rfl).trans ((kr .r15 (by simp [cs])).trans h15),
      hd3 ▸ kw (by omega) e64, hd3 ▸ kw (by omega) e72, hd3 ▸ kw (by omega) e80,
      hd3 ▸ kw (by omega) e120, hd3 ▸ kw (by omega) e112, ?_⟩
    simp only [foldRound_run, h1, h2, h3, h4, hr, Option.bind_some]

/-- **The reads and the grind**: from the entry to `b10`. -/
theorem reads (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hgr : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (cont : ∀ (x1 x2 x3 x4 : EW) (s5 : TState) (st : MachineState),
      st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b10Offset) → AtB10 a s0 w m0 x1 x2 x3 x4 s5 st.data →
      Eventually (step1 Host.exe) (Goal a s0 w m0) st) :
    Eventually (step1 Host.exe) (Goal a s0 w m0) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b0Offset)⟩ :=
  read1 hp h hrs fun _ _ _ h1 hpc hb w16 w24 h13 ↦
    read2 hp h hrs h1 hpc hb w16 w24 h13 fun _ _ _ h2 hpc hb w16 w24 h13 h12 hbp ↦
    read3 hp h hrs h1 h2 hpc hb w16 w24 h13 h12 hbp
      fun _ _ _ h3 hpc hb w16 w24 h13 h12 hbp h15 w64 ↦
    read4 hp h hrs h1 h2 h3 hpc hb w16 w24 h13 h12 hbp h15 w64
      fun _ _ _ h4 hpc hb w16 w24 h13 h12 hbp h15 w64 w72 w80 ↦
    grindStep hp h hgr h1 h2 h3 h4 hpc hb w16 w24 h13 h12 hbp h15 w64 w72 w80
      fun s5 st hpc hat ↦ cont _ _ _ _ s5 st hpc hat

end

end NativeRustcVmX64.Whir.FoldRound
