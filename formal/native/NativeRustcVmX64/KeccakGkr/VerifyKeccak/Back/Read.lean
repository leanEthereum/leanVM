module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.Open2
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names

/-!
# Reading the sixty-four output slices

Blocks 59–60 put the slices directly into `KeccakOutW` and preserve the opening value in spills.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea TStateAt tstateBytes)
open NativeRustcVm.KeccakGkr (off)

public section

@[expose] def Vf (V : Vs) (v : EW) : Vs := { V with f0 := v.c0.toBitVec, f1 := v.c1.toBitVec }

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

theorem readStep (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    {st : MachineState} {V : Vs} {s1 : TState} {v : EW}
    (hat : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b59Offset wrAll t59 (vv m0 V) st)
    (hv : NativeRustcVm.EWAt st.data.dmem (off (fb m0) 104) v)
    (hts : TStateAt st.data.dmem (reg m0 .rdi) a s1)
    (hfail : (readScalars 64).run s1 = none →
      (NativeVm.Model.verifyKeccak (reg m0 .rsi).toNat inst output).run s = none)
    (cont : ∀ st' sl s2, At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b61Offset wrAll t60 (vv m0 (Vf V v)) st' →
      (readScalars 64).run s1 = some (sl, s2) →
      NativeRustcVm.EWsAt st'.data.dmem (off (keccakOutArg m0) 584) sl.toList →
      TStateAt st'.data.dmem (reg m0 .rdi) a s2 →
      Chg m0 st.data.dmem st'.data.dmem [(0, 88), (3296, 48)] [(1, 0, 760), (4, 584, 1024)] →
      Kept st.data.dmem st'.data.dmem →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) st') :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  have hrc : RcAt m0 verifyKeccakStack := hpre.2.2.1
  have hl := fun ret ↦ ld_ew (rs := rsOf m0) (vals := vv m0 V) (ret := ret) hv
  have ho := fun ret ↦ argLoad c hat.2.same (vals := vv m0 V) (ret := ret) (i := 1) (by decide)
  refine stepC (T' := t60) (vals' := vv m0 (Vf V v)) hp c h hat b59_in_code
    (by simp [b59]) run_b59 hat.2.mt (by decide) (oc := 48) (by decide) rfl (hrs s1)
    (Sk := readScalarsStack) (by rw [vk_eq]; decide)
    (fun mc hmc hk hsk hso hrsp hch hkk ↦ ?_) (Lc := [])
    (Oc := [(1, 0, 760), (4, 584, 1024)]) (fun mc m' hmc hq ↦ ?_)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl ?_
    (fun i hi ↦ nomatch tregE (rfl : t60.reg .rax = some (.reg .rax)) hi)
    (fun i hi ↦ nomatch tregE (rfl : t60.reg .rdx = some (.reg .rdx)) hi)
    rfl rfl rfl (fun _ _ _ _ _ h ↦ by cases h) rfl
    fun st1 hpc1 hB1 ⟨mc, hmc, hrsp, hq, _⟩ hc1 hk1 ↦ ?_
  · have ca : CallAt m0 wrAll 48 mc := ⟨hrsp, by decide, hk, hso⟩
    have rdi : reg mc .rdi = reg m0 .rdi := hmc.regs .rdi _ rfl
    have rsi : reg mc .rsi = off (keccakOutArg m0) 584 := by
      change mc.regs.get64 .rsi = _
      rw [hmc.regs .rsi _ rfl]
      simp only [Sym.eval, ho, add64]
      rfl
    have rdx : reg mc .rdx = 64#64 := hmc.regs .rdx _ rfl
    unfold ReadScalarsPre
    rw [rdi, rsi, rdx]
    refine ⟨hsk, ca.rc c hrc (by rw [vk_eq]; decide),
      Chg.ts c hch (by decide) rfl (by decide) hkk hts,
      ca.tok c (by rw [vk_eq]; decide),
      ca.outR c h (i := 4) (by rw [vk_eq]; decide) (by decide) (by decide) (by decide) (by decide), ?_⟩
    apply ca.got c (by rw [vk_eq]; decide)
    simp only [NativeRustcVm.Transcript.DecArea.region, tstateBytes, show (64#64).toNat = 64 from rfl]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨(reg m0 .rdi, 760), by simp, le_rfl, le_rfl⟩
    · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
    · have hoff : (off (keccakOutArg m0) 584).toNat = (keccakOutArg m0).toNat + 584 :=
        offR c (i := 4) (o := 584) (by decide) (by decide) (by decide)
      refine ⟨(keccakOutArg m0, 1608), by simp, ?_, ?_⟩
      · dsimp only [Prod.fst, Prod.snd]
        rw [hoff]
        omega
      · dsimp only [Prod.fst, Prod.snd]
        rw [hoff]
    · exact ⟨(rcAddr, 192), by simp, le_rfl, le_rfl⟩
  · have rdi : reg mc .rdi = off (ob m0 1) 0 := (hmc.regs .rdi _ rfl).trans (off0 _).symm
    have rsi : reg mc .rsi = off (ob m0 4) 584 := by
      change mc.regs.get64 .rsi = _
      rw [hmc.regs .rsi _ rfl]
      simp only [Sym.eval, ho, add64]
      rfl
    have rdx : reg mc .rdx = 64#64 := hmc.regs .rdx _ rfl
    obtain ⟨-, -, -, hso, hsv⟩ := hq
    rw [rdx] at hso
    exact chgQ hso (fun q h ↦ h.elim
      (fun h ↦ .inr (inR_reg rsi (by decide) h)) fun h ↦ h.elim
      (fun h ↦ .inr (inR_reg rdi List.mem_cons_self h)) .inl) hsv
  · intro ret
    simp only [List.cons_append, List.nil_append, List.forall_mem_cons, Sym.eval, (hl ret).1,
      (hl ret).2, ho]
    and_intros <;> first | rfl | exact fun _ h ↦ nomatch h
  have rdi : reg mc .rdi = reg m0 .rdi := hmc.regs .rdi _ rfl
  have rsi : reg mc .rsi = off (keccakOutArg m0) 584 := by
    change mc.regs.get64 .rsi = _
    rw [hmc.regs .rsi _ rfl]
    simp only [Sym.eval, ho, add64]
    rfl
  have rdx : reg mc .rdx = 64#64 := hmc.regs .rdx _ rfl
  obtain ⟨hal, hews, hnext, -, -⟩ := hq
  rw [rdx] at hal hews hnext
  rw [rsi] at hews
  rw [rdi] at hnext
  simp only [show (64#64).toNat = 64 from rfl] at hal hews hnext
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b59_next] at hpc1
  refine stepJ (T' := t60) (vals' := vv m0 (Vf V v)) (o := NativeRustcVmX64.Vm.VerifyKeccak.b60Offset) hp c h ⟨hpc1, hB1⟩
    b60_in_code (by simp [b60]) run_b60 nofun (hB1.mt 0) (by decide) rfl rfl (by vtacJ)
    (by decide) rfl rfl rfl (fun _ _ _ _ _ h ↦ by cases h) rfl
    fun st2 hpc2 hB2 _ hc2 hk2 ↦ ?_
  simp only [PcOk] at hpc2
  rw [alCond] at hpc2
  cases hr : (readScalars 64).run s1 with
  | none =>
    rw [hr] at hal
    have hz : (reg st1.data .rax).toNat % 256 = 0 := hal
    simp only [show (envZ m0 st1.data 3344 3368 (rsOf m0) (vv m0 (Vf V v)) 0).regs .rax =
      reg st1.data .rax from rfl, hz, decide_true, ↓reduceIte] at hpc2
    exact failG hp hpre hB2 hpc2 (by decide) (hfail hr)
  | some p =>
    obtain ⟨sl, s2⟩ := p
    rw [hr] at hal hnext
    have hone : (reg st1.data .rax).toNat % 256 = 1 := hal
    simp only [show (envZ m0 st1.data 3344 3368 (rsOf m0) (vv m0 (Vf V v)) 0).regs .rax =
      reg st1.data .rax from rfl, hone, show ¬(1 = 0) from by decide, decide_false,
      Bool.false_eq_true, ↓reduceIte] at hpc2
    have h64 : sl.size = 64 := NativeRustcVm.Sumcheck.readScalars_size hr
    refine cont st2 sl s2 ⟨hpc2.trans (by rw [NativeRustcVmX64.Vm.VerifyKeccak.b60_next]), hB2⟩ hr
      (Chg.ewsR c hc2 (by decide) rfl (i := 4) (o := 584) (by decide) (by decide) rfl
        (by rw [Array.length_toList, h64]; decide) (hews sl s2 hr))
      (Chg.ts c hc2 (by decide) rfl (by decide) hk2 (hnext _ _ rfl)) ?_
      (NativeRustcVmX64.Transcript.kept_trans hk1 hk2)
    exact Chg.mono c (hc1.trans hc2) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
