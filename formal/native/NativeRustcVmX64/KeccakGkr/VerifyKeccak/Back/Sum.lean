module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.Push
public import NativeRustcVmX64.Spec.Sumcheck
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain.Names

/-!
# The instance sumcheck

Blocks 55–56 run the four-round plain sumcheck and handle its option tag.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea TStateAt tstateBytes)
open NativeRustcVm.KeccakGkr (off ClaimAt)

public section

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

theorem sumStep (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hsum : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s))
    {st : MachineState} {V : Vs} {s1 : TState} {cl : KeccakClaimW} {outs : Array ColumnClaimW}
    (hat : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b55Offset wrB t52 (vv m0 V) st)
    (hcl : ClaimAt st.data.dmem (off (fb m0) 992) cl)
    (hts : TStateAt st.data.dmem (reg m0 .rdi) a s1)
    (hmod : (NativeVm.Model.verifyKeccak (reg m0 .rsi).toNat inst output).run s =
      (restSum (reg m0 .rsi).toNat cl outs).run s1)
    (cont : ∀ st' low v s2, At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b57Offset wrB t57 (vv m0 V) st' →
      (sumcheckPlain cl.value 3 4).run s1 = some ((low, v), s2) →
      NativeRustcVm.EWAt st'.data.dmem (off (fb m0) 104) v →
      NativeRustcVm.EWsAt st'.data.dmem (off (fb m0) 168) low.toList →
      TStateAt st'.data.dmem (reg m0 .rdi) a s2 →
      Chg m0 st.data.dmem st'.data.dmem [(0, 232), (3296, 48)] [(1, 0, 760)] →
      Kept st.data.dmem st'.data.dmem →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) st') :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  have hrc : RcAt m0 verifyKeccakStack := hpre.2.2.1
  have hl := fun ret ↦ ld_ew (rs := rsOf m0) (vals := vv m0 V) (ret := ret) hcl.1
  refine stepC (T' := t56) (vals' := vv m0 V) hp c h hat b55_in_code (by simp [b55])
    run_b55 hat.2.mt (by decide) (oc := 32) (by decide) rfl (hsum s1)
    (Sk := sumcheckPlainStack) (by rw [vk_eq]; decide)
    (fun mc hmc hk hsk hso hrsp hch hkk ↦ ?_) (Lc := [(96, 24), (168, 64)])
    (Oc := [(1, 0, 760)]) (fun mc m' hmc hq ↦ ?_) (by decide) (by decide) (by decide)
    (by decide) (by decide) rfl rfl rfl (by vtacC)
    (fun i hi ↦ nomatch tregE (rfl : t56.reg .rax = some (.reg .rax)) hi)
    (fun i hi ↦ nomatch tregE (rfl : t56.reg .rdx = some (.reg .rdx)) hi)
    rfl rfl rfl (fun _ _ _ _ _ h ↦ by cases h) rfl
    fun st1 hpc1 hB1 ⟨mc, hmc, hrsp, hq, hch⟩ hc1 hk1 ↦ ?_
  · have ca : CallAt m0 wrB 32 mc := ⟨hrsp, by decide, hk, hso⟩
    have rdi : reg mc .rdi = off (fb m0) 96 := (hmc.regs .rdi _ rfl).trans (ev_frame 96)
    have rsi : reg mc .rsi = reg m0 .rdi := hmc.regs .rsi _ rfl
    have r9 : reg mc .r9 = off (fb m0) 168 := (hmc.regs .r9 _ rfl).trans (ev_frame 168)
    have r8 : reg mc .r8 = 3#64 := hmc.regs .r8 _ rfl
    have arg : stackArg mc 0 = 4#64 :=
      stackArg_of hmc rfl rfl (by decide) (i := 0) (v := .lit 4) (by decide) (by decide)
    unfold SumcheckPlainPre SumcheckOk
    rw [rdi, rsi, r9, r8, arg]
    refine ⟨argsOk c h ca (by decide), hsk, ca.rc c hrc (by rw [vk_eq]; decide),
      Chg.ts c hch (by decide) rfl (by decide) hkk hts,
      ca.tok c (by rw [vk_eq]; decide), by decide, by decide,
      ca.outF c h (by rw [vk_eq]; decide) (by decide) (by decide),
      ca.outF c h (by rw [vk_eq]; decide) (by decide) (by decide),
      sepF0 c (by decide) (by decide) (by decide), ?_⟩
    apply ca.got c (by rw [vk_eq]; decide)
    simp only [NativeRustcVm.Transcript.DecArea.region, tstateBytes, show (4#64).toNat = 4 from rfl]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact ⟨(reg m0 .rdi, 760), by simp, le_rfl, le_rfl⟩
    · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
    · refine ⟨(stackBelow m0 verifyKeccakStack, verifyKeccakStack + 8), by simp, ?_, ?_⟩
      all_goals
        dsimp only [Prod.fst, Prod.snd]
        rw [c.K, h.addr (by decide)]
        have := c.sp
        rw [vk_eq] at *
        omega
    · refine ⟨(stackBelow m0 verifyKeccakStack, verifyKeccakStack + 8), by simp, ?_, ?_⟩
      all_goals
        dsimp only [Prod.fst, Prod.snd]
        rw [c.K, h.addr (by decide)]
        have := c.sp
        rw [vk_eq] at *
        omega
    · exact ⟨(rcAddr, 192), by simp, le_rfl, le_rfl⟩
  · have rdi : reg mc .rdi = off (fb m0) 96 := (hmc.regs .rdi _ rfl).trans (ev_frame 96)
    have rsi : reg mc .rsi = off (ob m0 1) 0 := (hmc.regs .rsi _ rfl).trans (off0 _).symm
    have r9 : reg mc .r9 = off (fb m0) 168 := (hmc.regs .r9 _ rfl).trans (ev_frame 168)
    have arg : stackArg mc 0 = 4#64 :=
      stackArg_of hmc rfl rfl (by decide) (i := 0) (v := .lit 4) (by decide) (by decide)
    obtain ⟨-, hso, hsv⟩ := hq
    rw [arg] at hso
    exact chgQ hso (fun q h ↦ h.elim
      (fun h ↦ .inr (inR_frame rdi List.mem_cons_self h)) fun h ↦ h.elim
      (fun h ↦ .inr (inR_frame r9 (by decide) h)) fun h ↦ h.elim
      (fun h ↦ .inr (inR_reg rsi List.mem_cons_self h)) .inl) hsv
  have rdi : reg mc .rdi = off (fb m0) 96 := (hmc.regs .rdi _ rfl).trans (ev_frame 96)
  have rsi : reg mc .rsi = reg m0 .rdi := hmc.regs .rsi _ rfl
  have r9 : reg mc .r9 = off (fb m0) 168 := (hmc.regs .r9 _ rfl).trans (ev_frame 168)
  have r8 : reg mc .r8 = 3#64 := hmc.regs .r8 _ rfl
  have arg : stackArg mc 0 = 4#64 :=
    stackArg_of hmc rfl rfl (by decide) (i := 0) (v := .lit 4) (by decide) (by decide)
  have hc : claimArg mc = cl.value := by
    have rdx : reg mc .rdx = cl.value.c0.toBitVec := (hmc.regs .rdx _ rfl).trans (hl _).1
    have rcx : reg mc .rcx = cl.value.c1.toBitVec := (hmc.regs .rcx _ rfl).trans (hl _).2
    unfold claimArg
    rw [rdx, rcx]
  obtain ⟨hout, -, -⟩ := hq
  change SumcheckOut st1.data.dmem (reg mc .rsi) a (reg mc .rdi) (reg mc .r9)
    ((sumcheckPlain (claimArg mc) (reg mc .r8).toNat (stackArg mc 0).toNat).run s1) at hout
  rw [rdi, rsi, r9, hc, r8, arg] at hout
  simp only [show (3#64).toNat = 3 from rfl, show (4#64).toNat = 4 from rfl] at hout
  generalize hr : (sumcheckPlain cl.value 3 4).run s1 = res at hout
  obtain ⟨hopt, hlow, hnext⟩ := hout
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b55_next] at hpc1
  refine stepJ (T' := t57) (vals' := vv m0 V) (o := NativeRustcVmX64.Vm.VerifyKeccak.b56Offset) hp c h ⟨hpc1, hB1⟩ b56_in_code
    (by simp [b56]) run_b56 nofun (hB1.mt 0) (by decide) rfl rfl (by vtacJ)
    (by decide) rfl rfl rfl (fun _ _ _ _ _ h ↦ by cases h) rfl
    fun st2 hpc2 hB2 _ hc2 hk2 ↦ ?_
  simp only [PcOk] at hpc2
  cases res with
  | none =>
    rw [tag32 (env := envZ m0 st1.data 3344 3368 (rsOf m0) (vv m0 V) 0)
      (Or.inl rfl) hopt] at hpc2
    exact failG hp hpre hB2 hpc2 (by decide) (hmod.trans (restSum_none hr))
  | some p =>
    obtain ⟨⟨low, v⟩, s2⟩ := p
    obtain ⟨htag, hv⟩ := hopt
    rw [tag32 (env := envZ m0 st1.data 3344 3368 (rsOf m0) (vv m0 V) 0)
      (Or.inr rfl) htag] at hpc2
    simp only [show ((1 : UInt64) != 1) = false from rfl, Bool.false_eq_true, ↓reduceIte] at hpc2
    rw [toff, show 96 + 8 = 104 from rfl] at hv
    have hlow4 : low.size = 4 := by
      have hr' := hr
      rw [← NativeRustcVm.Sumcheck.sumcheckFn_none] at hr'
      exact Bus.Gkr.sumcheckFn_size _ _ _ _ hr'
    refine cont st2 low v s2 ⟨hpc2.trans (by rw [NativeRustcVmX64.Vm.VerifyKeccak.b56_next]), hB2⟩ hr
      (NativeRustcVm.Layout.EWAt.of_same hv
        (Chg.frame c hc2 (by decide) rfl (by decide) (by decide)) le_rfl)
      (Chg.ewsF c hc2 (by decide) rfl (by rw [Array.length_toList, hlow4]; decide)
        (by rw [Array.length_toList, hlow4]; decide) (hlow low v s2 rfl))
      (Chg.ts c hc2 (by decide) rfl (by decide) hk2 (hnext _ _ rfl)) ?_
      (NativeRustcVmX64.Transcript.kept_trans hk1 hk2)
    exact Chg.mono c (hc1.trans hc2) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
