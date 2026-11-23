module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.FrontA
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmX64.Code.Vm.TStateSampleChallenges.Names

/-!
# `verify_keccak`: the samples and the committed value (x86-64)

`b3` and `sample_challenges` (the segment, one element at frame offset `152`), `b4` and
`sample_challenges` (the lane point, five at `328`), `b5` and `read_scalar` (the committed
outputs' value, the `Option<EW>` at `992`), `b6` (its check: on `None` the return with AL `0`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea TStateAt OptEWAt tstateBytes)
open NativeRustcVm.KeccakGkr (off)

public section

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

/-- **A sample** of `n` challenges into the frame at `o`, from `t2` to `t2`. -/
theorem sampleStep (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hsc : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    {ds : List Directive} {p0 n o : Nat} (hds : ds.IsInfixAt code p0) (hne : ds ≠ [])
    {S' : SState} (hrun : exec ds t2 = some (S', .call NativeRustcVmX64.Vm.TStateSampleChallenges.entryLabel))
    (hw0 : frameW S' = true) (hokS : okL (wsL S') = true) (hsp : S'.reg .rsp = some (.ptr 0 48))
    (hdi : S'.reg .rdi = some (.var 6)) (hsi : S'.reg .rsi = some (.ptr 0 (o : Int)))
    (hdx : S'.reg .rdx = some (.lit n)) (hn : n < 2 ^ 64) (ho : 56 ≤ o) (hon : o + 16 * n ≤ 3344)
    (htm : tplMiss 48 [(o, 16 * n)] t2 = true)
    {L LW : List (Nat × Sym)} (hL : rlinksOf true S' t2 noRsp = some L)
    (hLW : wlinks S' t2.mem = some LW) (hvl : varLinks (L ++ LW) = true)
    {st : MachineState} {s1 : TState} (hat : At m0 k p0 wrA t2 (vv m0 {}) st)
    (hts : TStateAt st.data.dmem (reg m0 .rdi) a s1) {R : MachineState → Prop}
    (cont : ∀ st' xs s2, At m0 k (p0 + ds.length) wrA t2 (vv m0 {}) st' →
      (sampleChallenges n).run s1 = some (xs, s2) →
      NativeRustcVm.EWsAt st'.data.dmem (off (fb m0) o) xs.toList →
      TStateAt st'.data.dmem (reg m0 .rdi) a s2 →
      Chg m0 st.data.dmem st'.data.dmem (wsL S' ++ (0, 48) :: [(o, 16 * n)]) [(1, 0, 760)] →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  have hrc : RcAt m0 verifyKeccakStack := hpre.2.2.1
  have hdxN : ∀ mc : MachineData, reg mc .rdx = (Sym.lit n).eval
      (envZ m0 st.data 3344 3368 (rsOf m0) (vv m0 {})
        (Host.addrOf (k + (p0 + ds.length))).toBitVec) → (reg mc .rdx).toNat = n := by
    intro mc e
    rw [e]
    show (BitVec.ofNat 64 n).toNat = n
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  refine stepC (T' := t2) (vals' := vv m0 {}) hp c h hat hds hne hrun hat.2.mt hw0 (oc := 48)
    (by decide) hsp (hsc s1) (Sk := sampleChallengesStack) (by rw [vk_eq]; decide)
    (fun mc hmc hk hsk hso hrsp hch hkk ↦ ?_) (Lc := [(o, 16 * n)]) (Oc := [(1, 0, 760)])
    (fun mc m' hmc hq ↦ ?_) (by simp [okL]; omega) (by decide) (by decide) htm (by decide) rfl hL
    hLW (fun _ ↦ varLinks_eval hvl _)
    (fun i hi ↦ nomatch tregE (rfl : t2.reg .rax = some (.reg .rax)) hi)
    (fun i hi ↦ nomatch tregE (rfl : t2.reg .rdx = some (.reg .rdx)) hi) rfl rfl rfl
    (fun _ _ _ _ _ h ↦ by cases h) rfl fun st' hpc' hB' ⟨mc, hmc, hrsp, hq, _⟩ hchg hk' ↦ ?_
  · have ca : CallAt m0 wrA 48 mc := ⟨hrsp, by decide, hk, hso⟩
    have rdi : reg mc .rdi = reg m0 .rdi := hmc.regs .rdi _ hdi
    have rsi : reg mc .rsi = off (fb m0) o := (hmc.regs .rsi _ hsi).trans (ev_frame o)
    have rdx := hdxN mc (hmc.regs .rdx _ hdx)
    unfold SampleChallengesPre
    dsimp only
    rw [rdi, rsi, rdx]
    refine ⟨hsk, ca.rc c hrc (by rw [vk_eq]; decide),
      Chg.ts c hch hokS (by decide) (by decide) hkk hts, ca.tok c (by rw [vk_eq]; decide),
      ca.outF c h (by rw [vk_eq]; decide) ho hon, ?_⟩
    apply ca.got c (by rw [vk_eq]; decide)
    simp only [NativeRustcVm.Transcript.DecArea.region, tstateBytes]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨(reg m0 .rdi, 760), by simp, le_rfl, le_rfl⟩
    · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
    · refine ⟨(stackBelow m0 verifyKeccakStack, verifyKeccakStack + 8), by simp, ?_, ?_⟩
      all_goals
        rw [c.K, h.addr (by omega)]
        have := c.sp
        rw [vk_eq] at *
        omega
    · exact ⟨(rcAddr, 192), by simp, le_rfl, le_rfl⟩
  · have rdi : reg mc .rdi = off (ob m0 1) 0 := (hmc.regs .rdi _ hdi).trans (off0 _).symm
    have rsi : reg mc .rsi = off (fb m0) o := (hmc.regs .rsi _ hsi).trans (ev_frame o)
    have rdx := hdxN mc (hmc.regs .rdx _ hdx)
    obtain ⟨-, hso, hsv⟩ := hq
    rw [rdx] at hso
    exact chgQ hso (fun q h ↦ h.elim (fun h ↦ .inr (inR_frame rsi List.mem_cons_self h))
      fun h ↦ h.elim (fun h ↦ .inr (inR_reg rdi List.mem_cons_self h)) .inl) hsv
  · have rdi : reg mc .rdi = reg m0 .rdi := hmc.regs .rdi _ hdi
    have rsi : reg mc .rsi = off (fb m0) o := (hmc.regs .rsi _ hsi).trans (ev_frame o)
    have rdx := hdxN mc (hmc.regs .rdx _ hdx)
    obtain ⟨⟨xs, s2, hr, hxs, hts2⟩, -, -⟩ := hq
    rw [rdx] at hr
    rw [rsi] at hxs
    rw [rdi] at hts2
    exact cont st' xs s2 ⟨hpc', hB'⟩ hr hxs hts2 hchg

/-- **The samples and the committed value**: at `b7` (`t2`). -/
theorem frontB (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hsc : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    {st : MachineState} {s1 : TState} (hat : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b3Offset wrA t2 (vv m0 {}) st)
    (hts : TStateAt st.data.dmem (reg m0 .rdi) a s1)
    (hrun : (NativeVm.Model.verifyKeccak (reg m0 .rsi).toNat inst output).run s =
      (afterGrind (reg m0 .rsi).toNat inst output).run s1)
    (cont : ∀ st' s4 (seg lp : Array EW) (cm : EW), At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b7Offset wrA t2 (vv m0 {}) st' →
      TStateAt st'.data.dmem (reg m0 .rdi) a s4 →
      seg.size = 1 → NativeRustcVm.EWsAt st'.data.dmem (off (fb m0) 152) seg.toList →
      lp.size = 5 → NativeRustcVm.EWsAt st'.data.dmem (off (fb m0) 328) lp.toList →
      NativeRustcVm.EWAt st'.data.dmem (off (fb m0) 1000) cm →
      (NativeVm.Model.verifyKeccak (reg m0 .rsi).toNat inst output).run s =
        (afterLayers (reg m0 .rsi).toNat 0 inst (keccakFirstClaim inst seg lp output cm) cm
          (keccakFirstClaim inst seg lp output cm)).run s4 →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) st') :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  have hrc : RcAt m0 verifyKeccakStack := hpre.2.2.1
  -- `b3`: the segment.
  refine sampleStep (n := 1) (o := 152) hp hpre hsc b3_in_code (by simp [b3]) run_b3 (by decide)
    (by decide) rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide) hat hts
    fun st4 seg s2 hat4 hr2 hseg hts2 hc4 ↦ ?_
  have hsz1 : seg.size = 1 := Bus.Gkr.sampleChallenges_size hr2
  -- `b4`: the lane point.
  refine sampleStep (n := 5) (o := 328) hp hpre hsc b4_in_code (by simp [b4]) run_b4 (by decide)
    (by decide) rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide) hat4 hts2
    fun st5 lp s3 hat5 hr3 hlp hts3 hc5 ↦ ?_
  have hsz5 : lp.size = 5 := Bus.Gkr.sampleChallenges_size hr3
  -- `b5`: the committed value.
  refine stepC (hwfS := fun _ ↦ h.wf hat5.2.kept)
    (T' := t2) (vals' := vv m0 {}) hp c h hat5 b5_in_code (by simp [b5]) run_b5
    hat5.2.mt (by decide) (oc := 48) (by decide) rfl (hrs s3) (Sk := readScalarStack)
    (by rw [vk_eq]; decide) (fun mc hmc hk hsk hso hrsp hch hkk ↦ ?_) (Lc := [(992, 24)])
    (Oc := [(1, 0, 760)]) (fun mc m' hmc hq ↦ ?_) (by decide) (by decide) (by decide) (by decide)
    (by decide) rfl rfl rfl (by vtacC)
    (fun i hi ↦ nomatch tregE (rfl : t2.reg .rax = some (.reg .rax)) hi)
    (fun i hi ↦ nomatch tregE (rfl : t2.reg .rdx = some (.reg .rdx)) hi) rfl rfl rfl
    (fun _ _ _ _ _ h ↦ by cases h) rfl fun st6 hpc6 hB6 ⟨mc, hmc, hrsp, hq, _⟩ hc6 hk6 ↦ ?_
  · have ca : CallAt m0 wrA 48 mc := ⟨hrsp, by decide, hk, hso⟩
    have rsi : reg mc .rsi = reg m0 .rdi := hmc.regs .rsi _ rfl
    have rdi : reg mc .rdi = off (fb m0) 992 := (hmc.regs .rdi _ rfl).trans (ev_frame 992)
    unfold ReadScalarPre
    dsimp only
    rw [rdi, rsi]
    refine ⟨hsk, ca.rc c hrc (by rw [vk_eq]; decide),
      Chg.ts c hch (by decide) (by decide) (by decide) hkk hts3, ca.tok c (by rw [vk_eq]; decide),
      ca.outF c h (by rw [vk_eq]; decide) (by decide) (by decide), ?_⟩
    apply ca.got c (by rw [vk_eq]; decide)
    simp only [NativeRustcVm.Transcript.DecArea.region, tstateBytes]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨(reg m0 .rdi, 760), by simp, le_rfl, le_rfl⟩
    · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
    · refine ⟨(stackBelow m0 verifyKeccakStack, verifyKeccakStack + 8), by simp, ?_, ?_⟩
      all_goals
        rw [c.K, h.addr (by decide)]
        have := c.sp
        rw [vk_eq] at *
        omega
    · exact ⟨(rcAddr, 192), by simp, le_rfl, le_rfl⟩
  · have rsi : reg mc .rsi = off (ob m0 1) 0 := (hmc.regs .rsi _ rfl).trans (off0 _).symm
    have rdi : reg mc .rdi = off (fb m0) 992 := (hmc.regs .rdi _ rfl).trans (ev_frame 992)
    obtain ⟨-, -, hso, hsv⟩ := hq
    exact chgQ hso (fun q h ↦ h.elim (fun h ↦ .inr (inR_frame rdi List.mem_cons_self h))
      fun h ↦ h.elim (fun h ↦ .inr (inR_reg rsi List.mem_cons_self h)) .inl) hsv
  have rsi : reg mc .rsi = reg m0 .rdi := hmc.regs .rsi _ rfl
  have rdi : reg mc .rdi = off (fb m0) 992 := (hmc.regs .rdi _ rfl).trans (ev_frame 992)
  obtain ⟨hopt, hnext, -, -⟩ := hq
  rw [rdi] at hopt
  rw [rsi] at hnext
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b4_next, NativeRustcVmX64.Vm.VerifyKeccak.b5_next] at hpc6
  -- `b6`: the value's check.
  refine stepJ (T' := t2) (vals' := vv m0 {}) (o := NativeRustcVmX64.Vm.VerifyKeccak.b6Offset) hp c h ⟨hpc6, hB6⟩ b6_in_code
    (by simp [b6]) run_b6 nofun (hB6.mt 0) (by decide) rfl rfl (by vtacJ) (by decide) rfl rfl rfl
    (fun _ _ _ _ _ h ↦ by cases h) rfl fun st7 hpc7 hB7 _ hc7 hk7 ↦ ?_
  simp only [PcOk] at hpc7
  have hrun2 := hrun.trans (afterGrind_run hr2)
  rw [afterSeg_run hr3] at hrun2
  cases hr : readScalar.run s3 with
  | none =>
    rw [hr] at hopt
    have hw : NativeRustcVm.WordAt st6.data.dmem (off (fb m0) 992) 0 := hopt
    rw [tag32 (env := envZ m0 st6.data 3344 3368 (rsOf m0) (vv m0 {}) 0) (Or.inl rfl) hw] at hpc7
    exact failG hp hpre hB7 hpc7 (by decide) (by rw [hrun2]; exact afterLane_none hr)
  | some p =>
    obtain ⟨cm, s4⟩ := p
    rw [hr] at hopt hnext
    obtain ⟨htag, hcm⟩ := hopt
    rw [tag32 (env := envZ m0 st6.data 3344 3368 (rsOf m0) (vv m0 {}) 0) (Or.inr rfl) htag] at hpc7
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hpc7
    have hcm' : NativeRustcVm.EWAt st6.data.dmem (off (fb m0) 1000) cm := by
      rwa [NativeRustcVm.Transcript.off_off] at hcm
    have hc := (hc4.trans hc5).trans (hc6.trans hc7)
    have hc' := hc5.trans (hc6.trans hc7)
    refine cont st7 s4 seg lp cm ⟨hpc7.trans (by rw [NativeRustcVmX64.Vm.VerifyKeccak.b6_next]), hB7⟩
      (Chg.ts c hc7 (by decide) (by decide) (by decide) hk7 (hnext cm s4 rfl)) hsz1
      (Chg.ewsF c hc' (by decide) (by decide) (by rw [Array.length_toList, hsz1]; decide)
        (by rw [Array.length_toList, hsz1]; decide) hseg)
      hsz5
      (Chg.ewsF c (hc6.trans hc7) (by decide) (by decide)
        (by rw [Array.length_toList, hsz5]; decide) (by rw [Array.length_toList, hsz5]; decide) hlp)
      (NativeRustcVm.Layout.EWAt.of_same hcm' (Chg.frame c hc7 (by decide) (by decide)
        (o := 1000) (n := 16) (by decide) (by decide)) le_rfl)
      (by rw [hrun2]; exact afterLane_run hr)

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak
