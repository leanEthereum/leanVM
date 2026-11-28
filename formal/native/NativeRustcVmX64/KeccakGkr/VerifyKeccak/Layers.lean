module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Copies
public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Exit
public import NativeRustcVmX64.Code.Vm.VerifyKeccak.Names
public import NativeRustcVmX64.Code.Vm.VerifyLayer.Names

/-!
# `verify_keccak`: one layer (x86-64)

`verify_layer`'s footprint (`areas_vl`) and one layer (`layerStep`): a block ending in the call of
`verify_layer` (step `j`, the running claim at frame offset `992`, its bit weights at the
scratch's `weights`), then the check of its AL: on `None` the return with AL `0`, else the next
layer from `tL` with the new claim, the first claim at `1768` and its bit weights at the scratch's
start kept.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea TStateAt tstateBytes)
open NativeRustcVm.KeccakGkr (off ClaimAt WeightsAt)
open LeanVM.Protocol.Verifier (keccakDepth)

public section

/-- `verify_layer`'s check: `test %al, %al`, `je .LVerifyKeccak_31`. -/
abbrev alFail : Exit :=
  .cond (.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)) NativeRustcVmX64.Vm.VerifyKeccak.label_31

/-- **`verify_layer`'s footprint.** -/
theorem areas_vl [Labels] {m0 : MachineData} {a : DecArea} {inst : Array EW} (c : Ctx a inst m0)
    (h : LayZ m0 3344 3368 verifyKeccakStack (rsOf m0)) {mc : MachineData}
    (ca : CallAt m0 wrA 48 mc) :
    Areas mc verifyLayerStack [⟨reg m0 .rdi, 760⟩, ⟨off (fb m0) 992, 768⟩, ⟨reg m0 .r9, 205824⟩]
      [a.region, rcRegion, projectRegion, rhoRegion] := by
  have hN : 3344 - 48 + verifyLayerStack ≤ verifyKeccakStack := by rw [vk_eq]; decide
  have hS := stk_callee c ca hN
  refine areas_of ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
    · exact NativeRustcVm.Transcript.Mapped.keeps (ob_mapped h (i := 1) (by omega) (by omega))
        ca.kept
    · exact mapF h ca (by nd)
    · exact NativeRustcVm.Transcript.Mapped.keeps (ob_mapped h (i := 2) (by omega) (by omega))
        ca.kept
    · exact NativeRustcVm.Transcript.Mapped.keeps c.wM ca.kept
    · exact NativeRustcVm.Transcript.Mapped.keeps c.rcM ca.kept
    · exact NativeRustcVm.Transcript.Mapped.keeps c.pjM ca.kept
    · exact NativeRustcVm.Transcript.Mapped.keeps c.rhM ca.kept
  · intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
    · exact c.tW
    · exact nwF c (by nd)
    · exact c.sW
    · exact c.wW
    · exact c.rcW
    · exact c.pjW
    · exact c.rhW
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true]
    exact ⟨⟨(sepFX c (by nd) c.tS).symm, c.ts⟩, sepFX c (by nd) c.sS⟩
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact sep_stk' hS c.tS
    · exact (sepSF c ca hN (by nd) (by nd) (by nd)).symm
    · exact sep_stk' hS c.sS
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact sep_stk hS c.wS
    · exact sep_stk hS c.rcS
    · exact sep_stk hS c.pjS
    · exact sep_stk hS c.rhS
  · intro w hw r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw hr
    rcases hw with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl
    · exact c.tw
    · exact c.trc
    · exact c.tpj
    · exact c.trh
    · exact sepFX c (by nd) c.wS
    · exact sepFX c (by nd) c.rcS
    · exact sepFX c (by nd) c.pjS
    · exact sepFX c (by nd) c.rhS
    · exact c.sw
    · exact c.src
    · exact c.spj
    · exact c.srh

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

/-- **One layer**: the block `ds` at `p0` (from `T`) ending in `verify_layer`'s call for step
`j`, the check `ds2` (from `tL`). -/
theorem layerStep (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hvl : ∀ s c, Spec (Labels.label NativeRustcVmX64.Vm.VerifyLayer.entryLabel) (VerifyLayerPre a s c)
      (VerifyLayerPost a s c))
    {j : Nat} (hj : j < keccakDepth) {T : SState} {p0 : Nat} {ds ds2 : List Directive}
    (hds : ds.IsInfixAt code p0) (hne : ds ≠ []) {S' : SState}
    (hrun : exec ds T = some (S', .call NativeRustcVmX64.Vm.VerifyLayer.entryLabel)) (hw0 : frameW S' = true)
    (hokS : okL (wsL S') = true) (hmS : missL (wsL S') 992 768 = true)
    (hok1 : okL (wsL S' ++ (0, 48) :: [(992, 768)]) = true)
    (hm1 : missL (wsL S' ++ (0, 48) :: [(992, 768)]) 1768 768 = true)
    (hsp : S'.reg .rsp = some (.ptr 0 48)) (hdi : S'.reg .rdi = some (.var 6))
    (hsi : S'.reg .rsi = some (.var 7)) (hdx : S'.reg .rdx = some (.lit j))
    (hcx : S'.reg .rcx = some (.ptr 0 992)) (hr8 : S'.reg .r8 = some (.var 11))
    {L LW : List (Nat × Sym)} (hL : rlinksOf true S' tL noRsp = some L)
    (hLW : wlinks S' tL.mem = some LW) (hvl1 : varLinks (L ++ LW) = true)
    (hds2 : ds2.IsInfixAt code (p0 + ds.length)) (hne2 : ds2 ≠ []) {S2 : SState}
    (hrun2 : exec ds2 tL = some (S2, alFail)) (hw2 : frameW S2 = true)
    (hok2 : okL (wsL S2) = true) (hm2 : missL (wsL S2) 992 768 = true)
    (hm2' : missL (wsL S2) 1768 768 = true)
    {L2 LW2 : List (Nat × Sym)} (hL2 : rlinks false S2 tL = some L2)
    (hLW2 : wlinks S2 tL.mem = some LW2) (hvl2 : varLinks (L2 ++ LW2) = true)
    {n : Nat} {st : MachineState} {sj : TState} {cj first : KeccakClaimW} {cm : EW}
    (hat : At m0 k p0 wrA T (vv m0 (V2 cm n)) st)
    (hts : TStateAt st.data.dmem (reg m0 .rdi) a sj)
    (hcl : ClaimAt st.data.dmem (off (fb m0) 992) cj)
    (hcw : WeightsAt st.data.dmem (off (reg m0 .r9) 25600) cj)
    (hf : ClaimAt st.data.dmem (off (fb m0) 1768) first)
    (hfw : WeightsAt st.data.dmem (off (reg m0 .r9) 0) first)
    (hfit : SegmentsFit (reg m0 .rsi).toNat cj)
    (hmod : (NativeVm.Model.verifyKeccak (reg m0 .rsi).toNat inst output).run s =
      (afterLayers (reg m0 .rsi).toNat j inst first cm cj).run sj)
    (cont : ∀ st' s' c', At m0 k (p0 + ds.length + ds2.length) wrA tL (vv m0 (V2 cm n)) st' →
      TStateAt st'.data.dmem (reg m0 .rdi) a s' →
      ClaimAt st'.data.dmem (off (fb m0) 992) c' →
      WeightsAt st'.data.dmem (off (reg m0 .r9) 25600) c' →
      ClaimAt st'.data.dmem (off (fb m0) 1768) first →
      WeightsAt st'.data.dmem (off (reg m0 .r9) 0) first →
      c'.point.size = cj.point.size →
      (NativeVm.Model.verifyKeccak (reg m0 .rsi).toNat inst output).run s =
        (afterLayers (reg m0 .rsi).toNat (j + 1) inst first cm c').run s' →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) st') :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  have hrc : RcAt m0 verifyKeccakStack := hpre.2.2.1
  have hpj : ProjectAt m0 := hpre.2.2.2.1
  have hrh : RhoAt m0 := hpre.2.2.2.2.1
  have hN : 3344 - 48 + verifyLayerStack ≤ verifyKeccakStack := by rw [vk_eq]; decide
  have hj' : j < 2 ^ 64 := by have : keccakDepth = 12 := rfl; omega
  have hdxN : ∀ (mc : MachineData) env, reg mc .rdx = (Sym.lit j).eval env →
      (reg mc .rdx).toNat = j := by
    intro mc env e
    rw [e]
    show (BitVec.ofNat 64 j).toNat = j
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj']
  refine stepC (T' := tL) (vals' := vv m0 (V2 cm n)) hp c h hat hds hne hrun hat.2.mt hw0
    (oc := 48) (by decide) hsp (hvl sj cj) (Sk := verifyLayerStack) hN
    (fun mc hmc hk hsk hso hrsp hch hkk ↦ ?_) (Lc := [(992, 768)])
    (Oc := [(1, 0, 760), (2, 25600, 114688)]) (fun mc m' hmc hq ↦ ?_) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl hL hLW (fun _ ↦ varLinks_eval hvl1 _)
    (fun i hi ↦ nomatch tregE (rfl : tL.reg .rax = some (.reg .rax)) hi)
    (fun i hi ↦ nomatch tregE (rfl : tL.reg .rdx = some (.reg .rdx)) hi) rfl rfl rfl
    (fun _ _ _ _ _ h ↦ by cases h) rfl fun st1 hpc1 hB1 ⟨mc, hmc, hrsp, hq, hch⟩ hc1 hk1 ↦ ?_
  · -- `verify_layer`'s precondition.
    have ca : CallAt m0 wrA 48 mc := ⟨hrsp, by decide, hk, hso⟩
    have rdi : reg mc .rdi = reg m0 .rdi := hmc.regs .rdi _ hdi
    have rsi : reg mc .rsi = reg m0 .rsi := hmc.regs .rsi _ hsi
    have rdx := hdxN mc _ (hmc.regs .rdx _ hdx)
    have rcx : reg mc .rcx = off (fb m0) 992 := (hmc.regs .rcx _ hcx).trans (ev_frame 992)
    have r8 : reg mc .r8 = reg m0 .r9 := hmc.regs .r8 _ hr8
    unfold VerifyLayerPre
    dsimp only
    rw [rdi, rsi, rdx, rcx, r8]
    refine ⟨hsk, ca.rc c hrc hN, ca.pj c hpj, ca.rh c hrh,
      Chg.ts c hch hokS (by decide) (by decide) hkk hts,
      Chg.claimF c hch hokS (by decide) hmS (by decide) hcl,
      Chg.wtsR c hch hokS (by decide) (by decide) (by decide) hcw, hj, hfit, areas_vl c h ca, ?_⟩
    apply ca.got c hN
    simp only [NativeRustcVm.Transcript.DecArea.region, tstateBytes, NativeRustcVm.KeccakGkr.claimBytes, NativeRustcVm.KeccakGkr.scratchBytes]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (refine ⟨_, ?_, le_rfl, le_rfl⟩; solve | simp)
      | (refine ⟨(stackBelow m0 verifyKeccakStack, verifyKeccakStack + 8), by simp, ?_, ?_⟩ <;>
          rw [c.K, h.addr (by decide)] <;> have := c.sp <;> rw [vk_eq] at * <;> omega)
  · -- Its changes.
    have rdi : reg mc .rdi = off (ob m0 1) 0 := (hmc.regs .rdi _ hdi).trans (off0 _).symm
    have rcx : reg mc .rcx = off (fb m0) 992 := (hmc.regs .rcx _ hcx).trans (ev_frame 992)
    have r8 : reg mc .r8 = reg m0 .r9 := hmc.regs .r8 _ hr8
    obtain ⟨-, -, hso, hsv⟩ := hq
    refine chgQ hso (fun q ⟨r, hr, hq⟩ ↦ ?_) hsv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact .inl hq
    · exact .inr (inR_reg rdi List.mem_cons_self hq)
    · exact .inr (inR_frame rcx List.mem_cons_self hq)
    · exact .inr (inR_reg (i := 2) (o := 25600) (n := 114688) (by rw [r8]; rfl)
        (List.mem_cons_of_mem _ List.mem_cons_self) hq)
  -- The check.
  have rdi : reg mc .rdi = reg m0 .rdi := hmc.regs .rdi _ hdi
  have rsi : reg mc .rsi = reg m0 .rsi := hmc.regs .rsi _ hsi
  have rdx := hdxN mc _ (hmc.regs .rdx _ hdx)
  have rcx : reg mc .rcx = off (fb m0) 992 := (hmc.regs .rcx _ hcx).trans (ev_frame 992)
  have r8 : reg mc .r8 = reg m0 .r9 := hmc.regs .r8 _ hr8
  obtain ⟨hok, hnext, -, -⟩ := hq
  rw [rsi, rdx] at hok hnext
  rw [rdi, rcx, r8] at hnext
  refine stepJ (T' := tL) (vals' := vv m0 (V2 cm n)) (o := p0 + ds.length) hp c h ⟨hpc1, hB1⟩
    hds2 hne2 hrun2 nofun (hB1.mt 0) hw2 hL2 hLW2 (varLinks_eval hvl2 _) (by decide) rfl rfl rfl
    (fun _ _ _ _ _ h ↦ by cases h) rfl fun st2 hpc2 hB2 _ hc2 hk2 ↦ ?_
  simp only [PcOk] at hpc2
  cases hr : (verifyKeccakLayer (reg m0 .rsi).toNat j cj).run sj with
  | none =>
    rw [hr] at hok
    have hal : boolRet st1.data = 0 := hok
    unfold boolRet at hal
    have hce : (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)).eval
        (envZ m0 st1.data 3344 3368 (rsOf m0) (vv m0 (V2 cm n)) 0) = true := by
      rw [alCond]; exact decide_eq_true hal
    simp only [hce, ↓reduceIte] at hpc2
    exact failG hp hpre hB2 hpc2 (by decide) (by rw [hmod]; exact afterLayers_none hj hr)
  | some p =>
    obtain ⟨c', s'⟩ := p
    rw [hr] at hok hnext
    have hal : boolRet st1.data = 1 := hok
    unfold boolRet at hal
    have hce : (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)).eval
        (envZ m0 st1.data 3344 3368 (rsOf m0) (vv m0 (V2 cm n)) 0) = false := by
      rw [alCond]; exact decide_eq_false fun h ↦ absurd (hal.symm.trans h) (by decide)
    simp only [hce, Bool.false_eq_true, ↓reduceIte] at hpc2
    obtain ⟨hts', hcl', hcw'⟩ := hnext c' s' rfl
    exact cont st2 s' c' ⟨hpc2, hB2⟩ (Chg.ts c hc2 hok2 (by decide) (by decide) hk2 hts')
      (Chg.claimF c hc2 hok2 (by decide) hm2 (by decide) hcl')
      (Chg.wtsR c hc2 hok2 (by decide) (by decide) (by decide) hcw')
      (Chg.claimF c hc2 hok2 (by decide) hm2' (by decide)
        (Chg.claimF c hc1 hok1 (by decide) hm1 (by decide) hf))
      (Chg.wtsR c hc2 hok2 (by decide) (by decide) (by decide)
        (Chg.wtsR c hc1 hok1 (by decide) (by decide) (by decide) hfw))
      (layer_point_size hr) (hmod.trans (afterLayers_some hj hr))

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak
