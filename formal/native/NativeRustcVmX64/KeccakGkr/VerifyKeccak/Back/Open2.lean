module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.Sum
public import NativeRustcVmX64.Code.Vm.KeccakOpen.Names

/-!
# The opening of the input segments

Blocks 57–58 open both input segments and retain the last claim's point slice.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea TStateAt tstateBytes)
open NativeRustcVm.KeccakGkr (off ClaimAt WeightsAt)

public section

@[expose] def Vp (m0 : MachineData) (V : Vs) (cl : KeccakClaimW) : Vs :=
  { V with pl := BitVec.ofNat 64 cl.point.size, pp := off (fb m0) 1280 }

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

/-- The second opening's GOT footprint without symbolic execution state. -/
private theorem open2_got (c : Ctx a inst m0) {mc : MachineData}
    (ca : CallAt m0 wrB 0 mc) {n : Nat} (hn : n ≤ 30) :
    GotAt mc keccakOpenStack
      [(off (fb m0) 96, 24), (reg m0 .rdi, tstateBytes),
        (off (fb m0) 232, 96), (off (reg m0 .r9) 140288, NativeRustcVm.KeccakGkr.rowsBytes),
        (a.region.addr, a.region.size), (off (fb m0) 1280, 16 * n),
        (off (reg m0 .r9) 25600, NativeRustcVm.KeccakGkr.weightsBytes),
        (rcAddr, 192), (rspOf mc + 8#64, 48)] ["memcpy"] := by
  rw [args_eq ca]
  apply ca.got c ko_le
  simp only [List.forall_mem_cons]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨(stackBelow m0 verifyKeccakStack, verifyKeccakStack + 8), by simp,
      open_frame_cover c (by decide) (by decide)⟩
  · exact ⟨(reg m0 .rdi, 760), by simp, le_rfl, le_rfl⟩
  · exact ⟨(stackBelow m0 verifyKeccakStack, verifyKeccakStack + 8), by simp,
      open_frame_cover c (by decide) (by decide)⟩
  · exact ⟨(reg m0 .r9, 205824), by simp,
      open_scratch_cover c (by decide) (by decide)⟩
  · exact ⟨(a.region.addr, a.region.size), by simp, le_rfl, le_rfl⟩
  · exact ⟨(stackBelow m0 verifyKeccakStack, verifyKeccakStack + 8), by simp,
      open_frame_cover c (by decide) (by omega)⟩
  · exact ⟨(reg m0 .r9, 205824), by simp,
      open_scratch_cover c (by decide) (by decide)⟩
  · exact ⟨(rcAddr, 192), by simp, le_rfl, le_rfl⟩
  · exact ⟨(stackBelow m0 verifyKeccakStack, verifyKeccakStack + 8), by simp,
      open_frame_cover c (by decide) (by decide)⟩
  · intro p hp
    exact (List.not_mem_nil hp).elim

theorem open2Step (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hko : ∀ s c, Spec (Labels.label NativeRustcVmX64.Vm.KeccakOpen.entryLabel) (KeccakOpenPre a s c)
      (KeccakOpenPost a s c))
    {st : MachineState} {V : Vs} {s1 : TState} {cl : KeccakClaimW} {v : EW}
    (hat : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b57Offset wrB t57 (vv m0 V) st)
    (hcl : ClaimAt st.data.dmem (off (fb m0) 992) cl)
    (hcw : WeightsAt st.data.dmem (off (reg m0 .r9) 25600) cl)
    (hv : NativeRustcVm.EWAt st.data.dmem (off (fb m0) 104) v)
    (hts : TStateAt st.data.dmem (reg m0 .rdi) a s1)
    (hfit : SegmentsFit (reg m0 .rsi).toNat cl)
    (hfail : (keccakOpen (reg m0 .rsi).toNat cl 0 2 v).run s1 = none →
      (NativeVm.Model.verifyKeccak (reg m0 .rsi).toNat inst output).run s = none)
    (cont : ∀ st' slot ws v2 s2, At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b59Offset wrB t59 (vv m0 (Vp m0 V cl)) st' →
      (keccakOpen (reg m0 .rsi).toNat cl 0 2 v).run s1 = some ((slot, ws, v2), s2) →
      NativeRustcVm.EWAt st'.data.dmem (off (fb m0) 104) v2 →
      NativeRustcVm.EWsAt st'.data.dmem (off (fb m0) 232) slot.toList →
      NativeRustcVm.EWsAt st'.data.dmem (off (reg m0 .r9) 140288) ws.toList →
      TStateAt st'.data.dmem (reg m0 .rdi) a s2 →
      Chg m0 st.data.dmem st'.data.dmem [(0, 120), (232, 96), (3296, 48)]
        [(1, 0, 760), (2, 140288, 65536)] →
      Kept st.data.dmem st'.data.dmem →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) st') :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  have hrc : RcAt m0 verifyKeccakStack := hpre.2.2.1
  obtain ⟨hsz, hw, hpt⟩ := ClaimAt.pointAt hcl
  rw [koff] at hw hpt
  have hl := fun ret ↦ ld_frame (rs := rsOf m0) (vals := vv m0 V) (ret := ret) hw
  have h31 : ∀ ret, ((Sym.load 0 1272 8).eval
      (envZ m0 st.data 3344 3368 (rsOf m0) (vv m0 V) ret)).toNat < 31 := by
    intro ret
    change ((envZ m0 st.data 3344 3368 (rsOf m0) (vv m0 V) ret).load 0 1272 8).toNat < 31
    rw [hl, UInt64.toNat_toBitVec, toUInt64_toNat_of (by omega)]
    omega
  have hvld := fun ret ↦ ld_ew (rs := rsOf m0) (vals := vv m0 V) (ret := ret) hv
  refine stepC (T' := t58) (vals' := vv m0 (Vp m0 V cl)) hp c h hat b57_in_code
    (by simp [b57]) run_b57 hat.2.mt (by decide) (oc := 0) (by decide) rfl (hko s1 cl)
    (Sk := keccakOpenStack) ko_le (fun mc hmc hk hsk hso hrsp hch hkk ↦ ?_)
    (Lc := [(96, 24), (232, 96)]) (Oc := [(1, 0, 760), (2, 140288, 65536)])
    (fun mc m' hmc hq ↦ ?_) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl rfl ?_
    (fun i hi ↦ nomatch tregE (rfl : t58.reg .rax = some (.reg .rax)) hi)
    (fun i hi ↦ nomatch tregE (rfl : t58.reg .rdx = some (.reg .rdx)) hi)
    rfl rfl rfl (fun _ _ _ _ _ h ↦ by cases h) rfl
    fun st1 hpc1 hB1 ⟨mc, hmc, hrsp, hq, _⟩ hc1 hk1 ↦ ?_
  · have ca : CallAt m0 wrB 0 mc := ⟨hrsp, by decide, hk, hso⟩
    have rdi : reg mc .rdi = off (fb m0) 96 := (hmc.regs .rdi _ rfl).trans (ev_frame 96)
    have rsi : reg mc .rsi = reg m0 .rdi := hmc.regs .rsi _ rfl
    have rdx : reg mc .rdx = reg m0 .rsi := hmc.regs .rdx _ rfl
    have rcx : reg mc .rcx = off (fb m0) 1280 := by
      change mc.regs.get64 .rcx = _
      rw [hmc.regs .rcx _ rfl, eval_ite_ult_pos _ _ _ (by decide) (h31 _)]
      exact ev_frame 1280
    have r8 : (reg mc .r8).toNat = cl.point.size := by
      change (mc.regs.get64 .r8).toNat = _
      rw [hmc.regs .r8 _ rfl, eval_ite_ult_pos _ _ _ (by decide) (h31 _)]
      change ((envZ m0 st.data 3344 3368 (rsOf m0) (vv m0 V) _).load 0 1272 8).toNat = _
      rw [hl, UInt64.toNat_toBitVec, toUInt64_toNat_of (by omega)]
    have r9 : reg mc .r9 = off (reg m0 .r9) 25600 := (hmc.regs .r9 _ rfl).trans (add64 _ _)
    have a0 : openFirst mc = 0#64 := stackArg_of hmc rfl rfl (oc := 0) (by decide)
      (i := 0) (by decide) (v := .lit 0) (by decide)
    have a1 : openCount mc = 2#64 := stackArg_of hmc rfl rfl (oc := 0) (by decide)
      (i := 1) (by decide) (v := .lit 2) (by decide)
    have a4 : openSlot mc = off (fb m0) 232 :=
      (stackArg_of hmc rfl rfl (oc := 0) (by decide) (i := 4) (by decide)
        (v := .ptr 0 232) (by decide)).trans (ev_frame 232)
    have a5 : openRows mc = off (reg m0 .r9) 140288 :=
      (stackArg_of hmc rfl rfl (oc := 0) (by decide) (i := 5) (by decide)
        (v := .var 20) (by decide)).trans (add64 _ _)
    unfold KeccakOpenPre
    dsimp only
    rw [rdi, rsi, rdx, rcx, r8, r9, a0, a1, a4, a5]
    refine ⟨hsk, argsOk c h ca (by decide), ca.rc c hrc ko_le,
      Chg.ts c hch (by decide) rfl (by decide) hkk hts, rfl,
      NativeRustcVm.Tables.EWsAt.of_same hpt
        (Chg.frame c hch (by decide) rfl (o := 1280) (n := 480) (by decide) (by decide))
        (by simp; omega),
      Chg.wtsR c hch (by decide) rfl (by decide) (by decide) hcw, hfit, by decide, by decide,
      areas_ko c h ca (by decide) (by decide) (by decide) (by decide) hsz (by decide)
        (by decide) (by decide) (by decide), ?_⟩
    exact open2_got c ca hsz
  · have rdi : reg mc .rdi = off (fb m0) 96 := (hmc.regs .rdi _ rfl).trans (ev_frame 96)
    have rsi : reg mc .rsi = off (ob m0 1) 0 := (hmc.regs .rsi _ rfl).trans (off0 _).symm
    have a4 : openSlot mc = off (fb m0) 232 :=
      (stackArg_of hmc rfl rfl (oc := 0) (by decide) (i := 4) (by decide)
        (v := .ptr 0 232) (by decide)).trans (ev_frame 232)
    have a5 : openRows mc = off (ob m0 2) 140288 :=
      (stackArg_of hmc rfl rfl (oc := 0) (by decide) (i := 5) (by decide)
        (v := .var 20) (by decide)).trans (add64 _ _)
    obtain ⟨-, -, hso, hsv⟩ := hq
    refine chgQ hso (fun q ⟨r, hr, hq⟩ ↦ ?_) hsv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact .inl hq
    · exact .inr (inR_frame rdi List.mem_cons_self hq)
    · exact .inr (inR_reg rsi List.mem_cons_self hq)
    · exact .inr (inR_frame a4 (List.mem_cons_of_mem _ List.mem_cons_self) hq)
    · exact .inr (inR_reg a5 (List.mem_cons_of_mem _ List.mem_cons_self) hq)
  · intro ret
    simp only [List.cons_append, List.nil_append, List.forall_mem_cons]
    simp only [eval_ite_ult_pos _ _ _ (by decide) (h31 ret)]
    simp only [Sym.eval, hl]
    and_intros <;> first | rfl | exact fun _ h ↦ nomatch h
  have rdi : reg mc .rdi = off (fb m0) 96 := (hmc.regs .rdi _ rfl).trans (ev_frame 96)
  have rsi : reg mc .rsi = reg m0 .rdi := hmc.regs .rsi _ rfl
  have rdx : reg mc .rdx = reg m0 .rsi := hmc.regs .rdx _ rfl
  have a0 : openFirst mc = 0#64 := stackArg_of hmc rfl rfl (oc := 0) (by decide)
    (i := 0) (by decide) (v := .lit 0) (by decide)
  have a1 : openCount mc = 2#64 := stackArg_of hmc rfl rfl (oc := 0) (by decide)
    (i := 1) (by decide) (v := .lit 2) (by decide)
  have a2 : stackArg mc 2 = v.c0.toBitVec :=
    (stackArg_of hmc rfl rfl (oc := 0) (by decide) (i := 2) (by decide)
      (v := .load 0 104 8) (by decide)).trans (hvld _).1
  have a3 : stackArg mc 3 = v.c1.toBitVec :=
    (stackArg_of hmc rfl rfl (oc := 0) (by decide) (i := 3) (by decide)
      (v := .load 0 112 8) (by decide)).trans (hvld _).2
  have a4 : openSlot mc = off (fb m0) 232 :=
    (stackArg_of hmc rfl rfl (oc := 0) (by decide) (i := 4) (by decide)
      (v := .ptr 0 232) (by decide)).trans (ev_frame 232)
  have a5 : openRows mc = off (reg m0 .r9) 140288 :=
    (stackArg_of hmc rfl rfl (oc := 0) (by decide) (i := 5) (by decide)
      (v := .var 20) (by decide)).trans (add64 _ _)
  have hval : openValue mc = v := by unfold openValue ewArg; rw [a2, a3]
  have hr0 : keccakOpen (reg mc .rdx).toNat cl (openFirst mc).toNat (openCount mc).toNat
      (openValue mc) = keccakOpen (reg m0 .rsi).toNat cl 0 2 v := by
    rw [rdx, a0, a1, hval]
    rfl
  obtain ⟨hopt, hsome, -, -⟩ := hq
  rw [rdi, hr0] at hopt
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b57_next] at hpc1
  refine stepJ (T' := t59) (vals' := vv m0 (Vp m0 V cl)) (o := NativeRustcVmX64.Vm.VerifyKeccak.b58Offset) hp c h ⟨hpc1, hB1⟩
    b58_in_code (by simp [b58]) run_b58 nofun (hB1.mt 0) (by decide) rfl rfl (by vtacJ)
    (by decide) rfl rfl rfl (fun _ _ _ _ _ h ↦ by cases h) rfl
    fun st2 hpc2 hB2 _ hc2 hk2 ↦ ?_
  simp only [PcOk] at hpc2
  cases hr : (keccakOpen (reg m0 .rsi).toNat cl 0 2 v).run s1 with
  | none =>
    rw [hr] at hopt
    rw [tag8 (env := envZ m0 st1.data 3344 3368 (rsOf m0) (vv m0 (Vp m0 V cl)) 0)
      (Or.inl rfl) hopt] at hpc2
    exact failG hp hpre hB2 hpc2 (by decide) (hfail hr)
  | some p =>
    obtain ⟨⟨slot, ws, v2⟩, s2⟩ := p
    rw [hr] at hopt
    obtain ⟨htag, hv2⟩ := hopt
    rw [tag8 (env := envZ m0 st1.data 3344 3368 (rsOf m0) (vv m0 (Vp m0 V cl)) 0)
      (Or.inr rfl) htag] at hpc2
    simp only [show ((1 : UInt64) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte] at hpc2
    obtain ⟨hslot, hws, hts2⟩ := hsome slot ws v2 s2 (by rw [hr0]; exact hr)
    rw [a4] at hslot
    rw [a5] at hws
    rw [rsi] at hts2
    rw [toff, show 96 + 8 = 104 from rfl] at hv2
    obtain ⟨h6, h64⟩ := open_weights_size hr
    refine cont st2 slot ws v2 s2 ⟨hpc2.trans (by rw [NativeRustcVmX64.Vm.VerifyKeccak.b58_next]), hB2⟩ hr
      (NativeRustcVm.Layout.EWAt.of_same hv2
        (Chg.frame c hc2 (by decide) rfl (by decide) (by decide)) le_rfl)
      (Chg.ewsF c hc2 (by decide) rfl (by rw [Array.length_toList, h6]; decide)
        (by rw [Array.length_toList, h6]; decide) hslot)
      (Chg.ewsR c hc2 (by decide) rfl (i := 2) (o := 140288) (by decide) (by decide)
        rfl (by rw [Array.length_toList, h64]; decide) hws)
      (Chg.ts c hc2 (by decide) rfl (by decide) hk2 hts2) ?_
      (NativeRustcVmX64.Transcript.kept_trans hk1 hk2)
    exact Chg.mono c (hc1.trans hc2) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
