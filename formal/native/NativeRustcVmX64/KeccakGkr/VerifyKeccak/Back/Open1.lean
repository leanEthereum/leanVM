module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.OArea
public import NativeRustcVmX64.Code.Vm.KeccakOpen.Names

/-!
# `verify_keccak`: the opening of the committed outputs (x86-64)

`b40`: `keccak_open(frame + 408, t, logSteps, first.point (frame 2056), scratch.first_weights,
1, 1, committed, frame + 232, scratch.rows)`; `b41`: its tag, on `None` the return with AL `0`.
At `b42` (`t42`): the value at frame `416`, the slot point at `232`, row `0` at the scratch's
`rows`.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea TStateAt OptEWAt tstateBytes)
open NativeRustcVm.KeccakGkr (off ClaimAt WeightsAt rowsBytes weightsBytes)

public section

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

/-- Frame subregions used by either opening stay inside the protected stack. -/
theorem open_frame_cover (c : Ctx a inst m0) {o n : Nat}
    (ho : o < 3368) (hn : o + n ≤ 3352) :
    (stackBelow m0 verifyKeccakStack).toNat ≤ (off (fb m0) o).toNat ∧
      (off (fb m0) o).toNat + n ≤
        (stackBelow m0 verifyKeccakStack).toNat + (verifyKeccakStack + 8) := by
  rw [c.K, off_fb c ho]
  have hsp := c.sp
  have hstack := vk_eq
  omega

/-- Scratch subregions used by either opening stay inside the protected scratch. -/
theorem open_scratch_cover (c : Ctx a inst m0) {o n : Nat}
    (ho : o < 205824) (hn : o + n ≤ 205824) :
    (reg m0 .r9).toNat ≤ (off (reg m0 .r9) o).toNat ∧
      (off (reg m0 .r9) o).toNat + n ≤ (reg m0 .r9).toNat + 205824 := by
  have hw := c.sW
  rw [NativeRustcVm.Transcript.toNat_off (by omega)]
  omega

/-- The opening's GOT footprint, independent of the symbolic execution state. -/
private theorem open1_got (c : Ctx a inst m0) {mc : MachineData}
    (ca : CallAt m0 wrA 0 mc) {n : Nat} (hn : n ≤ 30) :
    GotAt mc keccakOpenStack
      [(off (fb m0) 408, 24), (reg m0 .rdi, tstateBytes),
        (off (fb m0) 232, 96), (off (reg m0 .r9) 140288, rowsBytes),
        (a.region.addr, a.region.size), (off (fb m0) 2056, 16 * n),
        (off (reg m0 .r9) 0, weightsBytes), (rcAddr, 192), (rspOf mc + 8#64, 48)]
      ["memcpy"] := by
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

/-- **The first opening** (`b40`, `b41`): at `b42` (`t42`). -/
theorem open1Step (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hko : ∀ s c, Spec (Labels.label NativeRustcVmX64.Vm.KeccakOpen.entryLabel) (KeccakOpenPre a s c)
      (KeccakOpenPost a s c))
    {st : MachineState} {V : Vs} {s' : TState} {first cl : KeccakClaimW} {cm : EW}
    (hat : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b40Offset wrA tL (vv m0 V) st)
    (hc0 : V.c0 = cm.c0.toBitVec) (hc1 : V.c1 = cm.c1.toBitVec)
    (hfl : V.fl = BitVec.ofNat 64 first.point.size)
    (hts : TStateAt st.data.dmem (reg m0 .rdi) a s')
    (hf : ClaimAt st.data.dmem (off (fb m0) 1768) first)
    (hfw : WeightsAt st.data.dmem (off (reg m0 .r9) 0) first)
    (hsf : SegmentsFit (reg m0 .rsi).toNat first)
    (hrun : (NativeVm.Model.verifyKeccak (reg m0 .rsi).toNat inst output).run s =
      (restOpen (reg m0 .rsi).toNat inst first cm cl).run s')
    (cont : ∀ st1 sl ws v s1, At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b42Offset wrA t42 (vv m0 V) st1 →
      (keccakOpen (reg m0 .rsi).toNat first 1 1 cm).run s' = some ((sl, ws, v), s1) →
      NativeRustcVm.EWAt st1.data.dmem (off (fb m0) 416) v →
      NativeRustcVm.EWsAt st1.data.dmem (off (fb m0) 232) sl.toList →
      NativeRustcVm.EWsAt st1.data.dmem (off (reg m0 .r9) 140288) ws.toList →
      TStateAt st1.data.dmem (reg m0 .rdi) a s1 →
      Chg m0 st.data.dmem st1.data.dmem [(0, 432), (3296, 48)]
        [(1, 0, 760), (2, 140288, 65536)] →
      Kept st.data.dmem st1.data.dmem →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) st1) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  have hrc : RcAt m0 verifyKeccakStack := hpre.2.2.1
  obtain ⟨hsz, -, hpt⟩ := ClaimAt.pointAt hf
  rw [koff, show 1768 + 288 = 2056 from rfl] at hpt
  have h18 : (vv m0 V 18).toNat = first.point.size := by
    show V.fl.toNat = _
    rw [hfl, ofNat_toNat (by omega)]
  have h31 : (vv m0 V 18).toNat < 31 := by omega
  refine stepC (T' := t41) (vals' := vv m0 V) hp c h hat b40_in_code (by simp [b40]) run_b40
    hat.2.mt (by decide) (oc := 0) (by decide) rfl (hko s' first) (Sk := keccakOpenStack) ko_le
    (fun mc hmc hk hsk hso hrsp hch hkk ↦ ?_) (Lc := [(408, 24), (232, 96)])
    (Oc := [(1, 0, 760), (2, 140288, 65536)]) (fun mc m' hmc hq ↦ ?_) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl rfl rfl (by vtacC)
    (fun i hi ↦ nomatch tregE (rfl : t41.reg .rax = some (.reg .rax)) hi)
    (fun i hi ↦ nomatch tregE (rfl : t41.reg .rdx = some (.reg .rdx)) hi) rfl rfl rfl
    (fun _ _ _ _ _ h ↦ by cases h) rfl fun st' hpc' hB' ⟨mc, hmc, hrsp, hq, _⟩ hc' hk' ↦ ?_
  · -- `keccak_open`'s precondition.
    have ca : CallAt m0 wrA 0 mc := ⟨hrsp, by decide, hk, hso⟩
    have rdi : reg mc .rdi = off (fb m0) 408 := (hmc.regs .rdi _ rfl).trans (ev_frame 408)
    have rsi : reg mc .rsi = reg m0 .rdi := hmc.regs .rsi _ rfl
    have rdx : reg mc .rdx = reg m0 .rsi := hmc.regs .rdx _ rfl
    have rcx : reg mc .rcx = off (fb m0) 2056 := by
      refine (hmc.regs .rcx _ rfl).trans ?_
      rw [eval_ite_ult_pos _ _ _ (by decide) (by exact h31)]
      exact ev_frame 2056
    have r8 : (reg mc .r8).toNat = first.point.size := by
      rw [show reg mc .r8 = _ from hmc.regs .r8 _ rfl,
        eval_ite_ult_pos _ _ _ (by decide) (by exact h31)]
      exact h18
    have r9 : reg mc .r9 = off (reg m0 .r9) 0 := (hmc.regs .r9 _ rfl).trans (off0 _).symm
    have a0 : openFirst mc = BitVec.ofNat 64 1 :=
      stackArg_of hmc rfl rfl (oc := 0) (by decide) (i := 0) (by decide) (v := .lit 1) (by decide)
    have a1 : openCount mc = BitVec.ofNat 64 1 :=
      stackArg_of hmc rfl rfl (oc := 0) (by decide) (i := 1) (by decide) (v := .lit 1) (by decide)
    have a4 : openSlot mc = off (fb m0) 232 :=
      (stackArg_of hmc rfl rfl (oc := 0) (by decide) (i := 4) (by decide) (v := .ptr 0 232)
        (by decide)).trans (ev_frame 232)
    have a5 : openRows mc = off (reg m0 .r9) 140288 :=
      (stackArg_of hmc rfl rfl (oc := 0) (by decide) (i := 5) (by decide)
        (v := .bin .add .W64 (.var 11) (.lit 140288)) (by decide)).trans (add64 _ _)
    have hch' : Chg m0 st.data.dmem mc.dmem _ [] := hch
    unfold KeccakOpenPre
    dsimp only
    rw [rdi, rsi, rdx, rcx, r8, r9, a0, a1, a4, a5]
    refine ⟨hsk, argsOk c h ca (by decide), ca.rc c hrc ko_le,
      Chg.ts c hch' (by decide) (by decide) (by decide) hkk hts, rfl,
      NativeRustcVm.Tables.EWsAt.of_same hpt
        (Chg.frame c hch' (by decide) (by decide) (o := 2056) (n := 480) (by decide) (by decide))
        (by simp only [Array.length_toList]; omega),
      Chg.wtsR c hch' (by decide) (by decide) (by decide) (by decide) hfw, hsf, by decide,
      by decide, ?_, ?_⟩
    · exact areas_ko c h ca (by decide) (by decide) (by decide) (by decide) hsz (by decide)
        (by decide) (by decide) (by decide)
    · exact open1_got c ca hsz
  · -- Its changes.
    have rdi : reg mc .rdi = off (fb m0) 408 := (hmc.regs .rdi _ rfl).trans (ev_frame 408)
    have rsi : reg mc .rsi = off (ob m0 1) 0 := (hmc.regs .rsi _ rfl).trans (off0 _).symm
    have a4 : openSlot mc = off (fb m0) 232 :=
      (stackArg_of hmc rfl rfl (oc := 0) (by decide) (i := 4) (by decide) (v := .ptr 0 232)
        (by decide)).trans (ev_frame 232)
    have a5 : openRows mc = off (ob m0 2) 140288 :=
      (stackArg_of hmc rfl rfl (oc := 0) (by decide) (i := 5) (by decide)
        (v := .bin .add .W64 (.var 11) (.lit 140288)) (by decide)).trans (add64 _ _)
    obtain ⟨-, -, hso, hsv⟩ := hq
    refine chgQ hso (fun q ⟨r, hr, hq⟩ ↦ ?_) hsv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact .inl hq
    · exact .inr (inR_frame rdi List.mem_cons_self hq)
    · exact .inr (inR_reg rsi List.mem_cons_self hq)
    · exact .inr (inR_frame a4 (List.mem_cons_of_mem _ List.mem_cons_self) hq)
    · exact .inr (inR_reg a5 (List.mem_cons_of_mem _ List.mem_cons_self) hq)
  -- `b41`: the tag.
  have rdi : reg mc .rdi = off (fb m0) 408 := (hmc.regs .rdi _ rfl).trans (ev_frame 408)
  have rsi : reg mc .rsi = reg m0 .rdi := hmc.regs .rsi _ rfl
  have rdx : reg mc .rdx = reg m0 .rsi := hmc.regs .rdx _ rfl
  have a0 : openFirst mc = BitVec.ofNat 64 1 :=
    stackArg_of hmc rfl rfl (oc := 0) (by decide) (i := 0) (by decide) (v := .lit 1) (by decide)
  have a1 : openCount mc = BitVec.ofNat 64 1 :=
    stackArg_of hmc rfl rfl (oc := 0) (by decide) (i := 1) (by decide) (v := .lit 1) (by decide)
  have a2 : stackArg mc 2 = cm.c0.toBitVec :=
    (stackArg_of hmc rfl rfl (oc := 0) (by decide) (i := 2) (by decide) (v := .var 16)
      (by decide)).trans hc0
  have a3 : stackArg mc 3 = cm.c1.toBitVec :=
    (stackArg_of hmc rfl rfl (oc := 0) (by decide) (i := 3) (by decide) (v := .var 17)
      (by decide)).trans hc1
  have a4 : openSlot mc = off (fb m0) 232 :=
    (stackArg_of hmc rfl rfl (oc := 0) (by decide) (i := 4) (by decide) (v := .ptr 0 232)
      (by decide)).trans (ev_frame 232)
  have a5 : openRows mc = off (reg m0 .r9) 140288 :=
    (stackArg_of hmc rfl rfl (oc := 0) (by decide) (i := 5) (by decide)
      (v := .bin .add .W64 (.var 11) (.lit 140288)) (by decide)).trans (add64 _ _)
  have hval : openValue mc = cm := by
    unfold openValue ewArg
    rw [a2, a3]
  have hr0 : keccakOpen (reg mc .rdx).toNat first (openFirst mc).toNat (openCount mc).toNat
      (openValue mc) = keccakOpen (reg m0 .rsi).toNat first 1 1 cm := by
    rw [rdx, a0, a1, hval]
    rfl
  obtain ⟨hopt, hsome, -, -⟩ := hq
  rw [rdi, hr0] at hopt
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b40_next] at hpc'
  refine stepJ (T' := t42) (vals' := vv m0 V) (o := NativeRustcVmX64.Vm.VerifyKeccak.b41Offset) hp c h ⟨hpc', hB'⟩ b41_in_code
    (by simp [b41]) run_b41 nofun (hB'.mt 0) (by decide) rfl rfl (by vtacJ) (by decide) rfl rfl
    rfl (fun _ _ _ _ _ h ↦ by cases h) rfl fun st2 hpc2 hB2 _ hc2 hk2 ↦ ?_
  simp only [PcOk] at hpc2
  cases hr : (keccakOpen (reg m0 .rsi).toNat first 1 1 cm).run s' with
  | none =>
    rw [hr] at hopt
    have hw : NativeRustcVm.WordAt st'.data.dmem (off (fb m0) 408) 0 := hopt
    rw [tag32 (env := envZ m0 st'.data 3344 3368 (rsOf m0) (vv m0 V) 0) (Or.inl rfl) hw] at hpc2
    exact failG hp hpre hB2 hpc2 (by decide) (by rw [hrun]; exact restOpen_none hr)
  | some p =>
    obtain ⟨⟨sl, ws, v⟩, s1⟩ := p
    rw [hr] at hopt
    obtain ⟨htag, hv⟩ := hopt
    rw [tag32 (env := envZ m0 st'.data 3344 3368 (rsOf m0) (vv m0 V) 0) (Or.inr rfl) htag]
      at hpc2
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hpc2
    obtain ⟨hsl, hws, hts1⟩ := hsome sl ws v s1 (by rw [hr0]; exact hr)
    rw [a4] at hsl
    rw [a5] at hws
    rw [rsi] at hts1
    rw [toff, show 408 + 8 = 416 from rfl] at hv
    obtain ⟨h6, h64⟩ := open_weights_size hr
    refine cont st2 sl ws v s1 ⟨hpc2.trans (by rw [NativeRustcVmX64.Vm.VerifyKeccak.b41_next]), hB2⟩
      hr ?_ ?_ ?_ (Chg.ts c hc2 (by decide) (by decide) (by decide) hk2 hts1) ?_
      (NativeRustcVmX64.Transcript.kept_trans hk' hk2)
    · exact NativeRustcVm.Layout.EWAt.of_same hv (Chg.frame c hc2 (by decide) (by decide)
        (o := 416) (n := 16) (by decide) (by decide)) le_rfl
    · exact Chg.ewsF c hc2 (by decide) (by decide) (by rw [Array.length_toList, h6]; decide)
        (by rw [Array.length_toList, h6]; decide) hsl
    · exact Chg.ewsR c hc2 (by decide) (by decide) (i := 2) (o := 140288) (by decide) (by decide)
        rfl (by rw [Array.length_toList, h64]; decide) hws
    · exact Chg.mono c (hc'.trans hc2) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
