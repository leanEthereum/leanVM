module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.ExtRest
public import NativeRustcVmX64.Code.Vm.PushClaim.Names

/-!
# Pushing the committed output claim

Blocks 53–54 append the column claim after the three bounded point extensions.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea)
open NativeRustcVm.KeccakGkr (off)

public section

@[expose] def pushS : SState where
  regs := [some (.ptr 0 416), some (.var 12),
    some (.ite (.cmp .ult .W64 (.load 0 408 8) (.lit 37)) (.load 0 408 8) (.lit 0)),
    some (.ite (.cmp .ult .W64 (.load 0 408 8) (.lit 37)) (.ptr 0 416) (.lit 8)),
    some (.lit 4), some (.load 0 3352 8), some (.ptr 0 48), some (.var 19),
    some (.var 23), some (.var 24), some (.reg .r10), some (.reg .r11),
    some (.ptr 0 232), some (.var 20), some (.var 22), some (.var 21)]
  flags := {
    cf := some (.cmp .ult .W64 (.load 0 408 8) (.lit 37))
    zf := some (.cmp .eq .W64 (.load 0 408 8) (.lit 37))
    sf := some (.msb .W64 (.bin .sub .W64 (.load 0 408 8) (.lit 37)))
    of := some (.cmp .subV .W64 (.load 0 408 8) (.lit 37)) }
  mem := { r := 0, off := 48, n := 8, v := .retAddr } :: t52.mem
  regions := t52.regions

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

theorem pushArgs (c : Ctx a inst m0) {d mc : MachineData} {V : Vs} {ret : BitVec 64}
    {xs : List EW} (hB : BndZ m0 3344 3368 verifyKeccakStack (rsOf m0) wrB t52 (vv m0 V) d)
    (hbuf : NativeRustcVm.BufEWAt d.dmem (off (fb m0) 408) 36 xs)
    (hm : Match (envZ m0 d 3344 3368 (rsOf m0) (vv m0 V) ret) pushS mc) :
    reg mc .rdi = stackArg m0 0 ∧ reg mc .rdx = off (fb m0) 416 ∧
      reg mc .rcx = xs.length.toUInt64.toBitVec := by
  have hn : xs.length.toUInt64.toNat = xs.length := toUInt64_toNat_of (by have := hbuf.1; omega)
  have hl := ld_frame (rs := rsOf m0) (vals := vv m0 V) (ret := ret) hbuf.2.1
  have hlt : ((.load 0 408 8 : Sym).eval
      (envZ m0 d 3344 3368 (rsOf m0) (vv m0 V) ret)).toNat < 37 := by
    simp only [Sym.eval, hl, UInt64.toNat_toBitVec, hn]
    have := hbuf.1
    omega
  refine ⟨(hm.regs .rdi _ rfl).trans (argLoad c hB.same (i := 0) (by decide)), ?_, ?_⟩
  · change mc.regs.get64 .rdx = _
    rw [hm.regs .rdx _ rfl, eval_ite_ult_pos _ _ _ (by decide) hlt]
    exact ev_frame 416
  · change mc.regs.get64 .rcx = _
    rw [hm.regs .rcx _ rfl, eval_ite_ult_pos _ _ _ (by decide) hlt]
    exact hl

theorem pushStep (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hpush : ∀ cs, Spec (Labels.label NativeRustcVmX64.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    {st : MachineState} {V : Vs} {slot : Array EW} {w : EW}
    (hat : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b53Offset wrB t52 (vv m0 V) st)
    (hw0 : V.w0 = w.c0.toBitVec) (hw1 : V.w1 = w.c1.toBitVec)
    (hbuf : NativeRustcVm.BufEWAt st.data.dmem (off (fb m0) 408) 36
      (inst.toList ++ slot.toList))
    (hcls : NativeRustcVm.Layout.ClaimsWAt st.data.dmem (keccakClaims m0) cs)
    {R : MachineState → Prop}
    (cont : ∀ st', At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b55Offset wrB t52 (vv m0 V) st' →
      NativeRustcVm.Layout.ClaimsWAt st'.data.dmem (keccakClaims m0)
        (cs.push (outClaim inst slot w)) →
      Chg m0 st.data.dmem st'.data.dmem [(0, 152), (3296, 48)] [(3, 0, 97288)] →
      Kept st.data.dmem st'.data.dmem → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  have hcap : cs.size < NativeRustcVm.Layout.claimCap := hpre.2.2.2.2.2.2.2.1
  let xs := inst.toList ++ slot.toList
  have hlen : xs.length ≤ 36 := hbuf.1
  have hn : xs.length.toUInt64.toNat = xs.length := toUInt64_toNat_of (by omega)
  have args := fun mc hm ↦ pushArgs c hat.2 hbuf (mc := mc)
    (ret := (Host.addrOf (k + (364 + b53.length))).toBitVec) hm
  have rdi := fun mc hm ↦ (args mc hm).1
  have rdx := fun mc hm ↦ (args mc hm).2.1
  have rcx := fun mc hm ↦ (args mc hm).2.2
  refine stepC (T' := t52) (vals' := vv m0 V) hp c h hat b53_in_code (by simp [b53])
    run_b53 hat.2.mt (by decide) (oc := 48) (by decide) rfl (hpush cs)
    (Sk := pushClaimStack) (by rw [vk_eq]; decide) (fun mc hmc hk hsk hso hrsp hch hkk ↦ ?_)
    (Lc := []) (Oc := [(3, 0, 97288)]) (fun mc m' hmc hq ↦ ?_)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl (by vtacC)
    (fun i hi ↦ nomatch tregE (rfl : t52.reg .rax = some (.reg .rax)) hi)
    (fun i hi ↦ nomatch tregE (rfl : t52.reg .rdx = some (.reg .rdx)) hi)
    rfl rfl rfl (fun _ _ _ _ _ h ↦ by cases h) rfl
    fun st1 hpc1 hB1 ⟨mc, hmc, hrsp, hq, hch⟩ hc1 hk1 ↦ ?_
  · have ca : CallAt m0 wrB 48 mc := ⟨hrsp, by decide, hk, hso⟩
    unfold PushClaimPre SliceOk
    rw [rdi mc hmc, rdx mc hmc, rcx mc hmc, UInt64.toNat_toBitVec, hn]
    refine ⟨hsk, Chg.cls c hch (by decide) rfl (by decide) hcls, ?_, ?_, ?_, ?_⟩
    · rw [NativeRustcVm.Layout.claimsBytes_eq]
      simpa only [off0, ob, keccakClaims] using
        (show Readable mc (off (ob m0 3) 0) 97288 from
          ⟨mapR h ca (by decide) (by decide) (by decide),
            nwR c (by decide) (by decide) (by decide)⟩)
    · exact sep_stk' (stk_callee c ca (by rw [vk_eq]; decide)) c.cS
    · refine ⟨⟨mapF h ca (by omega), nwF c (by omega)⟩, ?_⟩
      exact (sepSF0 c ca (by rw [vk_eq]; decide) (by decide) (by decide)).symm
    · exact (sepFX c (by omega) c.cS).symm
  · obtain ⟨-, hso, hsv⟩ := hq
    exact chgQ hso (fun q h ↦ h.elim
      (fun h ↦ .inr (inR_reg
        (show reg mc .rdi = off (ob m0 3) 0 from
          (rdi mc hmc).trans (off0 _).symm) List.mem_cons_self h)) .inl) hsv
  have hbufc := NativeRustcVm.Layout.BufEWAt.of_same hbuf
    (Chg.frame c hch (n := 584) (by decide) rfl (by decide) (by decide)) (by decide)
  have hews : NativeRustcVm.EWsAt mc.dmem (off (fb m0) 416) xs := by
    have := hbufc.2.2
    rw [show off (fb m0) 408 + 8#64 = off (fb m0) 416 from
      NativeRustcVm.Transcript.off_add _ _ _] at this
    exact this
  have rsi : reg mc .rsi = 4#64 := hmc.regs .rsi _ rfl
  have r8 : reg mc .r8 = w.c0.toBitVec := (hmc.regs .r8 _ rfl).trans hw0
  have r9 : reg mc .r9 = w.c1.toBitVec := (hmc.regs .r9 _ rfl).trans hw1
  obtain ⟨hres, -, -⟩ := hq
  rw [rdi mc hmc, rcx mc hmc, UInt64.toNat_toBitVec, hn] at hres
  simp only [hcap, show xs.length ≤ NativeRustcVm.Layout.pointCap from hlen,
    and_self, ↓reduceIte] at hres
  obtain ⟨hal, hcls1⟩ := hres
  rw [rsi, rdx mc hmc, slice_of hews (by rw [UInt64.toNat_toBitVec, hn]), r8, r9,
    show ewArg w.c0.toBitVec w.c1.toBitVec = w from rfl] at hcls1
  have hout : (⟨(4#64).toNat, xs.toArray, w⟩ : ColumnClaimW) = outClaim inst slot w := by
    unfold outClaim xs
    congr 1
    apply Array.toList_inj.mp
    simp [Array.toList_append, Array.toList_extract]
  rw [hout] at hcls1
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b53_next] at hpc1
  refine stepJ (T' := t52) (vals' := vv m0 V) (o := NativeRustcVmX64.Vm.VerifyKeccak.b54Offset) hp c h ⟨hpc1, hB1⟩ b54_in_code
    (by simp [b54]) run_b54 nofun (hB1.mt 0) (by decide) rfl rfl (by vtacJ)
    (by decide) rfl rfl rfl (fun _ _ _ _ _ h ↦ by cases h) rfl
    fun st2 hpc2 hB2 _ hc2 hk2 ↦ ?_
  simp only [PcOk] at hpc2
  rw [alCond] at hpc2
  have h1 : (reg st1.data .rax).toNat % 256 = 1 := hal
  simp only [show (envZ m0 st1.data 3344 3368 (rsOf m0) (vv m0 V) 0).regs .rax =
    reg st1.data .rax from rfl, h1, show ¬(1 = 0) from by decide, decide_false,
    Bool.false_eq_true, ↓reduceIte] at hpc2
  refine cont st2 ⟨hpc2.trans (by rw [NativeRustcVmX64.Vm.VerifyKeccak.b54_next]), hB2⟩
    (Chg.cls c hc2 (by decide) rfl (by decide) hcls1) ?_
    (NativeRustcVmX64.Transcript.kept_trans hk1 hk2)
  exact Chg.mono c (hc1.trans hc2) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
