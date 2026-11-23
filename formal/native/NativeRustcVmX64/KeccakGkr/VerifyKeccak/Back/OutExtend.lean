module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.OutFirst
public import NativeRustcVmX64.Code.Vm.BufEW36Extend.Names

/-! # Extensions into the final output point -/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea)
open NativeRustcVm.KeccakGkr (off)

public section

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

theorem outExtendStep (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    {T T' S' : SState} {V : Vs} {ds : List Directive} {p0 : Nat}
    (hds : ds.IsInfixAt code p0) (hne : ds ≠ [])
    (hrun : exec ds T = some (S', .call NativeRustcVmX64.Vm.BufEW36Extend.entryLabel))
    (hw0 : frameW S' = true) (hsp : S'.reg .rsp = some (.ptr 0 48))
    (hdi : S'.reg .rdi = some (.load 0 3360 8))
    (hokS : okL (wsL S') = true) (hcov : coverL (wsL S') [(0, 88), (3296, 48)] = true)
    (htm : tplMiss 48 [] T' = true) (hok : tplOk T' = true)
    (hrspT : T'.reg .rsp = some (.ptr 0 56))
    (hax : T'.reg .rax = some (.reg .rax)) (hdx' : T'.reg .rdx = some (.reg .rdx))
    {L LW : List (Nat × Sym)} (hL : rlinksOf true S' T' noRsp = some L)
    (hLW : wlinks S' T'.mem = some LW) (hvl : varLinks (L ++ LW) = true)
    (hsz : T'.regions = sizes) (hfl : T'.flags = atomFlags) (hlab : T'.labels = [])
    (hal : T'.aliases = []) (hbd : T'.bounds = [])
    {st : MachineState} (hat : At m0 k p0 wrAll T (vv m0 V) st)
    {Sr : BitVec 64} {n : Nat} {xs ys : List EW}
    (hbuf : NativeRustcVm.BufEWAt st.data.dmem (keccakOutArg m0) 36 xs)
    (hsi : ∀ mc, Match (envZ m0 st.data 3344 3368 (rsOf m0) (vv m0 V)
      (Host.addrOf (k + (p0 + ds.length))).toBitVec) S' mc → reg mc .rsi = Sr)
    (hdx : ∀ mc, Match (envZ m0 st.data 3344 3368 (rsOf m0) (vv m0 V)
      (Host.addrOf (k + (p0 + ds.length))).toBitVec) S' mc → (reg mc .rdx).toNat = n)
    (hsrc : ∀ mc : MachineData, Chg m0 st.data.dmem mc.dmem (wsL S') [] →
      NativeRustcVm.EWsAt mc.dmem Sr ys)
    (hlen : ys.length = n)
    (hsr : ∀ mc, CallAt m0 wrAll 48 mc → Readable mc Sr (16 * n) ∧
      Apart (keccakOutArg m0) 584 Sr (16 * n) ∧ OffStack mc Sr (16 * n) bufEWExtendStack)
    (hfit : xs.length + n ≤ 36) {R : MachineState → Prop}
    (cont : ∀ st', At m0 k (p0 + ds.length) wrAll T' (vv m0 V) st' → boolRet st'.data = 1 →
      NativeRustcVm.BufEWAt st'.data.dmem (keccakOutArg m0) 36 (xs ++ ys) →
      Chg m0 st.data.dmem st'.data.dmem [(0, 88), (3296, 48)] [(4, 0, 584)] →
      Kept st.data.dmem st'.data.dmem → Eventually (step1 Host.exe) R st') (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe) R st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  have ho := fun ret ↦ argLoad c hat.2.same (vals := vv m0 V) (ret := ret) (i := 1) (by decide)
  refine stepC (hknown := hknown) (T' := T') (vals' := vv m0 V) hp c h hat hds hne hrun hat.2.mt hw0
    (oc := 48) (by decide) hsp hext (Sk := bufEWExtendStack) (by rw [vk_eq]; decide)
    (fun mc hmc hk hsk hso hrsp hch hkk ↦ ?_) (Lc := []) (Oc := [(4, 0, 584)])
    (fun mc m' hmc hq ↦ ?_) rfl (by decide) (by decide) htm hok hrspT hL hLW
    (fun _ ↦ varLinks_eval hvl _) (fun i hi ↦ nomatch tregE hax hi)
    (fun i hi ↦ nomatch tregE hdx' hi) hsz hfl hlab
    (fun _ _ _ _ _ hx ↦ by simp [hal] at hx) hbd
    fun st1 hpc1 hB1 ⟨mc, hmc, hrsp, hq, hch⟩ hc1 hk1 ↦ ?_
  · have ca : CallAt m0 wrAll 48 mc := ⟨hrsp, by decide, hk, hso⟩
    have rdi : reg mc .rdi = keccakOutArg m0 := (hmc.regs .rdi _ hdi).trans (ho _)
    have hb := NativeRustcVm.Layout.BufEWAt.of_same hbuf
      (by simpa only [off0, ob] using
        (Chg.regS c hch hokS rfl (i := 4) (o := 0) (n := 584)
          (by decide) (by decide) rfl (by decide))) (by decide)
    obtain ⟨hrd, hap, hos⟩ := hsr mc ca
    unfold BufEWExtendPre
    rw [rdi, hsi mc hmc, hdx mc hmc, NativeRustcVm.wordOf_of_wordAt hb.2.1,
      toUInt64_toNat_of (by have := hbuf.1; omega)]
    refine ⟨hsk, hbuf.1, ?_, hrd, hap, ?_, hos⟩
    · simpa only [off0, ob] using (show Readable mc (off (ob m0 4) 0) 584 from
        ⟨mapR h ca (by decide) (by decide) (by decide), nwR c (by decide) (by decide) (by decide)⟩)
    · exact sep_stk' (stk_callee c ca (by rw [vk_eq]; decide)) (by
        have ho := c.oS
        unfold Sep at ho ⊢
        omega)
  · have rdi : reg mc .rdi = off (ob m0 4) 0 :=
      ((hmc.regs .rdi _ hdi).trans (ho _)).trans (off0 _).symm
    obtain ⟨-, hso, hsv⟩ := hq
    exact chgQ hso (fun q h ↦ h.elim
      (fun h ↦ .inr (inR_reg rdi List.mem_cons_self h)) .inl) hsv
  have rdi : reg mc .rdi = keccakOutArg m0 := (hmc.regs .rdi _ hdi).trans (ho _)
  have hb := NativeRustcVm.Layout.BufEWAt.of_same hbuf
    (by simpa only [off0, ob] using
      (Chg.regS c hch hokS rfl (i := 4) (o := 0) (n := 584)
        (by decide) (by decide) rfl (by decide))) (by decide)
  obtain ⟨hres, -, -⟩ := hq
  rw [rdi, hsi mc hmc, NativeRustcVm.wordOf_of_wordAt hb.2.1,
    toUInt64_toNat_of (by have := hbuf.1; omega), bufEWOf_of hb (by decide),
    slice_of (hsrc mc hch) ((hdx mc hmc).trans hlen.symm), hdx mc hmc] at hres
  simp only [hfit, ↓reduceIte] at hres
  refine cont st1 ⟨hpc1, hB1⟩ hres.1 hres.2 ?_ hk1
  apply Chg.mono c hc1
  · rw [okL_append, hokS]; rfl
  · decide
  · decide
  · decide
  · rw [coverL_append, hcov]; rfl
  · decide

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
