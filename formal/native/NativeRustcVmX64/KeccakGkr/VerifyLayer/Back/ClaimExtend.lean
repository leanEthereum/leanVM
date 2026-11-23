module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.ClaimCopy
public import NativeRustcVmX64.Code.Vm.BufEW30Extend.Names

/-! # Replacing the claim's point with the sumcheck point -/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (DecArea off)

public section

variable [Host] {m0 : MachineData} {a : DecArea} {s s6 : TState} {c : KeccakClaimW}
  {ch b : EW} {pt lp t : Array EW} {k : Nat}

theorem claim_extend (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    (hpt : pt.size ≤ 30) (hpsz : pt.size = c.point.size)
    {d : MachineData} (hb : Body m0 (outs m0) 24 d) (h : TailLive m0 a c ch b pt lp t s6 d.dmem)
    (hbx : reg d .rbx = cA m0)
    (hv : NativeRustcVm.EWAt d.dmem (cA m0)
      (t.getD 0 0 + b * (t.getD 1 0 + b * t.getD 2 0)))
    (hmu : NativeRustcVm.BufEWAt d.dmem (cA m0 + BitVec.ofNat 64 16) 16
      (keccakInstanceWeights ch).toList)
    {R : MachineState → Prop}
    (cont : ∀ d', Body m0 (outs m0) 24 d' → TailLive m0 a c ch b pt lp t s6 d'.dmem →
      OkAl d' true → NativeRustcVm.KeccakGkr.ClaimAt d'.dmem (cA m0) (newClaim ch pt lp t b) →
      Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b84Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b83Offset)⟩ := by
  have g := geo_of hpre
  have cx := ctx hpre (F := 2000) (by decide)
  have hw128 := h.fw (128, .ofBitVec (cA m0 + BitVec.ofNat 64 280))
    (by apply List.mem_append_left; fw_mem)
  have hw64 := h.fw (64, c.point.size.toUInt64) (by apply List.mem_append_left; fw_mem)
  have hwf := wfC hpre hb (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b83Offset + b83.length)).toBitVec)
  have hm : Match (envB m0 d [(cA m0, 768)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b83Offset + b83.length)).toBitVec) (claimS (.reg .rbx)) d :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb.rsp, trivial⟩ trivial trivial
      ⟨by show reg d .rbx = cA m0 + BitVec.ofInt 64 0
          rw [hbx]; simp, trivial⟩
  refine Body.blk (o' := 16) g hb hwf (blk hp b83_in_code (by simp [b83])) e83
    (fun _ _ ↦ rfl) hm (by decide +kernel)
    (fun w hw hr p n he q h1 h2 ↦ Or.inr (Or.inl
      (hexClaim g (by decide +kernel) w hw hr p n he q h1 h2)))
    fun st hm1 hpc1 hb1 _ ↦ ?_
  have h1 := h.claimBlk hpre hpt hwf hm1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hs1 : SameOutside d.dmem st.data.dmem (fun q ↦
      InRange (stackBelow m0 3232) 3232 q ∨ InRange (cA m0 + BitVec.ofNat 64 280) 8 q) :=
    NativeRustcVm.SameOutside.mono (hm1.sameOutside hwf) fun _ hq ↦
      written_chg g (by decide +kernel)
        (hexClaimRange g (by decide) (by decide) (by decide +kernel)) hq
  have hv1 := NativeRustcVm.Layout.EWAt.of_same hv
    (by simpa using (claim_same hpre (o := 280) (n := 8) (p := 0) (len := 16)
      (by decide) (by decide) (Or.inl (by decide)) hs1)) (by decide)
  have hmu1 := NativeRustcVm.Layout.BufEWAt.of_same hmu
    (claim_same hpre (o := 280) (n := 8) (p := 16) (len := 264)
      (by decide) (by decide) (Or.inl (by decide)) hs1) (by decide)
  have hzero : NativeRustcVm.WordAt st.data.dmem (cA m0 + BitVec.ofNat 64 280) 0 :=
    NativeRustcVmX64.Sumcheck.wordAt_written hm1 (r := 1) (v := .lit 0) rfl (o := 280)
      (by decide) (by decide +kernel) rfl
  have hdi : reg st.data .rdi = cA m0 + 280#64 :=
    (hm1.regs .rdi _ rfl).trans (fload8 hw128)
  have hsi : reg st.data .rsi = off (stackBelow m0 2016) 1224 :=
    hm1.regs .rsi (.ptr 0 1224) rfl
  have hdx : reg st.data .rdx = BitVec.ofNat 64 pt.size := by
    rw [show reg st.data .rdx = _ from hm1.regs .rdx _ rfl]
    change (envB m0 d [(cA m0, 768)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b83Offset + b83.length)).toBitVec).load 0 64 8 = _
    rw [fload8 hw64, ← hpsz]
    rfl
  have hlen : (reg st.data .rdx).toNat = pt.size := by
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hd := claimSlice hpre (fun _ h ↦ h) hb1 (Sk := bufEWExtendStack) (by decide)
    (o := 280) (n := 488) (by decide) (by decide)
  have hf := frame_ok (pre_stack hpre) hb1.fr.kept
  have hsrc : NativeRustcVm.Mapped st.data.dmem (off (stackBelow m0 2016) 1224) (16 * pt.size) := by
    intro i hi
    rw [NativeRustcVm.Transcript.off_add]
    exact hf.1 (1224 + i) (by omega)
  have hsp : (rspOf st.data).toNat = (rspOf m0).toNat - 2016 + 16 := by
    rw [hb1.fr.sp]
    exact g.fa (by decide)
  have hsb : (stackBelow st.data bufEWExtendStack).toNat = (rspOf m0).toNat - 2016 + 8 := by
    have hn := g.hN
    rw [stackBelow_toNat (by rw [hsp]; exact Nat.le_trans (by decide) (Nat.le_add_left _ _)), hsp]
    change (rspOf m0).toNat - 2016 + 16 - 8 = _
    omega
  have hpre1 : BufEWExtendPre 30 st.data := by
    dsimp only [BufEWExtendPre]
    rw [hdi, hsi, hlen, NativeRustcVm.wordOf_of_wordAt hzero]
    refine ⟨cx.stackOk (hb1.at_ hpre (fun _ h ↦ h) (by decide)) (by decide),
      by decide, ⟨hd.1, hd.2.1⟩, ⟨hsrc, ?_⟩, ?_, hd.2.2, ?_⟩
    · have hn := g.top
      change (stackBelow m0 2016 + BitVec.ofNat 64 1224).toNat + 16 * pt.size ≤ 2 ^ 64
      rw [g.fa (by decide)]
      omega
    · have hn := g.hN
      have ha := g.hcs
      unfold Apart
      change (cA m0 + BitVec.ofNat 64 280).toNat + 488 ≤
          (stackBelow m0 2016 + BitVec.ofNat 64 1224).toNat ∨
        (stackBelow m0 2016 + BitVec.ofNat 64 1224).toNat + 16 * pt.size ≤
          (cA m0 + BitVec.ofNat 64 280).toNat
      rw [g.ca (by decide), g.fa (by decide)]
      omega
    · apply Or.inr
      change (stackBelow st.data bufEWExtendStack).toNat + (bufEWExtendStack + 8) ≤
        (stackBelow m0 2016 + BitVec.ofNat 64 1224).toNat
      rw [hsb, g.fa (by decide)]
      change (rspOf m0).toNat - 2016 + 8 + 16 ≤ _
      omega
  refine call_then hpc1 hext hpre1 fun st2 hpc2 hrsp2 hq2 ↦ ?_
  obtain ⟨hret2, hch2, hsv2⟩ := hq2
  rw [hdi, hlen, NativeRustcVm.wordOf_of_wordAt hzero] at hret2
  simp only [UInt64.toNat_zero, zero_add, ite_eq_left hpt] at hret2
  have hp0 : NativeRustcVm.bufEWOf st.data.dmem (cA m0 + BitVec.ofNat 64 280) = [] := by
    simp [NativeRustcVm.bufEWOf, NativeRustcVm.wordOf_of_wordAt hzero, NativeRustcVm.ewsOf]
  have hslice : slice st.data (reg st.data .rsi) (reg st.data .rdx) = pt := by
    rw [hsi]
    exact slice_of h1.pt hlen
  rw [hp0, List.nil_append, hslice] at hret2
  have hso : SameOutside st.data.dmem st2.data.dmem (fun q ↦
      InRange (stackBelow st.data bufEWExtendStack) bufEWExtendStack q ∨
        InRange (cA m0 + BitVec.ofNat 64 280) 488 q) := by
    rw [hdi] at hch2
    exact NativeRustcVm.SameOutside.mono hch2 fun _ hq ↦ hq.symm
  have hb2 := Body.callX hpre (fun _ h ↦ h) hb1 hsv2 hrsp2 (by decide) hso
    (fun _ hq ↦ Or.inl (Or.inr (Or.inl (claim_subrange g (by decide) hq))))
  have hf2 := frSame_call g hb1 (Sk := bufEWExtendStack) (o := 24) (n := 1944)
    (by decide) hso (by decide) (by decide)
    (by
      intro q hq hf
      apply claim_not_fr hpre (claim_subrange g (by decide) hq)
      have hn := g.hN
      have ht := g.top
      rw [Sym.inRange_iff (by rw [g.fa (by decide)]; omega), g.fa (by decide)] at hf
      rw [Sym.inRange_iff (by rw [g.fbN]; omega), g.fbN]
      omega)
  have hs2 : SameOutside st.data.dmem st2.data.dmem (fun q ↦
      InRange (stackBelow m0 3232) 3232 q ∨ InRange (cA m0 + BitVec.ofNat 64 280) 488 q) :=
    NativeRustcVm.SameOutside.mono hso fun _ hq ↦ hq.elim
      (fun hq ↦ Or.inl (cx.inRange_callee (hb1.at_ hpre (fun _ h ↦ h) (by decide)) (by decide) hq).1)
      Or.inr
  have h2 := h1.claim hpre hpt (hf2.sub (by decide) (by decide)) hsv2.2
    (NativeRustcVm.SameOutside.mono hs2 fun _ hq ↦ hq.elim Or.inl
      (fun hq ↦ Or.inr (claim_subrange g (by decide) hq)))
  have hv2 := NativeRustcVm.Layout.EWAt.of_same hv1
    (by simpa using (claim_same hpre (o := 280) (n := 488) (p := 0) (len := 16)
      (by decide) (by decide) (Or.inl (by decide)) hs2)) (by decide)
  have hmu2 := NativeRustcVm.Layout.BufEWAt.of_same hmu1
    (claim_same hpre (o := 280) (n := 488) (p := 16) (len := 264)
      (by decide) (by decide) (Or.inl (by decide)) hs2) (by decide)
  exact at_pc hpc2 (cont st2.data hb2 h2 (by simpa [OkAl, okWord] using hret2.1)
    ⟨hv2, hmu2, hret2.2⟩)

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
