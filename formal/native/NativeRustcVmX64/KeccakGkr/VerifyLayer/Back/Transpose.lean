module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.TailState
public import NativeRustcVmX64.Code.Vm.LinearTranspose.Names

/-! # Transposing the layer weights into the claim's bit weights -/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (DecArea off)

public section

variable [Host] {m0 : MachineData} {a : DecArea} {s s6 : TState} {c : KeccakClaimW}
  {ch b : EW} {pt lp t : Array EW} {k : Nat}

theorem transpose (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    (hlt : ∀ ws, Spec (Labels.label NativeRustcVmX64.Vm.LinearTranspose.entryLabel) (LinearTransposePre ws)
      (LinearTransposePost ws)) (hpt : pt.size ≤ 30) (hlp : lp.size = 11)
    {d : MachineData} (hb : Body m0 (wFront m0) 24 d)
    (h : WMem m0 a c ch b pt lp t s6 1600 d.dmem) (h15 : reg d .r15 = sA m0)
    {R : MachineState → Prop}
    (cont : ∀ d', Body m0 (outs m0) 24 d' → TailLive m0 a c ch b pt lp t s6 d'.dmem →
      Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b80Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b79Offset)⟩ := by
  have g := geo_of hpre
  have hb0 := hb.mono (wFront_outs hpre)
  have cx := ctx hpre (F := 2000) (by decide)
  have hwf := wf0 (pre_stack hpre) hb0 (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b79Offset + b79.length)).toBitVec)
  have hm : Match (envB m0 d [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b79Offset + b79.length)).toBitVec)
      (fr 24) d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb0.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 16) g hb0 hwf (blk hp b79_in_code (by simp [b79])) e79
    (fun _ _ ↦ rfl) hm (by decide +kernel) (hex0 (by decide +kernel)) fun st hm1 hpc1 hb1 _ ↦ ?_
  have hmem1 := h.blk hpre hpt hlp (by decide) hwf hm1 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hw88 := h.fw (88, .ofBitVec (sA m0 + BitVec.ofNat 64 51200))
    (by apply List.mem_append_left; fw_mem)
  have hw120 := h.fw (120, .ofBitVec (sA m0 + BitVec.ofNat 64 25600))
    (by apply List.mem_append_left; fw_mem)
  have hdi : reg st.data .rdi = sA m0 + BitVec.ofNat 64 51200 :=
    (hm1.regs .rdi _ rfl).trans (fload8 hw88)
  have hsi : reg st.data .rsi = sA m0 + BitVec.ofNat 64 76800 := by
    rw [show reg st.data .rsi = _ from hm1.regs .rsi _ rfl]
    change BinOp.apply .add .W64 (reg d .r15) (BitVec.ofNat 64 76800) = _
    rw [add64, h15]
  have hdx : reg st.data .rdx = sA m0 + BitVec.ofNat 64 102400 := by
    rw [show reg st.data .rdx = _ from hm1.regs .rdx _ rfl]
    change BinOp.apply .add .W64 (BitVec.ofNat 64 102400) (reg d .r15) = _
    rw [add64, h15, BitVec.add_comm]
  have hcx : reg st.data .rcx = sA m0 + BitVec.ofNat 64 25600 :=
    (hm1.regs .rcx _ rfl).trans (fload8 hw120)
  have hpre1 : LinearTransposePre (layerWeights (eqKernel lp) b) st.data := by
    refine ⟨cx.stackOk (hb1.at_ hpre (fun _ h ↦ h) (by decide)) (by decide),
      hb1.keep_ro hpre (fun _ h ↦ h) (r := rhoRegion) (by simp) (pre_rho hpre)
        (by change rhoBytes.length ≤ 100; decide +kernel),
      layerWeights_size _ _, ?_, ?_⟩
    · rw [hdi]; exact lw_ewsAt hmem1.lw
    · rw [hdi, hsi, hdx, hcx]; exact transpose_areas hpre hb1
  refine call_then hpc1 (hlt _) hpre1 fun st2 hpc2 hrsp2 hq2 ↦ ?_
  obtain ⟨hw2, hch2, hsv2⟩ := hq2
  rw [hcx] at hw2
  rw [hsi, hdx, hcx] at hch2
  have hX : ∀ q, NativeRustcVm.InAny
      [⟨sA m0 + BitVec.ofNat 64 76800, 25600⟩,
        ⟨sA m0 + BitVec.ofNat 64 102400, 5120⟩,
        ⟨sA m0 + BitVec.ofNat 64 25600, 25600⟩] q →
      InRange (sA m0 + BitVec.ofNat 64 25600) 81920 q := by
    intro q ⟨r, hr, hq⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have hn := g.hs
    rcases hr with rfl | rfl | rfl <;>
      dsimp only [NativeRustcVm.Region.Holds] at hq <;>
      change InRange _ _ q at hq <;>
      rw [Sym.inRange_iff (by rw [g.sa (by decide)]; omega), g.sa (by decide)] at hq <;>
      rw [Sym.inRange_iff (by rw [g.sa (by decide)]; omega), g.sa (by decide)] <;> omega
  have hs2 : SameOutside st.data.dmem st2.data.dmem (fun q ↦
      InRange (stackBelow st.data linearTransposeStack) linearTransposeStack q ∨
        InRange (sA m0 + BitVec.ofNat 64 25600) 81920 q) := by
    apply NativeRustcVm.SameOutside.mono hch2
    intro q ⟨r, hr, hq⟩
    rcases List.mem_cons.mp hr with he | he
    · subst he; exact Or.inl hq
    · exact Or.inr (hX q ⟨r, he, hq⟩)
  have hb2 := Body.callX hpre (fun _ h ↦ h) hb1 hsv2 hrsp2 (by decide) hs2
    (fun _ hq ↦ Or.inl (Or.inr (Or.inr (inRange_mono hq (by decide)))))
  have hf2 := frSame_call g hb1 (Sk := linearTransposeStack) (o := 24) (n := 1944) (by decide) hs2 (by decide)
    (by decide) (fun _ hq ↦ scr_not_fr hpre (by decide) hq (by decide))
  have ht2 := ts_callX hpre (fun _ h ↦ h) hb1 hsv2.2 (by decide) hs2
    (fun _ hq ↦ scr_not_t hpre (by decide) hq) hmem1.ts
  have htail : TailLive m0 a c ch b pt lp t s6 st2.data.dmem :=
    ⟨ht2, FWs.keepR
      (os := [24, 40, 56, 64, 80, 88, 96, 120, 128, 224, 72, 104, 112, 184, 192, 200])
      rfl hf2 (by decide +kernel) hmem1.fw,
      (hf2.sub (o' := 1704) (n' := 264) (by decide) (by decide)).buf hmem1.mu,
      (hf2.sub (o' := 1224) (n' := 480) (by decide) (by decide)).ews hmem1.pt
        (by rw [Array.length_toList]; omega), hw2⟩
  exact at_pc hpc2 (cont st2.data hb2 htail)

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
