module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.WeightsState
public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.TailAreas
public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.Return
public import NativeRustcVm.KeccakGkr.Transpose

/-! # Live values between the transpose and the claim update -/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea TStateAt off)

@[expose] public section

structure TailLive (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (ch b : EW)
    (pt lp t : Array EW) (s6 : TState) (d : DataMem) : Prop where
  ts : TStateAt d (tA m0) a s6
  fw : FWs m0 d (weightWords m0 c t b)
  mu : NativeRustcVm.BufEWAt d (off (stackBelow m0 2016) 1704) 16
    (keccakInstanceWeights ch).toList
  pt : NativeRustcVm.EWsAt d (off (stackBelow m0 2016) 1224) pt.toList
  weights : NativeRustcVm.EWsAt d (lA m0)
    (keccakLinearTranspose (layerWeights (eqKernel lp) b)).toList

end

public section

variable [Labels] {m0 : MachineData} {a : DecArea} {s s6 : TState} {c : KeccakClaimW}
  {ch b : EW} {pt lp t : Array EW}

theorem TailLive.blk (hpre : VerifyLayerPre a s c m0) {d d' : MachineData}
    (h : TailLive m0 a c ch b pt lp t s6 d.dmem) (hpt : pt.size ≤ 30)
    {ex : List (BitVec 64 × Nat)} {ret : BitVec 64} {S : SState}
    (hwf : (envB m0 d ex (fun _ ↦ 0) ret).WF)
    (hm : Match (envB m0 d ex (fun _ ↦ 0) ret) S d')
    (h0 : S.mem.all (fun w ↦ w.r == 0) = true) (hbr : belowRet 2016 S = true)
    (hin : writesIn S = true) (hmiss : missB 24 1944 S = true) :
    TailLive m0 a c ch b pt lp t s6 d'.dmem := by
  have hf := frSame_blk hwf hm hin (show 24 + 1944 ≤ 2024 by decide) hmiss
  refine ⟨ts_blk0 hpre hwf hm h0 hbr h.ts,
    FWs.keepR (os := [24, 40, 56, 64, 80, 88, 96, 120, 128, 224, 72, 104, 112, 184, 192, 200])
      rfl hf (by decide +kernel) h.fw,
    (hf.sub (o' := 1704) (n' := 264) (by decide) (by decide)).buf h.mu,
    (hf.sub (o' := 1224) (n' := 480) (by decide) (by decide)).ews h.pt
      (by rw [Array.length_toList]; omega),
    scr_blk0E hpre hwf hm h0 hbr (by decide) ?_ h.weights⟩
  rw [Array.length_toList, NativeRustcVm.KeccakGkr.linearTranspose_size']
  decide

theorem TailLive.leaf (hpre : VerifyLayerPre a s c m0) {d d' : MachineData}
    (h : TailLive m0 a c ch b pt lp t s6 d.dmem) (hpt : pt.size ≤ 30)
    (hb : Body m0 (outs m0) 16 d) (hf : FrSame m0 d.dmem d'.dmem 24 2000)
    (ht : TStateAt d'.dmem (tA m0) a s6) {Sk : Nat} (hSk : 2000 + Sk ≤ 3232)
    (hso : SameOutside d.dmem d'.dmem (InRange (stackBelow d Sk) Sk)) :
    TailLive m0 a c ch b pt lp t s6 d'.dmem := by
  refine ⟨ht,
    FWs.keepR (os := [24, 40, 56, 64, 80, 88, 96, 120, 128, 224, 72, 104, 112, 184, 192, 200])
      rfl hf (by decide +kernel) h.fw,
    (hf.sub (o' := 1704) (n' := 264) (by decide) (by decide)).buf h.mu,
    (hf.sub (o' := 1224) (n' := 480) (by decide) (by decide)).ews h.pt
      (by rw [Array.length_toList]; omega),
    scr_call hpre (fun _ h ↦ h) hb hSk
      (NativeRustcVm.SameOutside.mono hso fun _ hq ↦ Or.inl hq) (X := fun _ ↦ False)
      (by decide) ?_ (fun _ hq ↦ hq.elim) h.weights⟩
  rw [Array.length_toList, NativeRustcVm.KeccakGkr.linearTranspose_size']
  decide

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
