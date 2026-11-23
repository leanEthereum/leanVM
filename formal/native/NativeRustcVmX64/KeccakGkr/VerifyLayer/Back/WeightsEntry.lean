module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.WeightsState

/-! # Initialising the layer weights loop -/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (DecArea off)

public section

variable [Host] {m0 : MachineData} {a : DecArea} {s s6 : TState} {c : KeccakClaimW}
  {ch b : EW} {pt lp t : Array EW} {k : Nat}

theorem weights_entry (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    {d : MachineData} (h : C6 m0 a c ch b pt lp t s6 d) {R : MachineState → Prop}
    (cont : ∀ d', WHead m0 a c ch b pt lp t s6 0 d' →
      Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b74Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b69Offset)⟩ := by
  have g := geo_of hpre
  have hwf := wf0 (pre_stack hpre) h.body (vars := fun _ ↦ 0) (ret := 0)
  have hm : Match (envB m0 d [] (fun _ ↦ 0) 0) (fr 24) d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨h.body.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 24) g h.body hwf (blk hp b69_in_code (by simp [b69])) e69 nofun hm
    (by decide +kernel) (hex0 (by decide +kernel)) fun st hm' hpc hb _ ↦ ?_
  have hfr := frSame_blk (o := 1224) (n := 744) hwf hm' (by decide +kernel)
    (by decide) (by decide +kernel)
  have hkeep := FWs.blkO (os := [32, 48, 64, 80, 96, 120, 128, 224]) (L :=
      [(32, (kap ch).c0), (48, (kap ch).c1), (64, .ofBitVec (BitVec.ofNat 64 c.point.size)),
       (80, .ofBitVec (sA m0)), (96, .ofBitVec (cA m0)), (120, .ofBitVec (sA m0 + 25600#64)),
       (128, .ofBitVec (cA m0 + 280#64)), (224, .ofBitVec (cA m0 + 16#64))])
      rfl hwf hm' (by decide +kernel) (by decide +kernel)
      (h.fw.set (fun q hq ↦ by
        left
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> fw_mem))
  have htw := FWs.blkO (os := [72, 104, 112, 184, 192, 200]) rfl hwf hm'
    (by decide +kernel) (by decide +kernel) h.tw
  have hw56 := (frSame_blk (o := 56) (n := 8) hwf hm' (by decide +kernel)
    (by decide) (by decide +kernel)).word h.w56 (by decide)
  have hw24 : NativeRustcVm.WordAt st.data.dmem (off (stackBelow m0 2016) 24) b.c0 :=
    fwW hm' (o := 24) (v := .reg .rax) rfl rfl (by decide) (by decide +kernel) h.rax
  have hw40 : NativeRustcVm.WordAt st.data.dmem (off (stackBelow m0 2016) 40) b.c1 :=
    fwW hm' (o := 40) (v := .reg .rdx) rfl rfl (by decide) (by decide +kernel) h.rdx
  have hw88 : NativeRustcVm.WordAt st.data.dmem (off (stackBelow m0 2016) 88)
      (.ofBitVec (sA m0 + BitVec.ofNat 64 51200)) :=
    fwW hm' rfl rfl (by decide) (by decide +kernel) (by
      change BinOp.apply .add .W64 (reg d .r15) (BitVec.ofNat 64 51200) = _
      rw [add64, h.r15])
  have hfw : FWs m0 st.data.dmem (weightWords m0 c t b) := by
    apply FWs.append
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hw24
      · exact hw40
      · exact hw56
      · exact hkeep _ (by fw_mem)
      · exact hkeep _ (by fw_mem)
      · exact hw88
      · exact hkeep _ (by fw_mem)
      · exact hkeep _ (by fw_mem)
      · exact hkeep _ (by fw_mem)
      · exact hkeep _ (by fw_mem)
    · exact htw
  have hh : WHead m0 a c ch b pt lp t s6 0 st.data :=
    ⟨hb, ⟨ts_blk0 hpre hwf hm' (by decide +kernel) (by decide +kernel) h.ts, hfw,
      (hfr.sub (o' := 1704) (n' := 264) (by decide) (by decide)).buf h.mu,
      (hfr.sub (o' := 1224) (n' := 480) (by decide) (by decide)).ews h.hpt
        (by rw [Array.length_toList, h.psz]; have := (claimPt hpre (fun _ h ↦ h) h.body).1; omega),
      scr_blk0E hpre hwf hm' (by decide +kernel) (by decide +kernel) (by decide)
        (by rw [eqK_len h.lsz]; decide) h.eq,
      fun _ hi ↦ (Nat.not_lt_zero _ hi).elim⟩, by decide,
      hm'.regs .rbp _ rfl, hm'.regs .rbx _ rfl,
      (hm'.regs .r15 _ rfl).trans h.r15, (hm'.regs .r13 _ rfl).trans h.r13⟩
  simp only [PcOk] at hpc
  rw [lbl hp b74_in_code rfl] at hpc
  exact at_pc hpc (cont st.data hh)

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
