module

public import NativeRustcVmArm.Code.Vm.VerifyLayer.Names
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.Defs

/-!
# `verify_layer`: the exit

At `.LVerifyLayer_38` (`b70`) with X0 the verdict (`exit`), at `.LVerifyLayer_37` (`b69`, X0
cleared) on a rejected run (`reject`): the epilogue restores the entry's registers and returns.
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVmArm.Vm.VerifyLayer
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (tstateBytes TStateAt DecArea)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt claimBytes)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- A block of the function in the program. -/
theorem blk {b : List Directive} {o : Nat} (hp : Placed code k) (h : b.IsInfixAt code o)
    (hne : b ≠ []) : b.IsInfixAt Host.prog (k + o) :=
  h.trans hp.1 hne

omit [Host] in
/-- An element of an infix. -/
theorem getElem?_of_infix {α : Type} {b l : List α} {o i : Nat} (h : b.IsInfixAt l o)
    (hi : i < b.length) : l[o + i]? = b[i]? := by
  obtain ⟨t, ht⟩ := h
  rw [show l[o + i]? = (l.drop o)[i]? by simp [List.getElem?_drop], ← ht,
    List.getElem?_append_left hi]

/-- `.LVerifyLayer_38`'s address. -/
theorem label38 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.VerifyLayer.label_38 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b70Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.VerifyLayer.b70Offset) NativeRustcVmArm.Vm.VerifyLayer.label_38_at

/-- `.LVerifyLayer_37`'s address. -/
theorem label37 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.VerifyLayer.label_37 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b69Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.VerifyLayer.b69Offset) NativeRustcVmArm.Vm.VerifyLayer.label_37_at

/-- The frame's environment of a body is well formed. -/
theorem wf_fr (hpre : VerifyLayerPre a s c m0) {m : MachineData} (hb : Body m0 m) :
    (Env.ofMachine m [(base m0 2032, 2032)]).WF :=
  Bus.wf_frame hpre.1 (by decide) hb.kept

/-- A body's state matches `frS`. -/
theorem match_fr (hpre : VerifyLayerPre a s c m0) {m : MachineData} (hb : Body m0 m) :
    Match (Env.ofMachine m [(base m0 2032, 2032)]) frS m :=
  Bus.match_frame hpre.1 (by decide) (by decide) hb.sp

omit [Host] in
/-- **The writes**: the stack and the outputs are the contract's regions. -/
theorem writes_of (g : Geo m0) {m : MachineData} (hb : Body m0 m) :
    Writes m0 m verifyLayerStack
      [⟨tA m0, tstateBytes⟩, ⟨cA m0, claimBytes⟩, layerRegion (sA m0)] := by
  refine NativeRustcVm.SameOutside.mono hb.same fun q hq ↦ ?_
  have := g.hN; have := Geo.sp_lt m0; have hb' := g.bN
  rcases hq with hq | hq | hq | hq | hq
  · exact ⟨stackRegion m0 verifyLayerStack, List.mem_cons_self, hq⟩
  · have h1 : InRange (base m0 2032) 2032 q := by unfold InRange at hq ⊢; omega
    refine ⟨stackRegion m0 verifyLayerStack, List.mem_cons_self, ?_⟩
    show NativeRustcVm.InRange (base m0 verifyLayerStack) verifyLayerStack q
    rw [stack_eq]
    exact Bus.frame_inRange (by omega) (by decide) h1
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hq⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), hq⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)), hq⟩

/-- **The exit**, at `.LVerifyLayer_38`. -/
theorem exit (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b70Offset)) (hb : Body m0 st.data)
    (hx0 : st.data.regs.X0 = okWord (runL s c m0).isSome)
    (hok : ∀ c' s', runL s c m0 = some (c', s') → TStateAt st.data.dmem (tA m0) a s' ∧
      ClaimAt st.data.dmem (cA m0) c' ∧ WeightsAt st.data.dmem (sA m0 + BitVec.ofNat 64 25600) c') :
    Eventually (step1 Host.exe) (Goal a s c m0) st := by
  have hwf := wf_fr hpre hb
  refine exec_at (blk hp b70_in_code (by simp [b70])) e70 hwf hpc (match_fr hpre hb)
    fun st' hm hpc' ↦ Eventually.done _ ?_
  obtain ⟨hret, hsv⟩ := Fr.exit hb hm hwf (by decide)
  have hd : st'.data.dmem = st.data.dmem := hm.dmem_eq hwf rfl
  have h0 : st'.data.regs.X0 = st.data.regs.X0 := UInt64.toBitVec_inj.mp (hm.regs .X0 _ rfl)
  refine ⟨hpc'.trans hret, h0.trans hx0, fun c' s' hr ↦ ?_, ?_, hsv⟩
  · rw [hd]; exact hok c' s' hr
  · rw [show Writes m0 st'.data = Writes m0 st.data from by
      unfold Writes; rw [hd]]
    exact writes_of (geo_of hpre) hb

/-- **A rejection**, at `.LVerifyLayer_37`: X0 cleared, then the exit. -/
theorem reject (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b69Offset)) (hb : Body m0 st.data) (hr : runL s c m0 = none) :
    Eventually (step1 Host.exe) (Goal a s c m0) st := by
  have hwf := wf_fr hpre hb
  refine exec_at (blk hp b69_in_code (by simp [b69])) e69 hwf hpc (match_fr hpre hb)
    fun st' hm hpc' ↦ ?_
  have hd : st'.data.dmem = st.data.dmem := hm.dmem_eq hwf rfl
  have hb' : Body m0 st'.data := Fr.ofBlock hb (match_fr hpre hb) hm hwf rfl rfl rfl
    (fun r hr ↦ by cases hr)
  refine exit hp hpre hpc' hb' ?_ fun c' s' h ↦ by rw [hr] at h; cases h
  rw [hr]
  apply UInt64.toBitVec_inj.mp
  rw [show st'.data.regs.X0 = st'.data.regs.getXReg .X0 from rfl, hm.regs .X0 _ rfl]
  rfl

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
