module

public import NativeRustcVmArm.Ring.Weight.Step
public import NativeRustcVmArm.Ring.OptOut

/-!
# `ring_weight`: the epilogue

`b26` stores the tag `1` and the total (X21, X23) at `out`, whose address the frame keeps at
byte `8`, and returns (`stepExit`, from `Done`).
-/

namespace NativeRustcVmArm.Ring.Weight

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Vm.RingWeight

@[expose] public section

/-- **At the epilogue**: the frame, the total in X21, X23. -/
structure Done (m0 m : MachineData) : Prop where
  fr : WFr m0 m
  val : (⟨m.regs.getXReg .X21, m.regs.getXReg .X23⟩ : EW) = ringWeight (rL m0) (qL m0) (cL m0)

end

public section

variable {m0 : MachineData} [Host] {k : Nat}

/-- **The epilogue** (`b26`): `ring_weight`'s postcondition, back at the caller. -/
theorem stepExit (hp : Placed code k) (h : RingWeightPre m0) {m : MachineData} (hD : Done m0 m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m0 ∧ RingWeightPost m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b26Offset)⟩ := by
  have hfr := hD.fr
  have ho := h.2.2.2.2.2
  have hap : Apart m0.regs.X0.toBitVec 24 (fb m0) 688 := apart_frame (hN h) (by decide) ho.2
  let rs : List (BitVec 64 × Nat) := [(fb m0, 688), (m0.regs.X0.toBitVec, 24)]
  have hwf : (Env.ofMachine m rs).WF :=
    Env.wf_of ⟨⟨fun i hi ↦ hfr.kept _ (frame_mapped h.1 (by decide) i hi), fbw h⟩,
      ⟨fun i hi ↦ hfr.kept _ (ho.1.1 i hi), ho.1.2⟩, trivial⟩ (List.pairwise_pair.mpr hap.symm)
  have hx0 : (Env.ofMachine m rs).load 0 8 8 = m0.regs.X0.toBitVec := by
    refine load_word ?_
    have := hfr.slots (8, .X0) (by simp [slots])
    exact this
  have hm : Match (Env.ofMachine m rs) exitS m :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.1 (by decide) (by decide), rfl, nofun, trivial⟩
      (by
        rw [hfr.sp]
        show fb m0 = fb m0 + BitVec.ofInt 64 (0 : Nat)
        rw [ofInt_lit, NativeRustcVm.addr_add_zero]) trivial trivial trivial
      ⟨by
        show (Env.ofMachine m rs).load 0 8 8 = m0.regs.X0.toBitVec + BitVec.ofInt 64 (0 : Nat)
        rw [hx0, ofInt_lit, NativeRustcVm.addr_add_zero], trivial⟩
  refine exec_then (hb b26_in_code (by simp [b26]) hp) run_b26 hwf hm fun st hm1 hpc ↦ ?_
  obtain ⟨hret, hS⟩ := hfr.exit hm1 hwf (by decide)
  refine .done _ ⟨by simp only [PcOk] at hpc; rw [hpc, hret], ⟨?_, ?_⟩, ?_, hS⟩
  · have w := hm1.bytesAt_write (r := 1) (o := 0) (n := 8) (b := m0.regs.X0.toBitVec) (sz := 24)
      rfl (by omega) (v := .lit 1) (by decide)
    rw [wordBytes_reg, NativeRustcVm.addr_add_zero] at w
    exact w
  · have w := ew_write hm1 (r := 1) (o := 8) (b := m0.regs.X0.toBitVec) (sz := 24) rfl (by omega)
      (v0 := .reg .X21) (v1 := .reg .X23) (by decide) (by decide)
    simp only [Sym.eval, Env.ofMachine_regs, UInt64.ofBitVec_toBitVec] at w
    rw [hD.val] at w
    exact w
  · have h2 := outOnly_same hm1 hwf rfl (by decide)
    intro q hq
    rw [h2 q fun h ↦ hq (.inl h)]
    exact hfr.same q fun h ↦ h.elim (fun h ↦ hq (.inr h)) id

end

end NativeRustcVmArm.Ring.Weight
