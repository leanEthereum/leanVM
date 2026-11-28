module

public import NativeRustcVmArm.Code.Vm.RingWeight.Names
public import NativeRustcVmArm.Ring.Claim.Basic

/-!
# `ring_claim_weight`: `ring_weight`

From `Mid1` (after `eq_eval_fn`), `b1`: `eq_above(p, x)` kept in X20, X21, `ring_weight(r,
x.get(..vc).unwrap_or(x), coefficients)` into the frame's `Option<EW>` at byte `8` (`Mid2`).
-/

namespace NativeRustcVmArm.Ring.Claim

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Vm.RingClaimWeight NativeRustcVmArm.Whir NativeRustcVm.Ring

@[expose] public section

/-- `ring_weight(r, x.get(..vc).unwrap_or(x), coefficients)`. -/
def wOf (m0 : MachineData) : EW :=
  ringWeight (slice m0 m0.regs.X3 m0.regs.X4) ((xOf m0).extract 0 m0.regs.X1.toNat)
    (arr m0 m0.regs.X5 coeffCount)

/-- **After `ring_weight`**: the frame, the output in X19, `eq_above(p, x)` in X20, X21, `Some`
of the ring weight at the frame's byte `8`. -/
structure Mid2 (m0 m : MachineData) : Prop where
  fr : CFr m0 m
  x19 : m.regs.getXReg .X19 = m0.regs.X0
  x20 : m.regs.getXReg .X20 = (eqOf m0).c0
  x21 : m.regs.getXReg .X21 = (eqOf m0).c1
  w : OptEWAt m.dmem (fb m0 + BitVec.ofNat 64 8) (some (wOf m0))

end

public section

variable {m0 : MachineData} [Host] {k : Nat}

/-- **`ring_weight`** (`b1`). -/
theorem stepWeight (hp : Placed code k) (h : RingClaimWeightPre m0)
    (hrw : Spec (Labels.label NativeRustcVmArm.Vm.RingWeight.entryLabel) RingWeightPre RingWeightPost)
    {R : MachineState → Prop} {m1 : MachineData} (hM : Mid1 m0 m1)
    (cont : ∀ m2, Mid2 m0 m2 → Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.RingClaimWeight.b2Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m1, Host.addrOf (k + NativeRustcVmArm.Vm.RingClaimWeight.b1Offset)⟩ := by
  have hwf := envM_wf h hM.fr
  have hm := matchM h hM.fr
  have hN' := hN h
  rw [stack_eq] at hN'
  refine exec_then (hb b1_in_code (by simp [b1]) hp) run_b1 hwf hm fun st hm2 hpc ↦ ?_
  have hfr2 : CFr m0 st.data :=
    hM.fr.ofBlock hm hm2 hwf rfl rfl rfl fun r hr ↦ by
      simp only [keep, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩
  have e0 : st.data.regs.X0.toBitVec = fb m0 + BitVec.ofNat 64 8 := by
    rw [show st.data.regs.X0 = st.data.regs.getXReg .X0 from rfl, hm2.regs .X0 (.ptr 0 8) rfl]
    simp [Sym.eval]
  have e1 : st.data.regs.X1 = m0.regs.X3 :=
    Column.reg_of hm2 (r := .X1) (v := .reg .X25) rfl (by simp [Sym.eval, hM.x25])
  have e2 : st.data.regs.X2 = m0.regs.X4 :=
    Column.reg_of hm2 (r := .X2) (v := .reg .X24) rfl (by simp [Sym.eval, hM.x24])
  have e3 : st.data.regs.X3 = m0.regs.X6 :=
    Column.reg_of hm2 (r := .X3) (v := .reg .X22) rfl (by simp [Sym.eval, hM.x22])
  have e4 : st.data.regs.X4.toNat = min m0.regs.X1.toNat m0.regs.X7.toNat := by
    rw [show st.data.regs.X4 = st.data.regs.getXReg .X4 from rfl,
      Column.reg_of hm2 (r := .X4) (v := .reg .X26) rfl rfl]
    exact hM.x26
  have e5 : st.data.regs.X5 = m0.regs.X5 :=
    Column.reg_of hm2 (r := .X5) (v := .reg .X23) rfl (by simp [Sym.eval, hM.x23])
  have hr := h.2.2.2.1
  have hc := h.2.2.2.2.1
  have hx := h.2.2.2.2.2.1
  have hfr : Readable m0 (fb m0) 112 := ⟨frame_mapped h.1 (by decide), fbw h⟩
  have hpre : RingWeightPre st.data := by
    unfold RingWeightPre SliceOk ArrOk OptOutOk
    rw [e0, e1, e2, e3, e4, e5]
    refine ⟨hfr2.stackOk h.1 (by decide) (by decide), h.2.1,
      ⟨readable_of hfr2 hr.1, hfr2.apart (hN h) hr.2 (by decide)⟩,
      ⟨Readable.mono (readable_of hfr2 hx.1) (by omega), ?_⟩,
      ⟨readable_of hfr2 hc.1, hfr2.apart (hN h) hc.2 (by decide)⟩,
      Readable.sub (readable_of hfr2 hfr) (by omega),
      apart_callee h hfr2 (by decide) (by decide)⟩
    have := hfr2.apart (hN h) hx.2 (N' := ringWeightStack) (by decide)
    unfold OffStack Apart at *
    omega
  refine Fr.leafIn hfr2 (hN h) (N' := ringWeightStack) (lo := 8) (n := 24) (by decide)
    (by decide) keep_cs (by decide) (fun _ h ↦ h.elim) hrw hpc hpre
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq ↦ hq.elim
      (fun hq ↦ .inr (.inl (e0 ▸ hq))) .inl, hq.2.2⟩)
    fun m2 hfr3 hq hcs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingClaimWeight.b1Offset + b1.length = k + NativeRustcVmArm.Vm.RingClaimWeight.b2Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingClaimWeight.b1_next]]
  refine cont m2 ⟨hfr3, ?_, ?_, ?_, ?_⟩
  · rw [hcs .X19 rfl, ← hM.x19]
    exact Column.reg_of hm2 (v := .reg .X19) rfl rfl
  · rw [hcs .X20 rfl, Column.reg_of hm2 (r := .X20) (v := .reg .X0) rfl rfl]
    exact congrArg EW.c0 hM.ret
  · rw [hcs .X21 rfl, Column.reg_of hm2 (r := .X21) (v := .reg .X1) rfl rfl]
    exact congrArg EW.c1 hM.ret
  · have harr : arr st.data m0.regs.X5 coeffCount = arr m0 m0.regs.X5 coeffCount := by
      unfold arr
      rw [NativeRustcVm.ewsOf_congr fun j hj ↦ same_of h hfr2 hc.2 hc.1.2 hj]
    have hw := hq.1
    rw [e0, e1, e2, e5, harr, slice_same h hfr2 hr, e3, slice_low e4,
      slice_same h hfr2 hx] at hw
    exact hw

end

end NativeRustcVmArm.Ring.Claim
