module

public import NativeRustcVmArm.Code.Vm.ColumnWeight.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Whir.BasisWEval.ColW

/-!
# `BasisW::eval`: the column claims' loop

`b9` steps to the next claim (`Loop (i + 1)` at `b10`) or ends (`End` at `b19`) (`b9_step`); the
loop from `Loop i` to `End` (`loop_run`).
-/

namespace NativeRustcVmArm.Whir.BasisWEval

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model LeanVM.Parameters
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVm.Layout NativeRustcVm.Ring
open NativeRustcVm.KeccakGkr NativeRustcVmArm.Vm.BasisWEval
open LeanVM.Protocol.Verifier (qkeccak Placement)

public section

variable {m0 : MachineData} {ba : BasisAddrs} {b : BasisW} {v : Vals} [Host] {k : Nat}

/-- **`b9`**: the next claim, or the loop's end. -/
theorem b9_step (hp : Placed code k) (h : In m0 ba b v) {i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b9Offset)) (ha : AtB9 m0 ba b v i st.data)
    {R : MachineState → Prop}
    (hloop : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b10Offset) →
      Loop m0 ba b v (i + 1) st'.data → Eventually (step1 Host.exe) R st')
    (hend : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b19Offset) → End m0 ba b v st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hle := h.claims.len_le
  unfold claimCap at hle
  have hi := ha.ilt
  refine ha.keep.fr.regsBlock (inf hp b9_in_code (by simp [b9])) run_b9 hpc rfl rfl (by rfl)
    fun st1 hf1 hd1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  have hk1 : ∀ r : XReg, r ≠ .X19 → r ≠ .X20 → st1.data.regs.getXReg r = st.data.regs.getXReg r :=
    fun r h19 h20 ↦ reg_of hm1 (v := .reg r) (by cases r <;> first | rfl | contradiction) rfl
  have h19 : (st.data.regs.getXReg .X19).toBitVec.toNat = 608 * (v.cs.size - i) := ha.x19
  have hx19 : (st1.data.regs.getXReg .X19).toNat = 608 * (v.cs.size - (i + 1)) := by
    rw [← UInt64.toNat_toBitVec, reg_val hm1 (r := .X19) rfl]
    simp only [Sym.eval, BinOp.apply, Sym.ext_W64, Sym.low_W64, Env.ofMachine_regs]
    rw [BitVec.toNat_sub, h19, show (608#64).toNat = 608 from rfl]
    omega
  have hx20 : st1.data.regs.X20.toBitVec = ba.claims + BitVec.ofNat 64 (24 + 608 * (i + 1)) := by
    refine (reg_val hm1 (r := .X20) rfl).trans ?_
    simp only [Sym.eval, BinOp.apply, Sym.ext_W64, Sym.low_W64, Env.ofMachine_regs]
    rw [show st.data.regs.getXReg .X20 = st.data.regs.X20 from rfl, ha.x20,
      show (608#64 : BitVec 64) = BitVec.ofNat 64 608 from rfl, NativeRustcVm.addr_add_add]
    rw [show 24 + 608 * i + 608 = 24 + 608 * (i + 1) by omega]
  have hcond : SBool.eval (Env.ofMachine st.data []) (SBool.cmp CmpOp.eq RegWidth.W64
      (Sym.reg .X19) (Sym.lit 608)) = decide (i + 1 = v.cs.size) := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, Sym.low_W64, Env.ofMachine_regs, bv_beq_toNat,
      h19, show (608#64).toNat = 608 from rfl]
    by_cases hc : i + 1 = v.cs.size
    · simp only [hc, decide_true, decide_eq_true_eq]; omega
    · simp only [hc, decide_false, decide_eq_false_iff_not]; omega
  rw [hcond] at hpc1
  have keep1 : Keep m0 ba st1.data := ⟨hf1, (hk1 .X21 (by decide) (by decide)).trans ha.keep.x21,
    (hk1 .X22 (by decide) (by decide)).trans ha.keep.x22,
    (hk1 .X23 (by decide) (by decide)).trans ha.keep.x23⟩
  have acc1 : Acc ba b (ws v (xpt m0) (i + 1)) st1.data :=
    ⟨(hk1 .X24 (by decide) (by decide)).trans ha.acc.x24,
      (hk1 .X25 (by decide) (by decide)).trans ha.acc.x25,
      by rw [show st1.data.regs.X28 = st1.data.regs.getXReg .X28 from rfl,
           hk1 .X28 (by decide) (by decide)]; exact ha.acc.x28,
      by rw [show st1.data.regs.X29 = st1.data.regs.getXReg .X29 from rfl,
           hk1 .X29 (by decide) (by decide)]; exact ha.acc.x29⟩
  by_cases hc : i + 1 = v.cs.size
  · simp only [hc, decide_true, ↓reduceIte] at hpc1
    rw [hp.label (j := NativeRustcVmArm.Vm.BasisWEval.b19Offset) NativeRustcVmArm.Vm.BasisWEval.label_14_at] at hpc1
    exact hend st1 hpc1 ⟨keep1, hc ▸ acc1⟩
  · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    exact hloop st1 hpc1 ⟨keep1, acc1, by omega, hx19, hx20⟩

/-- **The loop**, from `Loop i` at `b10` to `End` at `b19`. -/
theorem loop_run (hp : Placed code k) (h : In m0 ba b v)
    (hcw : Spec (Labels.label NativeRustcVmArm.Vm.ColumnWeight.entryLabel) ColumnWeightPre ColumnWeightPost)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {R : MachineState → Prop}
    (hend : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b19Offset) → End m0 ba b v st'.data →
      Eventually (step1 Host.exe) R st') :
    ∀ {d i : Nat} {st : MachineState}, d = v.cs.size - i → st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b10Offset) →
      Loop m0 ba b v i st.data → Eventually (step1 Host.exe) R st := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro i st hd hpc hl
    have hi := hl.ilt
    have next : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b9Offset) →
        AtB9 m0 ba b v i st'.data → Eventually (step1 Host.exe) R st' := fun st' hpc' ha ↦
      b9_step hp h hpc' ha
        (fun st'' hpc'' hl'' ↦ ih (v.cs.size - (i + 1)) (by omega) rfl hpc'' hl'') hend
    exact col_head hp h hpc hl next fun st' pl hpc' ha ↦ col_weight hp h hcw hmul hpc' ha next

end

end NativeRustcVmArm.Whir.BasisWEval
