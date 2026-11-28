module

public import NativeRustcVmX64.Whir.BasisWEval.ColW
public import NativeRustcVmX64.Code.Vm.ColumnWeight.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `BasisW::eval`: the column claims' loop (x86-64)

`b10` steps to the next claim (`Mid (i + 1) (i + 1)` at `b11`) or ends (`End` at `b21`)
(`b10_step`); the loop from `Mid i i` to `End` (`loop_run`).
-/

namespace NativeRustcVmX64.Whir.BasisWEval

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model LeanVM.Parameters
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVm.Layout NativeRustcVm.Ring
open NativeRustcVmX64.Vm.BasisWEval
open NativeRustcVm.Transcript (off off_add off_zero toNat_off OptEWAt)
open LeanVM.Protocol.Verifier (qkeccak Placement)

public section

variable {m0 : MachineData} {ba : BasisAddrs} {b : BasisW} {v : Vals} [Host] {k : Nat}

/-- **`b10`**: the next claim, or the loop's end. -/
theorem b10_step (hp : Placed code k) (h : In m0 ba b v) {i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b10Offset)) (hm : Mid m0 ba b v i (i + 1) st.data)
    {R : MachineState → Prop}
    (hloop : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b11Offset) →
      Mid m0 ba b v (i + 1) (i + 1) st'.data → Eventually (step1 Host.exe) R st')
    (hend : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b21Offset) → End m0 ba b v st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hf := hm.base.fr
  have hle : v.cs.size ≤ 160 := h.claims.len_le
  have hi := hm.ilt
  obtain ⟨hmid, hmem, hrbx, hr12, hk⟩ := ok_b10
  have hwf := h.wf0 hf (ret := 0)
  refine at_pc hpc (h.block hf hwf (inf hp b10_in_code (by simp [b10])) exit_b10 nofun
    (match_body hf ⟨rfl, trivial⟩) hmid (h0_of_nil hmem) fun st1 hm1 hpc1 hf1 ↦ ?_)
  obtain ⟨hc, hx⟩ := c10_eval (env := envB m0 st.data [] 0) hm.rbx hi hle
  simp only [PcOk, hc] at hpc1
  have hd : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf hmem
  have base1 := hm.base.nil hf1 hwf hm1 hmem
  have k1 : ∀ r ∈ [Reg64.rcx, .rbp, .r13], reg st1.data r = reg st.data r :=
    fun r hr ↦ keeps_reg hm1 hk hr
  have acc1 : Acc m0 ba b (ws v (xpt m0) (i + 1)) st1.data :=
    ⟨hm.acc.w24.nil hwf hm1 hmem, hm.acc.w64.nil hwf hm1 hmem,
      (k1 .r13 (by simp)).trans hm.acc.r13, (k1 .rbp (by simp)).trans hm.acc.rbp⟩
  have w56 := hm.w56.nil hwf hm1 hmem
  by_cases he : i + 1 = v.cs.size
  · simp only [he, decide_true, ↓reduceIte] at hpc1
    rw [hp.label NativeRustcVmX64.Vm.BasisWEval.label_10_at] at hpc1
    exact hend st1 hpc1 ⟨base1, w56, he ▸ acc1⟩
  · simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    rw [show k + NativeRustcVmX64.Vm.BasisWEval.b10Offset + b10.length = k + NativeRustcVmX64.Vm.BasisWEval.b11Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.BasisWEval.b10_next]] at hpc1
    refine hloop st1 hpc1 {
      base := base1
      w56 := w56
      w104 := hm.w104.nil hwf hm1 hmem
      acc := acc1
      ilt := by omega
      rbx := by rw [reg_eval hm1 hrbx]; exact hx
      r12 := by
        rw [reg_eval hm1 hr12]
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
        rw [show (envB m0 st.data [] 0).regs .r12 = reg st.data .r12 from rfl, hm.r12]
        apply BitVec.eq_of_toNat_eq
        simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat, show Width.W64.bits = 64 from rfl]
        omega
      rcx := (k1 .rcx (by simp)).trans hm.rcx }

/-- **The loop**, from `Mid i i` at `b11` to `End` at `b21`. -/
theorem loop_run (hp : Placed code k) (h : In m0 ba b v)
    (hcw : Spec (Labels.label NativeRustcVmX64.Vm.ColumnWeight.entryLabel) ColumnWeightPre ColumnWeightPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {R : MachineState → Prop}
    (hend : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b21Offset) → End m0 ba b v st'.data →
      Eventually (step1 Host.exe) R st') :
    ∀ {n i : Nat} {st : MachineState}, n = v.cs.size - i → st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b11Offset) →
      Mid m0 ba b v i i st.data → Eventually (step1 Host.exe) R st := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i st hn hpc hm
    have hi := hm.ilt
    have next : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b10Offset) →
        Mid m0 ba b v i (i + 1) st'.data → Eventually (step1 Host.exe) R st' := fun st' hpc' hm' ↦
      b10_step hp h hpc' hm'
        (fun st'' hpc'' hm'' ↦ ih (v.cs.size - (i + 1)) (by omega) rfl hpc'' hm'') hend
    exact col_head hp h hpc hm next fun st' pl hpc' ha ↦ col_weight hp h hcw hmul hpc' ha next

end

end NativeRustcVmX64.Whir.BasisWEval
