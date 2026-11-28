module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EWSqIter.Names
public import NativeRustcVmArm.Code.Vm.PolyEval.Names
public import NativeRustcVmArm.Ring.Target.ChainB

/-!
# `ring_target`: the sum, the last turn, the epilogue

From `M_7` in X0, X1 (`b33`): the sum `M_1 + … + M_7` into X20, X19 and `P_0` (`poly_eval`),
`T_0` (`b34`), `M_0` (`b35`), the result `M_0 + (M_1 + … + M_7)` returned (`b36`): `ringTarget`.
-/

namespace NativeRustcVmArm.Ring.Target

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Vm.RingTarget

public section

variable {m0 : MachineData}

instance : Std.Associative (α := EW) (· + ·) := ⟨EW.add_assoc'⟩
instance : Std.Commutative (α := EW) (· + ·) := ⟨EW.add_comm'⟩

/-- **The result**: `M_0 + (M_1 + … + M_7)` is `ringTarget`. -/
theorem result_eq : mV m0 0 + sV m0 = ringTarget (sl m0) (fl m0) (gl m0) := by
  rw [ringTarget_eq]
  show _ = 0 + mV m0 7 + mV m0 6 + mV m0 5 + mV m0 4 + mV m0 3 + mV m0 2 + mV m0 1 + mV m0 0
  rw [EW.zero_add', sV]
  ac_rfl

theorem tv_s0 : tv m0 sI = tv m0 (mI 1) ^^^ (tv m0 (mI 2) ^^^ (tv m0 (mI 3) ^^^ (tv m0 (mI 4) ^^^
    (tv m0 (mI 5) ^^^ (tv m0 (mI 6) ^^^ tv m0 (mI 7)))))) := rfl

theorem tv_s1 : tv m0 (sI + 1) = tv m0 (mI 1 + 1) ^^^ (tv m0 (mI 2 + 1) ^^^ (tv m0 (mI 3 + 1) ^^^
    (tv m0 (mI 4 + 1) ^^^ (tv m0 (mI 5 + 1) ^^^ (tv m0 (mI 6 + 1) ^^^ tv m0 (mI 7 + 1)))))) := rfl

theorem eval_eor [Labels] (env : Env) (a b : Sym) :
    Sym.eval env (.bin .eor .W64 a b) = Sym.eval env a ^^^ Sym.eval env b := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]

/-- A location's value from the description. -/
theorem Holds.ev [Labels] {rs : List (BitVec 64 × Nat)} {V : Nat → UInt64}
    {D : List (Sym × Nat)} {m : MachineData} (hH : Holds rs V D m) {s : Sym} {n : Nat}
    (h : D.contains (s, n) = true) : s.eval (Env.ofMachine m rs) = (V n).toBitVec := by
  rw [← hH _ (List.contains_iff_mem.mp h)]
  rfl

theorem sD_regs : ∀ p ∈ sD, ∃ r, p.1 = .reg r ∧ calleeSaved r = true := by
  intro p hp
  simp only [sD, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩

/-- **The sum** `b33` computes into X20, X19. -/
theorem sum_holds [Labels] {m st : MachineData} {S' : SState}
    (hH : Holds (rsT m0) (tv m0) ((.reg .X0, mI 7) :: (.reg .X1, mI 7 + 1) :: K32) m)
    (hm1 : Match (Env.ofMachine m (rsT m0)) S' st)
    (h20 : S'.reg .X20 = some (.bin .eor .W64 (.load 0 8 8) (.bin .eor .W64 (.reg .X19)
      (.bin .eor .W64 (.reg .X25) (.bin .eor .W64 (.reg .X28) (.bin .eor .W64 (.reg .X21)
        (.bin .eor .W64 (.reg .X22) (.reg .X0))))))))
    (h19 : S'.reg .X19 = some (.bin .eor .W64 (.reg .X26) (.bin .eor .W64 (.reg .X24)
      (.bin .eor .W64 (.reg .X27) (.bin .eor .W64 (.reg .X29) (.bin .eor .W64 (.reg .X20)
        (.bin .eor .W64 (.reg .X23) (.reg .X1)))))))) :
    Holds (rsT m0) (tv m0) sD st := by
  intro p hp
  simp only [sD, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · show st.regs.getXReg .X20 = tv m0 sI
    apply UInt64.toBitVec_inj.mp
    rw [hm1.regs .X20 _ h20]
    simp only [eval_eor]
    rw [Holds.ev hH (s := .load 0 8 8) (n := mI 1) (by decide),
      Holds.ev hH (s := .reg .X19) (n := mI 2) (by decide),
      Holds.ev hH (s := .reg .X25) (n := mI 3) (by decide),
      Holds.ev hH (s := .reg .X28) (n := mI 4) (by decide),
      Holds.ev hH (s := .reg .X21) (n := mI 5) (by decide),
      Holds.ev hH (s := .reg .X22) (n := mI 6) (by decide),
      Holds.ev hH (s := .reg .X0) (n := mI 7) (by decide), tv_s0]
    simp only [UInt64.toBitVec_xor]
  · show st.regs.getXReg .X19 = tv m0 (sI + 1)
    apply UInt64.toBitVec_inj.mp
    rw [hm1.regs .X19 _ h19]
    simp only [eval_eor]
    rw [Holds.ev hH (s := .reg .X26) (n := mI 1 + 1) (by decide),
      Holds.ev hH (s := .reg .X24) (n := mI 2 + 1) (by decide),
      Holds.ev hH (s := .reg .X27) (n := mI 3 + 1) (by decide),
      Holds.ev hH (s := .reg .X29) (n := mI 4 + 1) (by decide),
      Holds.ev hH (s := .reg .X20) (n := mI 5 + 1) (by decide),
      Holds.ev hH (s := .reg .X23) (n := mI 6 + 1) (by decide),
      Holds.ev hH (s := .reg .X1) (n := mI 7 + 1) (by decide), tv_s1]
    simp only [UInt64.toBitVec_xor]

variable [Host] {k : Nat}

/-- **The epilogue** (`b36`): `M_0 + (M_1 + … + M_7)` returned. -/
theorem stepExit (h : P m0) {i : Nat} (hk : b36.IsInfixAt Host.prog i) {m : MachineData}
    (hst : St m0 ((.reg .X0, mI 0) :: (.reg .X1, mI 0 + 1) :: sD) m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m0 ∧ RingTargetPost m0 st.data)
      ⟨m, Host.addrOf i⟩ := by
  have hwf := envT_wf h hst.fr
  refine exec_then hk run_b36 hwf (matchT2 hst.fr h) fun st hm1 hpc ↦ ?_
  obtain ⟨hret, hsaved⟩ := hst.fr.exit hm1 hwf (by decide)
  have hpc' : st.pc = retOf m0 := by simp only [PcOk] at hpc; rw [hpc, hret]
  refine .done _ ⟨hpc', ?_, ?_, hsaved⟩
  · have e0 : st.data.regs.getXReg .X0 = (mV m0 0 + sV m0).c0 := by
      apply UInt64.toBitVec_inj.mp
      rw [hm1.regs .X0 _ rfl]
      simp only [eval_eor]
      rw [Holds.ev hst.hd (s := .reg .X0) (n := mI 0) (by decide),
        Holds.ev hst.hd (s := .reg .X20) (n := sI) (by decide)]
      rfl
    have e1 : st.data.regs.getXReg .X1 = (mV m0 0 + sV m0).c1 := by
      apply UInt64.toBitVec_inj.mp
      rw [hm1.regs .X1 _ rfl]
      simp only [eval_eor]
      rw [Holds.ev hst.hd (s := .reg .X1) (n := mI 0 + 1) (by decide),
        Holds.ev hst.hd (s := .reg .X19) (n := sI + 1) (by decide)]
      rfl
    show (⟨st.data.regs.getXReg .X0, st.data.regs.getXReg .X1⟩ : EW) = _
    rw [e0, e1]
    exact result_eq
  · have hd : st.data.dmem = m.dmem := hm1.dmem_eq hwf rfl
    intro p hp
    rw [hd]
    refine hst.fr.same p fun h ↦ hp ?_
    rcases h with h | h
    · exact .inr h
    · exact h.elim

/-- **The sum and the last turn** (`b33` to `b36`). -/
theorem chainC (hp : Placed code k) (h : P m0)
    (hsq : Spec (Labels.label NativeRustcVmArm.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost)
    (hpoly : Spec (Labels.label NativeRustcVmArm.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {m : MachineData}
    (hst : St m0 ((.reg .X0, mI 7) :: (.reg .X1, mI 7 + 1) :: K32) m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m0 ∧ RingTargetPost m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingTarget.b33Offset)⟩ := by
  refine polyStep h hpoly (hb b33_in_code (by simp [b33]) hp) run_b33
    hst.ptr (matchT2 hst.fr h) rfl
    (by decide) (D' := f0D) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (hrP 0 (by decide)) (E := sD) sD_regs
    (fun _ hm1 ↦ sum_holds hst.hd hm1 rfl rfl) fun m hst ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingTarget.b33Offset + b33.length = k + NativeRustcVmArm.Vm.RingTarget.b34Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingTarget.b33_next]]
  refine sqStep h hsq (hb b34_in_code (by simp [b34]) hp) run_b34
    hst.ptr (matchT2 hst.fr h) rfl
    (by decide) (D' := sD ++ f0D) (by decide) (by decide) rfl (by decide) (by decide)
    (by decide) (hrT 0 (by decide)) fun m hst ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingTarget.b34Offset + b34.length = k + NativeRustcVmArm.Vm.RingTarget.b35Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingTarget.b34_next]]
  refine mulStep h hmul (hb b35_in_code (by simp [b35]) hp) run_b35
    hst.ptr (matchT2 hst.fr h) rfl
    (by decide) (D' := sD) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (hrM 0 (by decide)) fun m hst ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingTarget.b35Offset + b35.length = k + NativeRustcVmArm.Vm.RingTarget.b36Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingTarget.b35_next]]
  exact stepExit h (hb b36_in_code (by simp [b36]) hp) hst

end

end NativeRustcVmArm.Ring.Target
