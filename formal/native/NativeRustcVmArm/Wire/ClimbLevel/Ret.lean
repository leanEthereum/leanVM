module

public import NativeRustcVmArm.Wire.ClimbLevel.State

/-!
# `climb_level`'s returns

The epilogue (`b19`, `ret_spec`) with the parents' count in X19; `Some` after every node
(`b18`, `ok_spec`), `None` (`b16`, `none_spec`).
-/

namespace NativeRustcVmArm.Wire.ClimbLevel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.ClimbLevel
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

variable [Host] {k : Nat} {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}
  {ns : List (Nat × Digest)}

/-- **The return** (`b19`), the parents' count in X19. -/
theorem ret_spec (hp : Placed code k) (G : Geo m0 bp B) (hR : ReaderAt m0.dmem (rdr m0) bp B c)
    (hns : NodesAt m0.dmem (nodes m0) ns) (hlen : ns.length = cnt m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ClimbLevel.b19Offset)) (hfr : Frm m0 st.data)
    (hres : match sibsM B ns ns c with
      | some (sl, c') => st.data.regs.X0 = 1 ∧
          (st.data.regs.getXReg .X19).toNat = (parentsOf ns sl).length ∧
          NodesAt st.data.dmem (sibs m0) (sl.map fun s ↦ (s.1, s.2.1)) ∧
          NodesAt st.data.dmem (nxt m0) (parentsOf ns sl) ∧ ReaderAt st.data.dmem (rdr m0) bp B c'
      | none => st.data.regs.X0 = 0) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hwf := G.frEnv_wf hfr
  have hm := G.frEnv_match hfr
  refine exec_at (infix_of b19_in_code (by simp [b19]) hp) run_b19 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hret, hsv⟩ := hfr.exit hm1 hwf (by decide)
  have hd : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hx0 : st1.data.regs.X0 = st.data.regs.X0 := Match.reg_eq hm hm1 (r := .X0) rfl rfl
  have hx1 : st1.data.regs.X1 = st.data.regs.getXReg .X19 :=
    UInt64.toBitVec_inj.mp (hm1.regs .X1 _ rfl)
  refine .done _ ⟨by simp only [PcOk] at hpc1; rw [hpc1, hret],
    fun bp' B' c' hR' ns' hl' hns' ↦ ?_, ?_, hsv⟩
  · obtain ⟨rfl, rfl, rfl⟩ := hR.unique hR'
    obtain rfl := hns'.unique hns (by rw [hl', hlen])
    split at hres
    · rename_i sl c1 he
      rw [he]
      exact ⟨hx0.trans hres.1, by rw [hx1]; exact hres.2.1, by rw [hd]; exact hres.2.2.1,
        by rw [hd]; exact hres.2.2.2.1, by rw [hd]; exact hres.2.2.2.2⟩
    · rename_i he
      rw [he]
      exact hx0.trans hres
  · intro p hp
    rw [hd]
    refine hfr.same p ?_
    rintro (h | h | h | h)
    · exact hp ⟨stackR m0 climbLevelStack, by simp, h⟩
    · exact hp ⟨curRegion (rdr m0), by simp, h⟩
    · exact hp ⟨⟨sibs m0, nodesBytes⟩, by simp, h⟩
    · exact hp ⟨⟨nxt m0, nodesBytes⟩, by simp, h⟩

/-- **`Some`** (`b18`, then the return): every node done. -/
theorem ok_spec (hp : Placed code k) (G : Geo m0 bp B) (hR : ReaderAt m0.dmem (rdr m0) bp B c)
    (hns : NodesAt m0.dmem (nodes m0) ns) (hlen : ns.length = cnt m0) {st : MachineState}
    {sl : List (Nat × Digest × Bool)} {ci : Nat}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ClimbLevel.b18Offset)) (hfr : Frm m0 st.data)
    (hdn : Done m0 bp B c ns (cnt m0) sl ci st.data.dmem)
    (h19 : (st.data.regs.getXReg .X19).toNat = (parentsOf (ns.take (cnt m0)) sl).length) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hwf := G.frEnv_wf hfr
  have hm := G.frEnv_match hfr
  refine exec_at (infix_of b18_in_code (by simp [b18]) hp) run_b18 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hd : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hfr1 : Frm m0 st1.data := Fr.ofBlock hfr hm hm1 hwf rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  simp only [PcOk] at hpc1
  have ht : ns.take (cnt m0) = ns := List.take_of_length_le (by omega)
  rw [ht] at h19
  have hs := hdn.hs
  rw [ht] at hs
  have hnx := hdn.nx
  rw [ht] at hnx
  refine ret_spec hp G hR hns hlen (hpc1.trans (congrArg Host.addrOf rfl)) hfr1 ?_
  rw [hs]
  refine ⟨UInt64.toBitVec_inj.mp (hm1.regs .X0 _ rfl), ?_, by rw [hd]; exact hdn.sb,
    by rw [hd]; exact hnx, by rw [hd]; exact hdn.rd⟩
  rw [Match.reg_eq hm hm1 (r := .X19) rfl rfl]
  exact h19

/-- **`None`** (`b16`, then the return). -/
theorem none_spec (hp : Placed code k) (G : Geo m0 bp B) (hR : ReaderAt m0.dmem (rdr m0) bp B c)
    (hns : NodesAt m0.dmem (nodes m0) ns) (hlen : ns.length = cnt m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ClimbLevel.b16Offset)) (hfr : Frm m0 st.data) (hnone : sibsM B ns ns c = none) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hwf := G.frEnv_wf hfr
  have hm := G.frEnv_match hfr
  refine exec_at (infix_of b16_in_code (by simp [b16]) hp) run_b16 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : Frm m0 st1.data := Fr.ofBlock hfr hm hm1 hwf rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  simp only [PcOk, hp.label (j := NativeRustcVmArm.Vm.ClimbLevel.b19Offset) NativeRustcVmArm.Vm.ClimbLevel.label_15_at] at hpc1
  refine ret_spec hp G hR hns hlen hpc1 hfr1 ?_
  rw [hnone]
  exact UInt64.toBitVec_inj.mp (hm1.regs .X0 _ rfl)

end

end NativeRustcVmArm.Wire.ClimbLevel
