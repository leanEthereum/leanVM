module

public import NativeRustcVmArm.Code.Vm.HashPair.Names
public import NativeRustcVmArm.Code.Vm.ReaderDigest.Names
public import NativeRustcVmArm.Wire.ClimbLevel.Scan

/-!
# `climb_level`'s loop over the nodes

The scan to its end (`scan_spec`); node `i`'s set-up (`b6`, `b6_spec`); the loop's head (`b5`):
every node done (`ok_spec`) or the next (`head_step`); the loop (`loop_spec`).
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

section
variable (hp : Placed code k) (G : Geo m0 bp B)
  (hh : Spec (Labels.label NativeRustcVmArm.Vm.HashPair.entryLabel) HashPairPre HashPairPost)
  (hd : Spec (Labels.label NativeRustcVmArm.Vm.ReaderDigest.entryLabel) ReaderDigestPre ReaderDigestPost)
  (hR : ReaderAt m0.dmem (rdr m0) bp B c)
  (hns : NodesAt m0.dmem (nodes m0) ns) (hlen : ns.length = cnt m0)
include hp G hh hd hR hns hlen

/-- **The scan** for node `i`'s sibling, from node `j`. -/
theorem scan_spec {i : Nat} {sl : List (Nat × Digest × Bool)} {ci j : Nat} {st : MachineState}
    (hS : Scan m0 bp B c ns k i sl ci j st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      ∃ sl' ci', Head m0 bp B c ns k (i + 1) sl' ci' st') st := by
  refine Sym.loop (fun n st ↦ ∃ j, n = cnt m0 - j ∧ Scan m0 bp B c ns k i sl ci j st)
    (fun n st ⟨j, hn, hS⟩ ↦ ?_) ⟨j, rfl, hS⟩
  refine Eventually.mono (scan_step hp G hh hd hR hns hlen hS) fun st' h ↦ ?_
  rcases h with h | h
  · exact .inl h
  · exact .inr ⟨_, by have := h.le; omega, j + 1, rfl, h⟩

/-- **Node `i`'s set-up** (`b6`): the scan from node `0`. -/
theorem b6_spec {i : Nat} {sl : List (Nat × Digest × Bool)} {ci : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ClimbLevel.b6Offset)) (hfr : Frm m0 st.data) (hfx : Fix m0 st.data)
    (hdn : Done m0 bp B c ns i sl ci st.data.dmem) (hlt : i < cnt m0)
    (h19 : (st.data.regs.getXReg .X19).toNat = (parentsOf (ns.take i) sl).length)
    (h20 : (st.data.regs.getXReg .X20).toNat = i)
    (h23 : (st.data.regs.getXReg .X23).toBitVec = nd m0 i) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      ∃ sl' ci', Head m0 bp B c ns k (i + 1) sl' ci' st') st := by
  have hn := G.n256
  have hwf := G.frEnv_wf hfr
  have hm := G.frEnv_match hfr
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : Frm m0 st1.data := Fr.ofBlock hfr hm hm1 hwf rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have e : ∀ r ∈ [XReg.X19, .X22, .X25, .X27, .X28, .X29],
      st1.data.regs.getXReg r = st.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm hm1 rfl rfl
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  simp only [PcOk] at hpc1
  have hfx1 : Fix m0 st1.data := hfx.keep fun r h ↦ e r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with rfl | rfl | rfl | rfl | rfl <;> simp)
  refine scan_spec hp G hh hd hR hns hlen (j := 0)
    ⟨hpc1.trans (congrArg Host.addrOf rfl), ⟨hfr1, hfx1, by rw [hd1]; exact hdn, hlt,
      by rw [e .X19 (by simp)]; exact h19, ?_, ?_, ?_, ?_⟩, Nat.zero_le _, ?_, ?_,
      fun j' h ↦ absurd h (Nat.not_lt_zero _)⟩
  · show (st1.data.regs.getXReg .X20).toBitVec.toNat = _
    rw [hm1.regs .X20 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [toNat_add_one (by rw [UInt64.toNat_toBitVec, h20]; omega), UInt64.toNat_toBitVec, h20]
  · rw [hm1.regs .X23 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs, h23]
    rw [NativeRustcVm.addr_add_add, show 40 * i + 40 = 40 * (i + 1) by omega]
  · rw [hm1.regs .X24 _ rfl]
    exact h23
  · show (st1.data.regs.getXReg .X26).toBitVec.toNat = _
    rw [hm1.regs .X26 _ rfl]
    exact h20
  · rw [hm1.regs .X8 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [hfx.x29]
    show _ = nodes m0 + BitVec.ofNat 64 (40 * 0)
    rw [Nat.mul_zero, NativeRustcVm.addr_add_zero]
  · show (st1.data.regs.getXReg .X9).toBitVec.toNat = _
    rw [hm1.regs .X9 _ rfl, Nat.sub_zero]
    exact hfx.x25

/-- **The loop's head** (`b5`): every node done, or node `i`'s step. -/
theorem head_step {i : Nat} {sl : List (Nat × Digest × Bool)} {ci : Nat} {st : MachineState}
    (hH : Head m0 bp B c ns k i sl ci st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      ∃ sl' ci', Head m0 bp B c ns k (i + 1) sl' ci' st') st := by
  have hn := G.n256
  have hwf := G.frEnv_wf hH.fr
  have hm := G.frEnv_match hH.fr
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf hH.pc hm fun st1 hm1 hpc1 ↦ ?_
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hfr1 : Frm m0 st1.data := Fr.ofBlock hH.fr hm hm1 hwf rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have e : ∀ r ∈ [XReg.X19, .X20, .X22, .X23, .X25, .X27, .X28, .X29],
      st1.data.regs.getXReg r = st.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Match.reg_eq hm hm1 rfl rfl
  have hfx1 : Fix m0 st1.data := hH.fx.keep fun r h ↦ e r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with rfl | rfl | rfl | rfl | rfl <;> simp)
  have hle := hH.le
  have hnw := G.ndNw
  have key : (nd m0 i).toNat = (nd m0 (cnt m0)).toNat ↔ i = cnt m0 := by
    have h2 : (nd m0 (cnt m0)).toNat = (nodes m0).toNat + 40 * cnt m0 ∨
        ((nd m0 (cnt m0)).toNat = 0 ∧ (nodes m0).toNat + 40 * cnt m0 = 2 ^ 64) :=
      NativeRustcVm.toNat_add_ofNat_le hnw
    constructor
    · intro h
      by_contra hne
      have h1 : (nd m0 i).toNat = (nodes m0).toNat + 40 * i := toNat_off (by omega)
      rw [h1] at h
      rcases h2 with h2 | ⟨h2, h3⟩ <;> omega
    · intro h; rw [h]
  have hc : (SBool.cmp .eq .W64 (.reg .X23) (.reg .X28)).eval (frEnv m0 st.data) =
      decide (i = cnt m0) := by
    simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs, hH.x23, hH.fx.x28, key]
  simp only [PcOk, hc] at hpc1
  by_cases hend : i = cnt m0
  · simp only [hend, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.ClimbLevel.b18Offset) NativeRustcVmArm.Vm.ClimbLevel.label_14_at] at hpc1
    subst hend
    exact Eventually.mono (ok_spec hp G hR hns hlen hpc1 hfr1 (by rw [hd1]; exact hH.dn)
      (by rw [e .X19 (by simp)]; exact hH.x19)) fun _ h ↦ .inl h
  simp only [hend, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  exact b6_spec hp G hh hd hR hns hlen (hpc1.trans (congrArg Host.addrOf rfl)) hfr1 hfx1
    (by rw [hd1]; exact hH.dn) (by omega) (by rw [e .X19 (by simp)]; exact hH.x19)
    (by rw [e .X20 (by simp)]; exact hH.x20) (by rw [e .X23 (by simp)]; exact hH.x23)

/-- **The loop** from the head after `i` nodes. -/
theorem loop_spec {i : Nat} {sl : List (Nat × Digest × Bool)} {ci : Nat} {st : MachineState}
    (hH : Head m0 bp B c ns k i sl ci st) : Eventually (step1 Host.exe) (Post m0) st := by
  refine Sym.loop (fun n st ↦ ∃ i sl ci, n = cnt m0 - i ∧ Head m0 bp B c ns k i sl ci st)
    (fun n st ⟨i, sl, ci, hn, hH⟩ ↦ ?_) ⟨i, sl, ci, rfl, hH⟩
  refine Eventually.mono (head_step hp G hh hd hR hns hlen hH) fun st' h ↦ ?_
  rcases h with h | ⟨sl', ci', h⟩
  · exact .inl h
  · exact .inr ⟨_, by have := h.le; omega, i + 1, sl', ci', rfl, h⟩

end

end

end NativeRustcVmArm.Wire.ClimbLevel
