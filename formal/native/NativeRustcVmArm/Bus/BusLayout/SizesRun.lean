module

public import NativeRustcVmArm.Code.Vm.Memset.Names
public import NativeRustcVmArm.Bus.BusLayout.Heights

/-!
# `bus_layout`: from the entry to the sizes

`sizes_run`: the prologue `b0` and `memset` of the sizes; `b1` the sizes' count; the framework's
sizes (`b2`-`b4`, `fw_step`, at most three); `b5` the loop's registers (`from_b5`); the heights'
loop (`loop_step`) to `.LBusLayout_8` (`Done`).
-/

namespace NativeRustcVmArm.Bus.BusLayout

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BusLayout
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVmArm.Layout (infix_of)
open NativeRustcVm (wordOf wordsOf WordAt WordsAt)

public section

/-- Between `b1` and `b5`: `j` framework sizes written. -/
structure FwInv (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData) (j : Nat)
    (st : MachineData) : Prop where
  fr : Frm m0 st
  regs : Regs m0 st
  sizes : SizesAt st.dmem L bl m0 j
  x21 : (st.regs.getXReg .X21).toNat = nf m0 + bl.length
  x22 : st.regs.getXReg .X22 = m0.regs.X4
  x23 : st.regs.getXReg .X23 = m0.regs.X3

/-- A framework-size block's environment: the frame, the first `j + 1` framework sizes. -/
abbrev envW (st m0 : MachineData) (j : Nat) : Env :=
  Env.ofMachine st [(fb m0, 1840), (m0.regs.X1.toBitVec, 8 * (j + 1))]

section
variable [Host] {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 st : MachineData}
  {j : Nat}

omit [Host] in
theorem fw_wf (hpre : BusLayoutPre L bl m0) (hI : FwInv L bl m0 j st) (hj : j < nf m0) :
    (envW st m0 j).WF := by
  have hFo := hpre.2.2.2.1
  have hnf : nf m0 = m0.regs.X2.toNat := rfl
  refine Bus.wf_frame2 hpre.1 (by decide) hI.fr.kept
    ⟨fun t ht ↦ hFo.1.1 t (by omega), ?_⟩ ?_
  · have := hFo.1.2; unfold NoWrap at this ⊢; omega
  · have := hFo.2; unfold OffStack Apart at this ⊢; omega

theorem fw_match (hpre : BusLayoutPre L bl m0) (hI : FwInv L bl m0 j st) :
    Match (envW st m0 j) (sW (8 * (j + 1))) st := by
  have h := Bus.match_frame2 (r := .X25) (n := 8 * (j + 1)) hpre.1 (by decide) rfl hI.fr.sp
  rwa [hI.regs.x25] at h

/-- **A framework size written** (`b2`, `b3`, `b4`). -/
theorem fw_step (hpre : BusLayoutPre L bl m0) (hI : FwInv L bl m0 j st) (hj : j < nf m0)
    {S' : SState} {st' : MachineData} (hm' : Match (envW st m0 j) S' st')
    (hsp' : S'.sp = .ptr 0 0)
    (hkeep : ∀ r ∈ keep, ∃ v, (sW (8 * (j + 1))).reg r = some v ∧ S'.reg r = some v)
    (hregs : [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26].all (fun r ↦
      ((sW (8 * (j + 1))).reg r).isSome && S'.reg r == (sW (8 * (j + 1))).reg r) = true)
    (hw : ∀ t < 8, findWrite 0 (8 + 8 * j + t) S'.mem = some (.load 1 (8 * j) 8, t))
    (hall : (S'.mem.all fun w ↦ w.r == 0 && decide (8 + 8 * j ≤ w.off) &&
      decide (w.off + w.n ≤ 16 + 8 * j)) = true) :
    FwInv L bl m0 (j + 1) st' := by
  have K := KeepRegs.of_block' (fw_match hpre hI) hm' hregs
  obtain ⟨hfr, hsz⟩ := fw_write hpre hI.fr hI.sizes hj (fw_match hpre hI) hm' (fw_wf hpre hI hj)
    rfl hsp' hkeep hw hall
  exact ⟨hfr, hI.regs.keep fun r hr ↦ K r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp), hsz,
    by rw [K .X21 (by simp), hI.x21], by rw [K .X22 (by simp), hI.x22],
    by rw [K .X23 (by simp), hI.x23]⟩

end

variable [Host] {k : Nat}

/-- **From `b5`**: the loop's registers, then the heights' loop to `.LBusLayout_8`. -/
theorem from_b5 (hp : Placed code k) {L : LayoutW} {bl : List NativeRustcVm.Data.Block}
    {m0 : MachineData} (hpre : BusLayoutPre L bl m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b5Offset)) (hI : FwInv L bl m0 (nf m0) st.data) :
    Eventually (step1 Host.exe) (Done L bl m0 k) st := by
  have hbl1 : 1 ≤ bl.length := hpre.2.2.2.2.1
  have hx4 : m0.regs.X4.toNat = bl.length := hpre.2.2.2.2.2.2.1
  have hn54 := pre_n hpre
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 (Env.wf_nil _) hpc (match_nil _)
    fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : Frm m0 st1.data := Fr.ofBlock hI.fr (match_nil _) hm1 (Env.wf_nil _) rfl rfl rfl
    (ofBlock_keep (by decide))
  have K : Bus.KeepRegs [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26] st.data st1.data :=
    Bus.KeepRegs.of_block hm1 rfl
  have h8 := hm1.regs .X8 _ rfl
  have h9 := hm1.regs .X9 _ rfl
  simp only [PcOk] at hpc1
  rw [lbl_6 hp] at hpc1
  have hL0 : LInv L bl m0 0 st1.data := by
    refine ⟨hfr1, hI.regs.keep fun r hr ↦ K r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp), by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Nat.add_zero, hm1.dmem_eq (Env.wf_nil _) rfl]; exact hI.sizes
    · rw [K .X21 (by simp), hI.x21]
    · rw [K .X22 (by simp), hI.x22, hx4, Nat.sub_zero]
    · rw [K .X23 (by simp), hI.x23]; simp
    · rw [← UInt64.toNat_toBitVec, h8]
      show (UnOp.apply (.ubfm 61 60) .W64 (st.data.regs.getXReg .X20).toBitVec).toNat = _
      rw [lsl3, UInt64.toNat_toBitVec, hI.regs.x20]
      show 8 * m0.regs.X2.toNat % 2 ^ 64 = 8 * (m0.regs.X2.toNat + 0)
      have : m0.regs.X2.toNat ≤ 3 := hpre.2.1
      omega
    · rw [h9]
      sym_simp
      rw [Env.ofMachine_regs, hI.regs.x24]
  refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b7Offset) ∧ ∃ i, bl.length - i = n ∧
    LInv L bl m0 i st.data) (fun n st ⟨hpc, i, hn, hL⟩ ↦ ?_) ⟨hpc1, 0, rfl, hL0⟩
  refine Eventually.mono (loop_step hp hpre hpc hL) fun st' h ↦ ?_
  rcases h with h | ⟨hpc', hL'⟩
  · exact Or.inl h
  · exact Or.inr ⟨bl.length - (i + 1), by have := hL.lt; omega, hpc', i + 1, rfl, hL'⟩

/-- **The sizes**: from the entry to `.LBusLayout_8`. -/
theorem sizes_run (hp : Placed code k)
    (hms : Spec (Labels.label NativeRustcVmArm.Vm.Memset.entryLabel) MemsetPre MemsetPost) {L : LayoutW}
    {bl : List NativeRustcVm.Data.Block} {m0 : MachineData} (hpre : BusLayoutPre L bl m0) :
    Eventually (step1 Host.exe) (Done L bl m0 k) ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b0Offset)⟩ := by
  have hS := hpre.1
  have hN : busLayoutStack ≤ m0.regs.SP.toNat := hS.2.1
  have hF : 1840 ≤ busLayoutStack := by decide
  have hnf3 : nf m0 ≤ 3 := hpre.2.1
  have hx4 : m0.regs.X4.toNat = bl.length := hpre.2.2.2.2.2.2.1
  have hbl := pre_n hpre
  have hwf := Bus.wf_env0 hS hF
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf (Bus.match_entry hS hF rfl)
    fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : Frm m0 st1.data :=
    Fr.ofPrologue hN hF hm1 hwf rfl (by decide) slots_le (by decide) (by decide)
  have hregs1 : Regs m0 st1.data :=
    ⟨mov_reg (r' := .X0) hm1 rfl, mov_reg (r' := .X2) hm1 rfl, mov_reg (r' := .X5) hm1 rfl,
      mov_reg (r' := .X1) hm1 rfl, by
      rw [hm1.regs .X26 _ rfl]; rfl⟩
  have e22 : st1.data.regs.getXReg .X22 = m0.regs.X4 := mov_reg (r' := .X4) hm1 rfl
  have e23 : st1.data.regs.getXReg .X23 = m0.regs.X3 := mov_reg (r' := .X3) hm1 rfl
  have e0 : st1.data.regs.X0.toBitVec = fa m0 8 := by
    rw [show st1.data.regs.X0 = st1.data.regs.getXReg .X0 from rfl, hm1.regs .X0 _ rfl]; rfl
  have e2 : st1.data.regs.X2.toNat = 432 := by
    rw [show st1.data.regs.X2 = st1.data.regs.getXReg .X2 from rfl, ← UInt64.toNat_toBitVec,
      hm1.regs .X2 _ rfl]; rfl
  have hfb : (fb m0).toNat = m0.regs.SP.toNat - 1840 := base_toNat (by omega)
  have hlt := m0.regs.SP.toNat_lt
  have h8 : (fa m0 8).toNat = (fb m0).toNat + 8 := NativeRustcVm.toNat_add_ofNat (by omega)
  -- `memset` of the sizes.
  refine Fr.callW hfr1 keep_callee hms (W := InRange (fa m0 8) 432)
    (fun m' h ↦ ⟨by rw [← e0, ← e2]; exact h.2.2.1, h.2.2.2⟩)
    (fun q hq ↦ .inl (inRange_local hN hF (by omega) hq))
    (fun p hp' i hi ↦ slot_not_local (by omega) (by revert p; decide) (by
      have := slots_le p hp'; omega))
    hpc1 ⟨fun t ht ↦ by
        rw [e0, NativeRustcVm.addr_add_add]
        exact hfr1.kept _ ((Bus.frame_mapped hS hF).1 _ (by omega)),
      by unfold NoWrap; rw [e0, e2, h8]; omega⟩ fun m2 hfr2 _ hcs ↦ ?_
  have K2 : Bus.KeepRegs [.X19, .X20, .X22, .X23, .X24, .X25, .X26] st1.data m2 :=
    Bus.KeepRegs.of_call hcs rfl
  have hregs2 : Regs m0 m2 := hregs1.keep fun r hr ↦ K2 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp)
  -- `b1`: the sizes' count; no framework sizes: to `b5`.
  have hwf2 := Bus.wf_frame (F := 1840) hS hF hfr2.kept
  have hm2 := Bus.match_frame (m := m2) hS hF rfl hfr2.sp
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf2 rfl hm2
    fun st3 hm3 hpc3 ↦ ?_
  have hfr3 : Frm m0 st3.data := Fr.ofBlock hfr2 hm2 hm3 hwf2 rfl rfl rfl
    (ofBlock_keep (by decide))
  have K3 : Bus.KeepRegs [.X19, .X20, .X22, .X23, .X24, .X25, .X26] m2 st3.data :=
    Bus.KeepRegs.of_block hm3 rfl
  have h21 := hm3.regs .X21 _ rfl
  have hI0 : FwInv L bl m0 0 st3.data := by
    refine ⟨hfr3, hregs2.keep fun r hr ↦ K3 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp), fun _ h ↦ absurd h (by omega), ?_,
      by rw [K3 .X22 (by simp), K2 .X22 (by simp), e22],
      by rw [K3 .X23 (by simp), K2 .X23 (by simp), e23]⟩
    rw [← UInt64.toNat_toBitVec, h21]
    sym_simp
    rw [Env.ofMachine_regs, Env.ofMachine_regs, BitVec.toNat_add, UInt64.toNat_toBitVec,
      UInt64.toNat_toBitVec, K2 .X22 (by simp), e22, hregs2.x20, hx4]
    show (bl.length + m0.regs.X2.toNat) % 2 ^ 64 = m0.regs.X2.toNat + bl.length
    have : m0.regs.X2.toNat ≤ 3 := hpre.2.1
    omega
  have hx20 : ∀ st : MachineData, Regs m0 st → (st.regs.getXReg .X20).toNat = nf m0 :=
    fun st h ↦ by rw [h.x20]
  obtain ⟨hpcT3, hpcF3⟩ := pc_of_cond hpc3
  by_cases h0 : nf m0 = 0
  · refine from_b5 hp hpre ((hpcT3 ?_).trans (lbl_4 hp)) (h0 ▸ hI0)
    rw [eval_eq_lit _ _ _ .X20 (by decide), hx20 _ hregs2, h0]; rfl
  have hpc3 := hpcF3 (by rw [eval_eq_lit _ _ _ .X20 (by decide), hx20 _ hregs2]; simp [h0])
  -- `b2`: framework size `0`.
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 (fw_wf hpre hI0 (by omega)) hpc3
    (fw_match hpre hI0) fun st4 hm4 hpc4 ↦ ?_
  have hI1 := fw_step hpre hI0 (by omega) hm4 rfl (ofBlock_keep (by decide)) rfl (by decide)
    (by decide)
  obtain ⟨hpcT4, hpcF4⟩ := pc_of_cond hpc4
  by_cases h1 : nf m0 = 1
  · refine from_b5 hp hpre ((hpcT4 ?_).trans (lbl_4 hp)) (h1 ▸ hI1)
    rw [eval_eq_lit _ _ _ .X20 (by decide), hx20 _ hI0.regs, h1]; rfl
  have hpc4 := hpcF4 (by rw [eval_eq_lit _ _ _ .X20 (by decide), hx20 _ hI0.regs]; simp [h1])
  -- `b3`: framework size `1`.
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 (fw_wf hpre hI1 (by omega)) hpc4
    (fw_match hpre hI1) fun st5 hm5 hpc5 ↦ ?_
  have hI2 := fw_step hpre hI1 (by omega) hm5 rfl (ofBlock_keep (by decide)) rfl (by decide)
    (by decide)
  obtain ⟨hpcT5, hpcF5⟩ := pc_of_cond hpc5
  by_cases h2 : nf m0 = 2
  · refine from_b5 hp hpre ((hpcT5 ?_).trans (lbl_4 hp)) (h2 ▸ hI2)
    rw [eval_eq_lit _ _ _ .X20 (by decide), hx20 _ hI1.regs, h2]; rfl
  have hpc5 := hpcF5 (by rw [eval_eq_lit _ _ _ .X20 (by decide), hx20 _ hI1.regs]; simp [h2])
  -- `b4`: framework size `2`, then `b5`.
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 (fw_wf hpre hI2 (by omega)) hpc5
    (fw_match hpre hI2) fun st6 hm6 hpc6 ↦ ?_
  have hI3 := fw_step hpre hI2 (by omega) hm6 rfl (ofBlock_keep (by decide)) rfl (by decide)
    (by decide)
  simp only [PcOk] at hpc6
  exact from_b5 hp hpre hpc6 (show nf m0 = 3 by omega ▸ hI3)

end

end NativeRustcVmArm.Bus.BusLayout
