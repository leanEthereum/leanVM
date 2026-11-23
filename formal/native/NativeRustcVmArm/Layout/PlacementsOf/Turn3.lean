module

public import NativeRustcVmArm.Layout.PlacementsOf.Loop3

/-!
# `placements_of`: a turn of the third loop

From `.L17`: `b22` (`b22a`, `b22b`) loads column `c`'s slot byte and log-size; a slot goes to
`slot3`; else `b26` loads the output byte: an output lane is stored as `none` (`store27`), a
stacked column's offset is loaded (`b20`) and stored (`store21`).
-/

namespace NativeRustcVmArm.Layout.PlacementsOf

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PlacementsOf
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt wordOf addr_add_add addr_add_zero toNat_add_ofNat)
open NativeRustcVmArm.Arrays (Body calleeRegs inSlots keepsAll restores)
open NativeRustcVmArm.Layout.BuildLayout (toNat_toUInt64')

public section

variable [Host] {k : Nat}

/-- **A stacked column or an output lane** (`b26`, then `b20`, `b21` or `b27`). -/
theorem rest3 (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {c : Nat} (hc : c < 158)
    (hs : slotF c = none) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b26Offset))
    (hI : I3 m0 c st.data) (x11 : st.data.regs.X11.toNat = κ m0 c) :
    Eventually (step1 Host.exe) (Next3 k m0 c) st := by
  have hκ := hF.κ_le hc
  refine byte_step (infix_of b26_in_code (by simp [b26]) hp) run_b26 b26_keep hF hI.body hpc
    .keccakOutput (by rw [length_out]; exact hc) hI.keep.x24 hI.x9 (idxB_eval · .X24 .X9)
    fun st1 hpc1 hb1 hd1 hr1 hl1 _ ↦ ?_
  have hI1 := hI.mono hb1 hd1 (regs_of hr1 _ rfl)
  have x11' : st1.data.regs.X11.toNat = κ m0 c := by
    rw [show st1.data.regs.X11 = st.data.regs.X11 from hr1 .X11 rfl]; exact x11
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  rw [hl1, out_get hc] at hpc1
  obtain ⟨f1, t1⟩ := Arrays.pc_cond hpc1
  cases ho : outF c with
  | true =>
    simp only [ho, ite_true] at f1 t1
    exact store27 hp hF hc (pc_of (t1 (by decide)) rfl) hI1 (plF_out hs ho)
  | false =>
    simp only [ho] at f1 t1
    have hpc2 := (f1 (by decide)).trans (hp.label (j := NativeRustcVmArm.Vm.PlacementsOf.b20Offset) NativeRustcVmArm.Vm.PlacementsOf.label_15_at)
    have hblk : c ∈ blockList := mem_blockList hc (by rw [hs]; rfl) ho
    -- `b20`: the offset
    have hb1 := hI1.body
    have hr := frame_readable hF hb1 (o := 3792 + 8 * c) (n := 8) (by omega)
    have hwf := Arrays.wf_one hr.1 hr.2
    have hm : Match (Env.ofMachine st1.data [(fb m0 + BitVec.ofNat 64 (3792 + 8 * c), 8)]) l20S
        st1.data :=
      match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial trivial trivial ⟨by
        show (idx .X25 .X9).eval _ = _
        rw [idx_eval]
        simp only [Env.ofMachine_regs, Env.base_ofMachine_eq, List.getElem?_cons_zero,
          Option.map_some, Option.getD_some, Layout.ofInt_zero, BitVec.add_zero]
        rw [show (st1.data.regs.getXReg .X9).toBitVec.toNat = c from hI1.x9,
          show (st1.data.regs.getXReg .X25).toBitVec = _ from hI1.x25, addr_add_add], trivial⟩
    refine exec_at (infix_of b20_in_code (by simp [b20]) hp) run_b20 hwf hpc2 hm
      fun st2 hm2 hpc3 ↦ ?_
    have hb2 : Bd m0 st2.data := hb1.of_block hm hm2 hwf rfl b20_keep
    have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq hwf rfl
    have e2 := Arrays.regs_eq_of hm hm2 [.X8, .X9, .X10, .X19, .X20, .X21, .X23, .X24, .X25]
      rfl
    have e11 := Arrays.regs_eq_of hm hm2 [.X11] rfl .X11 (by simp)
    have hI2 := hI1.mono hb2 hd2 e2
    have g12 := hm2.regs .X12 _ rfl
    sym_simp at g12
    have h4 := hF.sumF_le (keyF (κ m0) c)
    simp only [PcOk] at hpc3
    refine store21 hp hF hc (pc_of hpc3 rfl) hI2 (idx := sumF (κ m0) (keyF (κ m0) c))
      (by omega) ?_ ?_ (plF_block hs ho)
    · rw [show st2.data.regs.X11 = st.data.regs.X11 from e11.trans (hr1 .X11 rfl)]
      exact x11
    · show (st2.data.regs.getXReg .X12).toBitVec.toNat = _
      rw [g12, Layout.load_word (v := (sumF (κ m0) (keyF (κ m0) c)).toUInt64) (by
        simp only [Env.ofMachine_mem0, Arrays.base0, addr_add_zero]
        exact hI1.offs c hblk)]
      simp only [UInt64.toNat_toBitVec]
      exact toNat_toUInt64' (by omega)

/-- **A turn** of the third loop from `.L17`. -/
theorem turn3 (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {c : Nat} (hc : c < 158)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b22Offset)) (hI : I3 m0 c st.data) :
    Eventually (step1 Host.exe) (Next3 k m0 c) st := by
  have hκ := hF.κ_le hc
  -- `b22a`: the slot byte
  refine byte_step (infix_of b22a_in_code (by simp [b22a, b22]) hp) run_b22a b22a_keep hF hI.body
    hpc .keccakSlot (by rw [length_slot]; exact hc) hI.keep.x23 hI.x9 (idxB_eval · .X23 .X9)
    fun st1 hpc1 hb1 hd1 hr1 hl1 hX1 ↦ ?_
  have hI1 := hI.mono hb1 hd1 (regs_of hr1 _ rfl)
  have x12 : (st1.data.regs.getXReg .X12).toBitVec =
      BitVec.ofNat 64 (NativeRustcVm.Data.slotByte (slotF c)).toNat := by
    rw [hX1 rfl rfl, slot_get hc]
  simp only [PcOk] at hpc1
  -- `b22b`: the log-size and the test
  have hb1' := hI1.body
  have hr := Layout.readable_sub (o := 8 * c) (j := 8) hF.kr hb1'.kept
    (by unfold kappasBytes columnCountW; omega)
  have hwf := Arrays.wf_one hr.1 hr.2
  have hm : Match (Env.ofMachine st1.data [(kk m0 + BitVec.ofNat 64 (8 * c), 8)]) kapS st1.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial trivial trivial ⟨by
      show (idx .X19 .X9).eval _ = _
      rw [idx_eval]
      simp only [Env.ofMachine_regs, Env.base_ofMachine_eq, List.getElem?_cons_zero,
        Option.map_some, Option.getD_some, Layout.ofInt_zero, BitVec.add_zero]
      rw [show (st1.data.regs.getXReg .X9).toBitVec.toNat = c from hI1.x9,
        show st1.data.regs.getXReg .X19 = m0.regs.X0 from hI1.keep.x19], trivial⟩
  refine exec_at (infix_of b22b_in_code (by simp [b22b, b22]) hp) run_b22b hwf
    (pc_of hpc1 rfl) hm fun st2 hm2 hpc2 ↦ ?_
  have hb2 : Bd m0 st2.data := hb1'.of_block hm hm2 hwf rfl (Arrays.after_eq run_b22b ▸ b22b_keep)
  have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq hwf rfl
  have e2 := Arrays.regs_eq_of hm hm2 [.X8, .X9, .X10, .X19, .X20, .X21, .X23, .X24, .X25] rfl
  have e12 := Arrays.regs_eq_of hm hm2 [.X12] rfl .X12 (by simp)
  have hI2 := hI1.mono hb2 hd2 e2
  have g11 := hm2.regs .X11 _ rfl
  sym_simp at g11
  have x11 : st2.data.regs.X11.toNat = κ m0 c := by
    show (st2.data.regs.getXReg .X11).toBitVec.toNat = _
    rw [g11, load_word', Env.ofMachine_mem0]
    simp only [Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some, addr_add_zero]
    rw [kap_same hF hb1' hc, κ_eq m0 hc]; rfl
  simp only [PcOk] at hpc2
  sym_simp at hpc2
  have hsb := slotByte_lt (c := c)
  rw [show (Env.ofMachine st1.data [(kk m0 + BitVec.ofNat 64 (8 * c), 8)]).regs .X12 = _
    from x12, ofNat_beq' (by omega) (by decide)] at hpc2
  obtain ⟨f2, t2⟩ := Arrays.pc_cond hpc2
  have x12' : st2.data.regs.X12.toNat = (NativeRustcVm.Data.slotByte (slotF c)).toNat := by
    show (st2.data.regs.getXReg .X12).toBitVec.toNat = _
    rw [e12, x12, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  cases hs : slotF c with
  | none =>
    have h255 : (NativeRustcVm.Data.slotByte (slotF c)).toNat = 255 := slotByte_255.mpr hs
    exact rest3 hp hF hc hs ((f2 (decide_eq_true h255)).trans (hp.label (j := NativeRustcVmArm.Vm.PlacementsOf.b26Offset) NativeRustcVmArm.Vm.PlacementsOf.label_20_at)) hI2 x11
  | some s =>
    have hne : ¬(NativeRustcVm.Data.slotByte (slotF c)).toNat = 255 := fun h ↦ by
      rw [slotByte_255.mp h] at hs; cases hs
    refine slot3 hp hF hc hs (pc_of (t2 (by simp [hne])) rfl) hI2 x11 ?_
    rw [x12', slotByte_toNat hs]

end

end NativeRustcVmArm.Layout.PlacementsOf
