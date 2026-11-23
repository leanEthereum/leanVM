module

public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Bus.BusLayout.Keep

/-!
# `bus_layout`: the layout copied out, the epilogue

From `.LBusLayout_17` (`finish`): `b20` stores the framework's count at `880` (the layout is then
`busLayout`'s, `built`) and copies the 888 bytes out with `memcpy`
(`busLayoutWAt_transfer`); `b21` sets the tag `1`; `b22` returns.
-/

namespace NativeRustcVmArm.Bus.BusLayout

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BusLayout
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVmArm.Layout (infix_of)
open NativeRustcVm (wordOf wordsOf WordAt WordsAt)
open NativeRustcVm.Transcript (off)

public section

/-- The layout under construction, its words moved. -/
theorem part_move {d d' : Mem 64} {L : LayoutW} {bl : List NativeRustcVm.Data.Block}
    {m0 : MachineData} {j : Nat} (h : Part d L bl m0 j) (hj : j ≤ nf m0 + bl.length)
    (hn : nf m0 + bl.length ≤ 54) (hbl : bl.length ≤ 51)
    (hk : ∀ {o : Nat} {w : UInt64}, o + 8 ≤ 880 ∨ 888 ≤ o → o + 8 ≤ 1760 →
      WordAt d (fa m0 o) w → WordAt d' (fa m0 o) w) : Part d' L bl m0 j :=
  ⟨hk (by omega) (by omega) h.depth, hk (by omega) (by omega) h.tlen,
    fun j' hj' ↦ pa_move (h.fw j' hj') (hk (by omega) (by omega)) (hk (by omega) (by omega)),
    fun j' hj' ↦ pa_move (h.tb j' hj') (hk (by omega) (by omega)) (hk (by omega) (by omega))⟩

variable [Host] {k : Nat}

/-- **The epilogue**: from `.LBusLayout_17`, every placement pushed, to the return. -/
theorem finish (hp : Placed code k)
    (hmc : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) {L : LayoutW}
    {bl : List NativeRustcVm.Data.Block} {m0 : MachineData} (hpre : BusLayoutPre L bl m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b20Offset)) (hE : PEnd L bl m0 st.data) :
    Eventually (step1 Host.exe) (Post L bl m0) st := by
  have hS := hpre.1
  have hN : busLayoutStack ≤ m0.regs.SP.toNat := hS.2.1
  have hF : 1840 ≤ busLayoutStack := by decide
  have hF' : 1840 ≤ m0.regs.SP.toNat := by omega
  have hn := pre_n hpre
  have hbl : bl.length ≤ 51 := hpre.2.2.2.2.2.1
  have hO : InOk m0 m0.regs.X0.toBitVec optBusLayoutBytes busLayoutStack :=
    hpre.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hOB : optBusLayoutBytes = 896 := by decide
  have hOn : m0.regs.X0.toBitVec.toNat + 896 ≤ 2 ^ 64 := by
    have := hO.1.2; unfold NoWrap at this; rwa [hOB] at this
  have hfb : (fb m0).toNat = m0.regs.SP.toNat - 1840 := base_toNat hF'
  have hfb' : (base m0 1840).toNat = m0.regs.SP.toNat - 1840 := base_toNat hF'
  have hlt := m0.regs.SP.toNat_lt
  have hA := apart_frame hN hF hO.2
  unfold Apart at hA
  rw [hOB] at hA
  have ho8 : (m0.regs.X0.toBitVec + BitVec.ofNat 64 8).toNat = m0.regs.X0.toBitVec.toNat + 8 :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  have h872 : (fa m0 872).toNat = (fb m0).toNat + 872 := NativeRustcVm.toNat_add_ofNat (by omega)
  -- `b20`: the framework's count; `memcpy` of the layout.
  have hwf := Bus.wf_frame (F := 1840) hS hF hE.fr.kept
  have hm := Bus.match_frame (m := st.data) hS hF rfl hE.fr.sp
  refine exec_at (infix_of b20_in_code (by simp [b20]) hp) run_b20 hwf hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : Frm m0 st1.data :=
    frm_block (lo := 880) (hi := 888) hN hE.fr hm hm1 hwf rfl (ofBlock_keep (by decide))
      (by decide) (by decide)
  have h880 : WordAt st1.data.dmem (fa m0 880) (nf m0).toUInt64 := by
    have h := Bus.wordAt_write hm1 (r := 0) (o := 880) (v := .reg .X9) rfl (by omega) (by decide)
    rw [show UInt64.ofBitVec ((Sym.reg .X9).eval (Env.ofMachine st.data [(fb m0, 1840)])) =
        (nf m0).toUInt64 by
      apply UInt64.toNat_inj.mp
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (lt_of_le_of_lt (show nf m0 ≤ 3 from hpre.2.1)
        (by decide))]
      show (st.data.regs.getXReg .X9).toBitVec.toNat = _
      rw [UInt64.toNat_toBitVec, hE.x9]] at h
    exact h
  have hpart1 : Part st1.data.dmem L bl m0 (nf m0 + bl.length) :=
    part_move hE.part le_rfl hn hbl fun ho ho' h ↦
      keep_out (lo := 880) (hi := 888) hm1 hwf rfl hF' (by decide) (by decide) (by decide)
        (by omega) ho h
  have hBL : ∀ rows, BusLayoutWAt st1.data.dmem (fa m0 872)
      (busLayout (fws m0) (bl.map (blockW L.tableLogHeights rows)).toArray) := fun rows ↦
    built hpre rows hpart1 h880
  have e19 : st1.data.regs.getXReg .X19 = m0.regs.X0 := by
    rw [KeepRegs.of_block' hm hm1 (L := [.X19]) rfl .X19 (by simp), hE.x19]
  have e0 : st1.data.regs.X0.toBitVec = m0.regs.X0.toBitVec + BitVec.ofNat 64 8 := by
    rw [show st1.data.regs.X0 = st1.data.regs.getXReg .X0 from rfl, hm1.regs .X0 _ rfl]
    sym_simp
    rw [Env.ofMachine_regs, hE.x19]
  have e1 : st1.data.regs.X1.toBitVec = fa m0 872 := by
    rw [show st1.data.regs.X1 = st1.data.regs.getXReg .X1 from rfl, hm1.regs .X1 _ rfl]; rfl
  have e2 : st1.data.regs.X2.toNat = 888 := by
    rw [show st1.data.regs.X2 = st1.data.regs.getXReg .X2 from rfl, ← UInt64.toNat_toBitVec,
      hm1.regs .X2 _ rfl]; rfl
  have hout8 : ∀ q, InRange (m0.regs.X0.toBitVec + BitVec.ofNat 64 8) 888 q → outs m0 q := by
    intro q hq
    show InRange m0.regs.X0.toBitVec optBusLayoutBytes q
    rw [Sym.inRange_iff (by rw [ho8]; omega), ho8] at hq
    rw [hOB, Sym.inRange_iff (by omega)]
    omega
  refine Fr.callW hfr1 keep_callee hmc (W := InRange (m0.regs.X0.toBitVec + BitVec.ofNat 64 8) 888)
    (fun m' h ↦ ⟨by rw [← e0, ← e2]; exact h.2.2.1, h.2.2.2⟩)
    (fun q hq ↦ .inr (hout8 q hq))
    (fun p hp' i hi hq ↦ outs_frame hpre _ (hout8 _ hq) (by
      have := slots_le p hp'
      rw [Sym.inRange_iff (base_noWrap hF'), NativeRustcVm.addr_add_add,
        NativeRustcVm.toNat_add_ofNat (by omega)]
      omega))
    hpc1 ⟨fun t ht ↦ by
        rw [e0, e2] at *
        rw [NativeRustcVm.addr_add_add]
        exact hfr1.kept _ (hO.1.1 _ (by rw [hOB]; omega)),
      fun t ht ↦ by
        rw [e1, e2] at *
        rw [NativeRustcVm.addr_add_add]
        exact hfr1.kept _ ((Bus.frame_mapped hS hF).1 _ (by omega)),
      by unfold NoWrap; rw [e0, e2, ho8]; omega,
      by unfold NoWrap; rw [e1, e2, h872]; omega,
      by unfold Apart; rw [e0, e1, e2, ho8, h872]; omega⟩ fun m2 hfr2 hq2 hcs2 ↦ ?_
  have hcp : NativeRustcVm.BytesAt m2.dmem (m0.regs.X0.toBitVec + BitVec.ofNat 64 8)
      (NativeRustcArm.bytesOf st1.data.dmem (fa m0 872) 888) := by
    rw [← e0, ← e1, ← e2]; exact hq2.2.1
  have hBL2 : ∀ rows, BusLayoutWAt m2.dmem (m0.regs.X0.toBitVec + BitVec.ofNat 64 8)
      (busLayout (fws m0) (bl.map (blockW L.tableLogHeights rows)).toArray) := fun rows ↦
    busLayoutWAt_transfer (fun i hi x hx ↦ by
      rw [hcp i (by simp [NativeRustcArm.bytesOf, hi])]
      simp only [NativeRustcArm.bytesOf, List.getElem_map, List.getElem_range, hx,
        Option.getD_some]) (hBL rows)
  have e19' : m2.regs.getXReg .X19 = m0.regs.X0 := (hcs2 .X19 rfl).trans e19
  -- `b21`: the tag.
  have hOr : Readable m0 m0.regs.X0.toBitVec 8 :=
    ⟨fun t ht ↦ hO.1.1 t (by rw [hOB]; omega), by unfold NoWrap; omega⟩
  have hOs : OffStack m0 m0.regs.X0.toBitVec 8 busLayoutStack := by
    have := hO.2; unfold OffStack Apart at this ⊢; rw [hOB] at this; omega
  have hwf3 := Bus.wf_frame2 hS hF hfr2.kept hOr hOs
  have hm3 : Match (Env.ofMachine m2 [(fb m0, 1840), (m0.regs.X0.toBitVec, 8)]) sO m2 := by
    have h := Bus.match_frame2 (r := .X19) (n := 8) hS hF rfl hfr2.sp
    rwa [e19'] at h
  refine exec_at (infix_of b21_in_code (by simp [b21]) hp) run_b21 hwf3 rfl hm3
    fun st3 hm3' hpc3 ↦ ?_
  have hfr3 : Frm m0 st3.data :=
    Fr.ofBlockW hfr2 hm3 hm3' hwf3 rfl rfl (ofBlock_keep (by decide)) rfl hF hN slots_le
      fun w hw ↦ writeOk_two' (fun i hi ↦ by
        show InRange m0.regs.X0.toBitVec optBusLayoutBytes _
        exact NativeRustcVm.inRange_add (by rw [hOB]; omega) (by rw [hOB]; omega))
        (.inr (by revert w; decide))
  have htag := Bus.wordAt_write hm3' (r := 1) (o := 0) (v := .lit 1) rfl (by omega) (by decide)
  rw [add_zero'] at htag
  have hs3 := same_of_writes_in hm3' hwf3 (r := 1) (lo := 0) (hi := 8) rfl (by omega) (by omega)
    le_rfl (by decide)
  have hBL3 : ∀ rows, BusLayoutWAt st3.data.dmem (off m0.regs.X0.toBitVec 8)
      (busLayout (fws m0) (bl.map (blockW L.tableLogHeights rows)).toArray) := fun rows ↦
    busLayoutWAt_transfer (fun i hi x hx ↦ by
      have hq : ¬InRange (m0.regs.X0.toBitVec + BitVec.ofNat 64 0) (8 - 0)
          (m0.regs.X0.toBitVec + BitVec.ofNat 64 (8 + i)) := by
        rw [add_zero', Nat.sub_zero, Sym.inRange_iff (by omega),
          NativeRustcVm.toNat_add_ofNat (by omega)]
        omega
      rw [show off m0.regs.X0.toBitVec 8 + BitVec.ofNat 64 i =
          m0.regs.X0.toBitVec + BitVec.ofNat 64 (8 + i) by
        simp only [off, NativeRustcVm.addr_add_add], hs3 _ hq]
      rw [NativeRustcVm.addr_add_add] at hx
      exact hx) (hBL2 rows)
  -- `b22`: the epilogue.
  have hwf4 := Bus.wf_frame (F := 1840) hS hF hfr3.kept
  have hm4 := Bus.match_frame (m := st3.data) hS hF rfl hfr3.sp
  simp only [PcOk] at hpc3
  refine exec_at (infix_of b22_in_code (by simp [b22]) hp) run_b22 hwf4 hpc3 hm4
    fun st4 hm4' hpc4 ↦ ?_
  obtain ⟨hret, hsaved⟩ := hfr3.exit hm4' hwf4 (by decide)
  have hd4 : st4.data.dmem = st3.data.dmem := hm4'.dmem_eq hwf4 rfl
  refine .done _ ⟨by simp only [PcOk] at hpc4; rw [hpc4, hret], fun rows ↦ ?_, ?_, hsaved⟩
  · rw [hd4]
    exact ⟨htag, hBL3 rows⟩
  · intro p hp'
    rw [hd4]
    exact Bus.Fr.changes hfr3 (fun _ h ↦ h) p hp'

end

end NativeRustcVmArm.Bus.BusLayout
