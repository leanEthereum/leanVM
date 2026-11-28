module

public import NativeRustcVmArm.Code.Vm.TableWeights.Names
public import NativeRustcVmArm.Tables.TableSumcheck.Rev

/-!
# `table_sumcheck`: the tables' weights

From the reversed challenges (`Rev (n / 2)`): `b6` keeps the claim's halves in X26, X27 and calls
`table_weights` on the heights, the bus's GKR point and the reversed challenges, its six weights
at `504` of the frame (`weights`). What follows reads the state `Wt`.
-/

namespace NativeRustcVmArm.Tables.TableSumcheck

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TableSumcheck
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Tables
open NativeRustcVm.Bus (BusWAt busBytes)
open NativeRustcVmArm.Sumcheck (Ctx)
open NativeRustcVm (ewOf ewsOf wordOf)

@[expose] public section

/-- The frame after `table_weights`: the reversed challenges at `24`, the weights at `504`, the
claim in X26, X27. -/
structure Wt [Labels] (m0 : MachineData) (a : DecArea) (n : Nat) (xs : Array EW) (c : EW)
    (s1 : TState) (heights : Array Nat) (bus : BusResultW) (m : MachineData) : Prop where
  fr : Fr m0 720 tableSumcheckStack slots keep (outs m0) m
  regs : Regs m0 m n
  ts : TStateAt m.dmem m0.regs.X0.toBitVec a s1
  pt : NativeRustcVm.EWsAt m.dmem (fb m0 + BitVec.ofNat 64 24) xs.reverse.toList
  w : NativeRustcVm.EWsAt m.dmem (fb m0 + BitVec.ofNat 64 504)
    (tableWeights heights bus.point xs.reverse).toList
  x26 : m.regs.getXReg .X26 = c.c0
  x27 : m.regs.getXReg .X27 = c.c1
  x28 : (m.regs.getXReg .X28).toBitVec = fb m0 + BitVec.ofNat 64 504

end

public section

section
variable [Labels] {a : DecArea} {s : TState} {heights : Array Nat} {bus : BusResultW}
  {m0 : MachineData}

/-- An input of the entry is none of the outputs. -/
theorem in_not_outs (hpre : TableSumcheckPre a s heights bus m0) {x : BitVec 64} {n : Nat}
    (h : ReadIn m0 x n tableSumcheckStack
      [⟨m0.regs.X0.toBitVec, tstateBytes⟩, ⟨m0.regs.X7.toBitVec, tableEvalsBytes⟩]) :
    ∀ j < n, ¬outs m0 (x + BitVec.ofNat 64 j) := fun j hj ho ↦ ho.elim
  (Bus.not_inRange_of_apart (h.2.2 ⟨m0.regs.X0.toBitVec, tstateBytes⟩ (by simp)) h.1.2
    hpre.2.2.2.1.footprint.1.2 hj)
  (Bus.not_inRange_of_apart (h.2.2 ⟨m0.regs.X7.toBitVec, tableEvalsBytes⟩ (by simp)) h.1.2
    hpre.2.2.2.2.2.1.2.1 hj)

/-- An input's bytes in a state of the frame: the entry's. -/
theorem same_input (hpre : TableSumcheckPre a s heights bus m0) {m : MachineData}
    (hfr : Fr m0 720 tableSumcheckStack slots keep (outs m0) m) {x : BitVec 64} {n : Nat}
    (h : ReadIn m0 x n tableSumcheckStack
      [⟨m0.regs.X0.toBitVec, tstateBytes⟩, ⟨m0.regs.X7.toBitVec, tableEvalsBytes⟩]) :
    NativeRustcVm.Layout.Same m0.dmem m.dmem x n :=
  same_in hfr hpre.1 h.1.2 h.2.1 (in_not_outs hpre h)

/-- The heights in a state of the frame. -/
theorem heights_fr (hpre : TableSumcheckPre a s heights bus m0) {m : MachineData}
    (hfr : Fr m0 720 tableSumcheckStack slots keep (outs m0) m) :
    HeightsAt m.dmem m0.regs.X1.toBitVec heights := by
  have hHin := hpre.2.2.2.2.2.2.2.2.1
  have hH := hpre.2.2.2.2.2.2.2.2.2.1
  refine ⟨hH.1, hH.2.1, WordsAt.of_same hH.2.2 (same_input hpre hfr hHin) ?_⟩
  have := hH.1
  simp [this, nTables]

/-- The bus's result in a state of the frame. -/
theorem bus_fr (hpre : TableSumcheckPre a s heights bus m0) {m : MachineData}
    (hfr : Fr m0 720 tableSumcheckStack slots keep (outs m0) m) :
    BusWAt m.dmem m0.regs.X2.toBitVec bus :=
  BusWAt.of_same hpre.2.2.2.2.2.2.2.2.2.2.2.1 (same_input hpre hfr hpre.2.2.2.2.2.2.2.2.2.2.1)

/-- The reversed challenges, from the frame after the reverse. -/
theorem ewsOf_rev {n : Nat} {xs : List EW} {c : EW} {s1 : TState} {m : MachineData}
    (hR : Rev m0 a n xs c s1 (n / 2) m) (hxs : xs.length = n) :
    ewsOf m.dmem (fb m0 + BitVec.ofNat 64 24) n = xs.reverse := by
  apply List.ext_getElem (by simp [hxs])
  intro i h1 h2
  rw [NativeRustcVm.getElem_ewsOf, NativeRustcVm.addr_add_add, hR.el i (by simpa using h1)]
  subst hxs
  exact rv_half (by simpa using h2)

end

section
variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat} {bus : BusResultW}
  {m0 : MachineData} {n : Nat} {xs : Array EW} {c : EW} {s1 : TState}

/-- **The weights** (`b6`): `table_weights` on the heights, the bus's point and the reversed
challenges. -/
theorem weights (hp : Placed code k)
    (hw : Spec (Labels.label NativeRustcVmArm.Vm.TableWeights.entryLabel) TableWeightsPre TableWeightsPost)
    (hpre : TableSumcheckPre a s heights bus m0) (hn30 : n ≤ 30) (hxs : xs.size = n)
    {m : MachineData} (hR : Rev m0 a n xs.toList c s1 (n / 2) m)
    (cont : ∀ m2, Wt m0 a n xs c s1 heights bus m2 →
      Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.TableSumcheck.b7Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableSumcheck.b6Offset)⟩ := by
  have hpre' := hpre
  obtain ⟨hS, hrc, -, hts0, htok, heo, -, -, hHin, -, hBin, -, -, -⟩ := hpre'
  have hN := hS.2.1
  have h720 : 720 ≤ tableSumcheckStack := N_ge
  have hSP := m0.regs.SP.toNat_lt
  have hfb := fb_toNat hS N_ge
  have cx : Ctx m0 m0.regs.X0.toBitVec a tableSumcheckStack 720 :=
    Bus.Gkr.ctx_of hS hrc hts0 htok N_ge rfl
  have hof : ∀ q, outs m0 q → ¬InRange (base m0 720) 720 q := fun q hq ↦
    hq.elim (Bus.Gkr.tstate_not_frame cx) (Bus.Gkr.out_not_frame cx heo)
  have hor : ∀ q, outs m0 q → ¬InRange rcAddr 192 q := fun q hq ↦
    hq.elim cx.not_rc_tstate (Bus.Gkr.out_not_rc cx heo)
  have hlen : xs.toList.length = n := by simp [hxs]
  have hpt := ewsOf_rev hR hlen
  -- `b6`.
  have e19 : (m.regs.getXReg .X19).toBitVec = m0.regs.X2.toBitVec := by rw [hR.regs.x19]
  have hwf : (Env.ofMachine m [(base m0 720, 720), ((m.regs.getXReg .X19).toBitVec,
      107768)]).WF := by
    rw [e19]; exact Bus.wf_frame2 hS N_ge hR.fr.kept hBin.1 hBin.2.1
  have hm := Bus.match_frame2 hS N_ge rfl hR.fr.sp (r := .X19) (n := 107768)
  refine exec_then (b6_in_code.trans hp.1 (by simp [b6])) run_b6 hwf hm fun st hm6 hpc ↦ ?_
  have hm6' : Match (Env.ofMachine m [(base m0 720, 720), ((m.regs.getXReg .X19).toBitVec,
      107768)]) (Bus.after b6 busS) st.data := by
    rw [Bus.after_eq run_b6]; exact hm6
  obtain ⟨hsp6, hmem6, hk6, g19, g0, g1, g2, g3, g4, g5, g26, g27, g28⟩ := ok_b6
  have hd6 : st.data.dmem = m.dmem := hm6'.dmem_eq hwf hmem6
  have hfr6 : Fr m0 720 tableSumcheckStack slots keep (outs m0) st.data :=
    Fr.ofBlock hR.fr hm hm6' hwf rfl hmem6 hsp6 nofun
  have rk : ∀ r ∈ [XReg.X20, .X21, .X22, .X23, .X24, .X25],
      st.data.regs.getXReg r = m.regs.getXReg r := fun r hr ↦ Bus.Gkr.reg_of hm6'
    (reg_keep hk6 (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto))
  have r19 : st.data.regs.getXReg .X19 = m.regs.getXReg .X19 := by
    apply UInt64.toBitVec_inj.mp
    rw [hm6'.regs .X19 _ g19]
    simp [Sym.eval]
  have rg6 : Regs m0 st.data n := hR.regs.of fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | h
    · exact r19
    · exact rk _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto)
  have hbus := bus_fr hpre hR.fr
  have hpb := hbus.point
  have hpl : bus.point.toList.length ≤ 63 := hpb.1
  have hlw : wordOf m.dmem (m0.regs.X2.toBitVec + BitVec.ofNat 64 106704) =
      bus.point.toList.length.toUInt64 := NativeRustcVm.wordOf_of_wordAt hpb.2.1
  have hld : (Env.ofMachine m [(base m0 720, 720), ((m.regs.getXReg .X19).toBitVec,
      107768)]).load 1 106704 8 = BitVec.ofNat 64 bus.point.size := by
    rw [load8]
    simp only [Env.base_ofMachine_eq, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.map_some, Option.getD_some, Env.ofMachine_mem0, e19]
    rw [hlw]
    apply BitVec.eq_of_toNat_eq
    simp only [Array.length_toList] at hpl ⊢
    rw [UInt64.toNat_toBitVec, toNat_toUInt64 (by omega), BitVec.toNat_ofNat]
    omega
  have hult : CmpOp.ult.apply .W64 (BitVec.ofNat 64 bus.point.size) (BitVec.ofNat 64 64) = true := by
    simp only [Array.length_toList] at hpl
    simp only [CmpOp.apply, low_W64, BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
    rw [Nat.mod_eq_of_lt (show bus.point.size < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 64 < 2 ^ 64 by decide)]
    omega
  have e0 : st.data.regs.X0.toBitVec = fb m0 + BitVec.ofNat 64 504 := by
    show (st.data.regs.getXReg .X0).toBitVec = _
    rw [hm6'.regs .X0 _ g0]; simp [Sym.eval]
  have e1 : st.data.regs.X1 = m0.regs.X1 := by
    show st.data.regs.getXReg .X1 = _
    rw [Bus.Gkr.reg_of hm6' g1]; exact hR.regs.x21
  have e2 : st.data.regs.X2.toBitVec = m0.regs.X2.toBitVec + BitVec.ofNat 64 106712 := by
    show (st.data.regs.getXReg .X2).toBitVec = _
    rw [hm6'.regs .X2 _ g2]
    simp only [Sym.eval, SBool.eval, hld, hult, ↓reduceIte]
    simp only [Env.base_ofMachine_eq, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.map_some, Option.getD_some, e19]
    rw [show BitVec.ofInt 64 106712 = BitVec.ofNat 64 106712 from rfl]
  have e3 : st.data.regs.X3.toNat = bus.point.size := by
    show (st.data.regs.getXReg .X3).toBitVec.toNat = _
    rw [hm6'.regs .X3 _ g3]
    simp only [Sym.eval, SBool.eval, hld, hult, ↓reduceIte, BitVec.toNat_ofNat]
    simp only [Array.length_toList] at hpl
    omega
  have e4 : st.data.regs.X4.toBitVec = fb m0 + BitVec.ofNat 64 24 := by
    show (st.data.regs.getXReg .X4).toBitVec = _
    rw [hm6'.regs .X4 _ g4]; simp [Sym.eval]
  have e5 : st.data.regs.X5.toNat = n := by
    show (st.data.regs.getXReg .X5).toBitVec.toNat = _
    rw [Bus.Gkr.reg_of hm6' g5]; exact hR.regs.x25
  have e26 : st.data.regs.getXReg .X26 = c.c0 := by
    apply UInt64.toBitVec_inj.mp
    rw [hm6'.regs .X26 _ g26]
    simp only [Sym.eval]
    rw [load8]
    simp only [Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some, Env.ofMachine_mem0]
    rw [← hR.claim]; rfl
  have e27 : st.data.regs.getXReg .X27 = c.c1 := by
    apply UInt64.toBitVec_inj.mp
    rw [hm6'.regs .X27 _ g27]
    simp only [Sym.eval]
    rw [load8]
    simp only [Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some, Env.ofMachine_mem0]
    rw [← hR.claim]
    show _ = (wordOf m.dmem (fb m0 + BitVec.ofNat 64 512 + BitVec.ofNat 64 8)).toBitVec
    rw [NativeRustcVm.addr_add_add]
  have e28 : (st.data.regs.getXReg .X28).toBitVec = fb m0 + BitVec.ofNat 64 504 := by
    rw [hm6'.regs .X28 _ g28]; simp [Sym.eval]
  -- `table_weights`.
  have hle : 720 + tableWeightsStack ≤ tableSumcheckStack := by
    unfold tableSumcheckStack; omega
  have hout := Bus.local_ok (o := 504) (n := 96) hS hle (by omega) hfr6.kept hfr6.sp
  have hptk := Bus.local_ok (o := 24) (n := 16 * n) hS hle (by omega) hfr6.kept hfr6.sp
  have hbp := ReadIn.fr hfr6 hS hle (ReadIn.sub hBin (o := 106712) (k := 16 * bus.point.size)
    (by unfold busBytes NativeRustcVm.Bus.busTotalsOff NativeRustcVm.Bus.busPointOff
          NativeRustcVm.Bus.pointBufBytes NativeRustcVm.Bus.formsBytes; decide)
    (by simp only [Array.length_toList] at hpl
        rw [show busBytes = 107768 from rfl]
        omega))
  have hht := ReadIn.fr hfr6 hS hle hHin
  have hpre6 : TableWeightsPre st.data := by
    refine ⟨hfr6.stackOk hS rfl hle, by rw [e0]; exact hout.1, by rw [e0]; exact hout.2,
      by rw [e1]; exact ⟨hht.1, hht.2.1, nofun⟩, ?_, ?_⟩
    · unfold SliceOk; rw [e2, e3]; exact ⟨hbp.1, hbp.2.1⟩
    · unfold SliceOk; rw [e4, e5]; exact hptk
  have hpc' : st.pc = Labels.label NativeRustcVmArm.Vm.TableWeights.entryLabel ∧ retOf st.data = Host.addrOf (k + NativeRustcVmArm.Vm.TableSumcheck.b7Offset) := hpc
  refine Bus.Gkr.Fr.callLocal (o := 504) (n := 96)
    (X := fun q ↦ InRange (fb m0 + BitVec.ofNat 64 504) 96 q) hfr6 hN hle keep_callee
    (fun p hp ↦ ⟨by have := slots_hi p hp; omega, (slots_le p hp)⟩) (by omega) hof
    (fun q hq ↦ .inr hq) hw hpc' hpre6
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q h ↦ ?_, hq.2.2⟩)
    fun m2 hfr2 hq2 hcs2 hs2 ↦ ?_
  · rw [e0] at h
    exact h.elim .inr .inl
  -- After the call.
  have hstk : ∀ q, (InRange (stackBelow st.data tableWeightsStack) tableWeightsStack q ∨
      InRange (fb m0 + BitVec.ofNat 64 504) 96 q) → InRange (stackBelow m0 tableSumcheckStack)
      tableSumcheckStack q := fun q hq ↦ hq.elim
    (cx.inRange_stack (Bus.Gkr.Fr.at_ cx hfr6 hor) hle) (fb_stack hS N_ge (by omega))
  refine cont m2 ⟨hfr2, rg6.of fun r hr ↦ hcs2 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl),
    tstate_keep cx hstk (by rw [hd6]; exact hR.ts) hq2.2.2.2.2 hs2, ?_, ?_,
    by rw [hcs2 .X26 rfl, e26], by rw [hcs2 .X27 rfl, e27], by rw [hcs2 .X28 rfl, e28]⟩
  · have hmp : NativeRustcVm.Mapped m.dmem (fb m0 + BitVec.ofNat 64 24) (16 * n) := by
      rw [← hd6]; exact hptk.1.1
    have h1 := NativeRustcVm.ewsAt_of_mapped hmp
    rw [hpt] at h1
    rw [← Array.toList_reverse] at h1
    rw [← hd6] at h1
    refine Bus.Gkr.keep_frame (N' := tableWeightsStack) hfr6.sp (by omega) hs2 (o := 24) ?_
      (fun i hi ↦ ?_) h1
    · rw [NativeRustcVm.length_ewsBytes]; simp [hxs]; omega
    · rw [NativeRustcVm.length_ewsBytes] at hi
      simp only [Array.length_toList, Array.size_reverse, hxs] at hi
      exact Bus.Gkr.not_loc (by omega) (by omega) (by omega) (by omega)
  · have hw2 := hq2.1
    have sp1 : slice st.data st.data.regs.X2 st.data.regs.X3 = bus.point := by
      unfold slice
      rw [e2, e3, hd6]
      have := NativeRustcVm.ewsOf_of_ewsAt hpb.2.2
      rw [Array.length_toList] at this
      rw [show m0.regs.X2.toBitVec + BitVec.ofNat 64 106712 =
          off m0.regs.X2.toBitVec NativeRustcVm.Bus.busPointOff + 8#64 by
        rw [off, NativeRustcVm.Bus.busPointOff_eq, NativeRustcVm.addr_add_add], this]
    have sp2 : slice st.data st.data.regs.X4 st.data.regs.X5 = xs.reverse := by
      unfold slice
      rw [e4, e5, hd6, hpt]
      apply Array.toList_inj.mp
      simp
    have hh : heightsOf st.data.dmem st.data.regs.X1.toBitVec = heights := by
      rw [e1]; exact heightsOf_eq (heights_fr hpre hfr6)
    rw [sp1, sp2, hh, e0] at hw2
    exact hw2

end

end

end NativeRustcVmArm.Tables.TableSumcheck
