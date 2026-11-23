module

public import NativeRustcVmX64.Bus.AccumulateSide.LoopKB
public import NativeRustcVmX64.Bus.AccumulateSide.FactsO
public import NativeRustcVmX64.Code.Vm.EqEvalFnOfEqAbove.Names

/-!
# `accumulate_side`: the framework ones (x86-64)

`b8` reads framework placement `j` (R12) and calls `eq_eval_fn` for `eq_above`; `b9` adds the
selector to the ones (R14, R15) and goes to the next placement or out (`turnO`). `ones`: from
`b6` (the known part done), `b7` sets the loop up, or `b11` sets the ones to `1` with no framework
block; both reach `b12` with the ones over the framework.
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.AccumulateSide
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

public section

variable [Host] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData} {k : Nat}

/-- **A turn of the framework ones.** -/
theorem turnO (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre EqEvalFnOfEqAbovePost)
    {j : Nat} (hj : j < SL.framework.size) {st : MachineData}
    (hst : St m0 Z (Vt SL m0 (lpO SL m0 j)) DO 8 st) :
    Eventually (step1 Host.exe) (fun st' ↦
      St m0 Z (Vt SL m0 (lpO SL m0 (j + 1))) DOf 8 st'.data ∧
      st'.data.regs.get64 .r12 = (lpO SL m0 (j + 1) 0).toBitVec ∧
      st'.data.regs.get64 .r14 = (lpO SL m0 (j + 1) 1).toBitVec ∧
      st'.data.regs.get64 .r15 = (lpO SL m0 (j + 1) 2).toBitVec ∧
      ((st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b8Offset) ∧ j + 1 < SL.framework.size) ∨
        (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b10Offset) ∧ j + 1 = SL.framework.size)))
      ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b8Offset)⟩ := by
  have hfw := h.fw
  have hn := h.pn
  have hpl := fw_place h hj
  have hslnw := h.slIn.2.1
  unfold NativeRustcVm.NoWrap at hslnw
  let pl := off (stackArg m0 0) (16 + 16 * j)
  have hplIn : In m0 pl 16 := h.slIn.sub (by omega) (by decide)
  let V := Vt SL m0 (lpO SL m0 j)
  let env1 := frameEnv m0 st F [(pl, 16)] (fun _ ↦ 0)
    (Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b8Offset + b8.length)).toBitVec
  have hwf1 : env1.WF := wf1 h hst.fr.kept hplIn
  have hr12 := hst.hd.reg (r := .r12) (i := 32) (by decide)
  have hrbp := hst.hd.reg (r := .rbp) (i := 14) (by decide)
  have hrdi := hst.hd.reg (r := .rdi) (i := 13) (by decide)
  have hrbx := hst.hd.reg (r := .rbx) (i := 27) (by decide)
  have hm1 : Match env1 oS st :=
    St.mt hst ⟨rfl, rfl, trivial⟩ trivial trivial ⟨by
      show st.regs.get64 .r12 = pl + BitVec.ofInt 64 0
      rw [hr12, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
      show stackArg m0 0 + 16#64 + BitVec.ofNat 64 (16 * j) = _
      rw [BitVec.add_assoc, ← BitVec.ofNat_add], trivial⟩
  have s0 : (Sym.load 1 0 8).eval env1 = BitVec.ofNat 64 (fpl SL j).variableCount :=
    St.load h hst Z_outs h.slIn (r := 1) (j := 16 + 16 * j) rfl (o' := 0) (by omega)
      (by rw [Nat.add_zero]; exact hpl.2.2.1)
  have s8 : (Sym.load 1 8 8).eval env1 = BitVec.ofNat 64 (fpl SL j).index :=
    St.load h hst Z_outs h.slIn (r := 1) (j := 16 + 16 * j) rfl (o' := 8) (by omega)
      (by rw [← off_off]; exact hpl.2.2.2)
  have sbp : (Sym.reg .rbp).eval env1 = stackArg m0 8 := by
    show st.regs.get64 .rbp = _; rw [hrbp]; rfl
  have sbx : (Sym.reg .rbx).eval env1 = 0#64 := by
    show st.regs.get64 .rbx = _; rw [hrbx]; rfl
  have sdi : (Sym.reg .rdi).eval env1 = stackArg m0 7 := by
    show st.regs.get64 .rdi = _; rw [hrdi]; rfl
  have hvc := hpl.1
  have hix := hpl.2.1
  obtain ⟨hmid, hw, htr, hdi, hcx, hsi, hdx⟩ := ok_b8
  refine St.run h (rest := [(pl, 16)]) rfl (infix_of b8_in_code (by simp [b8]) hp) exit_b8
    (fun _ _ ↦ rfl) hst.fr hst.same (hst.hd.reg0 (by decide) rfl) (by decide) hwf1 hm1 hmid hw
    (by decide) htr fun st2 hm2 hpc2 hst2 _ ↦ ?_
  have eSat : (satO.eval env1).toNat = (stackArg m0 8).toNat - (fpl SL j).variableCount := by
    unfold satO; rw [ev_sat env1 _ _ _ sbx, sbp, s0, toNat_ofNat_lt hvc]
  have g0 : (reg st2.data .rdi).toNat = (stackArg m0 8).toNat - (fpl SL j).variableCount := by
    rw [show reg st2.data .rdi = _ from hm2.regs .rdi _ hdi, eSat]
  have g3 : (reg st2.data .rcx).toNat = (stackArg m0 8).toNat - (fpl SL j).variableCount := by
    rw [show reg st2.data .rcx = _ from hm2.regs .rcx _ hcx, eSat]
  have g1 : (reg st2.data .rsi).toNat = (fpl SL j).index >>> (fpl SL j).variableCount := by
    rw [show reg st2.data .rsi = _ from hm2.regs .rsi _ hsi]
    unfold shrO
    rw [ev_shr env1 _ _ _ sbx, s8, s0, toNat_ofNat_lt hvc, toNat_ofNat_lt hix]
  have g2 : reg st2.data .rdx = if (stackArg m0 8).toNat < (fpl SL j).variableCount then 8#64
      else stackArg m0 7 + BitVec.ofNat 64 (16 * (fpl SL j).variableCount) := by
    rw [show reg st2.data .rdx = _ from hm2.regs .rdx _ hdx]
    unfold aboveO
    rw [ev_above env1 _ _ _ _ rfl, sbp, s0, sdi, toNat_ofNat_lt hvc]
  have hst2c : St m0 Z V DOc 0 st2.data := hst2
  refine St.call h hst2c le_ee (lo := 0) (n := 0) (by decide) (by decide) hee hpc2
    (eqAbove_pre (St.stackOk h hst2c le_ee) h.pn (St.sliceOk h hst2c le_ee h.pt)
      (St.sb8 h hst2c (by decide)) g0 g2 g3) (W := Z) (fun _ h ↦ h.elim)
    (fun _ hq ↦ ⟨changes_call hq.2.1, hq.2.2⟩) fun m3 hst3 hq3 ↦ ?_
  have hret : ewRet m3 = fsel SL (ptA m0) j := by
    rw [eqAbove_ret g0 g1 g2 g3 hq3, St.pt h hst2c Z_outs]
    rfl
  -- `b9`: the selector added, the next placement.
  show Eventually _ _ (⟨m3, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b9Offset)⟩ : MachineState)
  obtain ⟨hmid9, hw9, htr9, h12, h14, h15⟩ := ok_b9
  refine St.run h (rest := [(rspOf m0 + 8#64, 88)]) (vs := fun _ ↦ 0) (ret := 0) rfl
    (infix_of b9_in_code (by simp [b9]) hp) exit_b9 nofun hst3.fr hst3.same
    ((((hst3.hd.append (holds_reg (V := V) (i := 35) (ewRet_c0 hret)
      (holds_reg (i := 36) (ewRet_c1 hret) (holds_nil _ _ _)))).reg0
        (rs' := (fb m0, F + 8) :: [(rspOf m0 + 8#64, 88)]) (by decide) rfl)).append
      (St.holdsDA h hst3 Z_outs)) (by decide)
    (wf1 h hst3.fr.kept h.argsIn)
    (St.mt hst3 ⟨rfl, rfl, trivial⟩ trivial trivial argAliases_ok) hmid9 hw9 (by decide) htr9
    fun st4 hm4 hpc4 hst4 _ ↦ ?_
  have g12 := hst3.hd.reg (r := .r12) (i := 32) (by decide)
  have g13 := hst3.hd.reg (r := .r13) (i := 29) (by decide)
  have g14 := hst3.hd.reg (r := .r14) (i := 33) (by decide)
  have g15 := hst3.hd.reg (r := .r15) (i := 34) (by decide)
  have hon := onesF_succ SL (ptA m0) j
  have e12 : st4.data.regs.get64 .r12 = (lpO SL m0 (j + 1) 0).toBitVec := by
    rw [hm4.regs .r12 _ h12]
    show BinOp.apply .add .W64 (BitVec.ofNat 64 16) (m3.regs.get64 .r12) = _
    rw [add64, g12]
    exact step16 _ _
  have e14 : st4.data.regs.get64 .r14 = (lpO SL m0 (j + 1) 1).toBitVec := by
    rw [hm4.regs .r14 _ h14]
    show BinOp.apply .xor .W64 (m3.regs.get64 .r14) (m3.regs.get64 .rax) = _
    rw [xor64, g14, ewRet_c0 hret]
    show _ = ((onesF SL (ptA m0) (j + 1)).c0).toBitVec
    rw [hon, add_c0, UInt64.toBitVec_xor]
    rfl
  have e15 : st4.data.regs.get64 .r15 = (lpO SL m0 (j + 1) 2).toBitVec := by
    rw [hm4.regs .r15 _ h15]
    show BinOp.apply .xor .W64 (m3.regs.get64 .r15) (m3.regs.get64 .rdx) = _
    rw [xor64, g15, ewRet_c1 hret]
    show _ = ((onesF SL (ptA m0) (j + 1)).c1).toBitVec
    rw [hon, add_c1, UInt64.toBitVec_xor]
    rfl
  have hc9 : c9.eval (frameEnv m0 m3 F [(rspOf m0 + 8#64, 88)] (fun _ ↦ 0) 0) =
      decide (j + 1 ≠ SL.framework.size) := by
    show (!(CmpOp.apply .eq .W64
      (BinOp.apply .add .W64 (BitVec.ofNat 64 16) (m3.regs.get64 .r12)) (m3.regs.get64 .r13))) = _
    rw [add64, g12, g13]
    show (!CmpOp.apply .eq .W64 (16#64 + (stackArg m0 0 + 16#64 + BitVec.ofNat 64 (16 * j)))
      (stackArg m0 0 + 16#64 + BitVec.ofNat 64 (16 * SL.framework.size))) = _
    rw [step16, eq64]
    rw [Bool.eq_iff_iff, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_iff]
    constructor
    · intro hne heq; exact hne (by rw [heq])
    · intro hne heq
      have := congrArg BitVec.toNat heq
      rw [addr16 _ (by omega), addr16 _ (by omega)] at this
      exact hne (by omega)
  have hnext : St m0 Z (Vt SL m0 (lpO SL m0 (j + 1))) DOf 8 st4.data :=
    St.sub (St.add (E := []) hst4 (fun p hp ↦ Vt_lt (by revert p hp; decide)) (holds_nil _ _ _))
      (by decide)
  simp only [PcOk] at hpc4
  rw [hc9] at hpc4
  by_cases hlast : j + 1 = SL.framework.size
  · simp only [hlast, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      at hpc4
    exact .done _ ⟨hnext, e12, e14, e15, .inr ⟨by rw [hpc4]; rfl, hlast⟩⟩
  · simp only [hlast, ne_eq, not_false_eq_true, decide_true, ↓reduceIte] at hpc4
    exact .done _ ⟨hnext, e12, e14, e15,
      .inl ⟨by rw [hpc4]; exact hp.label NativeRustcVmX64.Vm.AccumulateSide.label_7_at, by omega⟩⟩

end

end NativeRustcVmX64.Bus.AccumulateSide
