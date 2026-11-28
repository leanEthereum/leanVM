module

public import NativeRustcVmX64.Bus.AccumulateSide.TPre
public import NativeRustcVmX64.Code.Vm.EqEvalFnOfEqAbove.Names

/-!
# `accumulate_side`: the table loop's turn, to `eq_above` (x86-64)

`b17` keeps the padding rows in the frame, reads table placement `j` and calls `eq_eval_fn` for
`eq_above`: `turnA`, from the loop's head at turn `j` to the call's return with the selector in
RAX, RDX.
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.AccumulateSide
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

public section

variable [Host] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData} {k : Nat}

/-- **The table loop's turn `j`, to `eq_above`'s return.** -/
theorem turnA (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre EqEvalFnOfEqAbovePost)
    {j : Nat} (hj : j < bl.length) {st : MachineData} (hth : TH L rows bl Fm SL m0 j st)
    {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (outs m0) (VT L rows bl Fm SL m0 j) D17 8 m2 →
      ewRet m2 = tsel SL (ptA m0) j →
      FormsAt m2.dmem (reg m0 .rsi) (stA L rows bl Fm SL m0 j).1 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b18Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b17Offset)⟩ := by
  obtain ⟨hst, hG⟩ := hth
  have hlen := h.sl_size
  have hj51 := h.bl51
  have hjS : j < SL.tables.size := by omega
  have hpl := tb_place h hjS
  let pl := off (stackArg m0 0) (16 * j)
  have hplIn : In m0 pl 88 := h.slIn.sub (by omega) (by decide)
  have hApl : Apart (rspOf m0 + 8#64) 88 pl 88 :=
    apart_sub (Apart.symm' h.slArgs) h.slIn.2.1 (by rw [busLayoutBytes_eq]; omega) (by decide)
  let V := VT L rows bl Fm SL m0 j
  let env1 := frameEnv m0 st F [(rspOf m0 + 8#64, 88), (pl, 88)] (fun _ ↦ 0)
    (Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b17Offset + b17.length)).toBitVec
  have hwf1 : env1.WF := wf2 h hst.fr.kept h.argsIn hplIn hApl
  have hl0 : env1.load 1 0 8 = stackArg m0 0 := St.arg h hst outs_id (i := 0) (by decide)
  have hl72 : env1.load 2 72 8 = BitVec.ofNat 64 (tpl SL j).variableCount :=
    St.load h hst outs_id h.slIn (r := 2) (j := 16 * j) rfl (o' := 72)
      (by omega) (by rw [Nat.add_comm]; exact hpl.2.2.1)
  have hl80 : env1.load 2 80 8 = BitVec.ofNat 64 (tpl SL j).index :=
    St.load h hst outs_id h.slIn (r := 2) (j := 16 * j) rfl (o' := 80)
      (by omega)
      (by rw [show 16 * j + 80 = 72 + 16 * j + 8 by omega, ← off_off]; exact hpl.2.2.2)
  have hr12 := hst.hd.reg (r := .r12) (i := 32) (by decide)
  have hrbp := hst.hd.reg (r := .rbp) (i := 14) (by decide)
  have hrdi := hst.hd.reg (r := .rdi) (i := 13) (by decide)
  have hr8 := hst.hd.reg (r := .r8) (i := 27) (by decide)
  have hr9 := hst.hd.reg (r := .r9) (i := 26) (by decide)
  have hm1 : Match env1 pS st :=
    St.mt hst ⟨rfl, rfl, rfl, trivial⟩ trivial trivial (allOf_append argAliases_ok ⟨by
      show BinOp.apply .add .W64 (env1.load 1 0 8) (st.regs.get64 .r12) = pl + BitVec.ofInt 64 0
      rw [add64, hl0, hr12, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
      rfl, trivial⟩)
  obtain ⟨hmid, hw, htr, hdi, hcx, hsi, hdx⟩ := ok_b17
  refine St.run h (rest := [(rspOf m0 + 8#64, 88), (pl, 88)]) rfl
    (infix_of b17_in_code (by simp [b17]) hp) exit_b17 (fun _ _ ↦ rfl) hst.fr hst.same
    ((hst.hd.reg0 (rs' := (fb m0, F + 8) :: [(rspOf m0 + 8#64, 88), (pl, 88)]) (by decide)
      rfl).append (St.holdsDA h hst outs_id)) (by decide) hwf1 hm1 hmid hw (by decide) htr
    fun st2 hm2 hpc2 hst2 _ ↦ ?_
  have hvc := hpl.1
  have hix := hpl.2.1
  have hz : (Sym.reg .r8).eval env1 = 0#64 := by
    show st.regs.get64 .r8 = _; rw [hr8]; rfl
  have s72 : (Sym.load 2 72 8).eval env1 = BitVec.ofNat 64 (tpl SL j).variableCount := hl72
  have s80 : (Sym.load 2 80 8).eval env1 = BitVec.ofNat 64 (tpl SL j).index := hl80
  have sbp : (Sym.reg .rbp).eval env1 = stackArg m0 8 := by
    show st.regs.get64 .rbp = _; rw [hrbp]; rfl
  have eSat : (satT.eval env1).toNat = (stackArg m0 8).toNat - (tpl SL j).variableCount := by
    unfold satT; rw [ev_sat env1 _ _ (.reg .r8) hz, sbp, s72, toNat_ofNat_lt hvc]
  have eShr : (shrT.eval env1).toNat = (tpl SL j).index >>> (tpl SL j).variableCount := by
    unfold shrT
    rw [ev_shr env1 _ _ (.reg .r8) hz, s80, s72, toNat_ofNat_lt hvc, toNat_ofNat_lt hix]
  have eAbove : aboveT.eval env1 = if (stackArg m0 8).toNat < (tpl SL j).variableCount then 8#64
      else stackArg m0 7 + BitVec.ofNat 64 (16 * (tpl SL j).variableCount) := by
    unfold aboveT
    rw [ev_above env1 _ _ (.reg .rdi) (.reg .r9) (by
      show st.regs.get64 .r9 = _; rw [hr9]; rfl), sbp, s72, toNat_ofNat_lt hvc]
    rw [show (Sym.reg .rdi).eval env1 = stackArg m0 7 from by
      show st.regs.get64 .rdi = _; rw [hrdi]; rfl]
  have g0 : (reg st2.data .rdi).toNat = (stackArg m0 8).toNat - (tpl SL j).variableCount := by
    rw [show reg st2.data .rdi = _ from hm2.regs .rdi _ hdi]; exact eSat
  have g1 : (reg st2.data .rsi).toNat = (tpl SL j).index >>> (tpl SL j).variableCount := by
    rw [show reg st2.data .rsi = _ from hm2.regs .rsi _ hsi]; exact eShr
  have g2 : reg st2.data .rdx = if (stackArg m0 8).toNat < (tpl SL j).variableCount then 8#64
      else stackArg m0 7 + BitVec.ofNat 64 (16 * (tpl SL j).variableCount) := by
    rw [show reg st2.data .rdx = _ from hm2.regs .rdx _ hdx]; exact eAbove
  have g3 : (reg st2.data .rcx).toNat = (stackArg m0 8).toNat - (tpl SL j).variableCount := by
    rw [show reg st2.data .rcx = _ from hm2.regs .rcx _ hcx]; exact eSat
  have hk2 : KeepF m0 st.dmem st2.data.dmem := run_keep hwf1 hm2 low_T.1 (writesIn_of_mid hmid)
  have hG2 := KeepF.forms h hk2 hG
  have hsp2 : rspOf st2.data = fb m0 := by rw [hst2.fr.sp, off_zero]
  refine St.call h hst2 le_ee (lo := 0) (n := 0) (by decide) (by decide) hee hpc2
    (eqAbove_pre (St.stackOk h hst2 le_ee) h.pn (St.sliceOk h hst2 le_ee h.pt)
      (St.sb8 h hst2 (by decide)) g0 g2 g3) (W := Z) (fun _ h ↦ h.elim)
    (fun _ hq ↦ ⟨changes_call hq.2.1, hq.2.2⟩) fun m4 hst4 hq4 ↦ ?_
  refine cont m4 hst4 ?_ (call_forms h hsp2 le_ee (by decide) (changes_call hq4.2.1) hG2)
  rw [eqAbove_ret g0 g1 g2 g3 hq4, St.pt h hst2 outs_id]
  rfl

end

end NativeRustcVmX64.Bus.AccumulateSide
