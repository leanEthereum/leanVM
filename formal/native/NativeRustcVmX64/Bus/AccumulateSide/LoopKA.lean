module

public import NativeRustcVmX64.Bus.AccumulateSide.Calls
public import NativeRustcVmX64.Code.Vm.EqEvalFnOfEqAbove.Names

/-!
# `accumulate_side`: the known part's turn, to `eq_above` (x86-64)

`b2a` reads framework placement `i` and computes `eq_above`'s arguments (the rest's count, the
selector, the rest's address); `b2b` adds `side_beta` to fingerprint `i` (RBX, R14) and calls
`eq_eval_fn`. `turnKA`: from the loop's head at turn `i`, the return from `eq_eval_fn` with the
selector in RAX, RDX.
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.AccumulateSide
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

public section

variable [Host] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData} {k : Nat}

/-- **The known part's turn `i`, to `eq_above`'s return.** -/
theorem turnKA (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre EqEvalFnOfEqAbovePost)
    {i : Nat} (hi : i < cA SL m0) {st : MachineData}
    (hst : St m0 Z (Vt SL m0 (lpK SL m0 i)) DK 8 st) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b3Offset) ∧
      St m0 Z (Vt SL m0 (lpK SL m0 i)) DKc 8 st'.data ∧ ewRet st'.data = fsel SL (ptA m0) i)
      ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b2Offset)⟩ := by
  have hfw := h.fw
  have hiF : i < SL.framework.size := Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)
  have hiA : i < nA m0 := Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
  have hn := h.pn
  have hpl := fw_place h hiF
  let pl := off (stackArg m0 0) (16 + 16 * i)
  have hplIn : In m0 pl 16 := h.slIn.sub (by omega) (by decide)
  have hApl : Apart (rspOf m0 + 8#64) 88 pl 16 :=
    apart_sub (Apart.symm' h.slArgs) h.slIn.2.1 (by rw [busLayoutBytes_eq]; omega) (by decide)
  let V := Vt SL m0 (lpK SL m0 i)
  let env1 := frameEnv m0 st F [(rspOf m0 + 8#64, 88), (pl, 16)] (fun _ ↦ 0) 0
  have hwf1 : env1.WF := wf2 h hst.fr.kept h.argsIn hplIn hApl
  have hl64 : env1.load 1 64 8 = stackArg m0 8 := St.arg h hst Z_outs (i := 8) (by decide)
  have hl20 : env1.load 2 0 8 = BitVec.ofNat 64 (fpl SL i).variableCount :=
    St.load h hst Z_outs h.slIn (r := 2) (j := 16 + 16 * i) rfl (o' := 0) (by omega)
      (by rw [Nat.add_zero]; exact hpl.2.2.1)
  have hl28 : env1.load 2 8 8 = BitVec.ofNat 64 (fpl SL i).index :=
    St.load h hst Z_outs h.slIn (r := 2) (j := 16 + 16 * i) rfl (o' := 8) (by omega)
      (by rw [← off_off]; exact hpl.2.2.2)
  have hr12 := hst.hd.reg (r := .r12) (i := 18) (by decide)
  have hrbp := hst.hd.reg (r := .rbp) (i := 32) (by decide)
  have hrdi := hst.hd.reg (r := .rdi) (i := 13) (by decide)
  have hr9 := hst.hd.reg (r := .r9) (i := 26) (by decide)
  have hm1 : Match env1 kAS st :=
    St.mt hst ⟨rfl, rfl, rfl, trivial⟩ trivial trivial (allOf_append argAliases_ok ⟨by
      show BinOp.apply .add .W64 (st.regs.get64 .r12) (st.regs.get64 .rbp) = pl + BitVec.ofInt 64 0
      rw [add64, hr12, hrbp]
      show stackArg m0 0 + 16#64 + BitVec.ofNat 64 (16 * i) = _
      rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, BitVec.add_assoc, ← BitVec.ofNat_add],
      trivial⟩)
  obtain ⟨hmid, hw, htr, hdi, hsi, hdx⟩ := ok_b2a
  refine St.run h (rest := [(rspOf m0 + 8#64, 88), (pl, 16)]) (vs := fun _ ↦ 0) (ret := 0) rfl
    (infix_of b2a_in_code (by simp [b2a, b2]) hp) exit_b2a nofun hst.fr hst.same
    ((hst.hd.reg0 (rs' := (fb m0, F + 8) :: [(rspOf m0 + 8#64, 88), (pl, 16)]) (by decide) rfl).append
      (St.holdsDA h hst Z_outs)) (by decide) hwf1 hm1 hmid hw
    (by decide) htr fun st2 hm2 hpc2 hst2 _ ↦ ?_
  have hvc := hpl.1
  have hix := hpl.2.1
  have s64 : (Sym.load 1 64 8).eval env1 = stackArg m0 8 := hl64
  have s20 : (Sym.load 2 0 8).eval env1 = BitVec.ofNat 64 (fpl SL i).variableCount := hl20
  have s28 : (Sym.load 2 8 8).eval env1 = BitVec.ofNat 64 (fpl SL i).index := hl28
  have eSat : (satK.eval env1).toNat = (stackArg m0 8).toNat - (fpl SL i).variableCount := by
    unfold satK; rw [ev_sat env1 _ _ (.lit 0) rfl, s64, s20, toNat_ofNat_lt hvc]
  have eShr : (shrK.eval env1).toNat = (fpl SL i).index >>> (fpl SL i).variableCount := by
    unfold shrK
    rw [ev_shr env1 _ _ (.lit 0) rfl, s28, s20, toNat_ofNat_lt hvc, toNat_ofNat_lt hix]
  have eAbove : aboveK.eval env1 = if (stackArg m0 8).toNat < (fpl SL i).variableCount then 8#64
      else stackArg m0 7 + BitVec.ofNat 64 (16 * (fpl SL i).variableCount) := by
    unfold aboveK
    rw [ev_above env1 _ _ (.reg .rdi) (.reg .r9) (by
      show st.regs.get64 .r9 = _; rw [hr9]; rfl), s64, s20, toNat_ofNat_lt hvc]
    rw [show (Sym.reg .rdi).eval env1 = stackArg m0 7 from by
      show st.regs.get64 .rdi = _; rw [hrdi]; rfl]
  have e_di : st2.data.regs.get64 .rdi = (V 35).toBitVec := by
    rw [hm2.regs .rdi _ hdi, bv_eq eSat]; rfl
  have e_si : st2.data.regs.get64 .rsi = (V 36).toBitVec := by
    rw [hm2.regs .rsi _ hsi, bv_eq eShr]; rfl
  have e_dx : st2.data.regs.get64 .rdx = (V 37).toBitVec := by
    rw [hm2.regs .rdx _ hdx, eAbove]; rfl
  have hst2' : St m0 Z V (D2 ++ E2) 8 st2.data :=
    St.add hst2 (fun _ _ ↦ rfl) (holds_reg e_di (holds_reg e_si (holds_reg e_dx (holds_nil _ _ _))))
  -- `b2b`: `side_beta` plus fingerprint `i`, the call.
  have hnA : 0 < nA m0 := by omega
  let fpi := off (stackArg m0 1) (16 * i)
  have hfpAll : In m0 (stackArg m0 1) (16 * nA m0) := In.of_inOk (h.fp hnA) (Apart.symm' (h.fFp hnA))
  have hfpIn : In m0 fpi 16 := hfpAll.sub (by omega) (by decide)
  let env2 := frameEnv m0 st2.data F [(fpi, 16)] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b2Offset + b2a.length + b2b.length)).toBitVec
  have hwf2 : env2.WF := wf1 h hst2.fr.kept hfpIn
  have hrcx := hst2.hd.reg (r := .rcx) (i := 7) (by decide)
  have hrbp2 := hst2.hd.reg (r := .rbp) (i := 32) (by decide)
  have hm2' : Match env2 kBS st2.data :=
    St.mt hst2 ⟨rfl, rfl, trivial⟩ trivial trivial ⟨by
      show BinOp.apply .add .W64 (st2.data.regs.get64 .rcx) (st2.data.regs.get64 .rbp) =
        fpi + BitVec.ofInt 64 0
      rw [add64, hrcx, hrbp2, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
      rfl, trivial⟩
  obtain ⟨hmidb, hwb, htrb, hbx, h14⟩ := ok_b2b
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.AccumulateSide.b2Offset + b2a.length) := by
    rw [hpc2, show b2a.length = 15 from rfl]
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2' hst2' hm2' hwf2 e_di e_dx
  subst hpc2'
  refine St.run h (rest := [(fpi, 16)]) rfl (infix_of (F := code) (k := k) (j := NativeRustcVmX64.Vm.AccumulateSide.b2Offset + b2a.length) b2b_in_code (by simp [b2b, b2]) hp)
    exit_b2b (fun _ _ ↦ rfl) hst2'.fr hst2'.same
    (hst2'.hd.reg0 (by decide) rfl) (by decide) hwf2 hm2' hmidb hwb (by decide) htrb
    fun st3 hm3 hpc3 hst3 _ ↦ ?_
  have hfpv : (fpsA m0).getD i 0 = NativeRustcVm.ewOf m0.dmem (stackArg m0 1 + BitVec.ofNat 64 (16 * i)) := by
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getElem?_eq_getElem (by rw [NativeRustcVm.length_ewsOf]; exact hiA),
      NativeRustcVm.getElem_ewsOf]
    rfl
  have hl10 : env2.load 1 0 8 = (NativeRustcVm.wordOf m0.dmem (stackArg m0 1 + BitVec.ofNat 64 (16 * i))).toBitVec :=
    St.load h hst2' Z_outs hfpAll (r := 1) (j := 16 * i) rfl (o' := 0) (by omega)
      (by rw [Nat.add_zero]; exact NativeRustcVm.wordAt_of_mapped (NativeRustcVm.Mapped.sub hfpAll.1 (by omega)))
  have hl18 : env2.load 1 8 8 =
      (NativeRustcVm.wordOf m0.dmem (stackArg m0 1 + BitVec.ofNat 64 (16 * i) + 8#64)).toBitVec :=
    St.load h hst2' Z_outs hfpAll (r := 1) (j := 16 * i) rfl (o' := 8) (by omega) (by
      rw [show stackArg m0 1 + BitVec.ofNat 64 (16 * i) + 8#64 = off (stackArg m0 1) (16 * i + 8) from
        NativeRustcVm.addr_add_add _ _ _]
      exact NativeRustcVm.wordAt_of_mapped (NativeRustcVm.Mapped.sub hfpAll.1 (by omega)))
  have e_bx : st3.data.regs.get64 .rbx = (V 38).toBitVec := by
    rw [hm3.regs .rbx _ hbx]
    show BinOp.apply .xor .W64 (env2.load 1 0 8) (d2.regs.get64 .rax) = _
    rw [xor64, hl10, hst2'.hd.reg (r := .rax) (i := 11) (by decide)]
    show _ = ((betaA m0 + (fpsA m0).getD i 0).c0).toBitVec
    rw [hfpv, add_c0, UInt64.toBitVec_xor, BitVec.xor_comm]
    rfl
  have e_14 : st3.data.regs.get64 .r14 = (V 39).toBitVec := by
    rw [hm3.regs .r14 _ h14]
    show BinOp.apply .xor .W64 (env2.load 1 8 8) (d2.regs.get64 .r8) = _
    rw [xor64, hl18, hst2'.hd.reg (r := .r8) (i := 12) (by decide)]
    show _ = ((betaA m0 + (fpsA m0).getD i 0).c1).toBitVec
    rw [hfpv, add_c1, UInt64.toBitVec_xor, BitVec.xor_comm]
    rfl
  have hst3' : St m0 Z V DKc 0 st3.data :=
    St.sub (St.add hst3 (fun _ _ ↦ rfl) (holds_reg e_bx (holds_reg e_14 (holds_nil _ _ _))))
      (by decide)
  have g0 : (reg st3.data .rdi).toNat = (stackArg m0 8).toNat - (fpl SL i).variableCount := by
    rw [show reg st3.data .rdi = _ from hst3.hd.reg (r := .rdi) (i := 35) (by decide)]
    exact toNat_ofNat_lt (by omega)
  have g1 : (reg st3.data .rsi).toNat = (fpl SL i).index >>> (fpl SL i).variableCount := by
    rw [show reg st3.data .rsi = _ from hst3.hd.reg (r := .rsi) (i := 36) (by decide)]
    exact toNat_ofNat_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hix)
  have g2 : reg st3.data .rdx = if (stackArg m0 8).toNat < (fpl SL i).variableCount then 8#64
      else stackArg m0 7 + BitVec.ofNat 64 (16 * (fpl SL i).variableCount) :=
    hst3.hd.reg (r := .rdx) (i := 37) (by decide)
  have g3 : (reg st3.data .rcx).toNat = (stackArg m0 8).toNat - (fpl SL i).variableCount := by
    rw [show reg st3.data .rcx = _ from hst3.hd.reg (r := .rcx) (i := 35) (by decide)]
    exact toNat_ofNat_lt (by omega)
  refine St.call h hst3' le_ee (lo := 0) (n := 0) (by decide) (by decide) hee hpc3
    (eqAbove_pre (St.stackOk h hst3' le_ee) h.pn (St.sliceOk h hst3' le_ee h.pt)
      (St.sb8 h hst3' (by decide)) g0 g2 g3) (W := Z) (fun _ h ↦ h.elim)
    (fun _ hq ↦ ⟨changes_call hq.2.1, hq.2.2⟩) fun m4 hst4 hq4 ↦ .done _ ⟨rfl, hst4, ?_⟩
  rw [eqAbove_ret g0 g1 g2 g3 hq4, St.pt h hst3' Z_outs]
  rfl

end

end NativeRustcVmX64.Bus.AccumulateSide
