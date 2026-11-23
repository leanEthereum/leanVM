module

public import NativeRustcVmX64.Whir.VerifyStackedOpening.TgtBlocks
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `verify_stacked_opening`: the target's loop (x86-64)

`tgt_step`: from the loop's head (`b34`, `Tgt i`): `b34` reads claim `i`'s column; above `157` the
claim is not placed (to `b33`); else `b35` reads its placement's `present` word; zero, not placed
(to `b33`); else `b36` (the scales never run out), `b37` loads the next scale, `b31` the claim's
value, `EW::mul`, `b32` adds the product (`placed_b36`): `Done i` at `b33`. `tgt_run`: the loop to
`b38` (`Acc` at the end).
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVmX64.Vm.VerifyStackedOpening

public section

/-- **The next term**: a placed claim's. -/
theorem accOf_succ {s : TState} {layout : LayoutW} {target : EW} {cs : Array ColumnClaimW}
    {value : EW} {i : Nat} (hi : i < cs.size) (hpl : (cs[i].onStack layout).isSome) :
    placedOf layout cs (i + 1) = placedOf layout cs i + 1 ∧
    ∃ hj : 1 + placedOf layout cs i < (scalesOf s layout cs).toList.length,
      accOf s layout target cs value (1 + placedOf layout cs (i + 1)) =
        accOf s layout target cs value (1 + placedOf layout cs i) +
          (scalesOf s layout cs).toList[1 + placedOf layout cs i] * cs[i].value := by
  have hps : placedOf layout cs (i + 1) = placedOf layout cs i + 1 := by
    rw [placedOf_succ hi]
    simp only [hpl, ↓reduceIte]
  have hle := placedOf_le (layout := layout) (cs := cs) i
  have hl : 1 + placedOf layout cs i < (scalesOf s layout cs).toList.length := by
    rw [length_scalesOf]; unfold cntOf; omega
  have hr : 1 + placedOf layout cs i < (valsOf layout target cs value).length := by
    rw [length_valsOf]; omega
  refine ⟨hps, hl, ?_⟩
  unfold accOf
  rw [hps, show 1 + (placedOf layout cs i + 1) = 1 + placedOf layout cs i + 1 by omega,
    dotL_take_succ hl hr]
  have hv := vals_placed (layout := layout) hi hpl target value
  rw [show placedOf layout cs i + 1 = 1 + placedOf layout cs i by omega] at hv
  obtain ⟨_, he⟩ := List.getElem?_eq_some_iff.mp hv
  rw [he]

section
variable [Labels] {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- Not placed: `Done i` from the loop's state. -/
theorem Done.skip {i : Nat}
    {st : MachineData} (hc : Acc a s layout target cs value m0 i st)
    (hw96 : NativeRustcVm.WordAt st.dmem (off (stackBelow m0 512) 96)
      (UInt64.ofBitVec (off (layA m0) 120)))
    (hi : i < cs.size) (hbp : (reg st .rbp).toNat = 608 * i)
    (h15 : (reg st .r15).toNat = 608 * cs.size) (hb : bitAt layout cs i = 0) :
    Done a s layout target cs value m0 i st :=
  ⟨hc.congr (by rw [placedOf_succ', hb, Nat.add_zero]), hw96, hi, hbp, h15⟩

end

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- **A placed claim**: from `b36`, its term added, at `b33`. -/
theorem placed_b36 (h : Parts a s layout target coefficients point slices cs z value m0)
    (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {i : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b36Offset))
    (hc : Acc a s layout target cs value m0 i st.data)
    (hw96 : NativeRustcVm.WordAt st.data.dmem (off (stackBelow m0 512) 96)
      (UInt64.ofBitVec (off (layA m0) 120)))
    (hi : i < cs.size) (hbp : (reg st.data .rbp).toNat = 608 * i)
    (h15 : (reg st.data .r15).toNat = 608 * cs.size) (hpl : (cs[i].onStack layout).isSome)
    {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b33Offset) →
      Done a s layout target cs value m0 i st'.data → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hok := hc.ok
  have hn := h.n_le
  have hP := (placedOf_le_self (layout := layout) (cs := cs) cs.size).trans hn
  have hle := placedOf_le (layout := layout) (cs := cs) i
  have hscn := h.sc_nw
  have hsc8 := h.sc8_le (layout := layout)
  have hsb : scalesBytes = 2600 := rfl
  have hscn' : (scA m0).toNat + 2600 ≤ 2 ^ 64 := hscn
  have hsc8' : 8 + 16 * cntOf layout cs ≤ 2600 := hsc8
  have hscap : NativeRustcVm.Apart (scA m0) scalesBytes (stackBelow m0 verifyStackedOpeningStack)
      (verifyStackedOpeningStack + 8) := h.so.1.2.2.2.2.1
  obtain ⟨hps, hj, hacc⟩ := accOf_succ (s := s) (target := target) (value := value) hi hpl
  -- `b36`: the scales never run out
  refine h.run hp b36_in_code (List.cons_ne_nil _ _) hpc hok (vars := fun _ ↦ 0) (hok.wf0 h)
    hok.m_reg run_b36 (o := 8) (by decide +kernel) (by decide) fun st1 hok1 hs1 hm1 hpc1 ↦ ?_
  have hc1 := Acc.blk h hc (hok.wf0 h) hm1 hok1 hs1 rfl (by decide +kernel) (by decide +kernel)
  simp only [PcOk] at hpc1
  rw [eval_eq64] at hpc1
  have hne : ¬ (((Sym.reg .r14).eval (frameEnv m0 st.data 512 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b36Offset + b36.length)).toBitVec)).toNat = ((Sym.reg .r12).eval
        (frameEnv m0 st.data 512 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b36Offset + b36.length)).toBitVec)).toNat)
      := by
    show ¬ (reg st.data .r14).toNat = (reg st.data .r12).toNat
    have hcnt : cntOf layout cs = placedOf layout cs cs.size + 2 := rfl
    have h1 : (scA m0).toNat + (8 + 16 * (1 + placedOf layout cs i)) < 2 ^ 64 := by omega
    rw [hc.r14, hc.r12, toNat_off h1]
    rcases NativeRustcVm.toNat_add_ofNat_le (a := scA m0) (i := 8 + 16 * cntOf layout cs)
      (by omega) with e | ⟨e, _⟩
    · rw [e]; omega
    · rw [e]; omega
  simp only [hne, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  have hbp1 : (reg st1.data .rbp).toNat = 608 * i := by rw [regKeep hm1 .rbp rfl]; exact hbp
  have h151 : (reg st1.data .r15).toNat = 608 * cs.size := by rw [regKeep hm1 .r15 rfl]; exact h15
  have hw961 := (FW.block_os (L := [(96, _)]) (hok.wf0 h) hm1 rfl (FW.one hw96) [96] rfl
    (by decide +kernel)).get List.mem_cons_self
  -- `b37`: the next scale
  have jo : 8 + 16 * (1 + placedOf layout cs i) + 16 ≤ 2600 := by unfold cntOf at hsc8; omega
  have hwf2 : ∀ ret, (frameEnv m0 st1.data 512 [(off (scA m0) (8 + 16 * (1 + placedOf layout cs i)),
      16)] (fun _ ↦ 0) ret).WF := fun _ ↦
    hok1.wf1 h (mapped_off h.so.1.1 (by omega)) (noWrap_off' hscn (by omega) (by omega)) (by
      have hh := hscap
      have hsbe := h.sb
      unfold NativeRustcVm.Apart at hh ⊢
      rw [hsb] at hh
      rw [toNat_off (by unfold NativeRustcVm.NoWrap at hscn; omega)]
      omega)
  have hm2 : ∀ ret, Match (frameEnv m0 st1.data 512 [(off (scA m0)
      (8 + 16 * (1 + placedOf layout cs i)), 16)] (fun _ ↦ 0) ret) scaleS st1.data := fun _ ↦
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hok1.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨by show reg st1.data .r14 = _
          rw [hc1.r14, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; rfl, trivial⟩
  have hsj := ew_loads (d := st1.data) (vs := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b37Offset + b37.length)).toBitVec)
    (rs := [(stackBelow m0 512, 520), (off (scA m0) (8 + 16 * (1 + placedOf layout cs i)), 16)])
    (b := off (scA m0) (8 + 16 * (1 + placedOf layout cs i))) (n := 16) (r := 1) (o := 0)
    (x := (scalesOf s layout cs).toList[1 + placedOf layout cs i]) rfl (by
      rw [off_zero, ← off_off]
      exact hc1.out.scs.getElem hj)
  refine h.run hp b37_in_code (List.cons_ne_nil _ _)
    (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b36_next)) hok1 (hwf2 _) (hm2 _) run_b37 (o := 8)
    (by decide +kernel) (by decide) fun st2 hok2 hs2 hm2' hpc2 ↦ ?_
  simp only [PcOk] at hpc2
  rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_24_at] at hpc2
  have hd2 := hm2'.dmem_eq (hwf2 _) rfl
  have e2_r14 : reg st2.data .r14 = off (scA m0) (8 + 16 * (1 + placedOf layout cs (i + 1))) := by
    rw [show reg st2.data .r14 = _ from hm2'.regs .r14 _ rfl, eval_add64]
    show BitVec.ofNat 64 16 + reg st1.data .r14 = _
    rw [hc1.r14, BitVec.add_comm, off_add, hps]
    congr 1
  have k2 : ∀ r : Reg64, r ∈ [Reg64.rbx, .r12, .r13, .rbp, .r15] →
      reg st2.data r = reg st1.data r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact regKeep hm2' _ rfl
  -- `b31`: the claim's value, `EW::mul`
  have hok2' : Ok m0 st2.data 8 := hok2
  refine h.run hp b31_in_code (List.cons_ne_nil _ _) hpc2 hok2 (hok2.cl_wf h hi)
    (clMatch hok2 (by rw [k2 .r13 (by simp)]; exact hc1.r13)
      (by rw [k2 .rbp (by simp)]; exact hbp1)) run_b31 (o := 0)
    (by decide +kernel) (by decide) fun st3 hok3 hs3 hm3 hpc3 ↦ ?_
  have hval := hok2.val_load h hi (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b31Offset + b31.length)).toBitVec)
  refine h.mul hmul hok3 hpc3 fun st4 hpc4 hok4 hfs4 hret4 hcs4 hk4 hs4 ↦ ?_
  have hprod : ewRet st4.data = (scalesOf s layout cs).toList[1 + placedOf layout cs i] *
      cs[i].value := by
    rw [hret4]
    show EW.mul _ _ = EW.mul _ _
    rw [show reg st3.data .rdi = _ from hm3.regs .rdi _ rfl,
      show reg st3.data .rsi = _ from hm3.regs .rsi _ rfl,
      show reg st3.data .rdx = _ from hm3.regs .rdx _ rfl,
      show reg st3.data .rcx = _ from hm3.regs .rcx _ rfl]
    show EW.mul (ewArg (reg st2.data .rdi) (reg st2.data .rsi))
      (ewArg ((clEnv m0 st2.data i _).load 1 592 8) ((clEnv m0 st2.data i _).load 1 (592 + 8) 8)) = _
    rw [hval.1, hval.2, show reg st2.data .rdi = _ from hm2'.regs .rdi _ rfl,
      show reg st2.data .rsi = _ from hm2'.regs .rsi _ rfl]
    show EW.mul (ewArg ((frameEnv m0 st1.data 512 _ (fun _ ↦ 0) _).load 1 0 8)
      ((frameEnv m0 st1.data 512 _ (fun _ ↦ 0) _).load 1 (0 + 8) 8)) _ = _
    rw [hsj.1, hsj.2]
    rfl
  obtain ⟨hax4, hdx4⟩ := ewRet_halves hprod
  -- `b32`: the term added
  refine h.run hp b32_in_code (List.cons_ne_nil _ _) hpc4 hok4 (vars := fun _ ↦ 0) (hok4.wf0 h)
    hok4.m_reg run_b32 (o := 8) (by decide +kernel) (by decide) fun st5 hok5 hs5 hm5 hpc5 ↦ ?_
  simp only [PcOk] at hpc5
  have k4 : ∀ r : Reg64, r ∈ [Reg64.rbx, .r12, .r13, .r14, .rbp, .r15] →
      reg st4.data r = reg st2.data r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (hcs4 _ rfl).trans (regKeep hm3 _ rfl)
  -- the frame's words and the outputs from `b36` on
  have hd2' : st2.data.dmem = st1.data.dmem := hd2
  have hfw2 : FW st2.data.dmem m0 (fwA m0 layout cs ++ [(96, UInt64.ofBitVec (off (layA m0) 120))])
      := by rw [hd2']; exact hc1.fw.append (FW.one hw961)
  have hfw3 := FW.block_os (hok2.cl_wf h hi) hm3 rfl hfw2 [24, 40, 48, 56, 64, 32, 80, 88, 96]
    rfl (by decide +kernel)
  have hfw4 := hfw3.call hfs4 (le_of_map [24, 40, 48, 56, 64, 32, 80, 88, 96] rfl (by decide))
  have hfw5 := FW.block_os (hok4.wf0 h) hm5 rfl hfw4 [24, 40, 48, 56, 64, 32, 80, 88, 96] rfl
    (by decide +kernel)
  have h72_2 : NativeRustcVm.WordAt st2.data.dmem (off (stackBelow m0 512) 72)
      (accOf s layout target cs value (1 + placedOf layout cs i)).c1 := by rw [hd2']; exact hc1.hi72
  have h72_3 := (FW.block_os (L := [(72, _)]) (hok2.cl_wf h hi) hm3 rfl (FW.one h72_2) [72] rfl
    (by decide +kernel))
  have h72_4 := h72_3.call hfs4 (le_of_map [72] rfl (by decide))
  have hout2 : Outs a s layout cs m0 st2.data.dmem := by rw [hd2']; exact hc1.out
  have hout3 := Outs.keep h hout2 (hm3.kept (hok2.cl_wf h hi)) (h.blk_stack hs3)
  have hout5 := Outs.keep h (Outs.keep h hout3 hk4 hs4) (hm5.kept (hok4.wf0 h)) (h.blk_stack hs5)
  have w72 : NativeRustcVm.WordAt st5.data.dmem (off (stackBelow m0 512) 72)
      (accOf s layout target cs value (1 + placedOf layout cs (i + 1))).c1 := by
    have := fw_write hm5 (o := 72) (by omega) (v := .bin .xor .W64 (.load 0 72 8) (.reg .rdx))
      (by decide +kernel)
    rw [eval_xor64, show (Sym.load 0 72 8).eval (frameEnv m0 st4.data 512 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b32Offset + b32.length)).toBitVec) = _ from fw_load h72_4 List.mem_cons_self,
      show (Sym.reg .rdx).eval (frameEnv m0 st4.data 512 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b32Offset + b32.length)).toBitVec) = reg st4.data .rdx from rfl, hdx4] at this
    rw [hacc]
    exact this
  have e5_rbx : reg st5.data .rbx =
      (accOf s layout target cs value (1 + placedOf layout cs (i + 1))).c0.toBitVec := by
    rw [show reg st5.data .rbx = _ from hm5.regs .rbx _ rfl, eval_xor64]
    show reg st4.data .rbx ^^^ reg st4.data .rax = _
    rw [hax4, k4 .rbx (by simp), k2 .rbx (by simp), hc1.rbx, hacc]
    rfl
  have k5 : ∀ r : Reg64, r ∈ [Reg64.r12, .r13, .r14, .rbp, .r15] →
      reg st5.data r = reg st2.data r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact (regKeep hm5 _ rfl).trans (k4 _ (by simp))
  refine cont st5 (hpc5.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b32_next))
    ⟨⟨hok5, hout5, hfw5.left, w72, e5_rbx,
      by rw [k5 .r13 (by simp), k2 .r13 (by simp)]; exact hc1.r13,
      by rw [k5 .r14 (by simp)]; exact e2_r14,
      by rw [k5 .r12 (by simp), k2 .r12 (by simp)]; exact hc1.r12⟩,
      hfw5.right.get List.mem_cons_self, hi,
      by rw [k5 .rbp (by simp), k2 .rbp (by simp)]; exact hbp1,
      by rw [k5 .r15 (by simp), k2 .r15 (by simp)]; exact h151⟩

/-- **A step of the target's loop**: claim `i`, from the head `b34` to `b33`. -/
theorem tgt_step (h : Parts a s layout target coefficients point slices cs z value m0)
    (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {i : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b34Offset))
    (ht : Tgt a s layout target cs value m0 i st.data) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b33Offset) →
      Done a s layout target cs value m0 i st'.data → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hc := ht.acc
  have hok := hc.ok
  have hi := ht.hi
  have hcol := hok.col_load h hi (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b34Offset + b34.length)).toBitVec)
  -- `b34`: the column
  refine h.run hp b34_in_code (List.cons_ne_nil _ _) hpc hok (hok.cl_wf h hi)
    (clMatch hok hc.r13 ht.rbp) run_b34 (o := 8) (by decide +kernel) (by decide)
    fun st1 hok1 hs1 hm1 hpc1 ↦ ?_
  have hc1 := Acc.blk h hc (hok.cl_wf h hi) hm1 hok1 hs1 rfl (by decide +kernel)
    (by decide +kernel)
  have hw961 := (FW.block_os (L := [(96, _)]) (hok.cl_wf h hi) hm1 rfl (FW.one ht.w96) [96] rfl
    (by decide +kernel)).get List.mem_cons_self
  have hbp1 : (reg st1.data .rbp).toNat = 608 * i := by rw [regKeep hm1 .rbp rfl]; exact ht.rbp
  have h151 : (reg st1.data .r15).toNat = 608 * cs.size := by
    rw [regKeep hm1 .r15 rfl]; exact ht.r15
  have hax1 : (reg st1.data .rax).toNat = cs[i].column := by
    rw [show reg st1.data .rax = _ from hm1.regs .rax _ rfl]; exact hcol
  simp only [PcOk] at hpc1
  rw [eval_gt157] at hpc1
  rw [show ((Sym.load 1 0 8).eval (clEnv m0 st.data i (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b34Offset + b34.length)).toBitVec)).toNat
    = cs[i].column from hcol] at hpc1
  by_cases hgt : 157 < cs[i].column
  · simp only [hgt, decide_true, ↓reduceIte] at hpc1
    rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_25_at] at hpc1
    refine cont st1 hpc1 (Done.skip hc1 hw961 hi hbp1 h151 ?_)
    rw [hok1.bit_eq h hi]
    simp only [show ¬ cs[i].column ≤ 157 by omega, ↓reduceIte]
  · simp only [hgt, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    -- `b35`: the placement's `present` word
    have hl := (h.ins _ mem_lay).1
    have hlb : NativeRustcVm.Layout.layoutBytes = 3912 := rfl
    simp only [hlb] at hl
    have hwf2 : ∀ ret, (frameEnv m0 st1.data 512 [(layA m0, 3912)] (fun _ ↦ 0) ret).WF :=
      fun _ ↦ hok1.wf1 h hl.1.1 hl.1.2 hl.2
    have hm2 : ∀ ret, Match (frameEnv m0 st1.data 512 [(layA m0, 3912)] (fun _ ↦ 0) ret) place2S
        st1.data := fun _ ↦
      match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hok1.fr.rsp_eval, trivial⟩ trivial
        ⟨by show ((t3 (.reg .rax)).eval _).toNat < 472
            rw [toNat_t3 _ (by show (reg st1.data .rax).toNat < _; omega)]
            show 3 * (reg st1.data .rax).toNat < 472
            omega, trivial⟩
        ⟨by show (frameEnv m0 st1.data 512 _ (fun _ ↦ 0) _).load 0 96 8 = _
            rw [load_ofMachine (r := 0) rfl hw961]
            rfl, trivial⟩
    have hcle : cs[i].column ≤ 157 := by omega
    have hpl : ∀ ret, ((Sym.loadx 1 120 (.bin .mul .W64 (.bin .add .W64 (.reg .rax)
        (.bin .mul .W64 (.reg .rax) (.lit 2))) (.lit 8)) 8).eval
        (frameEnv m0 st1.data 512 [(layA m0, 3912)] (fun _ ↦ 0) ret)) =
          (NativeRustcVm.wordOf st1.data.dmem (off (layA m0) (120 + 24 * cs[i].column))).toBitVec
        := fun _ ↦ by
      show ((Sym.loadx 1 120 (.bin .mul .W64 (t3 (.reg .rax)) (.lit 8)) 8).eval _) = _
      show (frameEnv m0 st1.data 512 _ (fun _ ↦ 0) _).load 1 (120 + _) 8 = _
      rw [toNat_idx _ (by show (reg st1.data .rax).toNat < _; omega)]
      show (frameEnv m0 st1.data 512 _ (fun _ ↦ 0) _).load 1 (120 + 24 * (reg st1.data .rax).toNat) 8
        = _
      rw [hax1]
      exact load_ofMachine (r := 1) rfl (NativeRustcVm.wordAt_of_mapped
        (mapped_off (Mapped.keeps hl.1.1 hok1.fr.kept) (by omega)))
    refine h.run hp b35_in_code (List.cons_ne_nil _ _)
      (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b34_next)) hok1 (hwf2 _) (hm2 _) run_b35 (o := 8)
      (by decide +kernel) (by decide) fun st2 hok2 hs2 hm2' hpc2 ↦ ?_
    have hc2 := Acc.blk h hc1 (hwf2 _) hm2' hok2 hs2 rfl (by decide +kernel) (by decide +kernel)
    have hw962 := (FW.block_os (L := [(96, _)]) (hwf2 _) hm2' rfl (FW.one hw961) [96] rfl
      (by decide +kernel)).get List.mem_cons_self
    have hbp2 : (reg st2.data .rbp).toNat = 608 * i := by rw [regKeep hm2' .rbp rfl]; exact hbp1
    have h152 : (reg st2.data .r15).toNat = 608 * cs.size := by
      rw [regKeep hm2' .r15 rfl]; exact h151
    have hd2 : st2.data.dmem = st1.data.dmem := hm2'.dmem_eq (hwf2 _) rfl
    simp only [PcOk] at hpc2
    rw [eval_eq64, hpl, show ((Sym.lit 0).eval (frameEnv m0 st1.data 512 [(layA m0, 3912)]
      (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b35Offset + b35.length)).toBitVec)).toNat = 0 from rfl] at hpc2
    have hbit := hok1.bit_eq h hi (layout := layout)
    simp only [hcle, ↓reduceIte] at hbit
    by_cases hw0 : NativeRustcVm.wordOf st1.data.dmem (off (layA m0) (120 + 24 * cs[i].column)) = 0
    · have hz : (NativeRustcVm.wordOf st1.data.dmem
          (off (layA m0) (120 + 24 * cs[i].column))).toBitVec.toNat = 0 := by rw [hw0]; rfl
      simp only [hz, decide_true, ↓reduceIte] at hpc2
      rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_25_at] at hpc2
      refine cont st2 hpc2 (Done.skip hc2 hw962 hi hbp2 h152 ?_)
      rw [hbit, hw0]
      rfl
    · have hz : ¬ (NativeRustcVm.wordOf st1.data.dmem
          (off (layA m0) (120 + 24 * cs[i].column))).toBitVec.toNat = 0 := fun e ↦
        hw0 (UInt64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (by rw [e]; rfl)))
      simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc2
      have hb1 : bitAt layout cs i = 1 := by rw [hbit]; simp [hw0]
      have hpls : (cs[i].onStack layout).isSome := by
        have := bitAt_eq (layout := layout) hi
        rw [hb1] at this
        by_contra hn
        simp [hn] at this
      exact placed_b36 h hp hmul (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b35_next)) hc2
        hw962 hi hbp2 h152 hpls cont

/-- **The target's loop**: from the head before claim `i`, to `b38`. -/
theorem tgt_run (h : Parts a s layout target coefficients point slices cs z value m0)
    (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {R : MachineState → Prop}
    (fin : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b38Offset) →
      Acc a s layout target cs value m0 cs.size st'.data → Eventually (step1 Host.exe) R st') :
    ∀ d i (st : MachineState), cs.size - i = d → st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b34Offset) →
      Tgt a s layout target cs value m0 i st.data → Eventually (step1 Host.exe) R st := by
  intro d
  induction d with
  | zero => intro i st hd _ ht; have := ht.hi; omega
  | succ d ih =>
    intro i st hd hpc ht
    exact tgt_step h hp hmul hpc ht fun st1 hpc1 hD ↦ mid_b33 h hp hpc1 hD
      (fun st2 hpc2 ht2 ↦ ih (i + 1) st2 (by omega) hpc2 ht2) fin

end

end NativeRustcVmX64.Whir.VerifyStackedOpening
