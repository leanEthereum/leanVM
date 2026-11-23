module

public import NativeRustcVmX64.Whir.VerifyStackedOpening.TgtLoop
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `verify_stacked_opening`: the out-of-domain term (x86-64)

`ood_b38`: from `b38` (`Acc` after every claim), `b38` reads the out-of-domain claim's address (the
stack argument `0`) and finds a scale left (`b39` loads it; never `b40`), `b41` its value and the
layout, `EW::mul`: at `b42` (`AtB42`). `claim_eq`: the last term completes the batched target
`dot scales values` (`claimOf`).
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVmX64.Vm.VerifyStackedOpening

@[expose] public section

/-- The batched target. -/
def claimOf (s : TState) (layout : LayoutW) (target : EW) (cs : Array ColumnClaimW) (value : EW) :
    EW :=
  accOf s layout target cs value (cntOf layout cs)

/-- **At `b42`**: the out-of-domain term in RAX, RDX, the others' sum in RBX and the frame's
`72`, the layout in R14, the out-of-domain claim in R15. -/
structure AtB42 [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (target : EW)
    (cs : Array ColumnClaimW) (value : EW) (m0 st : MachineData) : Prop where
  ok : Ok m0 st 8
  out : Outs a s layout cs m0 st.dmem
  fw : FW st.dmem m0 (fwA m0 layout cs)
  hi72 : NativeRustcVm.WordAt st.dmem (off (stackBelow m0 512) 72)
    (accOf s layout target cs value (1 + placedOf layout cs cs.size)).c1
  rbx : reg st .rbx = (accOf s layout target cs value (1 + placedOf layout cs cs.size)).c0.toBitVec
  sum : accOf s layout target cs value (1 + placedOf layout cs cs.size) + ewRet st =
    claimOf s layout target cs value
  r14 : reg st .r14 = layA m0
  r15 : reg st .r15 = oA m0

end

public section

/-- **The last term** completes the batched target. -/
theorem claim_eq (s : TState) (layout : LayoutW) (target : EW) (cs : Array ColumnClaimW)
    (value : EW) :
    ∃ hj : 1 + placedOf layout cs cs.size < (scalesOf s layout cs).toList.length,
      claimOf s layout target cs value = accOf s layout target cs value
        (1 + placedOf layout cs cs.size) +
          (scalesOf s layout cs).toList[1 + placedOf layout cs cs.size] * value := by
  have hl : 1 + placedOf layout cs cs.size < (scalesOf s layout cs).toList.length := by
    rw [length_scalesOf]; unfold cntOf; omega
  have hr : 1 + placedOf layout cs cs.size < (valsOf layout target cs value).length := by
    rw [length_valsOf]; omega
  refine ⟨hl, ?_⟩
  unfold claimOf accOf
  rw [show cntOf layout cs = 1 + placedOf layout cs cs.size + 1 by unfold cntOf; omega,
    dotL_take_succ hl hr]
  have hv : (valsOf layout target cs value)[1 + placedOf layout cs cs.size]? = some value := by
    have hl' : ((cs.toList.filterMap (·.onStack layout)).map (·.value)).length =
        placedOf layout cs cs.size := by
      simp [placedOf, List.take_of_length_le]
    rw [Nat.add_comm, valsOf, List.getElem?_cons_succ, List.getElem?_append_right (by omega), hl',
      Nat.sub_self]
    rfl
  obtain ⟨_, he⟩ := List.getElem?_eq_some_iff.mp hv
  rw [he]

/-- The batched target is `dot` of the scales and the stack claims' values. -/
theorem claimOf_eq (s : TState) (layout : LayoutW) (target : EW) (point coefficients : Array EW)
    (cs : Array ColumnClaimW) (z : Array EW) (value : EW) :
    dot (powers (sq s).1 (stackClaims layout target point coefficients cs z value).size)
      ((stackClaims layout target point coefficients cs z value).map (·.value)) =
        claimOf s layout target cs value := by
  rw [dot_eq, vals_stackClaims, size_stackClaims]
  unfold claimOf accOf
  rw [List.take_of_length_le (by rw [length_scalesOf]),
    List.take_of_length_le (by rw [length_valsOf])]

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- **The out-of-domain term**: `b38`, `b39`, `b41`, `EW::mul`, to `b42`. -/
theorem ood_b38 (h : Parts a s layout target coefficients point slices cs z value m0)
    (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b38Offset))
    (hc : Acc a s layout target cs value m0 cs.size st.data) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b42Offset) →
      AtB42 a s layout target cs value m0 st'.data → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hok := hc.ok
  have hn := h.n_le
  have hP := (placedOf_le_self (layout := layout) (cs := cs) cs.size).trans hn
  have hscn := h.sc_nw
  have hsc8 := h.sc8_le (layout := layout)
  have hsb : scalesBytes = 2600 := rfl
  have hscn' : (scA m0).toNat + 2600 ≤ 2 ^ 64 := hscn
  have hsc8' : 8 + 16 * cntOf layout cs ≤ 2600 := hsc8
  have hcnt : cntOf layout cs = placedOf layout cs cs.size + 2 := rfl
  have hscap : NativeRustcVm.Apart (scA m0) scalesBytes (stackBelow m0 verifyStackedOpeningStack)
      (verifyStackedOpeningStack + 8) := h.so.1.2.2.2.2.1
  obtain ⟨hj, hclaim⟩ := claim_eq s layout target cs value
  obtain ⟨ham, hanw, haap⟩ := h.arg_ok
  -- `b38`: the out-of-domain claim's address
  have hwf1 : ∀ ret, (frameEnv m0 st.data 512 [(rspOf m0 + 8#64, 24)] (fun _ ↦ 0) ret).WF :=
    fun _ ↦ hok.wf1 h ham hanw haap
  have hm1 : ∀ ret, Match (frameEnv m0 st.data 512 [(rspOf m0 + 8#64, 24)] (fun _ ↦ 0) ret) argS
      st.data := fun _ ↦
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hok.fr.rsp_eval, trivial⟩ trivial trivial argAl_ok
  refine h.run hp b38_in_code (List.cons_ne_nil _ _) hpc hok (hwf1 _) (hm1 _) run_b38 (o := 8)
    (by decide +kernel) (by decide) fun st1 hok1 hs1 hm1' hpc1 ↦ ?_
  have hc1 := Acc.blk h hc (hwf1 _) hm1' hok1 hs1 rfl (by decide +kernel) (by decide +kernel)
  have e1_15 : reg st1.data .r15 = oA m0 := by
    rw [show reg st1.data .r15 = _ from hm1'.regs .r15 _ rfl]
    exact hok.argLoad h (i := 0) (by omega)
  simp only [PcOk] at hpc1
  rw [eval_eq64] at hpc1
  have hne : ¬ (((Sym.reg .r14).eval (frameEnv m0 st.data 512 [(rspOf m0 + 8#64, 24)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b38Offset + b38.length)).toBitVec)).toNat = ((Sym.reg .r12).eval
        (frameEnv m0 st.data 512 [(rspOf m0 + 8#64, 24)] (fun _ ↦ 0)
          (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b38Offset + b38.length)).toBitVec)).toNat) := by
    show ¬ (reg st.data .r14).toNat = (reg st.data .r12).toNat
    have h1 : (scA m0).toNat + (8 + 16 * (1 + placedOf layout cs cs.size)) < 2 ^ 64 := by omega
    rw [hc.r14, hc.r12, toNat_off h1]
    rcases NativeRustcVm.toNat_add_ofNat_le (a := scA m0) (i := 8 + 16 * cntOf layout cs)
      (by omega) with e | ⟨e, _⟩
    · rw [e]; omega
    · rw [e]; omega
  simp only [hne, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  -- `b39`: the last scale
  have jo : 8 + 16 * (1 + placedOf layout cs cs.size) + 16 ≤ 2600 := by omega
  have hwf2 : ∀ ret, (frameEnv m0 st1.data 512 [(off (scA m0)
      (8 + 16 * (1 + placedOf layout cs cs.size)), 16)] (fun _ ↦ 0) ret).WF := fun _ ↦
    hok1.wf1 h (mapped_off h.so.1.1 (by omega)) (noWrap_off' hscn (by omega) (by omega)) (by
      have hh := hscap
      have hsbe := h.sb
      unfold NativeRustcVm.Apart at hh ⊢
      rw [hsb] at hh
      rw [toNat_off (by omega)]
      omega)
  have hm2 : ∀ ret, Match (frameEnv m0 st1.data 512 [(off (scA m0)
      (8 + 16 * (1 + placedOf layout cs cs.size)), 16)] (fun _ ↦ 0) ret) scaleS st1.data :=
    fun _ ↦ match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hok1.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨by show reg st1.data .r14 = _
          rw [hc1.r14, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; rfl, trivial⟩
  have hsj := ew_loads (d := st1.data) (vs := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b39Offset + b39.length)).toBitVec)
    (rs := [(stackBelow m0 512, 520), (off (scA m0) (8 + 16 * (1 + placedOf layout cs cs.size)),
      16)])
    (b := off (scA m0) (8 + 16 * (1 + placedOf layout cs cs.size))) (n := 16) (r := 1) (o := 0)
    (x := (scalesOf s layout cs).toList[1 + placedOf layout cs cs.size]) rfl (by
      rw [off_zero, ← off_off]
      exact hc1.out.scs.getElem hj)
  refine h.run hp b39_in_code (List.cons_ne_nil _ _)
    (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b38_next)) hok1 (hwf2 _) (hm2 _) run_b39 (o := 8)
    (by decide +kernel) (by decide) fun st2 hok2 hs2 hm2' hpc2 ↦ ?_
  simp only [PcOk] at hpc2
  rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_34_at] at hpc2
  have hc2 := Acc.blk h hc1 (hwf2 _) hm2' hok2 hs2 rfl (by decide +kernel) (by decide +kernel)
  have e2_15 : reg st2.data .r15 = oA m0 := by rw [regKeep hm2' .r15 rfl]; exact e1_15
  -- `b41`: the out-of-domain value, the layout, `EW::mul`
  have hood := (h.ins _ mem_ood).1
  have heb : NativeRustcVm.Layout.eqClaimBytes = 504 := rfl
  simp only [heb] at hood
  have hwf3 : ∀ ret, (frameEnv m0 st2.data 512 [(oA m0, 504)] (fun _ ↦ 0) ret).WF := fun _ ↦
    hok2.wf1 h hood.1.1 hood.1.2 hood.2
  have hm3 : ∀ ret, Match (frameEnv m0 st2.data 512 [(oA m0, 504)] (fun _ ↦ 0) ret) oodS st2.data :=
    fun _ ↦ match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hok2.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨by show reg st2.data .r15 = _
          rw [e2_15, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; rfl, trivial⟩
  have hval := ew_loads (d := st2.data) (vs := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b41Offset + b41.length)).toBitVec)
    (rs := [(stackBelow m0 512, 520), (oA m0, 504)]) (b := oA m0) (n := 504) (r := 1) (o := 488)
    (x := value) rfl
    (NativeRustcVm.Layout.EWAt.of_same h.ood.2 ((hok2.same_in h mem_ood).sub (o := 488) (k := 16)
      (by show 488 + 16 ≤ 504; decide)) le_rfl)
  refine h.run hp b41_in_code (List.cons_ne_nil _ _) hpc2 hok2 (hwf3 _) (hm3 _) run_b41 (o := 0)
    (by decide +kernel) (by decide) fun st3 hok3 hs3 hm3' hpc3 ↦ ?_
  have hout3 := Outs.keep h hc2.out (hm3'.kept (hwf3 _)) (h.blk_stack hs3)
  have hfw3 := FW.block_os (hwf3 _) hm3' rfl (hc2.fw.append (FW.one hc2.hi72))
    [24, 40, 48, 56, 64, 32, 80, 88, 72] rfl (by decide +kernel)
  have e3_14 : reg st3.data .r14 = layA m0 := by
    rw [show reg st3.data .r14 = _ from hm3'.regs .r14 _ rfl]
    show (frameEnv m0 st2.data 512 _ (fun _ ↦ 0) _).load 0 32 8 = _
    rw [fw_load hc2.fw (o := 32) (v := UInt64.ofBitVec (layA m0)) (by simp [fwA])]
  refine h.mul hmul hok3 hpc3 fun st4 hpc4 hok4 hfs4 hret4 hcs4 hk4 hs4 ↦ ?_
  have hprod : ewRet st4.data = (scalesOf s layout cs).toList[1 + placedOf layout cs cs.size] *
      value := by
    rw [hret4]
    show EW.mul _ _ = EW.mul _ _
    rw [show reg st3.data .rdi = _ from regKeep hm3' .rdi rfl,
      show reg st3.data .rsi = _ from regKeep hm3' .rsi rfl,
      show reg st3.data .rdx = _ from hm3'.regs .rdx _ rfl,
      show reg st3.data .rcx = _ from hm3'.regs .rcx _ rfl,
      show reg st2.data .rdi = _ from hm2'.regs .rdi _ rfl,
      show reg st2.data .rsi = _ from hm2'.regs .rsi _ rfl]
    show EW.mul (ewArg ((frameEnv m0 st1.data 512 _ (fun _ ↦ 0) _).load 1 0 8)
      ((frameEnv m0 st1.data 512 _ (fun _ ↦ 0) _).load 1 (0 + 8) 8))
      (ewArg ((frameEnv m0 st2.data 512 _ (fun _ ↦ 0) _).load 1 488 8)
        ((frameEnv m0 st2.data 512 _ (fun _ ↦ 0) _).load 1 (488 + 8) 8)) = _
    rw [hsj.1, hsj.2, hval.1, hval.2]
    rfl
  have hfw4 := hfw3.call hfs4 (le_of_map [24, 40, 48, 56, 64, 32, 80, 88, 72] rfl (by decide))
  refine cont st4 (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b41_next))
    ⟨hok4, Outs.keep h hout3 hk4 hs4, hfw4.left, hfw4.right.get List.mem_cons_self,
      by rw [hcs4 .rbx rfl, regKeep hm3' .rbx rfl]; exact hc2.rbx,
      by rw [hprod, ← hclaim], by rw [hcs4 .r14 rfl]; exact e3_14,
      by rw [hcs4 .r15 rfl, regKeep hm3' .r15 rfl]; exact e2_15⟩

end

end NativeRustcVmX64.Whir.VerifyStackedOpening
