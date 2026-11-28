module

public import NativeRustcVmX64.Layout.FormTerms.Exec
public import NativeRustcVm.Layout.Forms
public import NativeRustcVmX64.Code.Vm.FormTerms.Names
public import NativeRustcVmX64.Code.Vm.Names

/-!
# `form_terms` on x86-64

Region 0 of the environments the return address at RSP, region 1 `FORMS` at its label. A form
above `592` (`b0`'s branch, `b2`): the empty slice, and `formAt` is empty there (`593` forms).
Else `b1` loads the form's span (`forms_words`), which lies in `TERMS` (`formStart_add_le`), and
returns its terms (`termsAt_formAt`). Nothing is written.
-/

namespace NativeRustcVmX64.Layout.FormTerms

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.FormTerms
open NativeVm.Model NativeRustcVm.Layout NativeRustcVm.Data
open NativeRustcVm.Transcript (off)
open NativeRustcVmX64.Transcript (after after_eq exec_after infix_of infix_take infix_drop
  frameEnv)

public section

theorem formAt_of_ge {i : Nat} (h : 593 ≤ i) : formAt i = #[] := by
  unfold formAt
  rw [List.getElem?_eq_none (by rw [allForms_length]; exact h)]
  rfl

theorem formAt_of_lt {i : Nat} (h : i < NativeRustcVm.Data.allForms.length) :
    formAt i = FormW.ofForm NativeRustcVm.Data.allForms[i] := by
  simp [formAt, List.getElem?_eq_getElem h]

theorem size_formAt {i : Nat} (h : i < NativeRustcVm.Data.allForms.length) :
    (formAt i).size = NativeRustcVm.Data.allForms[i].terms.length := by
  simp [formAt_of_lt h, FormW.ofForm]

/-- `setae`, `setb`, `testb` of two set bytes: not zero. -/
theorem test_merge_one (x y : BitVec 64) :
    CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (BinOp.apply .merge .W8 x (BitVec.ofNat 64 1))
      (BinOp.apply .merge .W8 y (BitVec.ofNat 64 1))) (BitVec.ofNat 64 0) = false := by
  simp only [BinOp.apply, CmpOp.apply, Transcript.low8_replaceLow]
  decide

variable [Host] {k : Nat}

/-- **`form_terms`' contract.** -/
theorem formTerms_spec (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmX64.Vm.FormTerms.entryLabel) FormTermsPre FormTermsPost := by
  rintro m ⟨hst, hR⟩
  have hF := hR.bytesAt .forms
  have hT := hR.bytesAt .terms
  have hFn := hR.noWrap .forms
  have hFa := hR.apart .forms
  change BytesAt m.dmem (rodataAddr .forms) (NativeRustcVm.Data.forms.flatMap Span.bytes) at hF
  change BytesAt m.dmem (rodataAddr .terms) (NativeRustcVm.Data.terms.flatMap Term.bytes) at hT
  change NativeRustcVm.NoWrap _ (NativeRustcVm.Data.forms.flatMap Span.bytes).length at hFn
  change NativeRustcVm.Apart _ (NativeRustcVm.Data.forms.flatMap Span.bytes).length _ _ at hFa
  rw [length_forms_bytes] at hFn hFa
  have hFm : NativeRustcVm.Mapped m.dmem (rodataAddr .forms) 9488 := by
    have := NativeRustcVm.BytesAt.mapped (d := m.dmem) hF; rwa [length_forms_bytes] at this
  have hrest : ∀ d : MachineData, d.dmem = m.dmem → ∀ x ∈ [(rodataAddr .forms, 9488)],
      NativeRustcVm.Mapped d.dmem x.1 x.2 ∧ NativeRustcVm.NoWrap x.1 x.2 := by
    intro d hd x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact ⟨hd ▸ hFm, hFn⟩
  have hap : ((stackBelow m 0, 0 + 8) :: [(rodataAddr .forms, 9488)]).Pairwise
      fun x y ↦ NativeRustcVm.Apart x.1 x.2 y.1 y.2 :=
    List.pairwise_pair.mpr (Transcript.Apart.symm' hFa)
  have hfr : NativeRustcVm.Mapped m.dmem (stackBelow m 0) (0 + 8) ∧
      NativeRustcVm.NoWrap (stackBelow m 0) (0 + 8) :=
    ⟨Transcript.frame_mapped hst (Nat.zero_le _), Transcript.frame_noWrap hst (Nat.zero_le _)⟩
  have hwf := Transcript.frame_wf (m0 := m) (d := m) (F := 0) (rest := [(rodataAddr .forms, 9488)])
    (vars := fun _ ↦ 0) (ret := 0) hfr (hrest m rfl) hap
  have hlbl : (frameEnv m m 0 [(rodataAddr .forms, 9488)]).base 1 =
      (Labels.label NativeRustcVmX64.Vm.Symbols.rodata13Label).toBitVec := rfl
  have hm : Match (frameEnv m m 0 [(rodataAddr .forms, 9488)]) entryS m :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨rsp_ptr0 rfl, trivial⟩ ⟨hlbl, trivial⟩ trivial trivial
  rw [show Labels.label NativeRustcVmX64.Vm.FormTerms.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.FormTerms.b0Offset) from hp.label NativeRustcVmX64.Vm.FormTerms.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf nofun hm fun st hm1 hpc ↦ ?_
  obtain ⟨hk1, hmem1, hsp1, hdi1⟩ := after_eq run_b0 ▸ ok_b0
  have hd1 : st.data.dmem = m.dmem := hm1.dmem_eq hwf hmem1
  have hs1 : Saved m st.data := Match.saved hm hm1 hwf rfl hk1
  have hrsp1 : rspOf st.data = rspOf m := (hm1.regs .rsp _ hsp1).trans (rsp_ptr0 rfl).symm
  have hrdi1 : reg st.data .rdi = reg m .rdi := hm1.regs .rdi _ hdi1
  simp only [PcOk] at hpc
  obtain ⟨hT1, hF1⟩ := Arrays.pc_cond hpc
  by_cases hi : 592 < (reg m .rdi).toNat
  · -- `b2`: the empty slice.
    have hpc2 := hT1 (by
      simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs, BitVec.ult,
        BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        beq_eq_false_iff_ne]
      refine ⟨by show ¬ (reg m .rdi).toNat < 592 % 2 ^ 64; omega, fun he ↦ ?_⟩
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat] at this
      have : (reg m .rdi).toNat = 592 := this
      omega)
    rw [hp.label NativeRustcVmX64.Vm.FormTerms.label_1_at] at hpc2
    refine Eventually.mono (leaf_retS (infix_of b2_in_code (by simp [b2]) hp) run_b2
      (after_eq run_b2 ▸ ok_b2).1 (after_eq run_b2 ▸ ok_b2).2.1 hst hpc2 hs1 hrsp1
      (fun _ _ ↦ by rw [hd1])
      (Q := fun d ↦ reg d .rax = BitVec.ofNat 64 8 ∧ reg d .rdx = 0#64 ∧ d.dmem = m.dmem)
      fun d hr hd ↦ ⟨(hr .rax _ (after_eq run_b2 ▸ ok_b2).2.2.1).trans rfl,
        (hr .rdx _ (after_eq run_b2 ▸ ok_b2).2.2.2).trans rfl, hd.trans hd1⟩)
      fun s ⟨h1, h2, ⟨ha, hd, hdm⟩, h4⟩ ↦ ⟨h1, h2, ?_, ?_, ?_, fun q _ ↦ by rw [hdm], h4⟩
    · rw [formAt_of_ge (by omega), hd]; rfl
    · rw [formAt_of_ge (by omega)]; intro j hj; exact absurd hj (by simp)
    · rw [formAt_of_ge (by omega)]; exact Or.inl rfl
  · -- `b1`: the form's span.
    have hi' : (reg m .rdi).toNat < NativeRustcVm.Data.allForms.length := by
      rw [allForms_length]; omega
    have hpc2 := hF1 (by
      simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs, BitVec.ult,
        BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        beq_eq_false_iff_ne, not_and, not_not]
      intro h
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      show (reg m .rdi).toNat = 592 % 2 ^ 64
      have : ¬ (reg m .rdi).toNat < 592 % 2 ^ 64 := h
      omega)
    rw [NativeRustcVmX64.Vm.FormTerms.b0_length] at hpc2
    refine exec_at (infix_of ((infix_take b1 1).trans b1_in_code (by simp [b1])) (by simp [b1]) hp)
      (exec_after run_b0 run_b1a) hwf nofun hpc2 hm1 fun st2 hm2 hpc3 ↦ ?_
    obtain ⟨hk2, hmem2, hsp2, hdi2⟩ := after_eq run_b1a ▸ ok_b1a
    have hd2 : st2.data.dmem = m.dmem := hm2.dmem_eq hwf hmem2
    have hs2 : Saved m st2.data := Match.saved hm hm2 hwf rfl hk2
    have hrsp2 : rspOf st2.data = rspOf m := (hm2.regs .rsp _ hsp2).trans (rsp_ptr0 rfl).symm
    have hrdi2 : reg st2.data .rdi = reg m .rdi <<< 4 := by
      rw [show reg st2.data .rdi = _ from hm2.regs .rdi _ hdi2]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rfl
    simp only [PcOk] at hpc3
    -- `b1b`, from `idxS`: the form in variable `0`.
    let env1 := frameEnv m st2.data 0 [(rodataAddr .forms, 9488)] (fun _ ↦ reg m .rdi)
    have hidx : ((Sym.bin .mul .W64 (.var 0) (.lit 16)).eval env1).toNat =
        16 * (reg m .rdi).toNat := by
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_mul, BitVec.toNat_ofNat, env1]
      show (reg m .rdi).toNat * (16 % 2 ^ 64) % 2 ^ 64 = _
      omega
    have hm3 : Match env1 idxS st2.data := by
      refine match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨rsp_ptr0 hrsp2, ?_, trivial⟩ ⟨rfl, trivial⟩
        ⟨?_, trivial⟩ trivial
      · show reg st2.data .rdi = _
        rw [hrdi2]
        apply BitVec.eq_of_toNat_eq
        rw [hidx, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
        show (reg m .rdi).toNat * 2 ^ 4 % 2 ^ 64 = _
        omega
      · show (reg m .rdi).toNat < 593
        omega
    obtain ⟨hws, hwl⟩ := forms_words hF _ hi'
    have hst0 : startS.eval env1 = (formStart (reg m .rdi).toNat).toUInt64.toBitVec := by
      show env1.load 1 (0 + _) 8 = _
      rw [hidx, Nat.zero_add]
      exact Arrays.load_word (by show NativeRustcVm.WordAt st2.data.dmem _ _; rw [hd2]; exact hws)
    have hln0 : lenS.eval env1 =
        NativeRustcVm.Data.allForms[(reg m .rdi).toNat].terms.length.toUInt64.toBitVec := by
      show env1.load 1 (8 + _) 8 = _
      rw [hidx, Nat.add_comm]
      refine Arrays.load_word ?_
      show NativeRustcVm.WordAt st2.data.dmem _ _
      rw [hd2, ← NativeRustcVm.addr_add_add]
      exact hwl
    have hle := formStart_add_le _ hi'
    rw [terms_length] at hle
    set s := formStart (reg m .rdi).toNat with hsdef
    set l := NativeRustcVm.Data.allForms[(reg m .rdi).toNat].terms.length with hldef
    have hsn : (s.toUInt64.toBitVec).toNat = s := by
      simp only [Nat.toUInt64_eq, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']; omega
    have hln : (l.toUInt64.toBitVec).toNat = l := by
      simp only [Nat.toUInt64_eq, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']; omega
    have hend : (endS.eval env1).toNat = l + s := by
      simp only [endS, Sym.eval, BinOp.apply, low_W64, ext_W64]
      rw [hst0, hln0, BitVec.toNat_add, hsn, hln]
      omega
    have hc : condS.eval env1 = true := by
      have hu1 : (endS.eval env1).ult (startS.eval env1) = false := by
        simp only [BitVec.ult, hend, hst0, hsn, decide_eq_false_iff_not]; omega
      have hu2 : (endS.eval env1).ult (BitVec.ofNat 64 770) = true := by
        simp only [BitVec.ult, hend, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
      simp only [condS, SBool.eval, Sym.eval, CmpOp.apply, low_W64, hu1, hu2, Bool.not_false,
        ite_true, BinOp.apply, Transcript.low8_replaceLow]
      decide
    refine Eventually.mono (leaf_ret (rest := [(rodataAddr .forms, 9488)])
      (infix_of ((infix_drop b1 1).trans b1_in_code (by simp [b1])) (by simp [b1]) hp) run_b1b
      (after_eq run_b1b ▸ ok_b1b).1 (after_eq run_b1b ▸ ok_b1b).2.1 hst
      (hpc3.trans (congrArg Host.addrOf (by have : (b1.take 1).length = 1 := rfl; omega)))
      hs2 hrsp2 (fun _ _ ↦ by rw [hd2]) (hrest st2.data hd2) hap hm3
      (Q := fun d ↦ reg d .rax = raxOut.eval env1 ∧ reg d .rdx = rdxOut.eval env1 ∧
        d.dmem = m.dmem)
      fun d hr hd ↦ ⟨hr .rax _ (after_eq run_b1b ▸ ok_b1b).2.2.1,
        hr .rdx _ (after_eq run_b1b ▸ ok_b1b).2.2.2, hd.trans hd2⟩)
      fun s' ⟨h1, h2, ⟨ha, hd, hdm⟩, h4⟩ ↦ ?_
    have haddr : reg s'.data .rax = off (rodataAddr .terms) (termBytes * s) := by
      rw [ha]
      simp only [raxOut, Sym.eval, hc, ite_true, BinOp.apply, low_W64, ext_W64]
      rw [hst0, off]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, hsn, termBytes]
      rw [show (rodataAddr .terms) = (Labels.label NativeRustcVmX64.Vm.Symbols.rodata14Label).toBitVec from rfl]
      simp only [show Width.W64.bits = 64 from rfl]
      omega
    refine ⟨h1, h2, ?_, ?_, ?_, fun q _ ↦ by rw [hdm], h4⟩
    · rw [size_formAt hi', hd]
      simp only [rdxOut, Sym.eval, hc, ite_true]
      rw [hln0, hln]
    · rw [haddr, hdm]; exact termsAt_formAt hT _ hi'
    · rw [size_formAt hi']
      exact Or.inr ⟨_, by rw [terms_length]; exact hle, haddr⟩

end

end NativeRustcVmX64.Layout.FormTerms
