module

public import NativeRustcVmArm.Code.Vm.FormTerms.Names
public import NativeRustcVmArm.Code.Vm.Names
public import NativeRustcVmArm.Layout.FormTerms.Exec
public import NativeRustcVm.Layout.Forms

/-!
# `form_terms`

One environment, region 0 `FORMS` at its label. A form above `592` (`b0`'s branch, `b2`): the
empty slice, and `formAt` is empty there (`593` forms). Else `b1` loads the form's span
(`forms_words`), which lies in `TERMS` (`formStart_add_le`), and returns its terms
(`termsAt_formAt`).
-/

namespace NativeRustcVmArm.Layout.FormTerms

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.FormTerms
open NativeVm.Model NativeRustcVm.Layout NativeRustcVm.Data
open NativeRustcVm.Transcript (off)

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

theorem toBitVec_toUInt64 (n : Nat) : n.toUInt64.toBitVec = BitVec.ofNat 64 n := rfl

/-- `b1`'s checks pass on a span inside `TERMS`: its end does not wrap, and is below `770`. -/
theorem span_ult (s l : Nat) (h : s + l ≤ 769) :
    (BitVec.ofNat 64 l + BitVec.ofNat 64 s).ult (BitVec.ofNat 64 s) = false ∧
      (BitVec.ofNat 64 l + BitVec.ofNat 64 s).ult (BitVec.ofNat 64 770) = true := by
  have hl : (BitVec.ofNat 64 l + BitVec.ofNat 64 s).toNat = l + s := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  constructor
  · unfold BitVec.ult
    rw [hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp
  · unfold BitVec.ult
    rw [hl, BitVec.toNat_ofNat]
    simp
    omega

variable [Host] {k : Nat}

/-- **`form_terms`' contract.** -/
theorem formTerms_spec (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmArm.Vm.FormTerms.entryLabel) FormTermsPre FormTermsPost := by
  intro m hR
  have hF := hR.bytesAt .forms
  have hT := hR.bytesAt .terms
  have hFn := hR.noWrap .forms
  change BytesAt m.dmem (rodataAddr .forms) (NativeRustcVm.Data.forms.flatMap Span.bytes) at hF
  change BytesAt m.dmem (rodataAddr .terms) (NativeRustcVm.Data.terms.flatMap Term.bytes) at hT
  change NativeRustcVm.NoWrap _ (NativeRustcVm.Data.forms.flatMap Span.bytes).length at hFn
  rw [length_forms_bytes] at hFn
  let env := Env.ofMachine m [(rodataAddr .forms, 9488)]
  have hwf : env.WF := Env.wf_of
    ⟨⟨by have := NativeRustcVm.BytesAt.mapped (d := m.dmem) hF; rwa [length_forms_bytes] at this,
      hFn⟩, trivial⟩
    (List.pairwise_singleton _ _)
  have hm : Match env entryS m :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial ⟨rfl, trivial⟩ trivial trivial
  have hx30 : env.regs .X30 = m.regs.X30.toBitVec := rfl
  rw [show Labels.label NativeRustcVmArm.Vm.FormTerms.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.FormTerms.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.FormTerms.entryOffset) NativeRustcVmArm.Vm.FormTerms.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf hm fun st hm1 hpc ↦ ?_
  simp only [PcOk] at hpc
  sym_simp at hpc
  have hx0 : env.regs .X0 = m.regs.X0.toBitVec := rfl
  by_cases hi : 592 < m.regs.X0.toNat
  · -- `b2`: the empty slice.
    have hc : (!(m.regs.X0.toBitVec.ult (BitVec.ofNat 64 592)) &&
        !(m.regs.X0.toBitVec == BitVec.ofNat 64 592)) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_false_iff_not, beq_eq_false_iff_ne]
      refine ⟨by show ¬ m.regs.X0.toNat < 592 % 2 ^ 64; omega, fun he ↦ ?_⟩
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat] at this
      show False
      have : m.regs.X0.toNat = 592 := this
      omega
    simp only [hx0, hc, ↓reduceIte] at hpc
    rw [hp.label (j := NativeRustcVmArm.Vm.FormTerms.b2Offset) NativeRustcVmArm.Vm.FormTerms.label_2_at] at hpc
    refine exec_at (infix_of b2_in_code (by simp [b2]) hp) (exec_after run_b0 run_b2) hwf hpc
      hm1 fun st2 hm2 hpc2 ↦ .done _ ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [PcOk] at hpc2
      exact hpc2.trans (retOf_of_x30 hm2 rfl hx30)
    · rw [formAt_of_ge (by omega)]
      have := hm2.regs .X1 _ rfl
      show (st2.data.regs.getXReg .X1).toBitVec.toNat = 0
      rw [this]; rfl
    · rw [formAt_of_ge (by omega)]
      intro j hj; exact absurd hj (by simp)
    · rw [formAt_of_ge (by omega)]; exact Or.inl rfl
    · exact NativeRustcVm.SameOutside.of_eq (hm2.dmem_eq hwf rfl) _
    · exact Match.saved hm hm2 hwf rfl (by decide)
  · -- `b1`: the form's span.
    have hi' : m.regs.X0.toNat < NativeRustcVm.Data.allForms.length := by rw [allForms_length]; omega
    have hc : (!(m.regs.X0.toBitVec.ult (BitVec.ofNat 64 592)) &&
        !(m.regs.X0.toBitVec == BitVec.ofNat 64 592)) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Bool.and_eq_false_imp, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_false_iff_not, Bool.not_false, beq_iff_eq]
      intro h
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      show m.regs.X0.toNat = 592 % 2 ^ 64
      have : ¬ m.regs.X0.toNat < 592 % 2 ^ 64 := h
      omega
    simp only [hx0, hc, Bool.false_eq_true, ↓reduceIte] at hpc
    rw [NativeRustcVmArm.Vm.FormTerms.b0_length, NativeRustcVmArm.Vm.FormTerms.b0Length] at hpc
    have hm1' : Match env S1 st.data := by
      have := hm1.addBound (x := .reg .X0) (n := 593) (by show m.regs.X0.toNat < 593; omega)
      rwa [← after_eq run_b0] at this
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf hpc hm1'
      fun st2 hm2 hpc2 ↦ .done _ ?_
    obtain ⟨hws, hwl⟩ := forms_words hF _ hi'
    have hidx : (m.regs.X0.toBitVec <<< 4).toNat = 16 * m.regs.X0.toNat := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      show m.regs.X0.toNat * 2 ^ 4 % 2 ^ 64 = _
      omega
    have hls : env.load 0 (0 + (m.regs.X0.toBitVec <<< 4).toNat) 8 =
        BitVec.ofNat 64 (formStart m.regs.X0.toNat) := by
      rw [hidx, Nat.zero_add]; exact load_word hws
    have hll : env.load 0 (8 + (m.regs.X0.toBitVec <<< 4).toNat) 8 =
        BitVec.ofNat 64 NativeRustcVm.Data.allForms[m.regs.X0.toNat].terms.length := by
      rw [hidx, Nat.add_comm]
      refine load_word ?_
      rw [← NativeRustcVm.addr_add_add]; exact hwl
    have hle := formStart_add_le _ hi'
    rw [terms_length] at hle
    obtain ⟨e1, e2⟩ := span_ult _ _ hle
    have h0 := hm2.regs .X0 _ rfl
    have h1 := hm2.regs .X1 _ rfl
    sym_simp at h0 h1
    simp only [hx0, hls, hll, e1, e2, Bool.not_false, Bool.not_true, ↓reduceIte] at h0 h1
    have haddr : st2.data.regs.X0.toBitVec = off (rodataAddr .terms)
        (termBytes * formStart m.regs.X0.toNat) := by
      rw [show (st2.data.regs.X0).toBitVec = (st2.data.regs.getXReg .X0).toBitVec from rfl, h0,
        off]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, termBytes]
      rw [show (rodataAddr .terms) = (Labels.label NativeRustcVmArm.Vm.Symbols.rodata14Label).toBitVec
        from rfl]
      show (formStart m.regs.X0.toNat % 2 ^ 64 * (40 % 2 ^ 64) % 2 ^ 64 +
          (rodataAddr .terms).toNat) % 2 ^ 64 =
        ((rodataAddr .terms).toNat + 40 * formStart m.regs.X0.toNat % 2 ^ 64) % 2 ^ 64
      omega
    have hdm : st2.data.dmem = m.dmem := hm2.dmem_eq hwf rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [PcOk] at hpc2
      exact hpc2.trans (retOf_of_x30 hm2 rfl hx30)
    · rw [size_formAt hi']
      show (st2.data.regs.getXReg .X1).toBitVec.toNat = _
      rw [h1, BitVec.toNat_ofNat]
      omega
    · rw [haddr, hdm]; exact termsAt_formAt hT _ hi'
    · rw [size_formAt hi']
      exact Or.inr ⟨_, by rw [terms_length]; exact hle, haddr⟩
    · exact NativeRustcVm.SameOutside.of_eq hdm _
    · exact Match.saved hm hm2 hwf rfl (by decide)

end

end NativeRustcVmArm.Layout.FormTerms
