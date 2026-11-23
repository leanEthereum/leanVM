module

public import NativeRustcVmArm.Code.Vm.BlockForm.Names
public import NativeRustcVmArm.Code.Vm.FormBufAddScaled.Names
public import NativeRustcVmArm.Code.Vm.FormTerms.Names
public import NativeRustcVmArm.Bus.BlockForm.Exec
public import NativeRustcVmArm.Bus.Frame
public import NativeRustcVm.Bus.Tuples

/-!
# `block_form`

`b0` saves X19-X25 and X30 in its 64-byte frame and sets the form to the constant `side_beta`;
`b1` reads the tuple's span from `TUPLES` (the tuple is below `147`, so `b0`'s branch past it is
never taken); `b2` sets the count. The loop head `.LBlockForm_5` (`b6`, `Inv`): the form at X5 is
`bf` of the first `j` slots. A turn (`step`): `form_terms` of the span's next form (`b7`), its
weight from `side_weights` or `0` (`b8`, `b3`/`b9`), `FormBuf::add_scaled` (`b4`); a failure
(the form outgrows its `FormBuf`) leaves the loop with X0 `0`, else back to the head (`b5`). The
epilogue `b10` returns `1` where the loop ran to the span's end (`finish`).
-/

namespace NativeRustcVmArm.Bus.BlockForm

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BlockForm
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVmArm.Layout (infix_of)
open NativeRustcVm (ewsOf wordOf ewOf)
open NativeRustcVm.Transcript (off)

public section

/-- The frame's saved registers. -/
abbrev slots : List (Nat × XReg) :=
  [(0, .X30), (8, .X25), (16, .X24), (24, .X23), (32, .X22), (40, .X21), (48, .X20), (56, .X19)]

/-- The callee-saved registers it does not save. -/
abbrev keep : List XReg := [.X26, .X27, .X28, .X29]

theorem keep_callee : ∀ r ∈ keep, calleeSaved r = true := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 64 := by decide

/-- The form's bytes. -/
abbrev outs (m0 : MachineData) : BitVec 64 → Prop := InRange m0.regs.X5.toBitVec formBufBytes

/-- The tuple's span. -/
def tsp (m0 : MachineData) : NativeRustcVm.Data.Span :=
  (NativeRustcVm.Data.tuples[m0.regs.X0.toNat]?).getD ⟨0, 0⟩

/-- The block form after `j` slots. -/
abbrev g (m0 : MachineData) (j : Nat) : FormW :=
  bf (tsp m0).start (slice m0 m0.regs.X1 m0.regs.X2) (ewArg m0.regs.X3 m0.regs.X4) j

theorem tsp_eq {m0 : MachineData} (h : m0.regs.X0.toNat < NativeRustcVm.Data.tuples.length) :
    tsp m0 = NativeRustcVm.Data.tuples[m0.regs.X0.toNat] := by
  simp [tsp, List.getElem?_eq_getElem h]

theorem tsp_end {m0 : MachineData} (h : m0.regs.X0.toNat < NativeRustcVm.Data.tuples.length) :
    (tsp m0).start + (tsp m0).len ≤ 593 := by
  rw [tsp_eq h]; exact tuple_end_le _ h

theorem stack_le : 64 + formTermsStack ≤ blockFormStack ∧
    64 + formBufAddScaledStack ≤ blockFormStack := by decide

/-- **The loop head** `.LBlockForm_5`, `j` slots added. -/
structure Inv (m0 : MachineData) (j : Nat) (st : MachineData) : Prop where
  fr : Fr m0 64 blockFormStack slots keep (outs m0) st
  le : j ≤ (tsp m0).len
  x19 : st.regs.getXReg .X19 = m0.regs.X5
  x20 : st.regs.getXReg .X20 = m0.regs.X2
  x22 : (st.regs.getXReg .X22).toNat = (tsp m0).start + (tsp m0).len
  x24 : (st.regs.getXReg .X24).toNat = (tsp m0).len
  x23 : (st.regs.getXReg .X23).toNat = j
  x8 : (st.regs.getXReg .X8).toNat = (tsp m0).start + j
  x25 : (st.regs.getXReg .X25).toBitVec = m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * j + 8)
  form : FormBufAt st.dmem m0.regs.X5.toBitVec (g m0 j)

variable [Host] {k : Nat}

theorem lbl_2 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.BlockForm.label_2 = Host.addrOf (k + NativeRustcVmArm.Vm.BlockForm.b2Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.BlockForm.b2Offset) NativeRustcVmArm.Vm.BlockForm.label_2_at
theorem lbl_3 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.BlockForm.label_3 = Host.addrOf (k + NativeRustcVmArm.Vm.BlockForm.b3Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.BlockForm.b3Offset) NativeRustcVmArm.Vm.BlockForm.label_3_at
theorem lbl_4 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.BlockForm.label_4 = Host.addrOf (k + NativeRustcVmArm.Vm.BlockForm.b4Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.BlockForm.b4Offset) NativeRustcVmArm.Vm.BlockForm.label_4_at
theorem lbl_5 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.BlockForm.label_5 = Host.addrOf (k + NativeRustcVmArm.Vm.BlockForm.b6Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.BlockForm.b6Offset) NativeRustcVmArm.Vm.BlockForm.label_5_at
theorem lbl_8 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.BlockForm.label_8 = Host.addrOf (k + NativeRustcVmArm.Vm.BlockForm.b10Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.BlockForm.b10Offset) NativeRustcVmArm.Vm.BlockForm.label_8_at

/-- `block_form`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ BlockFormPost m0 st.data

/-- The form's bytes are not the read-only data's. -/
theorem outs_rodata {m0 : MachineData} (hpre : BlockFormPre m0) :
    ∀ t : NativeRustcVm.Data.Item, ∀ i < t.bytes.length,
      ¬outs m0 (NativeRustcVmArm.rodataAddr t + BitVec.ofNat 64 i) :=
  fun t i hi ↦ rodataApart_out hpre.2.2.2.2.2.1 hpre.2.1 hpre.2.2.2.2.1.1.2 t i hi

/-- **The epilogue** `b10`: X0 `1` where the loop ran to the end. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hpre : BlockFormPre m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BlockForm.b10Offset))
    (hfr : Fr m0 64 blockFormStack slots keep (outs m0) st.data)
    (hres : if (g m0 (tsp m0).len).size ≤ formCap then
        (st.data.regs.getXReg .X22).toNat ≤ (st.data.regs.getXReg .X21).toNat ∧
          FormBufAt st.data.dmem m0.regs.X5.toBitVec (g m0 (tsp m0).len)
      else (st.data.regs.getXReg .X21).toNat < (st.data.regs.getXReg .X22).toNat) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hS := hpre.1
  have hF : 64 ≤ blockFormStack := by decide
  have hwf := Bus.wf_frame (F := 64) hS hF hfr.kept
  have hm := Bus.match_frame (m := st.data) hS hF rfl hfr.sp
  refine exec_at (infix_of b10_in_code (by simp [b10]) hp) run_b10 hwf hpc hm
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hret, hsaved⟩ := hfr.exit hm' hwf (by decide)
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf rfl
  have h0 := hm'.regs .X0 _ rfl
  sym_simp at h0
  simp only [Env.ofMachine_regs, ite_bool, ult_toNat, UInt64.toNat_toBitVec] at h0
  refine .done _ ⟨by simp only [PcOk] at hpc'; rw [hpc', hret], ?_, ?_, hsaved⟩
  · rw [blockForm_eq_bf _ hpre.2.2.1, ← tsp_eq hpre.2.2.1]
    split at hres
    · rename_i hle
      rw [ite_eq_left_of_eq_true _ _ (eq_true hle)]
      refine ⟨?_, by rw [hd]; exact hres.2⟩
      apply UInt64.toBitVec_inj.mp
      rw [show st'.data.regs.X0 = st'.data.regs.getXReg .X0 from rfl, h0,
        decide_eq_false (by omega)]
      rfl
    · rename_i hle
      rw [ite_eq_right_of_eq_false _ _ (eq_false hle)]
      apply UInt64.toBitVec_inj.mp
      rw [show st'.data.regs.X0 = st'.data.regs.getXReg .X0 from rfl, h0,
        decide_eq_true (by omega)]
      rfl
  · intro p hp'
    rw [hd]
    exact Bus.Fr.changes hfr (fun _ h ↦ h) p hp'

/-- The registers a turn keeps from `b6` on. -/
abbrev L' : List XReg := [.X19, .X20, .X21, .X22, .X23, .X24, .X25]

/-- The form is apart from the frame. -/
theorem outs_frame {m0 : MachineData} (hpre : BlockFormPre m0) :
    ∀ q, outs m0 q → ¬InRange (base m0 64) 64 q := by
  intro q hq hq'
  change InRange m0.regs.X5.toBitVec formBufBytes q at hq
  have hN : blockFormStack ≤ m0.regs.SP.toNat := hpre.1.2.1
  have hF : 64 ≤ blockFormStack := by decide
  have hA := apart_frame hN hF hpre.2.2.2.2.1.2
  rw [Sym.inRange_iff hpre.2.2.2.2.1.1.2] at hq
  rw [Sym.inRange_iff (Bus.frame_mapped hpre.1 hF).2] at hq'
  unfold Apart at hA
  omega

/-- **A turn of the loop**: slot `j`'s form added, back at the head; or out of the loop (the
span's end, or a form outgrowing its `FormBuf`) and returned. -/
theorem step (hp : Placed code k)
    (hft : Spec (Labels.label NativeRustcVmArm.Vm.FormTerms.entryLabel) FormTermsPre FormTermsPost)
    (hadd : ∀ f o, Spec (Labels.label NativeRustcVmArm.Vm.FormBufAddScaled.entryLabel) (FormBufAddScaledPre f o)
      (FormBufAddScaledPost f o))
    {m0 : MachineData} (hpre : BlockFormPre m0) {j : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BlockForm.b6Offset)) (hI : Inv m0 j st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BlockForm.b6Offset) ∧ Inv m0 (j + 1) st'.data ∧ j < (tsp m0).len)) st := by
  have hpre' := hpre
  obtain ⟨hS, hR, htu, hW, hFo, hFA, hFW⟩ := hpre
  have hN : blockFormStack ≤ m0.regs.SP.toNat := hS.2.1
  obtain ⟨hle1, hle2⟩ := stack_le
  have hend := tsp_end htu
  have hjl := hI.le
  -- `b6`: `x21 = x8`; out at the span's end.
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 (Env.wf_nil _) hpc (match_nil _)
    fun st1 hm1 hpc1 ↦ ?_
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq (Env.wf_nil _) rfl
  have hfr1 := Fr.ofBlock hI.fr (match_nil _) hm1 (Env.wf_nil _) rfl rfl rfl
    (ofBlock_keep (by decide))
  have K1 : Bus.KeepRegs [.X19, .X20, .X22, .X23, .X24, .X25, .X8] st.data st1.data :=
    Bus.KeepRegs.of_block hm1 rfl
  have e1x21 : st1.data.regs.getXReg .X21 = st.data.regs.getXReg .X8 := mov_reg hm1 rfl
  obtain ⟨hpcT, hpcF⟩ := pc_of_cond hpc1
  by_cases hc : (tsp m0).len = j
  · -- The span's end: return `1`.
    have hpc1 := hpcT (by
      sym_simp
      simp only [Env.ofMachine_regs, beq_toNat, UInt64.toNat_toBitVec, hI.x24, hI.x23]
      simp [hc])
    rw [lbl_8 hp] at hpc1
    refine Eventually.mono (finish hp hpre' hpc1 hfr1 ?_) fun _ h ↦ Or.inl h
    have hform : FormBufAt st1.data.dmem m0.regs.X5.toBitVec (g m0 (tsp m0).len) := by
      rw [hd1, hc]; exact hI.form
    rw [ite_eq_left_of_eq_true _ _ (eq_true hform.len_le)]
    refine ⟨?_, hform⟩
    rw [(K1 .X22 (by simp)), e1x21, hI.x22, hI.x8, hc]
  · -- Not the end: `form_terms` of the span's next form.
    have hpc1 := hpcF (by
      sym_simp
      simp only [Env.ofMachine_regs, beq_toNat, UInt64.toNat_toBitVec, hI.x24, hI.x23]
      simp [hc])
    have hjl' : j < (tsp m0).len := by omega
    refine exec_at (infix_of b7_in_code (by simp [b7]) hp) run_b7 (Env.wf_nil _) hpc1
      (match_nil _) fun st2 hm2 hpc2 ↦ ?_
    have hd2 : st2.data.dmem = st.data.dmem := (hm2.dmem_eq (Env.wf_nil _) rfl).trans hd1
    have hfr2 := Fr.ofBlock hfr1 (match_nil _) hm2 (Env.wf_nil _) rfl rfl rfl
      (ofBlock_keep (by decide))
    have K2 : Bus.KeepRegs L' st1.data st2.data := Bus.KeepRegs.of_block hm2 rfl
    have e2x0 : st2.data.regs.getXReg .X0 = st1.data.regs.getXReg .X21 := mov_reg hm2 rfl
    have hx0 : st2.data.regs.X0.toNat = (tsp m0).start + j := by
      show (st2.data.regs.getXReg .X0).toNat = _
      rw [e2x0, e1x21, hI.x8]
    refine Fr.leaf hfr2 hN hle1 keep_callee slots_le (outs_frame hpre') hft
      (fun _ _ h ↦ ⟨NativeRustcVm.SameOutside.mono h.2.2.2.1 fun _ h ↦ h.elim, h.2.2.2.2⟩) hpc2
      (Bus.Fr.rodataAt hfr2 hR hN hle1 (outs_rodata hpre')) fun m3 hfr3 hq3 hcs3 ↦ ?_
    obtain ⟨hq3n, hq3t, hq3i, hq3s, -⟩ := hq3
    rw [hx0] at hq3n hq3t hq3i
    have hd3 : m3.dmem = st.data.dmem := (dmem_eq_of_same hq3s).trans hd2
    have K3 : Bus.KeepRegs L' st1.data m3 := K2.trans (Bus.KeepRegs.of_call hcs3 rfl)
    -- `b8`: the terms' address and count; the slot's weight or `0`.
    refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8 (Env.wf_nil _) rfl
      (match_nil _) fun st4 hm4 hpc4 ↦ ?_
    have hd4 : st4.data.dmem = st.data.dmem := (hm4.dmem_eq (Env.wf_nil _) rfl).trans hd3
    have hfr4 := Fr.ofBlock hfr3 (match_nil _) hm4 (Env.wf_nil _) rfl rfl rfl
      (ofBlock_keep (by decide))
    have K4 : Bus.KeepRegs L' st1.data st4.data := K3.trans (Bus.KeepRegs.of_block hm4 rfl)
    have e4x2 : st4.data.regs.getXReg .X2 = m3.regs.getXReg .X0 := mov_reg hm4 rfl
    have e4x5 : st4.data.regs.getXReg .X5 = m3.regs.getXReg .X1 := mov_reg hm4 rfl
    -- From `.LBlockForm_4` on: `add_scaled`, then `b5`.
    have tail : ∀ st5 : MachineState, st5.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BlockForm.b4Offset) →
        Fr m0 64 blockFormStack slots keep (outs m0) st5.data → st5.data.dmem = st.data.dmem →
        Bus.KeepRegs (.X2 :: .X5 :: L') st4.data st5.data →
        ewArg (st5.data.regs.getXReg .X3) (st5.data.regs.getXReg .X4) =
          (slice m0 m0.regs.X1 m0.regs.X2).getD j 0 →
        Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
          (st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BlockForm.b6Offset) ∧ Inv m0 (j + 1) st'.data ∧ j < (tsp m0).len)) st5 := by
      intro st5 hpc5 hfr5 hd5 K5 hw5
      refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 (Env.wf_nil _) hpc5
        (match_nil _) fun st6 hm6 hpc6 ↦ ?_
      have hd6 : st6.data.dmem = st.data.dmem := (hm6.dmem_eq (Env.wf_nil _) rfl).trans hd5
      have hfr6 := Fr.ofBlock hfr5 (match_nil _) hm6 (Env.wf_nil _) rfl rfl rfl
        (ofBlock_keep (by decide))
      have K6 : Bus.KeepRegs (.X3 :: .X4 :: L') st5.data st6.data := Bus.KeepRegs.of_block hm6 rfl
      have e6x0 : st6.data.regs.X0 = m0.regs.X5 := by
        show st6.data.regs.getXReg .X0 = _
        rw [mov_reg hm6 (r' := .X19) rfl, (K5 .X19 (by simp)), (K4 .X19 (by simp)),
          (K1 .X19 (by simp)), hI.x19]
      have e6x1 : st6.data.regs.X1 = m3.regs.X0 := by
        show st6.data.regs.getXReg .X1 = _
        rw [mov_reg hm6 (r' := .X2) rfl, (K5 .X2 (by simp)), e4x2]; rfl
      have e6x2 : st6.data.regs.X2 = m3.regs.X1 := by
        show st6.data.regs.getXReg .X2 = _
        rw [mov_reg hm6 (r' := .X5) rfl, (K5 .X5 (by simp)), e4x5]; rfl
      have hw6 : ewArg st6.data.regs.X3 st6.data.regs.X4 =
          (slice m0 m0.regs.X1 m0.regs.X2).getD j 0 := by
        rw [← hw5]
        show ewArg (st6.data.regs.getXReg .X3) (st6.data.regs.getXReg .X4) = _
        rw [(K6 .X3 (by simp)), (K6 .X4 (by simp))]
      have hpos : 0 < (formAt ((tsp m0).start + j)).size := size_formAt_pos (by omega)
      obtain ⟨kk, hkk, hka⟩ : ∃ kk, kk + (formAt ((tsp m0).start + j)).size ≤
          NativeRustcVm.Data.terms.length ∧ m3.regs.X0.toBitVec =
            NativeRustcVmArm.rodataAddr .terms + BitVec.ofNat 64 (termBytes * kk) := by
        rcases hq3i with h | h
        · omega
        · exact h
      have hR6 : RodataAt st6.data formBufAddScaledStack :=
        Bus.Fr.rodataAt hfr6 hR hN hle2 (outs_rodata hpre')
      obtain ⟨hTr, hTo, hTa⟩ := terms_ok hR6 hpos hkk hka hFA
      have hpre6 : FormBufAddScaledPre (g m0 j) (formAt ((tsp m0).start + j)) st6.data ∧
          st6.data.regs.X0 = m0.regs.X5 := by
        refine ⟨⟨hfr6.stackOk hS rfl hle2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, e6x0⟩
        · rw [e6x2]; exact hq3n
        · rw [e6x0, hd6]; exact hI.form
        · rw [e6x1, hd6, ← hd3]; exact hq3t
        · rw [e6x0]; exact Bus.Fr.readable hfr6 hFo.1
        · rw [e6x0]; exact Bus.Fr.offStack hfr6 hS hFo.2 hle2
        · rw [e6x1, e6x2, hq3n]; exact hTr
        · rw [e6x1, e6x2, hq3n]; exact hTo
        · rw [e6x0, e6x1, e6x2, hq3n]; exact hTa
      refine Fr.leaf hfr6 hN hle2 keep_callee slots_le (outs_frame hpre')
        (Bus.Spec.withFact (hadd (g m0 j) (formAt ((tsp m0).start + j)))
          fun m ↦ m.regs.X0 = m0.regs.X5)
        (fun m m' h ↦ ⟨NativeRustcVm.SameOutside.mono h.1.2.1 fun q hq ↦ hq.elim
          (fun h' ↦ .inr (by show InRange m0.regs.X5.toBitVec formBufBytes q; rw [← h.2]; exact h'))
          .inl, h.1.2.2⟩) hpc6 hpre6 fun m7 hfr7 hq7 hcs7 ↦ ?_
      obtain ⟨⟨hres7, -, -⟩, -⟩ := hq7
      have hg : (g m0 j).addScaled (formAt ((tsp m0).start + j))
          (ewArg st6.data.regs.X3 st6.data.regs.X4) = g m0 (j + 1) := by
        rw [hw6]; exact (bf_succ _ _ _ _).symm
      rw [hg, e6x0] at hres7
      have K7 : Bus.KeepRegs L' st1.data m7 :=
        ((K4.trans fun r hr ↦ K5 r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))).trans
          fun r hr ↦ K6 r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))).trans
          (Bus.KeepRegs.of_call hcs7 rfl)
      -- `b5`: the next slot; out where `add_scaled` failed.
      refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 (Env.wf_nil _) rfl
        (match_nil _) fun st8 hm8 hpc8 ↦ ?_
      have hd8 : st8.data.dmem = m7.dmem := hm8.dmem_eq (Env.wf_nil _) rfl
      have hfr8 := Fr.ofBlock hfr7 (match_nil _) hm8 (Env.wf_nil _) rfl rfl rfl
        (ofBlock_keep (by decide))
      have K8 : Bus.KeepRegs [.X19, .X20, .X21, .X22, .X24] m7 st8.data :=
        Bus.KeepRegs.of_block hm8 rfl
      have h8 := hm8.regs .X8 _ rfl
      have h23 := hm8.regs .X23 _ rfl
      have h25 := hm8.regs .X25 _ rfl
      sym_simp at h8 h23 h25
      simp only [Env.ofMachine_regs, (K7 .X21 (by simp)), (K7 .X23 (by simp)), (K7 .X25 (by simp)),
        e1x21, (K1 .X23 (by simp)), (K1 .X25 (by simp))] at h8 h23 h25
      have hx21 : (st8.data.regs.getXReg .X21).toNat = (tsp m0).start + j := by
        rw [(K8 .X21 (by simp)), (K7 .X21 (by simp)), e1x21, hI.x8]
      have hx22 : (st8.data.regs.getXReg .X22).toNat = (tsp m0).start + (tsp m0).len := by
        rw [(K8 .X22 (by simp)), (K7 .X22 (by simp)), (K1 .X22 (by simp)), hI.x22]
      obtain ⟨hpcT8, hpcF8⟩ := pc_of_cond hpc8
      by_cases hfit : (g m0 (j + 1)).size ≤ formCap
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hfit)] at hres7
        obtain ⟨hx0, hform⟩ := hres7
        have hpc8 := hpcF8 (by
          sym_simp
          simp only [Env.ofMachine_regs]
          rw [show m7.regs.getXReg .X0 = 1 from hx0]
          decide)
        · refine .done _ (Or.inr ⟨hpc8, ⟨hfr8, hjl', ?_, ?_, hx22, ?_, ?_, ?_, ?_, hd8 ▸ hform⟩,
            hjl'⟩)
          · rw [(K8 .X19 (by simp)), (K7 .X19 (by simp)), (K1 .X19 (by simp)), hI.x19]
          · rw [(K8 .X20 (by simp)), (K7 .X20 (by simp)), (K1 .X20 (by simp)), hI.x20]
          · rw [(K8 .X24 (by simp)), (K7 .X24 (by simp)), (K1 .X24 (by simp)), hI.x24]
          · have := congrArg BitVec.toNat h23
            simp only [BitVec.toNat_add, UInt64.toNat_toBitVec, hI.x23, BitVec.toNat_ofNat] at this
            omega
          · have := congrArg BitVec.toNat h8
            simp only [BitVec.toNat_add, UInt64.toNat_toBitVec, hI.x8, BitVec.toNat_ofNat] at this
            omega
          · rw [h25, hI.x25, NativeRustcVm.addr_add_add, show 16 * j + 8 + 16 = 16 * (j + 1) + 8 by
              omega]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hfit)] at hres7
        have hpc8 := hpcT8 (by
          sym_simp
          simp only [Env.ofMachine_regs]
          rw [show m7.regs.getXReg .X0 = 0 from hres7]
          decide)
        rw [lbl_8 hp] at hpc8
        refine Eventually.mono (finish hp hpre' hpc8 hfr8 ?_) fun _ h ↦ Or.inl h
        rw [ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hfit ((size_le_bf _ _ _ hjl').trans h)), hx21,
          hx22]
        omega
    obtain ⟨hpcT4, hpcF4⟩ := pc_of_cond hpc4
    by_cases hc' : j < m0.regs.X2.toNat
    · -- `b3`: the slot's weight.
      have hpc4 := hpcT4 (by
        sym_simp
        simp only [Env.ofMachine_regs, ult_toNat, UInt64.toNat_toBitVec, (K3 .X23 (by simp)),
          (K3 .X20 (by simp)), (K1 .X23 (by simp)), (K1 .X20 (by simp)), hI.x23, hI.x20]
        simp [hc'])
      have hmap5 : NativeRustcVm.Mapped st4.data.dmem
          (m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * j)) 16 := fun i hi ↦ by
        rw [NativeRustcVm.addr_add_add]; exact hfr4.kept _ (hW.1.1 _ (by omega))
      have hnw5 : NoWrap (m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * j)) 16 := by
        have := hW.1.2
        unfold NoWrap at *
        rw [NativeRustcVm.toNat_add_ofNat (by omega)]
        omega
      have hwf5 : (Env.ofMachine st4.data
          [(m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * j), 16)]).WF :=
        Env.wf_of ⟨⟨hmap5, hnw5⟩, trivial⟩ (List.pairwise_singleton _ _)
      have hm5 : Match (Env.ofMachine st4.data
          [(m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * j), 16)]) s3 st4.data :=
        match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
          ⟨by
            simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
              Option.getD_some]
            rw [(K4 .X25 (by simp)), (K1 .X25 (by simp)), hI.x25,
              show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add],
           trivial⟩ trivial trivial trivial
      refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf5
        (hpc4.trans (lbl_3 hp)) hm5 fun st5 hm5' hpc5 ↦ ?_
      refine tail st5 hpc5 (Fr.ofBlock hfr4 hm5 hm5' hwf5 rfl rfl rfl (ofBlock_keep (by decide)))
        ((hm5'.dmem_eq hwf5 rfl).trans hd4) (KeepRegs.of_block' hm5 hm5' rfl) ?_
      have h3 := hm5'.regs .X3 _ rfl
      have h4 := hm5'.regs .X4 _ rfl
      simp only [Sym.eval] at h3 h4
      rw [load_eq_wordOf] at h3 h4
      have hws : NativeRustcVm.ewsOf st4.data.dmem m0.regs.X1.toBitVec m0.regs.X2.toNat =
          NativeRustcVm.ewsOf m0.dmem m0.regs.X1.toBitVec m0.regs.X2.toNat :=
        Bus.Fr.ewsOf_eq hfr4 hS hW.1.2 hW.2 fun i hi ↦
          NativeRustcVm.Apart.not_inRange_add (NativeRustcVm.Apart.symm hFW) hW.1.2 hFo.1.2 hi
      have hget : (slice m0 m0.regs.X1 m0.regs.X2).getD j 0 =
          NativeRustcVm.ewOf st4.data.dmem (m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * j)) := by
        unfold slice
        rw [← hws, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
          List.getElem?_eq_getElem (by simpa using hc'), Option.getD_some,
          NativeRustcVm.getElem_ewsOf]
      rw [hget]
      show (⟨st5.data.regs.getXReg .X3, st5.data.regs.getXReg .X4⟩ : EW) = _
      rw [UInt64.toBitVec_inj.mp h3, UInt64.toBitVec_inj.mp h4]
      simp only [NativeRustcVm.ewOf, Env.ofMachine_mem0, Env.base_ofMachine_eq,
        List.getElem?_cons_zero, Option.map_some, Option.getD_some, add_zero']

    · -- `b9`: no weight, `0`.
      have hpc4 := hpcF4 (by
        sym_simp
        simp only [Env.ofMachine_regs, ult_toNat, UInt64.toNat_toBitVec, (K3 .X23 (by simp)),
          (K3 .X20 (by simp)), (K1 .X23 (by simp)), (K1 .X20 (by simp)), hI.x23, hI.x20]
        simp [hc'])
      refine exec_at (infix_of b9_in_code (by simp [b9]) hp) run_b9 (Env.wf_nil _) hpc4
        (match_nil _) fun st5 hm5 hpc5 ↦ ?_
      simp only [PcOk] at hpc5
      refine tail st5 (hpc5.trans (lbl_4 hp))
        (Fr.ofBlock hfr4 (match_nil _) hm5 (Env.wf_nil _) rfl rfl rfl (ofBlock_keep (by decide)))
        ((hm5.dmem_eq (Env.wf_nil _) rfl).trans hd4) (Bus.KeepRegs.of_block hm5 rfl) ?_
      have h3 := hm5.regs .X3 _ rfl
      have h4 := hm5.regs .X4 _ rfl
      simp only [Sym.eval] at h3 h4
      rw [UInt64.toBitVec_inj.mp h3, UInt64.toBitVec_inj.mp h4]
      simp only [slice, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
        List.getElem?_eq_none (show (NativeRustcVm.ewsOf m0.dmem m0.regs.X1.toBitVec
          m0.regs.X2.toNat).length ≤ j by simpa using hc'), Option.getD_none]
      rfl

/-- **`block_form` meets its contract.** -/
theorem blockForm_spec (hp : Placed code k)
    (hft : Spec (Labels.label NativeRustcVmArm.Vm.FormTerms.entryLabel) FormTermsPre FormTermsPost)
    (hadd : ∀ f o, Spec (Labels.label NativeRustcVmArm.Vm.FormBufAddScaled.entryLabel) (FormBufAddScaledPre f o)
      (FormBufAddScaledPost f o)) :
    Spec (Labels.label NativeRustcVmArm.Vm.BlockForm.entryLabel) BlockFormPre BlockFormPost := by
  intro m0 hpre
  have hpre' := hpre
  obtain ⟨hS, hR, htu, hW, hFo, hFA, hFW⟩ := hpre
  have hN : blockFormStack ≤ m0.regs.SP.toNat := hS.2.1
  have hF : 64 ≤ blockFormStack := by decide
  have htu' : m0.regs.X0.toNat < 147 := tuples_length ▸ htu
  have hend := tsp_end htu
  -- `b0`: the prologue; the form the constant `side_beta`.
  have hwf0 : (Env.ofMachine m0 [(base m0 64, 64), (m0.regs.X5.toBitVec, formBufBytes)]).WF :=
    Bus.wf_frame2 hS hF (fun _ h ↦ h) hFo.1 hFo.2
  have hm0 : Match (Env.ofMachine m0 [(base m0 64, 64), (m0.regs.X5.toBitVec, formBufBytes)])
      s0 m0 :=
    match_ofMachine (sregions := [(64, true), (5928, false)])
      (regions := [(base m0 64, 64), (m0.regs.X5.toBitVec, formBufBytes)])
      ⟨rfl, fun _ ↦ Bus.base_aligned hS hF rfl, rfl, nofun, trivial⟩
      (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
            Option.getD_some]
          rw [show BitVec.ofInt 64 64 = BitVec.ofNat 64 64 from rfl]; exact base_add_eq.symm)
      ⟨by simp [Sym.eval]; rfl, trivial⟩ trivial trivial trivial
  rw [show Labels.label NativeRustcVmArm.Vm.BlockForm.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.BlockForm.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.BlockForm.entryOffset) NativeRustcVmArm.Vm.BlockForm.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 hm0 fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : Fr m0 64 blockFormStack slots keep (outs m0) st1.data :=
    Fr.ofPrologueW hN hF hm1 hwf0 rfl (by decide) slots_le
      (fun w hw ↦ writeOk_two hFo.1.2 (by revert w; decide)) (by decide)
  have K1 : Bus.KeepRegs [.X0, .X1, .X2, .X3, .X4] m0 st1.data := Bus.KeepRegs.of_block hm1 rfl
  have e1x19 : st1.data.regs.getXReg .X19 = m0.regs.X5 := by
    have := hm1.regs .X19 _ rfl
    simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.map_some, Option.getD_some, BitVec.ofInt_ofNat, BitVec.add_zero] at this
    exact UInt64.toBitVec_inj.mp this
  have e1x20 : st1.data.regs.getXReg .X20 = m0.regs.getXReg .X2 := mov_reg hm1 rfl
  have hW1 : ∀ (o : Nat) (v : Sym), o + 8 ≤ formBufBytes →
      (∀ i < 8, findWrite 1 (o + i) (after b0 s0).mem = some (v, i)) →
      NativeRustcVm.WordAt st1.data.dmem (m0.regs.X5.toBitVec + BitVec.ofNat 64 o)
        (UInt64.ofBitVec (v.eval (Env.ofMachine m0 [(base m0 64, 64),
          (m0.regs.X5.toBitVec, formBufBytes)]))) := fun o v ho hw ↦
    Bus.wordAt_write hm1 (r := 1) (o := o) rfl ho (by rw [← Bus.after_eq run_b0]; exact hw)
  have hform1 : FormBufAt st1.data.dmem m0.regs.X5.toBitVec (g m0 0) := by
    refine ⟨show 1 ≤ 148 by decide, ?_, fun i hi ↦ ?_⟩
    · have h := hW1 0 (.lit 1) (by decide) (by decide)
      rw [add_zero'] at h
      exact h
    · have hi0 : i = 0 := by simpa [g, bf_zero, FormW.const] using hi
      subst hi0
      refine ⟨by simp [g, bf_zero, FormW.const], ?_, nofun, nofun, ?_⟩
      · have h := hW1 8 (.lit 0) (by decide) (by decide)
        simp only [off, NativeRustcVm.addr_add_add, Nat.mul_zero, Nat.add_zero]
        exact h
      · rw [NativeRustcVm.ewAt_iff]
        have h3 := hW1 32 (.reg .X3) (by decide) (by decide)
        have h4 := hW1 40 (.reg .X4) (by decide) (by decide)
        simp only [off, NativeRustcVm.addr_add_add, Nat.mul_zero, Nat.add_zero, Nat.reduceAdd]
        exact ⟨h3, h4⟩
  have hpc1 := (pc_of_cond hpc1).2 (by
    sym_simp
    simp only [Env.ofMachine_regs, ult_toNat, beq_toNat, UInt64.toNat_toBitVec, BitVec.toNat_ofNat,
      Bool.and_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq]
    have : (m0.regs.getXReg .X0).toNat = m0.regs.X0.toNat := rfl
    omega)
  -- `b1`: the tuple's span from `TUPLES`.
  have hR1 : RodataAt st1.data 0 := Bus.Fr.rodataAt hfr1 hR hN (by omega) (outs_rodata hpre')
  have hT := hR1.bytesAt .tuples
  have hTn := hR1.noWrap .tuples
  change NativeRustcVm.BytesAt st1.data.dmem (NativeRustcVmArm.rodataAddr .tuples)
    (NativeRustcVm.Data.tuples.flatMap NativeRustcVm.Data.Span.bytes) at hT
  change NoWrap _ (NativeRustcVm.Data.tuples.flatMap NativeRustcVm.Data.Span.bytes).length at hTn
  rw [length_tuples_bytes] at hTn
  have hTm := hT.mapped
  rw [length_tuples_bytes] at hTm
  have hwf1 : (Env.ofMachine st1.data [(NativeRustcVmArm.rodataAddr .tuples, 2352)]).WF :=
    Env.wf_of ⟨⟨hTm, hTn⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm1' : Match (Env.ofMachine st1.data [(NativeRustcVmArm.rodataAddr .tuples, 2352)]) s1
      st1.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial ⟨rfl, trivial⟩
      ⟨by show (st1.data.regs.getXReg .X0).toBitVec.toNat < 147; rw [(K1 .X0 (by simp))]; exact htu',
       trivial⟩ trivial
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf1 hpc1 hm1'
    fun st2 hm2 hpc2 ↦ ?_
  have hfr2 := Fr.ofBlock hfr1 hm1' hm2 hwf1 rfl rfl rfl (ofBlock_keep (by decide))
  have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq hwf1 rfl
  have K2 : Bus.KeepRegs [.X1, .X2, .X19, .X20] st1.data st2.data := Bus.KeepRegs.of_block hm2 rfl
  obtain ⟨hws, hwl⟩ := tuples_words hT _ htu
  have hidx : ((m0.regs.getXReg .X0).toBitVec <<< 4).toNat = 16 * m0.regs.X0.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    show m0.regs.X0.toNat * 2 ^ 4 % 2 ^ 64 = _
    omega
  have hls : (Env.ofMachine st1.data [(NativeRustcVmArm.rodataAddr .tuples, 2352)]).load 0
      (0 + ((m0.regs.getXReg .X0).toBitVec <<< 4).toNat) 8 =
      BitVec.ofNat 64 (tsp m0).start := by
    rw [hidx, Nat.zero_add, tsp_eq htu]; exact load_word hws
  have hll : (Env.ofMachine st1.data [(NativeRustcVmArm.rodataAddr .tuples, 2352)]).load 0
      (8 + ((m0.regs.getXReg .X0).toBitVec <<< 4).toNat) 8 =
      BitVec.ofNat 64 (tsp m0).len := by
    rw [hidx, Nat.add_comm, tsp_eq htu]
    refine load_word ?_
    rw [← NativeRustcVm.addr_add_add]; exact hwl
  have h8 := hm2.regs .X8 _ rfl
  have h22 := hm2.regs .X22 _ rfl
  sym_simp at h8 h22
  simp only [Env.ofMachine_regs, (K1 .X0 (by simp))] at h8 h22
  rw [hls] at h8
  rw [hls, hll] at h22
  -- `b2`: the count; to the loop head.
  simp only [PcOk] at hpc2
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 (Env.wf_nil _) hpc2
    (match_nil _) fun st3 hm3 hpc3 ↦ ?_
  have hfr3 := Fr.ofBlock hfr2 (match_nil _) hm3 (Env.wf_nil _) rfl rfl rfl
    (ofBlock_keep (by decide))
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq (Env.wf_nil _) rfl
  have K3 : Bus.KeepRegs [.X8, .X19, .X20, .X22] st2.data st3.data := Bus.KeepRegs.of_block hm3 rfl
  have h23 := hm3.regs .X23 _ rfl
  have h24 := hm3.regs .X24 _ rfl
  have h25 := hm3.regs .X25 _ rfl
  sym_simp at h23 h24 h25
  rw [ite_bool] at h24
  simp only [Env.ofMachine_regs, (K2 .X1 (by simp)), (K1 .X1 (by simp)), ult_toNat,
    UInt64.toNat_toBitVec] at h23 h24 h25
  have hx8 : (st2.data.regs.getXReg .X8).toNat = (tsp m0).start := by
    rw [← UInt64.toNat_toBitVec, h8, BitVec.toNat_ofNat]; omega
  have hx22 : (st2.data.regs.getXReg .X22).toNat = (tsp m0).start + (tsp m0).len := by
    rw [← UInt64.toNat_toBitVec, h22, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  rw [hx8, hx22, decide_eq_false (by omega), Bool.cond_false] at h24
  simp only [PcOk] at hpc3
  have hI0 : Inv m0 0 st3.data := by
    refine ⟨hfr3, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [(K3 .X19 (by simp)), (K2 .X19 (by simp)), e1x19]
    · rw [(K3 .X20 (by simp)), (K2 .X20 (by simp)), e1x20]; rfl
    · rw [(K3 .X22 (by simp)), hx22]
    · rw [← UInt64.toNat_toBitVec, h24, BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def, UInt64.toNat_toBitVec, UInt64.toNat_toBitVec, hx8, hx22]; omega)]
      rw [UInt64.toNat_toBitVec, UInt64.toNat_toBitVec, hx8, hx22]; omega
    · rw [← UInt64.toNat_toBitVec, h23]; rfl
    · rw [(K3 .X8 (by simp)), hx8]; rfl
    · rw [h25]; rfl
    · rw [hd3, hd2]; exact hform1
  refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BlockForm.b6Offset) ∧ ∃ j, (tsp m0).len - j = n ∧
    Inv m0 j st.data) (fun n st ⟨hpc, j, hn, hI⟩ ↦ ?_) ⟨hpc3.trans (lbl_5 hp), 0, rfl, hI0⟩
  refine Eventually.mono (step hp hft hadd hpre' hpc hI) fun st' h ↦ ?_
  rcases h with h | ⟨hpc', hI', hlt⟩
  · exact Or.inl h
  · exact Or.inr ⟨(tsp m0).len - (j + 1), by omega, hpc', j + 1, rfl, hI'⟩

end

end NativeRustcVmArm.Bus.BlockForm
