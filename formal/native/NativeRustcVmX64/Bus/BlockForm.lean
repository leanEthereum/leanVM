module

public import NativeRustcVmX64.Bus.BlockForm.Lemmas
public import NativeRustcVm.Tables.Same
public import NativeRustcVmX64.Code.Vm.BlockForm.Names
public import NativeRustcVmX64.Code.Vm.FormBufAddScaled.Names
public import NativeRustcVmX64.Code.Vm.FormTerms.Names

/-!
# `block_form` on x86-64

`b0` pushes RBP, R15, R14, R13, R12, RBX, keeps the weights' count at offset `24` of its frame and
sets the form at R9 to the constant `side_beta`; the tuple is below `147`, so its branch past
`TUPLES` is never taken; `b1` reads the tuple's span from `TUPLES`; `b3` keeps the span's end at
offset `16`, the count in R14, and goes to the loop head `NativeRustcVmX64.Vm.BlockForm.label_4` (`b8`, `Inv`): the form
at R9 is `bf` of the first `j` slots. A turn (`step`): `form_terms` of the span's next form
(`b9`), its weight from `side_weights` or `0` (`b10`, `b5`/`b11`), `FormBuf::add_scaled` (`b6`);
a failure (the form outgrows its `FormBuf`) leaves the loop, else back to the head (`b7`). The
epilogue `b12` returns AL = `1` where the loop ran to the span's end (`finish`).
-/

namespace NativeRustcVmX64.Bus.BlockForm

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.BlockForm
open NativeRustcVmX64.Transcript NativeRustcVm.Transcript NativeRustcVmX64.Bus
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVm (ewsOf wordOf ewOf)

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 80 := by decide

theorem stack_le : 80 + formTermsStack ≤ blockFormStack ∧
    80 + formBufAddScaledStack ≤ blockFormStack := by decide

theorem hF : 80 ≤ blockFormStack := by decide

/-- The tuple's span. -/
@[expose] def tsp (m0 : MachineData) : NativeRustcVm.Data.Span :=
  (NativeRustcVm.Data.tuples[(reg m0 .rdi).toNat]?).getD ⟨0, 0⟩

/-- The block form after `j` slots. -/
abbrev g (m0 : MachineData) (j : Nat) : FormW :=
  bf (tsp m0).start (slice m0 (reg m0 .rsi) (reg m0 .rdx)) (ewArg (reg m0 .rcx) (reg m0 .r8)) j

/-- The form's output. -/
abbrev fo (m0 : MachineData) : BitVec 64 := reg m0 .r9

theorem tsp_eq {m0 : MachineData} (h : (reg m0 .rdi).toNat < NativeRustcVm.Data.tuples.length) :
    tsp m0 = NativeRustcVm.Data.tuples[(reg m0 .rdi).toNat] := by
  simp [tsp, List.getElem?_eq_getElem h]

theorem tsp_end {m0 : MachineData} (h : (reg m0 .rdi).toNat < NativeRustcVm.Data.tuples.length) :
    (tsp m0).start + (tsp m0).len ≤ 593 := by
  rw [tsp_eq h]; exact tuple_end_le _ h

/-- **The loop head** `NativeRustcVmX64.Vm.BlockForm.label_4`, `j` slots added. -/
structure Inv (m0 : MachineData) (j : Nat) (st : MachineData) : Prop where
  fr : Frame m0 80 slots 8 st
  same : Same m0 blockFormStack (fo m0) formBufBytes st.dmem
  le : j ≤ (tsp m0).len
  rbx : reg st .rbx = fo m0
  rbp : (reg st .rbp).toNat = (tsp m0).start
  r14 : (reg st .r14).toNat = (tsp m0).len
  r13 : (reg st .r13).toNat = j
  r15 : reg st .r15 = reg m0 .rsi + BitVec.ofNat 64 (16 * j + 8)
  words : FrameWords m0 80 st.dmem
    [(16, ((tsp m0).start + (tsp m0).len).toUInt64), (24, UInt64.ofBitVec (reg m0 .rdx))]
  form : FormBufAt st.dmem (fo m0) (g m0 j)

theorem toNat_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toBitVec.toNat = n := by
  rw [UInt64.toNat_toBitVec, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

/-- The frame's words of the loop. -/
abbrev Words (m0 : MachineData) : List (Nat × UInt64) :=
  [(16, ((tsp m0).start + (tsp m0).len).toUInt64), (24, UInt64.ofBitVec (reg m0 .rdx))]

theorem words_ok (m0 : MachineData) : ∀ p ∈ Words m0, p.1 + 8 ≤ 80 + 8 ∧ 8 ≤ p.1 := by simp

theorem words_le (m0 : MachineData) : ∀ p ∈ Words m0, p.1 + 8 ≤ 80 + 8 := by simp

variable [Host] {k : Nat}

/-- `block_form`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ BlockFormPost m0 st.data

/-- A block keeping the frame's words, `Same` and the form. -/
theorem keep_block {m0 st st' : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {rest : List (BitVec 64 × Nat)} {S : SState} (hpre : BlockFormPre m0)
    (hwf : (frameEnv m0 st 80 rest vars ret).WF) (hm : Match (frameEnv m0 st 80 rest vars ret) S st')
    (hS : MidOk 80 8 slots S = true ∨ MidOk 80 0 slots S = true)
    (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 8) {ws : List (Nat × UInt64)}
    (hws : ∀ p ∈ ws, p.1 + 8 ≤ 80 + 8 ∧ 8 ≤ p.1)
    (hW : FrameWords m0 80 st.dmem ws) (hs : Same m0 blockFormStack (fo m0) formBufBytes st.dmem)
    {f : FormW} (hf : FormBufAt st.dmem (fo m0) f) :
    FrameWords m0 80 st'.dmem ws ∧ Same m0 blockFormStack (fo m0) formBufBytes st'.dmem ∧
      FormBufAt st'.dmem (fo m0) f := by
  have hbr : belowRet 80 S = true := by
    rcases hS with h | h <;> exact belowRet_of_mid h
  have hin : writesIn S = true := by
    rcases hS with h | h <;> exact writesIn_of_mid h
  have hst := hpre.1
  refine ⟨FrameWords.block hwf hm hin (fun p hp ↦ (hws p hp).1)
      (fun p hp w hw' _ ↦ .inl (by have := (hw w hw').2; have := (hws p hp).2; omega)) hW,
    Same.block hst hF hs hwf hm (fun w h ↦ (hw w h).1) hbr, ?_⟩
  have hFo := hpre.2.2.2.2.1
  have hnwF := frame_noWrap hst hF
  have hap : NativeRustcVm.Apart (fo m0) formBufBytes (stackBelow m0 80) (80 + 8) :=
    apart_frame hFo.2 hst.1 hF
  have hsame : NativeRustcVm.SameOutside st.dmem st'.dmem
      (NativeRustcVm.InRange (stackBelow m0 80) 80) := fun q hq ↦
    hm.get?_mem0 hwf fun hW' ↦ hq (written_low hwf (fun w h ↦ (hw w h).1) hbr hW')
  exact NativeRustcVm.Tables.FormBufAt.of_same hf (NativeRustcVm.Layout.Same.of_sameOutside hsame
    fun j hj hq ↦ NativeRustcVm.Apart.not_inRange_add hap hFo.1.2 hnwF hj (inRange_le hq (by omega)))

/-- **The epilogue** `b12`: AL `1` where the loop ran to the end. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hpre : BlockFormPre m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BlockForm.b12Offset))
    (hfr : Frame m0 80 slots 8 st.data)
    (hs : Same m0 blockFormStack (fo m0) formBufBytes st.data.dmem)
    (hW : FrameWords m0 80 st.data.dmem (Words m0))
    (hres : if (g m0 (tsp m0).len).size ≤ formCap then
        (reg st.data .r12).toNat = (tsp m0).start + (tsp m0).len ∧
          FormBufAt st.data.dmem (fo m0) (g m0 (tsp m0).len)
      else (reg st.data .r12).toNat < (tsp m0).start + (tsp m0).len) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hst := hpre.1
  have hend := tsp_end hpre.2.2.1
  have hwf := wf0 (d := st.data) hst hF hfr.kept (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b12_in_code (by simp [b12]) hp) run_b12 hwf nofun hpc
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hfr.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hepi, hmem, hrax⟩ := after_eq run_b12 ▸ ok_b12
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hfr hwf hm' hepi
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf hmem
  have hl16 := load_frameWord (rest := []) (vars := fun _ ↦ 0) (ret := 0) hW (o := 16)
    List.mem_cons_self
  have hal : boolRet st'.data =
      if (reg st.data .r12).toNat < (tsp m0).start + (tsp m0).len then 0 else 1 := by
    unfold boolRet
    rw [show reg st'.data .rax = _ from hm'.regs .rax _ hrax]
    simp only [Sym.eval]
    rw [merge8_toNat]
    simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64, Env.ofMachine_regs, hl16]
    rw [ult_of_toNat rfl (toNat_toUInt64 (by omega))]
    by_cases h : (reg st.data .r12).toNat < (tsp m0).start + (tsp m0).len <;> simp [h]
  have hbf : blockForm ⟨0, 0, tupleOf (reg m0 .rdi).toNat, 0⟩ (slice m0 (reg m0 .rsi) (reg m0 .rdx))
      (ewArg (reg m0 .rcx) (reg m0 .r8)) = g m0 (tsp m0).len := by
    rw [blockForm_eq_bf _ hpre.2.2.1, ← tsp_eq hpre.2.2.1]
  simp only [PcOk] at hpc'
  refine .done _ ⟨by rw [hpc']; exact hfr.load_ret hst hF, hrsp, ?_, fun q hq ↦ ?_, hsv⟩
  · rw [hbf, hal]
    split at hres
    · rename_i hle
      have hn : ¬(reg st.data .r12).toNat < (tsp m0).start + (tsp m0).len := by omega
      simp only [hle, hn, ↓reduceIte, hd]
      exact ⟨trivial, hres.2⟩
    · rename_i hle
      simp only [hle, hres, ↓reduceIte]
  · rw [hd]; exact hs q hq

theorem fo_frame {m0 : MachineData} (hpre : BlockFormPre m0) :
    ∀ q, NativeRustcVm.InRange (fo m0) formBufBytes q →
      ¬NativeRustcVm.InRange (stackBelow m0 80) (80 + 8) q := fun _ hq ↦
  not_inRange_of_apart (apart_frame hpre.2.2.2.2.1.2 hpre.1.1 hF) hpre.2.2.2.2.1.1.2
    (frame_noWrap hpre.1 hF) hq

omit [Host] in
theorem zero_range {q : BitVec 64} : ¬NativeRustcVm.InRange 0 0 q := by
  unfold NativeRustcVm.InRange; omega

/-- **A turn of the loop**: slot `j`'s form added, back at the head; or out of the loop (the
span's end, or a form outgrowing its `FormBuf`) and returned. -/
theorem step (hp : Placed code k)
    (hft : Spec (Labels.label NativeRustcVmX64.Vm.FormTerms.entryLabel) FormTermsPre FormTermsPost)
    (hadd : ∀ f o, Spec (Labels.label NativeRustcVmX64.Vm.FormBufAddScaled.entryLabel) (FormBufAddScaledPre f o)
      (FormBufAddScaledPost f o))
    {m0 : MachineData} (hpre : BlockFormPre m0) {j : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BlockForm.b8Offset)) (hI : Inv m0 j st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BlockForm.b8Offset) ∧ Inv m0 (j + 1) st'.data ∧ j < (tsp m0).len)) st := by
  have hpre' := hpre
  obtain ⟨hst, hR, htu, hW, hFo, hFA, hFW⟩ := hpre
  have hend := tsp_end htu
  have hjl := hI.le
  have hnwF := frame_noWrap hst hF
  obtain ⟨hle1, hle2⟩ := stack_le
  -- `b8`: `r12 = start + j`; out at the span's end.
  have hwf0 := wf0 (d := st.data) hst hF hI.fr.kept (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8 hwf0 nofun hpc
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hI.fr.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hmem1, h12_1, hk1⟩ := after_eq run_b8 ▸ ok_b8
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf0 hmem1
  have hfr1 : Frame m0 80 slots 8 st1.data := Frame.of_block hI.fr hwf0 hm1 hmid1 slots_le
  have e1_12 : (reg st1.data .r12).toNat = (tsp m0).start + j := by
    rw [show reg st1.data .r12 = _ from hm1.regs .r12 _ h12_1]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [BitVec.toNat_add, hI.r13, hI.rbp]; omega
  have hc1 : (SBool.cmp .eq .W64 (.reg .r14) (.reg .r13)).eval
      (frameEnv m0 st.data 80 [] (fun _ ↦ 0) 0) = decide ((tsp m0).len = j) := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs]
    exact beq_of_toNat hI.r14 hI.r13
  simp only [PcOk] at hpc1
  rw [hc1] at hpc1
  by_cases hcj : (tsp m0).len = j
  · -- The span's end: return `1`.
    subst hcj
    rw [ite_eq_left_of_eq_true _ _ (by simp), hp.label NativeRustcVmX64.Vm.BlockForm.label_9_at] at hpc1
    refine Eventually.mono (finish hp hpre' hpc1 hfr1 (by rw [hd1]; exact hI.same)
      (by rw [hd1]; exact hI.words) ?_) fun _ h ↦ Or.inl h
    rw [ite_eq_left_of_eq_true _ _ (eq_true hI.form.len_le)]
    exact ⟨e1_12, by rw [hd1]; exact hI.form⟩
  have hjl' : j < (tsp m0).len := by omega
  rw [decide_eq_false hcj] at hpc1
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
  -- `b9`: `form_terms` of the span's next form.
  have hwf1 := wf0 (d := st1.data) hst hF hfr1.kept (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.BlockForm.b9Offset + b9.length)).toBitVec)
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) run_b9 hwf1 (fun _ _ ↦ rfl)
    (hpc1.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BlockForm.b8_next)))
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hfr1.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid2, hw2, hdi2, hk2⟩ := after_eq run_b9 ▸ ok_b9
  have hfr2 : Frame m0 80 slots 0 st2.data := Frame.of_block hfr1 hwf1 hm2 hmid2 slots_le
  obtain ⟨FW2, S2, F2⟩ := keep_block hpre' hwf1 hm2 (.inr hmid2) hw2 (words_ok m0)
    (by rw [hd1]; exact hI.words) (by rw [hd1]; exact hI.same) (by rw [hd1]; exact hI.form)
  have hsp2 : rspOf st2.data = stackBelow m0 80 := by rw [hfr2.sp, off_zero]
  have e2di : (reg st2.data .rdi).toNat = (tsp m0).start + j :=
    (congrArg BitVec.toNat (hm2.regs .rdi _ hdi2)).trans e1_12
  refine call_then hpc2 hft ⟨stackOk_callee hst hfr2.kept hsp2 hle1,
    rodataAt_callee hst hR S2 hFA hFo.1.2 hsp2 hle1⟩
    fun st3 hpc3 hrsp3 ⟨hsz3, hT3, hIT3, hso3, hsv3⟩ ↦ ?_
  rw [e2di] at hsz3 hT3 hIT3
  have hfr3 := Frame.call hfr2 hsv3 hrsp3 hso3 (fun _ h ↦ h.elim) hnwF slots_le
  have hch3 : Changes st2.data st3.data formTermsStack 0 0 :=
    NativeRustcVm.Transcript.SameOutside.mono hso3 fun _ h ↦ h.elim
  have FW3 := FrameWords.call_out hst hfr2 hle1 hch3 (fun _ h ↦ absurd h zero_range)
    (words_le m0) FW2
  have S3 := Same.call hst hsp2 hle1 S2 hch3 fun _ h ↦ absurd h zero_range
  have F3 : FormBufAt st3.data.dmem (fo m0) (g m0 j) :=
    NativeRustcVm.Tables.FormBufAt.of_same F2
      (NativeRustcVm.Layout.Same.of_sameOutside hso3 fun _ _ h ↦ h)
  have hpos : 0 < (formAt ((tsp m0).start + j)).size := size_formAt_pos (by omega)
  obtain ⟨kk, hkk, hka⟩ : ∃ kk, kk + (formAt ((tsp m0).start + j)).size ≤
      NativeRustcVm.Data.terms.length ∧ reg st3.data .rax =
        rodataAddr .terms + BitVec.ofNat 64 (termBytes * kk) := by
    rcases hIT3 with h | h
    · omega
    · exact h
  obtain ⟨hTr, hTo, hTa⟩ := terms_ok hR hpos hkk hka hFA
  -- Callee-saved registers from the head to `form_terms`' return.
  have K3 : ∀ r ∈ [Reg64.rbx, .rbp, .r13, .r14, .r15], reg st3.data r = reg st.data r := by
    intro r hr
    have hcs : calleeSaved r = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl
    exact (hsv3.1 r hcs).trans ((hk2.reg' hm2 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp)).trans (hk1.reg' hm1 hr))
  have e3_12 : (reg st3.data .r12).toNat = (tsp m0).start + j := by
    exact (congrArg BitVec.toNat ((hsv3.1 .r12 rfl).trans (hk2.reg' hm2 (by simp)))).trans e1_12
  -- From `NativeRustcVmX64.Vm.BlockForm.label_8` on: `add_scaled`, then `b7`.
  have tail : ∀ st5 : MachineState, st5.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BlockForm.b6Offset) →
      Frame m0 80 slots 8 st5.data → st5.data.dmem = st3.data.dmem →
      (∀ r ∈ [Reg64.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15],
        reg st5.data r = reg st3.data r) →
      ewArg (reg st5.data .rcx) (reg st5.data .r8) =
        (slice m0 (reg m0 .rsi) (reg m0 .rdx)).getD j 0 →
      Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
        (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BlockForm.b8Offset) ∧ Inv m0 (j + 1) st'.data ∧ j < (tsp m0).len)) st5 := by
    intro st5 hpc5 hfr5 hd5 K5 hw5
    have hwf5 := wf0 (d := st5.data) hst hF hfr5.kept (vars := fun _ ↦ 0)
      (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.BlockForm.b6Offset + b6.length)).toBitVec)
    refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf5 (fun _ _ ↦ rfl) hpc5
      (match_ofMachine ⟨rfl, trivial⟩ ⟨hfr5.rsp_eval, trivial⟩ trivial trivial trivial)
      fun st6 hm6 hpc6 ↦ ?_
    obtain ⟨hmid6, hw6, hdi6, hsi6, hk6⟩ := after_eq run_b6 ▸ ok_b6
    have hfr6 : Frame m0 80 slots 0 st6.data := Frame.of_block hfr5 hwf5 hm6 hmid6 slots_le
    obtain ⟨FW6, S6, F6⟩ := keep_block hpre' hwf5 hm6 (.inr hmid6) hw6 (words_ok m0)
      (by rw [hd5]; exact FW3) (by rw [hd5]; exact S3) (by rw [hd5]; exact F3)
    have hsp6 : rspOf st6.data = stackBelow m0 80 := by rw [hfr6.sp, off_zero]
    have hsame6 : NativeRustcVm.SameOutside st5.data.dmem st6.data.dmem
        (NativeRustcVm.InRange (stackBelow m0 80) 80) := fun q hq ↦
      hm6.get?_mem0 hwf5 fun hW' ↦ hq (written_low hwf5 (fun w h ↦ (hw6 w h).1)
        (belowRet_of_mid hmid6) hW')
    have hTap := apart_frame hTo hst.1 hF
    have T6 : TermsAt st6.data.dmem (reg st3.data .rax) (formAt ((tsp m0).start + j)) :=
      termsAt_keep hsame6 (by rw [hd5]; exact hT3) fun i hi hq ↦
        NativeRustcVm.Apart.not_inRange_add hTap hTr.2 hnwF hi (inRange_le hq (by omega))
    have e6di : reg st6.data .rdi = fo m0 :=
      (hm6.regs .rdi _ hdi6).trans ((K5 .rbx (by simp)).trans ((K3 .rbx (by simp)).trans hI.rbx))
    have e6si : reg st6.data .rsi = reg st3.data .rax :=
      (hm6.regs .rsi _ hsi6).trans (K5 .rax (by simp))
    have e6dx : (reg st6.data .rdx).toNat = (formAt ((tsp m0).start + j)).size := by
      rw [hk6.reg' hm6 (by simp), K5 .rdx (by simp)]; exact hsz3
    have e6w : ewArg (reg st6.data .rcx) (reg st6.data .r8) =
        (slice m0 (reg m0 .rsi) (reg m0 .rdx)).getD j 0 := by
      rw [hk6.reg' hm6 (by simp), hk6.reg' hm6 (by simp)]; exact hw5
    have hpre6 : FormBufAddScaledPre (g m0 j) (formAt ((tsp m0).start + j)) st6.data := by
      simp only [FormBufAddScaledPre]
      rw [e6di, e6si, e6dx]
      exact ⟨stackOk_callee hst hfr6.kept hsp6 hle2, rfl, F6, T6,
        ⟨Mapped.keeps hFo.1.1 hfr6.kept, hFo.1.2⟩, apart_callee hFo.2 hsp6 hst.1 hle2,
        ⟨Mapped.keeps hTr.1 hfr6.kept, hTr.2⟩, apart_callee hTo hsp6 hst.1 hle2, hTa⟩
    refine call_then hpc6 (hadd _ _) hpre6 fun st7 hpc7 hrsp7 ⟨hres7, hch7, hsv7⟩ ↦ ?_
    rw [e6di, e6w] at hres7
    rw [e6di] at hch7
    have hg : (g m0 j).addScaled (formAt ((tsp m0).start + j))
        ((slice m0 (reg m0 .rsi) (reg m0 .rdx)).getD j 0) = g m0 (j + 1) :=
      (bf_succ _ _ _ _).symm
    rw [hg] at hres7
    have hfr7 := Frame.call hfr6 hsv7 hrsp7 hch7
      (fun q h ↦ h.elim (fo_frame hpre' q) fun h ↦ (inRange_callee hsp6 hst.2.1 hst.1 hle2 h).2)
      hnwF slots_le
    have S7 := Same.call hst hsp6 hle2 S6 hch7 fun _ h ↦ h
    have FW7 := FrameWords.call_out hst hfr6 hle2 hch7 (fo_frame hpre') (words_le m0) FW6
    -- `b7`: the next slot; out where `add_scaled` failed.
    have hwf7 := wf0 (d := st7.data) hst hF hfr7.kept (vars := fun _ ↦ 0) (ret := 0)
    refine exec_at (infix_of b7_in_code (by simp [b7]) hp) run_b7 hwf7 nofun
      (hpc7.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BlockForm.b6_next)))
      (match_ofMachine ⟨rfl, trivial⟩ ⟨hfr7.rsp_eval, trivial⟩ trivial trivial trivial)
      fun st8 hm8 hpc8 ↦ ?_
    obtain ⟨hmid8, hmem8, h15_8, h13_8, hk8⟩ := after_eq run_b7 ▸ ok_b7
    have hd8 : st8.data.dmem = st7.data.dmem := hm8.dmem_eq hwf7 hmem8
    have hfr8 : Frame m0 80 slots 8 st8.data := Frame.of_block hfr7 hwf7 hm8 hmid8 slots_le
    have K8 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r14], reg st8.data r = reg st3.data r := by
      intro r hr
      have hcs : calleeSaved r = true := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> rfl
      have hr6 : r ∈ [Reg64.rdx, .rcx, .r8, .rbx, .rbp, .r12, .r13, .r14, .r15] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl <;> simp
      have hr5 : r ∈ [Reg64.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl <;> simp
      exact (hk8.reg' hm8 hr).trans ((hsv7.1 r hcs).trans ((hk6.reg' hm6 hr6).trans (K5 r hr5)))
    have e7_13 : reg st7.data .r13 = reg st.data .r13 :=
      (hsv7.1 .r13 rfl).trans ((hk6.reg' hm6 (by simp)).trans ((K5 .r13 (by simp)).trans
        (K3 .r13 (by simp))))
    have e7_15 : reg st7.data .r15 = reg st.data .r15 :=
      (hsv7.1 .r15 rfl).trans ((hk6.reg' hm6 (by simp)).trans ((K5 .r15 (by simp)).trans
        (K3 .r15 (by simp))))
    have hc8 : (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)).eval
        (frameEnv m0 st7.data 80 [] (fun _ ↦ 0) 0) = decide (boolRet st7.data = 0) := by
      simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
      exact test_al _
    simp only [PcOk] at hpc8
    rw [hc8] at hpc8
    by_cases hfit : (g m0 (j + 1)).size ≤ formCap
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hfit)] at hres7
      obtain ⟨hal, hform⟩ := hres7
      rw [hal, decide_eq_false (by decide)] at hpc8
      simp only [Bool.false_eq_true, ↓reduceIte] at hpc8
      refine .done _ (Or.inr ⟨hpc8.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BlockForm.b7_next)), ⟨hfr8, by rw [hd8]; exact S7, hjl', ?_, ?_, ?_, ?_,
          ?_, by rw [hd8]; exact FW7, by rw [hd8]; exact hform⟩, hjl'⟩)
      · exact (K8 .rbx (by simp)).trans ((K3 .rbx (by simp)).trans hI.rbx)
      · rw [K8 .rbp (by simp), K3 .rbp (by simp)]; exact hI.rbp
      · rw [K8 .r14 (by simp), K3 .r14 (by simp)]; exact hI.r14
      · rw [show reg st8.data .r13 = _ from hm8.regs .r13 _ h13_8]
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
        rw [BitVec.toNat_add, show st7.data.regs.get64 .r13 = st.data.regs.get64 .r13 from e7_13,
          show (st.data.regs.get64 .r13).toNat = j from hI.r13]
        simp only [BitVec.toNat_ofNat]
        omega
      · rw [show reg st8.data .r15 = _ from hm8.regs .r15 _ h15_8]
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
        rw [show st7.data.regs.get64 .r15 = st.data.regs.get64 .r15 from e7_15,
          show st.data.regs.get64 .r15 = _ from hI.r15, BitVec.add_comm, BitVec.add_assoc,
          ← BitVec.ofNat_add, show 16 * j + 8 + 16 = 16 * (j + 1) + 8 by omega]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hfit)] at hres7
      rw [hres7, ite_eq_left_of_eq_true _ _ (by simp), hp.label NativeRustcVmX64.Vm.BlockForm.label_9_at] at hpc8
      refine Eventually.mono (finish hp hpre' hpc8 hfr8 (by rw [hd8]; exact S7)
        (by rw [hd8]; exact FW7) ?_) fun _ h ↦ Or.inl h
      rw [ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hfit ((size_le_bf _ _ _ hjl').trans h))]
      rw [show reg st8.data .r12 = reg st3.data .r12 from K8 .r12 (by simp), e3_12]
      omega
  -- `b10`: the slot's weight or `0`.
  have hwf3 := wf0 (d := st3.data) hst hF hfr3.kept (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b10_in_code (by simp [b10]) hp) run_b10 hwf3 nofun
    (hpc3.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BlockForm.b9_next)))
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hfr3.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid4, hmem4, hk4⟩ := after_eq run_b10 ▸ ok_b10
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf3 hmem4
  have hfr4 : Frame m0 80 slots 8 st4.data := Frame.of_block hfr3 hwf3 hm4 hmid4 slots_le
  have hl24 := load_frameWord (rest := []) (vars := fun _ ↦ 0) (ret := 0) FW3 (o := 24)
    (List.mem_cons_of_mem _ List.mem_cons_self)
  have hc4 : (SBool.cmp .ult .W64 (.reg .r13) (.load 0 24 8)).eval
      (frameEnv m0 st3.data 80 [] (fun _ ↦ 0) 0) = decide (j < (reg m0 .rdx).toNat) := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs, hl24]
    exact ult_of_toNat ((congrArg BitVec.toNat (K3 .r13 (by simp))).trans hI.r13) rfl
  simp only [PcOk] at hpc4
  rw [hc4] at hpc4
  have K4 : ∀ r ∈ [Reg64.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15],
      reg st4.data r = reg st3.data r := fun r hr ↦ hk4.reg' hm4 hr
  by_cases hjw : j < (reg m0 .rdx).toNat
  · -- `b5`: the slot's weight.
    rw [decide_eq_true hjw, ite_eq_left_of_eq_true _ _ (by simp), hp.label NativeRustcVmX64.Vm.BlockForm.label_7_at] at hpc4
    obtain ⟨hEr, hEa⟩ := elem_ok hW.1 hW.2 hjw
    have hwf4 := wf1 (d := st4.data) hst hF hfr4.kept hEr hEa (vars := fun _ ↦ 0) (ret := 0)
    have e4_15 : reg st4.data .r15 = (Sym.ptr 1 8).eval
        (frameEnv m0 st4.data 80 [(reg m0 .rsi + BitVec.ofNat 64 (16 * j), 16)] (fun _ ↦ 0) 0) := by
      rw [K4 .r15 (by simp), K3 .r15 (by simp), hI.r15]
      show _ = (reg m0 .rsi + BitVec.ofNat 64 (16 * j)) + BitVec.ofInt 64 8
      rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add]
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf4 nofun hpc4
      (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hfr4.rsp_eval, e4_15, trivial⟩ trivial trivial trivial)
      fun st5 hm5 hpc5 ↦ ?_
    obtain ⟨hmid5, hmem5, hcx5, h8_5, hk5, h15_5⟩ := after_eq run_b5 ▸ ok_b5
    have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq hwf4 hmem5
    refine tail st5 (hpc5.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BlockForm.b5_next)))
      (Frame.of_block hfr4 hwf4 hm5 hmid5 slots_le) (hd5.trans hd4) (fun r hr ↦ ?_) ?_
    · by_cases h15 : r = .r15
      · subst h15
        exact (hm5.regs .r15 _ h15_5).trans (e4_15.symm.trans (K4 .r15 hr))
      · have hr' : r ∈ [Reg64.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with h | h | h | h | h | h | h | h <;> subst h <;>
            first | exact absurd rfl h15 | simp
        exact (hk5.reg' hm5 hr').trans (K4 r hr)
    · rw [show reg st5.data .rcx = _ from hm5.regs .rcx _ hcx5,
        show reg st5.data .r8 = _ from hm5.regs .r8 _ h8_5]
      have hbase : (frameEnv m0 st4.data 80 [(reg m0 .rsi + BitVec.ofNat 64 (16 * j), 16)]
          (fun _ ↦ 0) 0).base 1 = reg m0 .rsi + BitVec.ofNat 64 (16 * j) := rfl
      have hmem0 : (frameEnv m0 st4.data 80 [(reg m0 .rsi + BitVec.ofNat 64 (16 * j), 16)]
          (fun _ ↦ 0) 0).mem0 = st4.data.dmem := rfl
      have e0 := NativeRustcVmX64.Arrays.ewOf_loads
        (frameEnv m0 st4.data 80 [(reg m0 .rsi + BitVec.ofNat 64 (16 * j), 16)] (fun _ ↦ 0) 0) 1 0
      rw [hbase, hmem0, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at e0
      show ewArg ((frameEnv m0 st4.data 80 [(reg m0 .rsi + BitVec.ofNat 64 (16 * j), 16)]
          (fun _ ↦ 0) 0).load 1 0 8) ((frameEnv m0 st4.data 80
          [(reg m0 .rsi + BitVec.ofNat 64 (16 * j), 16)] (fun _ ↦ 0) 0).load 1 (0 + 8) 8) = _
      rw [← e0]
      have hkeep : NativeRustcVm.ewOf st4.data.dmem (reg m0 .rsi + BitVec.ofNat 64 (16 * j)) =
          NativeRustcVm.ewOf m0.dmem (reg m0 .rsi + BitVec.ofNat 64 (16 * j)) := by
        refine NativeRustcVm.ewOf_congr fun i hi ↦ ?_
        rw [hd4, NativeRustcVm.addr_add_add]
        have hi' : 16 * j + i < 16 * (reg m0 .rdx).toNat := by omega
        refine S3 _ fun hq ↦ hq.elim (fun h ↦ ?_) fun h ↦ ?_
        · exact NativeRustcVm.Apart.not_inRange_add (NativeRustcVm.Apart.symm hFW) hW.1.2
            hFo.1.2 hi' h
        · exact NativeRustcVm.Apart.not_inRange_add hW.2 hW.1.2 (noWrap_stackBelow hst) hi'
            (inRange_le h (by omega))
      rw [hkeep]
      unfold slice
      rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
        List.getElem?_eq_getElem (by simpa using hjw), Option.getD_some,
        NativeRustcVm.getElem_ewsOf]
  · -- `b11`: no weight, `0`.
    rw [decide_eq_false hjw] at hpc4
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc4
    have hwf4 := wf0 (d := st4.data) hst hF hfr4.kept (vars := fun _ ↦ 0) (ret := 0)
    refine exec_at (infix_of b11_in_code (by simp [b11]) hp) run_b11 hwf4 nofun
      (hpc4.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BlockForm.b10_next)))
      (match_ofMachine ⟨rfl, trivial⟩ ⟨hfr4.rsp_eval, trivial⟩ trivial trivial trivial)
      fun st5 hm5 hpc5 ↦ ?_
    obtain ⟨hmid5, hmem5, hcx5, h8_5, hk5⟩ := after_eq run_b11 ▸ ok_b11
    have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq hwf4 hmem5
    simp only [PcOk] at hpc5
    refine tail st5 (hpc5.trans (hp.label NativeRustcVmX64.Vm.BlockForm.label_8_at))
      (Frame.of_block hfr4 hwf4 hm5 hmid5 slots_le) (hd5.trans hd4)
      (fun r hr ↦ (hk5.reg' hm5 hr).trans (K4 r hr)) ?_
    rw [show reg st5.data .rcx = _ from hm5.regs .rcx _ hcx5,
      show reg st5.data .r8 = _ from hm5.regs .r8 _ h8_5]
    unfold slice
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getElem?_eq_none (by simpa using hjw), Option.getD_none]
    rfl

omit [Host] in
theorem add_toUInt64 {a b : Nat} (h : a + b < 2 ^ 64) :
    a.toUInt64.toBitVec + b.toUInt64.toBitVec = (a + b).toUInt64.toBitVec := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega),
    toNat_toUInt64 h, Nat.mod_eq_of_lt h]

/-- **`block_form` meets its contract.** -/
theorem blockForm_spec (hp : Placed code k)
    (hft : Spec (Labels.label NativeRustcVmX64.Vm.FormTerms.entryLabel) FormTermsPre FormTermsPost)
    (hadd : ∀ f o, Spec (Labels.label NativeRustcVmX64.Vm.FormBufAddScaled.entryLabel) (FormBufAddScaledPre f o)
      (FormBufAddScaledPost f o)) :
    Spec (Labels.label NativeRustcVmX64.Vm.BlockForm.entryLabel) BlockFormPre BlockFormPost := by
  intro m0 hpre
  have hpre' := hpre
  obtain ⟨hst, hR, htu, hW, hFo, hFA, hFW⟩ := hpre
  have htu' : (reg m0 .rdi).toNat < 147 := by have := tuples_length; omega
  have hend := tsp_end htu
  have hnwF := frame_noWrap hst hF
  -- `b0`: the prologue; the form the constant `side_beta`.
  have hwf0 := wf1 (d := m0) hst hF (fun _ h ↦ h) hFo.1 hFo.2 (vars := fun _ ↦ 0)
    (ret := 0)
  unfold NativeRustcVmX64.Vm.BlockForm.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.BlockForm.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 nofun
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, known_ptr rfl rfl, trivial⟩ trivial trivial
      trivial) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro1, hw1, hwr1, hwr0, hbx1, h15_1, hdi1⟩ := after_eq run_b0 ▸ ok_b0
  have hfr1 : Frame m0 80 slots 8 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro1 slots_le (by decide)
  have S1 : Same m0 blockFormStack (fo m0) formBufBytes st1.data.dmem :=
    Same.block2 hst hF (fun _ _ ↦ rfl) hwf0 hm1 hw1 (belowRet_of_pro hpro1)
  have FW1 : FrameWords m0 80 st1.data.dmem [(24, UInt64.ofBitVec (reg m0 .rdx))] := by
    intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact wordAt_write_eq hm1 (b := stackBelow m0 80) rfl (by omega) (.reg .rdx)
      (hwr0.find (by simp)) rfl
  have F1 : FormBufAt st1.data.dmem (fo m0) (g m0 0) := by
    refine ⟨show 1 ≤ 148 by decide, ?_, fun i hi ↦ ?_⟩
    · rw [← off_zero (fo m0)]
      exact wordAt_write_eq hm1 (b := fo m0) rfl (by decide) (.lit 1) (hwr1.find (by simp)) rfl
    · have hi0 : i = 0 := by simpa [g, bf_zero, FormW.const] using hi
      subst hi0
      refine ⟨show 0 ≤ 2 by decide, ?_, nofun, nofun, ?_⟩
      · rw [show off (off (fo m0) 8) (termBytes * 0) = off (fo m0) 8 by rw [off_off]; rfl]
        exact wordAt_write_eq hm1 (b := fo m0) rfl (by decide) (.lit 0) (hwr1.find (by simp)) rfl
      · rw [NativeRustcVm.Transcript.ewAt_iff, off_off, off_off, off_off]
        exact ⟨wordAt_write_eq hm1 (b := fo m0) rfl (by decide) (.reg .rcx)
            (hwr1.find (by simp)) rfl,
          wordAt_write_eq hm1 (b := fo m0) rfl (by decide) (.reg .r8)
            (hwr1.find (by simp)) rfl⟩
  have e1bx : reg st1.data .rbx = fo m0 := (hm1.regs .rbx _ hbx1).trans (eval_ptr rfl)
  have e1_15 : reg st1.data .r15 = reg m0 .rsi := hm1.regs .r15 _ h15_1
  have e1di : reg st1.data .rdi = reg m0 .rdi := hm1.regs .rdi _ hdi1
  -- Past `TUPLES`: never.
  simp only [PcOk] at hpc1
  change st1.pc = if c0.eval (frameEnv m0 m0 80 [(fo m0, formBufBytes)] (fun _ ↦ 0) 0) then _
    else _ at hpc1
  have hc0 : c0.eval (frameEnv m0 m0 80 [(fo m0, formBufBytes)] (fun _ ↦ 0) 0) = false := by
    simp only [c0, SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs]
    rw [ult_of_toNat rfl (show (BitVec.ofNat 64 146).toNat = 146 from rfl),
      beq_of_toNat rfl (show (BitVec.ofNat 64 146).toNat = 146 from rfl)]
    rcases (show (reg m0 .rdi).toNat < 146 ∨ (reg m0 .rdi).toNat = 146 by omega) with h | h <;>
      simp [h]
  rw [hc0] at hpc1
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
  -- `b1`: the tuple's span from `TUPLES`.
  have hT := rodata_keep hst hR S1 hFA hFo.1.2 .tuples
  have hTn := hR.noWrap .tuples
  have hTa := apart_frame (hR.apart .tuples) hst.1 hF
  change NativeRustcVm.BytesAt st1.data.dmem (rodataAddr .tuples)
    (NativeRustcVm.Data.tuples.flatMap NativeRustcVm.Data.Span.bytes) at hT
  change NativeRustcVm.NoWrap _ (NativeRustcVm.Data.tuples.flatMap
    NativeRustcVm.Data.Span.bytes).length at hTn
  change NativeRustcVm.Apart _ (NativeRustcVm.Data.tuples.flatMap
    NativeRustcVm.Data.Span.bytes).length _ _ at hTa
  rw [length_tuples_bytes] at hTn hTa
  have hTm := hT.mapped
  rw [length_tuples_bytes] at hTm
  have hwf1 := frame_wf (m0 := m0) (d := st1.data) (F := 80)
    (rest := [(rodataAddr .tuples, 2352)]) (vars := fun _ ↦ 0) (ret := 0)
    ⟨Mapped.keeps (frame_mapped hst hF) hfr1.kept, hnwF⟩
    (fun x hx ↦ by rw [List.mem_singleton] at hx; subst hx; exact ⟨hTm, hTn⟩)
    (List.pairwise_pair.mpr (Apart.symm' hTa))
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf1 nofun
    (hpc1.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BlockForm.b0_next)))
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hfr1.rsp_eval, trivial⟩ ⟨rfl, trivial⟩
      ⟨by show (reg st1.data .rdi).toNat < 147; rw [e1di]; exact htu', trivial⟩ trivial)
    fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid2, hmem2, hbp2, h14_2, hk2⟩ := after_eq run_b1 ▸ ok_b1
  have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq hwf1 hmem2
  have hfr2 : Frame m0 80 slots 8 st2.data := Frame.of_block hfr1 hwf1 hm2 hmid2 slots_le
  obtain ⟨hws, hwl⟩ := tuples_words hT _ htu
  have hx : (Sym.reg .rdi).eval (frameEnv m0 st1.data 80 [(rodataAddr .tuples, 2352)]
      (fun _ ↦ 0) 0) = BitVec.ofNat 64 ((Sym.reg .rdi).eval (frameEnv m0 st1.data 80
        [(rodataAddr .tuples, 2352)] (fun _ ↦ 0) 0)).toNat :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)])
  have hX : ((Sym.reg .rdi).eval (frameEnv m0 st1.data 80 [(rodataAddr .tuples, 2352)]
      (fun _ ↦ 0) 0)).toNat = (reg m0 .rdi).toNat := by
    show (reg st1.data .rdi).toNat = _; rw [e1di]
  have hs0 : (spanWord 0).eval (frameEnv m0 st1.data 80 [(rodataAddr .tuples, 2352)]
      (fun _ ↦ 0) 0) = (tsp m0).start.toUInt64.toBitVec := by
    rw [eval_spanWord hx (by rw [hX]; exact htu'), hX, Nat.zero_add, tsp_eq htu]
    exact load_ofMachine rfl hws
  have hs8 : (spanWord 8).eval (frameEnv m0 st1.data 80 [(rodataAddr .tuples, 2352)]
      (fun _ ↦ 0) 0) = (tsp m0).len.toUInt64.toBitVec := by
    rw [eval_spanWord hx (by rw [hX]; exact htu'), hX, tsp_eq htu]
    refine load_ofMachine rfl ?_
    rw [show off (rodataAddr .tuples) (8 + 16 * (reg m0 .rdi).toNat) =
      rodataAddr .tuples + BitVec.ofNat 64 (16 * (reg m0 .rdi).toNat) + BitVec.ofNat 64 8 by
        rw [NativeRustcVm.addr_add_add, Nat.add_comm]]
    exact hwl
  have e2bp : reg st2.data .rbp = (tsp m0).start.toUInt64.toBitVec :=
    (hm2.regs .rbp _ hbp2).trans hs0
  have e2_14 : reg st2.data .r14 = ((tsp m0).start + (tsp m0).len).toUInt64.toBitVec := by
    rw [show reg st2.data .r14 = _ from hm2.regs .r14 _ h14_2]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    rw [hs0, hs8, add_toUInt64 (by omega)]
  -- `b3`: the count, the span's end at `16`; to the loop head.
  simp only [PcOk] at hpc2
  have hwf2 := wf0 (d := st2.data) hst hF hfr2.kept (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf2 nofun
    (hpc2.trans (hp.label NativeRustcVmX64.Vm.BlockForm.label_3_at))
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hfr2.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hw3, hwr3, h14_3, h13_3, h15_3, hk3⟩ := after_eq run_b3 ▸ ok_b3
  have hfr3 : Frame m0 80 slots 8 st3.data := Frame.of_block hfr2 hwf2 hm3 hmid3 slots_le
  have S3 : Same m0 blockFormStack (fo m0) formBufBytes st3.data.dmem :=
    Same.block hst hF (by rw [hd2]; exact S1) hwf2 hm3 (fun w h ↦ (hw3 w h).1)
      (belowRet_of_mid hmid3)
  have F3 : FormBufAt st3.data.dmem (fo m0) (g m0 0) :=
    formBuf_keep hst hF hFo.2 hFo.1.2 hwf2 hm3 (fun w h ↦ (hw3 w h).1) (belowRet_of_mid hmid3)
      (by rw [hd2]; exact F1)
  have FW3 : FrameWords m0 80 st3.data.dmem (Words m0) := by
    have FW3' := FrameWords.block (ws := [(24, UInt64.ofBitVec (reg m0 .rdx))]) hwf2 hm3
      (writesIn_of_mid hmid3) (by simp)
      (fun p hp w hw _ ↦ by
        rw [List.mem_singleton] at hp; rw [hp]; exact .inl (show w.off + w.n ≤ 24 from (hw3 w hw).2.2))
      (by rw [hd2]; exact FW1)
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact wordAt_write_eq hm3 (b := stackBelow m0 80) rfl (by omega) (.reg .r14)
        (hwr3.find (by simp)) e2_14
    · exact FW3' p hp
  have hI0 : Inv m0 0 st3.data := by
    refine ⟨hfr3, S3, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, FW3, F3⟩
    · exact (hk3.reg' hm3 (by simp)).trans ((hk2.reg' hm2 (by simp)).trans e1bx)
    · rw [show reg st3.data .rbp = _ from hk3.reg' hm3 (by simp), e2bp]
      exact toNat_toUInt64 (by omega)
    · rw [show reg st3.data .r14 = _ from hm3.regs .r14 _ h14_3]
      simp only [Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
        Env.ofMachine_regs]
      rw [show st2.data.regs.get64 .r14 = _ from e2_14, show st2.data.regs.get64 .rbp = _ from e2bp,
        ult_of_toNat (toNat_toUInt64 (by omega)) (toNat_toUInt64 (by omega))]
      rw [decide_eq_false (by omega)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]; omega),
        toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
    · rw [show reg st3.data .r13 = _ from hm3.regs .r13 _ h13_3]; rfl
    · rw [show reg st3.data .r15 = _ from hm3.regs .r15 _ h15_3]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [show st2.data.regs.get64 .r15 = _ from (hk2.reg' hm2 (by simp)).trans e1_15,
        BitVec.add_comm]
  simp only [PcOk] at hpc3
  refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BlockForm.b8Offset) ∧ ∃ j, (tsp m0).len - j = n ∧
    Inv m0 j st.data) (fun n st ⟨hpc, j, hn, hI⟩ ↦ ?_)
    ⟨hpc3.trans (hp.label NativeRustcVmX64.Vm.BlockForm.label_4_at), 0, rfl, hI0⟩
  refine Eventually.mono (step hp hft hadd hpre' hpc hI) fun st' h ↦ ?_
  rcases h with h | ⟨hpc', hI', hlt⟩
  · exact Or.inl h
  · exact Or.inr ⟨(tsp m0).len - (j + 1), by omega, hpc', j + 1, rfl, hI'⟩

end

end NativeRustcVmX64.Bus.BlockForm
