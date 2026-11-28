module

public import NativeRustcVmX64.Whir.NovelEval.Mid
public import NativeRustcVmX64.Code.Vm.Kmul.Names
public import NativeRustcVmX64.Code.Vm.Memset.Names
public import NativeRustcVmX64.Code.Vm.NovelEval.Names

/-!
# `novel_eval` on x86-64

**`novelEval_spec`**: `b0a` pushes the callee-saved registers and opens the 1048-byte frame;
`b0b` keeps the arguments in them and zeroes the basis but its first word (`memset`). More than 64
coefficients (`b1`): `b17a` stores `None`'s tag. Else `b2` spills the output and the
coefficients' pointers and sets the basis to `[1]`; with fewer than two coefficients the basis is
complete, else `b3` spills the `What`s' end and the doubling loops (`doubling`) build it; `sum`
sums the products; `b16` stores them, `b17a` `Some`'s tag, `b17b` returns.
-/

namespace NativeRustcVmX64.Whir.NovelEval

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.NovelEval NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region WordAt WordsAt wordOf)
open NativeRustcVm.Transcript (off OptEWAt)
open NativeRustcVmX64.Field (midS frameS frameEnv frame_wf match_frame)
open NativeRustcVmX64.Arrays (stackOk_mono load8_eq wordAt_of_write ewAt_of_writes eval_reg
  eval_lit eval_load eval_add wf_two apart_symm not_inRange_of_apart)

public section

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0a.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.NovelEval.b0Offset) ∧
    b0b.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.NovelEval.b0Offset + b0a.length) := by
  have h := b0_in_code.trans hp.1 (by simp [b0])
  rw [← List.take_append_drop 8 b0] at h
  exact h.append
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.NovelEval.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.NovelEval.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.NovelEval.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb16 (hp : Placed code k) : b16.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.NovelEval.b16Offset) :=
  b16_in_code.trans hp.1 (by simp [b16])
theorem hb17 (hp : Placed code k) : b17a.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.NovelEval.b17Offset) ∧
    b17b.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.NovelEval.b17Offset + b17a.length) := by
  have h := b17_in_code.trans hp.1 (by simp [b17])
  rw [← List.take_append_drop 2 b17] at h
  exact h.append

/-- `novel_eval`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧ NovelEvalPost m0 s.data

/-- The output's frame. -/
abbrev OFrame (m0 st : MachineData) : Prop :=
  Frame m0 1104 novelEvalStack slots [⟨reg m0 .rdi, 24⟩] st

/-- **The tag and the epilogue** (`b17a`, `b17b`): RBX the tag, R15 the output, the value (for
`Some`) already stored. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hpre : NovelEvalPre m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b17Offset)) (hfr : OFrame m0 st.data)
    (hr15 : reg st.data .r15 = reg m0 .rdi) {v : Option EW}
    (htag : reg st.data .rbx = BitVec.ofNat 64 (if v.isSome then 1 else 0))
    (hval : ∀ x, v = some x → NativeRustcVm.EWAt st.data.dmem (off (reg m0 .rdi) 8) x)
    (hv : v = if (reg m0 .rdx).toNat ≤ laneCap then
      some (novelEval (slice m0 (reg m0 .rsi) (reg m0 .rdx))
        (wordSlice m0 (reg m0 .rcx) (reg m0 .r8).toNat)) else none) :
    Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hS, hcs, hwh, hout, _⟩ := hpre
  have hF : 1104 ≤ novelEvalStack := by decide
  have hrd : Readable st.data (reg m0 .rdi) 8 := Readable.keep (Readable.mono hout.1 (by omega)) hfr.kept
  have hwf : (Env.ofMachine st.data [(reg m0 .rdi, 8)]).WF :=
    Env.wf_of ⟨⟨hrd.1, hrd.2⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine st.data [(reg m0 .rdi, 8)]) tagS st.data :=
    match_ofMachine ⟨rfl, trivial⟩
      ⟨show reg st.data .r15 = reg m0 .rdi + BitVec.ofInt 64 0 by
          rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; exact hr15, trivial⟩
      trivial trivial trivial
  refine exec_at (hb17 hp).1 run_b17a hwf (by intro l h; cases h) hpc hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hk1, hw1, hv1⟩ := after_eq run_b17a ▸ b17a_write
  have hfr1 : OFrame m0 st1.data := hfr.of_write hm hm1 hwf rfl hk1 (r := 0) rfl le_rfl hw1
    (fun p h ↦ .inl (inAny_one (Arrays.inRange_sub hout.1.2 (c := 0) (m := 8) (by omega)
      (by rwa [NativeRustcVm.addr_add_zero]))))
    fun q hq i hi ↦ by
      rw [addr_add]
      exact not_inRange_of_apart (Arrays.apart_mono (apart_symm (apart_frame' hS hF hout.2))
        (n'' := 8) (by omega)) (frame_ok hS hF).2.1
        (NativeRustcVm.NoWrap.mono hout.1.2 (by omega)) (by have := slots_ok q hq; omega)
  have hso1 := same_region_le hm1 hwf (r := 0) rfl le_rfl hw1
  have htag1 : WordAt st1.data.dmem (reg m0 .rdi) (if v.isSome then 1 else 0) := by
    have := wordAt_of_write hm1 (r := 0) (o := 0) rfl (by decide) (v := .reg .rbx) hv1
    rw [NativeRustcVm.addr_add_zero, eval_reg, Env.ofMachine_regs,
      show st.data.regs.get64 .rbx = _ from htag] at this
    convert this using 1
    split <;> rfl
  -- `b17b`
  have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b17Offset + b17a.length) := hpc1
  have hwf2 := hfr1.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at (hb17 hp).2 run_b17b hwf2 (by intro l h; cases h) hpc1' hfr1.mid_match
    fun st2 hm2 hpc2 ↦ .done _ ?_
  obtain ⟨hpc', hrsp', hdm, hsaved⟩ := hfr1.done hS hF (out_one hout) hm2 hpc2
    (after_eq run_b17b ▸ b17b_restores).1 (after_eq run_b17b ▸ b17b_restores).2
  refine ⟨hpc', hrsp', ?_, fun p hp ↦ by rw [hdm]; exact hfr1.same p hp, hsaved⟩
  show OptEWAt st2.data.dmem (reg m0 .rdi) _
  rw [← hv, hdm]
  cases hvv : v with
  | none => rw [hvv] at htag1; exact htag1
  | some x =>
    rw [hvv] at htag1
    refine ⟨htag1, NativeRustcVm.BytesAt.of_sameOutside_apart (hval x hvv) hso1 ?_
      (NativeRustcVm.NoWrap.sub hout.1.2 (by rw [NativeRustcVm.length_ewBytes]))
      (NativeRustcVm.NoWrap.mono hout.1.2 (by omega))⟩
    rw [NativeRustcVm.length_ewBytes]
    have := hout.1.2
    unfold NoWrap at this
    unfold NativeRustcVm.Apart off
    rw [toNat_add_ofNat _ _ (by omega)]
    omega

/-- **The sum stored** (`b16`), then the tag and the epilogue. -/
theorem store (hp : Placed code k) {m0 : MachineData} (hpre : NovelEvalPre m0) (hc : cnt m0 ≤ 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b16Offset)) (hD : Done m0 st.data) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hpre' := hpre
  obtain ⟨hS, hcs, hwh, hout, _⟩ := hpre'
  have hF : 1104 ≤ novelEvalStack := by decide
  have hfr : OFrame m0 st.data := frame_mono hD.fr
  have hwf : (Env.ofMachine st.data [(stackBelow m0 1104, 1104 + 8), (reg m0 .rdi, 24)]).WF :=
    wf_two (stackOk_mono hS hF) hfr.kept (Readable.keep hout.1 hfr.kept)
      (apart_symm (apart_frame' hS hF hout.2))
  have hm : Match (Env.ofMachine st.data [(stackBelow m0 1104, 1104 + 8), (reg m0 .rdi, 24)]) outS
      st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hfr.rsp, trivial⟩ trivial trivial
      ⟨by
        show (Sym.load 0 16 8).eval (Env.ofMachine st.data [(stackBelow m0 1104, 1104 + 8),
          (reg m0 .rdi, 24)]) = reg m0 .rdi + BitVec.ofInt 64 0
        rw [eval_load, load8_eq]
        show (wordOf st.data.dmem (fbOf m0 + BitVec.ofNat 64 16)).toBitVec = _
        rw [NativeRustcVm.wordOf_of_wordAt hD.sp.out, UInt64.toBitVec_ofBitVec,
          show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], trivial⟩
  refine exec_at (hb16 hp) run_b16 hwf (by intro l h; cases h) hpc hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hk1, hw1, hv8, hv16⟩ := after_eq run_b16 ▸ b16_write
  have hfr1 : OFrame m0 st1.data := hfr.of_write hm hm1 hwf rfl hk1 (r := 1) rfl le_rfl hw1
    (fun p h ↦ .inl (inAny_one h))
    fun q hq i hi ↦ by
      rw [addr_add]
      exact not_inRange_of_apart (apart_symm (apart_frame' hS hF hout.2)) (frame_ok hS hF).2.1
        hout.1.2 (by have := slots_ok q hq; omega)
  have hval := ewAt_of_writes hm1 (r := 1) (o := 8) rfl (by decide) hv8 hv16
  rw [eval_reg, eval_reg, Env.ofMachine_regs, Env.ofMachine_regs,
    show st.data.regs.get64 .r14 = _ from hD.r14, show st.data.regs.get64 .rbx = _ from hD.rbx]
    at hval
  have hr15 : reg st1.data .r15 = reg m0 .rdi := by
    refine (hm1.regs .r15 _ rfl).trans ?_
    rw [eval_load, load8_eq]
    show (wordOf st.data.dmem (fbOf m0 + BitVec.ofNat 64 16)).toBitVec = _
    rw [NativeRustcVm.wordOf_of_wordAt hD.sp.out, UInt64.toBitVec_ofBitVec]
  have hc' : (reg m0 .rdx).toNat ≤ laneCap := hc
  refine finish hp hpre hpc1 hfr1 hr15 (v := some (accOf m0 (lenOf m0)))
    ((hm1.regs .rbx _ rfl).trans rfl) (fun x hx ↦ ?_) ?_
  · cases hx
    exact hval
  · rw [novelEval_eq']
    simp only [hc', ↓reduceIte]

omit [Host] in
theorem stack_le : 1104 ≤ novelEvalStack ∧ 1104 + kmulStack ≤ novelEvalStack := by decide

/-- **`novel_eval` meets its contract.** -/
theorem novelEval_spec (hp : Placed code k)
    (hkmul : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost)
    (hmemset : Spec (Labels.label NativeRustcVmX64.Vm.Memset.entryLabel) MemsetPre MemsetPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.NovelEval.entryLabel) NovelEvalPre NovelEvalPost := by
  intro m0 hpre
  have hpre' := hpre
  obtain ⟨hS, hcs, hwh, hout, hgot⟩ := hpre'
  obtain ⟨hF, -⟩ := stack_le
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hS1 := hS.1
  have hS2 := hS.2.1
  have hsl := slots_ok
  have hlw : ∀ w : UInt64, (NativeRustcVm.wordBytes w).length = 8 := NativeRustcVm.length_wordBytes
  rw [show Labels.label NativeRustcVmX64.Vm.NovelEval.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b0Offset) from hp.label NativeRustcVmX64.Vm.NovelEval.entry_at]
  -- `b0a`: the prologue
  have hwf0 := frame_wf (m := m0) (vars := fun _ ↦ 0) (ret := 0) (stackOk_mono hS hF)
    fun _ h ↦ h
  refine exec_then (hb0 hp).1 run_b0a hwf0 (by intro l h; cases h) match_frame
    fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, show b0a.length = 8 from rfl] at hpc1
  obtain ⟨hw0, hregs0, hmem0, hsp0, hargs0⟩ := after_eq run_b0a ▸ b0a_entry
  have hfr1 : NFrame m0 st1.data := Frame.of_entry hS hF hm1 hsp0 hw0 hregs0 hmem0
  have harg : ∀ r ∈ [Reg64.rdi, .rsi, .rdx, .rcx, .r8], reg st1.data r = reg m0 r := fun r hr ↦
    hm1.regs r (.reg r) (hargs0 r hr)
  -- `b0b`: the arguments, `memset`
  have hwf2 := hfr1.got_wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b1Offset)).toBitVec) hS hF hgot (by simp : "memset" ∈ _)
  have hm2start := hfr1.got_match (l := "memset") (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b1Offset)).toBitVec)
    (fun i hi => hfr1.got_byte hS hgot
    (by
      intro ar har
      simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with rfl | rfl | rfl
      · exact hcs.1.2
      · exact hwh.1.2
      · exact hout.1.2)
    (by intro r hr; cases hr) (by simp) hi)
  refine exec_at (hb0 hp).2 run_b0b hwf2 (fun _ _ ↦ rfl) hpc1 hm2start fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hk2, hsp2, hw2⟩ := after_eq run_b0b ▸ b0b_call
  have hrsp2 := rsp_call hm2 hsp2
  have hkept2 : Kept m0.dmem st2.data.dmem := fun p h ↦ hm2.kept hwf2 p (hfr1.kept p h)
  have hrdi2 : reg st2.data .rdi = fbOf m0 + BitVec.ofNat 64 40 := hm2.regs .rdi _ rfl
  have hrdx2 : (reg st2.data .rdx).toNat = 1016 := by
    rw [show reg st2.data .rdx = _ from hm2.regs .rdx _ rfl]; rfl
  have h40 : (fbOf m0 + BitVec.ofNat 64 40).toNat = (rspOf m0).toNat - 1104 + 40 := by
    rw [toNat_add_ofNat _ _ (by unfold fbOf; rw [hfe]; omega)]; unfold fbOf; rw [hfe]
  have hpre2 : MemsetPre st2.data := by
    unfold MemsetPre
    simp only [hrdi2, hrdx2]
    refine ⟨stackOk_callee hS hkept2 hrsp2 (by omega), fun i hi ↦ ?_, ?_, ?_⟩
    · rw [fbOf, addr_add]; exact hkept2 _ (hfmap _ (by omega))
    · unfold NoWrap; rw [h40]; omega
    · unfold Apart; rw [hrsp2, hfe, h40]; omega
  refine Frame.call hmemset hfr1 hS (by decide : 1104 + 0 ≤ novelEvalStack) (L := 1056)
    (by decide) hsl out_nil hwf2 hm2start hm2 hpc2 hk2 hsp2
    (fun w hw ↦ ⟨(hw2 w hw).1, by have := (hw2 w hw).2; omega⟩) hpre2
    (fun m' ⟨_, _, hso, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hso p fun h ↦ hp (.inr (.inl (by
      simp only [hrdi2, hrdx2] at h
      exact inRange_low_of hS hF (by omega) (by omega) h)))⟩)
    fun st3 hpc3 hfr3 ⟨_, _, _, hsv3⟩ ↦ ?_
  have hrbp3 : reg st3.data .rbp = reg m0 .rsi :=
    (hsv3.1 .rbp rfl).trans ((hm2.regs .rbp _ rfl).trans (harg .rsi (by simp)))
  have hr123 : reg st3.data .r12 = reg m0 .rcx :=
    (hsv3.1 .r12 rfl).trans ((hm2.regs .r12 _ rfl).trans (harg .rcx (by simp)))
  have hr133 : reg st3.data .r13 = reg m0 .r8 :=
    (hsv3.1 .r13 rfl).trans ((hm2.regs .r13 _ rfl).trans (harg .r8 (by simp)))
  have hr143 : reg st3.data .r14 = reg m0 .rdx :=
    (hsv3.1 .r14 rfl).trans ((hm2.regs .r14 _ rfl).trans (harg .rdx (by simp)))
  have hr153 : reg st3.data .r15 = reg m0 .rdi :=
    (hsv3.1 .r15 rfl).trans ((hm2.regs .r15 _ rfl).trans (harg .rdi (by simp)))
  have hrbx3 : reg st3.data .rbx = BitVec.ofNat 64 0 :=
    (hsv3.1 .rbx rfl).trans ((hm2.regs .rbx _ rfl).trans rfl)
  -- `b1`: more than 64 coefficients
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b1Offset) := hpc3
  refine exec_at (hb1 hp) run_b1 (Env.wf_nil _) (by intro l h; cases h) hpc3' (match_nil _)
    fun st4 hm4 hpc4 ↦ ?_
  have hfr4 := hfr3.of_block (match_nil _) hm4 (Env.wf_nil _) rfl (after_eq run_b1 ▸ b1_keeps)
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq (Env.wf_nil _) rfl
  have e4 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg st4.data r = reg st3.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Match.reg_eq (match_nil _) hm4 rfl rfl
  have hcnt : cnt m0 = (reg m0 .rdx).toNat := rfl
  simp only [PcOk] at hpc4
  rw [gt_eval, eval_reg, eval_lit, Env.ofMachine_regs,
    show st3.data.regs.get64 .r14 = _ from hr143, BitVec.toNat_ofNat] at hpc4
  obtain ⟨hT, hF4⟩ := Arrays.pc_cond hpc4
  by_cases hbig : 64 < cnt m0
  · refine finish hp hpre ((hT (by rw [decide_eq_true_eq]; omega)).trans
      (hp.label NativeRustcVmX64.Vm.NovelEval.label_12_at)) (frame_mono hfr4) ((e4 .r15 (by simp)).trans (hr153))
      (v := none) ((e4 .rbx (by simp)).trans hrbx3) (fun _ h ↦ by cases h) ?_
    have : ¬(reg m0 .rdx).toNat ≤ laneCap := by show ¬_ ≤ 64; omega
    simp only [this, ↓reduceIte]
  have hc : cnt m0 ≤ 64 := by omega
  have hpc4' : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b2Offset) := hF4 (by rw [decide_eq_true_eq]; omega)
  -- `b2`: the spills, the basis `[1]`
  have hwf5 := hfr4.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at (hb2 hp) run_b2 hwf5 (by intro l h; cases h) hpc4' hfr4.mid_match
    fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hk5, hw5, hv32, hv16, hv24⟩ := after_eq run_b2 ▸ b2_write
  have hfr5 : NFrame m0 st5.data := hfr4.of_write hfr4.mid_match hm5 hwf5 rfl hk5 (r := 0) rfl
    (len := 40) (by omega) (fun w hw ↦ ⟨(hw5 w hw).1, (hw5 w hw).2.2⟩)
    (fun p h ↦ .inr (inRange_frame hS hF (by omega) h))
    (fun q hq i hi ↦ by
      rw [addr_add]
      exact Arrays.not_inRange_above (by have := hsl q hq; omega)
        (by rw [hfe]; have := hsl q hq; omega))
  have hsp5 : Spill m0 st5.data := by
    refine ⟨?_, ?_⟩
    · have := wordAt_of_write hm5 (r := 0) (o := 16) rfl (by decide) (v := .reg .r15) hv16
      rwa [eval_reg, Env.ofMachine_regs, show st4.data.regs.get64 .r15 = _ from
        (e4 .r15 (by simp)).trans (hr153)] at this
    · have := wordAt_of_write hm5 (r := 0) (o := 24) rfl (by decide) (v := .reg .rbp) hv24
      rwa [eval_reg, Env.ofMachine_regs, show st4.data.regs.get64 .rbp = _ from
        (e4 .rbp (by simp)).trans (hrbp3)] at this
  have hb0 : basisOf m0 0 = #[1] := by unfold basisOf; rw [novelPre_zero]
  have hbas5 : WordsAt st5.data.dmem (fbOf m0 + BitVec.ofNat 64 32) (basisOf m0 0).toList := by
    rw [hb0]
    exact NativeRustcVm.wordsAt_singleton.mpr
      (wordAt_of_write hm5 (r := 0) (o := 32) rfl (by decide) (v := .lit 1) hv32)
  have hrbp5 : (reg st5.data .rbp).toNat = (basisOf m0 0).size := by
    rw [hb0, show reg st5.data .rbp = _ from hm5.regs .rbp _ rfl]; rfl
  have e5 : ∀ r ∈ [Reg64.r12, .r13, .r14], reg st5.data r = reg st4.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Match.reg_eq hfr4.mid_match hm5 rfl rfl
  have hr145 : reg st5.data .r14 = reg m0 .rdx :=
    (e5 .r14 (by simp)).trans ((e4 .r14 (by simp)).trans (hr143))
  simp only [PcOk] at hpc5
  rw [show (SBool.cmp .ult .W64 (.reg .r14) (.lit 2)).eval (frameEnv m0 st4.data 1104 (fun _ ↦ 0) 0)
      = decide ((reg st4.data .r14).toNat < 2) from by
        rw [show (SBool.cmp .ult .W64 (.reg .r14) (.lit 2)).eval
          (frameEnv m0 st4.data 1104 (fun _ ↦ 0) 0) =
            (reg st4.data .r14).ult (BitVec.ofNat 64 2) from rfl, ult_ofNat (by decide)],
    (e4 .r14 (by simp)).trans (hr143)] at hpc5
  obtain ⟨hT5, hF5⟩ := Arrays.pc_cond hpc5
  have hmid : ∀ {s : MachineState}, s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b9Offset) → Mid m0 s.data →
      Eventually (step1 Host.exe) (Post m0) s := fun hpc hM ↦
    (sum hp hkmul hpre hc hpc hM).bind fun s ⟨hpc', hD⟩ ↦ store hp hpre hc hpc' hD
  by_cases hsmall : cnt m0 < 2
  · have hfin := basisOf_final m0 (j := 0) (Nat.zero_le _) (by rw [hb0]; simp; omega)
    exact hmid ((hT5 (by rw [decide_eq_true_eq]; omega)).trans (hp.label NativeRustcVmX64.Vm.NovelEval.label_7_at))
      ⟨hfr5, hsp5, by rw [hfin]; exact hrbp5, hr145, by rw [hfin]; exact hbas5⟩
  -- `b3`: the `What`s' end
  have hpc5' : st5.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NovelEval.b3Offset) := hF5 (by rw [decide_eq_true_eq]; omega)
  have hwf6 := hfr5.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at (hb3 hp) run_b3 hwf6 (by intro l h; cases h) hpc5' hfr5.mid_match
    fun st6 hm6 hpc6 ↦ ?_
  obtain ⟨hk6, hw6, hv8⟩ := after_eq run_b3 ▸ b3_write
  have hfr6 : NFrame m0 st6.data := hfr5.of_write hfr5.mid_match hm6 hwf6 rfl hk6 (r := 0) rfl
    (len := 16) (by omega) (fun w hw ↦ ⟨(hw6 w hw).1, (hw6 w hw).2.2⟩)
    (fun p h ↦ .inr (inRange_frame hS hF (by omega) h))
    (fun q hq i hi ↦ by
      rw [addr_add]
      exact Arrays.not_inRange_above (by have := hsl q hq; omega)
        (by rw [hfe]; have := hsl q hq; omega))
  have k6 : ∀ {o : Nat} {bs : List UInt8}, 16 ≤ o → o + bs.length ≤ 1112 →
      NativeRustcVm.BytesAt st5.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt st6.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs :=
    fun h16 hl h ↦ bytesAt_block hm6 hwf6 rfl hl
      (fun w hw ↦ ⟨(hw6 w hw).1, .inl (by have := (hw6 w hw).2.2; omega)⟩) h
  have hr12 : reg st5.data .r12 = reg m0 .rcx :=
    (e5 .r12 (by simp)).trans ((e4 .r12 (by simp)).trans (hr123))
  have hr13 : reg st5.data .r13 = reg m0 .r8 :=
    (e5 .r13 (by simp)).trans ((e4 .r13 (by simp)).trans (hr133))
  have hed : EndAt m0 st6.data := by
    have := wordAt_of_write hm6 (r := 0) (o := 8) rfl (by decide)
      (v := .bin .add .W64 (.reg .r12) (.bin .mul .W64 (.reg .r13) (.lit 8))) hv8
    rw [eval_add, eval_reg, Env.ofMachine_regs, show st5.data.regs.get64 .r12 = _ from hr12,
      show (Sym.bin .mul .W64 (.reg .r13) (.lit 8)).eval (frameEnv m0 st5.data 1104 (fun _ ↦ 0) 0)
        = reg st5.data .r13 * BitVec.ofNat 64 8 from mul64 _ _, hr13,
      ofNat_toNat (x := reg m0 .r8) rfl, mul8] at this
    exact this
  have hlb0 : ((basisOf m0 0).toList.flatMap NativeRustcVm.wordBytes).length = 8 := by
    rw [hb0]; rfl
  have hI0 : OInv m0 0 st6.data := by
    refine ⟨hfr6, ⟨k6 (by omega) (by rw [hlw]; omega) hsp5.out,
      k6 (by omega) (by rw [hlw]; omega) hsp5.cs⟩, hed, Nat.zero_le _, by rw [hb0]; simp; omega,
      ?_, ?_, ?_, k6 (by omega) (by rw [hlb0]; omega) hbas5⟩
    · refine (Match.reg_eq (r := .r12) hfr5.mid_match hm6 rfl rfl).trans (hr12.trans ?_)
      simp
    · show (st6.data.regs.get64 .rbp).toNat = _
      rw [Match.reg_eq (r := .rbp) (v := .reg .rbp) hfr5.mid_match hm6 rfl rfl]; exact hrbp5
    · exact (Match.reg_eq (r := .r14) hfr5.mid_match hm6 rfl rfl).trans hr145
  exact (doubling hp hkmul hpre hc hpc6 hI0).bind fun s ⟨hpc', hM⟩ ↦ hmid hpc' hM

end

end NativeRustcVmX64.Whir.NovelEval
