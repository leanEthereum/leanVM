module

public import NativeRustcVmX64.Whir.SubspaceTable.Layer
public import NativeRustcVmX64.Code.Vm.Memset.Names

/-!
# `subspace_table`: from the entry to the turns (x86-64)

`entry`: after `start`, `b1` tests `μ < 32` (else `b5` stores `None`'s tag and jumps to the
epilogue); `b2` spills the output; `μ = 0` goes on at `b11`; else `b3` splits `μ` into
`μ - μ % 8` words set eight at a time (`b6`, `vturn`) and `μ % 8` set one at a time (`b9`,
`tturn`), to `Init μ` at `b11`.
-/

namespace NativeRustcVmX64.Whir.SubspaceTable

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SubspaceTable NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region WordAt WordsAt wordOf)
open NativeRustcVmX64.Field (midS frameS frameEnv frame_wf match_frame)
open NativeRustcVmX64.Arrays (stackOk_mono load8_eq load_word wordAt_of_write eval_reg eval_lit
  eval_load eval_add eval_cmp_eq eval_not eval_test apart_symm not_inRange_of_apart
  written_region0)

public section

variable [Host] {k : Nat}

/-- From `b9` (`b10` next) with the first `μ - μ % 8` words set: `Init μ` at `b11`. -/
theorem tail (hp : Placed code k) {m0 : MachineData} (hpre : SubspaceTablePre m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b9Offset))
    (hI : Init m0 (muOf m0 / 8 * 8) st.data)
    (hr15 : reg st.data .r15 = fbOf m0 + BitVec.ofNat 64 (552 + 8 * (muOf m0 / 8 * 8)))
    (hrdx : reg st.data .rdx = BitVec.ofNat 64 (muOf m0 / 8 * 8))
    (hrax : reg st.data .rax = BitVec.ofNat 64 (muOf m0 % 8)) (h8 : 0 < muOf m0 % 8) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b11Offset) ∧ Init m0 (muOf m0) s.data)
      st := by
  refine exec_at (hb9 hp) run_b9 (Env.wf_nil _) (by intro l h; cases h) hpc (match_nil _)
    fun st1 hm1 hpc1 ↦ ?_
  have hfr1 := hI.fr.of_block (match_nil _) hm1 (Env.wf_nil _) rfl (after_eq run_b9 ▸ b9_keeps)
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq (Env.wf_nil _) rfl
  have hT0 : TInv m0 0 st1.data := by
    refine ⟨⟨hfr1, ?_, ?_, (Match.reg_eq (r := .r14) (match_nil _) hm1 rfl rfl).trans hI.r14,
      hI.hmu⟩, h8, (Match.reg_eq (r := .r15) (match_nil _) hm1 rfl rfl).trans hr15,
      (Match.reg_eq (r := .rdx) (match_nil _) hm1 rfl rfl).trans hrdx,
      (hm1.regs .rsi _ rfl).trans rfl,
      (Match.reg_eq (r := .rax) (match_nil _) hm1 rfl rfl).trans hrax⟩
    · unfold OutAt; rw [hd1]; exact hI.out
    · rw [hd1, Nat.add_zero]; exact hI.layer
  have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b10Offset) := hpc1
  refine Sym.loop (fun n s ↦ ∃ j, n = muOf m0 % 8 - j ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b10Offset) ∧
    TInv m0 j s.data) (fun n s ⟨j, hn, hpc, hT⟩ ↦ ?_) ⟨0, rfl, hpc1', hT0⟩
  have hs := hT.hs
  refine (tturn hp hpre hpc hT).mono fun s' h ↦ ?_
  rcases h with ⟨hpc', hT'⟩ | h
  · exact .inr ⟨_, by have := hT'.hs; omega, j + 1, rfl, hpc', hT'⟩
  · exact .inl h

/-- **From the entry to the turns**: `None` (μ ≥ 32) at the epilogue, or the layer at `b11`. -/
theorem entry (hp : Placed code k) (hmemset : Spec (Labels.label NativeRustcVmX64.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    {m0 : MachineData} (hpre : SubspaceTablePre m0) :
    Eventually (step1 Host.exe) (fun s ↦ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b24Offset) ∧ Fr m0 s.data ∧
      WordAt s.data.dmem (reg m0 .rdi) 0 ∧ 32 ≤ muOf m0) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b11Offset) ∧ Init m0 (muOf m0) s.data)) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b0Offset)⟩ := by
  have hpre' := hpre
  obtain ⟨hS, hout, _⟩ := hpre'
  obtain ⟨hF, -, -, -⟩ := stack_le
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hS1 := hS.1
  have hS2 := hS.2.1
  have hsl := slots_ok
  have htb : tableBytes = 504 := rfl
  have hmu64 : muOf m0 < 2 ^ 64 := (reg m0 .rsi).isLt
  have hmuv : reg m0 .rsi = BitVec.ofNat 64 (muOf m0) := reg_ofNat _
  refine (start hp hmemset hpre).bind fun st ⟨hpc, hfr, hlay, hrbx, hr14, hr15⟩ ↦ ?_
  -- `b1`: `μ < 32`
  refine exec_at (hb1 hp) run_b1 (Env.wf_nil _) (by intro l h; cases h) hpc (match_nil _)
    fun st1 hm1 hpc1 ↦ ?_
  have hfr1 := hfr.of_block (match_nil _) hm1 (Env.wf_nil _) rfl (after_eq run_b1 ▸ b1_keeps)
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq (Env.wf_nil _) rfl
  have e1 : ∀ R ∈ [Reg64.rbx, .r14, .r15], reg st1.data R = reg st.data R := by
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl <;> exact Match.reg_eq (match_nil _) hm1 rfl rfl
  simp only [PcOk] at hpc1
  rw [eval_not, show (SBool.cmp .ult .W64 (.reg .r14) (.lit 32)).eval (Env.ofMachine st.data []) =
      (reg st.data .r14).ult (BitVec.ofNat 64 32) from rfl, ult_ofNat (by decide), hr14] at hpc1
  obtain ⟨hT1, hF1⟩ := Arrays.pc_cond hpc1
  by_cases hbig : 32 ≤ muOf m0
  · -- `b5`: `None`
    have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b5Offset) :=
      (hT1 (by rw [Bool.not_eq_true', decide_eq_false_iff_not]; unfold muOf at hbig; omega)).trans
        (hp.label NativeRustcVmX64.Vm.SubspaceTable.label_1_at)
    have hrd : Readable st1.data (reg m0 .rdi) 8 :=
      Readable.keep (Readable.mono hout.1 (by omega)) hfr1.kept
    have hwf : (Env.ofMachine st1.data [(reg m0 .rdi, 8)]).WF :=
      Env.wf_of ⟨⟨hrd.1, hrd.2⟩, trivial⟩ (List.pairwise_singleton _ _)
    have hm : Match (Env.ofMachine st1.data [(reg m0 .rdi, 8)]) outS st1.data :=
      match_ofMachine ⟨rfl, trivial⟩
        ⟨show reg st1.data .rbx = reg m0 .rdi + BitVec.ofInt 64 0 by
            rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, e1 .rbx (by simp)]
            exact hrbx, trivial⟩
        trivial trivial trivial
    refine exec_at (hb5 hp) run_b5 hwf (by intro l h; cases h) hpc1' hm fun st2 hm2 hpc2 ↦ ?_
    obtain ⟨⟨hk2, hw2⟩, hv2⟩ := after_eq run_b5 ▸ b5_write
    have hfr2 : Fr m0 st2.data := hfr1.of_write hm hm2 hwf rfl hk2 (r := 0) rfl le_rfl hw2
      (fun p h ↦ .inl (inAny_one (Arrays.inRange_sub hout.1.2 (c := 0) (m := 8) (by omega)
        (by rwa [NativeRustcVm.addr_add_zero]))))
      fun q hq i hi ↦ by
        rw [addr_add]
        exact not_inRange_of_apart (Arrays.apart_mono (apart_symm (apart_frame' hS hF hout.2))
          (n'' := 8) (by omega)) (frame_ok hS hF).2.1
          (NativeRustcVm.NoWrap.mono hout.1.2 (by omega)) (by have := hsl q hq; omega)
    have htag := wordAt_of_write hm2 (r := 0) (o := 0) rfl (by decide) hv2
    rw [NativeRustcVm.addr_add_zero] at htag
    simp only [PcOk] at hpc2
    exact .done _ (.inl ⟨hpc2.trans (hp.label NativeRustcVmX64.Vm.SubspaceTable.label_2_at), hfr2, htag, hbig⟩)
  have hmu32 : muOf m0 < 32 := by omega
  have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b2Offset) :=
    hF1 (by rw [Bool.not_eq_true', decide_eq_false_iff_not, not_not]; unfold muOf at hmu32; omega)
  -- `b2`: the output spilled
  have hwf2 := hfr1.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at (hb2 hp) run_b2 hwf2 (by intro l h; cases h) hpc1' hfr1.mid_match
    fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨⟨hk2, hw2⟩, hw2', hv2⟩ := after_eq run_b2 ▸ b2_write
  have hfr2 : Fr m0 st2.data := hfr1.of_write hfr1.mid_match hm2 hwf2 rfl hk2 (r := 0) rfl
    (len := 16) (by omega) hw2 (fun p h ↦ .inr (inRange_frame hS hF (by omega) h))
    (fun q hq i hi ↦ by
      rw [addr_add]
      exact Arrays.not_inRange_above (by have := hsl q hq; omega)
        (by rw [hfe]; have := hsl q hq; omega))
  have hout2 : OutAt m0 st2.data := by
    have := wordAt_of_write hm2 (r := 0) (o := 8) rfl (by decide) (v := .reg .rbx) hv2
    rwa [eval_reg, Env.ofMachine_regs, show st1.data.regs.get64 .rbx = _ from
      (e1 .rbx (by simp)).trans hrbx] at this
  have hl248 : ((initL 0).flatMap NativeRustcVm.wordBytes).length = 248 := by
    rw [zero_words, List.length_replicate]
  have hlay2 : WordsAt st2.data.dmem (fbOf m0 + BitVec.ofNat 64 552) (initL 0) :=
    bytesAt_block hm2 hwf2 rfl (by rw [hl248]; omega)
      (fun w hw ↦ ⟨(hw2 w hw).1, .inl (by have := (hw2 w hw).2; omega)⟩)
      (by rw [Env.ofMachine_mem0, hd1]; exact hlay)
  have e2 : ∀ R ∈ [Reg64.r14, .r15], reg st2.data R = reg st.data R := by
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl <;>
      exact (Match.reg_eq hfr1.mid_match hm2 rfl rfl).trans (e1 _ (by simp))
  simp only [PcOk] at hpc2
  rw [eval_test, eval_reg, Env.ofMachine_regs, show st1.data.regs.get64 .r14 = _ from
    (e1 .r14 (by simp)).trans hr14, hmuv, ofNat_beq hmu64 (by decide)] at hpc2
  obtain ⟨hT2, hF2⟩ := Arrays.pc_cond hpc2
  have hinit0 : Init m0 0 st2.data :=
    ⟨hfr2, hout2, hlay2, (e2 .r14 (by simp)).trans hr14, hmu32⟩
  by_cases h0 : muOf m0 = 0
  · exact .done _ (.inr ⟨(hT2 (by rw [decide_eq_true_eq]; exact h0)).trans (hp.label NativeRustcVmX64.Vm.SubspaceTable.label_11_at),
      h0 ▸ hinit0⟩)
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b3Offset) := hF2 (by rw [decide_eq_true_eq]; exact h0)
  -- `b3`: `μ - μ % 8` and `μ % 8`
  obtain ⟨hv1, hv2, hv3, hv4⟩ := b3_vals (muOf m0) hmu32 (by omega)
  refine exec_at (hb3 hp) run_b3 (Env.wf_nil _) (by intro l h; cases h) hpc2' (match_nil _)
    fun st3 hm3 hpc3 ↦ ?_
  have hfr3 := hfr2.of_block (match_nil _) hm3 (Env.wf_nil _) rfl (after_eq run_b3 ▸ b3_keeps)
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq (Env.wf_nil _) rfl
  have hr14v : (Env.ofMachine st2.data []).regs .r14 = BitVec.ofNat 64 (muOf m0) :=
    (e2 .r14 (by simp)).trans (hr14.trans hmuv)
  have hrcx : (Sym.bin .and .W64 (.lit 2305843009213693951)
      (.bin .add .W64 (.reg .r14) (.lit 18446744073709551615))).eval (Env.ofMachine st2.data []) =
      BitVec.ofNat 64 (muOf m0 - 1) := by
    simp only [Sym.eval, hr14v]; exact hv1
  have hrsi3 : reg st3.data .rsi = BitVec.ofNat 64 (muOf m0) := by
    refine (hm3.regs .rsi _ rfl).trans ?_
    show BinOp.apply .add .W64 (Sym.eval _ _) (BitVec.ofNat 64 1) = _
    rw [hrcx, hv2]
  have hrax3 : reg st3.data .rax = BitVec.ofNat 64 (muOf m0 % 8) := by
    refine (hm3.regs .rax _ rfl).trans ?_
    show BinOp.apply .and .W32 (UnOp.apply .trunc .W32 (BinOp.apply .add .W64 (Sym.eval _ _)
      (BitVec.ofNat 64 1))) (BitVec.ofNat 64 7) = _
    rw [hrcx, hv2, hv3]
  have e3 : ∀ R ∈ [Reg64.r14, .r15], reg st3.data R = reg st.data R := by
    intro R hR
    rw [← e2 R hR]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl <;> exact Match.reg_eq (match_nil _) hm3 rfl rfl
  have hinit3 : Init m0 0 st3.data :=
    ⟨hfr3, by unfold OutAt; rw [hd3]; exact hout2, by rw [hd3]; exact hlay2,
      (e3 .r14 (by simp)).trans hr14, hmu32⟩
  simp only [PcOk] at hpc3
  rw [eval_not, show (SBool.cmp .ult .W64 (.bin .and .W64 (.lit 2305843009213693951)
      (.bin .add .W64 (.reg .r14) (.lit 18446744073709551615))) (.lit 7)).eval
        (Env.ofMachine st2.data []) = (BitVec.ofNat 64 (muOf m0 - 1)).ult (BitVec.ofNat 64 7) from
      by rw [← hrcx]; rfl, ult_ofNat (by decide), toNat_ofNat_lt (by omega)] at hpc3
  obtain ⟨hT3, hF3⟩ := Arrays.pc_cond hpc3
  by_cases hge : 8 ≤ muOf m0
  · -- `b6`, `b7`: eight words at a time
    have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b6Offset) :=
      (hT3 (by rw [Bool.not_eq_true', decide_eq_false_iff_not]; omega)).trans
        (hp.label NativeRustcVmX64.Vm.SubspaceTable.label_6_at)
    have hwf6 := hfr3.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
    refine exec_at (hb6 hp) run_b6 hwf6 (by intro l h; cases h) hpc3' hfr3.mid_match
      fun st4 hm4 hpc4 ↦ ?_
    have hfr4 := hfr3.of_block hfr3.mid_match hm4 hwf6 rfl (after_eq run_b6 ▸ b6_keeps)
    have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf6 rfl
    have hV0 : VInv m0 0 st4.data := by
      refine ⟨⟨hfr4, by unfold OutAt; rw [hd4]; exact hinit3.out, by rw [hd4]; exact hinit3.layer,
        (Match.reg_eq (r := .r14) hfr3.mid_match hm4 rfl rfl).trans hinit3.r14, hmu32⟩, rfl,
        by omega, ?_, (hm4.regs .rdx _ rfl).trans rfl, ?_, ?_⟩
      · refine (hm4.regs .r15 _ rfl).trans ?_
        exact ptr0_eval (o := 552)
      · refine (hm4.regs .rsi _ rfl).trans ?_
        show BinOp.apply .and .W64 (reg st3.data .rsi) (BitVec.ofNat 64 18446744073709551608) = _
        rw [hrsi3, hv4]
      · exact (Match.reg_eq (r := .rax) hfr3.mid_match hm4 rfl rfl).trans hrax3
    have hpc4' : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b7Offset) := hpc4
    have hloop := Sym.loop (tr := step1 Host.exe)
      (Q := fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b8Offset) ∧ Init m0 (muOf m0 / 8 * 8) s.data ∧
        reg s.data .r15 = fbOf m0 + BitVec.ofNat 64 (552 + 8 * (muOf m0 / 8 * 8)) ∧
        reg s.data .rdx = BitVec.ofNat 64 (muOf m0 / 8 * 8) ∧
        reg s.data .rax = BitVec.ofNat 64 (muOf m0 % 8))
      (fun n s ↦ ∃ d, n = muOf m0 - d ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b7Offset) ∧ VInv m0 d s.data)
      (fun n s ⟨d, hn, hpc, hV⟩ ↦ by
        have := hV.hlt
        refine (vturn hp hpre hpc hV).mono fun s' h ↦ ?_
        rcases h with ⟨hpc', hV'⟩ | h
        · exact .inr ⟨_, by omega, d + 8, rfl, hpc', hV'⟩
        · exact .inl h) (n := muOf m0 - 0) ⟨0, rfl, hpc4', hV0⟩
    refine hloop.bind fun s ⟨hpc5, hI5, hr155, hrdx5, hrax5⟩ ↦ ?_
    -- `b8`: the rest
    refine exec_at (hb8 hp) run_b8 (Env.wf_nil _) (by intro l h; cases h) hpc5 (match_nil _)
      fun st6 hm6 hpc6 ↦ ?_
    have hfr6 := hI5.fr.of_block (match_nil _) hm6 (Env.wf_nil _) rfl (after_eq run_b8 ▸ b8_keeps)
    have hd6 : st6.data.dmem = s.data.dmem := hm6.dmem_eq (Env.wf_nil _) rfl
    have hI6 : Init m0 (muOf m0 / 8 * 8) st6.data :=
      ⟨hfr6, by unfold OutAt; rw [hd6]; exact hI5.out, by rw [hd6]; exact hI5.layer,
        (Match.reg_eq (r := .r14) (match_nil _) hm6 rfl rfl).trans hI5.r14, hmu32⟩
    simp only [PcOk] at hpc6
    rw [eval_test, eval_reg, Env.ofMachine_regs, show s.data.regs.get64 .rax = _ from hrax5,
      ofNat_beq (by omega) (by decide)] at hpc6
    obtain ⟨hT6, hF6⟩ := Arrays.pc_cond hpc6
    by_cases hz : muOf m0 % 8 = 0
    · exact .done _ (.inr ⟨(hT6 (by rw [decide_eq_true_eq]; exact hz)).trans
        (hp.label NativeRustcVmX64.Vm.SubspaceTable.label_11_at), (show muOf m0 / 8 * 8 = muOf m0 by omega) ▸ hI6⟩)
    · exact (tail hp hpre (hF6 (by rw [decide_eq_true_eq]; exact hz)) hI6
        ((Match.reg_eq (r := .r15) (match_nil _) hm6 rfl rfl).trans hr155)
        ((Match.reg_eq (r := .rdx) (match_nil _) hm6 rfl rfl).trans hrdx5)
        ((Match.reg_eq (r := .rax) (match_nil _) hm6 rfl rfl).trans hrax5) (by omega)).mono
        fun _ h ↦ .inr h
  · -- `b4`: one word at a time from the first
    have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b4Offset) :=
      hF3 (by rw [Bool.not_eq_true', decide_eq_false_iff_not, not_not]; omega)
    refine exec_at (hb4 hp) run_b4 (Env.wf_nil _) (by intro l h; cases h) hpc3' (match_nil _)
      fun st4 hm4 hpc4 ↦ ?_
    have hfr4 := hfr3.of_block (match_nil _) hm4 (Env.wf_nil _) rfl (after_eq run_b4 ▸ b4_keeps)
    have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq (Env.wf_nil _) rfl
    have hq : muOf m0 / 8 * 8 = 0 := by omega
    simp only [PcOk] at hpc4
    refine (tail hp hpre (hpc4.trans (hp.label NativeRustcVmX64.Vm.SubspaceTable.label_9_at)) ?_ ?_ ?_ ?_ (by omega)).mono
      fun _ h ↦ .inr h
    · rw [hq]
      exact ⟨hfr4, by unfold OutAt; rw [hd4]; exact hinit3.out, by rw [hd4]; exact hinit3.layer,
        (Match.reg_eq (r := .r14) (match_nil _) hm4 rfl rfl).trans hinit3.r14, hmu32⟩
    · rw [hq, Nat.mul_zero, Nat.add_zero]
      exact (Match.reg_eq (r := .r15) (match_nil _) hm4 rfl rfl).trans ((e3 .r15 (by simp)).trans hr15)
    · rw [hq]; exact (hm4.regs .rdx _ rfl).trans rfl
    · exact (Match.reg_eq (r := .rax) (match_nil _) hm4 rfl rfl).trans hrax3

end

end NativeRustcVmX64.Whir.SubspaceTable
