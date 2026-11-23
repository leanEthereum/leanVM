module

public import NativeRustcVmX64.Whir.FoldRow.Round
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.FoldRow.Names
public import NativeRustcVmX64.Code.Vm.Kmul.Names

/-!
# `fold_row` on x86-64

**`foldRow_spec`**: `b0a` pushes the callee-saved registers and opens the 40-byte frame; `b0b`
spills `x` and keeps `n` (RBX) and the lanes (R14). With no round (`b0b`'s test) the result is
read at once; else `b1` spills the rounds' end and the rounds (`round`, `next`, by `Sym.loop`)
fold the lanes in place. `b13` tests the size left: none, the result `0`; else `b14` reads lane
`0`. `b15` returns it.
-/

namespace NativeRustcVmX64.Whir.FoldRow

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.FoldRow NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region WordAt WordsAt EWAt ewOf wordOf)
open NativeRustcVmX64.Field (midS frameS frameEnv frame_wf match_frame)
open NativeRustcVmX64.Arrays (stackOk_mono load8_eq load_word wordAt_of_write eval_reg eval_lit
  eval_load eval_add eval_cmp_eq eval_test eval_shl_lit beq_add_left ew_of_loads
  not_inRange_of_apart)

public section

theorem add32 (a : BitVec 64) (r : Nat) :
    BitVec.ofNat 64 32 + (a + BitVec.ofNat 64 (32 * r)) = a + BitVec.ofNat 64 (32 * (r + 1)) := by
  rw [BitVec.add_comm, addr_add]
  congr 2

variable [Host] {k : Nat}

/-- **After round `r`** (`b3`): the next round's head, or the rounds done. -/
theorem next (hp : Placed code k) {m0 : MachineData} (hpre : FoldRowPre m0) {r : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b3Offset)) (hE : EInv m0 r st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b4Offset) ∧ RInv m0 (r + 1) s.data) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b13Offset) ∧ Done m0 s.data)) st := by
  obtain ⟨hS, hlanes, hrin, hap, hR6⟩ := hpre
  obtain ⟨hF, -, -⟩ := stack_le
  have hfr := hE.base.fr
  have hR : rnOf m0 ≤ 6 := hR6
  have hr := hE.hr
  have hwf := hfr.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at (hb3 hp) run_b3 hwf (by intro l h; cases h) hpc hfr.mid_match
    fun st1 hm1 hpc1 ↦ ?_
  have hfr1 := hfr.of_block hfr.mid_match hm1 hwf rfl (after_eq run_b3 ▸ b3_keeps)
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hl40 : (frameEnv m0 st.data 96 (fun _ ↦ 0) 0).load 0 40 8 =
      rpOf m0 + BitVec.ofNat 64 (32 * r) := by
    rw [load_word (show WordAt st.data.dmem (stackBelow m0 96 + BitVec.ofNat 64 40) _ from hE.rd)]
  have hl24 : (frameEnv m0 st.data 96 (fun _ ↦ 0) 0).load 0 24 8 =
      rpOf m0 + BitVec.ofNat 64 (32 * rnOf m0) := by
    rw [load_word (show WordAt st.data.dmem (stackBelow m0 96 + BitVec.ofNat 64 24) _ from
      hE.base.ed)]
  have hbase1 : Base m0 st1.data := ⟨hfr1, hd1 ▸ hE.base.x, hd1 ▸ hE.base.ed,
    (Match.reg_eq (r := .r14) hfr.mid_match hm1 rfl rfl).trans hE.base.r14⟩
  have hrbx1 : reg st1.data .rbx = BitVec.ofNat 64 (nOf m0 >>> (r + 1)) :=
    (Match.reg_eq (r := .rbx) hfr.mid_match hm1 rfl rfl).trans hE.rbx
  simp only [PcOk] at hpc1
  rw [eval_cmp_eq, eval_add, eval_lit, eval_load, eval_load, hl40, hl24, add32, beq_add_left,
    ofNat_beq (by omega) (by omega)] at hpc1
  obtain ⟨hT, hF1⟩ := Arrays.pc_cond hpc1
  by_cases hlast : r + 1 = rnOf m0
  · refine .done _ (.inr ⟨(hT (by rw [decide_eq_true_eq]; omega)).trans (hp.label NativeRustcVmX64.Vm.FoldRow.label_8_at),
      hfr1, hbase1.r14, by rw [hrbx1, hlast], by rw [hd1, ← hlast]; exact hE.lanes⟩)
  · refine .done _ (.inl ⟨hF1 (by rw [decide_eq_true_eq]; omega), hbase1, by omega, ?_,
      by rw [hrbx1], by rw [hd1]; exact hE.lanes⟩)
    refine (hm1.regs .rcx _ rfl).trans ?_
    rw [eval_add, eval_lit, eval_load, hl40, add32]

/-- **The rounds**, from the first's head. -/
theorem rounds (hp : Placed code k) (hkmul : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : FoldRowPre m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b4Offset)) (hI : RInv m0 0 st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b13Offset) ∧ Done m0 s.data) st := by
  refine Sym.loop (fun n s ↦ ∃ r, n = rnOf m0 - r ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b4Offset) ∧
    RInv m0 r s.data) (fun n s ⟨r, hn, hpc, hI⟩ ↦ ?_) ⟨0, rfl, hpc, hI⟩
  have hr := hI.hr
  refine (round hp hkmul hmul hpre hpc hI).bind fun s ⟨hpc', hE⟩ ↦ ?_
  refine (next hp hpre hpc' hE).mono fun s' h ↦ ?_
  rcases h with ⟨hpc'', hI'⟩ | h
  · exact .inr ⟨_, by have := hI'.hr; omega, r + 1, rfl, hpc'', hI'⟩
  · exact .inl h

theorem hb0 (hp : Placed code k) : b0a.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.FoldRow.b0Offset) ∧
    b0b.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.FoldRow.b0Offset + b0a.length) := by
  have h := b0_in_code.trans hp.1 (by simp [b0])
  rw [← List.take_append_drop 8 b0] at h
  exact h.append
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.FoldRow.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb13 (hp : Placed code k) : b13.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.FoldRow.b13Offset) :=
  b13_in_code.trans hp.1 (by simp [b13])
theorem hb14 (hp : Placed code k) : b14.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.FoldRow.b14Offset) :=
  b14_in_code.trans hp.1 (by simp [b14])
theorem hb15 (hp : Placed code k) : b15.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.FoldRow.b15Offset) :=
  b15_in_code.trans hp.1 (by simp [b15])

/-- `fold_row`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧ FoldRowPost m0 s.data

/-- **The result** (`b13`, `b14`, `b15`). -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hpre : FoldRowPre m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b13Offset)) (hD : Done m0 st.data) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hpre' := hpre
  obtain ⟨hS, hlanes, hrin, hap, hR6⟩ := hpre'
  obtain ⟨hF, -, -⟩ := stack_le
  have hfr := hD.fr
  have hR : rnOf m0 ≤ 6 := hR6
  have hn64 := (reg m0 .rsi).isLt
  have hsh64 : nOf m0 >>> rnOf m0 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by unfold nOf; exact hn64)
  have hout := out_one hlanes
  refine exec_at (hb13 hp) run_b13 (Env.wf_nil _) (by intro l h; cases h) hpc (match_nil _)
    fun st1 hm1 hpc1 ↦ ?_
  have hfr1 := hfr.of_block (match_nil _) hm1 (Env.wf_nil _) rfl (after_eq run_b13 ▸ b13_keeps)
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq (Env.wf_nil _) rfl
  have hrbx1 : reg st1.data .rbx = BitVec.ofNat 64 (nOf m0 >>> rnOf m0) :=
    (Match.reg_eq (r := .rbx) (match_nil _) hm1 rfl rfl).trans hD.rbx
  have hrax1 : reg st1.data .rax = BitVec.ofNat 64 (nOf m0 >>> rnOf m0) :=
    (hm1.regs .rax _ rfl).trans hD.rbx
  simp only [PcOk] at hpc1
  rw [eval_test, eval_reg, Env.ofMachine_regs, show st.data.regs.get64 .rbx = _ from hD.rbx,
    ofNat_beq hsh64 (by decide)] at hpc1
  obtain ⟨hT, hF1⟩ := Arrays.pc_cond hpc1
  have hres := foldRow_eq' m0 hR
  -- `b15` from a state with the result in RAX, RBX
  have epi : ∀ {s : MachineState}, s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b15Offset) → Fr m0 s.data →
      ewArg (reg s.data .rax) (reg s.data .rbx) =
        (if nOf m0 >>> rnOf m0 = 0 then 0 else lanesAt m0 (rnOf m0) 0) →
      Eventually (step1 Host.exe) (Post m0) s := fun {s} hpc hfr hv ↦ by
    have hwf := hfr.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
    refine exec_at (hb15 hp) run_b15 hwf (by intro l h; cases h) hpc hfr.mid_match
      fun s1 hm hpc' ↦ .done _ ?_
    obtain ⟨hpc'', hrsp', hdm, hsaved⟩ := hfr.done hS hF hout hm hpc'
      (after_eq run_b15 ▸ b15_restores).1 (after_eq run_b15 ▸ b15_restores).2
    refine ⟨hpc'', hrsp', ?_, fun p hp ↦ by rw [hdm]; exact hfr.same p hp, hsaved⟩
    show ewRet s1.data = foldRow _ _ _
    rw [hres, ← hv]
    show (⟨UInt64.ofBitVec (s1.data.regs.get64 .rax), UInt64.ofBitVec (s1.data.regs.get64 .rdx)⟩
      : EW) = _
    rw [Match.reg_eq (r := .rax) hfr.mid_match hm rfl rfl, hm.regs .rdx _ rfl]
    rfl
  by_cases h0 : nOf m0 >>> rnOf m0 = 0
  · refine epi ((hT (by rw [decide_eq_true_eq]; exact h0)).trans (hp.label NativeRustcVmX64.Vm.FoldRow.label_10_at)) hfr1 ?_
    rw [hrax1, hrbx1, h0]
    simp only [↓reduceIte]
    rfl
  · have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b14Offset) := hF1 (by rw [decide_eq_true_eq]; exact h0)
    have hrd : Readable st1.data (aOf m0) 16 := Readable.keep (Readable.mono hlanes.1 (by
      show 16 ≤ 1024; omega)) hfr1.kept
    have hwf2 : (Env.ofMachine st1.data [(aOf m0, 16)]).WF :=
      Env.wf_of ⟨⟨hrd.1, hrd.2⟩, trivial⟩ (List.pairwise_singleton _ _)
    have hm2 : Match (Env.ofMachine st1.data [(aOf m0, 16)]) firstS st1.data :=
      match_ofMachine ⟨rfl, trivial⟩
        ⟨show reg st1.data .r14 = aOf m0 + BitVec.ofInt 64 0 by
            rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
            exact (Match.reg_eq (r := .r14) (match_nil _) hm1 rfl rfl).trans hD.r14, trivial⟩
        trivial trivial trivial
    refine exec_at (hb14 hp) run_b14 hwf2 (by intro l h; cases h) hpc1' hm2 fun st2 hm3 hpc2 ↦ ?_
    have hfr2 := hfr1.of_block hm2 hm3 hwf2 rfl (after_eq run_b14 ▸ b14_keeps)
    refine epi hpc2 hfr2 ?_
    rw [ew_of_loads (r := 0) (off := 0) hm3 rfl rfl]
    simp only [h0, ↓reduceIte]
    show ewOf st1.data.dmem (aOf m0 + BitVec.ofNat 64 0) = _
    rw [hd1]
    exact NativeRustcVm.ewOf_of_ewAt (hD.lanes 0 (by decide))

/-- **`fold_row` meets its contract.** -/
theorem foldRow_spec (hp : Placed code k)
    (hkmul : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.FoldRow.entryLabel) FoldRowPre FoldRowPost := by
  intro m0 hpre
  have hpre' := hpre
  obtain ⟨hS, hlanes, hrin, hap, hR6⟩ := hpre'
  obtain ⟨hF, -, -⟩ := stack_le
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hsl := slots_ok
  have hR : rnOf m0 ≤ 6 := hR6
  have hrb : roundBytes = 32 := rfl
  rw [show Labels.label NativeRustcVmX64.Vm.FoldRow.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b0Offset) from hp.label NativeRustcVmX64.Vm.FoldRow.entry_at]
  have hwf0 := frame_wf (m := m0) (vars := fun _ ↦ 0) (ret := 0) (stackOk_mono hS hF)
    fun _ h ↦ h
  refine exec_then (hb0 hp).1 run_b0a hwf0 (by intro l h; cases h) match_frame
    fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, show b0a.length = 8 from rfl] at hpc1
  obtain ⟨hw0, hregs0, hmem0, hsp0, hargs0⟩ := after_eq run_b0a ▸ b0a_entry
  have hfr1 : Fr m0 st1.data := Frame.of_entry hS hF hm1 hsp0 hw0 hregs0 hmem0
  have harg : ∀ r ∈ [Reg64.rdi, .rsi, .rdx, .rcx, .r8], reg st1.data r = reg m0 r := fun r hr ↦
    hm1.regs r (.reg r) (hargs0 r hr)
  -- `b0b`
  have hwf2 := hfr1.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at (hb0 hp).2 run_b0b hwf2 (by intro l h; cases h) hpc1 hfr1.mid_match
    fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hk2, hw2, hv2⟩ := after_eq run_b0b ▸ b0b_write
  have hfr2 : Fr m0 st2.data := hfr1.of_write hfr1.mid_match hm2 hwf2 rfl hk2 (r := 0) rfl
    (len := 40) (by omega) (fun w hw ↦ ⟨(hw2 w hw).1, (hw2 w hw).2.2⟩)
    (fun p h ↦ .inr (inRange_frame hS hF (by omega) h))
    (fun q hq i hi ↦ by
      rw [addr_add]
      exact Arrays.not_inRange_above (by have := hsl q hq; omega)
        (by rw [hfe]; have := hsl q hq; omega))
  have hx2 : WordAt st2.data.dmem (fbOf m0 + BitVec.ofNat 64 32) (xOf m0) := by
    have := wordAt_of_write hm2 (r := 0) (o := 32) rfl (by decide) (v := .reg .rdx) hv2
    rwa [eval_reg, Env.ofMachine_regs, show st1.data.regs.get64 .rdx = _ from
      harg .rdx (by simp)] at this
  have hb02 : ∀ j < lanesBytes, st2.data.dmem.get? (aOf m0 + BitVec.ofNat 64 j) =
      m0.dmem.get? (aOf m0 + BitVec.ofNat 64 j) := fun j hj ↦ by
    unfold aOf
    rw [get?_of_frame hm2 hwf2 rfl (fun w hw ↦ ⟨(hw2 w hw).1, by have := (hw2 w hw).2.2; omega⟩)
        hS hF hlanes.2 hlanes.1.2 j hj,
      Env.ofMachine_mem0, get?_of_frame hm1 hwf0 rfl (fun w hw ↦ ⟨(hmem0 w hw).1,
        by have := (hmem0 w hw).2; omega⟩) hS hF hlanes.2 hlanes.1.2 j hj]
    rfl
  have hlanes0 : LanesAt m0 st2.data.dmem (lanesAt m0 0) := by
    intro j hj
    have hm := NativeRustcVm.ewAt_of_mapped (d := m0.dmem) (a := aOf m0 + BitVec.ofNat 64 (16 * j))
      fun i hi ↦ by rw [addr_add]; exact hlanes.1.1 _ (by show _ < 1024; omega)
    intro i hi
    rw [NativeRustcVm.length_ewBytes] at hi
    rw [addr_add, hb02 _ (by show _ < 1024; omega), ← addr_add]
    exact hm i (by rw [NativeRustcVm.length_ewBytes]; exact hi)
  have hrbx2 : reg st2.data .rbx = reg m0 .rsi := (hm2.regs .rbx _ rfl).trans (harg .rsi (by simp))
  have hr142 : reg st2.data .r14 = aOf m0 := (hm2.regs .r14 _ rfl).trans (harg .rdi (by simp))
  have hrcx2 : reg st2.data .rcx = rpOf m0 :=
    (Match.reg_eq (r := .rcx) hfr1.mid_match hm2 rfl rfl).trans (harg .rcx (by simp))
  have hr82 : reg st2.data .r8 = reg m0 .r8 :=
    (Match.reg_eq (r := .r8) hfr1.mid_match hm2 rfl rfl).trans (harg .r8 (by simp))
  have hRn : rnOf m0 = (reg m0 .r8).toNat := rfl
  simp only [PcOk] at hpc2
  rw [eval_test, eval_reg, Env.ofMachine_regs, show st1.data.regs.get64 .r8 = _ from
    harg .r8 (by simp), bv_beq_toNat, BitVec.toNat_ofNat] at hpc2
  obtain ⟨hT, hF2⟩ := Arrays.pc_cond hpc2
  by_cases h0 : rnOf m0 = 0
  · refine finish hp hpre ((hT (by rw [decide_eq_true_eq]; rw [← hRn, h0])).trans
      (hp.label NativeRustcVmX64.Vm.FoldRow.label_8_at)) ⟨hfr2, hr142, ?_, ?_⟩
    · rw [hrbx2, h0, Nat.shiftRight_zero]
      show reg m0 .rsi = BitVec.ofNat 64 (reg m0 .rsi).toNat
      simp
    · rw [h0]; exact hlanes0
  -- `b1`: the rounds' end
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b1Offset) := hF2 (by rw [decide_eq_true_eq]; omega)
  have hwf3 := hfr2.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at (hb1 hp) run_b1 hwf3 (by intro l h; cases h) hpc2' hfr2.mid_match
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hk3, hw3, hv3⟩ := after_eq run_b1 ▸ b1_write
  have hfr3 : Fr m0 st3.data := hfr2.of_write hfr2.mid_match hm3 hwf3 rfl hk3 (r := 0) rfl
    (len := 32) (by omega) (fun w hw ↦ ⟨(hw3 w hw).1, (hw3 w hw).2.2⟩)
    (fun p h ↦ .inr (inRange_frame hS hF (by omega) h))
    (fun q hq i hi ↦ by
      rw [addr_add]
      exact Arrays.not_inRange_above (by have := hsl q hq; omega)
        (by rw [hfe]; have := hsl q hq; omega))
  have hed : WordAt st3.data.dmem (fbOf m0 + BitVec.ofNat 64 24)
      (.ofBitVec (rpOf m0 + BitVec.ofNat 64 (32 * rnOf m0))) := by
    have := wordAt_of_write hm3 (r := 0) (o := 24) rfl (by decide)
      (v := .bin .add .W64 (.reg .rcx) (.bin .shl .W64 (.reg .r8) (.lit 5))) hv3
    rw [eval_add, eval_shl_lit _ (by decide), eval_reg, eval_reg, Env.ofMachine_regs,
      Env.ofMachine_regs, show st2.data.regs.get64 .rcx = _ from hrcx2,
      show st2.data.regs.get64 .r8 = _ from hr82] at this
    rw [show reg m0 .r8 <<< 5 = BitVec.ofNat 64 (32 * rnOf m0) from by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      unfold rnOf
      omega] at this
    exact this
  have hkw3 : ∀ {o : Nat} {w : UInt64}, 32 ≤ o → o + 8 ≤ 104 →
      WordAt st2.data.dmem (fbOf m0 + BitVec.ofNat 64 o) w →
      WordAt st3.data.dmem (fbOf m0 + BitVec.ofNat 64 o) w := fun h32 ho h ↦
    bytesAt_block hm3 hwf3 rfl (by rw [NativeRustcVm.length_wordBytes]; omega)
      (fun w hw ↦ ⟨(hw3 w hw).1, .inl (by have := (hw3 w hw).2.2; omega)⟩) h
  have hlanes3 : LanesAt m0 st3.data.dmem (lanesAt m0 0) :=
    lanes_stack hS hlanes hlanes0 (Match.sameOutside hm3 hwf3) fun p h ↦
      inRange_frame hS hF (L := 32) (by omega)
        (Arrays.written_region0 rfl hwf3 (k := 32) (by omega)
          (fun w hw ↦ ⟨(hw3 w hw).1, (hw3 w hw).2.2⟩) h)
  have hI0 : RInv m0 0 st3.data := by
    refine ⟨⟨hfr3, hkw3 (by omega) (by omega) hx2, hed,
      (Match.reg_eq (r := .r14) hfr2.mid_match hm3 rfl rfl).trans hr142⟩, by omega, ?_, ?_,
      hlanes3⟩
    · refine (hm3.regs .rcx _ rfl).trans ?_
      show reg st2.data .rcx = _
      rw [hrcx2]; simp
    · refine (Match.reg_eq (r := .rbx) hfr2.mid_match hm3 rfl rfl).trans ?_
      show reg st2.data .rbx = _
      rw [hrbx2, Nat.shiftRight_zero]
      show reg m0 .rsi = BitVec.ofNat 64 (reg m0 .rsi).toNat
      simp
  simp only [PcOk] at hpc3
  exact (rounds hp hkmul hmul hpre (hpc3.trans (hp.label NativeRustcVmX64.Vm.FoldRow.label_3_at)) hI0).bind
    fun s ⟨hpc, hD⟩ ↦ finish hp hpre hpc hD

end

end NativeRustcVmX64.Whir.FoldRow
