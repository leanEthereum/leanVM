module

public import NativeRustcVmX64.Whir.SubspaceAtTable.Loop
public import NativeRustcVmX64.Code.Vm.Kmul.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.Memset.Names
public import NativeRustcVmX64.Code.Vm.SubspaceAtTable.Names

/-!
# `subspace_at_table` on x86-64

**`subspaceAtTable_spec`**: `b0a` pushes the callee-saved registers and opens the 280-byte frame;
`b0b` keeps the table (R15), the point (R12), the count (RBX), spills the output pointer and
zeroes the `what` buffer's items (`memset`). `b1` spills the count and, with no table entry, goes
to the end; else `b2` starts the loop (`SubspaceAtTable.step`, by `Sym.loop`). `b7` stores the
count in the buffer's `len` and copies the buffer to the output (`memcpy`), `b8` returns. The
output holds `subspaceAtTable`.
-/

namespace NativeRustcVmX64.Whir.SubspaceAtTable

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SubspaceAtTable NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region wordOf)
open NativeRustcVmX64.Field (midS frameS frameEnv frame_wf match_frame)
open NativeRustcVmX64.Arrays (stackOk_mono load8_eq wordAt_of_write eval_reg eval_lit eval_add
  eval_load eval_test)

public section

theorem eight_mul (x : BitVec 64) :
    x * BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem ptr_eval [Labels] {m0 st : MachineData} {F : Nat} {vars : Nat → BitVec 64}
    {ret : BitVec 64} (o : Nat) :
    (Sym.ptr 0 (o : Int)).eval (frameEnv m0 st F vars ret) = stackBelow m0 F + BitVec.ofNat 64 o :=
  by show stackBelow m0 F + BitVec.ofInt 64 (o : Int) = _; rw [ofInt_ofNat]

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0a.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceAtTable.b0Offset) ∧
    b0b.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceAtTable.b0Offset + b0a.length) := by
  have h := b0_in_code.trans hp.1 (by simp [b0])
  rw [← List.take_append_drop 8 b0] at h
  exact h.append
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceAtTable.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceAtTable.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceAtTable.b7Offset) :=
  b7_in_code.trans hp.1 (by simp [b7])
theorem hb8 (hp : Placed code k) : b8.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceAtTable.b8Offset) :=
  b8_in_code.trans hp.1 (by simp [b8])

/-- `subspace_at_table`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧ SubspaceAtTablePost m0 s.data

/-- **After the loop**: the count, the copy, the epilogue. -/
theorem finish (hp : Placed code k) (hmemcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {m0 : MachineData} (hpre : SubspaceAtTablePre m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b7Offset)) (hD : Done m0 st.data) :
    Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hS, hn31, htin, houtin, hap, hgot⟩ := hpre
  have hF : 336 ≤ subspaceAtTableStack := by decide
  have hn : nOf m0 ≤ 31 := hn31
  have hwb : whatBytes = 256 := rfl
  have hout := out_one houtin
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hS1 := hS.1
  have hS2 := hS.2.1
  have hfr := hD.fr
  have hlist := subspaceAtTable_size (tbOf m0) (xOf m0)
  rw [tbOf_size] at hlist
  have hwlen : ((subspaceAtTable (tbOf m0) (xOf m0)).toList.flatMap
      NativeRustcVm.wordBytes).length = 8 * nOf m0 := by
    rw [NativeRustcVm.length_wordsBytes, Array.length_toList, hlist]
  -- `b7`: the count, `memcpy`
  have hwf7 := hfr.got_wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b8Offset)).toBitVec) hS hF hgot (by simp : "memcpy" ∈ _)
  have hm7 := hfr.got_match (l := "memcpy") (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b8Offset)).toBitVec)
    (fun i hi => hfr.got_byte hS hgot
    (by
      intro ar har
      simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with rfl | rfl
      · exact htin.1.2
      · exact houtin.1.2)
    (by intro r hr; simp only [outsOf, List.mem_singleton] at hr; subst r; simp)
    (by simp) hi)
  refine exec_at (hb7 hp) run_b7 hwf7 (fun _ _ ↦ rfl) hpc hm7 fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hk1, hsp1, hw1⟩ := after_eq run_b7 ▸ b7_call
  have hrsp1 := rsp_call hm1 hsp1
  have hcount : NativeRustcVm.WordAt st1.data.dmem (stackBelow m0 336 + BitVec.ofNat 64 32)
      (.ofBitVec (reg m0 .rdx)) := by
    have := wordAt_of_write hm1 (r := 0) (o := 32) rfl (by decide) (v := .load 0 16 8)
      (by decide)
    rwa [eval_load, load8_eq, show (gotEnv m0 st.data 336 "memcpy" (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b8Offset)).toBitVec).base 0 = stackBelow m0 336 from rfl,
      gotEnv_mem0, NativeRustcVm.wordOf_of_wordAt (show NativeRustcVm.WordAt st.data.dmem
        (stackBelow m0 336 + BitVec.ofNat 64 16) _ from hD.cnt), UInt64.ofBitVec_toBitVec] at this
  have hwhat1 : NativeRustcVm.WordsAt st1.data.dmem (stackBelow m0 336 + BitVec.ofNat 64 40)
      (subspaceAtTable (tbOf m0) (xOf m0)).toList :=
    bytesAt_block hm1 hwf7 rfl (by rw [hwlen]; omega)
      (fun w hw ↦ ⟨(hw1 w hw).1, .inl (hw1 w hw).2.2⟩) hD.what
  have hbuf : NativeRustcVm.WordsAt st1.data.dmem (stackBelow m0 336 + BitVec.ofNat 64 32)
      (.ofBitVec (reg m0 .rdx) :: (subspaceAtTable (tbOf m0) (xOf m0)).toList) :=
    NativeRustcVm.wordsAt_cons_iff.mpr ⟨hcount, by rw [addr_add]; exact hwhat1⟩
  have hrdi : reg st1.data .rdi = reg m0 .rdi := by
    refine (hm1.regs .rdi _ rfl).trans ?_
    rw [eval_load, load8_eq]
    exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_of_wordAt (show NativeRustcVm.WordAt
      st.data.dmem (stackBelow m0 336 + BitVec.ofNat 64 24) _ from hD.out))
  have hrsi : reg st1.data .rsi = stackBelow m0 336 + BitVec.ofNat 64 32 :=
    (hm1.regs .rsi _ rfl).trans (gotEnv_ptr 32)
  have hrdx : (reg st1.data .rdx).toNat = 256 := by
    rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ rfl]; rfl
  have hfb : (stackBelow m0 336).toNat = (rspOf m0).toNat - 336 := hfe
  have hkept1 : Kept m0.dmem st1.data.dmem := fun p h ↦ hm1.kept hwf7 p (hfr.kept p h)
  have hoff := houtin.2
  have hnwo := houtin.1.2
  unfold OffStack Apart at hoff
  unfold NoWrap at hnwo
  rw [Arrays.stackBelow_toNat hS1] at hoff
  rw [hwb] at hoff hnwo
  have h32 : (stackBelow m0 336 + BitVec.ofNat 64 32).toNat = (rspOf m0).toNat - 336 + 32 := by
    rw [toNat_add_ofNat _ _ (by omega), hfb]
  have hpre1 : MemcpyPre st1.data := by
    unfold MemcpyPre
    simp only [hrdi, hrsi, hrdx]
    refine ⟨stackOk_callee hS hkept1 hrsp1 (by omega), fun i hi ↦ hkept1 _ (houtin.1.1 i hi),
      fun i hi ↦ ?_, houtin.1.2, ?_, ?_, ?_⟩
    · rw [addr_add]; exact hkept1 _ (hfmap _ (by omega))
    · unfold NoWrap; rw [h32]; omega
    · unfold Apart; rw [h32]; omega
    · unfold Apart; rw [hrsp1, hfb]; omega
  refine Frame.call hmemcpy hfr hS (by decide : 336 + 0 ≤ subspaceAtTableStack) (L := 288)
    (by decide) slots_ok hout hwf7 hm7 hm1 hpc1 hk1 hsp1
    (fun w hw ↦ ⟨(hw1 w hw).1, by have := (hw1 w hw).2.2; omega⟩) hpre1
    (fun m' ⟨_, _, hso, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hso p fun h ↦ hp (.inl (by
      simp only [hrdi, hrdx] at h
      exact inAny_one (hwb ▸ h)))⟩)
    fun st2 hpc2 hfr2 ⟨_, hcopy, _, _⟩ ↦ ?_
  simp only [hrdi, hrsi, hrdx] at hcopy
  -- `b8`
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b8Offset) := hpc2
  have hwf8 := hfr2.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at (hb8 hp) run_b8 hwf8 (by intro l h; cases h) hpc2' hfr2.mid_match
    fun st3 hm3 hpc3 ↦ .done _ ?_
  obtain ⟨hpc', hrsp', hdm, hsaved⟩ := hfr2.done hS hF hout hm3 hpc3
    (after_eq run_b8 ▸ b8_restores).1 (after_eq run_b8 ▸ b8_restores).2
  refine ⟨hpc', hrsp', ?_, fun p hp ↦ by rw [hdm]; exact hfr2.same p hp, hsaved⟩
  -- the output
  have hlen8 : ((UInt64.ofBitVec (reg m0 .rdx) :: (subspaceAtTable (tbOf m0) (xOf m0)).toList).flatMap
      NativeRustcVm.wordBytes).length = 8 + 8 * nOf m0 := by
    rw [NativeRustcVm.length_wordsBytes, List.length_cons, Array.length_toList, hlist]; omega
  have hb := NativeRustcVm.BytesAt.take hcopy (8 + 8 * nOf m0)
  rw [bytesOf_take _ _ (by omega), ← hlen8, NativeRustcVmX64.bytesOf_eq hbuf] at hb
  have hw := NativeRustcVm.wordsAt_cons_iff.mp (show NativeRustcVm.WordsAt st3.data.dmem
    (reg m0 .rdi) _ from hdm ▸ hb)
  refine ⟨by rw [Array.length_toList]; exact hlist ▸ hn, ?_, hw.2⟩
  rw [Array.length_toList]
  show NativeRustcVm.WordAt _ _ (subspaceAtTable (tbOf m0) (xOf m0)).size.toUInt64
  rw [hlist, show (nOf m0).toUInt64 = UInt64.ofBitVec (reg m0 .rdx) from toUInt64_toNat _]
  exact hw.1

/-- **`subspace_at_table` meets its contract.** -/
theorem subspaceAtTable_spec (hp : Placed code k)
    (hkmul : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost)
    (hmemset : Spec (Labels.label NativeRustcVmX64.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.SubspaceAtTable.entryLabel) SubspaceAtTablePre SubspaceAtTablePost := by
  intro m0 hpre
  have hpre' := hpre
  obtain ⟨hS, hn31, htin, houtin, hap, hgot⟩ := hpre'
  have hF : 336 ≤ subspaceAtTableStack := by decide
  have hn : nOf m0 ≤ 31 := hn31
  have hnn : nOf m0 = (reg m0 .rdx).toNat := rfl
  have hout := out_one houtin
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hS1 := hS.1
  have hS2 := hS.2.1
  rw [show Labels.label NativeRustcVmX64.Vm.SubspaceAtTable.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b0Offset) from hp.label NativeRustcVmX64.Vm.SubspaceAtTable.entry_at]
  -- `b0a`: the prologue
  have hwf0 := frame_wf (m := m0) (vars := fun _ ↦ 0) (ret := 0) (stackOk_mono hS hF)
    fun _ h ↦ h
  refine exec_then (hb0 hp).1 run_b0a hwf0 (by intro l h; cases h) match_frame
    fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, show b0a.length = 8 from rfl] at hpc1
  obtain ⟨hw0, hregs0, hmem0, hsp0⟩ := after_eq run_b0a ▸ b0a_entry
  have hfr1 : Fr m0 st1.data := Frame.of_entry hS hF hm1 hsp0 hw0 hregs0 hmem0
  have harg : ∀ r ∈ [Reg64.rdi, .rsi, .rdx, .rcx], reg st1.data r = reg m0 r := fun r hr ↦
    hm1.regs r (.reg r) ((after_eq run_b0a ▸ b0a_args) r hr)
  -- `b0b`: the arguments, `memset`
  have hwf2 := hfr1.got_wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b1Offset)).toBitVec) hS hF hgot (by simp : "memset" ∈ _)
  have hm2start := hfr1.got_match (l := "memset") (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b1Offset)).toBitVec)
    (fun i hi => hfr1.got_byte hS hgot
    (by
      intro ar har
      simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with rfl | rfl
      · exact htin.1.2
      · exact houtin.1.2)
    (by intro r hr; simp only [outsOf, List.mem_singleton] at hr; subst r; simp)
    (by simp) hi)
  refine exec_at (hb0 hp).2 run_b0b hwf2 (fun _ _ ↦ rfl) hpc1 hm2start fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hk2, hsp2, hw2⟩ := after_eq run_b0b ▸ b0b_call
  have hrsp2 := rsp_call hm2 hsp2
  have hkept2 : Kept m0.dmem st2.data.dmem := fun p h ↦ hm2.kept hwf2 p (hfr1.kept p h)
  have hout2 : NativeRustcVm.WordAt st2.data.dmem (stackBelow m0 336 + BitVec.ofNat 64 24)
      (.ofBitVec (reg m0 .rdi)) := by
    have := wordAt_of_write hm2 (r := 0) (o := 24) rfl (by decide) (v := .reg .rdi) (by decide)
    rwa [eval_reg, gotEnv_regs, harg .rdi (by simp)] at this
  have hrdi2 : reg st2.data .rdi = stackBelow m0 336 + BitVec.ofNat 64 40 :=
    (hm2.regs .rdi _ rfl).trans (gotEnv_ptr 40)
  have hrdx2 : (reg st2.data .rdx).toNat = 248 := by
    rw [show reg st2.data .rdx = _ from hm2.regs .rdx _ rfl]; rfl
  have hfb : (stackBelow m0 336).toNat = (rspOf m0).toNat - 336 := hfe
  have h40 : (stackBelow m0 336 + BitVec.ofNat 64 40).toNat = (rspOf m0).toNat - 336 + 40 := by
    rw [toNat_add_ofNat _ _ (by omega), hfb]
  have hpre2 : MemsetPre st2.data := by
    unfold MemsetPre
    simp only [hrdi2, hrdx2]
    refine ⟨stackOk_callee hS hkept2 hrsp2 (by omega), fun i hi ↦ ?_, ?_, ?_⟩
    · rw [addr_add]; exact hkept2 _ (hfmap _ (by omega))
    · unfold NoWrap; rw [h40]; omega
    · unfold Apart; rw [hrsp2, hfb, h40]; omega
  refine Frame.call hmemset hfr1 hS (by decide : 336 + 0 ≤ subspaceAtTableStack) (L := 288)
    (by decide) slots_ok hout hwf2 hm2start hm2 hpc2 hk2 hsp2
    (fun w hw ↦ ⟨(hw2 w hw).1, by have := (hw2 w hw).2; omega⟩) hpre2
    (fun m' ⟨_, _, hso, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hso p fun h ↦ hp (.inr (.inl (by
      simp only [hrdi2, hrdx2] at h
      exact inRange_low_of hS hF (by omega) (by omega) h)))⟩)
    fun st3 hpc3 hfr3 ⟨_, _, hso3, hsv3⟩ ↦ ?_
  simp only [hrdi2, hrdx2] at hso3
  have hout3 : NativeRustcVm.WordAt st3.data.dmem (stackBelow m0 336 + BitVec.ofNat 64 24)
      (.ofBitVec (reg m0 .rdi)) :=
    NativeRustcVm.BytesAt.of_sameOutside hout2 hso3 fun j hj ↦ by
      rw [NativeRustcVm.length_wordBytes] at hj
      rw [addr_add, inRange_fb_iff hS hF (by omega) (by omega) (by omega)]
      omega
  have e3 : ∀ r ∈ [Reg64.rbx, .r12, .r15], reg st3.data r = reg m0 (match r with
      | .rbx => .rdx | .r12 => .rcx | _ => .rsi) := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hsv3.1 .rbx rfl).trans ((hm2.regs .rbx _ rfl).trans (harg .rdx (by simp)))
    · exact (hsv3.1 .r12 rfl).trans ((hm2.regs .r12 _ rfl).trans (harg .rcx (by simp)))
    · exact (hsv3.1 .r15 rfl).trans ((hm2.regs .r15 _ rfl).trans (harg .rsi (by simp)))
  -- `b1`: spill the count, test it
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b1Offset) := hpc3
  have hwf4 := hfr3.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at (hb1 hp) run_b1 hwf4 (by intro l h; cases h) hpc3' hfr3.mid_match
    fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hk4, hw4⟩ := after_eq run_b1 ▸ b1_write
  have hfr4 : Fr m0 st4.data := hfr3.of_write hfr3.mid_match hm4 hwf4 rfl hk4 (r := 0) rfl
    (len := 24) (by omega) (fun w hw ↦ ⟨(hw4 w hw).1, (hw4 w hw).2.2⟩)
    (fun p h ↦ .inr (inRange_frame hS hF (by omega) h))
    (fun q hq i hi ↦ by
      rw [addr_add]
      exact Arrays.not_inRange_above (by have := slots_ok q hq; omega)
        (by rw [hfb]; have := slots_ok q hq; omega))
  have hcnt4 : NativeRustcVm.WordAt st4.data.dmem (stackBelow m0 336 + BitVec.ofNat 64 16)
      (.ofBitVec (reg m0 .rdx)) := by
    have := wordAt_of_write hm4 (r := 0) (o := 16) rfl (by decide) (v := .reg .rbx) (by decide)
    rwa [eval_reg, Env.ofMachine_regs, show st3.data.regs.get64 .rbx = reg m0 .rdx from
      e3 .rbx (by simp)] at this
  have hout4 : NativeRustcVm.WordAt st4.data.dmem (stackBelow m0 336 + BitVec.ofNat 64 24)
      (.ofBitVec (reg m0 .rdi)) :=
    bytesAt_block hm4 hwf4 rfl (by rw [NativeRustcVm.length_wordBytes]; omega)
      (fun w hw ↦ ⟨(hw4 w hw).1, .inl (hw4 w hw).2.2⟩) hout3
  have r4 : ∀ r ∈ [Reg64.rbx, .r12, .r15], reg st4.data r = reg st3.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Match.reg_eq hfr3.mid_match hm4 rfl rfl
  simp only [PcOk] at hpc4
  rw [eval_test, eval_reg, Env.ofMachine_regs, show st3.data.regs.get64 .rbx = reg m0 .rdx from
    e3 .rbx (by simp)] at hpc4
  obtain ⟨hT, hF4⟩ := Arrays.pc_cond hpc4
  have hl3 : Labels.label NativeRustcVmX64.Vm.SubspaceAtTable.label_3 = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b7Offset) := hp.label NativeRustcVmX64.Vm.SubspaceAtTable.label_3_at
  by_cases hn0 : nOf m0 = 0
  · have hz : (reg m0 .rdx == BitVec.ofNat 64 0) = true := by
      rw [bv_beq_toNat]; simp [← hnn, hn0]
    refine finish hp hmemcpy hpre ((hT hz).trans hl3) ⟨hfr4, hcnt4, hout4, ?_⟩
    rw [show subspaceAtTable (tbOf m0) (xOf m0) = #[] from
      Array.eq_empty_of_size_eq_zero (by rw [subspaceAtTable_size, tbOf_size, hn0])]
    exact NativeRustcVm.wordsAt_nil _ _
  · have hz : ¬(reg m0 .rdx == BitVec.ofNat 64 0) = true := by
      rw [bv_beq_toNat]; simp only [decide_eq_true_eq, BitVec.toNat_ofNat]; omega
    have hpc4' : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b2Offset) := hF4 hz
    -- `b2`: the loop's registers
    have hwf5 := hfr4.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
    refine exec_at (hb2 hp) run_b2 hwf5 (by intro l h; cases h) hpc4' hfr4.mid_match
      fun st5 hm5 hpc5 ↦ ?_
    have hfr5 := hfr4.of_block hfr4.mid_match hm5 hwf5 rfl (after_eq run_b2 ▸ b2_keeps)
    have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq hwf5 rfl
    have hpc5' : st5.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b3Offset) := hpc5
    have hL16 : (frameEnv m0 st4.data 336 (fun _ ↦ 0) 0).load 0 16 8 = reg m0 .rdx := by
      rw [load8_eq]
      exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_of_wordAt hcnt4)
    have hI0 : Inv m0 0 st5.data := by
      refine ⟨hfr5, ?_, ?_, ?_, ?_, hd5 ▸ hcnt4, hd5 ▸ hout4, ?_⟩
      · refine (hm5.regs .rbx _ rfl).trans ?_
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, hL16]
        exact eight_mul _
      · refine (Match.reg_eq hfr4.mid_match hm5 rfl rfl).trans ?_
        refine (r4 .r12 (by simp)).trans ((e3 .r12 (by simp)).trans ?_)
        rw [atAfter_zero]
        rfl
      · exact (hm5.regs .r14 _ rfl).trans rfl
      · exact (Match.reg_eq hfr4.mid_match hm5 rfl rfl).trans
          ((r4 .r15 (by simp)).trans (e3 .r15 (by simp)))
      · rw [atAfter_zero]
        exact NativeRustcVm.wordsAt_nil _ _
    have hloop := Sym.loop (tr := step1 Host.exe)
      (Q := fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b7Offset) ∧ Done m0 s.data)
      (fun n s ↦ ∃ i, n = nOf m0 - i ∧ i < nOf m0 ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b3Offset) ∧
        Inv m0 i s.data)
      (fun n s ⟨i, hn', hi, hpc, hI⟩ ↦
        (step hp hkmul hpre hi hpc hI).mono fun s' h ↦ by
          rcases h with h | ⟨hpc', hI', hlt⟩
          · exact .inl h
          · exact .inr ⟨nOf m0 - (i + 1), by omega, i + 1, rfl, hlt, hpc', hI'⟩)
      (n := nOf m0) ⟨0, by omega, by omega, hpc5', hI0⟩
    exact hloop.bind fun s ⟨hpc, hD⟩ ↦ finish hp hmemcpy hpre hpc hD

end

end NativeRustcVmX64.Whir.SubspaceAtTable
