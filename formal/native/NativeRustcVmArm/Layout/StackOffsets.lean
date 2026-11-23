module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Code.Vm.InsertionSortOfStackOffsets.Names
public import NativeRustcVmArm.Code.Vm.Memset.Names
public import NativeRustcVmArm.Code.Vm.StackOffsets.Names
public import NativeRustcVmArm.Layout.StackOffsets.Loop

/-!
# `stack_offsets` on AArch64

**`stackOffsets_spec`**: rustc's `stack_offsets(sizes, offsets)`, placed anywhere in the program,
meets `StackOffsetsPre`/`StackOffsetsPost` given `memset`'s, `insertion_sort`'s and
`bit_length`'s contracts. `b0` returns `None` (`b1`) when `offsets` is shorter than `sizes`. Else
the prologue `b2` saves eight registers above the 1264-byte `order` array and zeroes it
(`memset`); `b3`-`b12` write `0, …, n - 1` into it (`init_spec`), `b13` sorts it
(`insertion_sort`: the model's `ord`), `b14` starts the main loop (`loop`), which places the
blocks along the order (`P`) or fails (`b21`, the blocks not fitting a `u64`). `b22` takes the
total's `bit_length(total - 1)` (`log2Ceil`), `b23` returns it with the offsets.
-/

namespace NativeRustcVmArm.Layout.StackOffsets

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.StackOffsets
open NativeVm.Model NativeRustcVm.Layout
open NativeRustcVmArm.Arrays (regs_eq_of savedRegs mem_savedRegs)
open NativeRustcVm (WordAt WordsAt wordOf)

public section

theorem readable_kept {m0 st : MachineData} {a : BitVec 64} {len : Nat} (h : Readable m0 a len)
    (hk : Kept m0.dmem st.dmem) : Readable st a len :=
  ⟨fun i hi ↦ hk _ (h.1 i hi), h.2⟩

theorem inRange_zero {a p : BitVec 64} : ¬InRange a 0 p := by unfold InRange; omega

/-- Bytes of the frame at or past `lo` are not among its first `lo`. -/
theorem not_in_low {m0 : MachineData} (hS : StackOk m0 1328) {lo c : Nat} (hc : lo ≤ c)
    (hc' : c < 1328) : ¬InRange (fb m0) lo (fb m0 + BitVec.ofNat 64 c) := by
  have := NativeRustcVm.not_inRange_sub (fb_noWrap hS) (o := 0) (m := lo) (i := c) (by omega) hc'
    (Or.inr (by omega))
  rwa [NativeRustcVm.addr_add_zero] at this

/-- The slots are past the order array. -/
theorem slots_not_low {m0 : MachineData} (hS : StackOk m0 1328) {lo : Nat} (hlo : lo ≤ 1264) :
    ∀ q ∈ slots, ∀ i < 8, ¬InRange (fb m0) lo (fbase m0 1328 + BitVec.ofNat 64 q.1 +
      BitVec.ofNat 64 i) := fun q hq i hi ↦ by
  obtain ⟨h1, h2⟩ := slots_bounds q hq
  rw [NativeRustcVm.addr_add]
  exact not_in_low hS (by omega) (by omega)

theorem in_frame {m0 : MachineData} (hS : StackOk m0 1328) {lo : Nat} (hlo : lo ≤ 1328)
    {p : BitVec 64} (h : InRange (fb m0) lo p) : InRange (stackBelow m0 1328) 1328 p :=
  frame_in_stack hS (Nat.le_refl _) (by unfold InRange at h ⊢; exact Nat.lt_of_lt_of_le h hlo)

variable [Host] {k : Nat}

/-- `stack_offsets`' postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ StackOffsetsPost m0 s.data

/-- **An epilogue** (`b21`, `b23`) from a frame: `cont` with the registers restored, memory
kept. -/
theorem epilogue {m0 : MachineData} (hS : StackOk m0 1328) {ds : List Directive} {kk : Nat}
    {S1 : SState} {x : Exit} (hk : ds.IsInfixAt Host.prog kk) (hx : exec ds exitS = some (S1, x))
    (hr : Arrays.restores slots 1328 S1 = true ∧ S1.mem = []) {st : MachineState}
    (hpc : st.pc = Host.addrOf kk) (hb : Fr m0 st.data) {R : MachineState → Prop}
    (cont : ∀ st', Match (Env.ofMachine st.data [(fb m0, 1328)]) S1 st'.data →
      PcOk (Env.ofMachine st.data [(fb m0, 1328)]) x (Host.addrOf (kk + ds.length)) st' →
      Saved m0 st'.data → st'.data.regs.X30 = m0.regs.X30 → st'.data.dmem = st.data.dmem →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  obtain ⟨hwf, hm⟩ := Fr.exit_match hS hb
  refine exec_at hk hx hwf hpc hm fun st' hm' hpc' ↦ ?_
  obtain ⟨hsv, hx30⟩ := Frame.saved hb hm' hwf (by simp [slots]) hr.1
  exact cont st' hm' hpc' hsv hx30 (hm'.dmem_eq hwf hr.2)

/-- **A failure** at `b21`: `None`. -/
theorem fail (hp : Placed code k) {m0 : MachineData} (hpre : StackOffsetsPre m0)
    {st : MachineState} (h : Fail k m0 st) : Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hpc, hfr, hfit⟩ := h
  refine epilogue hpre.1 (infix_of b21_in_code (by simp [b21]) hp) run_b21 b21_restores hpc hfr
    fun st' hm hpc' hsv hx30 hd ↦ .done _ ⟨?_, ?_, fun p hp' ↦ by rw [hd]; exact hfr.same p hp',
      hsv⟩
  · simp only [PcOk] at hpc'
    exact hpc'.trans (by simp only [retOf, hx30])
  · split
    · rename_i h; exact absurd h.2 hfit
    · apply UInt64.toBitVec_inj.mp
      show (st'.data.regs.getXReg .X0).toBitVec = _
      rw [hm.regs .X0 _ rfl]
      rfl

/-- **The end** `b22`, `b23`: `bit_length(total - 1)` and the offsets returned. -/
theorem finish (hp : Placed code k)
    (hbl : Spec (label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost) {m0 : MachineData}
    (hpre : StackOffsetsPre m0) (hcap : n m0 ≤ cap m0) {st : MachineState} (h : End k m0 st) :
    Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hpc, hL⟩ := h
  have hS : StackOk m0 1328 := hpre.1
  refine run_regs hS (infix_of b22_in_code (by simp [b22]) hp) run_b22
    (after_eq run_b22 ▸ b22_keeps) hpc hL.fr fun st1 hm1 hpc1 hfr1 hd1 ↦ ?_
  have e8 : (st.data.regs.getXReg .X8).toBitVec.toNat = (P m0 (n m0)).2 := hL.x8
  have h0 : st1.data.regs.X0.toNat = (P m0 (n m0)).2 - 1 := by
    show (st1.data.regs.getXReg .X0).toBitVec.toNat = _
    rw [hm1.regs .X0 _ rfl]
    simp only [Sym.eval, SBool.eval, Env.ofMachine_regs]
    have hcd := ult_apply e8 (lit_toNat (c := 1) (by decide))
    by_cases hc : CmpOp.apply .ult .W64 (st.data.regs.getXReg .X8).toBitVec
      (BitVec.ofNat 64 1) = true
    · simp only [hc, ↓reduceIte]
      rw [hcd] at hc
      have := of_decide_eq_true hc
      rw [lit_toNat (by decide)]
      omega
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      rw [hcd] at hc
      have : ¬(P m0 (n m0)).2 < 1 := fun h ↦ by
        rw [decide_eq_true h] at hc; exact absurd hc (by decide)
      rw [sub_apply (by omega), e8]
  simp only [NativeRustcVmArm.Vm.StackOffsets.b22_length, NativeRustcVmArm.Vm.StackOffsets.b22Length] at hpc1
  refine call_then hpc1 hbl trivial fun st2 hpc2 ⟨hx0, hsame, hsv⟩ ↦ ?_
  have hd2 : ∀ p, st2.data.dmem.get? p = st1.data.dmem.get? p := fun p ↦
    hsame p (by simp [bitLengthStack, inRange_zero])
  have hfr2 : Fr m0 st2.data := Frame.call hfr1 hsame hsv
    (fun p h ↦ absurd h (by simp [bitLengthStack, inRange_zero]))
    (fun q _ i _ h ↦ absurd h (by simp [bitLengthStack, inRange_zero]))
  refine epilogue hS (infix_of b23_in_code (by simp [b23]) hp) run_b23 b23_restores hpc2 hfr2
    fun st3 hm3 hpc3 hsv3 hx30 hd3 ↦ .done _ ⟨?_, ?_, fun p hp' ↦ by
      rw [hd3]; exact hfr2.same p hp', hsv3⟩
  · simp only [PcOk] at hpc3
    exact hpc3.trans (by simp only [retOf, hx30])
  · have hfit : n m0 ≤ cap m0 ∧ OffsetsFit (sizes m0) := ⟨hcap, fit_end (by
      have := (st.data.regs.getXReg .X8).toBitVec.isLt
      omega)⟩
    simp only [hfit, and_self, ↓reduceIte]
    rw [stackOffsets_eq]
    refine ⟨?_, ?_, ?_⟩
    · apply UInt64.toBitVec_inj.mp
      show (st3.data.regs.getXReg .X0).toBitVec = _
      rw [hm3.regs .X0 _ rfl]
      rfl
    · show (st3.data.regs.getXReg .X1).toBitVec.toNat = _
      rw [hm3.regs .X1 _ rfl]
      show st2.data.regs.X0.toNat = _
      rw [hx0, h0]
      rfl
    · rw [hd3]
      exact OutAt.words fun i hi ↦ Arrays.bytesAt_congr (hL.out i hi) fun t _ ↦ by
        rw [hd2, hd1]

/-- `b13`, `b14`: the order sorted, the main loop's head. -/
theorem sorted (hp : Placed code k)
    (hsort : Spec (label NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.entryLabel) InsertionSortPre InsertionSortPost)
    {m0 : MachineData} (hpre : StackOffsetsPre m0) {st : MachineState} (h : At13 k m0 st) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b17Offset) ∧ Loop m0 0 s.data) st := by
  obtain ⟨hpc, hR⟩ := h
  have hS : StackOk m0 1328 := hpre.1
  have hn : n m0 ≤ 158 := hpre.2.1
  have hrs := hpre.2.2.1
  have hsoff : OffStack m0 m0.regs.X0.toBitVec (8 * m0.regs.X1.toNat) 1328 := hpre.2.2.2.1
  have hro := hpre.2.2.2.2.1
  have hooff : Apart (out m0) (8 * cap m0) (fb m0) 1328 := hpre.2.2.2.2.2.1
  have hap := hpre.2.2.2.2.2.2
  have hnd : n m0 = m0.regs.X1.toNat := rfl
  have hfbsb : stackBelow m0 1328 = fb m0 := rfl
  refine run_regs hS (infix_of b13_in_code (by simp [b13]) hp) run_b13
    (after_eq run_b13 ▸ b13_keeps) hpc hR.init.fr fun st1 hm1 hpc1 hfr1 hd1 ↦ ?_
  have he1 := regs_eq_of (match_nil _) hm1 [.X0, .X1, .X2, .X3, .X19, .X20, .X21, .X22, .X23,
    .X24] rfl
  have x0 : st1.data.regs.X0.toBitVec = fb m0 := by
    rw [show st1.data.regs.X0 = st.data.regs.X0 from he1 .X0 (by simp)]; exact hR.x0
  have x1 : st1.data.regs.X1.toNat = n m0 := by
    rw [show st1.data.regs.X1 = st.data.regs.X1 from he1 .X1 (by simp)]; exact hR.x1
  have x2 : st1.data.regs.X2 = m0.regs.X0 := (he1 .X2 (by simp)).trans hR.x2
  have x3 : st1.data.regs.X3.toNat = n m0 := by
    rw [show st1.data.regs.X3 = st.data.regs.X3 from he1 .X3 (by simp)]; exact hR.x3
  have hR1 : Regs m0 st1.data := hR.init.regs.of fun r hr ↦ he1 r (by
    simp only [regsList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp)
  have hpre1 : InsertionSortPre st1.data := by
    refine ⟨?_, ?_, ?_⟩
    · rw [x0, x1]
      have := frame_readable hS (Nat.le_refl _) hfr1 (o := 0) (k := 8 * n m0) (by omega)
      rwa [NativeRustcVm.addr_add_zero] at this
    · rw [x2, x3]
      exact readable_kept hrs hfr1.kept
    · rw [x0, x1, x2, x3]
      unfold OffStack at hsoff
      rw [hfbsb] at hsoff
      unfold Apart at hsoff ⊢
      omega
  simp only [NativeRustcVmArm.Vm.StackOffsets.b13_length, NativeRustcVmArm.Vm.StackOffsets.b13Length] at hpc1
  refine call_then hpc1 hsort hpre1 fun st2 hpc2 ⟨hw2, hsame2, hsv2⟩ ↦ ?_
  have hsizes : natsOf st1.data st1.data.regs.X2 st1.data.regs.X3.toNat = sizes m0 := by
    rw [x2, x3]
    simp only [natsOf, sizes]
    rw [NativeRustcVm.wordsOf_congr fun t ht ↦ ?_]
    exact Arrays.same_of_apart hfr1.same hS hrs.2 hsoff hap hro.2 _ (by omega)
  have hord : natsOf st1.data st1.data.regs.X0 st1.data.regs.X1.toNat = Array.range (n m0) := by
    rw [x1]
    exact natsOf_ords x0 (by omega) (hd1 ▸ hR.init.ords)
  rw [hsizes, hord, x0] at hw2
  have hfr2 : Fr m0 st2.data := Frame.call hfr1 hsame2 hsv2
    (fun p h ↦ by
      rcases h with h | h
      · rw [x0, x1] at h; exact Or.inr (in_frame hS (by omega) h)
      · exact absurd h (by simp [insertionSortStack, inRange_zero]))
    (fun q hq i hi h ↦ by
      rcases h with h | h
      · rw [x0, x1] at h; exact slots_not_low hS (by omega) q hq i hi h
      · exact absurd h (by simp [insertionSortStack, inRange_zero]))
  have hR2 : Regs m0 st2.data := hR1.call hsv2
  refine run_regs hS (infix_of b14_in_code (by simp [b14]) hp) run_b14
    (after_eq run_b14 ▸ b14_keeps) hpc2 hfr2 fun st3 hm3 hpc3 hfr3 hd3 ↦ ?_
  have he3 := regs_eq_of (match_nil _) hm3 (.X23 :: regsList) rfl
  simp only [PcOk] at hpc3
  refine .done _ ⟨hpc3.trans (lbl_15 hp), hfr3, hR2.of fun r hr ↦ he3 r (by simp [hr]),
    Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show st3.data.regs.X23 = st.data.regs.X23 from (he3 .X23 (by simp)).trans
      ((hsv2.1 .X23 rfl).trans (he1 .X23 (by simp)))]
    rw [hR.init.x23, Nat.sub_zero]
  · show (st3.data.regs.getXReg .X9).toBitVec = _
    rw [hm3.regs .X9 _ rfl, NativeRustcVm.addr_add_zero]
    exact hfr2.sp
  · show (st3.data.regs.getXReg .X8).toBitVec.toNat = _
    rw [hm3.regs .X8 _ rfl, P_zero]
    rfl
  · show (st3.data.regs.getXReg .X10).toBitVec.toNat = _
    rw [hm3.regs .X10 _ rfl]
    rfl
  · rw [hd3]
    exact hw2
  · exact outAt_zero m0 _

/-- **`stack_offsets` meets its contract.** -/
theorem stackOffsets_spec (hp : Placed code k)
    (hmemset : Spec (label NativeRustcVmArm.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    (hsort : Spec (label NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.entryLabel) InsertionSortPre InsertionSortPost)
    (hbl : Spec (label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost) :
    Spec (label NativeRustcVmArm.Vm.StackOffsets.entryLabel) StackOffsetsPre StackOffsetsPost := by
  intro m0 hpre
  have hS : StackOk m0 1328 := hpre.1
  have hn : n m0 ≤ 158 := hpre.2.1
  have hcapd : cap m0 = m0.regs.X3.toNat := rfl
  have hnd : n m0 = m0.regs.X1.toNat := rfl
  rw [lbl_entry hp]
  obtain ⟨hwf, hm⟩ := Arrays.entry_match (F := 1328) hS (Nat.le_refl _) rfl
  have hm' : Match (Arrays.frameEnv m0 m0 1328) entryS m0 := hm
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf hm' fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.StackOffsets.b0_length, NativeRustcVmArm.Vm.StackOffsets.b0Length] at hpc1
  obtain ⟨hy, hno⟩ := pc_of (P := ¬cap m0 < n m0) hpc1 (by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    rw [ult_apply (show (m0.regs.getXReg .X3).toBitVec.toNat = cap m0 from rfl)
      (show (m0.regs.getXReg .X1).toBitVec.toNat = n m0 from rfl), decide_not])
  by_cases hcap : cap m0 < n m0
  · -- `b1`: `None`
    have hb1 := b1_ret
    rw [after_eq run_b0, after_eq (exec_after run_b0 run_b1)] at hb1
    obtain ⟨hregs, hsp, hmem⟩ := hb1
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) (exec_after run_b0 run_b1) hwf
      (hno (by omega)) hm1 fun st2 hm2 hpc2 ↦ .done _ ?_
    have hr : ∀ r ∈ savedRegs, st2.data.regs.getXReg r = m0.regs.getXReg r := by
      intro r hr'
      apply UInt64.toBitVec_inj.mp
      rw [hm2.regs r _ (beq_iff_eq.mp (List.all_eq_true.mp hregs r hr'))]
      rfl
    have hd : st2.data.dmem = m0.dmem := hm2.dmem_eq hwf hmem
    refine ⟨?_, ?_, fun p _ ↦ by rw [hd], ⟨fun r hc ↦ hr r (mem_savedRegs hc), ?_,
      fun p hp' ↦ hm2.kept hwf p hp'⟩⟩
    · simp only [PcOk] at hpc2
      rw [hpc2]
      simp only [retOf]
      rw [show st2.data.regs.X30 = m0.regs.X30 from hr .X30 (by simp [savedRegs])]
    · split
      · rename_i h; exact absurd h.1 (by omega)
      · apply UInt64.toBitVec_inj.mp
        show (st2.data.regs.getXReg .X0).toBitVec = _
        rw [hm2.regs .X0 _ rfl]
        rfl
    · apply UInt64.toBitVec_inj.mp
      rw [hm2.sp, hsp]
      simp only [Sym.eval, Arrays.frameEnv, Env.base_ofMachine_eq, List.getElem?_cons_zero,
        Option.map_some, Option.getD_some]
      rw [show BitVec.ofInt 64 1328 = BitVec.ofNat 64 1328 from rfl, BitVec.sub_add_cancel]
  · have hcap' : n m0 ≤ cap m0 := by omega
    -- `b2`: the prologue, `memset`
    have hb2 := b2_frame
    rw [after_eq run_b0, after_eq (exec_after run_b0 run_b2)] at hb2
    obtain ⟨hsp, hw, hmem, hregs⟩ := hb2
    refine exec_at (infix_of b2_in_code (by simp [b2]) hp) (exec_after run_b0 run_b2) hwf
      ((hy hcap).trans (lbl_2 hp)) hm1 fun st2 hm2 hpc2 ↦ ?_
    have hfr2 : Fr m0 st2.data := Frame.of_entry (rs := []) hS (Nat.le_refl _) hm2 hwf hsp hw
      hregs hmem
    have hx0 : st2.data.regs.X0.toBitVec = fb m0 := by
      show (st2.data.regs.getXReg .X0).toBitVec = _
      rw [hm2.regs .X0 _ rfl]
      simp [Sym.eval]
    have hx2 : st2.data.regs.X2.toNat = 1264 := by
      show (st2.data.regs.getXReg .X2).toBitVec.toNat = _
      rw [hm2.regs .X2 _ rfl]
      rfl
    have hpre2 : MemsetPre st2.data := by
      unfold MemsetPre
      rw [hx0, hx2]
      have := frame_readable hS (Nat.le_refl _) hfr2 (o := 0) (k := 1264) (by omega)
      rw [NativeRustcVm.addr_add_zero] at this
      exact this
    simp only [NativeRustcVmArm.Vm.StackOffsets.b2_length, NativeRustcVmArm.Vm.StackOffsets.b2Length] at hpc2
    refine call_then hpc2 hmemset hpre2 fun st3 hpc3 ⟨_, _, hsame3, hsv3⟩ ↦ ?_
    rw [hx0, hx2] at hsame3
    have hfr3 : Fr m0 st3.data := Frame.call hfr2 hsame3 hsv3
      (fun p h ↦ Or.inr (in_frame hS (by omega) h)) (slots_not_low hS (by omega))
    have hreg : ∀ r, calleeSaved r = true → (st3.data.regs.getXReg r).toBitVec =
        (st2.data.regs.getXReg r).toBitVec := fun r hr ↦ congrArg UInt64.toBitVec (hsv3.1 r hr)
    have hR3 : Regs m0 st3.data := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · apply UInt64.toBitVec_inj.mp
        rw [show st3.data.regs.X19 = st3.data.regs.getXReg .X19 from rfl, hreg .X19 rfl,
          hm2.regs .X19 _ rfl]
        rfl
      · apply UInt64.toBitVec_inj.mp
        rw [show st3.data.regs.X20 = st3.data.regs.getXReg .X20 from rfl, hreg .X20 rfl,
          hm2.regs .X20 _ rfl]
        rfl
      · apply UInt64.toBitVec_inj.mp
        rw [show st3.data.regs.X21 = st3.data.regs.getXReg .X21 from rfl, hreg .X21 rfl,
          hm2.regs .X21 _ rfl]
        rfl
      · apply UInt64.toBitVec_inj.mp
        rw [show st3.data.regs.X22 = st3.data.regs.getXReg .X22 from rfl, hreg .X22 rfl,
          hm2.regs .X22 _ rfl]
        rfl
      · rw [show st3.data.regs.X24 = st3.data.regs.getXReg .X24 from rfl, hreg .X24 rfl,
          hm2.regs .X24 _ rfl]
        simp [Sym.eval]
    refine Eventually.bind (init_spec hp hS hn hpc3 hfr3 hR3) fun s4 h4 ↦ ?_
    refine Eventually.bind (sorted hp hsort hpre h4) fun s5 ⟨hpc5, hL5⟩ ↦ ?_
    refine Eventually.bind (loop hp hpre hcap' hpc5 hL5) fun s6 h6 ↦ ?_
    rcases h6 with h6 | h6
    · exact fail hp hpre h6
    · exact finish hp hbl hpre hcap' h6

end

end NativeRustcVmArm.Layout.StackOffsets
