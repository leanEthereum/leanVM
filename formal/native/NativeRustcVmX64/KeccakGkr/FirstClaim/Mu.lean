module

public import NativeRustcVmX64.KeccakGkr.FirstClaim.Last
public import NativeRustcVmX64.Code.Vm.EqKernel.Names

/-!
# `first_claim`: the instance weights (x86-64)

`b9` keeps `last` in R13, RBP, zeroes `mu`'s `Buf<EW, 16>` at `64` and calls `eq_kernel` on
`inst`'s first `min |inst| 4` coordinates into its items at `72`; `b10` checks it succeeded
(`mu`, to `MDone`).
-/

namespace NativeRustcVmX64.KeccakGkr.FirstClaim

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.FirstClaim
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off inRange_iff' Mapped.keeps
  bytesAt_congr inRange_off_self Touch)
open NativeVm.Math.Keccak (bitW)

@[expose] public section

/-- **The instance weights computed**: their kernel at `72`, its size in RDX; `inst` in R14,
RBX; `last` in R13, RBP. -/
structure MDone (m0 : MachineData) (inst segment lanePoint output : Array EW)
    (st : MachineData) : Prop where
  body : Body m0 st
  w : ElemsAt st.dmem (wA m0) (bitW (eqKernel lanePoint)) 1600
  mu : NativeRustcVm.EWsAt st.dmem (off (fbA m0) 72) (eqKernel (inst.extract 0 4)).toList
  rdx : (reg st .rdx).toNat = (eqKernel (inst.extract 0 4)).size
  rbx : reg st .rbx = reg m0 .rdx
  r14 : reg st .r14 = reg m0 .rsi
  r13 : reg st .r13 = (lastOf segment lanePoint output).c0.toBitVec
  rbp : reg st .rbp = (lastOf segment lanePoint output).c1.toBitVec
  r12 : reg st .r12 = reg m0 .rcx
  r15 : reg st .r15 = outA m0

end

public section

theorem mu_size (inst : Array EW) :
    (eqKernel (inst.extract 0 4)).size = 2 ^ min 4 inst.size := by
  rw [NativeVm.Math.Keccak.eqKernel_size, Array.size_extract]
  congr 1

theorem pow_min4 (n : Nat) : 2 ^ min 4 n ≤ 16 := by
  rcases Nat.le_total n 4 with h | h
  · rw [Nat.min_eq_right h]
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) h) (by decide)
  · rw [Nat.min_eq_left h]; decide

variable {inst segment lanePoint output : Array EW} {m0 : MachineData}

/-- `inst`'s elements kept from the entry. -/
theorem inst_keep (h : PreOk inst segment lanePoint output m0) {d : DataMem}
    (hs : NativeRustcVm.SameOutside m0.dmem d (Out m0)) :
    NativeRustcVm.EWsAt d (reg m0 .rsi) inst.toList := by
  have hn := nums h
  have := hn.i; have := hn.oi; have := hn.wi; have := hn.si; have := hn.r1
  have hl : (inst.toList.flatMap NativeRustcVm.ewBytes).length = 16 * inst.size := by
    rw [ews_len, Array.length_toList]
  exact keep_in h hs (by rw [hl]; omega) (by rw [hl]; omega) (by rw [hl]; omega)
    (by rw [hl]; omega) h.instAt

variable [Host] {k : Nat}

/-- **`b9`, `b10`**: the instance weights. -/
theorem mu (hp : Placed code k) (hpre : FirstClaimPre inst segment lanePoint output m0)
    (heq : Spec (Labels.label NativeRustcVmX64.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b9Offset)) (hI : LDone m0 segment lanePoint output st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b11Offset) ∧
      MDone m0 inst segment lanePoint output s'.data) st := by
  have h := preOk hpre
  have hn := nums h
  have hr1 := hn.r1
  have hr2 := hn.r2
  have hfb := fbA_toNat h
  have hfmap := frame_mapped h.st (F := 1376) (by rw [stack_eq]; decide)
  -- `b9`: `mu` zeroed, `call eq_kernel`.
  have hwf := wf_body h hI.body.frame.kept (d := st.data) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b9Offset + b9.length)).toBitVec)
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) exit_b9 hwf (fun _ _ ↦ rfl) hpc
    (match_callS hI.body.frame) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hwi1, -, -, hrdi, hrsi, hrdx, hrcx, hrbx, hr14, hr13, hrbp, hat1⟩ := ok_b9
  have hf1 : Frame m0 1376 slots 0 st1.data := Frame.of_block hI.body.frame hwf hm1 hmid1 slots_le'
  have hs1 := sameOutside_touch hwf hm1 (r := 0) rfl (by decide) (within_spec hwi1)
  have hsp1 : rspOf st1.data = fbA m0 := by rw [hf1.sp, off_zero]
  have hso1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (Out m0) := fun q hq ↦
    (hs1 q fun ht ↦ hq (touch_out h (fun _ hj ↦ by omega) ht)).trans (hI.body.same q hq)
  have l16 : (frameEnv m0 st.data 1376 [(argA m0, 24)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b9Offset + b9.length)).toBitVec).load 0 16 8 = reg m0 .rsi :=
    load_frame hI.il.ip
  have l24 : (frameEnv m0 st.data 1376 [(argA m0, 24)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b9Offset + b9.length)).toBitVec).load 0 24 8 = reg m0 .rdx :=
    load_frame hI.il.il
  have e7 : reg st1.data .rdi = reg m0 .rsi := (hm1.regs .rdi _ hrdi).trans l16
  have e6 : (reg st1.data .rsi).toNat = min 4 inst.size := by
    rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hrsi]
    show (if CmpOp.apply .ult .W64 (Env.load _ 0 24 8) (BitVec.ofNat 64 4) = true then
      Env.load _ 0 24 8 else BitVec.ofNat 64 4).toNat = _
    rw [l24, min4_eval, ← h.sz]
  have e2 : reg st1.data .rdx = off (fbA m0) 72 := (hm1.regs .rdx _ hrdx).trans (eval_ptr0 72)
  have e1 : (reg st1.data .rcx).toNat = 16 := by
    rw [show reg st1.data .rcx = _ from hm1.regs .rcx _ hrcx]; rfl
  have hinst := inst_keep h hso1
  have hi := hn.i
  have hsi := hn.si
  -- `eq_kernel` on `inst`'s first coordinates into `mu`'s items.
  have hek : eqKernelStack = 256 := by decide
  have hsb1 : (stackBelow st1.data eqKernelStack).toNat = (rspOf m0).toNat - 1632 := by
    rw [stackBelow_callee hsp1 (by rw [hek]; omega), stackBelow_toNat (by rw [hek]; omega), hek]
  have hf72 : (off (fbA m0) 72).toNat = (rspOf m0).toNat - 1376 + 72 := fb_off h (by decide)
  have him : NativeRustcVm.Mapped m0.dmem (reg m0 .rsi) (16 * inst.size) :=
    rd_mapped h (r := ewsRegion (reg m0 .rsi) inst.size) List.mem_cons_self
  have hpre1 : EqKernelPre st1.data := by
    unfold EqKernelPre SliceOk Readable OffStack
    rw [e7, e2, e6, e1]
    refine ⟨stackOk_callee h.st hf1.kept hsp1 (by rw [stack_eq, hek]), by omega,
      ⟨⟨Mapped.keeps (fun i hi ↦ him i (by omega)) hf1.kept, by show _ + _ ≤ _; omega⟩, ?_⟩,
      ⟨⟨Mapped.keeps (mapped_off hfmap (by decide)) hf1.kept, by show _ + _ ≤ _; rw [hf72]; omega⟩,
        ?_⟩, ?_⟩
    · show _ + _ ≤ _ ∨ _ + _ ≤ _
      rw [hsb1, hek]; omega
    · show _ + _ ≤ _ ∨ _ + _ ≤ _
      rw [hf72, hsb1, hek]; omega
    · show _ + _ ≤ _ ∨ _ + _ ≤ _
      rw [hf72]; omega
  refine call_then hpc1 heq hpre1 fun st2 hpc2 hrsp2 ⟨hpost, hch, hsv2⟩ ↦ ?_
  rw [e6, e1] at hpost
  simp only [pow_min4 inst.size, ite_true] at hpost
  obtain ⟨hr0, hrdx2, hker⟩ := hpost
  have hslice : slice st1.data (reg st1.data .rdi) (reg st1.data .rsi) = inst.extract 0 4 := by
    unfold slice
    have ht := NativeRustcVm.ewsOf_of_ewsAt (hinst.take 4)
    rw [List.length_take, Array.length_toList] at ht
    rw [e7, e6, ht, extract_zero]
  rw [hslice, e2] at hker
  unfold Changes at hch
  rw [e2, e1, hek] at hch
  obtain ⟨hb2, hch2⟩ := call_body h hf1 hso1 hsv2 hrsp2 (s := 256) (by decide) hch
    (frame_D h (o := 72) (n := 16 * 16) (by decide))
  -- `b10`: `eq_kernel`'s result checked.
  have hwf2 := wf_body h hb2.frame.kept (d := st2.data) (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b10_in_code (by simp [b10]) hp) exit_b10 hwf2 nofun
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.FirstClaim.b9_next)) (match_callS hb2.frame) fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hmem3, hat3⟩ := ok_test b10 (by simp)
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 hmem3
  have hb3 : Body m0 st3.data := hb2.of_mem (Frame.of_block hb2.frame hwf2 hm3 hmid3 slots_le') hd3
  have hc3 : test1.eval (frameEnv m0 st2.data 1376 [(argA m0, 24)] (fun _ ↦ 0) 0) = false := by
    show CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (reg st2.data .rax) (BitVec.ofNat 64 1))
      (BitVec.ofNat 64 0) = false
    rw [hr0]; decide
  simp only [PcOk, hc3, Bool.false_eq_true, ite_false] at hpc3
  -- the registers
  have a1 : ∀ r ∈ [Reg64.r12, .r15], reg st1.data r = reg st.data r :=
    fun r hr ↦ atoms_eq hm1 hat1 hr
  have a3 : ∀ r ∈ [Reg64.rdx, .rbx, .rbp, .r12, .r13, .r14, .r15],
      reg st3.data r = reg st2.data r := fun r hr ↦ atoms_eq hm3 hat3 hr
  -- the bit weights kept
  have hw3 : ElemsAt st3.data.dmem (wA m0) (bitW (eqKernel lanePoint)) 1600 := by
    have w1 := w_keep h hs1 (stk_w h fun _ hq ↦ touch_stk h (fun _ hj ↦ by omega) hq) hI.w
    rw [hd3]
    exact w_keep h hch2 (stk_w h fun _ hq ↦ hq.elim (fd_stk h (by decide)) (low_stk h)) w1
  refine .done _ ⟨hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.FirstClaim.b10_next), hb3, hw3,
    by rw [hd3]; exact hker, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a3 .rdx (by simp), hrdx2, mu_size inst]
  · exact (a3 .rbx (by simp)).trans ((hsv2.1 .rbx rfl).trans ((hm1.regs .rbx _ hrbx).trans l24))
  · exact (a3 .r14 (by simp)).trans ((hsv2.1 .r14 rfl).trans ((hm1.regs .r14 _ hr14).trans l16))
  · exact (a3 .r13 (by simp)).trans ((hsv2.1 .r13 rfl).trans ((hm1.regs .r13 _ hr13).trans hI.rax))
  · exact (a3 .rbp (by simp)).trans ((hsv2.1 .rbp rfl).trans ((hm1.regs .rbp _ hrbp).trans hI.rdx))
  · exact (a3 .r12 (by simp)).trans ((hsv2.1 .r12 rfl).trans ((a1 .r12 (by simp)).trans hI.r12))
  · exact (a3 .r15 (by simp)).trans ((hsv2.1 .r15 rfl).trans ((a1 .r15 (by simp)).trans hI.r15))

end

end NativeRustcVmX64.KeccakGkr.FirstClaim
