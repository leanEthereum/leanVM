module

public import NativeRustcVmX64.KeccakGkr.FirstClaim.Defs
public import NativeRustcVmX64.Code.Vm.EqKernel.Names

/-!
# `first_claim`: the prologue (x86-64)

`b0` pushes RBP to RBX, reserves 1320 bytes, zeroes the lanes' kernel at `328` and calls
`eq_kernel` on the lane point into it; `b1` checks it succeeded, `b2` saves `inst`'s address and
length at `16`, `24` and starts the bit weights' loop (`prologue`, to `WInv` at bit `0`).
-/

namespace NativeRustcVmX64.KeccakGkr.FirstClaim

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.FirstClaim
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off inRange_iff' Mapped.keeps
  bytesAt_congr inRange_off_self Touch)

@[expose] public section

/-- `inst`'s address and length, saved in the frame. -/
structure IL (m0 : MachineData) (d : DataMem) : Prop where
  ip : NativeRustcVm.WordAt d (off (fbA m0) 16) (UInt64.ofBitVec (reg m0 .rsi))
  il : NativeRustcVm.WordAt d (off (fbA m0) 24) (UInt64.ofBitVec (reg m0 .rdx))

/-- **The bit weights' loop head** at bit `j`: the weights before it written. -/
structure WInv (m0 : MachineData) (lanePoint : Array EW) (j : Nat) (st : MachineData) : Prop where
  body : Body m0 st
  il : IL m0 st.dmem
  lanes : NativeRustcVm.EWsAt st.dmem (off (fbA m0) 328) (eqKernel lanePoint).toList
  w : ElemsAt st.dmem (wA m0) (NativeVm.Math.Keccak.bitW (eqKernel lanePoint)) j
  j_lt : j < 1600
  rcx : reg st .rcx = BitVec.ofNat 64 j
  rbp : reg st .rbp = BitVec.ofNat 64 (8 + 16 * j)
  r14 : reg st .r14 = wA m0
  r15 : reg st .r15 = outA m0
  rbx : reg st .rbx = reg m0 .rcx
  r13 : reg st .r13 = reg m0 .r9

end

public section

variable {inst segment lanePoint output : Array EW} {m0 : MachineData}

theorem lanes_len (h : PreOk inst segment lanePoint output m0) :
    ((eqKernel lanePoint).toList.flatMap NativeRustcVm.ewBytes).length = 512 := by
  rw [ews_len, Array.length_toList, NativeVm.Math.Keccak.eqKernel_size, h.lpSz]
  rfl

/-- An argument's bytes off the stack. -/
theorem rd_mapped (h : PreOk inst segment lanePoint output m0) {r : Region}
    (hr : r ∈ rsOf m0 inst.size) : NativeRustcVm.Mapped m0.dmem r.addr r.size :=
  (Areas.ok h.areas (List.mem_append_right _ hr)).1

variable [Host] {k : Nat}

/-- **The prologue**: from the entry to the bit weights' loop head at bit `0`. -/
theorem prologue (hp : Placed code k) (hpre : FirstClaimPre inst segment lanePoint output m0)
    (heq : Spec (Labels.label NativeRustcVmX64.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b3Offset) ∧
      WInv m0 lanePoint 0 s'.data) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b0Offset)⟩ := by
  have h := preOk hpre
  have hn := nums h
  have hr1 := hn.r1
  have hr2 := hn.r2
  have hl := hn.l
  have hsl := hn.sl
  have hfb := fbA_toNat h
  -- `b0`: the prologue, `call eq_kernel`.
  have hwf0 := wf_body h (d := m0) (fun _ h ↦ h) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b0Offset + b0.length)).toBitVec)
  have hm0 : Match (frameEnv m0 m0 1376 [(argA m0, 24)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b0Offset + b0.length)).toBitVec) entryS m0 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial
      ⟨arg_alias 0, arg_alias 1, arg_alias 2, trivial⟩
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 (fun _ _ ↦ rfl) hm0
    fun st1 hm1 hpc1 => ?_
  obtain ⟨hpro, hws1, -, hx7, hx6, hx2, hx1, h13, h14, h15, h12, hbx⟩ := ok_b0
  have hf1 : Frame m0 1376 slots 0 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le' (by decide)
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (NativeRustcVm.InRange (fbA m0) 1376) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hws1
  have hsp1 : rspOf st1.data = fbA m0 := by rw [hf1.sp, off_zero]
  have hso1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (Out m0) :=
    NativeRustcVm.Transcript.SameOutside.mono hs1 fun q hq ↦ frame_out h hq
  have hX7 : reg st1.data .rdi = reg m0 .r8 := hm1.regs .rdi _ hx7
  have hX6 : (reg st1.data .rsi).toNat = 5 := by
    rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hx6]; rfl
  have hX2 : reg st1.data .rdx = off (fbA m0) 328 := (hm1.regs .rdx _ hx2).trans (eval_ptr0 328)
  have hX1 : (reg st1.data .rcx).toNat = 32 := by
    rw [show reg st1.data .rcx = _ from hm1.regs .rcx _ hx1]; rfl
  -- `eq_kernel` on the lane point into the lanes' kernel.
  have hek : eqKernelStack = 256 := by decide
  have hsb1 : (stackBelow st1.data eqKernelStack).toNat = (rspOf m0).toNat - 1632 := by
    rw [stackBelow_callee hsp1 (by rw [hek]; omega), stackBelow_toNat (by rw [hek]; omega), hek]
  have hf328 : (off (fbA m0) 328).toNat = (rspOf m0).toNat - 1376 + 328 := fb_off h (by decide)
  have hlpm : NativeRustcVm.Mapped m0.dmem (reg m0 .r8) (16 * 5) :=
    rd_mapped h (r := ewsRegion (reg m0 .r8) 5)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hlp1 : NativeRustcVm.EWsAt st1.data.dmem (reg m0 .r8) lanePoint.toList :=
    keep_stk hs1 (fun q hq ↦ frame_stk h hq)
      (by rw [ews_len, Array.length_toList, h.lpSz]; omega)
      (by rw [ews_len, Array.length_toList, h.lpSz]; omega) h.lpAt
  have hfmap := frame_mapped h.st (F := 1376) (by rw [stack_eq]; decide)
  have hpre1 : EqKernelPre st1.data := by
    unfold EqKernelPre SliceOk Readable OffStack
    rw [hX7, hX2, hX6, hX1]
    refine ⟨stackOk_callee h.st hf1.kept hsp1 (by rw [stack_eq, hek]), by decide,
      ⟨⟨Mapped.keeps hlpm hf1.kept, by show _ + _ ≤ _; omega⟩, ?_⟩,
      ⟨⟨Mapped.keeps (mapped_off hfmap (by decide)) hf1.kept, by show _ + _ ≤ _; rw [hf328]; omega⟩,
        ?_⟩, ?_⟩
    · show _ + _ ≤ _ ∨ _ + _ ≤ _
      rw [hsb1, hek]; omega
    · show _ + _ ≤ _ ∨ _ + _ ≤ _
      rw [hf328, hsb1, hek]; omega
    · show _ + _ ≤ _ ∨ _ + _ ≤ _
      rw [hf328]; omega
  refine call_then hpc1 heq hpre1 fun st2 hpc2 hrsp2 ⟨hpost, hch, hsv2⟩ => ?_
  rw [hX6, hX1] at hpost
  simp only [show 2 ^ 5 ≤ 32 by decide, ite_true] at hpost
  obtain ⟨hr0, -, hker⟩ := hpost
  have hslice : slice st1.data (reg st1.data .rdi) (reg st1.data .rsi) = lanePoint := by
    unfold slice
    rw [hX7, hX6, ← h.lpSz, ← Array.length_toList, NativeRustcVm.ewsOf_of_ewsAt hlp1]
  rw [hslice, hX2] at hker
  unfold Changes at hch
  rw [hX2, hX1, hek] at hch
  obtain ⟨hb2, hch2⟩ := call_body h hf1 hso1 hsv2 hrsp2 (s := 256) (by decide) hch
    (frame_D h (o := 328) (n := 16 * 32) (by decide))
  -- `b1`: `eq_kernel`'s result checked.
  have hwf2 := wf_body h hb2.frame.kept (d := st2.data) (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf2 nofun
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.FirstClaim.b0_next)) (match_callS hb2.frame) fun st3 hm3 hpc3 => ?_
  obtain ⟨hmid3, hmem3, hat3⟩ := ok_b1
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 hmem3
  have hb3 : Body m0 st3.data := hb2.of_mem (Frame.of_block hb2.frame hwf2 hm3 hmid3 slots_le') hd3
  have hc3 : ((SBool.cmp .eq .W64 (.reg .rax) (.lit 1)).not).eval
      (frameEnv m0 st2.data 1376 [(argA m0, 24)] (fun _ ↦ 0) 0) = false := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, low_W64]
    rw [show (frameEnv m0 st2.data 1376 [(argA m0, 24)] (fun _ ↦ 0) 0).regs .rax = 1#64 from hr0]
    rfl
  simp only [PcOk, hc3, Bool.false_eq_true, ite_false] at hpc3
  -- `b2`: `inst` saved, the loop's start.
  have hwf3 := wf_body h hb3.frame.kept (d := st3.data) (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwf3 nofun
    (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.FirstClaim.b1_next)) (match_callS hb3.frame) fun st4 hm4 hpc4 => ?_
  obtain ⟨hmid4, hwi4, hw16, hw24, h15', hbx', h14', hbp', hcx', hat4⟩ := ok_b2
  have hs4 := sameOutside_touch hwf3 hm4 (r := 0) rfl (by decide) (within_spec hwi4)
  have hb4 : Body m0 st4.data :=
    block_body h hb3 (Frame.of_block hb3.frame hwf3 hm4 hmid4 slots_le') (by decide) hs4
  simp only [PcOk] at hpc4
  -- the registers
  have ekeep : ∀ r, r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15] → reg st3.data r = reg st1.data r :=
    fun r hr ↦ (atoms_eq hm3 hat3 hr).trans (hsv2.1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl))
  have e12 : reg st3.data .r12 = reg m0 .rsi :=
    (ekeep .r12 (by simp)).trans (hm1.regs .r12 _ h12)
  have e15 : reg st3.data .r15 = reg m0 .rdx :=
    (ekeep .r15 (by simp)).trans (hm1.regs .r15 _ h15)
  have l16 := wordAt_write hm4 (r := 0) (o := 16) (v := .reg .r12) rfl (by decide) hw16
  have l24 := wordAt_write hm4 (r := 0) (o := 24) (v := .reg .r15) rfl (by decide) hw24
  refine .done _ ⟨hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.FirstClaim.b2_next), ⟨hb4,
    ⟨by rw [← e12]; exact l16, by rw [← e15]; exact l24⟩,
    keep_touch h hs4 (by rw [lanes_len h]; omega) (by rw [lanes_len h]; omega)
      (by show NativeRustcVm.BytesAt st3.data.dmem _ _; rw [hd3]; exact hker),
    fun i hi ↦ absurd hi (Nat.not_lt_zero _), by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (hm4.regs .rcx _ hcx').trans rfl
  · exact (hm4.regs .rbp _ hbp').trans rfl
  · exact (hm4.regs .r14 _ h14').trans (load_arg h hb3.same (i := 2) (by decide))
  · exact (hm4.regs .r15 _ h15').trans ((ekeep .rbx (by simp)).trans (hm1.regs .rbx _ hbx))
  · exact (hm4.regs .rbx _ hbx').trans ((ekeep .r14 (by simp)).trans (hm1.regs .r14 _ h14))
  · exact (atoms_eq hm4 hat4 (by simp)).trans ((ekeep .r13 (by simp)).trans (hm1.regs .r13 _ h13))

end

end NativeRustcVmX64.KeccakGkr.FirstClaim
