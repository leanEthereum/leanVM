module

public import NativeRustcVmArm.Code.Vm.EqKernel.Names
public import NativeRustcVmArm.KeccakGkr.FirstClaim.Defs
public import NativeVm.Math.Keccak.Facts

/-!
# `first_claim`: the prologue

`b0` saves X19 to X30 in the 1408-byte frame, keeps the arguments in X19 to X25, zeroes the 32
lanes at `16` and calls `eq_kernel` on the lane point into them; `b1` checks it succeeded; `b2`
saves `committed`'s high limb at `8`, reads the bit weights' address above the frame and starts
the bit weights' loop (`prologue`, to `WInv` at bit `0`).
-/

namespace NativeRustcVmArm.KeccakGkr.FirstClaim

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Vm.FirstClaim NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVm (Region)
open NativeRustcVm.KeccakGkr (claimBytes weightsBytes)

@[expose] public section

/-- The registers the body keeps from the entry. -/
structure Args (m0 st : MachineData) : Prop where
  x19 : st.regs.X19 = m0.regs.X0
  x22 : st.regs.X22 = m0.regs.X3
  x23 : st.regs.X23 = m0.regs.X2
  x24 : st.regs.X24 = m0.regs.X1

/-- **The bit weights' loop head** at bit `j`. -/
structure WInv [Labels] (m0 : MachineData) (lanePoint : Array EW) (j : Nat) (st : MachineData) :
    Prop where
  body : Body m0 st
  args : Args m0 st
  x21 : st.regs.X21 = m0.regs.X6
  x25 : st.regs.X25 = m0.regs.X5
  x26 : st.regs.X26.toBitVec = fbA m0 + BitVec.ofNat 64 16
  x20 : st.regs.X20.toNat = j
  x27 : st.regs.X27.toBitVec = wtsA m0 + BitVec.ofNat 64 (8 + 16 * j)
  x28 : st.regs.X28.toNat = 25600 - 16 * j
  x29 : st.regs.X29 = 1
  j_lt : j < 1600
  lanes : NativeRustcVm.EWsAt st.dmem (fbA m0 + BitVec.ofNat 64 16) (eqKernel lanePoint).toList
  c1 : NativeRustcVm.WordAt st.dmem (fbA m0 + BitVec.ofNat 64 8) m0.regs.X7
  w : ElemsAt st.dmem (wtsA m0) (wOf (eqKernel lanePoint)) j

end

public section

variable [NativeRustcArm.Host] {inst segment lanePoint output : Array EW} {m0 : MachineData} {k : Nat}

/-- **The prologue**: from the entry to the bit weights' loop head at bit `0`. -/
theorem prologue (hp : Placed code k) (hpre : FirstClaimPre inst segment lanePoint output m0)
    (heq : Spec (Labels.label NativeRustcVmArm.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost) :
    Eventually (step1 Host.exe)
      (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FirstClaim.b3Offset) ∧ WInv m0 lanePoint 0 s'.data)
      ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.FirstClaim.b0Offset)⟩ := by
  have hS := hpre.1
  have hA := pre_areas hpre
  have h1408 : 1408 ≤ firstClaimStack := by decide
  obtain ⟨hmap, hnw, hfb⟩ := frame_ok hS h1408
  have hws := wsOff hpre
  have hlp : lanePoint.size = 5 := hpre.2.2.2.2.2.2.1
  have hlpm : NativeRustcVm.EWsAt m0.dmem m0.regs.X4.toBitVec lanePoint.toList :=
    hpre.2.2.2.2.2.2.2.1
  -- the prologue
  have hmA : Match (Env.ofMachine m0 [(fbA m0, 1408)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h1408 rfl, trivial⟩
      (by
        show _ = fbA m0 + BitVec.ofInt 64 1408
        rw [show BitVec.ofInt 64 1408 = BitVec.ofNat 64 1408 from rfl, BitVec.sub_add_cancel])
      trivial trivial trivial trivial
  refine exec_then (b0_in_code.trans hp.1 (by simp [b0])) e0 (wf_one hmap hnw) hmA
    fun s1 hm1 hpc1 ↦ ?_
  have hb1 : Body m0 s1.data :=
    Frame.of_entry hS h1408 hm1 rfl (by decide +kernel)
      (fun r hr hn ↦ absurd (all_slots r (by
        simp only [calleeRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> rfl) hn) (by simp))
      (by decide +kernel)
  have hx1 : s1.data.regs.X1.toNat = 5 := by
    show (s1.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [hm1.regs .X1 _ rfl]; rfl
  have hx2 : s1.data.regs.X2.toBitVec = fbA m0 + BitVec.ofNat 64 16 := hm1.regs .X2 _ rfl
  have hx3 : s1.data.regs.X3.toNat = 32 := by
    show (s1.data.regs.getXReg .X3).toBitVec.toNat = _
    rw [hm1.regs .X3 _ rfl]; rfl
  have hr : ewsRegion m0.regs.X4.toBitVec lanePoint.size ∈ rsOf m0 inst.size := by
    rw [hlp]; simp
  obtain ⟨hsl, hslice⟩ := arg_slice hpre hb1 hr hlpm (n := eqKernelStack) (by decide)
    (x := s1.data.regs.X0) (l := s1.data.regs.X1) (hm1.regs .X0 _ rfl) (by rw [hx1, hlp])
  -- `eq_kernel` into the lanes
  refine call_then hpc1 heq ⟨hb1.stackOk hS (by decide) (by decide), by rw [hx1]; decide, hsl,
    ⟨by rw [hx2, hx3]; exact local_readable hpre hb1 (by decide),
      by rw [hx2, hx3]; exact local_offStack hpre hb1 (by decide) (by decide)⟩, ?_⟩
    fun s2 hpc2 hpost2 ↦ ?_
  · rw [show s1.data.regs.X0.toBitVec = m0.regs.X4.toBitVec from hm1.regs .X0 _ rfl, hx1, hx2, hx3]
    have := arg_local_apart hpre hr (o := 16) (n := 16 * 32) (by decide)
    rw [hlp] at this
    exact this
  obtain ⟨hpost, hch, hsv2⟩ := hpost2
  rw [hx1, hx3, ite_eq_left (by decide), hslice, hx2] at hpost
  obtain ⟨hr0, -, hlanes⟩ := hpost
  have hb2 : Body m0 s2.data :=
    hb1.call_local (n := eqKernelStack) (lo := 1312) hS (by decide) slots_le (by decide) hws hch
      (fun p h ↦ by
        rcases h with h | h
        · rw [hx2, hx3] at h
          exact Or.inr (Or.inr (inRange_mono h (by decide)))
        · exact Or.inl h) hsv2
  -- `b1`: `eq_kernel` succeeded
  have hx0' : (s2.data.regs.getXReg .X0).toBitVec = 1#64 := by
    show s2.data.regs.X0.toBitVec = _
    rw [hr0]; rfl
  refine exec_at (b1_in_code.trans hp.1 (by simp [b1])) e1 (Env.wf_nil _) hpc2 (match_nil _)
    fun s3 hm3 hpc3 ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.FirstClaim.b1_length, NativeRustcVmArm.Vm.FirstClaim.b1Length] at hpc3
  sym_simp at hpc3
  simp only [Env.ofMachine_regs, hx0'] at hpc3
  rw [ite_eq_right (by decide)] at hpc3
  have hb3 : Body m0 s3.data :=
    hb2.of_block (match_nil _) hm3 (Env.wf_nil _) rfl all_slots (by decide)
  have k3 := KeccakGkr.Match.regs_keep (match_nil _) hm3
    [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26] (by decide)
  have hd3 : s3.data.dmem = s2.data.dmem := hm3.dmem_eq (Env.wf_nil _) rfl
  -- `b2`: the bit weights' address, the loop's start
  obtain ⟨hfwm, hfwn⟩ := frame_word_ok hpre
  have hwfB := wf_one (m := s3.data) (Mapped.kept' hfwm hb3.kept) hfwn
  have hmB : Match (Env.ofMachine s3.data [(fbA m0, 1416)]) wS s3.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h1408 rfl, trivial⟩
      (by rw [hb3.sp]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_at (b2_in_code.trans hp.1 (by simp [b2])) e2 hwfB hpc3 hmB fun s4 hm4 hpc4 ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.FirstClaim.b2_length, NativeRustcVmArm.Vm.FirstClaim.b2Length] at hpc4
  have hb4 : Body m0 s4.data :=
    hb3.write_local (lo := 1312) hS h1408 slots_le (by decide) hws hmB hm4 hwfB rfl all_slots
      (by decide) fun p hw ↦
        Or.inr (Written.inRange_le (r := 0) rfl hfwn (by decide) (by decide) hw)
  have hso4 : SameOutside s3.data.dmem s4.data.dmem (InRange (fbA m0) 16) := fun p hp ↦
    hm4.sameOutside hwfB p fun hw ↦
      hp (Written.inRange_le (r := 0) rfl hfwn (by decide) (by decide) hw)
  have k4 := KeccakGkr.Match.regs_keep hmB hm4 [.X19, .X21, .X22, .X23, .X24, .X25, .X26]
    (by decide)
  have hreg : ∀ r ∈ [XReg.X19, .X21, .X22, .X23, .X24, .X25, .X26],
      s4.data.regs.getXReg r = s1.data.regs.getXReg r := by
    intro r hr
    rw [k4 r hr, k3 r (by simp at hr ⊢; rcases hr with h | h | h | h | h | h | h <;> simp [h])]
    exact hsv2.1 r (by simp at hr; rcases hr with h | h | h | h | h | h | h <;> subst h <;> rfl)
  -- the bit weights' address
  have hwts : NativeRustcVm.WordAt s3.data.dmem (fbA m0 + BitVec.ofNat 64 1408)
      (NativeRustcVm.wordOf m0.dmem m0.regs.SP.toBitVec) := by
    have hw := Areas.ok hA (r := ⟨m0.regs.SP.toBitVec, 8⟩) (Or.inr (by simp))
    have h0 := NativeRustcVm.wordAt_of_mapped (d := m0.dmem) (a := m0.regs.SP.toBitVec) hw.1
    have h1 := hb3.bytesAt hA hS (r := ⟨m0.regs.SP.toBitVec, 8⟩) (by simp) (o := 0)
      (bs := NativeRustcVm.wordBytes (NativeRustcVm.wordOf m0.dmem m0.regs.SP.toBitVec))
      (by rw [NativeRustcVm.length_wordBytes])
      (by rw [NativeRustcVm.addr_add_zero]; exact h0)
    rw [NativeRustcVm.addr_add_zero] at h1
    rwa [show fbA m0 + BitVec.ofNat 64 1408 = m0.regs.SP.toBitVec by
      unfold fbA; exact BitVec.sub_add_cancel _ _]
  have l8 := load_word (env := Env.ofMachine s3.data [(fbA m0, 1416)]) (r := 0) (off := 1408) hwts
  have v20 : (s3.data.regs.getXReg .X20) = m0.regs.X7 := by
    rw [k3 .X20 (by simp), hsv2.1 .X20 rfl]
    exact UInt64.toBitVec_inj.mp (hm1.regs .X20 _ rfl)
  have e20 : UInt64.ofBitVec (s3.data.regs.getXReg .X20).toBitVec = m0.regs.X7 := by
    rw [UInt64.ofBitVec_toBitVec, v20]
  have hc1 : NativeRustcVm.WordAt s4.data.dmem (fbA m0 + BitVec.ofNat 64 8) m0.regs.X7 := by
    rw [← e20]
    exact Sumcheck.Match.wordAt_write hm4 (r := 0) (o := 8) (v := .reg .X20) rfl (by decide)
      (by decide +kernel)
  have hlanes4 : NativeRustcVm.EWsAt s4.data.dmem (fbA m0 + BitVec.ofNat 64 16)
      (eqKernel lanePoint).toList :=
    NativeRustcVm.BytesAt.of_sameOutside (hd3 ▸ hlanes) hso4 fun i hi ↦ by
      rw [NativeRustcVm.addr_add_add]
      exact slot_not_local (lo := 16) (o := 16 + i) (by omega) (by
        rw [length_flatMap_ewBytes] at hi
        have : (eqKernel lanePoint).toList.length = 32 := by
          rw [Array.length_toList, NativeVm.Math.Keccak.eqKernel_size, hlp]; rfl
        omega)
  refine .done _ ⟨by simpa only [b2Offset, b3Offset] using hpc4, hb4, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide,
    hlanes4, hc1, fun i hi ↦ absurd hi (by omega)⟩
  · show s4.data.regs.getXReg .X19 = _
    rw [hreg .X19 (by simp)]; exact UInt64.toBitVec_inj.mp (hm1.regs .X19 _ rfl)
  · show s4.data.regs.getXReg .X22 = _
    rw [hreg .X22 (by simp)]; exact UInt64.toBitVec_inj.mp (hm1.regs .X22 _ rfl)
  · show s4.data.regs.getXReg .X23 = _
    rw [hreg .X23 (by simp)]; exact UInt64.toBitVec_inj.mp (hm1.regs .X23 _ rfl)
  · show s4.data.regs.getXReg .X24 = _
    rw [hreg .X24 (by simp)]; exact UInt64.toBitVec_inj.mp (hm1.regs .X24 _ rfl)
  · show s4.data.regs.getXReg .X21 = _
    rw [hreg .X21 (by simp)]; exact UInt64.toBitVec_inj.mp (hm1.regs .X21 _ rfl)
  · show s4.data.regs.getXReg .X25 = _
    rw [hreg .X25 (by simp)]; exact UInt64.toBitVec_inj.mp (hm1.regs .X25 _ rfl)
  · show (s4.data.regs.getXReg .X26).toBitVec = _
    rw [hreg .X26 (by simp)]; exact hm1.regs .X26 _ rfl
  · show (s4.data.regs.getXReg .X20).toBitVec.toNat = 0
    rw [hm4.regs .X20 _ rfl]; rfl
  · show (s4.data.regs.getXReg .X27).toBitVec = _
    rw [hm4.regs .X27 _ rfl]
    sym_simp
    rw [l8]
    rfl
  · show (s4.data.regs.getXReg .X28).toBitVec.toNat = _
    rw [hm4.regs .X28 _ rfl]; rfl
  · apply UInt64.toBitVec_inj.mp
    show (s4.data.regs.getXReg .X29).toBitVec = _
    rw [hm4.regs .X29 _ rfl]; rfl

end

end NativeRustcVmArm.KeccakGkr.FirstClaim
