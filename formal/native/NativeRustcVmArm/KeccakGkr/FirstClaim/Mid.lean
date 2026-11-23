module

public import NativeRustcVmArm.Code.Vm.Dot.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EqKernel.Names
public import NativeRustcVmArm.KeccakGkr.FirstClaim.Loop

/-!
# `first_claim`: the segment's kernel, `last`, the instance weights

`b5` calls `eq_kernel` on the segment into the two elements at `528`, `b6` checks it succeeded;
`b7`, `b8` compute `last`, the product of the kernel's last entry and the dot product of the
first 25 lanes with the output lanes (`dot`, `EW::mul`); `b9` calls `eq_kernel` on `inst`'s first
four coordinates into the `Buf<EW, 16>`'s items at `568`, `b10` checks it succeeded (`mid`, to
`MDone`).
-/

namespace NativeRustcVmArm.KeccakGkr.FirstClaim

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model LeanVM.Protocol.Verifier
open NativeRustcVmArm.Vm.FirstClaim NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVm (Region)
open NativeRustcVm.KeccakGkr (claimBytes weightsBytes)

@[expose] public section

/-- `last`: the segment kernel's last entry times the dot product of the first 25 lanes with the
output lanes. -/
def lastOf (segment lanePoint output : Array EW) : EW :=
  (eqKernel segment).getD (keccakSegments - 1) 0 * dot ((eqKernel lanePoint).extract 0 25) output

/-- **Before the claim's point**: `last` in X25, X26, the instance weights' kernel at `568`, its
length in X1. -/
structure MDone [Labels] (m0 : MachineData) (inst segment lanePoint output : Array EW)
    (st : MachineData) : Prop where
  body : Body m0 st
  args : Args m0 st
  x21 : st.regs.X21 = m0.regs.X6
  x25 : st.regs.X25 = (lastOf segment lanePoint output).c0
  x26 : st.regs.X26 = (lastOf segment lanePoint output).c1
  x1 : st.regs.X1.toNat = (eqKernel (inst.extract 0 4)).size
  c1 : NativeRustcVm.WordAt st.dmem (fbA m0 + BitVec.ofNat 64 8) m0.regs.X7
  w : ElemsAt st.dmem (wtsA m0) (wOf (eqKernel lanePoint)) 1600
  mu : NativeRustcVm.EWsAt st.dmem (fbA m0 + BitVec.ofNat 64 568)
    (eqKernel (inst.extract 0 4)).toList

end

public section

theorem extract_zero (xs : Array EW) (n : Nat) : xs.extract 0 n = (xs.toList.take n).toArray := by
  apply Array.toList_inj.mp
  simp [Array.toList_extract, List.extract]

theorem take_min4 (l : List EW) : l.take (min l.length 4) = l.take 4 := by
  rcases Nat.le_total l.length 4 with h | h
  · rw [Nat.min_eq_left h, List.take_of_length_le (Nat.le_refl _), List.take_of_length_le h]
  · rw [Nat.min_eq_right h]

variable [NativeRustcArm.Host] {inst segment lanePoint output : Array EW} {m0 : MachineData} {k : Nat}

/-- **`b5` to `b10`**. -/
theorem mid (hp : Placed code k) (hpre : FirstClaimPre inst segment lanePoint output m0)
    (heq : Spec (Labels.label NativeRustcVmArm.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hdot : Spec (Labels.label NativeRustcVmArm.Vm.Dot.entryLabel) DotPre DotPost) {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FirstClaim.b5Offset)) (hI : WDone m0 lanePoint s.data) :
    Eventually (step1 Host.exe)
      (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FirstClaim.b11Offset) ∧ MDone m0 inst segment lanePoint output s'.data)
      s := by
  have hS := hpre.1
  have hA := pre_areas hpre
  have hws := wsOff hpre
  have h1408 : 1408 ≤ firstClaimStack := by decide
  obtain ⟨hmap, hnw, -⟩ := frame_ok hS h1408
  have hn : inst.size = m0.regs.X2.toNat := hpre.2.1
  have hn30 : inst.size ≤ 30 := hpre.2.2.1
  have hinst : NativeRustcVm.EWsAt m0.dmem m0.regs.X1.toBitVec inst.toList := hpre.2.2.2.1
  have hsg : segment.size = 1 := hpre.2.2.2.2.1
  have hsgm : NativeRustcVm.EWsAt m0.dmem m0.regs.X3.toBitVec segment.toList := hpre.2.2.2.2.2.1
  have hlp : lanePoint.size = 5 := hpre.2.2.2.2.2.2.1
  have hos : output.size = 25 := hpre.2.2.2.2.2.2.2.2.1
  have hom : NativeRustcVm.EWsAt m0.dmem m0.regs.X5.toBitVec output.toList :=
    hpre.2.2.2.2.2.2.2.2.2.1
  have hlen : (eqKernel lanePoint).size = 32 := by
    rw [NativeVm.Math.Keccak.eqKernel_size, hlp]; rfl
  have hwr : (⟨wtsA m0, weightsBytes⟩ : Region) ∈ wsOf m0 := by simp
  -- `b5`: the segment's kernel
  have hwf0 := wf_one (m := s.data) (Mapped.kept' hmap hI.body.kept) hnw
  have hm0 : Match (Env.ofMachine s.data [(fbA m0, 1408)]) bodyS s.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h1408 rfl, trivial⟩
      (by rw [hI.body.sp]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_at (b5_in_code.trans hp.1 (by simp [b5])) e5 hwf0 hpc hm0 fun s1 hm1 hpc1 ↦ ?_
  have hb1 : Body m0 s1.data :=
    hI.body.write_local (lo := 1312) hS h1408 slots_le (by decide) hws hm0 hm1 hwf0 rfl all_slots
      (by decide) fun p hw ↦ Or.inr (Written.inRange_le (r := 0) rfl hnw (by decide) (by decide) hw)
  have hso1 : SameOutside s.data.dmem s1.data.dmem (InRange (fbA m0 + BitVec.ofNat 64 528) 32) :=
    fun p hp ↦ hm1.sameOutside hwf0 p fun hw ↦ hp
      (Written.inRange_sub (r := 0) (lo := 528) (hi := 560) rfl hnw (by decide) (by decide) hw)
  have k1 := KeccakGkr.Match.regs_keep hm0 hm1 [.X19, .X21, .X22, .X23, .X24, .X25] (by decide)
  have hx0 : s1.data.regs.X0.toBitVec = m0.regs.X3.toBitVec :=
    (hm1.regs .X0 _ rfl).trans (congrArg UInt64.toBitVec hI.args.x22)
  have hx1 : s1.data.regs.X1.toNat = 1 := by
    show (s1.data.regs.getXReg .X1).toBitVec.toNat = 1
    rw [hm1.regs .X1 _ rfl]; rfl
  have hx2 : s1.data.regs.X2.toBitVec = fbA m0 + BitVec.ofNat 64 528 :=
    (hm1.regs .X2 _ rfl).trans (by
      show fbA m0 + BitVec.ofInt 64 528 = _
      rw [show BitVec.ofInt 64 528 = BitVec.ofNat 64 528 from rfl])
  have hx3 : s1.data.regs.X3.toNat = 2 := by
    show (s1.data.regs.getXReg .X3).toBitVec.toNat = 2
    rw [hm1.regs .X3 _ rfl]; rfl
  have hsr : ewsRegion m0.regs.X3.toBitVec segment.size ∈ rsOf m0 inst.size := by
    rw [hsg]; simp
  obtain ⟨hsl1, hslc1⟩ := arg_slice hpre hb1 hsr hsgm (n := eqKernelStack) (by decide) hx0
    (by rw [hx1, hsg])
  refine call_then hpc1 heq ⟨hb1.stackOk hS (by decide) (by decide), by rw [hx1]; decide, hsl1,
    ⟨by rw [hx2, hx3]; exact local_readable hpre hb1 (by decide),
      by rw [hx2, hx3]; exact local_offStack hpre hb1 (by decide) (by decide)⟩, ?_⟩
    fun s2 hpc2 hpost2 ↦ ?_
  · rw [hx0, hx1, hx2, hx3]
    have := arg_local_apart hpre hsr (o := 528) (n := 16 * 2) (by decide)
    rwa [hsg] at this
  obtain ⟨hpost, hch2, hsv2⟩ := hpost2
  rw [hx1, hx3, ite_eq_left (by decide), hslc1, hx2] at hpost
  obtain ⟨hr0, -, hseg⟩ := hpost
  have hR2 : ∀ p, (InRange (fbA m0 + BitVec.ofNat 64 528) (16 * 2) p ∨
      InRange (stackBelow s1.data eqKernelStack) eqKernelStack p) →
      InRange (stackBelow s1.data eqKernelStack) eqKernelStack p ∨
        NativeRustcVm.InAny (wsOf m0) p ∨ InRange (fbA m0 + BitVec.ofNat 64 528) 32 p :=
    fun p h ↦ h.elim (fun h ↦ Or.inr (Or.inr h)) Or.inl
  have hch2' : SameOutside s1.data.dmem s2.data.dmem (fun p ↦
      InRange (fbA m0 + BitVec.ofNat 64 528) (16 * 2) p ∨
        InRange (stackBelow s1.data eqKernelStack) eqKernelStack p) := by
    have := hch2; rwa [hx2, hx3] at this
  have hb2 : Body m0 s2.data :=
    hb1.call_local (n := eqKernelStack) (lo := 1312) hS (by decide) slots_le (by decide) hws hch2'
      (fun p h ↦ by
        rcases h with h | h
        · exact Or.inr (Or.inr (inRange_mono h (by decide)))
        · exact Or.inl h) hsv2
  have hlanes2 : NativeRustcVm.EWsAt s2.data.dmem (fbA m0 + BitVec.ofNat 64 16)
      (eqKernel lanePoint).toList := by
    have hl :
        16 + (List.flatMap NativeRustcVm.ewBytes (eqKernel lanePoint).toList).length ≤ 528 := by
      rw [length_flatMap_ewBytes, Array.length_toList, hlen]
    exact local_keep' hpre hb1 (local_keep' hpre hI.body hI.lanes (by omega) (n := 0) (by decide)
      (by decide) (Or.inl hl) hso1 fun _ h ↦ Or.inr (Or.inr h)) (by omega) (by decide) (by decide)
      (Or.inl hl) hch2' hR2
  have hc12 : NativeRustcVm.WordAt s2.data.dmem (fbA m0 + BitVec.ofNat 64 8) m0.regs.X7 := by
    have hl : 8 + (NativeRustcVm.wordBytes m0.regs.X7).length ≤ 528 := by
      rw [NativeRustcVm.length_wordBytes]; decide
    exact local_keep' hpre hb1 (local_keep' hpre hI.body hI.c1 (by omega) (n := 0) (by decide)
      (by decide) (Or.inl hl) hso1 fun _ h ↦ Or.inr (Or.inr h)) (by omega) (by decide) (by decide)
      (Or.inl hl) hch2' hR2
  have hw2 : ElemsAt s2.data.dmem (wtsA m0) (wOf (eqKernel lanePoint)) 1600 :=
    ws_keep hpre hb1 hwr (n := eqKernelStack) (by decide) (o' := 528) (n' := 32) (by decide)
      (show 16 * 1600 ≤ weightsBytes by decide) (ws_keep hpre hI.body hwr (n := 0) (by decide)
        (o' := 528) (n' := 32) (by decide) (show 16 * 1600 ≤ weightsBytes by decide) hI.w hso1
        fun _ h ↦ Or.inr h) hch2'
      fun p h ↦ h.elim (fun h ↦ Or.inr h) Or.inl
  have hreg2 : ∀ r ∈ [XReg.X19, .X21, .X22, .X23, .X24, .X25],
      s2.data.regs.getXReg r = s.data.regs.getXReg r := by
    intro r hr
    rw [← k1 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hsv2.1 _ rfl
  -- `b6`: it succeeded
  have hx0' : (s2.data.regs.getXReg .X0).toBitVec = 1#64 := by
    show s2.data.regs.X0.toBitVec = _; rw [hr0]; rfl
  refine exec_at (b6_in_code.trans hp.1 (by simp [b6])) e6 (Env.wf_nil _) hpc2 (match_nil _)
    fun s3 hm3 hpc3 ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.FirstClaim.b6_length, NativeRustcVmArm.Vm.FirstClaim.b6Length] at hpc3
  sym_simp at hpc3
  simp only [Env.ofMachine_regs, hx0'] at hpc3
  rw [ite_eq_right (by decide)] at hpc3
  have hb3 : Body m0 s3.data :=
    hb2.of_block (match_nil _) hm3 (Env.wf_nil _) rfl all_slots (by decide)
  have k3 := KeccakGkr.Match.regs_keep (match_nil _) hm3 [.X19, .X21, .X22, .X23, .X24, .X25]
    (by decide)
  have hd3 : s3.data.dmem = s2.data.dmem := hm3.dmem_eq (Env.wf_nil _) rfl
  -- `b7`: `dot` of the first 25 lanes and the output lanes
  have hwf3 := wf_one (m := s3.data) (Mapped.kept' hmap hb3.kept) hnw
  have hm3b : Match (Env.ofMachine s3.data [(fbA m0, 1408)]) bodyS s3.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h1408 rfl, trivial⟩
      (by rw [hb3.sp]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_at (b7_in_code.trans hp.1 (by simp [b7])) e7 hwf3 hpc3 hm3b fun s4 hm4 hpc4 ↦ ?_
  have hb4 : Body m0 s4.data := hb3.of_block hm3b hm4 hwf3 rfl all_slots (by decide)
  have k4 := KeccakGkr.Match.regs_keep hm3b hm4 [.X19, .X21, .X22, .X23, .X24, .X25] (by decide)
  have hd4 : s4.data.dmem = s3.data.dmem := hm4.dmem_eq hwf3 rfl
  have hk1 : 1 < (eqKernel segment).size := by
    rw [NativeVm.Math.Keccak.eqKernel_size, hsg]; decide
  have hs1 := ewsAt_getD hseg (i := 1) hk1
  rw [NativeRustcVm.addr_add_add] at hs1
  rw [← hd3] at hs1
  obtain ⟨hl0, hl1⟩ := load_ew (env := Env.ofMachine s3.data [(fbA m0, 1408)]) (r := 0)
    (o := 528 + 16 * 1) hs1
  have h26 : s4.data.regs.X26 = ((eqKernel segment).getD 1 0).c0 :=
    UInt64.toBitVec_inj.mp ((hm4.regs .X26 _ rfl).trans hl0)
  have h27 : s4.data.regs.X27 = ((eqKernel segment).getD 1 0).c1 :=
    UInt64.toBitVec_inj.mp ((hm4.regs .X27 _ rfl).trans hl1)
  have hy0 : s4.data.regs.X0.toBitVec = fbA m0 + BitVec.ofNat 64 16 := hm4.regs .X0 _ rfl
  have hy1 : s4.data.regs.X1.toNat = 25 := by
    show (s4.data.regs.getXReg .X1).toBitVec.toNat = 25
    rw [hm4.regs .X1 _ rfl]; rfl
  have hy2 : s4.data.regs.X2.toBitVec = m0.regs.X5.toBitVec + BitVec.ofNat 64 (16 * 0) := by
    rw [Nat.mul_zero, NativeRustcVm.addr_add_zero]
    show (s4.data.regs.getXReg .X2).toBitVec = _
    rw [hm4.regs .X2 _ rfl]
    show (s3.data.regs.getXReg .X25).toBitVec = _
    rw [k3 .X25 (by simp), hreg2 .X25 (by simp)]
    exact congrArg UInt64.toBitVec hI.x25
  have hy3 : s4.data.regs.X3.toNat = 25 := by
    show (s4.data.regs.getXReg .X3).toBitVec.toNat = 25
    rw [hm4.regs .X3 _ rfl]; rfl
  have hor : ewsRegion m0.regs.X5.toBitVec output.size ∈ rsOf m0 inst.size := by
    rw [hos]; simp
  obtain ⟨hor1, hor2, hor3⟩ := arg_sub hpre hb4 hor hom (o := 0) (l := 25) (by omega)
    (n := dotStack) (by decide)
  have hlanes4 : NativeRustcVm.EWsAt s4.data.dmem (fbA m0 + BitVec.ofNat 64 16)
      (eqKernel lanePoint).toList := by rw [hd4, hd3]; exact hlanes2
  refine call_then hpc4 hdot ⟨hb4.stackOk hS (by decide) (by decide),
    ⟨by rw [hy0, hy1]; exact local_readable hpre hb4 (by decide),
      by rw [hy0, hy1]; exact local_offStack hpre hb4 (by decide) (by decide)⟩,
    by rw [hy2, hy3]; exact hor1, by rw [hy2, hy3]; exact hor2⟩ fun s5 hpc5 hpost5 ↦ ?_
  obtain ⟨hdv, hch5, hsv5⟩ := hpost5
  have hdotv : ewRet s5.data = dot ((eqKernel lanePoint).extract 0 25) output := by
    rw [hdv]
    unfold slice
    rw [hy0, hy1, hy2, hy3, hor3, List.drop_zero,
      List.take_of_length_le (l := output.toList) (by rw [Array.length_toList, hos]),
      Array.toArray_toList]
    have := NativeRustcVm.ewsOf_of_ewsAt (hlanes4.take 25)
    rw [List.length_take, Array.length_toList, hlen] at this
    rw [show min 25 32 = 25 from rfl] at this
    rw [this, extract_zero]
  have hb5 : Body m0 s5.data :=
    hb4.call hS (n := dotStack) (by decide) slots_le' hws hch5
      (fun p h ↦ h.elim (fun h ↦ absurd h (by unfold InRange; omega)) Or.inl) hsv5
  -- `b8`: `last`
  refine exec_at (b8_in_code.trans hp.1 (by simp [b8])) e8 (Env.wf_nil _) hpc5 (match_nil _)
    fun s6 hm6 hpc6 ↦ ?_
  have hb6 : Body m0 s6.data :=
    hb5.of_block (match_nil _) hm6 (Env.wf_nil _) rfl all_slots (by decide)
  have hd6 : s6.data.dmem = s5.data.dmem := hm6.dmem_eq (Env.wf_nil _) rfl
  have k6 := KeccakGkr.Match.regs_keep (match_nil _) hm6 [.X19, .X21, .X22, .X23, .X24, .X25]
    (by decide)
  have hz0 : s6.data.regs.X0 = s5.data.regs.X26 := UInt64.toBitVec_inj.mp (hm6.regs .X0 _ rfl)
  have hz1 : s6.data.regs.X1 = s5.data.regs.X27 := UInt64.toBitVec_inj.mp (hm6.regs .X1 _ rfl)
  have hz2 : s6.data.regs.X2 = s5.data.regs.X0 := UInt64.toBitVec_inj.mp (hm6.regs .X2 _ rfl)
  have hz3 : s6.data.regs.X3 = s5.data.regs.X1 := UInt64.toBitVec_inj.mp (hm6.regs .X3 _ rfl)
  refine call_then hpc6 hmul (hb6.stackOk hS (by decide) (by decide)) fun s7 hpc7 hpost7 ↦ ?_
  obtain ⟨hp0, hp1, hch7, hsv7⟩ := hpost7
  have hb7 : Body m0 s7.data :=
    hb6.call hS (n := ewMulStack) (by decide) slots_le' hws hch7 (fun _ h ↦ Or.inl h) hsv7
  have hlast : (⟨s7.data.regs.X0, s7.data.regs.X1⟩ : EW) = lastOf segment lanePoint output := by
    have e26 : s5.data.regs.X26 = ((eqKernel segment).getD 1 0).c0 := (hsv5.1 .X26 rfl).trans h26
    have e27 : s5.data.regs.X27 = ((eqKernel segment).getD 1 0).c1 := (hsv5.1 .X27 rfl).trans h27
    rw [hp0, hp1, hz0, hz1, hz2, hz3, e26, e27]
    have := hdotv
    unfold ewRet at this
    rw [this, lastOf, show keccakSegments - 1 = 1 by decide]
    rfl
  -- the registers and memory so far
  have hreg7 : ∀ r ∈ [XReg.X19, .X21, .X22, .X23, .X24],
      s7.data.regs.getXReg r = s.data.regs.getXReg r := by
    intro r hr
    have hr' : r ∈ [XReg.X19, .X21, .X22, .X23, .X24, .X25] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h | h <;> simp [h]
    rw [← hreg2 r hr', ← k3 r hr', ← k4 r hr']
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact (hsv7.1 _ rfl).trans ((k6 _ (by simp)).trans (hsv5.1 _ rfl))
  have hd7 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 1408 →
      NativeRustcVm.BytesAt s3.data.dmem (fbA m0 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt s7.data.dmem (fbA m0 + BitVec.ofNat 64 o) bs := by
    intro o bs ho h
    have h5 := local_keep hpre hb4 (by rw [hd4]; exact h) ho (by decide) hch5
      (fun p h ↦ h.elim (fun h ↦ absurd h (by unfold InRange; omega)) Or.inl)
    rw [← hd6] at h5
    exact local_keep hpre hb6 h5 ho (by decide) hch7 fun _ h ↦ Or.inl h
  have hw7 : ElemsAt s7.data.dmem (wtsA m0) (wOf (eqKernel lanePoint)) 1600 := by
    have h5 := ws_keep hpre hb4 hwr (n := dotStack) (N := 1600) (o' := 0) (n' := 0) (by decide)
      (by decide) (show 16 * 1600 ≤ weightsBytes by decide) (by rw [hd4, hd3]; exact hw2) hch5
      (fun p h ↦ h.elim (fun h ↦ absurd h (by unfold InRange; omega)) Or.inl)
    rw [← hd6] at h5
    exact ws_keep_call hpre hb6 hwr (by decide) (show 16 * 1600 ≤ weightsBytes by decide) h5 hch7
  have hseg7 : NativeRustcVm.WordAt s7.data.dmem (fbA m0 + BitVec.ofNat 64 8) m0.regs.X7 :=
    hd7 (by rw [NativeRustcVm.length_wordBytes]; decide) (by rw [hd3]; exact hc12)
  -- `b9`: the instance weights' kernel
  have hwf7 := wf_one (m := s7.data) (Mapped.kept' hmap hb7.kept) hnw
  have hm7 : Match (Env.ofMachine s7.data [(fbA m0, 1408)]) bodyS s7.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h1408 rfl, trivial⟩
      (by rw [hb7.sp]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_at (b9_in_code.trans hp.1 (by simp [b9])) e9 hwf7 hpc7 hm7 fun s8 hm8 hpc8 ↦ ?_
  have hb8 : Body m0 s8.data :=
    hb7.write_local (lo := 1312) hS h1408 slots_le (by decide) hws hm7 hm8 hwf7 rfl all_slots
      (by decide) fun p hw ↦ Or.inr (Written.inRange_le (r := 0) rfl hnw (by decide) (by decide) hw)
  have hso8 : SameOutside s7.data.dmem s8.data.dmem (InRange (fbA m0 + BitVec.ofNat 64 560) 264) :=
    fun p hp ↦ hm8.sameOutside hwf7 p fun hw ↦ hp
      (Written.inRange_sub (r := 0) (lo := 560) (hi := 824) rfl hnw (by decide) (by decide) hw)
  have k8 := KeccakGkr.Match.regs_keep hm7 hm8 [.X19, .X21, .X22, .X23, .X24] (by decide)
  have h25 : s8.data.regs.X25 = (lastOf segment lanePoint output).c0 := by
    rw [← hlast]; exact UInt64.toBitVec_inj.mp (hm8.regs .X25 _ rfl)
  have h26' : s8.data.regs.X26 = (lastOf segment lanePoint output).c1 := by
    rw [← hlast]; exact UInt64.toBitVec_inj.mp (hm8.regs .X26 _ rfl)
  have hw0 : s8.data.regs.X0.toBitVec = m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * 0) := by
    rw [Nat.mul_zero, NativeRustcVm.addr_add_zero]
    show (s8.data.regs.getXReg .X0).toBitVec = _
    rw [hm8.regs .X0 _ rfl]
    show (s7.data.regs.getXReg .X24).toBitVec = _
    rw [hreg7 .X24 (by simp)]
    exact congrArg UInt64.toBitVec hI.args.x24
  have hw1 : s8.data.regs.X1.toNat = min inst.size 4 := by
    show (s8.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [hm8.regs .X1 _ rfl]
    have h23 : (s7.data.regs.getXReg .X23).toBitVec.toNat = inst.size := by
      rw [hreg7 .X23 (by simp), hn]; exact congrArg UInt64.toNat hI.args.x23
    have e23 : (s7.data.regs.getXReg .X23).toBitVec = BitVec.ofNat 64 inst.size :=
      BitVec.eq_of_toNat_eq (by rw [h23, BitVec.toNat_ofNat]; omega)
    sym_simp
    simp only [Env.ofMachine_regs, e23]
    by_cases hc : inst.size < 4
    · have : (BitVec.ofNat 64 inst.size).ult 4#64 = true := by
        simp [BitVec.ult]; omega
      simp only [this, ite_true, BitVec.toNat_ofNat]
      omega
    · have : (BitVec.ofNat 64 inst.size).ult 4#64 = false := by
        simp [BitVec.ult]; omega
      simp only [this, Bool.false_eq_true, ite_false]
      show 4 = _
      omega
  have hw2' : s8.data.regs.X2.toBitVec = fbA m0 + BitVec.ofNat 64 568 :=
    (hm8.regs .X2 _ rfl).trans (by
      show fbA m0 + BitVec.ofInt 64 568 = _
      rw [show BitVec.ofInt 64 568 = BitVec.ofNat 64 568 from rfl])
  have hw3 : s8.data.regs.X3.toNat = 16 := by
    show (s8.data.regs.getXReg .X3).toBitVec.toNat = 16
    rw [hm8.regs .X3 _ rfl]; rfl
  have hir : ewsRegion m0.regs.X1.toBitVec inst.size ∈ rsOf m0 inst.size := by simp
  obtain ⟨hi1, hi2, hi3⟩ := arg_sub hpre hb8 hir hinst (o := 0) (l := min inst.size 4)
    (by omega) (n := eqKernelStack) (by decide)
  refine call_then hpc8 heq ⟨hb8.stackOk hS (by decide) (by decide), by rw [hw1]; omega,
    ⟨by rw [hw0, hw1]; exact hi1, by rw [hw0, hw1]; exact hi2⟩,
    ⟨by rw [hw2', hw3]; exact local_readable hpre hb8 (by decide),
      by rw [hw2', hw3]; exact local_offStack hpre hb8 (by decide) (by decide)⟩, ?_⟩
    fun s9 hpc9 hpost9 ↦ ?_
  · rw [hw0, hw1, hw2', hw3, Nat.mul_zero, NativeRustcVm.addr_add_zero]
    have := arg_local_apart hpre hir (o := 568) (n := 16 * 16) (by decide)
    unfold Apart at this ⊢
    simp only [ewsRegion] at this
    omega
  obtain ⟨hpost, hch9, hsv9⟩ := hpost9
  have hpow : 2 ^ min inst.size 4 ≤ 16 := by
    rcases Nat.le_total inst.size 4 with h | h
    · rw [Nat.min_eq_left h]
      exact Nat.le_trans (Nat.pow_le_pow_right (by decide) h) (by decide)
    · rw [Nat.min_eq_right h]; decide
  have hsl9 : slice s8.data s8.data.regs.X0 s8.data.regs.X1 = inst.extract 0 4 := by
    unfold slice
    rw [hw0, hw1, hi3, extract_zero, List.drop_zero,
      show min inst.size 4 = min inst.toList.length 4 by rw [Array.length_toList], take_min4]
  rw [hw1, hw3, ite_eq_left hpow, hsl9, hw2'] at hpost
  obtain ⟨hr9, hx9, hmu⟩ := hpost
  have hch9' : SameOutside s8.data.dmem s9.data.dmem (fun p ↦
      InRange (fbA m0 + BitVec.ofNat 64 568) (16 * 16) p ∨
        InRange (stackBelow s8.data eqKernelStack) eqKernelStack p) := by
    have := hch9; rwa [hw2', hw3] at this
  have hb9 : Body m0 s9.data :=
    hb8.call_local (n := eqKernelStack) (lo := 1312) hS (by decide) slots_le (by decide) hws hch9'
      (fun p h ↦ by
        rcases h with h | h
        · exact Or.inr (Or.inr (inRange_mono h (by decide)))
        · exact Or.inl h) hsv9
  -- `b10`: it succeeded
  have hx0'' : (s9.data.regs.getXReg .X0).toBitVec = 1#64 := by
    show s9.data.regs.X0.toBitVec = _; rw [hr9]; rfl
  refine exec_at (b10_in_code.trans hp.1 (by simp [b10])) e10 (Env.wf_nil _) hpc9 (match_nil _)
    fun s10 hm10 hpc10 ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.FirstClaim.b10_length, NativeRustcVmArm.Vm.FirstClaim.b10Length] at hpc10
  sym_simp at hpc10
  simp only [Env.ofMachine_regs, hx0''] at hpc10
  rw [ite_eq_right (by decide)] at hpc10
  have hb10 : Body m0 s10.data :=
    hb9.of_block (match_nil _) hm10 (Env.wf_nil _) rfl all_slots (by decide)
  have hd10 : s10.data.dmem = s9.data.dmem := hm10.dmem_eq (Env.wf_nil _) rfl
  have k10 := KeccakGkr.Match.regs_keep (match_nil _) hm10
    [.X1, .X19, .X21, .X22, .X23, .X24, .X25, .X26] (by decide)
  have hreg10 : ∀ r ∈ [XReg.X19, .X21, .X22, .X23, .X24],
      s10.data.regs.getXReg r = s.data.regs.getXReg r := by
    intro r hr
    have hr' : r ∈ [XReg.X1, .X19, .X21, .X22, .X23, .X24, .X25, .X26] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h | h <;> simp [h]
    rw [k10 r hr', ← hreg7 r hr, ← k8 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hsv9.1 _ rfl
  have hin9 : ∀ p, InRange (fbA m0 + BitVec.ofNat 64 568) (16 * 16) p →
      InRange (fbA m0 + BitVec.ofNat 64 560) 264 p := fun p h ↦
    inRange_mono (c := 8) (n := 256) (by rwa [NativeRustcVm.addr_add_add]) (by decide)
  have hR9 : ∀ p, (InRange (fbA m0 + BitVec.ofNat 64 568) (16 * 16) p ∨
      InRange (stackBelow s8.data eqKernelStack) eqKernelStack p) →
      InRange (stackBelow s8.data eqKernelStack) eqKernelStack p ∨
        NativeRustcVm.InAny (wsOf m0) p ∨ InRange (fbA m0 + BitVec.ofNat 64 560) 264 p :=
    fun p h ↦ h.elim (fun h ↦ Or.inr (Or.inr (hin9 p h))) Or.inl
  refine .done _ ⟨hpc10, hb10, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show s10.data.regs.getXReg .X19 = _
    rw [hreg10 .X19 (by simp)]; exact hI.args.x19
  · show s10.data.regs.getXReg .X22 = _
    rw [hreg10 .X22 (by simp)]; exact hI.args.x22
  · show s10.data.regs.getXReg .X23 = _
    rw [hreg10 .X23 (by simp)]; exact hI.args.x23
  · show s10.data.regs.getXReg .X24 = _
    rw [hreg10 .X24 (by simp)]; exact hI.args.x24
  · show s10.data.regs.getXReg .X21 = _
    rw [hreg10 .X21 (by simp)]; exact hI.x21
  · show s10.data.regs.getXReg .X25 = _
    rw [k10 .X25 (by simp), hsv9.1 .X25 rfl]; exact h25
  · show s10.data.regs.getXReg .X26 = _
    rw [k10 .X26 (by simp), hsv9.1 .X26 rfl]; exact h26'
  · show (s10.data.regs.getXReg .X1).toNat = _
    rw [k10 .X1 (by simp)]
    show s9.data.regs.X1.toNat = _
    rw [hx9, NativeVm.Math.Keccak.eqKernel_size, Array.size_extract]
    congr 1
    omega
  · rw [hd10]
    have hl : 8 + (NativeRustcVm.wordBytes m0.regs.X7).length ≤ 560 := by
      rw [NativeRustcVm.length_wordBytes]; decide
    exact local_keep' hpre hb8 (local_keep' hpre hb7 hseg7 (by omega) (n := 0) (by decide)
      (by decide) (Or.inl hl) hso8 fun _ h ↦ Or.inr (Or.inr h)) (by omega) (by decide) (by decide)
      (Or.inl hl) hch9' hR9
  · rw [hd10]
    exact ws_keep hpre hb8 hwr (n := eqKernelStack) (by decide) (o' := 560) (n' := 264) (by decide)
      (show 16 * 1600 ≤ weightsBytes by decide) (ws_keep hpre hb7 hwr (n := 0) (by decide)
        (o' := 560) (n' := 264) (by decide) (show 16 * 1600 ≤ weightsBytes by decide) hw7 hso8
        fun _ h ↦ Or.inr h) hch9'
      fun p h ↦ h.elim (fun h ↦ Or.inr (hin9 p h)) Or.inl
  · rw [hd10]; exact hmu

end

end NativeRustcVmArm.KeccakGkr.FirstClaim
