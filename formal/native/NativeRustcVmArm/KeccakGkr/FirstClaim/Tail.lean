module

public import NativeRustcVmArm.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmArm.KeccakGkr.FirstClaim.Mid
public import NativeRustcVmArm.KeccakGkr.FirstClaim.Keep

/-!
# `first_claim`: the claim's point

`b11` stores the instance weights' count at `560`, empties the point (a `Buf<EW, 30>` at `824`)
and calls `Buf::extend` with `inst`'s coordinates from `4` on; `b12` checks it succeeded; `b13`
extends the point with the segment, `b14` checks it succeeded (`tail`, to `PDone`).
-/

namespace NativeRustcVmArm.KeccakGkr.FirstClaim

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model LeanVM.Protocol.Verifier
open NativeRustcVmArm.Vm.FirstClaim NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVm (Region)
open NativeRustcVm.KeccakGkr (claimBytes weightsBytes)

@[expose] public section

/-- The claim's point: `inst`'s coordinates from `4` on, then the segment. -/
def pointOf (inst segment : Array EW) : Array EW := inst.extract 4 inst.size ++ segment

/-- **The claim in the frame**: `last` in X25, X26, the instance weights (a `Buf<EW, 16>` at
`560`) and the point (a `Buf<EW, 30>` at `824`). -/
structure PDone [Labels] (m0 : MachineData) (inst segment lanePoint output : Array EW)
    (st : MachineData) : Prop where
  body : Body m0 st
  x19 : st.regs.X19 = m0.regs.X0
  x21 : st.regs.X21 = m0.regs.X6
  x25 : st.regs.X25 = (lastOf segment lanePoint output).c0
  x26 : st.regs.X26 = (lastOf segment lanePoint output).c1
  c1 : NativeRustcVm.WordAt st.dmem (fbA m0 + BitVec.ofNat 64 8) m0.regs.X7
  w : ElemsAt st.dmem (wtsA m0) (wOf (eqKernel lanePoint)) 1600
  mu : NativeRustcVm.BufEWAt st.dmem (fbA m0 + BitVec.ofNat 64 560) 16
    (eqKernel (inst.extract 0 4)).toList
  pt : NativeRustcVm.BufEWAt st.dmem (fbA m0 + BitVec.ofNat 64 824) 30 (pointOf inst segment).toList

end

public section

theorem extract_from (xs : Array EW) (n : Nat) :
    xs.extract n xs.size = (xs.toList.drop n).toArray := by
  apply Array.toList_inj.mp
  simp [Array.toList_extract, List.extract]

variable [NativeRustcArm.Host] {inst segment lanePoint output : Array EW} {m0 : MachineData} {k : Nat}

/-- **`b11` to `b14`**. -/
theorem tail (hp : Placed code k) (hpre : FirstClaimPre inst segment lanePoint output m0)
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FirstClaim.b11Offset))
    (hI : MDone m0 inst segment lanePoint output s.data) :
    Eventually (step1 Host.exe)
      (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FirstClaim.b15Offset) ∧ PDone m0 inst segment lanePoint output s'.data)
      s := by
  have hS := hpre.1
  have hws := wsOff hpre
  have h1408 : 1408 ≤ firstClaimStack := by decide
  obtain ⟨hmap, hnw, hfb⟩ := frame_ok hS h1408
  have hnw' : (fbA m0).toNat + 1408 ≤ 2 ^ 64 := hnw
  have hn : inst.size = m0.regs.X2.toNat := hpre.2.1
  have hn30 : inst.size ≤ 30 := hpre.2.2.1
  have hinst : NativeRustcVm.EWsAt m0.dmem m0.regs.X1.toBitVec inst.toList := hpre.2.2.2.1
  have hsg : segment.size = 1 := hpre.2.2.2.2.1
  have hsgm : NativeRustcVm.EWsAt m0.dmem m0.regs.X3.toBitVec segment.toList := hpre.2.2.2.2.2.1
  have hwr : (⟨wtsA m0, weightsBytes⟩ : Region) ∈ wsOf m0 := by simp
  have hir : ewsRegion m0.regs.X1.toBitVec inst.size ∈ rsOf m0 inst.size := by simp
  have hsr : ewsRegion m0.regs.X3.toBitVec segment.size ∈ rsOf m0 inst.size := by
    rw [hsg]; simp
  have hmus : (eqKernel (inst.extract 0 4)).size ≤ 16 := by
    rw [NativeVm.Math.Keccak.eqKernel_size, Array.size_extract]
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (show min 4 inst.size - 0 ≤ 4 by omega))
      (by decide)
  have hSP := m0.regs.SP.toBitVec.isLt
  have hN : firstClaimStack ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  rw [stack_eq] at hN
  -- `b11`: the instance weights' count, the point emptied
  have hwf0 := wf_one (m := s.data) (Mapped.kept' hmap hI.body.kept) hnw
  have hm0 : Match (Env.ofMachine s.data [(fbA m0, 1408)]) bodyS s.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h1408 rfl, trivial⟩
      (by rw [hI.body.sp]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_at (b11_in_code.trans hp.1 (by simp [b11])) e11 hwf0 hpc hm0 fun s1 hm1 hpc1 ↦ ?_
  have hb1 : Body m0 s1.data :=
    hI.body.write_local (lo := 1312) hS h1408 slots_le (by decide) hws hm0 hm1 hwf0 rfl all_slots
      (by decide) fun p hw ↦ Or.inr (Written.inRange_le (r := 0) rfl hnw (by decide) (by decide) hw)
  have k1 := KeccakGkr.Match.regs_keep hm0 hm1
    [.X19, .X21, .X22, .X23, .X24, .X25, .X26] (by decide)
  have hc1 : NativeRustcVm.WordAt s1.data.dmem (fbA m0 + BitVec.ofNat 64 8) m0.regs.X7 :=
    NativeRustcVm.Layout.WordAt.of_same hI.c1
      (written_same hm1 hwf0 rfl (r := 0) rfl hnw (o := 8) (n := 8) (by decide) (by decide))
      (Nat.le_refl _)
  have hmu1 : NativeRustcVm.EWsAt s1.data.dmem (fbA m0 + BitVec.ofNat 64 568)
      (eqKernel (inst.extract 0 4)).toList :=
    NativeRustcVm.Layout.BytesAt.of_same hI.mu
      (written_same hm1 hwf0 rfl (r := 0) rfl hnw (o := 568) (n := 256) (by decide) (by decide))
      (by rw [length_flatMap_ewBytes, Array.length_toList]; omega)
  have hcnt : NativeRustcVm.WordAt s1.data.dmem (fbA m0 + BitVec.ofNat 64 560)
      (eqKernel (inst.extract 0 4)).toList.length.toUInt64 := by
    have h := Sumcheck.Match.wordAt_write hm1 (r := 0) (o := 560) (v := .reg .X1) rfl (by decide)
      (by decide +kernel)
    have e : UInt64.ofBitVec (Sym.eval (Env.ofMachine s.data [(fbA m0, 1408)]) (.reg .X1)) =
        (eqKernel (inst.extract 0 4)).toList.length.toUInt64 := by
      show UInt64.ofBitVec s.data.regs.X1.toBitVec = _
      rw [UInt64.ofBitVec_toBitVec, Array.length_toList, ← hI.x1]
      exact UInt64.ofNat_toNat.symm
    rwa [e] at h
  have hz : NativeRustcVm.WordAt s1.data.dmem (fbA m0 + BitVec.ofNat 64 824) 0 :=
    Sumcheck.Match.wordAt_write hm1 (r := 0) (o := 824) (v := .lit 0) rfl (by decide)
      (by decide +kernel)
  have hmuB1 : NativeRustcVm.BufEWAt s1.data.dmem (fbA m0 + BitVec.ofNat 64 560) 16
      (eqKernel (inst.extract 0 4)).toList :=
    ⟨by rw [Array.length_toList]; exact hmus, hcnt, by
      show NativeRustcVm.EWsAt _ (fbA m0 + BitVec.ofNat 64 560 + BitVec.ofNat 64 8) _
      rw [NativeRustcVm.addr_add_add]; exact hmu1⟩
  have hw1 : ElemsAt s1.data.dmem (wtsA m0) (wOf (eqKernel lanePoint)) 1600 :=
    ws_keep hpre hI.body hwr (n := 0) (by decide) (o' := 560) (n' := 752) (by decide)
      (show 16 * 1600 ≤ weightsBytes by decide) hI.w (hm1.sameOutside hwf0) fun p hw ↦
        Or.inr (Written.inRange_sub (r := 0) (lo := 560) (hi := 1312) rfl hnw (by decide)
          (by decide) hw)
  -- the arguments of `extend`
  have hx0 : s1.data.regs.X0.toBitVec = fbA m0 + BitVec.ofNat 64 824 :=
    (hm1.regs .X0 _ rfl).trans (by
      show fbA m0 + BitVec.ofInt 64 824 = _
      rw [show BitVec.ofInt 64 824 = BitVec.ofNat 64 824 from rfl])
  have h23 : (s.data.regs.getXReg .X23).toBitVec.toNat = inst.size := by
    rw [hn]; exact congrArg UInt64.toNat hI.args.x23
  have e23 : (s.data.regs.getXReg .X23).toBitVec = BitVec.ofNat 64 inst.size :=
    BitVec.eq_of_toNat_eq (by rw [h23, BitVec.toNat_ofNat]; omega)
  have e24 : (s.data.regs.getXReg .X24).toBitVec = m0.regs.X1.toBitVec :=
    congrArg UInt64.toBitVec hI.args.x24
  have hx2 : s1.data.regs.X2.toNat = inst.size - 4 := by
    show (s1.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [hm1.regs .X2 _ rfl]
    sym_simp
    simp only [Env.ofMachine_regs, e23]
    by_cases hc : inst.size < 4
    · have : (BitVec.ofNat 64 inst.size).ult 4#64 = true := by simp [BitVec.ult]; omega
      simp only [this, ite_true]
      simp; omega
    · have : (BitVec.ofNat 64 inst.size).ult 4#64 = false := by simp [BitVec.ult]; omega
      simp only [this, Bool.false_eq_true, ite_false]
      simp [BitVec.toNat_sub]
      omega
  have hx1 : s1.data.regs.X1.toBitVec =
      if inst.size < 4 then 8#64 else m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * 4) := by
    show (s1.data.regs.getXReg .X1).toBitVec = _
    rw [hm1.regs .X1 _ rfl]
    sym_simp
    simp only [Env.ofMachine_regs, e23, e24]
    by_cases hc : inst.size < 4
    · have : (BitVec.ofNat 64 inst.size).ult 4#64 = true := by simp [BitVec.ult]; omega
      simp only [this, ite_true, ite_eq_left hc]
    · have : (BitVec.ofNat 64 inst.size).ult 4#64 = false := by simp [BitVec.ult]; omega
      simp only [this, Bool.false_eq_true, ite_false, ite_eq_right hc]
  have hXr : Readable s1.data s1.data.regs.X1.toBitVec (16 * s1.data.regs.X2.toNat) ∧
      Apart (fbA m0 + BitVec.ofNat 64 824) (8 + 16 * 30) s1.data.regs.X1.toBitVec
        (16 * s1.data.regs.X2.toNat) ∧
      slice s1.data s1.data.regs.X1 s1.data.regs.X2 = inst.extract 4 inst.size := by
    unfold slice
    rw [hx2, hx1, extract_from]
    by_cases hc : inst.size < 4
    · rw [ite_eq_left hc, show inst.size - 4 = 0 by omega, Nat.mul_zero,
        List.drop_eq_nil_of_le (by rw [Array.length_toList]; omega)]
      refine ⟨⟨fun i hi ↦ absurd hi (Nat.not_lt_zero _), by unfold NoWrap; decide⟩, ?_, rfl⟩
      unfold Apart
      right
      rw [toNat_add_ofNat' (by omega)]
      simp only [BitVec.toNat_ofNat]
      omega
    · rw [ite_eq_right hc]
      obtain ⟨hr1, -, hr3⟩ := arg_sub hpre hb1 hir hinst (o := 4) (l := inst.size - 4)
        (by omega) (n := 0) (by decide)
      refine ⟨hr1, (arg_local_apart' hpre hir (o := 16 * 4) (l := 16 * (inst.size - 4))
        (by simp only [ewsRegion]; omega) (o' := 824) (n' := 8 + 16 * 30) (by decide)).symm, ?_⟩
      rw [hr3, List.take_of_length_le (by simp)]
  -- `extend` with `inst`'s coordinates from `4` on
  refine call_then hpc1 hext ⟨by rw [hx0, NativeRustcVm.wordOf_of_wordAt hz]; decide,
    by rw [hx0]; exact local_readable hpre hb1 (by decide), hXr.1, by rw [hx0]; exact hXr.2.1⟩
    fun s2 hpc2 hpost2 ↦ ?_
  obtain ⟨hpost, hch2, hsv2⟩ := hpost2
  rw [hx0, NativeRustcVm.wordOf_of_wordAt hz, hx2] at hpost
  simp only [UInt64.toNat_zero, Nat.zero_add] at hpost
  rw [ite_eq_left (by omega)] at hpost
  obtain ⟨hr0, hpt⟩ := hpost
  have hbuf0 : NativeRustcVm.bufEWOf s1.data.dmem (fbA m0 + BitVec.ofNat 64 824) = [] := by
    unfold NativeRustcVm.bufEWOf
    rw [NativeRustcVm.wordOf_of_wordAt hz]
    rfl
  rw [hbuf0, hXr.2.2, List.nil_append] at hpt
  rw [hx0] at hch2
  have hR2 : ∀ p, (InRange (fbA m0 + BitVec.ofNat 64 824) (8 + 16 * 30) p ∨
      InRange (stackBelow s1.data bufExtendStack) bufExtendStack p) →
      InRange (stackBelow s1.data bufExtendStack) bufExtendStack p ∨
        NativeRustcVm.InAny (wsOf m0) p ∨
        InRange (fbA m0 + BitVec.ofNat 64 824) (8 + 16 * 30) p :=
    fun p h ↦ h.elim (fun h ↦ Or.inr (Or.inr h)) Or.inl
  have hb2 : Body m0 s2.data :=
    hb1.call_local (n := bufExtendStack) (lo := 1312) hS (by decide) slots_le (by decide) hws hch2
      (fun p h ↦ by
        rcases h with h | h
        · exact Or.inr (Or.inr (inRange_mono h (by decide)))
        · exact Or.inl h) hsv2
  have hc12 : NativeRustcVm.WordAt s2.data.dmem (fbA m0 + BitVec.ofNat 64 8) m0.regs.X7 :=
    NativeRustcVm.Layout.WordAt.of_same hc1
      (local_same hpre hb1 (o := 8) (n := 8) (by decide) (by decide) (by decide) (by decide) hch2
        hR2) (Nat.le_refl _)
  have hmu2 : NativeRustcVm.BufEWAt s2.data.dmem (fbA m0 + BitVec.ofNat 64 560) 16
      (eqKernel (inst.extract 0 4)).toList :=
    NativeRustcVm.Layout.BufEWAt.of_same hmuB1
      (local_same hpre hb1 (o := 560) (n := 264) (by decide) (by decide) (by decide) (by decide)
        hch2 hR2) (by decide)
  have hw2 : ElemsAt s2.data.dmem (wtsA m0) (wOf (eqKernel lanePoint)) 1600 :=
    ws_keep hpre hb1 hwr (n := bufExtendStack) (by decide) (o' := 824) (n' := 8 + 16 * 30)
      (by decide) (show 16 * 1600 ≤ weightsBytes by decide) hw1 hch2 fun p h ↦ h.elim Or.inr Or.inl
  -- `b12`: it succeeded
  have hx0' : (s2.data.regs.getXReg .X0).toBitVec = 1#64 := by
    show s2.data.regs.X0.toBitVec = _; rw [hr0]; rfl
  refine exec_at (b12_in_code.trans hp.1 (by simp [b12])) e12 (Env.wf_nil _) hpc2 (match_nil _)
    fun s3 hm3 hpc3 ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.FirstClaim.b12_length, NativeRustcVmArm.Vm.FirstClaim.b12Length] at hpc3
  sym_simp at hpc3
  simp only [Env.ofMachine_regs, hx0'] at hpc3
  rw [ite_eq_right (by decide)] at hpc3
  have hb3 : Body m0 s3.data :=
    hb2.of_block (match_nil _) hm3 (Env.wf_nil _) rfl all_slots (by decide)
  have k3 := KeccakGkr.Match.regs_keep (match_nil _) hm3
    [.X19, .X21, .X22, .X23, .X24, .X25, .X26] (by decide)
  have hd3 : s3.data.dmem = s2.data.dmem := hm3.dmem_eq (Env.wf_nil _) rfl
  -- `b13`: `extend` with the segment
  have hwf3 := wf_one (m := s3.data) (Mapped.kept' hmap hb3.kept) hnw
  have hm3b : Match (Env.ofMachine s3.data [(fbA m0, 1408)]) bodyS s3.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h1408 rfl, trivial⟩
      (by rw [hb3.sp]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_at (b13_in_code.trans hp.1 (by simp [b13])) e13 hwf3 hpc3 hm3b fun s4 hm4 hpc4 ↦ ?_
  have hb4 : Body m0 s4.data := hb3.of_block hm3b hm4 hwf3 rfl all_slots (by decide)
  have k4 := KeccakGkr.Match.regs_keep hm3b hm4
    [.X19, .X21, .X22, .X23, .X24, .X25, .X26] (by decide)
  have hd4 : s4.data.dmem = s3.data.dmem := hm4.dmem_eq hwf3 rfl
  have hy0 : s4.data.regs.X0.toBitVec = fbA m0 + BitVec.ofNat 64 824 :=
    (hm4.regs .X0 _ rfl).trans (by
      show fbA m0 + BitVec.ofInt 64 824 = _
      rw [show BitVec.ofInt 64 824 = BitVec.ofNat 64 824 from rfl])
  have hy1 : s4.data.regs.X1.toBitVec = m0.regs.X3.toBitVec :=
    (hm4.regs .X1 _ rfl).trans (by
      show (s3.data.regs.getXReg .X22).toBitVec = _
      rw [k3 .X22 (by simp), hsv2.1 .X22 rfl, k1 .X22 (by simp)]
      exact congrArg UInt64.toBitVec hI.args.x22)
  have hy2 : s4.data.regs.X2.toNat = 1 := by
    show (s4.data.regs.getXReg .X2).toBitVec.toNat = 1
    rw [hm4.regs .X2 _ rfl]; rfl
  have hpt4 : NativeRustcVm.BufEWAt s4.data.dmem (fbA m0 + BitVec.ofNat 64 824) 30
      (inst.extract 4 inst.size).toList := by
    rw [hd4, hd3]; exact hpt
  have hlen4 : (inst.extract 4 inst.size).toList.length = inst.size - 4 := by simp
  have hcnt4 : (NativeRustcVm.wordOf s4.data.dmem (fbA m0 + BitVec.ofNat 64 824)).toNat =
      inst.size - 4 := by
    rw [NativeRustcVm.wordOf_of_wordAt hpt4.2.1, Nat.toUInt64,
      UInt64.toNat_ofNat_of_lt' (show _ < UInt64.size by simp [UInt64.size]; omega), hlen4]
  obtain ⟨hsl4, hslc4⟩ := arg_slice hpre hb4 hsr hsgm (n := 0) (by decide) hy1 (by rw [hy2, hsg])
  refine call_then hpc4 hext ⟨by rw [hy0, hcnt4]; omega,
    by rw [hy0]; exact local_readable hpre hb4 (by decide), hsl4.1, ?_⟩ fun s5 hpc5 hpost5 ↦ ?_
  · rw [hy0, hy1, hy2]
    have := arg_local_apart hpre hsr (o := 824) (n := 8 + 16 * 30) (by decide)
    rw [hsg] at this
    exact this.symm
  obtain ⟨hpost, hch5, hsv5⟩ := hpost5
  rw [hy0, hcnt4, hy2, ite_eq_left (by omega)] at hpost
  obtain ⟨hr5, hpt5⟩ := hpost
  rw [bufEWOf_eq hpt4 (by decide), hslc4, ← Array.toList_append] at hpt5
  rw [hy0] at hch5
  have hR5 : ∀ p, (InRange (fbA m0 + BitVec.ofNat 64 824) (8 + 16 * 30) p ∨
      InRange (stackBelow s4.data bufExtendStack) bufExtendStack p) →
      InRange (stackBelow s4.data bufExtendStack) bufExtendStack p ∨
        NativeRustcVm.InAny (wsOf m0) p ∨
        InRange (fbA m0 + BitVec.ofNat 64 824) (8 + 16 * 30) p :=
    fun p h ↦ h.elim (fun h ↦ Or.inr (Or.inr h)) Or.inl
  have hb5 : Body m0 s5.data :=
    hb4.call_local (n := bufExtendStack) (lo := 1312) hS (by decide) slots_le (by decide) hws hch5
      (fun p h ↦ by
        rcases h with h | h
        · exact Or.inr (Or.inr (inRange_mono h (by decide)))
        · exact Or.inl h) hsv5
  have hc14 : NativeRustcVm.WordAt s4.data.dmem (fbA m0 + BitVec.ofNat 64 8) m0.regs.X7 := by
    rw [hd4, hd3]; exact hc12
  have hmu4 : NativeRustcVm.BufEWAt s4.data.dmem (fbA m0 + BitVec.ofNat 64 560) 16
      (eqKernel (inst.extract 0 4)).toList := by
    rw [hd4, hd3]; exact hmu2
  have hw4 : ElemsAt s4.data.dmem (wtsA m0) (wOf (eqKernel lanePoint)) 1600 := by
    rw [hd4, hd3]; exact hw2
  have hc15 : NativeRustcVm.WordAt s5.data.dmem (fbA m0 + BitVec.ofNat 64 8) m0.regs.X7 :=
    NativeRustcVm.Layout.WordAt.of_same hc14
      (local_same hpre hb4 (o := 8) (n := 8) (by decide) (by decide) (by decide) (by decide) hch5
        hR5) (Nat.le_refl _)
  have hmu5 : NativeRustcVm.BufEWAt s5.data.dmem (fbA m0 + BitVec.ofNat 64 560) 16
      (eqKernel (inst.extract 0 4)).toList :=
    NativeRustcVm.Layout.BufEWAt.of_same hmu4
      (local_same hpre hb4 (o := 560) (n := 264) (by decide) (by decide) (by decide) (by decide)
        hch5 hR5) (by decide)
  have hw5 : ElemsAt s5.data.dmem (wtsA m0) (wOf (eqKernel lanePoint)) 1600 :=
    ws_keep hpre hb4 hwr (n := bufExtendStack) (by decide) (o' := 824) (n' := 8 + 16 * 30)
      (by decide) (show 16 * 1600 ≤ weightsBytes by decide) hw4 hch5 fun p h ↦ h.elim Or.inr Or.inl
  -- `b14`: it succeeded
  have hx0'' : (s5.data.regs.getXReg .X0).toBitVec = 1#64 := by
    show s5.data.regs.X0.toBitVec = _; rw [hr5]; rfl
  refine exec_at (b14_in_code.trans hp.1 (by simp [b14])) e14 (Env.wf_nil _) hpc5 (match_nil _)
    fun s6 hm6 hpc6 ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.FirstClaim.b14_length, NativeRustcVmArm.Vm.FirstClaim.b14Length] at hpc6
  sym_simp at hpc6
  simp only [Env.ofMachine_regs, hx0''] at hpc6
  rw [ite_eq_right (by decide)] at hpc6
  have hb6 : Body m0 s6.data :=
    hb5.of_block (match_nil _) hm6 (Env.wf_nil _) rfl all_slots (by decide)
  have k6 := KeccakGkr.Match.regs_keep (match_nil _) hm6 [.X19, .X21, .X25, .X26] (by decide)
  have hd6 : s6.data.dmem = s5.data.dmem := hm6.dmem_eq (Env.wf_nil _) rfl
  have hreg : ∀ r ∈ [XReg.X19, .X21, .X25, .X26],
      s6.data.regs.getXReg r = s.data.regs.getXReg r := by
    intro r hr
    have hr' : r ∈ [XReg.X19, .X21, .X22, .X23, .X24, .X25, .X26] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h <;> simp [h]
    rw [k6 r hr, ← k1 r hr']
    have e43 := (k4 r hr').trans (k3 r hr')
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact (hsv5.1 _ rfl).trans (e43.trans (hsv2.1 _ rfl))
  refine .done _ ⟨hpc6, hb6, ?_, ?_, ?_, ?_, by rw [hd6]; exact hc15, by rw [hd6]; exact hw5,
    by rw [hd6]; exact hmu5, by rw [hd6]; exact hpt5⟩
  · show s6.data.regs.getXReg .X19 = _
    rw [hreg .X19 (by simp)]; exact hI.args.x19
  · show s6.data.regs.getXReg .X21 = _
    rw [hreg .X21 (by simp)]; exact hI.x21
  · show s6.data.regs.getXReg .X25 = _
    rw [hreg .X25 (by simp)]; exact hI.x25
  · show s6.data.regs.getXReg .X26 = _
    rw [hreg .X26 (by simp)]; exact hI.x26

end

end NativeRustcVmArm.KeccakGkr.FirstClaim
