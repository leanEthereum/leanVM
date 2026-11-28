module

public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.KeccakGkr.FirstClaim.Tail

/-!
# `first_claim`: the result

`b15` computes the claim's value `committed + last` (X20, X21) and copies the instance weights to
the result, `b16` copies the point; `b17` stores `Some`'s tag and the value; `b19` restores the
registers and returns (`finish`).
-/

namespace NativeRustcVmArm.KeccakGkr.FirstClaim

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model LeanVM.Protocol.Verifier
open NativeRustcVmArm.Vm.FirstClaim NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVm (Region)
open NativeRustcVm.KeccakGkr (claimBytes weightsBytes)

public section

variable [NativeRustcArm.Host] {inst segment lanePoint output : Array EW} {m0 : MachineData} {k : Nat}

/-- **`b15` to `b19`**: from the claim in the frame to the return. -/
theorem finish (hp : Placed code k) (hpre : FirstClaimPre inst segment lanePoint output m0)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FirstClaim.b15Offset))
    (hI : PDone m0 inst segment lanePoint output s.data) :
    Eventually (step1 Host.exe)
      (fun s' ↦ s'.pc = retOf m0 ∧ FirstClaimPost inst segment lanePoint output m0 s'.data) s := by
  have hS := hpre.1
  have hA := pre_areas hpre
  have hws := wsOff hpre
  have h1408 : 1408 ≤ firstClaimStack := by decide
  obtain ⟨hmap, hnw, -⟩ := frame_ok hS h1408
  have hwo : (⟨outA m0, 8 + claimBytes⟩ : Region) ∈ wsOf m0 := by simp
  have hook := Areas.ok hA (Or.inl hwo)
  have hook' : (outA m0).toNat + 776 ≤ 2 ^ 64 := hook.2
  -- `b15`: the value, `memcpy` of the instance weights
  have hwf0 := wf_one (m := s.data) (Mapped.kept' hmap hI.body.kept) hnw
  have hm0 : Match (Env.ofMachine s.data [(fbA m0, 1408)]) bodyS s.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h1408 rfl, trivial⟩
      (by rw [hI.body.sp]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_at (b15_in_code.trans hp.1 (by simp [b15])) e15 hwf0 hpc hm0 fun s1 hm1 hpc1 ↦ ?_
  have hb1 : Body m0 s1.data := hI.body.of_block hm0 hm1 hwf0 rfl all_slots (by decide)
  have hd1 : s1.data.dmem = s.data.dmem := hm1.dmem_eq hwf0 rfl
  have k1 := KeccakGkr.Match.regs_keep hm0 hm1 [.X19] (by decide)
  have l8 := load_word (env := Env.ofMachine s.data [(fbA m0, 1408)]) (r := 0) (off := 8) hI.c1
  have h19e : (s.data.regs.getXReg .X19).toBitVec = outA m0 := congrArg UInt64.toBitVec hI.x19
  have hv20 : s1.data.regs.X20 = (lastOf segment lanePoint output).c0 ^^^ m0.regs.X6 := by
    apply UInt64.toBitVec_inj.mp
    show (s1.data.regs.getXReg .X20).toBitVec = _
    rw [hm1.regs .X20 _ rfl]
    sym_simp
    simp only [Env.ofMachine_regs, show s.data.regs.getXReg .X25 = _ from hI.x25,
      show s.data.regs.getXReg .X21 = _ from hI.x21]
    simp [UInt64.toBitVec_xor]
  have hv21 : s1.data.regs.X21 = (lastOf segment lanePoint output).c1 ^^^ m0.regs.X7 := by
    apply UInt64.toBitVec_inj.mp
    show (s1.data.regs.getXReg .X21).toBitVec = _
    rw [hm1.regs .X21 _ rfl]
    sym_simp
    simp only [Env.ofMachine_regs, show s.data.regs.getXReg .X26 = _ from hI.x26, l8]
    simp [UInt64.toBitVec_xor]
  have hx0 : s1.data.regs.X0.toBitVec = outA m0 + BitVec.ofNat 64 24 := by
    show (s1.data.regs.getXReg .X0).toBitVec = _
    rw [hm1.regs .X0 _ rfl]
    sym_simp
    simp only [Env.ofMachine_regs, h19e]
  have hx1 : s1.data.regs.X1.toBitVec = fbA m0 + BitVec.ofNat 64 560 :=
    (hm1.regs .X1 _ rfl).trans (by
      show fbA m0 + BitVec.ofInt 64 560 = _
      rw [show BitVec.ofInt 64 560 = BitVec.ofNat 64 560 from rfl])
  have hx2 : s1.data.regs.X2.toNat = 264 := by
    show (s1.data.regs.getXReg .X2).toBitVec.toNat = 264
    rw [hm1.regs .X2 _ rfl]; rfl
  have hso1 := sub_ok hook (o := 24) (n := 264) (by show 24 + 264 ≤ 8 + 768; decide)
  have hl1 := local_readable hpre hb1 (o := 560) (n := 264) (by decide)
  refine call_then hpc1 hmemcpy ⟨?_, ?_, ?_, ?_, ?_⟩ fun s2 hpc2 hpost2 ↦ ?_
  · rw [hx0, hx2]; exact Mapped.kept' hso1.1 hb1.kept
  · rw [hx1, hx2]; exact hl1.1
  · rw [hx0, hx2]; exact hso1.2
  · rw [hx1, hx2]; exact hl1.2
  · rw [hx0, hx1, hx2]; exact out_local_apart hpre (by decide) (by decide) (by decide) (by decide)
  obtain ⟨-, hcp2, hsame2, hsv2⟩ := hpost2
  rw [hx0, hx1, hx2] at hcp2
  rw [hx0, hx2] at hsame2
  have hb2 : Body m0 s2.data :=
    hb1.call (n := 0) hS (by decide) slots_le' hws hsame2
      (fun p h ↦ Or.inr ⟨_, hwo, inRange_mono h (by show 24 + 264 ≤ 8 + 768; decide)⟩) hsv2
  have hmu1 : NativeRustcVm.BufEWAt s1.data.dmem (fbA m0 + BitVec.ofNat 64 560) 16
      (eqKernel (inst.extract 0 4)).toList := by
    rw [hd1]; exact hI.mu
  have hmuO2 : NativeRustcVm.BufEWAt s2.data.dmem (outA m0 + BitVec.ofNat 64 24) 16
      (eqKernel (inst.extract 0 4)).toList :=
    BufEWAt.copy hmu1 hcp2
  have hpt2 : NativeRustcVm.BufEWAt s2.data.dmem (fbA m0 + BitVec.ofNat 64 824) 30
      (pointOf inst segment).toList :=
    NativeRustcVm.Layout.BufEWAt.of_same (by rw [hd1]; exact hI.pt)
      (local_same_out hpre (o := 824) (n := 488) (o' := 24) (n' := 264) (by decide) (by decide)
        (by decide) hsame2) (by decide)
  have hw2 : ElemsAt s2.data.dmem (wtsA m0) (wOf (eqKernel lanePoint)) 1600 :=
    w_keep_out hpre (by rw [hd1]; exact hI.w) hsame2 fun p h ↦ inRange_mono h (by decide)
  -- `b16`: `memcpy` of the point
  have hwf2 := wf_one (m := s2.data) (Mapped.kept' hmap hb2.kept) hnw
  have hm2 : Match (Env.ofMachine s2.data [(fbA m0, 1408)]) bodyS s2.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h1408 rfl, trivial⟩
      (by rw [hb2.sp]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_at (b16_in_code.trans hp.1 (by simp [b16])) e16 hwf2 hpc2 hm2 fun s3 hm3 hpc3 ↦ ?_
  have hb3 : Body m0 s3.data := hb2.of_block hm2 hm3 hwf2 rfl all_slots (by decide)
  have hd3 : s3.data.dmem = s2.data.dmem := hm3.dmem_eq hwf2 rfl
  have k3 := KeccakGkr.Match.regs_keep hm2 hm3 [.X19, .X20, .X21] (by decide)
  have e19' : (s2.data.regs.getXReg .X19).toBitVec = outA m0 := by
    rw [hsv2.1 .X19 rfl, k1 .X19 (by simp)]; exact h19e
  have hy0 : s3.data.regs.X0.toBitVec = outA m0 + BitVec.ofNat 64 288 := by
    show (s3.data.regs.getXReg .X0).toBitVec = _
    rw [hm3.regs .X0 _ rfl]
    sym_simp
    simp only [Env.ofMachine_regs, e19']
  have hy1 : s3.data.regs.X1.toBitVec = fbA m0 + BitVec.ofNat 64 824 :=
    (hm3.regs .X1 _ rfl).trans (by
      show fbA m0 + BitVec.ofInt 64 824 = _
      rw [show BitVec.ofInt 64 824 = BitVec.ofNat 64 824 from rfl])
  have hy2 : s3.data.regs.X2.toNat = 488 := by
    show (s3.data.regs.getXReg .X2).toBitVec.toNat = 488
    rw [hm3.regs .X2 _ rfl]; rfl
  have hso3 := sub_ok hook (o := 288) (n := 488) (by show 288 + 488 ≤ 8 + 768; decide)
  have hl3 := local_readable hpre hb3 (o := 824) (n := 488) (by decide)
  refine call_then hpc3 hmemcpy ⟨?_, ?_, ?_, ?_, ?_⟩ fun s4 hpc4 hpost4 ↦ ?_
  · rw [hy0, hy2]; exact Mapped.kept' hso3.1 hb3.kept
  · rw [hy1, hy2]; exact hl3.1
  · rw [hy0, hy2]; exact hso3.2
  · rw [hy1, hy2]; exact hl3.2
  · rw [hy0, hy1, hy2]; exact out_local_apart hpre (by decide) (by decide) (by decide) (by decide)
  obtain ⟨-, hcp4, hsame4, hsv4⟩ := hpost4
  rw [hy0, hy1, hy2] at hcp4
  rw [hy0, hy2] at hsame4
  have hb4 : Body m0 s4.data :=
    hb3.call (n := 0) hS (by decide) slots_le' hws hsame4
      (fun p h ↦ Or.inr ⟨_, hwo, inRange_mono h (by show 288 + 488 ≤ 8 + 768; decide)⟩) hsv4
  have hptO4 : NativeRustcVm.BufEWAt s4.data.dmem (outA m0 + BitVec.ofNat 64 288) 30
      (pointOf inst segment).toList :=
    BufEWAt.copy (by rw [hd3]; exact hpt2) hcp4
  have hmuO4 : NativeRustcVm.BufEWAt s4.data.dmem (outA m0 + BitVec.ofNat 64 24) 16
      (eqKernel (inst.extract 0 4)).toList :=
    NativeRustcVm.Layout.BufEWAt.of_same (by rw [hd3]; exact hmuO2)
      (out_same hsame4 (o := 24) (n := 264) (o' := 288) (n' := 488) (by decide) (by decide)
        (by decide) fun _ h ↦ h) (by decide)
  have hw4 : ElemsAt s4.data.dmem (wtsA m0) (wOf (eqKernel lanePoint)) 1600 :=
    w_keep_out hpre (by rw [hd3]; exact hw2) hsame4 fun p h ↦ inRange_mono h (by decide)
  have r4 : ∀ r ∈ [XReg.X19, .X20, .X21], s4.data.regs.getXReg r = s1.data.regs.getXReg r := by
    intro r hr
    have e := k3 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact (hsv4.1 _ rfl).trans (e.trans (hsv2.1 _ rfl))
  -- `b17`: `Some`'s tag and the value
  have hwf4 : (Env.ofMachine s4.data [(outA m0, 776)]).WF :=
    wf_one (Mapped.kept' hook.1 hb4.kept) hook.2
  have hm4 : Match (Env.ofMachine s4.data [(outA m0, 776)]) outS s4.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
      ⟨by
        show (s4.data.regs.getXReg .X19).toBitVec = outA m0 + BitVec.ofInt 64 0
        rw [r4 .X19 (by simp), k1 .X19 (by simp), h19e, show BitVec.ofInt 64 0 = 0#64 from rfl,
          BitVec.add_zero], trivial⟩ trivial trivial trivial
  refine exec_at (b17_in_code.trans hp.1 (by simp [b17])) e17 hwf4 hpc4 hm4 fun s5 hm5 hpc5 ↦ ?_
  have hb5 : Body m0 s5.data :=
    hb4.write hS h1408 slots_le' hws hm4 hm5 hwf4 rfl all_slots (by decide)
      fun p hw ↦ ⟨_, hwo, Written.inRange (r := 0) (sz := 776) rfl hook' (by decide) hw⟩
  have hpc5' : s5.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FirstClaim.b19Offset) := by
    simp only [PcOk] at hpc5
    exact hpc5.trans (hp.label (j := NativeRustcVmArm.Vm.FirstClaim.b19Offset) NativeRustcVmArm.Vm.FirstClaim.label_9_at)
  have htag : NativeRustcVm.WordAt s5.data.dmem (outA m0) 1 := by
    have h := Sumcheck.Match.wordAt_write hm5 (r := 0) (o := 0) (v := .lit 1) rfl (by decide)
      (by decide +kernel)
    rw [NativeRustcVm.addr_add_zero] at h
    exact h
  have hval : NativeRustcVm.EWAt s5.data.dmem (outA m0 + BitVec.ofNat 64 8)
      ((⟨m0.regs.X6, m0.regs.X7⟩ : EW) + lastOf segment lanePoint output) := by
    have h := KeccakGkr.Match.ewAt_write hm5 (r := 0) (o := 8) rfl (by decide) (v0 := .reg .X20)
      (v1 := .reg .X21) (by decide +kernel) (by decide +kernel)
    have e : (⟨UInt64.ofBitVec (Sym.eval (Env.ofMachine s4.data [(outA m0, 776)]) (.reg .X20)),
        UInt64.ofBitVec (Sym.eval (Env.ofMachine s4.data [(outA m0, 776)]) (.reg .X21))⟩ : EW) =
        (⟨m0.regs.X6, m0.regs.X7⟩ : EW) + lastOf segment lanePoint output := by
      show (⟨UInt64.ofBitVec (s4.data.regs.getXReg .X20).toBitVec,
        UInt64.ofBitVec (s4.data.regs.getXReg .X21).toBitVec⟩ : EW) = _
      rw [r4 .X20 (by simp), r4 .X21 (by simp), UInt64.ofBitVec_toBitVec,
        UInt64.ofBitVec_toBitVec]
      show (⟨s1.data.regs.X20, s1.data.regs.X21⟩ : EW) =
        ⟨m0.regs.X6 ^^^ (lastOf segment lanePoint output).c0,
          m0.regs.X7 ^^^ (lastOf segment lanePoint output).c1⟩
      rw [hv20, hv21, UInt64.xor_comm, UInt64.xor_comm (lastOf segment lanePoint output).c1]
    rwa [e] at h
  have hmuO5 : NativeRustcVm.BufEWAt s5.data.dmem (outA m0 + BitVec.ofNat 64 24) 16
      (eqKernel (inst.extract 0 4)).toList :=
    NativeRustcVm.Layout.BufEWAt.of_same hmuO4
      (written_same hm5 hwf4 rfl (r := 0) rfl hook' (o := 24) (n := 264) (by decide) (by decide))
      (by decide)
  have hptO5 : NativeRustcVm.BufEWAt s5.data.dmem (outA m0 + BitVec.ofNat 64 288) 30
      (pointOf inst segment).toList :=
    NativeRustcVm.Layout.BufEWAt.of_same hptO4
      (written_same hm5 hwf4 rfl (r := 0) rfl hook' (o := 288) (n := 488) (by decide) (by decide))
      (by decide)
  have hw5 : ElemsAt s5.data.dmem (wtsA m0) (wOf (eqKernel lanePoint)) 1600 :=
    w_keep_out hpre hw4 (hm5.sameOutside hwf4) fun p hw ↦
      Written.inRange (r := 0) (sz := 776) rfl hook' (by decide) hw
  -- `b19`: the epilogue
  have hwf5 := wf_one (m := s5.data) (Mapped.kept' hmap hb5.kept) hnw
  have hm5b : Match (Env.ofMachine s5.data [(fbA m0, 1408)]) bodyS s5.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h1408 rfl, trivial⟩
      (by rw [hb5.sp]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_at (b19_in_code.trans hp.1 (by simp [b19])) e19 hwf5 hpc5' hm5b fun s6 hm6 hpc6 ↦
    .done _ ?_
  obtain ⟨hsaved, hx30, hdm⟩ := hb5.saved hm6 hwf5
    (List.mem_map.mpr ⟨(1320, .X30), by simp [slots], rfl⟩) (by decide +kernel) rfl
  have hlen : (NativeVm.Model.keccakFirstClaim inst segment lanePoint output
      ⟨m0.regs.X6, m0.regs.X7⟩).weights.toList.length = 1600 := by
    simp [NativeVm.Model.keccakFirstClaim]; rfl
  have hget : ∀ i < 1600, (NativeVm.Model.keccakFirstClaim inst segment lanePoint output
      ⟨m0.regs.X6, m0.regs.X7⟩).weights.toList.getD i 0 = wOf (eqKernel lanePoint) i := by
    intro i hi
    have hi' : i < keccakBits := hi
    simp [NativeVm.Model.keccakFirstClaim, wOf, hi']
  refine ⟨?_, by rw [hdm]; exact htag, ?_, ⟨(Array.length_toList).symm.trans hlen, ?_⟩,
    fun p hp' ↦ by rw [hdm]; exact hb5.same p hp', hsaved⟩
  · simp only [PcOk] at hpc6
    rw [hpc6]
    simp only [retOf, hx30]
  · rw [hdm]
    refine ⟨hval, ?_, ?_⟩
    · show NativeRustcVm.BufEWAt _ (outA m0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 16) 16
        (eqKernel (inst.extract 0 4)).toList
      rw [NativeRustcVm.addr_add_add]; exact hmuO5
    · show NativeRustcVm.BufEWAt _ (outA m0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 280) 30
        (pointOf inst segment).toList
      rw [NativeRustcVm.addr_add_add]; exact hptO5
  · rw [hdm]
    refine ElemsAt.ewsAt ?_
    rw [hlen]
    intro i hi
    beta_reduce
    rw [hget i hi]
    exact hw5 i hi

end

end NativeRustcVmArm.KeccakGkr.FirstClaim
