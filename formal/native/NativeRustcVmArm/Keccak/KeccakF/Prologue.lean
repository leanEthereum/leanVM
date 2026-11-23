module

public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Keccak.KeccakF.Inv
public import NativeRustcVmArm.Keccak.KeccakF.Blocks

/-!
# `keccak_f`'s prologue

`prologue_step`: from `keccak_f`'s entry, in a state satisfying `KeccakFPre`, the machine
inevitably reaches the round loop's head with the loop invariant before the first round
(`At m0 0`): the entry block (`entry`) saves X29, X30 and the callee-saved registers in the frame
and calls `memcpy` to copy the round constants to the frame at 112; the next (`load`) saves the
state pointer at 16 and loads the 25 lanes into registers and frame slots.
-/

namespace NativeRustcVmArm.KeccakF

open NativeRustcArm NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcArm.KeccakF (WordAt wordAt_of_eq wordAt_write wordAt_keep same_region load_lane')
open NativeRustcVmArm.Keccak

public section

theorem not_inRange_rc {m0 : MachineData} (hstk : StackOk m0 NativeRustcVmArm.keccakFStack)
    {o : Nat} (ho : 304 ≤ o) (ho' : o + 8 ≤ 400) : ∀ i < 8,
      ¬ InRange (frame m0 + BitVec.ofNat 64 112) 192 (frame m0 + BitVec.ofNat 64 o + BitVec.ofNat 64 i) := by
  intro i hi
  have hf := frame_noWrap hstk
  unfold NoWrap NativeRustcVmArm.keccakFStack at hf
  rw [addr_add, Hasher.inRange_add_iff (by omega) (by omega) (by decide)]
  omega

theorem inRange_frame_of_rc {m0 : MachineData} (hstk : StackOk m0 NativeRustcVmArm.keccakFStack)
    {p : BitVec 64} (h : InRange (frame m0 + BitVec.ofNat 64 112) 192 p) :
    InRange (frame m0) NativeRustcVmArm.keccakFStack p := by
  have hf := frame_noWrap hstk
  have h112 := frame_add_toNat hstk (o := 112) (by decide)
  unfold NoWrap NativeRustcVmArm.keccakFStack at hf
  rw [inRange_iff (by rw [h112]; omega), h112] at h
  unfold NativeRustcVmArm.keccakFStack
  rw [inRange_iff hf]
  omega

variable [Host]

set_option linter.unusedSimpArgs false in
/-- **The prologue.** -/
theorem prologue_step {k : Nat} (hp : Placed Vm.KeccakF.code k)
    (hmemcpy : Spec (label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) {m0 : MachineData}
    (hpre : NativeRustcVmArm.KeccakFPre m0) :
    Eventually (step1 Host.exe) (fun st => At m0 0 st.data ∧ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakF.b2Offset))
      ⟨m0, Host.addrOf k⟩ := by
  obtain ⟨hstk, ⟨hrc, hrcnw, hrcap⟩, hmap, hnw, hap, -⟩ := hpre
  have hf := frame_noWrap hstk
  have h112 := frame_add_toNat hstk (o := 112) (by decide)
  have hk0 : Vm.KeccakF.b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.KeccakF.b0Offset) :=
    Vm.KeccakF.b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let env0 := Env.ofMachine m0 [(frame m0, 400), (m0.regs.X0.toBitVec, 200)]
  have hwf0 : env0.WF :=
    Env.wf_of ⟨⟨hstk.2.2, hf⟩, ⟨hmap, hnw⟩, trivial⟩ (List.pairwise_pair.mpr hap.symm)
  have hm0 : Match env0 startEntry m0 :=
    match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, rfl, fun h => absurd h (by decide), trivial⟩
      (by
        simp only [Sym.eval, Env.base_ofMachine_eq, frame, stackBelow,
          NativeRustcVmArm.keccakFStack]
        simp)
      ⟨by simp [Sym.eval]; rfl, trivial⟩ trivial trivial trivial
  have hb0 : env0.regions[0]? = some (frame m0, 400) := rfl
  have hrc192 : rcBytes.length = 192 := length_rcBytes
  refine exec_then hk0 entry hwf0 hm0 fun st1 hm1 hpc1 => ?_
  have hx0 : st1.data.regs.X0.toBitVec = frame m0 + BitVec.ofNat 64 112 :=
    (hm1.regs .X0 _ rfl).trans (by simp [Sym.eval, env0])
  have hx1 : st1.data.regs.X1.toBitVec = NativeRustcVmArm.rcAddr :=
    (hm1.regs .X1 _ rfl).trans (by simp [Sym.eval]; rfl)
  have hx2 : st1.data.regs.X2.toNat = 192 := by
    have := hm1.regs .X2 _ rfl
    simp only [Sym.eval] at this
    rw [← UInt64.toNat_toBitVec]
    exact (congrArg BitVec.toNat this).trans (by simp)
  have hx19 : (st1.data.regs.getXReg .X19).toBitVec = m0.regs.X0.toBitVec :=
    (hm1.regs .X19 _ rfl).trans (by simp [Sym.eval, env0])
  have hsp1 : st1.data.regs.SP.toBitVec = frame m0 :=
    hm1.sp.trans (by simp [Sym.eval, env0])
  have hsame1 : SameOutside m0.dmem st1.data.dmem (InRange (frame m0) 400) :=
    same_region hm1 hwf0 hb0 (by decide)
  have hkept1 : Kept m0.dmem st1.data.dmem := hm1.kept hwf0
  -- the round constants, untouched by the entry block
  have hrc1 : BytesAt st1.data.dmem NativeRustcVmArm.rcAddr rcBytes :=
    bytesAt_of_same hsame1 hrc fun i hi =>
      not_inRange_of_apart hrcnw hf hrcap (by rw [hrc192] at hi; exact hi)
  have hpre1 : MemcpyPre st1.data := by
    unfold MemcpyPre
    simp only [hx0, hx1, hx2]
    refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, hrcnw, ?_⟩
    · rw [addr_add]
      exact hkept1 _ (hstk.2.2 (112 + i) (by unfold NativeRustcVmArm.keccakFStack; omega))
    · rw [hrc1 i (by omega)]
      rfl
    · unfold NoWrap at hf ⊢
      unfold NativeRustcVmArm.keccakFStack at hf
      omega
    · rw [show stackBelow m0 NativeRustcVmArm.keccakFStack = frame m0 from rfl] at hrcap
      unfold Apart at hrcap ⊢
      unfold NativeRustcVmArm.keccakFStack at hrcap
      omega
  refine call_then hpc1 hmemcpy hpre1 fun st2 hpc2 hpost => ?_
  obtain ⟨-, hcopy, hsame2, hsaved2⟩ := hpost
  simp only [hx0, hx1, hx2] at hcopy hsame2
  have hrcb : bytesOf st1.data.dmem NativeRustcVmArm.rcAddr 192 = rcBytes := by
    rw [← hrc192]
    exact Hasher.bytesOf_of_bytesAt hrc1
  rw [hrcb] at hcopy
  have hkept2 : Kept m0.dmem st2.data.dmem := fun p h => hsaved2.2.2 p (hkept1 p h)
  have hsame12 : SameOutside m0.dmem st2.data.dmem (InRange (frame m0) 400) := fun p hp =>
    (hsame2 p fun h => hp (inRange_frame_of_rc hstk h)).trans (hsame1 p hp)
  have hk1 : Vm.KeccakF.b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.KeccakF.b1Offset) :=
    Vm.KeccakF.b1_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let env2 := Env.ofMachine st2.data [(frame m0, 400), (m0.regs.X0.toBitVec, 200)]
  have hwf2 : env2.WF :=
    Env.wf_of ⟨⟨fun j hj => hkept2 _ (hstk.2.2 j hj), hf⟩,
      ⟨fun j hj => hkept2 _ (hmap j hj), hnw⟩, trivial⟩ (List.pairwise_pair.mpr hap.symm)
  have hm2 : Match env2 startLoad st2.data :=
    match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, rfl, fun h => absurd h (by decide), trivial⟩
      (by rw [hsaved2.2.1, hsp1]; simp [Sym.eval, env2])
      ⟨by show (st2.data.regs.getXReg .X19).toBitVec = _; rw [hsaved2.1 .X19 rfl, hx19]; simp [Sym.eval, env2], trivial⟩
      trivial trivial trivial
  have hb2 : env2.regions[0]? = some (frame m0, 400) := rfl
  have hbytes : bytesOf st2.data.dmem m0.regs.X0.toBitVec 200 =
      bytesOf m0.dmem m0.regs.X0.toBitVec 200 :=
    bytesOf_of_same hsame12 fun i hi => not_inRange_of_apart hnw hf hap hi
  have hl : ∀ {off : Nat} (j : Nat), off = 8 * j → j < 25 →
      env2.load 1 off 8 = (Keccak.lane (stAfter m0 0) j).toBitVec := fun j hoff hj => by
    rw [load_lane' hoff hj]
    show (Keccak.lane (stateOf (bytesOf st2.data.dmem m0.regs.X0.toBitVec 200)) j).toBitVec = _
    rw [hbytes]
    rfl
  have hl0 : env2.load 1 0 8 = (Keccak.lane (stAfter m0 0) 0).toBitVec := hl 0 rfl (by decide)
  have hl1 : env2.load 1 8 8 = (Keccak.lane (stAfter m0 0) 1).toBitVec := hl 1 rfl (by decide)
  have hl2 : env2.load 1 16 8 = (Keccak.lane (stAfter m0 0) 2).toBitVec := hl 2 rfl (by decide)
  have hl3 : env2.load 1 24 8 = (Keccak.lane (stAfter m0 0) 3).toBitVec := hl 3 rfl (by decide)
  have hl4 : env2.load 1 32 8 = (Keccak.lane (stAfter m0 0) 4).toBitVec := hl 4 rfl (by decide)
  have hl5 : env2.load 1 40 8 = (Keccak.lane (stAfter m0 0) 5).toBitVec := hl 5 rfl (by decide)
  have hl6 : env2.load 1 48 8 = (Keccak.lane (stAfter m0 0) 6).toBitVec := hl 6 rfl (by decide)
  have hl7 : env2.load 1 56 8 = (Keccak.lane (stAfter m0 0) 7).toBitVec := hl 7 rfl (by decide)
  have hl8 : env2.load 1 64 8 = (Keccak.lane (stAfter m0 0) 8).toBitVec := hl 8 rfl (by decide)
  have hl9 : env2.load 1 72 8 = (Keccak.lane (stAfter m0 0) 9).toBitVec := hl 9 rfl (by decide)
  have hl10 : env2.load 1 80 8 = (Keccak.lane (stAfter m0 0) 10).toBitVec :=
    hl 10 rfl (by decide)
  have hl11 : env2.load 1 88 8 = (Keccak.lane (stAfter m0 0) 11).toBitVec :=
    hl 11 rfl (by decide)
  have hl12 : env2.load 1 96 8 = (Keccak.lane (stAfter m0 0) 12).toBitVec :=
    hl 12 rfl (by decide)
  have hl13 : env2.load 1 104 8 = (Keccak.lane (stAfter m0 0) 13).toBitVec :=
    hl 13 rfl (by decide)
  have hl14 : env2.load 1 112 8 = (Keccak.lane (stAfter m0 0) 14).toBitVec :=
    hl 14 rfl (by decide)
  have hl15 : env2.load 1 120 8 = (Keccak.lane (stAfter m0 0) 15).toBitVec :=
    hl 15 rfl (by decide)
  have hl16 : env2.load 1 128 8 = (Keccak.lane (stAfter m0 0) 16).toBitVec :=
    hl 16 rfl (by decide)
  have hl17 : env2.load 1 136 8 = (Keccak.lane (stAfter m0 0) 17).toBitVec :=
    hl 17 rfl (by decide)
  have hl18 : env2.load 1 144 8 = (Keccak.lane (stAfter m0 0) 18).toBitVec :=
    hl 18 rfl (by decide)
  have hl19 : env2.load 1 152 8 = (Keccak.lane (stAfter m0 0) 19).toBitVec :=
    hl 19 rfl (by decide)
  have hl20 : env2.load 1 160 8 = (Keccak.lane (stAfter m0 0) 20).toBitVec :=
    hl 20 rfl (by decide)
  have hl21 : env2.load 1 168 8 = (Keccak.lane (stAfter m0 0) 21).toBitVec :=
    hl 21 rfl (by decide)
  have hl22 : env2.load 1 176 8 = (Keccak.lane (stAfter m0 0) 22).toBitVec :=
    hl 22 rfl (by decide)
  have hl23 : env2.load 1 184 8 = (Keccak.lane (stAfter m0 0) 23).toBitVec :=
    hl 23 rfl (by decide)
  have hl24 : env2.load 1 192 8 = (Keccak.lane (stAfter m0 0) 24).toBitVec :=
    hl 24 rfl (by decide)
  -- a slot the entry block wrote, kept by `memcpy`
  have hslot : ∀ {o : Nat} {r : XReg}, 304 ≤ o → o + 8 ≤ 400 →
      WordAt st1.data.dmem (frame m0 + BitVec.ofNat 64 o) (m0.regs.getXReg r).toBitVec →
      WordAt env2.mem0 (frame m0 + BitVec.ofNat 64 o) (m0.regs.getXReg r).toBitVec :=
    fun ho ho' h => bytesAt_of_same hsame2 h fun i hi =>
      not_inRange_rc hstk ho ho' i (by simpa using hi)
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakF.b1Offset) := hpc2
  refine exec_at hk1 load hwf2 hpc2' hm2 fun st3 hm3 hpc3 => .done _ ⟨?_, hpc3⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm3.sp]
    simp [Sym.eval, env2]
  · rw [hm3.regs .X9 _ rfl]
    rfl
  · simp only [AllOf, laneRegs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      trivial⟩ <;>
    · refine (hm3.regs _ _ rfl).trans ?_
      sym_simp
      simp only [hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9, hl10, hl11, hl12, hl13, hl14,
        hl15, hl16, hl17, hl18, hl19, hl20, hl21, hl22, hl23, hl24]
  · simp only [AllOf, laneSlots]
    refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
    · refine wordAt_of_eq (wordAt_write hm3 hb2 (by decide) rfl) ?_
      sym_simp
      simp only [hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9, hl10, hl11, hl12, hl13, hl14,
        hl15, hl16, hl17, hl18, hl19, hl20, hl21, hl22, hl23, hl24]
  · simp only [AllOf, savedSlots]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · refine wordAt_of_eq (wordAt_write hm3 hb2 (by decide) rfl) ?_
      simp [Sym.eval, env2]
      rfl
    all_goals
      refine wordAt_keep hm3 hb2 (by decide) rfl (hslot (by decide) (by decide) ?_)
      refine wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) ?_
      simp [Sym.eval, env0]
  · exact bytesAt_keep hm3 hb2 (by rw [hrc192]; decide) (by rw [hrc192]; rfl) hcopy
  · intro p hp
    exact (same_region hm3 hwf2 hb2 (by decide) p hp).trans (hsame12 p hp)
  · exact fun p h => hm3.kept hwf2 p (hkept2 p h)

end

end NativeRustcVmArm.KeccakF
