module

public import NativeRustcVmX64.Keccak.KeccakF.Inv
public import NativeRustcVmX64.Keccak.KeccakF.Blocks
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

/-!
# `keccak_f`'s prologue (x86-64)

`prologue_step`: from `keccak_f`'s entry, in a state satisfying `KeccakFPre`, the machine
inevitably reaches the round loop's head with the loop invariant before the first round
(`At m0 0`): the entry block (`entry`) pushes the callee-saved registers and calls `memcpy` to copy
the round constants to the frame at 240; the next (`load`) saves the state pointer at 184, loads the
25 lanes into registers and frame slots and sets the counter RAX to 2.
-/

namespace NativeRustcVmX64.KeccakF

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcX64.KeccakF (WordAt wordAt_of_eq wordAt_write wordAt_keep same_region load_lane')
open NativeRustcVmX64.Keccak

public section

theorem not_inRange_rc {m0 : MachineData} (hstk : StackOk m0 NativeRustcVmX64.keccakFStack)
    {o : Nat} (ho : 432 ≤ o ∨ o + 8 ≤ 240) (ho' : o + 8 ≤ 488) : ∀ i < 8,
      ¬ InRange (frame m0 + BitVec.ofNat 64 240) 192
        (frame m0 + BitVec.ofNat 64 o + BitVec.ofNat 64 i) := by
  intro i hi
  have hf := frame_noWrap hstk
  unfold NoWrap NativeRustcVmX64.keccakFStack at hf
  rw [addr_add, Hasher.inRange_add_iff (by omega) (by omega) (by decide)]
  omega

theorem inRange_frame_of_rc {m0 : MachineData} (hstk : StackOk m0 NativeRustcVmX64.keccakFStack)
    {p : BitVec 64} (h : InRange (frame m0 + BitVec.ofNat 64 240) 192 p) :
    InRange (frame m0) NativeRustcVmX64.keccakFStack p := by
  have hf := frame_noWrap hstk
  have h240 := frame_add_toNat hstk (o := 240) (by decide)
  unfold NoWrap NativeRustcVmX64.keccakFStack at hf
  rw [inRange_iff (by rw [h240]; omega), h240] at h
  unfold NativeRustcVmX64.keccakFStack
  rw [inRange_iff (by omega)]
  omega

variable [Host]

set_option linter.unusedSimpArgs false in
/-- **The prologue.** -/
theorem prologue_step {k : Nat} (hp : Placed Vm.KeccakF.code k)
    (hmemcpy : Spec (label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) {m0 : MachineData}
    (hpre : NativeRustcVmX64.KeccakFPre m0) :
    Eventually (step1 Host.exe) (fun st => At m0 0 st.data ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakF.b2Offset))
      ⟨m0, Host.addrOf k⟩ := by
  obtain ⟨hstk, ⟨hrc, hrcnw, hrcap⟩, hmap, hnw, hap, -, hgot⟩ := hpre
  have hf := frame_noWrap hstk
  have hft := frame_toNat hstk
  have h1 := hstk.1
  have h2 := hstk.2.1
  unfold NoWrap NativeRustcVmX64.keccakFStack at hf
  unfold NativeRustcVmX64.keccakFStack at h1 h2
  have h240 := frame_add_toNat hstk (o := 240) (by decide)
  have hrcap' : Apart NativeRustcVmX64.rcAddr 192 (frame m0) 488 := hrcap
  have hrcnw' : NoWrap NativeRustcVmX64.rcAddr 192 := hrcnw
  unfold Apart at hrcap'
  unfold NoWrap at hrcnw'
  have hap' : Apart (m0.regs.get64 .rdi) 200 (frame m0) 488 := hap
  unfold Apart at hap'
  have hk0 : Vm.KeccakF.b0.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.KeccakF.b0Offset) :=
    Vm.KeccakF.b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let env0 := Env.ofMachine m0
    [(frame m0, 488), (m0.regs.get64 .rdi, 200), (gotAddr "memcpy", 8)] (fun _ => 0)
    (Host.addrOf (k + NativeRustcVmX64.Vm.KeccakF.b0Offset + Vm.KeccakF.b0.length)).toBitVec
  obtain ⟨_, hgnw, hgs, hga⟩ := hgot.1 "memcpy" (by simp)
  have hgf : Apart (gotAddr "memcpy") 8 (frame m0) 488 := hgs
  have hgo : Apart (gotAddr "memcpy") 8 (m0.regs.get64 .rdi) 200 :=
    hga (m0.regs.get64 .rdi, 200) (by simp)
  have hwf0 : env0.WF := by
    refine Env.wf_of ⟨⟨hstk.2.2, frame_noWrap hstk⟩, ⟨hmap, hnw⟩,
      ⟨hgot.mapped (by simp), hgnw⟩, trivial⟩ ?_
    apply List.pairwise_cons.mpr
    refine ⟨?_, List.pairwise_pair.mpr hgo.symm⟩
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact hap.symm
    · exact hgf.symm
  have hm0 : Match env0 startEntry m0 := by
    refine Match.withKnownBytes ?_ ?_
    · exact match_ofMachine ⟨rfl, rfl, rfl, trivial⟩
        ⟨show rspOf m0 = _ from (frame_add m0).symm.trans rfl,
          show m0.regs.get64 .rdi = _ from (BitVec.add_zero _).symm.trans rfl, trivial⟩
        trivial trivial ⟨(BitVec.add_zero _).symm, trivial⟩
    · intro i hi
      simpa [env0, Env.base, Sym.eval] using hgot.byte (l := "memcpy") (by simp) hi
  have hb0 : env0.regions[0]? = some (frame m0, 488) := rfl
  have hrc192 : rcBytes.length = 192 := length_rcBytes
  refine exec_then hk0 entry hwf0 (fun _ _ => rfl) hm0 fun st1 hm1 hpc1 => ?_
  have hrdi1 : st1.data.regs.get64 .rdi = frame m0 + BitVec.ofNat 64 240 :=
    (hm1.regs .rdi _ rfl).trans rfl
  have hrsi1 : st1.data.regs.get64 .rsi = NativeRustcVmX64.rcAddr :=
    (hm1.regs .rsi _ rfl).trans (by sym_simp; rfl)
  have hrdx1 : (st1.data.regs.get64 .rdx).toNat = 192 := by
    rw [hm1.regs .rdx _ rfl]
    rfl
  have hrbx1 : st1.data.regs.get64 .rbx = m0.regs.get64 .rdi + BitVec.ofInt 64 0 :=
    (hm1.regs .rbx _ rfl).trans rfl
  have hrsp1 : rspOf st1.data = frame m0 :=
    (hm1.regs .rsp _ rfl).trans (by sym_simp; exact BitVec.add_zero _)
  have hsame1 :
      SameOutside m0.dmem st1.data.dmem (InRange (frame m0) NativeRustcVmX64.keccakFStack) :=
    same_region hm1 hwf0 hb0 (by decide) (by decide)
  have hkept1 : Kept m0.dmem st1.data.dmem := hm1.kept hwf0
  -- the round constants, untouched by the entry block
  have hrc1 : BytesAt st1.data.dmem NativeRustcVmX64.rcAddr rcBytes :=
    Keccak.bytesAt_of_same hsame1 hrc fun i hi =>
      not_inRange_of_apart hrcnw
        (by unfold NoWrap NativeRustcVmX64.keccakFStack; omega)
        (by unfold Apart NativeRustcVmX64.keccakFStack; omega)
        (by rw [hrc192] at hi; exact hi)
  have hfr : ∀ i < 488, (st1.data.dmem.get? (frame m0 + BitVec.ofNat 64 i)).isSome := fun i hi =>
    hkept1 _ (hstk.2.2 i hi)
  refine call_then hpc1 hmemcpy ?pre1 fun st2 hpc2 hrsp2 hpost2 => ?_
  case pre1 =>
    unfold MemcpyPre
    simp only [NativeRustcX64.reg, hrdi1, hrsi1, hrdx1]
    refine ⟨⟨Nat.zero_le _, by rw [hrsp1]; omega, fun i hi => ?_⟩, fun i hi => ?_,
      fun i hi => ?_, ?_, hrcnw, ?_, ?_⟩
    · rw [hrsp1, BitVec.sub_zero]
      exact hfr i (by omega)
    · rw [addr_add]
      exact hfr _ (by omega)
    · rw [hrc1 i (by omega)]
      rfl
    · unfold NoWrap
      omega
    · unfold Apart
      rw [h240]
      omega
    · unfold Apart
      rw [h240, hrsp1]
      omega
  obtain ⟨-, hcopy, hsame2, hsaved2⟩ := hpost2
  simp only [NativeRustcX64.reg] at hcopy hsame2
  rw [hrdi1, hrsi1, hrdx1] at hcopy
  rw [hrdi1, hrdx1] at hsame2
  have hrcb : bytesOf st1.data.dmem NativeRustcVmX64.rcAddr 192 = rcBytes := by
    rw [← hrc192]
    exact Hasher.bytesOf_of_bytesAt hrc1
  rw [hrcb] at hcopy
  have hkept2 : Kept m0.dmem st2.data.dmem := fun p h => hsaved2.2 p (hkept1 p h)
  have hsame12 : SameOutside m0.dmem st2.data.dmem
      (InRange (frame m0) NativeRustcVmX64.keccakFStack) := fun p hp =>
    (hsame2 p fun h => hp (inRange_frame_of_rc hstk h)).trans (hsame1 p hp)
  have hk1 : Vm.KeccakF.b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.KeccakF.b1Offset) :=
    Vm.KeccakF.b1_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let env2 := Env.ofMachine st2.data [(frame m0, 488), (m0.regs.get64 .rdi, 200)]
  have hwf2 : env2.WF :=
    Env.wf_of ⟨⟨fun j hj => hkept2 _ (hstk.2.2 j hj), frame_noWrap hstk⟩,
      ⟨fun j hj => hkept2 _ (hmap j hj), hnw⟩, trivial⟩ (List.pairwise_pair.mpr hap.symm)
  have hm2 : Match env2 startLoad st2.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨show rspOf st2.data = _ by rw [hrsp2, hrsp1]; rfl,
        show st2.data.regs.get64 .rbx = _ by rw [hsaved2.1 .rbx rfl, hrbx1]; rfl, trivial⟩
      trivial trivial trivial
  have hb2 : env2.regions[0]? = some (frame m0, 488) := rfl
  have hbytes : bytesOf st2.data.dmem (m0.regs.get64 .rdi) 200 =
      bytesOf m0.dmem (m0.regs.get64 .rdi) 200 :=
    bytesOf_of_same hsame12 fun i hi =>
      not_inRange_of_apart (show NoWrap (m0.regs.get64 .rdi) 200 from hnw)
      (by unfold NoWrap NativeRustcVmX64.keccakFStack; omega)
      (by unfold Apart NativeRustcVmX64.keccakFStack; omega) hi
  have hl : ∀ {off : Nat} (j : Nat), off = 8 * j → j < 25 →
      env2.load 1 off 8 = (Keccak.lane (stAfter m0 0) j).toBitVec := fun j hoff hj => by
    rw [load_lane' hoff hj]
    show (Keccak.lane (stateOf (bytesOf st2.data.dmem (m0.regs.get64 .rdi) 200)) j).toBitVec = _
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
  have hslot : ∀ {o : Nat} {w : BitVec 64}, 432 ≤ o → o + 8 ≤ 488 →
      WordAt st1.data.dmem (frame m0 + BitVec.ofNat 64 o) w →
      WordAt env2.mem0 (frame m0 + BitVec.ofNat 64 o) w :=
    fun ho ho' h => Keccak.bytesAt_of_same hsame2 h fun i hi =>
      not_inRange_rc hstk (.inl ho) ho' i (by simpa using hi)
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakF.b1Offset) := hpc2
  refine exec_at hk1 load hwf2 nofun hpc2' hm2 fun st3 hm3 hpc3 => .done _ ⟨?_, hpc3⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hm3.regs .rsp _ rfl).trans rfl
  · exact (hm3.regs .rax _ rfl).trans rfl
  · exact wordAt_of_eq (wordAt_write hm3 hb2 (by decide) rfl) (BitVec.add_zero _)
  · simp only [AllOf, laneRegs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
    · refine (hm3.regs _ _ rfl).trans ?_
      sym_simp
      simp only [hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9, hl10, hl11, hl12, hl13, hl14,
        hl15, hl16, hl17, hl18, hl19, hl20, hl21, hl22, hl23, hl24]
  · simp only [AllOf, laneSlots]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
    · refine wordAt_of_eq (wordAt_write hm3 hb2 (by decide) rfl) ?_
      sym_simp
      simp only [hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9, hl10, hl11, hl12, hl13, hl14,
        hl15, hl16, hl17, hl18, hl19, hl20, hl21, hl22, hl23, hl24]
  · simp only [AllOf, savedSlots]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
    · refine wordAt_keep hm3 hb2 (by decide) rfl (hslot (by decide) (by decide) ?_)
      exact wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl
  · exact bytesAt_keep hm3 hb2 (by rw [hrc192]; decide) (by rw [hrc192]; rfl) hcopy
  · intro p hp
    exact (same_region hm3 hwf2 hb2 (by decide) (by decide) p hp).trans (hsame12 p hp)
  · exact fun p h => hm3.kept hwf2 p (hkept2 p h)

end

end NativeRustcVmX64.KeccakF
