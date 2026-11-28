module

public import NativeRustcVmArm.Code.Vm.KeccakF.Names
public import NativeRustcVmArm.Keccak.WordsHash.Inv
public import NativeRustcVmArm.Spec.Keccak

/-!
# `keccak256_words::<hash_words's closure>`: its calls of `keccak_f`

`call_kf`: where a block ends in `bl keccak_f` with X0 the state in the frame (its byte 8) holding
the lanes of `A`, `keccak_f`'s contract takes the machine to the return address with the lanes of
`keccakF1600 A`, `Ctx` kept and the callee-saved registers kept. The stack `keccak_f` uses is the
400 bytes below the frame, within the function's (`stackBelow m0 keccak256WordsStack`).
-/

namespace NativeRustcVmArm.WordsHash

open NativeRustcArm NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcArm.KeccakF (WordAt bytesAt_stateBytes byteOf_toBitVec)
open NativeRustcVmArm.Keccak

public section

/-- A word of a state's bytes. -/
theorem wordAt_of_stateBytes {d : DataMem} {a : BitVec 64} {B : KeccakState}
    (h : BytesAt d a (stateBytes B)) {j : Nat} (hj : j < 25) :
    WordAt d (a + BitVec.ofNat 64 (8 * j)) (Keccak.lane B j).toBitVec := by
  intro t ht
  simp only [List.length_map, List.length_range] at ht
  rw [addr_add, h (8 * j + t) (by rw [length_stateBytes]; omega), List.getElem_map,
    List.getElem_range, byteOf_toBitVec _ ht, KeccakF.getElem_eq_getD', stateBytes,
    Native.Keccak.Proof.getD_wordsBytes, KeccakF.getD_toList, show (8 * j + t) / 8 = j by omega,
    show (8 * j + t) % 8 = t by omega]

/-- The facts on the stack the call uses. -/
theorem stack_facts {m0 : MachineData} (h : StackOk m0 NativeRustcVmArm.keccak256WordsStack) :
    (stackBelow m0 NativeRustcVmArm.keccak256WordsStack).toNat + 688 = m0.regs.SP.toNat ∧
      (frame m0).toNat + 288 = m0.regs.SP.toNat ∧ 688 ≤ m0.regs.SP.toNat ∧
      m0.regs.SP.toNat < 2 ^ 64 := by
  have := h.2.1
  have := stack_toNat h
  have := frame_toNat h
  have := @sp_lt m0
  have hK : NativeRustcVmArm.keccak256WordsStack = 688 := rfl
  omega

variable [Host]

/-- **A call of `keccak_f` on the state in the frame.** -/
theorem call_kf (hkf : Spec (label NativeRustcVmArm.Vm.KeccakF.entryLabel) NativeRustcVmArm.KeccakFPre
      NativeRustcVmArm.KeccakFPost) {m0 : MachineData}
    (hstk : StackOk m0 NativeRustcVmArm.keccak256WordsStack)
    (hrc : NativeRustcVmArm.RcAt m0 NativeRustcVmArm.keccak256WordsStack)
    {st : MachineState} {env : Env} {next : Int64} {A : KeccakState}
    (hc : Ctx m0 st.data) (hl : Lanes m0 st.data (Keccak.lane A))
    (hx0 : st.data.regs.X0.toBitVec = frame m0 + BitVec.ofNat 64 8)
    (hpc : PcOk env (.call NativeRustcVmArm.Vm.KeccakF.entryLabel) next st) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = next → Ctx m0 st'.data →
      Lanes m0 st'.data (Keccak.lane (keccakF1600 A)) →
      (∀ r, calleeSaved r = true → st'.data.regs.getXReg r = st.data.regs.getXReg r) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hK : NativeRustcVmArm.keccak256WordsStack = 688 := rfl
  have hK4 : NativeRustcVmArm.keccakFStack = 400 := rfl
  obtain ⟨hS, hF, hS688, hlt⟩ := stack_facts hstk
  obtain ⟨hrcw, hrcnw, hrcap⟩ := hrc
  have hsp : st.data.regs.SP.toBitVec = frame m0 := hc.sp
  have hspn : st.data.regs.SP.toNat = (frame m0).toNat := by
    rw [← UInt64.toNat_toBitVec, hsp]
  have hsb : (stackBelow st.data NativeRustcVmArm.keccakFStack).toNat = (frame m0).toNat - 400 := by
    unfold stackBelow
    rw [hsp, hK4, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
    simp
  have ha : (st.data.regs.X0.toBitVec).toNat = (frame m0).toNat + 8 := by
    rw [hx0, toNat_add_ofNat _ _ (by omega)]
  -- bytes of the function's stack
  have hin : ∀ p : BitVec 64, (frame m0).toNat - 400 ≤ p.toNat → p.toNat < (frame m0).toNat + 288 →
      InRange (stackBelow m0 NativeRustcVmArm.keccak256WordsStack)
        NativeRustcVmArm.keccak256WordsStack p := by
    intro p h1 h2
    rw [inRange_iff (by omega)]
    omega
  have hrcSame : NativeRustcVm.WordsAt st.data.dmem NativeRustcVmArm.rcAddr
      LeanVM.Parameters.keccakRC :=
    bytesAt_of_same hc.same hrcw fun i hi => not_inRange_of_apart hrcnw
      (by unfold NoWrap; omega) hrcap (by
        have : (LeanVM.Parameters.keccakRC.flatMap NativeRustcVm.wordBytes).length = 192 :=
          length_rcBytes
        omega)
  have hpre : NativeRustcVmArm.KeccakFPre st.data := by
    refine ⟨⟨?_, ?_, ?_⟩, ⟨hrcSame, hrcnw, ?_⟩, ?_, ?_, ?_, ?_⟩
    · rw [hspn]; exact frame_aligned hstk
    · rw [hspn]; omega
    · intro i hi
      refine hc.kept _ (hstk.2.2 i (by omega)) |> fun h => ?_
      have e : st.data.regs.SP.toBitVec - BitVec.ofNat 64 NativeRustcVmArm.keccakFStack +
          BitVec.ofNat 64 i = m0.regs.SP.toBitVec -
          BitVec.ofNat 64 NativeRustcVmArm.keccak256WordsStack + BitVec.ofNat 64 i := by
        rw [hsp, hK, hK4]
        simp only [frame]
        bv_omega
      rw [e]
      exact h
    · unfold Apart at hrcap ⊢
      rw [hsb]
      omega
    · intro i hi
      rw [hx0, addr_add]
      exact frame_mapped hstk hc.kept _ (by omega)
    · unfold NoWrap; rw [ha]; omega
    · unfold Apart; rw [ha, hsb]; omega
    · unfold Apart at hrcap ⊢
      rw [ha]
      omega
  refine call_then hpc hkf hpre fun st' hpc' hpost => cont st' hpc' ?_ ?_ ?_
  · obtain ⟨-, hsame, hsaved⟩ := hpost
    have hsame' : SameOutside st.data.dmem st'.data.dmem
        (InRange (stackBelow m0 NativeRustcVmArm.keccak256WordsStack)
          NativeRustcVmArm.keccak256WordsStack) := fun p hp => hsame p fun h => hp (by
      rcases h with h | h
      · rw [inRange_iff (by rw [ha]; omega), ha] at h
        exact hin p (by omega) (by omega)
      · rw [inRange_iff (by rw [hsb]; omega), hsb] at h
        exact hin p (by omega) (by omega))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun p hp => (hsame' p hp).trans (hc.same p hp),
      fun p h => hsaved.2.2 p (hc.kept p h)⟩
    · rw [hsaved.2.1]; exact hc.sp
    · rw [hsaved.1 .X19 rfl]; exact hc.x19
    · rw [hsaved.1 .X20 rfl]; exact hc.x20
    · rw [hsaved.1 .X21 rfl]; exact hc.x21
    · rw [hsaved.1 .X22 rfl]; exact hc.x22
    · rw [hsaved.1 .X23 rfl]; exact hc.x23
    · rw [hsaved.1 .X24 rfl]; exact hc.x24
    · rw [hsaved.1 .X27 rfl]; exact hc.x27
    · rw [hsaved.1 .X28 rfl]; exact hc.x28
    · have hsv := hc.saved
      have hkeep : ∀ {o : Nat} {w : BitVec 64}, 208 ≤ o → o + 8 ≤ 288 →
          WordAt st.data.dmem (frame m0 + BitVec.ofNat 64 o) w →
          WordAt st'.data.dmem (frame m0 + BitVec.ofNat 64 o) w := fun {o} {w} ho ho' h =>
        bytesAt_of_same hsame h fun i hi hr => by
          simp only [List.length_map, List.length_range] at hi
          have hp : (frame m0 + BitVec.ofNat 64 o + BitVec.ofNat 64 i).toNat =
              (frame m0).toNat + (o + i) := by
            rw [addr_add, toNat_add_ofNat _ _ (by omega)]
          rcases hr with h | h
          · rw [inRange_iff (by rw [ha]; omega), ha, hp] at h
            omega
          · rw [inRange_iff (by rw [hsb]; omega), hsb, hp] at h
            omega
      simp only [AllOf, savedSlots] at hsv ⊢
      obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, -⟩ := hsv
      exact ⟨hkeep (by decide) (by decide) s0, hkeep (by decide) (by decide) s1,
        hkeep (by decide) (by decide) s2, hkeep (by decide) (by decide) s3,
        hkeep (by decide) (by decide) s4, hkeep (by decide) (by decide) s5,
        hkeep (by decide) (by decide) s6, hkeep (by decide) (by decide) s7,
        hkeep (by decide) (by decide) s8, hkeep (by decide) (by decide) s9, trivial⟩
  · have hw : BytesAt st.data.dmem st.data.regs.X0.toBitVec (stateBytes A) := by
      refine bytesAt_stateBytes fun j hj => ?_
      rw [hx0, addr_add]
      exact hl j hj
    have := wordsAt_iff.mp (hpost.1 A (wordsAt_iff.mpr hw))
    intro i hi
    have h' := wordAt_of_stateBytes this hi
    rwa [hx0, addr_add] at h'
  · exact fun r hr => hpost.2.2.1 r hr

end

end NativeRustcVmArm.WordsHash
