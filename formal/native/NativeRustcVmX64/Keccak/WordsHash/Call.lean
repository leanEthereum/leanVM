module

public import NativeRustcVmX64.Keccak.WordsHash.Frame
public import NativeRustcVmX64.Code.Vm.KeccakF.Names

/-!
# `keccak256_words` (x86-64): its calls of `keccak_f`

`call_kf`: where a block ends in `callq keccak_f` with RDI the lanes (the frame's byte 40) holding
the lanes of `A`, RSP at the frame (`Ctx … 0`), `keccak_f`'s contract takes the machine to the
return address with RSP back at the frame's offset 8, the lanes of `keccakF1600 A`, the slots and
the callee-saved registers kept. `keccak_f`'s stack is the 480 bytes below the frame, the bottom
of the function's (`stackBelow m0 keccak256WordsStack`).
-/

namespace NativeRustcVmX64.WordsHash

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcX64.KeccakF (WordAt bytesAt_stateBytes byteOf_toBitVec)
open NativeRustcVmX64.Keccak (wordsAt_iff bytesAt_of_same not_inRange_of_apart)

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

/-- The lanes as the state's bytes at the frame's byte 40. -/
theorem bytesAt_lanes {m0 : MachineData} {d : DataMem} {A : KeccakState}
    (h : Lanes m0 d (Keccak.lane A)) :
    BytesAt d (frame m0 + BitVec.ofNat 64 40) (stateBytes A) :=
  bytesAt_stateBytes fun j hj => by rw [addr_add]; exact h j hj

/-- The lanes from the state's bytes at the frame's byte 40. -/
theorem lanes_of_bytesAt {m0 : MachineData} {d : DataMem} {A : KeccakState}
    (h : BytesAt d (frame m0 + BitVec.ofNat 64 40) (stateBytes A)) :
    Lanes m0 d (Keccak.lane A) := fun j hj => by
  have := wordAt_of_stateBytes h hj
  rwa [addr_add] at this

variable [Host]

/-- **A call of `keccak_f` on the lanes.** -/
theorem call_kf (hkf : Spec (label NativeRustcVmX64.Vm.KeccakF.entryLabel) NativeRustcVmX64.KeccakFPre
      NativeRustcVmX64.KeccakFPost) {m0 : MachineData}
    (hstk : StackOk m0 NativeRustcVmX64.keccak256WordsStack)
    (hrc : NativeRustcVmX64.RcAt m0 NativeRustcVmX64.keccak256WordsStack)
    (hgot : GotAt m0 NativeRustcVmX64.keccak256WordsStack
      [(m0.regs.get64 .rdi, 32), (NativeRustcVmX64.rcAddr, 192)] ["memcpy", "memset"])
    {L : List (Nat × BitVec 64)} (hL : LowSlots L) {R : List (Reg64 × BitVec 64)}
    {st : MachineState} {env : Env} {next : Int64} {A : KeccakState}
    (hc : Ctx m0 L R 0 st.data) (hl : Lanes m0 st.data.dmem (Keccak.lane A))
    (hrdi : st.data.regs.get64 .rdi = frame m0 + BitVec.ofNat 64 40)
    (hpc : PcOk env (.call NativeRustcVmX64.Vm.KeccakF.entryLabel) next st) {Q : MachineState → Prop}
    (cont : ∀ st', st'.pc = next → Ctx m0 L [] 8 st'.data →
      Lanes m0 st'.data.dmem (Keccak.lane (keccakF1600 A)) →
      (∀ r, calleeSaved r = true → st'.data.regs.get64 r = st.data.regs.get64 r) →
      Eventually (step1 Host.exe) Q st') :
    Eventually (step1 Host.exe) Q st := by
  obtain ⟨hF, hS, h768, hlt⟩ := stack_facts hstk
  have hK4 : NativeRustcVmX64.keccakFStack = 480 := rfl
  obtain ⟨hrcw, hrcnw, hrcap⟩ := hrc
  rw [stk_eq] at hrcap
  have hrcap' := hrcap
  have hrcnw' := hrcnw
  unfold NativeRustcVm.Apart at hrcap'
  unfold NativeRustcVm.NoWrap at hrcnw'
  have hsp : rspOf st.data = frame m0 := by rw [hc.rsp]; exact BitVec.add_zero _
  have hspn : (rspOf st.data).toNat = (frame m0).toNat := by rw [hsp]
  have hsb : (stackBelow st.data 480).toNat = (frame m0).toNat - 480 := by
    rw [stackBelow, bv_sub_toNat (by omega), hspn]
  have hsb' : stackBelow st.data 480 = stackBelow m0 768 := by
    apply BitVec.eq_of_toNat_eq
    rw [hsb]
    omega
  have h40 : (frame m0 + BitVec.ofNat 64 40).toNat = (frame m0).toNat + 40 :=
    frame_add_toNat hstk (by decide)
  have hin : ∀ p : BitVec 64, (frame m0).toNat - 480 ≤ p.toNat →
      p.toNat < (frame m0).toNat + 240 →
      InRange (stackBelow m0 NativeRustcVmX64.keccak256WordsStack)
        NativeRustcVmX64.keccak256WordsStack p := by
    intro p h1 h2
    rw [stk_eq, inRange_iff (by omega)]
    omega
  have hrc1 : NativeRustcVm.WordsAt st.data.dmem NativeRustcVmX64.rcAddr
      LeanVM.Parameters.keccakRC :=
    bytesAt_of_same hc.same hrcw fun i hi => by
      rw [stk_eq]
      refine not_inRange_of_apart hrcnw (by unfold NoWrap; omega) (by
        unfold Apart; omega) (by
          have : (LeanVM.Parameters.keccakRC.flatMap NativeRustcVm.wordBytes).length = 192 :=
            Keccak.length_rcBytes
          omega)
  have hpre : NativeRustcVmX64.KeccakFPre st.data := by
    refine ⟨⟨?_, ?_, ?_⟩, ⟨hrc1, hrcnw, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · show 480 ≤ (rspOf st.data).toNat
      rw [hspn]; omega
    · rw [hspn]; omega
    · intro i hi
      rw [hK4] at hi
      show (st.data.dmem.get? (stackBelow st.data 480 + BitVec.ofNat 64 i)).isSome
      rw [hsb']
      exact hc.kept _ (hstk.2.2 i (by rw [stk_eq]; omega))
    · show NativeRustcVm.Apart NativeRustcVmX64.rcAddr 192 (stackBelow st.data 480) (480 + 8)
      unfold NativeRustcVm.Apart
      rw [hsb]
      omega
    · show Mapped st.data.dmem (st.data.regs.get64 .rdi) 200
      rw [hrdi]
      intro i hi
      rw [addr_add]
      exact frame_mapped hstk hc.kept _ (by omega)
    · show NoWrap (st.data.regs.get64 .rdi) 200
      unfold NoWrap
      rw [hrdi, h40]
      omega
    · show Apart (st.data.regs.get64 .rdi) 200 (stackBelow st.data 480) (480 + 8)
      unfold Apart
      rw [hrdi, h40, hsb]
      omega
    · show Apart (st.data.regs.get64 .rdi) 200 NativeRustcVmX64.rcAddr 192
      unfold Apart
      rw [hrdi, h40]
      omega
    · have hg := hgot.symbols (show ["memcpy"].Sublist ["memcpy", "memset"] by simp)
      refine hg.transport ?_ ?_ ?_
      · intro l hl i hi
        apply hc.same
        have hs := (hg.1 l hl).2.2.1
        change Apart (gotAddr l) 8
          (stackBelow m0 NativeRustcVmX64.keccak256WordsStack) _ at hs
        have hn := (hg.1 l hl).2.1
        exact fun h => hs.not_inRange hn
          (by unfold NoWrap; rw [stk_eq]; omega) hi (Nat.lt_trans h (by decide))
      · intro l hl
        have hs := (hg.1 l hl).2.2.1
        change Apart (gotAddr l) 8
          (stackBelow m0 NativeRustcVmX64.keccak256WordsStack) _ at hs
        change Apart (gotAddr l) 8 (stackBelow st.data 480) 488
        rw [hsb']
        rw [stk_eq] at hs
        unfold Apart at hs ⊢
        omega
      · intro l hl a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · have hs := (hg.1 l hl).2.2.1
          change Apart (gotAddr l) 8
            (stackBelow m0 NativeRustcVmX64.keccak256WordsStack) _ at hs
          change Apart (gotAddr l) 8 (st.data.regs.get64 .rdi) 200
          rw [hrdi]
          rw [stk_eq] at hs
          unfold Apart at hs ⊢
          rw [h40]
          omega
        · exact (hg.1 l hl).2.2.2 (NativeRustcVmX64.rcAddr, 192) (by simp)
  refine call_then hpc hkf hpre fun st' hpc' hrsp' hpost => ?_
  obtain ⟨hw, hsame, hsaved⟩ := hpost
  simp only [NativeRustcX64.reg, hrdi, hK4] at hw hsame
  rw [hsb'] at hsame
  -- the bytes `keccak_f` changes: the lanes and its stack
  have hout : ∀ p : BitVec 64, ¬ InRange (stackBelow m0 NativeRustcVmX64.keccak256WordsStack)
      NativeRustcVmX64.keccak256WordsStack p →
      ¬ (InRange (frame m0 + BitVec.ofNat 64 40) 200 p ∨ InRange (stackBelow m0 768) 480 p) :=
    fun p hp h => hp (by
      rcases h with h | h
      · rw [inRange_iff (by rw [h40]; omega), h40] at h
        exact hin p (by omega) (by omega)
      · rw [inRange_iff (by omega)] at h
        exact hin p (by omega) (by omega))
  have hslot : ∀ {o : Nat} {w : BitVec 64}, (8 ≤ o ∧ o + 8 ≤ 40) ∨ (240 ≤ o ∧ o + 8 ≤ 288) →
      WordAt st.data.dmem (frame m0 + BitVec.ofNat 64 o) w →
      WordAt st'.data.dmem (frame m0 + BitVec.ofNat 64 o) w := fun {o} {w} ho h =>
    bytesAt_of_same hsame h fun i hi hr => by
      simp only [List.length_map, List.length_range] at hi
      have hp : (frame m0 + BitVec.ofNat 64 o + BitVec.ofNat 64 i).toNat =
          (frame m0).toNat + (o + i) := by
        rw [addr_add, frame_add_toNat hstk (by omega)]
      rcases hr with h | h
      · rw [inRange_iff (by rw [h40]; omega), h40, hp] at h
        omega
      · rw [inRange_iff (by omega), hp] at h
        omega
  refine cont st' hpc' ⟨?_, trivial, ?_, ?_, ?_, ?_⟩ ?_ hsaved.1
  · rw [hrsp', hsp]
  · exact allOf_imp (fun p hp h => hslot (.inl (mem_of_allOf hL hp)) h) hc.slots
  · have hs := hc.saved
    simp only [SlotsAt, savedSlots, AllOf] at hs ⊢
    obtain ⟨s0, s1, s2, s3, s4, s5, -⟩ := hs
    exact ⟨hslot (.inr (by decide)) s0, hslot (.inr (by decide)) s1, hslot (.inr (by decide)) s2,
      hslot (.inr (by decide)) s3, hslot (.inr (by decide)) s4, hslot (.inr (by decide)) s5,
      trivial⟩
  · exact fun p hp => (hsame p (hout p hp)).trans (hc.same p hp)
  · exact fun p h => hsaved.2 p (hc.kept p h)
  · exact lanes_of_bytesAt (wordsAt_iff.mp (hw A (wordsAt_iff.mpr (bytesAt_lanes hl))))

end

end NativeRustcVmX64.WordsHash
