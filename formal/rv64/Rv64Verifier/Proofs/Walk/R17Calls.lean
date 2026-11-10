import Rv64Verifier.Proofs.Walk.Tail
import Rv64Verifier.Proofs.Bus.VbbHead

/-!
# `walk` from `0x800035f0`: `sample`

`duplexW`: `Sponge::duplex` on the transcript's sponge, as a `StepW` writing only the sponge;
`sampleLanes`: `sample` is `duplex` and the state's first three lanes.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.Transcript

theorem duplexW (hD : DuplexSpec) {s u₀ u : MachineState} (hpre : WalkPre s) (h : Inv s u)
    (hptr : u.getMem (tp s) = s.getReg .x13) (hr : Reaches Image.code u₀ u)
    (hpc : u.pc = 0x80007cd8) (h10 : u.getReg .x10 = tp s + 8) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧
      StepW s u v (fun _ ↦ False) True ∧
      ∀ T, TranscriptAt u (tp s) T →
        TranscriptAt v (tp s) { T with sponge := spDuplex T.sponge }) ∨ Dead Image.code v) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hab := hpre.stack.above
  have hx := hpre.stack.next
  have hro := hpre.stack.rodata
  rw [stackLo_eq] at hab
  rw [stackLo_eq, stack_eq] at hx hro
  have hrb : rodataBase.toNat = 2684354560 := rfl
  have hrs : rodataStart.toNat = 2684354560 := rfl
  have hsl := stackLo_callee h duplexStack
  have hds : duplexStack ≤ 8736 := by decide
  have hpre' : DuplexPre u := {
    sponge := by rw [h10, tp]; addr_omega [hb1, hb2, hb3]
    stack := hpre.stack.sub 2656 h.sp (by rw [stack_eq]; omega) (by decide) (by decide)
      (by decide) (by decide)
    spongeStack := by rw [h10, hsl, tp]; addr_omega [hb1, hds]
    rodata := h.rodata hpre
    spongeRodata := by rw [h10, tp]; addr_omega [hro, hrb, hrs, hb1] }
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hd⟩ := hD.call hr hpc hpre'
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have fr := post.frame
  rw [h10, hsl] at fr
  have hval := post.value
  rw [h10] at hval
  have hn : heapNext v = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr nextAddr fun i hi hw ↦ by
      rw [tp] at hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hi, hb1, hds])
  have st : StepW s u v (fun _ ↦ False) True :=
    ⟨fr.mono fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨trivial, by rw [tp] at ha ⊢; addr_omega [ha]⟩)))
      · exact Or.inr (Or.inl (by addr_omega [ha, hb1, hds])),
      ⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩, hn.ge, hp .x2 (by decide)⟩
  refine ⟨v, hrv, Or.inl ⟨hpcv, hp, st, fun T hT ↦ ?_⟩⟩
  have pRO := hpre.proofRO
  have sRO := hpre.streamRO
  have hP := hpre.proof
  obtain ⟨e0, e1, e2⟩ := proofVals hpre h hptr
  have miss : ∀ {a : Word} {n : Nat}, ReadOnly s a n → a.toNat + n ≤ 2 ^ 64 → ∀ i < n,
      ¬ (Within (a + BitVec.ofNat 64 i) (tp s + 8) 336 ∨
        Within (a + BitVec.ofNat 64 i) (s.getReg .x2 - 2656 - BitVec.ofNat 64 duplexStack)
          duplexStack) := by
    intro a n hr hn i hi hw
    refine h.miss hr hn (a + BitVec.ofNat 64 i) (by addr_omega [hn, hi]) (Or.inr (Or.inl ?_))
    rw [stackLo_eq, stack_eq]
    rw [tp] at hw
    rcases hw with hw | hw <;> addr_omega [hw, hi, hb1, hds]
  have kept (y : Word) (hy : (s.getReg .x2 - 2656).toNat ≤ y.toNat)
      (hy' : y.toNat + 8 ≤ (s.getReg .x2).toNat) (ht : Apart y 8 (tp s + 8) 336) :
      v.getMem y = u.getMem y :=
    fr y fun i hi hw ↦ by
      rw [tp] at hw ht; rcases hw with hw | hw <;> addr_omega [hw, hi, hy, hy', ht, hb1, hds]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hT.stream]
    refine fr.eListAt_stream (fun i hi hw ↦ ?_) (fun i hi hw ↦ ?_) (fun i hi hw ↦ ?_)
    · rw [tp] at hw; rcases hw with hw | hw <;> addr_omega [hw, hi, hb1, hds]
    · rw [e0] at hw; exact miss pRO (by addr_omega [hP]) i hi hw
    · rw [e1] at hw; rw [e2] at hi
      rcases hpre.stream with h0 | h0
      · omega
      · exact miss sRO (by addr_omega [h0]) i hi hw
  · rw [hval, hT.sponge]
  · rw [← hT.streamOffset, kept _ (by rw [tp]; addr_omega [hb1]) (by rw [tp]; addr_omega [hb1])
      (by rw [tp]; addr_omega [hb1])]
  · rw [← hT.openingOffset, kept _ (by rw [tp]; addr_omega [hb1]) (by rw [tp]; addr_omega [hb1])
      (by rw [tp]; addr_omega [hb1])]

/-- `sample` is `duplex`, then the first three lanes of the state. -/
theorem sample_lanes {v : MachineState} {p : Word} {T : TState}
    (hT : spongeAt v (p + 8) = spDuplex T.sponge) :
    TM.sample.run T = some (eAt v (p + 136), { T with sponge := spDuplex T.sponge }) := by
  have e1 : (spSqueeze T.sponge).2 = spDuplex T.sponge := rfl
  have e2 : (spSqueeze T.sponge).1 = challengeOf (spDuplex T.sponge).state := rfl
  have hc : challengeOf (spDuplex T.sponge).state = eAt v (p + 136) := by
    rw [← hT]
    show challengeOf (stateAt v (p + 8 + 128)) = _
    rw [Bus.VerifyBusBalance.challengeOf_stateAt']
    congr 1
    bv_omega
  show some ((spSqueeze T.sponge).1, { T with sponge := (spSqueeze T.sponge).2 }) = _
  rw [e1, e2, hc]

end Rv64Verifier.Proofs.Walk
