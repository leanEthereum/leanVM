import Rv64Verifier.Proofs.Transcript.SumcheckRound

/-!
# `transcript::sumcheck`'s rounds: the challenge

From `0x80010658`: `duplex` on the transcript's sponge, its state's first three lanes into
`S - 128`, and on to the push at `0x800105e0` (`grow_one` is never called: the length is the round,
below the capacity `n`).
-/

namespace Rv64Verifier.Transcript.Sumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F76
  Rv64Verifier.Contracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- At `0x800105e0`: the challenge at `S - 128`, and what it and the round's mirror return. -/
structure Chal (s u : MachineState) (ptr : Word) (i : Nat) : Prop extends Head s u ptr i where
  mbuf : (u.getReg .x22).toNat = 0 ∨
    (ptr.toNat + (s.getReg .x15).toNat * 24 ≤ (u.getReg .x23).toNat ∧
      (u.getReg .x23).toNat + 24 * (u.getReg .x22).toNat ≤ heapNext u ∧ (u.getReg .x23).toNat % 8 = 0)
  value : ∀ T, TranscriptAt s (s.getReg .x11) T → ∃ Ti T',
    (pre s i).run T = some ((eListAt u ptr i, eAt u (s.getReg .x12)), Ti) ∧
    (TM.sumcheckRoundPoly (s.getReg .x13).toNat (eAt u (s.getReg .x12))
      (optEAt s (s.getReg .x14 + BitVec.ofNat 64 (32 * i)))).run Ti =
      some (eListAt u (u.getReg .x23) (u.getReg .x22).toNat, T') ∧
    eAt u (s.getReg .x2 - 128) = (spSqueeze T'.sponge).1 ∧
    TranscriptAt u (s.getReg .x11) { T' with sponge := (spSqueeze T'.sponge).2 }

theorem ofNat_ne_of_lt {i : Nat} {w : Word} (h : i < w.toNat) : BitVec.ofNat 64 i ≠ w := fun e ↦ by
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h w.isLt)] at this
  omega

/-- A step that writes only the sponge and memory apart from the transcript and its proof: the
transcript then stands for its state with the new sponge. -/
theorem sponge_step {u w : MachineState} {p lo : Word} {k : Nat} {T : TState} {sp : Sponge}
    (hT : TranscriptAt u p T) (hok : TranscriptOk u p)
    (G : DFrame u w fun a ↦ Within a (p + 8) 336 ∨ Within a lo k)
    (hlo : Apart p transcriptSize lo k) (hpl : ProofApart u p lo k)
    (hsp : spongeAt w (p + 8) = sp) : TranscriptAt w p { T with sponge := sp } := by
  have hS := hok.self
  have hP := hok.proof
  have hpa := hok.apart
  obtain ⟨hpa1, hpa2⟩ := hpa
  obtain ⟨hpl1, hpl2⟩ := hpl
  have keep (y : Word) (h1 : (p + 344).toNat ≤ y.toNat) (h2 : y.toNat + 8 ≤ (p + 344).toNat + 16) :
      w.getMem y = u.getMem y :=
    G y fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, h1, h2, hS, hlo]
  refine ⟨?_, hsp, ?_, ?_⟩
  · rw [← hT.stream]
    refine G.eListAt_stream (fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hS, hlo])
      (fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hP, hpa1, hpl1]) ?_
    rcases hok.stream with h0 | hB
    · intro j hj; rw [h0] at hj; omega
    · exact fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hB, hpa2, hpl2]
  · rw [← hT.streamOffset, keep _ (by addr_omega [hS]) (by addr_omega [hS])]
  · rw [← hT.openingOffset, show p + 352 = p + 344 + 8 by ring,
      keep _ (by addr_omega [hS]) (by addr_omega [hS])]

set_option maxHeartbeats 4000000 in
/-- `duplex`, the challenge into `S - 128`. -/
theorem sample (hD : DuplexSpec) {s u : MachineState} {ptr : Word} {i : Nat}
    (hpre : SumcheckPre s) (hpc : u.pc = 0x80010658) (h : Msg s u ptr i) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ (v.pc = 0x800105e0 ∧ Chal s v ptr i)) := by
  have hb := bounds hpre
  have hS : 208 ≤ (s.getReg .x2).toNat := by addr_omega [hb]
  have hst := hpre.stack
  have hself := hpre.selfStack
  have hSelf := hpre.self.self
  have hcl := hpre.claim
  have hbuf := h.buf
  simp only [NewBuf] at hbuf
  have hlt := h.lt
  have hhi := h.fr.heap.hi
  obtain ⟨w₀, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80010658_spec hpc trivial
  have k₁ := b80010658_keeps h₁
  have hm₁ := b80010658_mem_same h₁
  have x2₀ : w₀.getReg .x2 = s.getReg .x2 - 208 := (k₁ .x2 (by decide)).trans h.fr.saved.x2
  have x10₀ : w₀.getReg .x10 = s.getReg .x11 + 8 := (b80010658_x10 h₁).trans h.x21
  have nx₀ : heapNext w₀ = heapNext u := by simp only [heapNext, hm₁]
  have F₀ : Fr s w₀ := h.fr.same (by omega) (k₁ .x2 (by decide)) hm₁
  have hdp : DuplexPre w₀ := {
    sponge := by rw [x10₀]; addr_omega [hSelf]
    stack := hst.sub 208 x2₀ (by simp only [sumcheckStack, roundPolyStack, nextScalarsStack,
      shuntNextStack, nextScalarStack, absorbStack, duplexStack]; omega) (by decide) (by decide)
      (by decide) (by decide)
    spongeStack := by rw [x10₀]; simp only [stackLo, x2₀]; addr_omega [hb, hself, hSelf]
    rodata := V.rodata hpre F₀.heap.hi F₀.frame
    spongeRodata := by rw [x10₀]; addr_omega [hpre.selfRodata, hSelf] }
  obtain ⟨w, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hD.call hr₁ (b80010658_pc h₁) hdp
  swap
  · exact ⟨w, hr₂, Or.inl hd⟩
  have val₂ := hpost₂.value
  rw [x10₀] at val₂
  have G₂ := hpost₂.frame
  simp only [stackLo, x2₀, x10₀] at G₂
  have hm₂ (y : Word) (hy : ∀ j < 8, ¬ (Within (y + BitVec.ofNat 64 j) (s.getReg .x11 + 8) 336 ∨
      Within (y + BitVec.ofNat 64 j) (s.getReg .x2 - 208 - BitVec.ofNat 64 duplexStack)
        duplexStack)) : w.getMem y = w₀.getMem y := G₂ y hy
  have nx₂ : heapNext w = heapNext w₀ := by
    simp only [heapNext]
    rw [hm₂ nextAddr fun j hj hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hj, hSelf, hpre.selfFree, hst.next, hb]]
  have F₂ : Fr s w := F₀.step (by omega) (hpres₂.reg .x2) ⟨nx₂ ▸ F₀.heap.lo, nx₂ ▸ F₀.heap.hi⟩
    (Nat.le_of_eq nx₂.symm) G₂ (fun a hw ↦ by
      rcases hw with hw | hw
      · exact Or.inr (Or.inl (by addr_omega [hw, hSelf]))
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [hw, hb]))))
    fun y h1 h2 j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, h1, h2, hb, hself, hSelf]
  have H₂ : Head s w ptr i := h.toHead.step F₂ (fun r hr ↦ by
      rw [hpres₂.reg r (headRegs_saved r hr), k₁ r (mem_of_mem hr _)])
    (fun y h1 h2 ↦ by
      rw [hm₂ y fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, h1, h2, hb, hself, hSelf],
        hm₁])
    hS (by omega)
  have x2₂ := H₂.fr.saved.x2
  have x20₂ := H₂.x20
  obtain ⟨v, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80010664_spec
    (by rw [hpc₂, returnAddress_eq, b80010658_x1 h₁]; decide) (by
      rv_eval [x2₂, x20₂]
      and_intros <;> first
        | valid_access hst.valid [hb]
        | (refine Region.valid hSelf ?_ ?_ ?_ <;> addr_omega [hSelf]))
  have k₃ := b80010664_keeps h₃
  have m80 := b80010664_m_x2_80 h₃
  have m88 := b80010664_m_x2_88 h₃
  have m96 := b80010664_m_x2_96 h₃
  have f₃ := b80010664_frame h₃ (by rw [x2₂]; addr_omega [hb])
  have e80 : s.getReg .x2 - 208 + 80 = s.getReg .x2 - 128 := by ring
  rw [x2₂, x20₂, e80] at m80
  rw [x2₂, x20₂, show s.getReg .x2 - 208 + 88 = s.getReg .x2 - 128 + 8 by ring] at m88
  rw [x2₂, x20₂, show s.getReg .x2 - 208 + 96 = s.getReg .x2 - 128 + 16 by ring] at m96
  rw [x2₂, e80] at f₃
  have hpc₃ := b80010664_pc_taken h₃ (by
    rw [H₂.x26, x2₂, show s.getReg .x2 - 208 + 8 = s.getReg .x2 - 200 by ring, H₂.capM]
    exact ofNat_ne_of_lt hlt)
  have nx₃ : heapNext v = heapNext w := by
    simp only [heapNext]; rw [f₃ _ (by addr_omega [hb, hst.next])]
  have F₃ : Fr s v := F₂.step (by omega) (k₃ .x2 (by decide)) ⟨nx₃ ▸ F₂.heap.lo, nx₃ ▸ F₂.heap.hi⟩
    (Nat.le_of_eq nx₃.symm) (DFrame.of_memFrame f₃)
    (fun a hw ↦ Or.inr (Or.inr (Or.inl (by addr_omega [hw, hb]))))
    fun y h1 h2 j hj hw ↦ by addr_omega [hw, hj, h1, h2, hb]
  have H₃ : Head s v ptr i := H₂.step F₃ (fun r hr ↦ k₃ r (mem_of_mem hr _))
    (fun y h1 h2 ↦ f₃ y (by addr_omega [h1, h2, hb])) hS (Nat.le_of_eq nx₃.symm)
  have x22 : v.getReg .x22 = u.getReg .x22 := by
    rw [k₃ .x22 (by decide), hpres₂.reg .x22, k₁ .x22 (by decide)]
  have x23 : v.getReg .x23 = u.getReg .x23 := by
    rw [k₃ .x23 (by decide), hpres₂.reg .x23, k₁ .x23 (by decide)]
  have nxv : heapNext v = heapNext u := by rw [nx₃, nx₂, nx₀]
  -- what the duplex and the block keep: the heap, the claim
  have Gk : DFrame u v fun a ↦ Within a (s.getReg .x11 + 8) 336 ∨ Within a
      (s.getReg .x2 - 208 - BitVec.ofNat 64 duplexStack) (duplexStack + 104) := by
    refine ((DFrame.of_same hm₁ _).trans (G₂.mono fun a ha ↦ ?_) fun _ h ↦ h).trans
      ((DFrame.of_memFrame f₃).mono fun a ha ↦ ?_) fun _ h ↦ h
    · rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (by addr_omega [ha, hb])
    · exact Or.inr (by addr_omega [ha, hb])
  have pk : eListAt v ptr i = eListAt u ptr i := Gk.eListAt fun j hj hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hw, hj, hbuf, hlt, hb, hSelf, hpre.selfFree, hst.above, hhi]
  have ck : eAt v (s.getReg .x12) = eAt u (s.getReg .x12) := Gk.eAt fun j hj hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hw, hj, hcl, hpre.claimSelf, hpre.claimStack, hb, hSelf]
  have mk : eListAt v (v.getReg .x23) (v.getReg .x22).toNat =
      eListAt u (u.getReg .x23) (u.getReg .x22).toNat := by
    rw [x22, x23]
    refine Gk.eListAt fun j hj hw ↦ ?_
    rcases h.mbuf with h0 | ⟨b1, b2, b3⟩
    · rw [h0] at hj; omega
    · rcases hw with hw | hw <;> addr_omega [hw, hj, b1, b2, b3, hbuf, hlt, hb, hSelf, hpre.selfFree,
        hst.above, hhi]
  refine ⟨v, hr₂.trans hr₃, Or.inr ⟨hpc₃, ⟨H₃, by rw [x22, x23, nxv]; exact h.mbuf, fun T hT ↦ ?_⟩⟩⟩
  obtain ⟨Ti, T', hrun, hq, hT'⟩ := h.value T hT
  have hT₀ : TranscriptAt w₀ (s.getReg .x11) T' := hT'.congr hm₁
  have hsp₀ : spongeAt w₀ (s.getReg .x11 + 8) = T'.sponge := hT₀.sponge
  have hsw : spongeAt w (s.getReg .x11 + 8) = spDuplex T'.sponge := by rw [val₂, hsp₀]
  have hTw : TranscriptAt w (s.getReg .x11) { T' with sponge := spDuplex T'.sponge } :=
    sponge_step hT₀ (V.ok hpre F₀.heap.hi F₀.frame) G₂
      (by addr_omega [hself, hb, hSelf])
      (V.proofApart hpre F₀.heap.hi F₀.frame (ProofApart.mono' hpre.proofStack
        (by addr_omega [hb]) (by addr_omega [hb]))) hsw
  refine ⟨Ti, T', by rw [pk, ck]; exact hrun, by rw [ck, mk]; exact hq, ?_,
    Low.transcriptAt hpre F₃.heap.hi F₂.heap.hi F₂.frame ((DFrame.of_memFrame f₃).mono
      fun a ha ↦ Or.inr (Or.inl (by addr_omega [ha, hb]))) hTw⟩
  change eAt v (s.getReg .x2 - 128) = challengeOf (spDuplex T'.sponge).state
  rw [← hsw, show (spongeAt w (s.getReg .x11 + 8)).state = stateAt w (s.getReg .x11 + 8 + 128) from rfl,
    Samples.challengeOf_stateAt, show s.getReg .x11 + 8 + 128 = s.getReg .x11 + 136 by ring]
  refine eAt_congr m80 ?_ ?_
  · rw [m88, show s.getReg .x11 + 136 + 8 = s.getReg .x11 + 144 by ring]
  · rw [m96, show s.getReg .x11 + 136 + 16 = s.getReg .x11 + 152 by ring]

end Rv64Verifier.Transcript.Sumcheck
