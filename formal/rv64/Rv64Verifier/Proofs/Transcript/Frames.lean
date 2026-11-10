import Rv64Verifier.Proofs.Transcript.Sponge

/-!
# What a frame keeps of a transcript

A frame (`DFrame s t w`) whose `w` misses what the transcript at `p` reads (the pointer at `p`, the
`Proof`, the stream's buffer) keeps `TranscriptOk` and `ProofApart`; one that also misses the
sponge and the offsets keeps `TranscriptAt`.
-/

namespace Rv64Verifier.Transcript
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model

attribute [local rv_addr] vecPtr vecLen

/-- `w` misses the `n` bytes from `lo`. -/
def Misses (w : Word → Prop) (lo : Word) (n : Nat) : Prop := ∀ y, Within y lo n → ¬ w y

theorem Misses.bytes {w : Word → Prop} {lo : Word} {n : Nat} (h : Misses w lo n) {x : Word}
    {m : Nat} (h1 : lo.toNat ≤ x.toNat) (h2 : x.toNat + m ≤ lo.toNat + n)
    (hn : lo.toNat + n ≤ 2 ^ 64) : ∀ i < m, ¬ w (x + BitVec.ofNat 64 i) :=
  fun i hi ↦ h _ (by addr_omega [h1, h2, hn, hi])

theorem DFrame.proofAt_eq {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {p : Word}
    (hp : Misses w p 8) (hpn : p.toNat + 8 ≤ 2 ^ 64) : proofAt t p = proofAt s p :=
  h p (hp.bytes (Nat.le_refl _) (Nat.le_refl _) hpn)

theorem DFrame.stream' {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {p : Word}
    (hp : Misses w p 8) (hpn : p.toNat + 8 ≤ 2 ^ 64) (hq : Misses w (proofAt s p) 48)
    (hqn : (proofAt s p).toNat + 48 ≤ 2 ^ 64) :
    proofAt t p = proofAt s p ∧ streamPtr t p = streamPtr s p ∧ streamLen t p = streamLen s p :=
  h.stream (hp.bytes (Nat.le_refl _) (Nat.le_refl _) hpn)
    (hq.bytes (Nat.le_refl _) (Nat.le_refl _) hqn)

theorem DFrame.proofApart {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {p : Word}
    (hp : Misses w p 8) (hpn : p.toNat + 8 ≤ 2 ^ 64) (hq : Misses w (proofAt s p) 48)
    (hqn : (proofAt s p).toNat + 48 ≤ 2 ^ 64) {lo : Word} {n : Nat}
    (ha : ProofApart s p lo n) : ProofApart t p lo n := by
  obtain ⟨e0, e1, e2⟩ := h.stream' hp hpn hq hqn
  simp only [ProofApart, e0, e1, e2]
  exact ha

theorem DFrame.transcriptOk {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {p : Word}
    (hok : TranscriptOk s p) (hp : Misses w p 8) (hq : Misses w (proofAt s p) 48) :
    TranscriptOk t p := by
  have hS := hok.self
  have hP := hok.proof
  obtain ⟨e0, e1, e2⟩ := h.stream' hp (by addr_omega [hS]) hq (by addr_omega [hP])
  exact ⟨hok.self, e0 ▸ hok.proof, by rw [e1, e2]; exact hok.stream,
    by simp only [ProofApart, e0, e1, e2]; exact hok.apart⟩

/-- A frame that misses the transcript's reads and its mutable part keeps what it stands for. -/
theorem DFrame.transcriptAt {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {p : Word}
    {T : TState} (hT : TranscriptAt s p T) (hok : TranscriptOk s p) (hp : Misses w p 8)
    (hq : Misses w (proofAt s p) 48)
    (hb : Misses w (streamPtr s p) (24 * streamLen s p))
    (hm : Misses w (p + 8) 352) : TranscriptAt t p T := by
  have hS := hok.self
  have hP := hok.proof
  have hB : streamLen s p = 0 ∨ (streamPtr s p).toNat + 24 * streamLen s p ≤ 2 ^ 64 := by
    rcases hok.stream with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (by addr_omega [h0])
  have keep (y : Word) (h1 : (p + 8).toNat ≤ y.toNat) (h2 : y.toNat + 8 ≤ (p + 8).toNat + 352) :
      t.getMem y = s.getMem y := h y (hm.bytes h1 h2 (by addr_omega [hS]))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hT.stream]
    apply h.eListAt_stream (hp.bytes (Nat.le_refl _) (Nat.le_refl _) (by addr_omega [hS]))
      (hq.bytes (Nat.le_refl _) (Nat.le_refl _) (by addr_omega [hP]))
    rcases hB with h0 | h0
    · intro i hi; rw [h0] at hi; omega
    · exact hb.bytes (Nat.le_refl _) (Nat.le_refl _) h0
  · rw [← hT.sponge]
    exact spongeAt_congr (by addr_omega [hS]) fun y h1 h2 ↦
      keep y (by addr_omega [h1, hS]) (by addr_omega [h2, hS])
  · rw [← hT.streamOffset, keep _ (by addr_omega [hS]) (by addr_omega [hS])]
  · rw [← hT.openingOffset, keep _ (by addr_omega [hS]) (by addr_omega [hS])]

end Rv64Verifier.Transcript
