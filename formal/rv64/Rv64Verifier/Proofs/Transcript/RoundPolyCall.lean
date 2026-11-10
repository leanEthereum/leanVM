import Rv64Verifier.Proofs.Transcript.RoundPolyLoop

/-!
# `sumcheck_round_poly`'s calls to `next_scalars`

Both paths call `next_scalars` with the result at `S - 152` and the stack below `S - 160`
(`call_ns`): the frame (`Fr`) is kept, and the result is what `NextScalarsPost` says.
-/

namespace Rv64Verifier.Transcript.RoundPoly
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F44
  Rv64Verifier.Contracts LeanVM.Protocol.Verifier
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- Where the function ends: its return, with the contract, or a dead end. -/
def Done (s t : MachineState) : Prop :=
  (t.pc = returnAddress s ∧ Preserves s t ∧ RoundPolyPost s t) ∨ Dead Image.code t

/-- After `next_scalars` called from `c` returns at `t`. -/
structure CallOut (s c t : MachineState) : Prop where
  fr : Fr s t
  pres : Preserves c t
  value : ∀ T, TranscriptAt c (s.getReg .x11) T →
    match (TM.nextScalars (c.getReg .x12).toNat).run T with
    | some (xs, T') => vecCap t (s.getReg .x2 - 152) ≠ errNiche ∧
        NewVecE c t (s.getReg .x2 - 152) xs ∧ TranscriptAt t (s.getReg .x11) T'
    | none => vecCap t (s.getReg .x2 - 152) = errNiche
  ok : VecResult c t (s.getReg .x2 - 152)
  err : vecCap t (s.getReg .x2 - 152) = errNiche →
    t.getMem (s.getReg .x2 - 152 + 8) ≠ errNiche

set_option maxHeartbeats 1000000 in
theorem call_ns (hNS : NextScalarsSpec) {s c : MachineState} (hpre : RoundPolyPre s) (h : Fr s c)
    (hpc : c.pc = 0x80004818) (x10 : c.getReg .x10 = s.getReg .x2 - 152)
    (x11 : c.getReg .x11 = s.getReg .x11) :
    ∃ t, Reaches Image.code c t ∧ ((t.pc = returnAddress c ∧ CallOut s c t) ∨ Dead Image.code t) := by
  have hb := bounds hpre
  have hS : 80 ≤ (s.getReg .x2).toNat := by addr_omega [hb]
  have hst := hpre.stack
  have hself := hpre.selfStack
  have x2 := h.saved.x2
  have F : DFrame s c (TW 24 roundPolyStack s c) := h.frame.mono fun _ h ↦ h.toW
  have hnp : NextScalarsPre c := TPre.callee 160 hpre.toTPre h.heap h.mono F
    (by rw [x2]; rfl) x11 (Nat.le_refl _) (by decide) (by decide) (by decide) (by decide)
    (by rw [x10]; refine ⟨?_, ?_, ?_⟩ <;> addr_omega [hb])
  obtain ⟨t, hr, ⟨hpct, hprest, hpost⟩ | hd⟩ := hNS c hpc hnp
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  have G := hpost.frame
  simp only [TFrame, stackLo, x2, x10, x11] at G
  have mono := hpost.mono
  have hhi := hpost.heap.hi
  have miss (y : Word) (h1 : (s.getReg .x2).toNat - 80 ≤ y.toNat) (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat) :
      t.getMem y = c.getMem y :=
    G y fun i hi hw ↦ by
      rcases hw with hw | hw | hw | hw | hw <;>
        addr_omega [hw, hi, h1, h2, hb, hself, hpre.self.self, hst.next, hst.above, hhi]
  refine ⟨t, hr, Or.inl ⟨hpct, {
    fr := {
      saved := h.saved.step hS (hprest.reg .x2) (fun r hr ↦ hprest r (by
        simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide)) miss
      x8 := (hprest.reg .x8).trans h.x8
      heap := hpost.heap
      mono := h.mono.trans mono
      frame := (h.frame.mono fun a h ↦ V.mono mono h).trans G fun a hw ↦ by
        rcases hw with hw | hw | hw | hw | hw
        · exact Or.inr (Or.inl (by addr_omega [hw, hb]))
        · exact Or.inl hw
        · exact Or.inr (Or.inl (by addr_omega [hw, hb]))
        · exact Or.inr (Or.inr (Or.inl hw))
        · exact Or.inr (Or.inr (Or.inr ⟨by have := h.mono; simp only [Fresh] at hw; omega, hw.2⟩)) }
    pres := hprest
    value := by
      have v := hpost.value
      rw [x10, x11] at v
      exact v
    ok := by
      have v := hpost.ok
      rw [x10] at v
      exact v
    err := by
      have v := hpost.err
      rw [x10] at v
      exact v }⟩⟩

end Rv64Verifier.Transcript.RoundPoly
