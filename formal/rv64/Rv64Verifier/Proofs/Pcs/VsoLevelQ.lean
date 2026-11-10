import Rv64Verifier.Proofs.Pcs.VsoUniform

/-!
# `verify_stacked_opening`'s level loop: the slots the queries and the Merkle checks read

At `0x8000a790` (`Opened`) the level's slots set before its fold rounds are still in the frame
(`Opened.slots`): the level, `QP`, the root's address, `8 ℓ`, the rate, the transcript, `QL` and
the fold count.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The slots the fold rounds keep from `S - 816` to `S - 792`. -/
theorem FW.keepMid {s : MachineState} {x : LCtx} {h u : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {fl lfs q : List E} (hpre : VsoPre s)
    (hr : RB s x h u ℓ Wl fl lfs q) {y : Word}
    (hy : (s.getReg .x2 - 816).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 792).toNat) :
    u.getMem y = h.getMem y := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hf := hr.head.facts
  have hhi := hr.heap.hi
  refine hr.fr y fun i hi hw ↦ ?_
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
  · addr_omega [hw, hi, hy, hb]
  · addr_omega [hw, hi, hy, hb]
  · addr_omega [hw, hi, hy, hb]
  · addr_omega [hw, hi, hy, hb]
  · addr_omega [hw, hi, hy, hb]
  · addr_omega [hw, hi, hy, hb]
  · addr_omega [hw, hi, hy, hb, hnx]
  · addr_omega [hw.2, hi, hy, hb, hhi]
  · simp only [W] at hw; addr_omega [hw, hi, hy, hb, hIs, hS]
  · rcases hf.F with h0 | h0
    · simp only [Within] at hw; omega
    · addr_omega [hw, hi, hy, hb, h0.2, hf.hend]

theorem Opened.slots {s : MachineState} {x : LCtx} {h t u : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf q res : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} (hpre : VsoPre s)
    (ho : Opened s x h t u ℓ Wl lf q res pend d) :
    u.getMem (s.getReg .x2 - 856) = BitVec.ofNat 64 ℓ ∧ u.getMem (s.getReg .x2 - 848) = x.QP ∧
      u.getMem (s.getReg .x2 - 840) = s.getReg .x11 ∧
      u.getMem (s.getReg .x2 - 832) = BitVec.ofNat 64 (8 * ℓ) ∧
      u.getMem (s.getReg .x2 - 824) = BitVec.ofNat 64 (rtOf s ℓ) ∧
      u.getMem (s.getReg .x2 - 816) = s.getReg .x10 ∧ u.getMem (s.getReg .x2 - 800) = x.QL ∧
      u.getMem (s.getReg .x2 - 784) = BitVec.ofNat 64 (fcOf s ℓ) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hf := ho.fo
  have hh := hf.head
  have hk := LM.kept hpre hh.fr hh.heap.hi hh.cfg.kept
  have hhi := ho.heap.hi
  have kO (y : Word) (hy : (s.getReg .x2 - 856).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 808).toNat ∨ (s.getReg .x2 - 800).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 792).toNat ∨ (s.getReg .x2 - 784).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 776).toNat) : u.getMem y = t.getMem y :=
    ho.fr y fun i hi hx ↦ by
      rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx <;> first
        | addr_omega [hx, hi, hy, hb]
        | addr_omega [hx, hi, hy, hb, hnx]
        | (simp only [W] at hx; addr_omega [hx, hi, hy, hb, hS, hIs])
        | (simp only [Fresh] at hx; addr_omega [hx.2, hi, hy, hb, hhi])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [kO _ (by addr_omega [hb])]; exact hf.m184
  · rw [kO _ (by addr_omega [hb]), FW.keepHi hpre hf.toRB (by addr_omega [hb])]; exact hk.qp
  · rw [kO _ (by addr_omega [hb])]; exact Folded.root hpre hf
  · rw [kO _ (by addr_omega [hb])]; exact hf.m208
  · rw [kO _ (by addr_omega [hb])]; exact hf.m216
  · rw [kO _ (by addr_omega [hb]), FW.keepMid hpre hf.toRB (by addr_omega [hb])]; exact hh.m224
  · rw [kO _ (by addr_omega [hb]), FW.keepMid hpre hf.toRB (by addr_omega [hb])]; exact hk.ql
  · rw [kO _ (by addr_omega [hb])]; exact hf.m256

end Rv64Verifier.Proofs.Pcs.Vso
