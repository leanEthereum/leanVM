import Rv64Verifier.Proofs.Pcs.VsoMerkleModel

/-!
# `verify_stacked_opening`'s Merkle checks: the mirror's step

`merkle_model`: on the transcript `u` stands for, the mirror's `TM.merkleLeaves` at level `ℓ`
returns the leaves of the phase the checks read and counts it, and the transcript at the block's
end `w` stands for the result. Commitment `ℓ` must be recorded with the root at `[S - 840]`, the
height the checks compared the siblings' counts with (`s0`) and the leaf's width, and the block
length's `log2_strict` must be that height.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- Read in place and apart from the sponge and offsets: `Clear`. -/
theorem clear_of_outside {s : MachineState} {lo : ℕ} {a : Word} {n : ℕ}
    (hst : Apart a n (stackLo s vsoStack) vsoStack) (hf : Outside s a n)
    (hsp : Apart a n (s.getReg .x10 + 8) 352) (hlo : heapNext s ≤ lo) : Clear s lo a n := by
  rw [stackLo_vso, vso_stack] at hst
  simp only [Outside] at hf
  refine ⟨⟨?_, hst, hf.2⟩, hsp⟩
  rcases hf.1 with h | h
  · exact Or.inl (by omega)
  · exact Or.inr h

/-- **The mirror's Merkle step**, and the transcript at the block's end. -/
theorem merkle_model {s u w : MachineState} {ℓ fc : ℕ} {T0 T : Model.TState} {bl : BitVec 64}
    (hpre : VsoPre s) (hm : MerkleIn s u ℓ fc) (hout : MerkleOut s u w ℓ fc)
    (hO : VsoOpeningsAt s (s.getReg .x10) T0) (hT : TranscriptAt u (s.getReg .x10) T)
    (hproof : T.proof = T0.proof)
    (hroot : T.roots[ℓ]? =
      some (digestAt u (s.getReg .x11), (u.getReg .x8).toNat, (widthW ℓ fc).toNat))
    (hbl : Model.log2StrictRust bl = some (u.getReg .x8).toNat) :
    (Model.Pcs.TM.merkleLeaves ℓ (u.readWords (u.getMem (s.getReg .x2 - 824)) (u.getReg .x26).toNat)
      (widthW ℓ fc).toNat).run T =
      some ((T.proof.openings[T.openingOffset]!).map (·.leaf),
        { T with openingOffset := T.openingOffset + 1 }) ∧
    TranscriptAt w (s.getReg .x10) { T with openingOffset := T.openingOffset + 1 } := by
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hb := bounds hpre
  obtain ⟨-, e0, e1, e2⟩ := trR_facts hpre hm.inv
  obtain ⟨e40, -⟩ := count_keep hpre hm.inv
  have hoff : (u.getMem (s.getReg .x10 + 352)).toNat = T.openingOffset := hT.openingOffset
  have ecount : vecLen u (proofAt s (s.getReg .x10) + 24) =
      u.getMem (u.getMem (s.getReg .x10) + 40) := by
    rw [← e0]; simp only [vecLen, proofAt]; rw [BitVec.add_assoc]; rfl
  have hcnt : (u.getMem (s.getReg .x10 + 352)).toNat <
      (vecLen s (proofAt s (s.getReg .x10) + 24)).toNat := by
    rw [← e40, ecount]; exact hout.hdr
  have hlen : T.openingOffset < T.proof.openings.length := by
    rw [hproof, ← hO.count, ← hoff]; exact hcnt
  have hph : phaseAt u (proofAt u (s.getReg .x10)) (u.getMem (s.getReg .x10 + 352)).toNat =
      T.proof.openings[T.openingOffset]! := by
    rw [e0, phaseAt_keep hpre hO hm.inv hcnt, hO.phases _ (by rw [← hO.count]; exact hcnt), hproof,
      hoff]
  have hget : T.proof.openings[T.openingOffset]? =
      some (phaseAt u (proofAt u (s.getReg .x10)) (u.getMem (s.getReg .x10 + 352)).toNat) := by
    rw [hph]; simp [hlen]
  have hidx : ∀ o ∈ phaseAt u (proofAt u (s.getReg .x10)) (u.getMem (s.getReg .x10 + 352)).toNat,
      o.leafIndex < 2 ^ 64 := by
    intro o ho
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp ho
    simp only [openingAt]
    exact BitVec.isLt _
  refine ⟨by rw [Model.Pcs.merkleRust_run hroot hbl hget hidx (merkleRust_out hout hbl), hph], ?_⟩
  -- the transcript at `w`
  have hu := hm.inv.heap hpre.heap
  have hhi := (hout.inv.heap hpre.heap).hi
  have hlo : heapNext s ≤ heapNext u := hm.inv.mono
  have hst := hI.stack
  rw [stackLo_vso, vso_stack] at hst
  have hTf := hI.free
  simp only [Outside] at hTf
  obtain ⟨hnx, -⟩ := sfacts hpre
  have keepT (x : Word) (h1 : (s.getReg .x10).toNat ≤ x.toNat)
      (h2 : x.toNat + 8 ≤ (s.getReg .x10).toNat + 352) : w.getMem x = u.getMem x :=
    hout.fr x fun i hi hw ↦ by
      rcases hw with (hw | hw | hw) | (hw | hw | hw | hw) | hw | hw | ⟨hw1, hw2⟩
      · addr_omega [hw, hi, h1, h2, hS]
      · addr_omega [hw, hi, h1, h2, hS, hst, hb]
      · addr_omega [hw, hi, h1, h2, hS, hst, hb]
      · addr_omega [hw, hi, h1, h2, hS, hst, hb]
      · addr_omega [hw, hi, h1, h2, hS, hst, hb]
      · addr_omega [hw, hi, h1, h2, hS, hst, hb]
      · addr_omega [hw, hi, h1, h2, hS, hst, hb]
      · addr_omega [hw, hi, h1, h2, hS, hst, hb]
      · addr_omega [hw, hi, h1, h2, hS, hTf.2]
      · rcases hTf.1 with h | h
        · addr_omega [hw1, hi, h1, h2, hS, h, hlo]
        · addr_omega [hw2, hi, h1, h2, hS, h, hhi]
  have hpa := hpre.proofSponge
  simp only [ProofApart] at hpa
  have cP : Clear s (heapNext u) (proofAt s (s.getReg .x10)) 48 :=
    clear_of_outside hI.proofStack.1 hI.proofFree hpa.1 hlo
  have cB : Clear s (heapNext u) (streamPtr s (s.getReg .x10)) (24 * streamLen s (s.getReg .x10)) :=
    clear_of_outside hI.proofStack.2 hI.streamFree hpa.2 hlo
  have hPb := Region.bounds hI.ok.proof
  refine ⟨?_, ?_, ?_, ?_⟩
  · show _ = T.proof.stream
    rw [← hT.stream]
    apply hout.fr.eListAt_stream
    · intro i hi hw
      rcases hw with (hw | hw | hw) | (hw | hw | hw | hw) | hw | hw | ⟨hw1, hw2⟩
      · addr_omega [hw, hi, hS]
      · addr_omega [hw, hi, hS, hst, hb]
      · addr_omega [hw, hi, hS, hst, hb]
      · addr_omega [hw, hi, hS, hst, hb]
      · addr_omega [hw, hi, hS, hst, hb]
      · addr_omega [hw, hi, hS, hst, hb]
      · addr_omega [hw, hi, hS, hst, hb]
      · addr_omega [hw, hi, hS, hst, hb]
      · addr_omega [hw, hi, hS, hTf.2]
      · rcases hTf.1 with h | h
        · addr_omega [hw1, hi, hS, h, hlo]
        · addr_omega [hw2, hi, hS, h, hhi]
    · intro i hi
      rw [e0]
      exact cP.misses hpre hhi _ (by addr_omega [hi, hPb])
    · rcases hI.ok.stream with h0 | h0
      · intro i hi; rw [e2, h0] at hi; omega
      · have hBb := Region.bounds h0
        intro i hi
        rw [e1]
        rw [e2] at hi
        exact cB.misses hpre hhi _ (by addr_omega [hi, hBb])
  · show _ = T.sponge
    rw [← hT.sponge]
    exact spongeAt_congr (by addr_omega [hS]) fun y h1 h2 ↦
      keepT y (by addr_omega [h1, hS]) (by addr_omega [h2, hS])
  · show _ = T.streamOffset
    rw [← hT.streamOffset, keepT _ (by addr_omega [hS]) (by addr_omega [hS])]
  · show _ = T.openingOffset + 1
    have hc := (u.getMem (u.getMem (s.getReg .x10) + 40)).isLt
    have hd := hout.hdr
    rw [hout.off, ← hoff, BitVec.toNat_add, show (1 : Word).toNat = 1 from rfl]
    omega

end Rv64Verifier.Proofs.Pcs.Vso
