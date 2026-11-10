import Rv64Verifier.Proofs.Pcs.VsoMerkleRun

/-!
# `verify_stacked_opening`'s Merkle checks, as the mirror runs them

What `MerkleOut` says of the phase in `u`'s memory is `merkleRust`'s checks passing
(`merkleRust_out`). The phase in memory is the entry's (`phaseAt_keep`), which `VsoOpeningsAt`
makes the transcript's, so the mirror's `TM.merkleLeaves` returns the phase's leaves with the
opening offset counted, and the transcript at the block's end stands for that (`merkle_model`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem phaseHdr_eq (s u : MachineState) :
    phaseHdr u (proofAt u (s.getReg .x10)) (u.getMem (s.getReg .x10 + 352)).toNat = phaseH s u := by
  simp only [phaseHdr, phaseH, proofAt, vecPtr]
  rw [BitVec.add_assoc]
  rfl

/-- The phase the Merkle checks read, in `u`'s memory. -/
theorem phaseAt_eq {s u w : MachineState} {ℓ fc : ℕ} (hout : MerkleOut s u w ℓ fc) :
    phaseAt u (proofAt u (s.getReg .x10)) (u.getMem (s.getReg .x10 + 352)).toNat =
      (List.range (u.getReg .x26).toNat).map fun j ↦
        openingAt u (vecPtr u (phaseH s u) + BitVec.ofNat 64 (56 * j)) := by
  simp only [phaseAt, pathAddr]
  rw [phaseHdr_eq, hout.count]

/-- **`merkleRust` passes** on the phase in `u`'s memory. -/
theorem merkleRust_out {s u w : MachineState} {ℓ fc : ℕ} {bl : BitVec 64}
    (hout : MerkleOut s u w ℓ fc) (hbl : Model.log2StrictRust bl = some (u.getReg .x8).toNat) :
    Model.Pcs.merkleRust (digestAt u (s.getReg .x11)) bl
      (u.readWords (u.getMem (s.getReg .x2 - 824)) (u.getReg .x26).toNat) (widthW ℓ fc).toNat
      (phaseAt u (proofAt u (s.getReg .x10)) (u.getMem (s.getReg .x10 + 352)).toNat) =
      some ((phaseAt u (proofAt u (s.getReg .x10)) (u.getMem (s.getReg .x10 + 352)).toNat).map
        (·.leaf)) := by
  rw [phaseAt_eq hout]
  unfold Model.Pcs.merkleRust
  rw [hbl]
  dsimp only
  refine ite_eq_left ⟨fun o ho ↦ ?_, ?_, fun o ho ↦ ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ho
    rw [List.mem_range] at hj
    obtain ⟨e1, e2, -⟩ := hout.scanned j hj
    simp only [openingAt, vecWords, List.length_map, List.length_range, readWords_length]
    refine ⟨by simp only [vecLen]; rw [e1], ?_⟩
    simp only [vecLen]
    rw [BitVec.add_assoc]
    exact congrArg BitVec.toNat e2
  · rw [readWords_eq_map, List.map_map]
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    simp only [Function.comp, openingAt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact (hout.scanned j hj).2.2
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ho
    rw [List.mem_range] at hj
    exact hout.roots j hj

/-- What the function writes misses the `Proof`. -/
theorem proof_misses {s : MachineState} {nx : Word} (hpre : VsoPre s) (hfit : nx.toNat ≤ heapEnd) :
    ∀ y, Within y (proofAt s (s.getReg .x10)) 48 → ¬ Wr s vsoStack (WR s) nx y := by
  have hI := hpre.self
  have hpa := hpre.proofSponge
  have hrp := hpre.rootProof
  simp only [ProofApart] at hpa hrp
  have hP := Region.bounds hI.ok.proof
  intro y hy hW
  rcases hW with (hW | hW) | hW
  · simp only [W] at hW; addr_omega [hy, hW, hpa.1, hP]
  · addr_omega [hy, hW, hrp.1]
  · exact src_misses hfit hI.proofStack.1 hI.proofFree y hy (Or.inr hW)

/-- What the function writes misses the openings. -/
theorem open_misses {s : MachineState} {nx : Word}
    (hO : VsoOpenMem s (s.getReg .x10)) (hfit : nx.toNat ≤ heapEnd) :
    ∀ y, InOpenings s (proofAt s (s.getReg .x10)) y → ¬ Wr s vsoStack (WR s) nx y := by
  intro y hy hW
  obtain ⟨h1, h2, h3, h4, h5⟩ := hO.src y hy
  rcases hW with (hW | hW) | hW | hW | ⟨hW1, hW2⟩
  · exact h4 hW
  · exact h5 hW
  · exact h2 hW
  · exact h3 hW
  · rcases h1 with h | h <;> omega

/-- The openings' count in `u`, the entry's. -/
theorem count_keep {s u : MachineState} {nx : Word} (hpre : VsoPre s) (hinv : InvR s u nx) :
    vecLen u (proofAt s (s.getReg .x10) + 24) = vecLen s (proofAt s (s.getReg .x10) + 24) ∧
      vecPtr u (proofAt s (s.getReg .x10) + 24) = vecPtr s (proofAt s (s.getReg .x10) + 24) := by
  have hP := Region.bounds hpre.self.ok.proof
  have hm := proof_misses hpre hinv.fits
  exact ⟨hinv.mem _ fun j hj hw ↦ hm _ (by addr_omega [hP, hj]) hw,
    hinv.mem _ fun j hj hw ↦ hm _ (by addr_omega [hP, hj]) hw⟩

/-- **The phase in memory is the entry's.** -/
theorem phaseAt_keep {s u : MachineState} {nx : Word} {i : ℕ} (hpre : VsoPre s)
    (hO : VsoOpenMem s (s.getReg .x10)) (hinv : InvR s u nx)
    (hi : i < (vecLen s (proofAt s (s.getReg .x10) + 24)).toNat) :
    phaseAt u (proofAt s (s.getReg .x10)) i = phaseAt s (proofAt s (s.getReg .x10)) i := by
  have hX := hinv.mem
  have hm := open_misses hO hinv.fits
  obtain ⟨e40, e32⟩ := count_keep hpre hinv
  have hH : phaseHdr u (proofAt s (s.getReg .x10)) i = phaseHdr s (proofAt s (s.getReg .x10)) i := by
    simp only [phaseHdr, e32]
  have hR : Region (vecPtr s (proofAt s (s.getReg .x10) + 24))
      (24 * (vecLen s (proofAt s (s.getReg .x10) + 24)).toNat) := by
    rcases hO.hdrs with h0 | h0
    · omega
    · exact h0
  have hRb := Region.bounds hR
  have eH8 : vecPtr u (phaseHdr s (proofAt s (s.getReg .x10)) i) =
      vecPtr s (phaseHdr s (proofAt s (s.getReg .x10)) i) :=
    hX _ fun j hj hw ↦ hm _ (Or.inl (by addr_omega [hRb, hi, hj])) hw
  have eH16 : vecLen u (phaseHdr s (proofAt s (s.getReg .x10)) i) =
      vecLen s (phaseHdr s (proofAt s (s.getReg .x10)) i) :=
    hX _ fun j hj hw ↦ hm _ (Or.inl (by addr_omega [hRb, hi, hj])) hw
  unfold phaseAt
  rw [hH, eH16]
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  have hpa : pathAddr u (proofAt s (s.getReg .x10)) i j = pathAddr s (proofAt s (s.getReg .x10)) i j := by
    simp only [pathAddr, hH, eH8]
  rw [hpa]
  have hQ : Region (vecPtr s (phaseHdr s (proofAt s (s.getReg .x10)) i))
      (56 * (vecLen s (phaseHdr s (proofAt s (s.getReg .x10)) i)).toNat) := by
    rcases hO.paths i hi with h0 | h0
    · omega
    · exact h0
  have hQb := Region.bounds hQ
  have hpb : (pathAddr s (proofAt s (s.getReg .x10)) i j).toNat + 56 ≤ 2 ^ 64 := by
    addr_omega [hQb, hj]
  obtain ⟨hl, hs⟩ := hO.leaves i hi j hj
  apply openingAt_keep hX hpb (fun y hy ↦ hm y (Or.inr ⟨i, hi, Or.inl (by addr_omega [hy, hQb, hj])⟩))
  · rcases hl with h0 | h0
    · exact Or.inl h0
    · exact Or.inr ⟨by have := Region.bounds h0; omega,
        fun y hy ↦ hm y (Or.inr ⟨i, hi, Or.inr ⟨j, hj, Or.inl hy⟩⟩)⟩
  · rcases hs with h0 | h0
    · exact Or.inl h0
    · exact Or.inr ⟨by have := Region.bounds (region_wide h0); omega,
        fun y hy ↦ hm y (Or.inr ⟨i, hi, Or.inr ⟨j, hj, Or.inr hy⟩⟩)⟩

end Rv64Verifier.Proofs.Pcs.Vso
