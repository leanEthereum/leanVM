import Rv64Verifier.Proofs.Pcs.VsoMerkleT

/-!
# `verify_stacked_opening`'s Merkle checks: their inputs from the openings

The openings `VsoOpenMem` places at the entry are read in place and never written, so inside the
function (`InvR`) the phase to read is `PhaseOk` (`phaseOk_of`) and the front's header facts hold
(`frontIn_of`); `merkleIn_of` assembles `MerkleIn` from what the level's earlier steps establish:
the registers and slots at `0x8000aa14` and the queries' buffer.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- Ranges with no byte in common are apart. -/
theorem apart_of {a b : Word} {n m : ℕ} (h : ∀ y, Within y a n → ¬ Within y b m) :
    Apart a n b m := by
  simp only [Apart]
  by_contra hc
  simp only [not_or, not_le] at hc
  obtain ⟨hn, hm, h1, h2⟩ := hc
  rcases Nat.le_total a.toNat b.toNat with hab | hab
  · exact h b ⟨hab, by omega⟩ ⟨le_refl _, by omega⟩
  · exact h a ⟨le_refl _, by omega⟩ ⟨hab, by omega⟩

/-- A region whose every byte is below the entry's `NEXT` or above the heap, off the stack, `NEXT`
and the sponge, is `Clear`. -/
theorem clear_of_src {s : MachineState} {lo : ℕ} {a : Word} {n : ℕ} (hr : Region a n) (hn : 0 < n)
    (hlo : heapNext s ≤ lo)
    (h : ∀ y, Within y a n → (y.toNat < heapNext s ∨ heapEnd ≤ y.toNat) ∧
      ¬ Within y (stackLo s vsoStack) vsoStack ∧ ¬ Within y nextAddr 8 ∧
      ¬ Within y (s.getReg .x10 + 8) 352) :
    Clear s lo a n := by
  have hb : a.toNat + n ≤ 2 ^ 64 := by have := Region.bounds hr; omega
  refine ⟨⟨?_, apart_of fun y hy hs ↦ (h y hy).2.1 (by rw [stackLo_vso, vso_stack]; exact hs),
    apart_of fun y hy ↦ (h y hy).2.2.1⟩, apart_of fun y hy ↦ (h y hy).2.2.2⟩
  have hl := (h (a + BitVec.ofNat 64 (n - 1)) (by addr_omega [hb, hn])).1
  have hm := hr.1
  simp only [Mapped] at hm
  rcases hl with hl | hl
  · left; rw [toNat_add_ofNat (by omega)] at hl; omega
  · right; rw [toNat_add_ofNat (by omega)] at hl; simp only [heapEnd] at hl ⊢; omega

/-- A path header's doubleword, kept inside the function. -/
theorem pathHdr_keep {s u : MachineState} {nx : Word} {i j o : ℕ}
    (hO : VsoOpenMem s (s.getReg .x10)) (hinv : InvR s u nx)
    (hi : i < (vecLen s (proofAt s (s.getReg .x10) + 24)).toNat)
    (hj : j < (vecLen s (phaseHdr s (proofAt s (s.getReg .x10)) i)).toNat) (ho : o + 8 ≤ 56) :
    u.getMem (pathAddr s (proofAt s (s.getReg .x10)) i j + BitVec.ofNat 64 o) =
      s.getMem (pathAddr s (proofAt s (s.getReg .x10)) i j + BitVec.ofNat 64 o) := by
  have hm := open_misses hO hinv.fits
  have hQ : Region (vecPtr s (phaseHdr s (proofAt s (s.getReg .x10)) i))
      (56 * (vecLen s (phaseHdr s (proofAt s (s.getReg .x10)) i)).toNat) := by
    rcases hO.paths i hi with h0 | h0
    · omega
    · exact h0
  have hQb := Region.bounds hQ
  exact hinv.mem _ fun k hk hw ↦ hm _ (Or.inr ⟨i, hi, Or.inl (by addr_omega [hQb, hj, ho, hk])⟩) hw

/-- The phase header the front reads, the entry's. -/
theorem phaseH_eq {s u : MachineState} {nx : Word} (hpre : VsoPre s) (hinv : InvR s u nx) :
    phaseH s u = phaseHdr s (proofAt s (s.getReg .x10)) (u.getMem (s.getReg .x10 + 352)).toNat := by
  obtain ⟨-, e0, -, -⟩ := trR_facts hpre hinv
  obtain ⟨-, e32⟩ := count_keep hpre hinv
  rw [← phaseHdr_eq, e0]
  simp only [phaseHdr, e32]

theorem off_lt {s u : MachineState} {nx : Word} (hpre : VsoPre s) (hinv : InvR s u nx)
    (hoff : (u.getMem (s.getReg .x10 + 352)).toNat <
      (u.getMem (u.getMem (s.getReg .x10) + 40)).toNat) :
    (u.getMem (s.getReg .x10 + 352)).toNat < (vecLen s (proofAt s (s.getReg .x10) + 24)).toNat := by
  obtain ⟨-, e0, -, -⟩ := trR_facts hpre hinv
  obtain ⟨e40, -⟩ := count_keep hpre hinv
  have ecount : vecLen u (proofAt s (s.getReg .x10) + 24) =
      u.getMem (u.getMem (s.getReg .x10) + 40) := by
    rw [← e0]; simp only [vecLen, proofAt]; rw [BitVec.add_assoc]; rfl
  rw [← e40, ecount]; exact hoff

/-- **The phase to read is `PhaseOk`.** -/
theorem phaseOk_of {s u : MachineState} (hpre : VsoPre s)
    (hO : VsoOpenMem s (s.getReg .x10)) (hinv : InvR s u (u.getMem nextAddr))
    (hoff : (u.getMem (s.getReg .x10 + 352)).toNat <
      (u.getMem (u.getMem (s.getReg .x10) + 40)).toNat) :
    PhaseOk s u (phaseH s u) := by
  have hi := off_lt hpre hinv hoff
  rw [phaseH_eq hpre hinv]
  generalize (u.getMem (s.getReg .x10 + 352)).toNat = i at hi
  have hX := hinv.mem
  have hm := open_misses hO hinv.fits
  have hlo : heapNext s ≤ heapNext u := hinv.mono
  have src' (y : Word) (hy : InOpenings s (proofAt s (s.getReg .x10)) y) :
      (y.toNat < heapNext s ∨ heapEnd ≤ y.toNat) ∧ ¬ Within y (stackLo s vsoStack) vsoStack ∧
        ¬ Within y nextAddr 8 ∧ ¬ Within y (s.getReg .x10 + 8) 352 :=
    let h := hO.src y hy; ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
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
  have hdrR : Region (phaseHdr s (proofAt s (s.getReg .x10)) i) 24 :=
    region_sub hR (24 * i) 24 (by omega) (by omega)
  refine ⟨clear_of_src hdrR (by decide) hlo fun y hy ↦ src' y (Or.inl (by addr_omega [hy, hRb, hi])),
    ?_, fun j hj ↦ ?_, fun j hj ↦ ?_⟩
  · unfold BufOk
    rw [eH8, eH16]
    by_cases h0 : (vecLen s (phaseHdr s (proofAt s (s.getReg .x10)) i)).toNat = 0
    · exact Or.inl h0
    rcases hO.paths i hi with h1 | hQ
    · exact absurd h1 h0
    exact Or.inr ⟨hQ, clear_of_src hQ (by omega) hlo fun y hy ↦ src' y (Or.inr ⟨i, hi, Or.inl hy⟩)⟩
  · rw [eH16] at hj
    unfold BufOk
    rw [eH8]
    rw [show vecPtr s (phaseHdr s (proofAt s (s.getReg .x10)) i) + BitVec.ofNat 64 (56 * j) =
      pathAddr s (proofAt s (s.getReg .x10)) i j from rfl]
    have k (o : ℕ) (ho : o + 8 ≤ 56) := pathHdr_keep hO hinv hi hj ho
    have e8 : vecPtr u (pathAddr s (proofAt s (s.getReg .x10)) i j) =
        vecPtr s (pathAddr s (proofAt s (s.getReg .x10)) i j) := k 8 (by decide)
    have e16 : vecLen u (pathAddr s (proofAt s (s.getReg .x10)) i j) =
        vecLen s (pathAddr s (proofAt s (s.getReg .x10)) i j) := k 16 (by decide)
    rw [e8, e16]
    by_cases h0 : (vecLen s (pathAddr s (proofAt s (s.getReg .x10)) i j)).toNat = 0
    · exact Or.inl h0
    rcases (hO.leaves i hi j hj).1 with h1 | hL
    · exact absurd h1 h0
    exact Or.inr ⟨hL, clear_of_src hL (by omega) hlo fun y hy ↦
      src' y (Or.inr ⟨i, hi, Or.inr ⟨j, hj, Or.inl hy⟩⟩)⟩
  · rw [eH16] at hj
    unfold SibOk
    rw [eH8]
    rw [show vecPtr s (phaseHdr s (proofAt s (s.getReg .x10)) i) + BitVec.ofNat 64 (56 * j) =
      pathAddr s (proofAt s (s.getReg .x10)) i j from rfl]
    have k (o : ℕ) (ho : o + 8 ≤ 56) := pathHdr_keep hO hinv hi hj ho
    have e32 : vecPtr u (pathAddr s (proofAt s (s.getReg .x10)) i j + 24) =
        vecPtr s (pathAddr s (proofAt s (s.getReg .x10)) i j + 24) := by
      simp only [vecPtr]; rw [BitVec.add_assoc]; exact k 32 (by decide)
    have e40 : vecLen u (pathAddr s (proofAt s (s.getReg .x10)) i j + 24) =
        vecLen s (pathAddr s (proofAt s (s.getReg .x10)) i j + 24) := by
      simp only [vecLen]; rw [BitVec.add_assoc]; exact k 40 (by decide)
    rw [e32, e40]
    by_cases h0 : (vecLen s (pathAddr s (proofAt s (s.getReg .x10)) i j + 24)).toNat = 0
    · exact Or.inl h0
    rcases (hO.leaves i hi j hj).2 with h1 | hL
    · exact absurd h1 h0
    have hW := region_wide hL
    exact Or.inr ⟨hW, clear_of_src hW (by simp only [sibSpan]; omega) hlo fun y hy ↦
      src' y (Or.inr ⟨i, hi, Or.inr ⟨j, hj, Or.inr hy⟩⟩)⟩

/-- **The front's inputs**, from the openings and what the level's steps establish. -/
theorem frontIn_of {s u : MachineState} {ℓ fc : ℕ} (hpre : VsoPre s)
    (hO : VsoOpenMem s (s.getReg .x10)) (hinv : InvR s u (u.getMem nextAddr))
    (hpc : u.pc = 0x8000aa14) (hsp : u.getReg .x2 = s.getReg .x2 - 1040)
    (hx20 : u.getReg .x20 = s.getReg .x10) (hlvl : u.getMem (s.getReg .x2 - 856) = BitVec.ofNat 64 ℓ)
    (hfold : u.getMem (s.getReg .x2 - 784) = BitVec.ofNat 64 fc) : FrontIn s u ℓ fc := by
  have hS := Region.bounds hpre.self.ok.self
  refine ⟨hpc, hsp, hx20, hlvl, hfold, hpre.self.ok.self, (trR_facts hpre hinv).1.proof, fun hoff ↦ ?_⟩
  have hc := (phaseOk_of hpre hO hinv hoff).hdr.2
  have hi := off_lt hpre hinv hoff
  have hR : Region (vecPtr s (proofAt s (s.getReg .x10) + 24))
      (24 * (vecLen s (proofAt s (s.getReg .x10) + 24)).toNat) := by
    rcases hO.hdrs with h0 | h0
    · omega
    · exact h0
  have hr : Region (phaseH s u) 24 := by
    rw [phaseH_eq hpre hinv]; exact region_sub hR _ 24 (by omega) (by omega)
  have hrb := Region.bounds hr
  have ha : Apart (phaseH s u) 24 (s.getReg .x10 + 352) 8 := by addr_omega [hc, hS, hrb]
  exact ⟨hr, ha⟩

/-- **`MerkleIn`**, from the openings and what the level's steps establish. -/
theorem merkleIn_of {s u : MachineState} {ℓ fc : ℕ} (hpre : VsoPre s)
    (hO : VsoOpenMem s (s.getReg .x10)) (hinv : InvR s u (u.getMem nextAddr))
    (hpc : u.pc = 0x8000aa14) (hsp : u.getReg .x2 = s.getReg .x2 - 1040)
    (hx20 : u.getReg .x20 = s.getReg .x10) (hlvl : u.getMem (s.getReg .x2 - 856) = BitVec.ofNat 64 ℓ)
    (hfold : u.getMem (s.getReg .x2 - 784) = BitVec.ofNat 64 fc) (hℓ : ℓ < 2 ^ 64)
    (hfc : fc < 2 ^ 64) (hroot : u.getMem (s.getReg .x2 - 840) = s.getReg .x11)
    (hq : (u.getReg .x26).toNat = 0 ∨
      Region (u.getMem (s.getReg .x2 - 824)) (8 * (u.getReg .x26).toNat) ∧
        Clear s (heapNext u) (u.getMem (s.getReg .x2 - 824)) (8 * (u.getReg .x26).toNat))
    (hx23 : u.getReg .x23 = u.getMem (s.getReg .x2 - 808)) :
    MerkleIn s u ℓ fc :=
  ⟨frontIn_of hpre hO hinv hpc hsp hx20 hlvl hfold, hℓ, hfc, hinv, hroot, hq,
    phaseOk_of hpre hO hinv, hx23⟩

end Rv64Verifier.Proofs.Pcs.Vso
