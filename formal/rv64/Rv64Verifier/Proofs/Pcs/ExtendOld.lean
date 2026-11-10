import Rv64Verifier.Proofs.Pcs.ExtendLoop

/-!
# `Vec<StackClaim>::extend_desugared`: the `Vec`'s claims at the entry

What `ExtendPre` says of the claims already on the `Vec` makes their regions safe.
-/

namespace Rv64Verifier.Proofs.Pcs.Extend
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Transcript Rv64Verifier.Pcs
  Rv64Verifier.PcsContracts Rv64Verifier.Model.Pcs LeanVM.Parameters

theorem safe_of_src {s : MachineState} {a : Word} {n : Nat} (hpre : Walk.ExtendPreE s)
    (hs : Src s extendStack a n) (ho : ExtendOff s a n) : Safe s s a n := by
  rcases hs.region with h0 | hR
  · exact Or.inl h0
  have hf := hs.free
  simp only [Outside] at hf
  exact Or.inr ⟨hR, ho, hs.stack, hf.2, hf.1,
    Or.inr (Or.inl (by simp only [spareLen, hpre.full, Nat.sub_self, Nat.mul_zero]))⟩

theorem off_of {s : MachineState} {a : Word} {n : Nat}
    (h0 : Apart a n (s.getReg .x10) 24) (h1 : Apart a n (s.getReg .x11) 24) : ExtendOff s a n :=
  ⟨h0, h1⟩

theorem claim_pre {s : MachineState} (hpre : Walk.ExtendPreE s) {i : Nat}
    (hi : i < (vecLen s (s.getReg .x10)).toNat) :
    ClaimRegions (Safe s s) s (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (88 * i)) := by
  have hE := hpre.elems
  have hEo := hpre.elemsOff
  have hR := hE.region.resolve_left (by omega)
  have hRb := Region.bounds hR
  have hws := hpre.weights i hi
  have hwo := hpre.weightsOff i hi
  refine ⟨safe_of_src hpre (hE.sub (by addr_omega [hRb, hi]) (by addr_omega [hRb, hi])
      (by addr_omega [hRb, hi])) ⟨by addr_omega [hEo.1, hRb, hi], by addr_omega [hEo.2, hRb, hi]⟩, ?_⟩
  obtain ⟨-, hw⟩ := hws
  obtain ⟨hw0, hw1⟩ := hwo
  have n32 : vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (88 * i) + 8 + 24 =
      vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (88 * i) + 32 := add_lit _ _ _ _ rfl
  unfold WeightApart RingApart at hw0 hw1
  by_cases h1 : s.getMem (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (88 * i)) = eqTag
  · simp only [h1, ↓reduceIte] at hw hw0 hw1 ⊢
    exact safe_of_src hpre hw (off_of hw0 hw1)
  by_cases h2 : s.getMem (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (88 * i)) = ringTag
  · simp only [h2, ↓reduceIte] at hw hw0 hw1 ⊢
    rw [n32] at hw0 hw1
    have hp := hw.point
    have hc := hw.coeffs
    rw [n32] at hc
    exact ⟨safe_of_src hpre hp (off_of hw0.1 hw1.1), safe_of_src hpre hc (off_of hw0.2 hw1.2)⟩
  · simp only [h1, h2, ↓reduceIte] at hw hw0 hw1 ⊢
    exact ⟨safe_of_src hpre hw.point (off_of hw0.1 hw1.1),
      safe_of_src hpre hw.coeffs (off_of hw0.2 hw1.2)⟩

end Rv64Verifier.Proofs.Pcs.Extend
