import Rv64Verifier.Proofs.Pcs.ExtendRoomCases

/-!
# `Vec<StackClaim>::extend_desugared`: a pass within the function's frame

What a pass writes (`StepW`) is what the function may write and misses its saved registers; a
region safe before a pass stays safe after it.
-/

namespace Rv64Verifier.Proofs.Pcs.Extend
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Transcript Rv64Verifier.Pcs
  Rv64Verifier.PcsContracts Rv64Verifier.Model.Pcs LeanVM.Parameters

theorem spare_heap {s u : MachineState} {j : Nat} (hI : Inv s u j) {x : Word}
    (h : Within x (spareLo u (s.getReg .x10)) (spareLen u (s.getReg .x10))) :
    heapNext s ≤ x.toNat ∧ x.toNat < heapNext u := by
  have hl := hI.vec.len
  rcases hI.buf with he | hn
  · simp only [Within, spareLen, he, Nat.sub_self, Nat.mul_zero] at h; omega
  · simp only [NewBuf] at hn
    rcases hn with ⟨-, h0 | ⟨h1, h2⟩⟩
    · simp only [Within, spareLen] at h
      have : (vecCap u (s.getReg .x10)).toNat = 0 := by omega
      omega
    · have hlt : heapNext u < 2 ^ 64 := (u.getMem nextAddr).isLt
      simp only [Within, spareLo, spareLen] at h
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)] at h
      omega

theorem stepW_wr {s u : MachineState} {j : Nat} (hI : Inv s u j) {nx x : Word}
    (hnx : heapNext u ≤ nx.toNat) (hx : StepW s u nx x) : Wr s extendStack (W s) nx x := by
  have hu' : heapNext s ≤ heapNext u := hI.p.mono
  rcases hx with h | h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inl (by addr_omega [h]))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨by omega, h.2⟩))
  · have := spare_heap hI h
    exact Or.inr (Or.inr (Or.inr ⟨this.1, by omega⟩))

theorem stepW_slot {s u : MachineState} {j : Nat} (hpre : ExtendPre s) (hI : Inv s u j)
    {nx x : Word} (hnx : nx.toNat ≤ heapEnd) (hx : StepW s u nx x) :
    ¬ Within x (s.getReg .x2 - BitVec.ofNat 64 104) 104 := by
  have hb := sbounds hpre
  have hAs := hpre.self.stack
  have hIs := hpre.iter.stack
  have hab := hpre.stack.above
  have hfit := hI.p.fits
  rw [hK] at hAs hIs hab
  intro hw
  rcases hx with h | h | h | h | h | h
  · addr_omega [h, hw, hAs, hb]
  · addr_omega [h, hw, hIs, hb]
  · rw [hK] at h; addr_omega [h, hw, hb]
  · addr_omega [h, hw, hb]
  · addr_omega [h.2, hw, hnx, hab, hb]
  · have := spare_heap hI h
    addr_omega [this.2, hw, hfit, hab, hb]

theorem Safe.next {s u t : MachineState} {a : Word} {n : Nat} (h : Safe s u a n)
    (hn : heapNext u ≤ heapNext t)
    (hsp : spareLen t (s.getReg .x10) = 0 ∨
      ((spareLo u (s.getReg .x10)).toNat ≤ (spareLo t (s.getReg .x10)).toNat ∧
        (spareLo t (s.getReg .x10)).toNat + spareLen t (s.getReg .x10) ≤
          (spareLo u (s.getReg .x10)).toNat + spareLen u (s.getReg .x10)) ∨
      (heapNext u ≤ (spareLo t (s.getReg .x10)).toNat ∧
        (spareLo t (s.getReg .x10)).toNat + spareLen t (s.getReg .x10) ≤ heapEnd)) :
    Safe s t a n := by
  refine h.mono hn ?_
  rcases h with h0 | ⟨-, -, -, -, hh, hs⟩
  · exact Or.inl h0
  · simp only [Apart] at hs ⊢
    omega

end Rv64Verifier.Proofs.Pcs.Extend
