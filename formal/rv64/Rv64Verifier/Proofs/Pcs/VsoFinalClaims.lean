import Rv64Verifier.Proofs.Pcs.VsoFinalPoint
import Rv64Verifier.Proofs.Pcs.ExtendBase

/-!
# `verify_stacked_opening`: the claims, never written

The claims and their weights' buffers are read from the entry on and never written (`Ro`: a
region the entry reads, apart from the sponge and the root). Inside the function they stand for
the same claims (`claims_keep`), and each weight is read as at the entry (`weightSrc_keep`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol

/-- `n` bytes from `a` the entry reads, apart from the sponge and the root. -/
def Ro (s : MachineState) (a : Word) (n : ℕ) : Prop :=
  Src s vsoStack a n ∧ Apart a n (s.getReg .x10 + 8) 352 ∧ Apart a n (s.getReg .x11) 32

section
variable {s t : MachineState} {nx : Word}

/-- What the function writes misses them. -/
theorem Ro.misses {a : Word} {n : ℕ} (h : Ro s a n) (hinv : InvR s t nx) :
    ∀ y, Within y a n → ¬ Wr s vsoStack (WR s) nx y := by
  obtain ⟨hsrc, hsp, hrt⟩ := h
  have hfit := hinv.fits
  have hst := hsrc.stack
  have hfr := hsrc.free
  simp only [Outside] at hfr
  intro y hy hW
  rcases hW with (hW | hW) | hW | hW | ⟨hW1, hW2⟩
  · simp only [W] at hW; addr_omega [hy, hW, hsp]
  · addr_omega [hy, hW, hrt]
  · addr_omega [hy, hW, hst]
  · addr_omega [hy, hW, hfr.2]
  · rcases hfr.1 with h1 | h1
    · addr_omega [hy, hW1, h1]
    · simp only [heapEnd] at hfit h1; addr_omega [hy, hW2, h1, hfit]

theorem Ro.eList {a : Word} {m : ℕ} (h : Ro s a (24 * m)) (hinv : InvR s t nx) :
    eListAt t a m = eListAt s a m :=
  DFrame.eList hinv.mem (h.misses hinv) (by
    rcases h.1.bound with h0 | h0
    · left; omega
    · right; omega)

theorem Ro.word {a y : Word} {n : ℕ} (h : Ro s a n) (hinv : InvR s t nx)
    (h1 : a.toNat ≤ y.toNat) (h2 : y.toNat + 8 ≤ a.toNat + n) : t.getMem y = s.getMem y := by
  have hb := h.1.bound
  exact hinv.mem.word (fun z hz ↦ h.misses hinv z (by
    rcases hb with h0 | h0
    · omega
    · addr_omega [hz, h1, h2, h0])) (by rcases hb with h0 | h0 <;> omega)

theorem Ro.sub {a b : Word} {n m : ℕ} (h : Ro s a n) (h1 : a.toNat ≤ b.toNat)
    (h2 : b.toNat + m ≤ a.toNat + n) (h3 : b.toNat % 8 = 0) : Ro s b m :=
  ⟨h.1.sub h1 h2 h3, by have := h.2.1; addr_omega [this, h1, h2],
    by have := h.2.2; addr_omega [this, h1, h2]⟩

end

/-- The claim at `e` reads regions `Ro`. -/
theorem claimRegions_ro {s : MachineState} (hpre : VsoPre s) {i : ℕ}
    (hi : i < (s.getReg .x15).toNat) :
    Extend.ClaimRegions (Ro s) s (s.getReg .x14 + BitVec.ofNat 64 (88 * i)) := by
  have hc := hpre.claims
  have hcs := hpre.claimsSponge
  have hrc := hpre.rootClaims
  have hcb := hc.bound
  have hw := hpre.weights i hi
  have hws := hpre.weightsSponge i hi
  have hwr := hpre.rootWeights i hi
  set e := s.getReg .x14 + BitVec.ofNat 64 (88 * i) with he
  have he8 : e.toNat % 8 = 0 := by
    rcases hc.region with h0 | h0
    · omega
    · have := Region.bounds h0; rw [he]; addr_omega [this, hi]
  refine ⟨⟨hc.sub (by rw [he]; addr_omega [hcb, hi]) (by rw [he]; addr_omega [hcb, hi]) he8,
    by rw [he]; addr_omega [hcs, hcb, hi], by rw [he]; addr_omega [hrc, hcb, hi]⟩, ?_⟩
  simp only [WeightSrc] at hw
  simp only [WeightApart] at hws hwr
  by_cases h1 : s.getMem e = eqTag
  · simp only [h1, ↓reduceIte] at hw hws hwr ⊢
    exact ⟨hw.2, hws, by simp only [Apart] at hwr ⊢; omega⟩
  · by_cases h2 : s.getMem e = ringTag
    · simp only [h2, ↓reduceIte] at hw hws hwr ⊢
      have r := hw.2
      simp only [RingApart] at hws hwr
      have e32 : e + 8 + 24 = e + 32 := Extend.add_lit _ _ _ _ rfl
      rw [e32] at hws hwr
      have rc := r.coeffs
      rw [e32] at rc
      exact ⟨⟨r.point, hws.1, hwr.1⟩, ⟨rc, hws.2, hwr.2⟩⟩
    · simp only [h1, h2, ↓reduceIte] at hw hws hwr ⊢
      have r := hw.2
      simp only [RingApart] at hws hwr
      exact ⟨⟨r.point, hws.1, hwr.1⟩, ⟨r.coeffs, hws.2, hwr.2⟩⟩

/-- Inside the function the claims are the entry's. -/
theorem claim_keep {s t : MachineState} {nx : Word} (hpre : VsoPre s) (hinv : InvR s t nx)
    {i : ℕ} (hi : i < (s.getReg .x15).toNat) :
    stackClaimAt t (s.getReg .x14 + BitVec.ofNat 64 (88 * i)) =
      stackClaimAt s (s.getReg .x14 + BitVec.ofNat 64 (88 * i)) ∧
    Extend.ClaimRegions (Ro s) t (s.getReg .x14 + BitVec.ofNat 64 (88 * i)) := by
  have hcr := claimRegions_ro hpre hi
  have h88 := hcr.1
  have hb := h88.1.bound
  exact Extend.claim_move (fun k hk ↦ h88.word hinv (by
      rcases hb with h0 | h0
      · omega
      · addr_omega [hk, h0]) (by
      rcases hb with h0 | h0
      · omega
      · addr_omega [hk, h0])) hcr (fun a m h ↦ h.eList hinv) (fun _ _ h ↦ h) h88

theorem claims_keep {s t : MachineState} {nx : Word} (hpre : VsoPre s) (hinv : InvR s t nx) :
    claimsAt t (s.getReg .x14) (s.getReg .x15).toNat =
      claimsAt s (s.getReg .x14) (s.getReg .x15).toNat :=
  Extend.claimsAt_congr fun _ hi ↦ (claim_keep hpre hinv hi).1

end Rv64Verifier.Proofs.Pcs.Vso
