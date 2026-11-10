import Rv64Verifier.Proofs.Pcs.VsoMerkleBlock

/-!
# `verify_stacked_opening`'s Merkle checks: the whole block

From the scans' end, `merkle_enter` checks the transcript is checked and goes to `0x8000b0dc` for an
empty phase or to the path loop (`LoopIn`); `merkle_loop` runs the path loop and reloads the paths;
`merkle` is the block from `0x8000aa14` to `0x8000b0dc` (`MerkleOut`), or an `Err` returned
(`FailR`), or a dead end.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The transcript's checked byte, kept by the function's invariant. -/
theorem checked_ext {s u : MachineState} {nx : Word} (hpre : VsoPre s) (hinv : InvR s u nx) :
    extractByte (u.getMem (s.getReg .x10 + 360)) 0 ≠ 0 := by
  have hS := Region.bounds hpre.self.ok.self
  have hst := hpre.self.stack
  rw [stackLo_vso, vso_stack] at hst
  have hf := hpre.self.free
  simp only [Outside] at hf
  have hrs := hpre.rootSelf
  have hfit := hinv.fits
  have e : u.getMem (s.getReg .x10 + 360) = s.getMem (s.getReg .x10 + 360) :=
    hinv.mem.word (fun x hx hW ↦ by
      rcases hW with (hW | hW) | hW | hW | ⟨hW1, hW2⟩
      · simp only [W] at hW; addr_omega [hx, hW, hS]
      · addr_omega [hx, hW, hrs, hS]
      · rw [stackLo_vso, vso_stack] at hW; addr_omega [hx, hW, hst, hS]
      · addr_omega [hx, hW, hf.2, hS]
      · rcases hf.1 with h1 | h1
        · addr_omega [hx, hW1, h1, hS]
        · addr_omega [hx, hW2, h1, hS, hfit]) (by addr_omega [hS])
  rw [e]
  have h : byteAt s (s.getReg .x10 + 360) ≠ 0 := by rw [hpre.checked]; decide
  rwa [← add_ofNat_zero (s.getReg .x10 + 360), byteAt_add (by addr_omega [hS]) (by decide)] at h

/-- The path loop keeps the function's frame below the leaf index's slot. -/
theorem PW.keepFrame {s u v : MachineState} {lo hi : ℕ} (hpre : VsoPre s)
    (hf : DFrame u v (PW s lo hi)) (hhi : hi ≤ heapEnd) {y : Word}
    (h1 : (s.getReg .x2 - 1040).toNat ≤ y.toNat) (h2 : y.toNat + 8 ≤ (s.getReg .x2 - 784).toNat) :
    v.getMem y = u.getMem y := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  exact hf y fun i hi hw ↦ by
    rcases hw with (hw | hw | hw | hw) | hw | hw | ⟨hw1, hw2⟩
    · addr_omega [hw, hi, h1, h2, hb]
    · addr_omega [hw, hi, h1, h2, hb]
    · addr_omega [hw, hi, h1, h2, hb]
    · addr_omega [hw, hi, h1, h2, hb]
    · addr_omega [hw, hi, h1, h2, hb]
    · addr_omega [hw, hi, h1, h2, hb, hnx]
    · addr_omega [hw2, hi, h1, h2, hb, hhi]

/-- The path loop keeps the opening offset. -/
theorem PW.keepTr {s u v : MachineState} {lo hi : ℕ} (hpre : VsoPre s)
    (hf : DFrame u v (PW s lo hi)) (hhi : hi ≤ heapEnd) (hlo : heapNext s ≤ lo) :
    v.getMem (s.getReg .x10 + 352) = u.getMem (s.getReg .x10 + 352) := by
  have hb := bounds hpre
  have hS := Region.bounds hpre.self.ok.self
  have hst := hpre.self.stack
  rw [stackLo_vso, vso_stack] at hst
  have hf' := hpre.self.free
  simp only [Outside] at hf'
  exact hf _ fun i hi hw ↦ by
    rcases hw with (hw | hw | hw | hw) | hw | hw | ⟨hw1, hw2⟩
    · addr_omega [hw, hi, hst, hS, hb]
    · addr_omega [hw, hi, hst, hS, hb]
    · addr_omega [hw, hi, hst, hS, hb]
    · addr_omega [hw, hi, hst, hS, hb]
    · addr_omega [hw, hi, hst, hS, hb]
    · addr_omega [hw, hi, hf'.2, hS]
    · rcases hf'.1 with h1 | h1
      · addr_omega [hw1, hi, h1, hS, hlo]
      · addr_omega [hw2, hi, h1, hS, hhi]

/-- At `0x8000ab38`, the path loop's start, after the writes `MY` from `u`. -/
structure LoopIn (s u w : MachineState) (ℓ : ℕ) : Prop where
  pc : w.pc = 0x8000ab38
  fr : DFrame u w (MY s)
  sp : w.getReg .x2 = s.getReg .x2 - 1040
  x22 : w.getReg .x22 = vecPtr u (phaseH s u)
  x5 : w.getReg .x5 = vecPtr u (phaseH s u) + BitVec.ofNat 64 (56 * (u.getReg .x26).toNat)
  regs : ∀ r ∈ [Reg.x9, .x26], w.getReg r = u.getReg r
  ne : u.getReg .x26 ≠ 0
  slot : w.getMem (s.getReg .x2 - 832) = phaseH s u
  off : w.getMem (s.getReg .x10 + 352) = u.getMem (s.getReg .x10 + 352) + 1
  s16 : w.getMem (s.getReg .x2 - 1008) = BitVec.ofNat 64 ℓ + 1
  s19 : w.getMem (s.getReg .x2 - 1000) = u.getReg .x19
  s18 : w.getMem (s.getReg .x2 - 992) = u.getReg .x18
  s25 : w.getMem (s.getReg .x2 - 984) = u.getReg .x25
  s24 : w.getMem (s.getReg .x2 - 976) = u.getReg .x24

/-- **From the scans' end**: an empty phase done, or the path loop's start. -/
theorem merkle_enter {s u t v : MachineState} {ℓ fc : ℕ} (hpre : VsoPre s) (hm : MerkleIn s u ℓ fc)
    (hs : Scans s u t v ℓ fc) :
    ∃ w, Reaches Image.code v w ∧ (MerkleOut s u w ℓ fc ∨ LoopIn s u w ℓ) := by
  have hF := hs.front
  have hb := bounds hpre
  have hT := Region.bounds hpre.self.ok.self
  have hIs := hpre.self.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hu := hm.inv.heap hpre.heap
  have kvu (r : Reg) (h1 : r ∈ KS2) (h2 : r ∈ FR) : v.getReg r = u.getReg r :=
    (hs.regs r h1).trans (hF.regs r h2)
  have frV : DFrame u v (MY s) :=
    (hF.fr.mono fun _ h ↦ Or.inl h).trans (DFrame.of_same hs.mem _) fun _ h ↦ h
  have hck : extractByte (v.getMem (s.getReg .x10 + 360)) 0 ≠ 0 := by
    rw [frV _ fun i hi hw ↦ by
      rcases hw with hw | hw | hw
      · addr_omega [hw, hi, hT]
      · addr_omega [hw, hi, hT, hIs, hb]
      · addr_omega [hw, hi, hT, hIs, hb]]
    exact checked_ext hpre hm.inv
  have sp : v.getReg .x2 = s.getReg .x2 - 1040 := by rw [hs.regs .x2 (by decide), hF.sp]
  obtain ⟨w, r, kw, fw, sl, hw⟩ := enterPaths hpre hs.pc sp
    (by rw [kvu .x20 (by decide) (by decide), hm.front.x20]) hck
  have frW : DFrame u w (MY s) := frV.trans fw fun _ h ↦ Or.inr h
  have hnW := MY.next hpre frW
  have spW : w.getReg .x2 = s.getReg .x2 - 1040 := by rw [kw .x2 (by decide), sp]
  have off : w.getMem (s.getReg .x10 + 352) = u.getMem (s.getReg .x10 + 352) + 1 := by
    rw [fw _ fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hT, hIs, hb], hs.mem,
      hF.off]
  have s16 : w.getMem (s.getReg .x2 - 1008) = BitVec.ofNat 64 ℓ + 1 := by
    rw [sl.x16, hs.regs .x16 (by decide), hF.x16]
  have regs : ∀ r ∈ [Reg.x9, .x26], w.getReg r = u.getReg r := fun r hr ↦ by
    rw [kw r (mem_of_mem hr _), kvu r (mem_of_mem hr _) (mem_of_mem hr _)]
  have x22 : w.getReg .x22 = vecPtr u (phaseH s u) := by
    rw [kw .x22 (by decide), hs.regs .x22 (by decide), hF.x22]; rfl
  rcases hw with ⟨pc, x20, h0⟩ | ⟨pc, hne, hH⟩
  · refine ⟨w, r, Or.inl {
      pc := pc
      sp := spW
      inv := MW.inv hpre hm.inv (MY.toMW frW _ _) ⟨hnW ▸ hu.lo, hnW ▸ hu.hi⟩ (le_of_eq hnW.symm)
        (by rw [spW, hm.front.sp])
      fr := MY.toMW frW _ _
      mono := le_of_eq hnW.symm
      regs := regs
      x20 := by rw [x20, hs.count, ← kvu .x26 (by decide) (by decide), h0]
      x22 := x22
      hdr := hF.hdr
      off := off
      s16 := s16
      s19 := by rw [sl.x19, kvu .x19 (by decide) (by decide)]
      s18 := by rw [sl.x18, kvu .x18 (by decide) (by decide)]
      s25 := by rw [sl.x25, kvu .x25 (by decide) (by decide)]
      s24 := by rw [sl.x24, kvu .x24 (by decide) (by decide)]
      count := hs.count
      scanned := hs.scanned
      roots := fun i hi ↦ by
        rw [← kvu .x26 (by decide) (by decide), h0] at hi
        exact absurd hi (Nat.not_lt_zero _) }⟩
  · refine ⟨w, r, Or.inr {
      pc := pc
      fr := frW
      sp := spW
      x22 := x22
      x5 := by
        rw [kw .x5 (by decide), hs.regs .x5 (by decide), hF.x5, ← hs.count]; rfl
      regs := regs
      ne := by rw [← kvu .x26 (by decide) (by decide)]; exact hne
      slot := by rw [hH, hs.regs .x17 (by decide), hF.x17]
      off := off
      s16 := s16
      s19 := by rw [sl.x19, kvu .x19 (by decide) (by decide)]
      s18 := by rw [sl.x18, kvu .x18 (by decide) (by decide)]
      s25 := by rw [sl.x25, kvu .x25 (by decide) (by decide)]
      s24 := by rw [sl.x24, kvu .x24 (by decide) (by decide)] }⟩

/-- A path's root, checked at the path loop's start, holds of `u`. -/
theorem roots_keep {s u w : MachineState} {p : Word} (hpre : VsoPre s) (hu : HeapOk u)
    (hf : DFrame u w (MY s)) (hh : Region p 56) (hc : Clear s (heapNext u) p 56)
    (hl : BufOk s u p 8) (hs : BufOk s u (p + 24) 32) (h : PathRoot w p (s.getReg .x11)) :
    PathRoot u p (s.getReg .x11) := by
  have hb := bounds hpre
  have hT := Region.bounds hpre.self.ok.self
  have hrs := hpre.rootSelf
  have hrst := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hP := Region.bounds hh
  have mis {a : Word} {n : ℕ} (c : Clear s (heapNext u) a n) : ∀ y, Within y a n → ¬ MY s y :=
    fun y hy hmy ↦ c.misses hpre hu.hi y hy (Or.inl hmy)
  refine pathRoot_keep h (openingAt_keep hf (by omega) (mis hc) ?_ ?_) (digest_keep hf
    (root_bound hpre) fun y hy hw ↦ by
      rcases hw with hw | hw | hw
      · addr_omega [hy, hw, hrs, hT]
      · addr_omega [hy, hw, hrst, hb]
      · addr_omega [hy, hw, hrst, hb])
  · rcases hl with h0 | ⟨hR, hC⟩
    · exact Or.inl h0
    · exact Or.inr ⟨by have := Region.bounds hR; omega, mis hC⟩
  · rcases hs with h0 | ⟨hR, hC⟩
    · exact Or.inl h0
    · exact Or.inr ⟨by have := Region.bounds hR; omega, mis hC⟩

end Rv64Verifier.Proofs.Pcs.Vso
