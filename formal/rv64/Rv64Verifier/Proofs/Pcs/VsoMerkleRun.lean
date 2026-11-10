import Rv64Verifier.Proofs.Pcs.VsoMerkleLoop

/-!
# `verify_stacked_opening`'s Merkle checks, `0x8000aa14` to `0x8000b0dc`

`merkle_loop` runs the path loop from `LoopIn` and reloads the paths; `merkle` is the whole block.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- **The path loop**, from its start to `0x8000b0dc`. -/
theorem merkle_loop (hT : TryAllocZeroedSpec) (hRF : ReserveFastSpec 0x8000c898)
    (hM : Runtime.MemcpySpec 0x800126e4) (hK : KeccakHashSpec) (hC : MemcmpSpec)
    {s u t v w : MachineState} {ℓ fc : ℕ} (hpre : VsoPre s) (hm : MerkleIn s u ℓ fc)
    (hs : Scans s u t v ℓ fc) (hl : LoopIn s u w ℓ) :
    ∃ w', Reaches Image.code w w' ∧ (FailR s w' ∨ MerkleOut s u w' ℓ fc) := by
  have hb := bounds hpre
  have hu := hm.inv.heap hpre.heap
  have hP := hm.phase hs.front.hdr
  have hcnt : (vecLen u (phaseH s u)).toNat = (u.getReg .x26).toNat := by rw [hs.count]
  have hn0 : 0 < (u.getReg .x26).toNat := by
    rcases Nat.eq_zero_or_pos (u.getReg .x26).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq h) hl.ne
    · exact h
  obtain ⟨hR, hCl⟩ : Region (vecPtr u (phaseH s u)) (56 * (u.getReg .x26).toNat) ∧
      Clear s (heapNext u) (vecPtr u (phaseH s u)) (56 * (u.getReg .x26).toNat) := by
    rcases hP.paths with h0 | h
    · omega
    · rw [← hcnt]; exact h
  have hRb := Region.bounds hR
  have hnW := MY.next hpre hl.fr
  have hPn : (vecPtr u (phaseH s u)).toNat + 56 * (u.getReg .x26).toNat < 2 ^ 64 := by omega
  have hsub (j : ℕ) (hj : j < (u.getReg .x26).toNat) :
      Region (vecPtr u (phaseH s u) + BitVec.ofNat 64 (56 * j)) 56 ∧
        Clear s (heapNext u) (vecPtr u (phaseH s u) + BitVec.ofNat 64 (56 * j)) 56 :=
    ⟨region_sub hR (56 * j) 56 (by omega) (by omega),
      hCl.sub (by addr_omega [hRb, hj]) (by addr_omega [hRb, hj])⟩
  have hps (j : ℕ) (hj : j < (u.getReg .x26).toNat) :
      PathOk s w (vecPtr u (phaseH s u) + BitVec.ofNat 64 (56 * j)) :=
    pathOk_of hpre hu hl.fr (hsub j hj).1 (hsub j hj).2
      (fun h ↦ width_ne_zero ℓ fc ((hs.scanned j hj).1.symm.trans (BitVec.eq_of_toNat_eq h)))
      (hP.leaves j (by omega)) (hP.sibs j (by omega))
  have hroot : RootOk s w (s.getReg .x11) := by
    have hT := Region.bounds hpre.self.ok.self
    have hIs := hpre.self.stack
    rw [stackLo_vso, vso_stack] at hIs
    have hrst := hpre.root.stack
    rw [stackLo_vso, vso_stack] at hrst
    have hrf := hpre.root.free
    simp only [Outside] at hrf
    have hmono : heapNext s ≤ heapNext u := hm.inv.mono
    refine ⟨?_, ?_, ⟨?_, hrst, hrf.2⟩⟩
    · rw [hl.fr _ fun i hi hw ↦ by
        rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hT, hIs, hb]]
      exact hm.root
    · rcases hpre.root.region with h | h
      · cases h
      · exact h
    · rw [hnW]
      rcases hrf.1 with h | h
      · exact Or.inl (by omega)
      · exact Or.inr h
  have hin : PathIn s w (vecPtr u (phaseH s u) + BitVec.ofNat 64 (56 * 0))
      (vecPtr u (phaseH s u) + BitVec.ofNat 64 (56 * (u.getReg .x26).toNat)) w :=
    { pc := hl.pc
      sp := hl.sp
      x22 := by rw [hl.x22, Nat.mul_zero, add_ofNat_zero]
      x5 := hl.x5
      fr := DFrame.refl _ _
      heap := ⟨hnW ▸ hu.lo, hnW ▸ hu.hi⟩
      mono := le_refl _
      rodata := MY.rodata hpre (hm.inv.rodata' hpre) hl.fr }
  obtain ⟨w3, r3, hd | ⟨PF, hw3⟩⟩ := paths_loop hT hRF hM hK hC hpre hPn hps hroot _ 0 w
    (Nat.sub_zero _) hn0 hin fun _ _ ↦ rfl
  · exact ⟨w3, r3, Or.inl (Or.inl hd)⟩
  have pf : DFrame w w3 (PW s (heapNext u) (heapNext w3)) := hnW ▸ PF.fr
  have fr3 : DFrame u w3 (MW s (heapNext u) (heapNext w3)) :=
    (MY.toMW hl.fr _ _).trans pf fun _ h ↦ Or.inr h
  have mono3 : heapNext u ≤ heapNext w3 := hnW ▸ PF.mono
  rcases hw3 with hpc | ⟨hpc, rg3, roots⟩
  · obtain ⟨w4, r4, h4⟩ := merkle_err hpre hm.inv hm.front.sp PF.sp (Or.inr (Or.inr (Or.inr hpc)))
      fr3 PF.heap mono3
    exact ⟨w4, r3.trans r4, Or.inl h4⟩
  have hhi := PF.heap.hi
  have kf {y : Word} (h1 : (s.getReg .x2 - 1040).toNat ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2 - 784).toNat) : w3.getMem y = w.getMem y :=
    PW.keepFrame hpre PF.fr hhi h1 h2
  have hHr : Region (phaseH s u) 24 := (hm.front.hdr hs.front.hdr).1
  have hHb := Region.bounds hHr
  obtain ⟨w4, r4, pc4, x20₄, x22₄, m4, k4⟩ := reload hpre hpc PF.sp
    (by rw [kf (by addr_omega [hb]) (by addr_omega [hb])]; exact hl.slot) hHr
  have hn4 : heapNext w4 = heapNext w3 := by simp only [heapNext, m4]
  have fr4 : DFrame u w4 (MW s (heapNext u) (heapNext w4)) := by
    rw [hn4]; exact fr3.trans (DFrame.of_same m4 _) fun _ h ↦ h
  have kH {o : ℕ} (ho : o + 8 ≤ 24) :
      w3.getMem (phaseH s u + BitVec.ofNat 64 o) = u.getMem (phaseH s u + BitVec.ofNat 64 o) :=
    hP.hdr.keep hpre fr3 hhi (by omega) (by addr_omega [hHb, ho]) (by addr_omega [hHb, ho])
  have sp4 : w4.getReg .x2 = s.getReg .x2 - 1040 := by rw [k4 .x2 (by decide), PF.sp]
  refine ⟨w4, r3.trans r4, Or.inr {
    pc := pc4
    sp := sp4
    inv := MW.inv hpre hm.inv fr4 ⟨by rw [hn4]; exact PF.heap.lo, by rw [hn4]; exact hhi⟩
      (by rw [hn4]; exact mono3) (by rw [sp4, hm.front.sp])
    fr := fr4
    mono := by rw [hn4]; exact mono3
    regs := fun r hr ↦ by
      rw [k4 r (mem_of_mem hr _), rg3 r hr, hl.regs r hr]
    x20 := by rw [x20₄]; exact kH (o := 16) (by decide)
    x22 := by rw [x22₄]; exact kH (o := 8) (by decide)
    hdr := hs.front.hdr
    off := by
      rw [m4, PW.keepTr hpre PF.fr hhi (by rw [hnW]; exact hm.inv.mono), hl.off]
    s16 := by rw [m4, kf (by addr_omega [hb]) (by addr_omega [hb])]; exact hl.s16
    s19 := by rw [m4, kf (by addr_omega [hb]) (by addr_omega [hb])]; exact hl.s19
    s18 := by rw [m4, kf (by addr_omega [hb]) (by addr_omega [hb])]; exact hl.s18
    s25 := by rw [m4, kf (by addr_omega [hb]) (by addr_omega [hb])]; exact hl.s25
    s24 := by rw [m4, kf (by addr_omega [hb]) (by addr_omega [hb])]; exact hl.s24
    count := hs.count
    scanned := hs.scanned
    roots := fun i hi ↦ roots_keep hpre hu hl.fr (hsub i hi).1 (hsub i hi).2
      (hP.leaves i (by omega)) (hP.sibs i (by omega)) (roots i (Nat.zero_le _) hi) }⟩

/-- **The Merkle checks**, from `0x8000aa14`: their end at `0x8000b0dc`, an `Err` returned, or a
dead end. -/
theorem merkle (hT : TryAllocZeroedSpec) (hRF : ReserveFastSpec 0x8000c898)
    (hM : Runtime.MemcpySpec 0x800126e4) (hK : KeccakHashSpec) (hC : MemcmpSpec)
    {s u : MachineState} {ℓ fc : ℕ} (hpre : VsoPre s) (hm : MerkleIn s u ℓ fc) :
    ∃ w, Reaches Image.code u w ∧ (FailR s w ∨ MerkleOut s u w ℓ fc) := by
  obtain ⟨v, r1, hf | ⟨t, hs⟩⟩ := merkle_scans hpre hm
  · exact ⟨v, r1, Or.inl hf⟩
  obtain ⟨w, r2, ho | hl⟩ := merkle_enter hpre hm hs
  · exact ⟨w, r1.trans r2, Or.inr ho⟩
  obtain ⟨w', r3, h⟩ := merkle_loop hT hRF hM hK hC hpre hm hs hl
  exact ⟨w', r1.trans (r2.trans r3), h⟩

end Rv64Verifier.Proofs.Pcs.Vso
