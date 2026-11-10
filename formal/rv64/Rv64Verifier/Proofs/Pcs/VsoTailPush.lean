import Rv64Verifier.Proofs.Pcs.VsoTailCalls

/-!
# `verify_stacked_opening`'s level tail: the intro message pushed onto the pending claims

`0x8000b498` writes element `n` of the pending claims (`Vec` at `S - 616`, 80-byte elements, room
for one more): the intro message's `Vec` from `x21`/`x8`/`x19`, then the `Queries` weight (the
queries' capacity at `S - 1000`, their buffer at `S - 824`, their count in `x26`, `lam`'s powers'
`Vec` at `S - 488`, the message log at `S - 872`); the count becomes `n + 1`, the glue's scalar
at `S - 408` is set to one, and the glue starts (`0x8000b650`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem offset80 (x : Word) : x * 64 + x * 16 = BitVec.ofNat 64 (80 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    show (64 : Word).toNat = 64 from rfl, show (16 : Word).toNat = 16 from rfl]
  omega

/-- At `0x8000b650`, after the push from `p`. -/
structure Pushed (s p g : MachineState) : Prop where
  pc : g.pc = 0x8000b650
  sp : g.getReg .x2 = s.getReg .x2 - 1040
  regs : ∀ q ∈ [Reg.x8, .x9, .x19, .x20, .x21, .x23, .x24, .x27], g.getReg q = p.getReg q
  x18 : g.getReg .x18 = vecPtr p (s.getReg .x2 - 616)
  x22 : g.getReg .x22 = vecLen p (s.getReg .x2 - 616) + 1
  x25 : g.getReg .x25 = p.getMem (s.getReg .x2 - 792)
  x26 : g.getReg .x26 = p.getMem (s.getReg .x2 - 912)
  fr : DFrame p g fun a ↦ Within a (s.getReg .x2 - 600) 8 ∨ Within a (s.getReg .x2 - 408) 24 ∨
    Within a (vecPtr p (s.getReg .x2 - 616) +
      BitVec.ofNat 64 (80 * (vecLen p (s.getReg .x2 - 616)).toNat)) 80
  len : vecLen g (s.getReg .x2 - 616) = vecLen p (s.getReg .x2 - 616) + 1
  ptr : vecPtr g (s.getReg .x2 - 616) = vecPtr p (s.getReg .x2 - 616)
  cap : vecCap g (s.getReg .x2 - 616) = vecCap p (s.getReg .x2 - 616)
  one : eAt g (s.getReg .x2 - 408) = 1
  /-- The element's words. -/
  e0 : g.getMem (pAddr p s (vecLen p (s.getReg .x2 - 616)).toNat) = p.getReg .x21
  e8 : g.getMem (pAddr p s (vecLen p (s.getReg .x2 - 616)).toNat + 8) = p.getReg .x8
  e16 : g.getMem (pAddr p s (vecLen p (s.getReg .x2 - 616)).toNat + 16) = p.getReg .x19
  e24 : g.getMem (pAddr p s (vecLen p (s.getReg .x2 - 616)).toNat + 24) =
    p.getMem (s.getReg .x2 - 1000)
  e32 : g.getMem (pAddr p s (vecLen p (s.getReg .x2 - 616)).toNat + 32) =
    p.getMem (s.getReg .x2 - 824)
  e40 : g.getMem (pAddr p s (vecLen p (s.getReg .x2 - 616)).toNat + 40) = p.getReg .x26
  e48 : g.getMem (pAddr p s (vecLen p (s.getReg .x2 - 616)).toNat + 48) =
    p.getMem (s.getReg .x2 - 488)
  e56 : g.getMem (pAddr p s (vecLen p (s.getReg .x2 - 616)).toNat + 56) =
    p.getMem (s.getReg .x2 - 480)
  e64 : g.getMem (pAddr p s (vecLen p (s.getReg .x2 - 616)).toNat + 64) =
    p.getMem (s.getReg .x2 - 472)
  e72 : g.getMem (pAddr p s (vecLen p (s.getReg .x2 - 616)).toNat + 72) =
    p.getMem (s.getReg .x2 - 872)

/-- **The push at `0x8000b498`**, with room for one more element. -/
theorem push498 {s p : MachineState} (hpre : VsoPre s) (hpc : p.pc = 0x8000b498)
    (hsp : p.getReg .x2 = s.getReg .x2 - 1040) (hheap : HeapOk p)
    (hlt : (vecLen p (s.getReg .x2 - 616)).toNat < (vecCap p (s.getReg .x2 - 616)).toNat)
    (hbuf : HS s p (vecPtr p (s.getReg .x2 - 616)) ((vecCap p (s.getReg .x2 - 616)).toNat * 80))
    (hx22 : p.getReg .x22 = vecLen p (s.getReg .x2 - 616)) :
    ∃ g, Reaches Image.code p g ∧ Pushed s p g := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hhi := hheap.hi
  obtain ⟨P, hP⟩ : ∃ P, vecPtr p (s.getReg .x2 - 616) = P := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, vecLen p (s.getReg .x2 - 616) = n := ⟨_, rfl⟩
  rw [hP] at hbuf
  rw [hn] at hlt hx22
  obtain ⟨hP8, hPb⟩ := hbuf
  have hPb' : heapNext s ≤ P.toNat ∧ P.toNat + 80 * (n.toNat + 1) ≤ heapNext p := by
    rcases hPb with h0 | h0
    · omega
    · exact ⟨h0.1, by nlinarith [h0.2]⟩
  have hsl := hpre.heap.lo
  simp only [heapStart, heapEnd] at hsl hhi
  have hPP : p.getMem (s.getReg .x2 - 608) = P := by
    rw [← hP]; simp only [vecPtr]; rv_eval []
  have hE : P + BitVec.ofNat 64 (80 * n.toNat) = pAddr p s n.toNat := by
    simp only [pAddr, hP]
  have hRe : Region (P + BitVec.ofNat 64 (80 * n.toNat)) 80 :=
    heap_region (by addr_omega [hPb', hsl]) (by addr_omega [hPb', hhi]) (by addr_omega [hP8, hPb', hhi])
  have hReb := Region.bounds hRe
  have hoff := offset80 n
  obtain ⟨g, hr, h⟩ := Sym.BlockSpec.reaches b8000b498_spec hpc (by
    rv_eval [hsp, hPP, hx22, hoff]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hRe (by addr_omega [hReb]) (by addr_omega [hReb]) (by addr_omega [hReb])
      | addr_omega [hb, hReb, hPb', hhi])
  have k := b8000b498_keeps h
  have eA : p.getMem (p.getReg .x2 + 432) + (p.getReg .x22 * 64 + p.getReg .x22 * 16) =
      pAddr p s n.toNat := by
    rw [hx22, hoff, ← hE, hsp, show s.getReg .x2 - 1040 + 432 = s.getReg .x2 - 608 by rv_eval [],
      hPP]
  have X : DFrame p g fun a ↦ Within a (s.getReg .x2 - 600) 8 ∨
      Within a (s.getReg .x2 - 408) 24 ∨ Within a (P + BitVec.ofNat 64 (80 * n.toNat)) 80 :=
    (holds_dframe h).mono fun a ⟨k, hk, hw'⟩ ↦ by
      simp only [b8000b498, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> rv_eval [hsp, hPP, hx22, hoff] at hw' <;> first
        | exact Or.inl (by addr_omega [hw', hb])
        | exact Or.inr (Or.inl (by addr_omega [hw', hb]))
        | exact Or.inr (Or.inr (by addr_omega [hw', hReb]))
  have kp (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 600).toNat) : g.getMem y = p.getMem y :=
    X y fun i hi hw ↦ by
      rcases hw with hw | hw | hw
      · addr_omega [hw, hi, hy, hb]
      · addr_omega [hw, hi, hy, hb]
      · addr_omega [hw, hi, hy, hb, hReb, hhi, hPb']
  have hn1 : n + 1 ≠ 0 := by
    intro he
    have := congrArg BitVec.toNat he
    have hc := (vecCap p (s.getReg .x2 - 616)).isLt
    rw [BitVec.toNat_add] at this
    simp at this
    omega
  refine ⟨g, hr, {
    pc := b8000b498_pc_taken h (by rw [hx22]; exact hn1)
    sp := (k .x2 (by decide)).trans hsp
    regs := fun q hq ↦ k q ((by decide : ∀ q ∈ [Reg.x8, .x9, .x19, .x20, .x21, .x23, .x24, .x27],
      q ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x15, .x16, .x17, .x19, .x20, .x21, .x23,
        .x24, .x27, .x28, .x29, .x30, .x31] : List Reg)) q hq)
    x18 := by
      rw [b8000b498_x18 h, hsp, show s.getReg .x2 - 1040 + 432 = s.getReg .x2 - 608 by rv_eval [],
        hPP, hP]
    x22 := by rw [b8000b498_x22 h, hx22, hn]
    x25 := by rw [b8000b498_x25 h, hsp, show s.getReg .x2 - 1040 + 248 = s.getReg .x2 - 792 by rv_eval []]
    x26 := by rw [b8000b498_x26 h, hsp, show s.getReg .x2 - 1040 + 128 = s.getReg .x2 - 912 by rv_eval []]
    fr := by rw [hP, hn]; exact X
    len := by
      have := b8000b498_m_x2_440 h
      rw [hsp, show s.getReg .x2 - 1040 + 440 = s.getReg .x2 - 616 + 16 by rv_eval [], hx22] at this
      simp only [vecLen]; rw [this]; exact congrArg (· + 1) hn.symm
    ptr := by simp only [vecPtr]; exact kp _ (by addr_omega [hb])
    cap := by simp only [vecCap]; exact kp _ (by addr_omega [hb])
    one := by
      refine eAt_eq_of_limbs ?_
      rw [limbs_one]
      have m0 := b8000b498_m_x2_632 h
      have m1 := b8000b498_m_x2_640 h
      have m2 := b8000b498_m_x2_648 h
      rw [hsp, show s.getReg .x2 - 1040 + 632 = s.getReg .x2 - 408 by rv_eval []] at m0
      rw [hsp, show s.getReg .x2 - 1040 + 640 = s.getReg .x2 - 408 + 8 by rv_eval []] at m1
      rw [hsp, show s.getReg .x2 - 1040 + 648 = s.getReg .x2 - 408 + 16 by rv_eval []] at m2
      rw [m0, m1, m2]
    e0 := by rw [hn, ← eA]; exact b8000b498_m12 h
    e8 := by rw [hn, ← eA]; exact b8000b498_m11 h
    e16 := by rw [hn, ← eA]; exact b8000b498_m10 h
    e24 := by rw [hn, ← eA, b8000b498_m9 h, hsp, show s.getReg .x2 - 1040 + 40 = s.getReg .x2 - 1000 by rv_eval []]
    e32 := by rw [hn, ← eA, b8000b498_m8 h, hsp, show s.getReg .x2 - 1040 + 216 = s.getReg .x2 - 824 by rv_eval []]
    e40 := by rw [hn, ← eA]; exact b8000b498_m7 h
    e48 := by rw [hn, ← eA, b8000b498_m6 h, hsp, show s.getReg .x2 - 1040 + 552 = s.getReg .x2 - 488 by rv_eval []]
    e56 := by rw [hn, ← eA, b8000b498_m5 h, hsp, show s.getReg .x2 - 1040 + 560 = s.getReg .x2 - 480 by rv_eval []]
    e64 := by rw [hn, ← eA, b8000b498_m4 h, hsp, show s.getReg .x2 - 1040 + 568 = s.getReg .x2 - 472 by rv_eval []]
    e72 := by rw [hn, ← eA, b8000b498_m3 h, hsp, show s.getReg .x2 - 1040 + 168 = s.getReg .x2 - 872 by rv_eval []] }⟩

end Rv64Verifier.Proofs.Pcs.Vso
