import Rv64Verifier.Proofs.Pcs.VsoGlueSpec

/-!
# `verify_stacked_opening`'s level tail: `dot` on two heap slices

At `0x8000b42c` the rows' values and `lam`'s powers, both in the heap, go to `dot`, its result at
`S - 512` (`callDotV`). `HS` is a heap slice allocated since the entry, or empty.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol

/-- `n` bytes from `p`, aligned, allocated between the entry and `t`, or none. -/
@[rv_addr] def HS (s t : MachineState) (p : Word) (n : ℕ) : Prop :=
  p.toNat % 8 = 0 ∧ (n = 0 ∨ heapNext s ≤ p.toNat ∧ p.toNat + n ≤ heapNext t)

theorem heapVmr {a : Word} {n : ℕ} (h1 : heapStart ≤ a.toNat) (h2 : a.toNat + 8 * n ≤ heapEnd)
    (h3 : a.toNat % 8 = 0) : ValidMemRange a n := fun i hi ↦ by
  simp only [heapStart, heapEnd] at h1 h2
  have e : (a + BitVec.ofNat 64 (8 * i)).toNat = a.toNat + 8 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  exact (Sym.validAccess_eight _).mpr ⟨Or.inl ⟨by omega, by omega⟩, by omega⟩

theorem HS.vmr {s t : MachineState} {p : Word} {n : ℕ} (hs : HeapOk s) (ht : HeapOk t)
    (h : HS s t p (24 * n)) : ValidMemRange p (3 * n) := by
  rcases h.2 with h0 | h0
  · intro i hi; omega
  · have := hs.lo; have := ht.hi
    exact heapVmr (by omega) (by omega) h.1

/-- A heap slice misses the frame and `NEXT`. -/
theorem HS.apart {s t : MachineState} {p : Word} {n : ℕ} (hpre : VsoPre s) (ht : HeapOk t)
    (h : HS s t p n) {a : Word} {m : ℕ}
    (ha : (s.getReg .x2 - 2464).toNat ≤ a.toNat ∧ a.toNat + m ≤ (s.getReg .x2).toNat) :
    Apart p n a m := by
  have hb := bounds hpre
  have hhi := ht.hi
  simp only [heapEnd] at hhi
  rcases h.2 with h0 | h0
  · exact Or.inl h0
  · addr_omega [hb, ha, h0, hhi]

/-- **`dot(S - 512, a1/a2, a3/a4)`** of two heap slices. -/
theorem callDotV (hDt : MultilinearContracts.DotSpec) {s t : MachineState} {nx : Word}
    (hpre : VsoPre s) (hinv : InvR s t nx) (hheap : HeapOk t) (hpc : t.pc = 0x80007f3c)
    (hx10 : t.getReg .x10 = s.getReg .x2 - 512)
    (hl : HS s t (t.getReg .x11) (24 * (t.getReg .x12).toNat))
    (hr : HS s t (t.getReg .x13) (24 * (t.getReg .x14).toNat)) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      DFrame t v (fun a ↦ Within a (s.getReg .x2 - 512) 24 ∨ Within a (s.getReg .x2 - 2160) 1120) ∧
      t.getReg .x12 = t.getReg .x14 ∧
      eAt v (s.getReg .x2 - 512) = Model.dotRust (eListAt t (t.getReg .x11) (t.getReg .x12).toNat)
        (eListAt t (t.getReg .x13) (t.getReg .x12).toNat))) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := hinv.sp
  have hro := hst.rodata
  rw [stackLo_vso] at hro
  have hs0 := hpre.heap
  have hsl : stackLo t MultilinearContracts.dotStack = s.getReg .x2 - 2160 := by
    simp only [stackLo, MultilinearContracts.dotStack, mulStack, hsp, Nat.reduceAdd]; rv_eval []
  have hpreD : MultilinearContracts.DotPre t := {
    ret := by rw [hx10]; valid_sub hst.valid [hb]
    left := hl.vmr hs0 hheap
    right := hr.vmr hs0 hheap
    stack := ⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp]; addr_omega [hb]⟩
    retLeft := by
      rw [hx10]
      have := hl.apart hpre hheap (a := s.getReg .x2 - 512) (m := 24) (by addr_omega [hb])
      simp only [Apart] at this ⊢; omega
    retRight := by
      rw [hx10]
      have := hr.apart hpre hheap (a := s.getReg .x2 - 512) (m := 24) (by addr_omega [hb])
      simp only [Apart] at this ⊢; omega
    retStack := by rw [hx10, hsl]; addr_omega [hb]
    leftStack := by rw [hsl]; exact hl.apart hpre hheap (by addr_omega [hb])
    rightStack := by rw [hsl]; exact hr.apart hpre hheap (by addr_omega [hb])
    rodata := hinv.rodata' hpre
    retRodata := by rw [hx10]; addr_omega [hro, hb]
    stackRodata := by rw [hsl]; addr_omega [hro, hb] }
  obtain ⟨v, hrv, ⟨hpc', hpres, hpost⟩ | hdead⟩ := hDt.call (Reaches.refl t) hpc hpreD
  · have hfr := hpost.frame
    have hval := hpost.value
    rw [hx10, hsl] at hfr
    rw [hx10] at hval
    exact ⟨v, hrv, Or.inr ⟨hpc', hpres, DFrame.of_two hfr, hpost.len, hval⟩⟩
  · exact ⟨v, hrv, Or.inl hdead⟩

end Rv64Verifier.Proofs.Pcs.Vso
