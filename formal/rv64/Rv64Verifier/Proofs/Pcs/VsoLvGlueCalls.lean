import Rv64Verifier.Proofs.Pcs.VsoLvGlueBase
import Rv64Verifier.Proofs.Pcs.VsoFinalEnd

/-!
# `verify_stacked_opening`'s glue: its calls

`E::mul` with its right operand in the heap (`callMulH`), `memcpy` of a claim from `S - 384`
into the glued claims' buffer (`callMemcpy80`), `grow_one` of the glued claims (`callGrow88`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol

theorem glue_range {a : Word} {n : Nat} (h : Region a (8 * n)) : ValidMemRange a n :=
  fun i hi ↦ Region.valid h (by addr_omega [h, hi]) (by addr_omega [h, hi]) (by addr_omega [h, hi])

/-- `E::mul(o, a, b)`, `o` and `a` in the frame, `b` in the heap. -/
theorem callMulH (hM : MulSpec) {s t : MachineState} {nx o a b : Word} (hpre : VsoPre s)
    (hinv : InvR s t nx) (hpc : t.pc = 0x80008c48) (hx10 : t.getReg .x10 = o)
    (hx11 : t.getReg .x11 = a) (hx12 : t.getReg .x12 = b)
    (ho : (s.getReg .x2 - 1040).toNat ≤ o.toNat ∧ o.toNat + 24 ≤ (s.getReg .x2 - 104).toNat ∧
      o.toNat % 8 = 0)
    (ha : (s.getReg .x2 - 1040).toNat ≤ a.toNat ∧ a.toNat + 24 ≤ (s.getReg .x2 - 104).toNat ∧
      a.toNat % 8 = 0)
    (hb' : 0x20 ≤ b.toNat ∧ b.toNat + 24 ≤ heapEnd ∧ b.toNat % 8 = 0)
    (hoa : Apart o 24 a 24) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      DFrame t v (fun y ↦ Within y o 24 ∨ Within y (s.getReg .x2 - 2064) 1024) ∧
      eAt v o = eAt t a * eAt t b)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := hinv.sp
  have hro := hst.rodata
  rw [stackLo_vso] at hro
  have hsl : stackLo t mulStack = s.getReg .x2 - 2064 := by
    simp only [stackLo, hsp, mulStack]; rv_eval []
  have hR : Region b (8 * 3) := heap_region hb'.1 hb'.2.1 hb'.2.2
  simp only [heapEnd] at hb'
  have hpreM : MulPre t := {
    out := by rw [hx10]; valid_sub hst.valid [hb, ho]
    lhs := by rw [hx11]; valid_sub hst.valid [hb, ha]
    rhs := by rw [hx12]; exact glue_range hR
    stack := ⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp]; addr_omega [hb]⟩
    outLhs := by rw [hx10, hx11]; exact hoa
    outRhs := by rw [hx10, hx12]; addr_omega [hb, ho, hb']
    outStack := by rw [hx10, hsl]; addr_omega [hb, ho]
    lhsStack := by rw [hx11, hsl]; addr_omega [hb, ha]
    rhsStack := by rw [hx12, hsl]; addr_omega [hb, hb']
    rodata := hinv.rodata' hpre
    stackRodata := by rw [hsl]; addr_omega [hro, hb] }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost⟩ | hdead⟩ := hM.call (Reaches.refl t) hpc hpreM
  · have hfr := hpost.frame
    have hval := hpost.value
    rw [hx10, hsl] at hfr
    rw [hx10, hx11, hx12] at hval
    exact ⟨v, hr, Or.inr ⟨hpc', hpres, DFrame.of_two hfr, hval⟩⟩
  · exact ⟨v, hr, Or.inl hdead⟩

/-- `memcpy` of the 80 bytes at `S - 384` to `d` in the heap. -/
theorem callMemcpy80 (hM : Runtime.MemcpySpec 0x800126e4) {s t : MachineState} {d : Word}
    (hpre : VsoPre s) (hpc : t.pc = 0x800126e4) (hsp : t.getReg .x2 = s.getReg .x2 - 1040)
    (hx10 : t.getReg .x10 = d) (hx11 : t.getReg .x11 = s.getReg .x2 - 384)
    (hx12 : t.getReg .x12 = 80) (hd : 0x20 ≤ d.toNat ∧ d.toNat + 80 ≤ heapEnd) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      Contracts.bytesAt v d 80 = Contracts.bytesAt t (s.getReg .x2 - 384) 80 ∧
      DFrame t v fun a ↦ Within a d 80 ∨ Within a (s.getReg .x2 - 1056) 16)) := by
  have hm := stack_mapped hpre
  have hsl : stackLo t memcpyStack = s.getReg .x2 - 1056 := by
    simp only [stackLo, memcpyStack, hsp]; rv_eval []
  have h80 : (t.getReg .x12).toNat = 80 := by rw [hx12]; rfl
  simp only [heapEnd] at hd
  have hpreM : Runtime.MemcpyPre t := {
    dst := by rw [hx10, h80]; simp only [Mapped]; omega
    src := by rw [hx11, h80]; addr_omega [hm]
    apart := by rw [hx10, hx11, h80]; addr_omega [hm, hd]
    stack := (hpre.stack.sub 1040 hsp (by decide) (by decide) (by decide) (by decide)
      (by decide)).toStackOk
    dstStack := by rw [hx10, h80, hsl]; addr_omega [hm, hd]
    srcStack := by rw [hx11, h80, hsl]; addr_omega [hm] }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost⟩ | hdead⟩ := hM.call (Reaches.refl t) hpc hpreM
  · have hb := hpost.bytes
    have hf := DFrame.of_byteFrame hpost.frame
    rw [hx10, hx11, h80, bytesAt_rt, bytesAt_rt] at hb
    rw [hx10, h80, hsl] at hf
    exact ⟨v, hr, Or.inr ⟨hpc', hpres, hb, hf⟩⟩
  · exact ⟨v, hr, Or.inl hdead⟩

/-- `grow_one` of the glued claims (`Vec<GluedClaim>`, 88-byte elements) at `A`. -/
theorem callGrow88 (hG : GrowOneFreshSpec 0x8000db78 88 8) {s t : MachineState} {nx A : Word}
    (hpre : VsoPre s) (hinv : InvR s t nx) (hheap : HeapOk t) (hpc : t.pc = 0x8000db78)
    (hx10 : t.getReg .x10 = A)
    (hA : (s.getReg .x2 - 1040).toNat ≤ A.toNat ∧ A.toNat + 24 ≤ (s.getReg .x2 - 104).toNat ∧
      A.toNat % 8 = 0)
    (hv : VecOk t A 88 8) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      HeapOk v ∧ heapNext t ≤ heapNext v ∧
      DFrame t v (fun a ↦ Within a A 16 ∨ Within a (s.getReg .x2 - 1200) 160 ∨
        Within a nextAddr 8 ∨ Fresh t v a) ∧
      vecLen v A = vecLen t A ∧ (vecCap t A).toNat + 1 ≤ (vecCap v A).toNat ∧
      RawVecOk v A 88 8 ∧ NewBuf t v (vecPtr v A) ((vecCap v A).toNat * 88) 8 ∧
      Contracts.bytesAt v (vecPtr v A) ((vecCap t A).toNat * 88) =
        Contracts.bytesAt t (vecPtr t A) ((vecCap t A).toNat * 88))) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsp := hinv.sp
  have hsl : stackLo t growOneStack = s.getReg .x2 - 1200 := by
    simp only [stackLo, growOneStack, hsp]; rv_eval []
  have hpreG : GrowOnePre 88 8 t := {
    heap := hheap
    self := by rw [hx10]; valid_sub hst.valid [hb, hA]
    raw := by rw [hx10]; exact hv.raw
    stack := hst.sub 1040 hsp (by decide) (by decide) (by decide) (by decide) (by decide)
    selfFree := by
      rw [hx10]; exact stack_outside hpre (by addr_omega [hA, hb]) (by addr_omega [hA, hb])
    selfStack := by rw [hx10, hsl]; addr_omega [hA, hb] }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost, hnew⟩ | hdead⟩ := hG.call (Reaches.refl t) hpc hpreG
  swap
  · exact ⟨v, hr, Or.inl hdead⟩
  have hfr := DFrame.of_byteFrame hpost.frame
  rw [hx10, hsl] at hfr
  rw [hx10] at hnew
  have hcap := hpost.cap
  have hraw' := hpost.raw
  have hbytes := hpost.bytes
  rw [hx10] at hcap hraw' hbytes
  rw [bytesAt_rt, bytesAt_rt] at hbytes
  have hhv := hpost.heap.hi
  have e2 : vecLen v A = vecLen t A := hfr _ fun i hi hx ↦ by
    rcases hx with hx | hx | hx | hx
    · addr_omega [hx, hi, hA]
    · addr_omega [hx, hi, hA, hb]
    · addr_omega [hx, hi, hA, hb, hnx]
    · simp only [Fresh] at hx; addr_omega [hx.2, hi, hA, hb, hhv]
  exact ⟨v, hr, Or.inr ⟨hpc', hpres, hpost.heap, hpost.mono, hfr, e2, hcap, hraw', hnew, hbytes⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
