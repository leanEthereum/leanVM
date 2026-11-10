import Rv64Verifier.Proofs.Pcs.ExtendStep

/-!
# `Vec<StackClaim>::extend_desugared`: the store

`0x80009bf8` writes the 88-byte `StackClaim` at the `Vec`'s end (`eNew`) and its length.
-/

namespace Rv64Verifier.Proofs.Pcs.Extend
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Transcript Rv64Verifier.Pcs
  Rv64Verifier.PcsContracts Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F37 LeanVM.Parameters
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The new claim's address. -/
@[rv_addr] def eNew (s u w : MachineState) : Word :=
  vecPtr w (s.getReg .x10) + BitVec.ofNat 64 (88 * (vecLen u (s.getReg .x10)).toNat)

theorem mul88 (x : Word) : x * 88 = BitVec.ofNat 64 (88 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  have h : (88 : Word).toNat = 88 := rfl
  rw [h, Nat.mul_comm]

/-- The `Vec`'s buffer at `w` lies in the heap allocated since the entry. -/
theorem vbuf {s u w : MachineState} {k : Nat} (hp : Push s u k) (hr : Room s u w k) :
    heapNext s ≤ (vecPtr w (s.getReg .x10)).toNat ∧
      (vecPtr w (s.getReg .x10)).toNat + (vecCap w (s.getReg .x10)).toNat * 88 ≤ heapNext w ∧
      (vecPtr w (s.getReg .x10)).toNat % 8 = 0 := by
  have hI := hp.inv
  have hu' : heapNext s ≤ heapNext u := hI.p.mono
  have hm := hr.mono
  have hroom := hr.room
  rcases hr.moved with ⟨hP, hC⟩ | ⟨hn, -⟩
  · rw [hP, hC]
    rw [hC] at hroom
    rcases hI.buf with he | hn
    · rw [he] at hroom; omega
    · simp only [NewBuf] at hn; omega
  · simp only [NewBuf] at hn; omega

/-- After the store. -/
structure Stored (s u w t : MachineState) (k : Nat) : Prop where
  fr : DFrame w t fun x ↦ Within x (s.getReg .x10 + 16) 8 ∨ Within x (eNew s u w) 88
  len : vecLen t (s.getReg .x10) = vecLen u (s.getReg .x10) + 1
  tag : t.getMem (eNew s u w) = eqTag
  p8 : t.getMem (eNew s u w + 8) = w.getMem (s.getReg .x2 - 184)
  p16 : t.getMem (eNew s u w + 16) = w.getMem (s.getReg .x2 - 184 + 8)
  p24 : t.getMem (eNew s u w + 24) = w.getMem (s.getReg .x2 - 184 + 16)
  v64 : t.getMem (eNew s u w + 64) = w.getMem (s.getReg .x2 - 208)
  v72 : t.getMem (eNew s u w + 72) = w.getMem (s.getReg .x2 - 208 + 8)
  v80 : t.getMem (eNew s u w + 80) = w.getMem (s.getReg .x2 - 208 + 16)
  keep : ∀ r ∈ [Reg.x2, .x8, .x9, .x19, .x20, .x21, .x22, .x23, .x24, .x25], t.getReg r = w.getReg r
  pc : (k + 1 = itCount s ∧ t.pc = 0x80009d7c) ∨ (k + 1 < itCount s ∧ t.pc = 0x80009c64)

theorem store_blk {s u w : MachineState} {k : Nat} (hpre : Walk.ExtendPreE s) (hp : Push s u k)
    (hr : Room s u w k) : ∃ t, Reaches Image.code w t ∧ Stored s u w t k := by
  have hI := hp.inv
  have hk := hp.lt
  have hf := facts hpre (by omega)
  have hb := sbounds hpre
  have hA := hpre.self
  have hAb := Region.bounds hA.region
  have hAf := hA.free
  simp only [Outside] at hAf
  have hu' : heapNext s ≤ heapNext u := hI.p.mono
  have hm := hr.mono
  have hwh := hr.heap.hi
  have hroom := hr.room
  have hlo := hpre.heap.lo
  simp only [heapStart] at hlo
  have hv := hpre.stack.valid
  rw [hK] at hv
  obtain ⟨hv1, hv2, hv3⟩ := vbuf hp hr
  have x9w : w.getReg .x9 = s.getReg .x10 := (hr.keep .x9 (by decide)).trans hI.x9
  have x22w : w.getReg .x22 = 88 := (hr.keep .x22 (by decide)).trans hI.x22
  have x24w : w.getReg .x24 = eqTag := (hr.keep .x24 (by decide)).trans hI.x24
  have hE : w.getMem (s.getReg .x10 + 8) + vecLen u (s.getReg .x10) * 88 = eNew s u w := by
    rw [mul88]; rfl
  have hRg : Region (eNew s u w) 88 :=
    heap_region (by simp only [eNew]; addr_omega [hv1, hv2, hlo, hroom, hu'])
      (by simp only [eNew, heapEnd] at hwh ⊢; addr_omega [hv1, hv2, hwh, hroom])
      (by simp only [eNew]; addr_omega [hv1, hv2, hv3, hroom])
  have hRb := Region.bounds hRg
  have heB : heapNext s ≤ (eNew s u w).toNat ∧ (eNew s u w).toNat + 88 ≤ heapNext w := by
    simp only [eNew]; constructor <;> addr_omega [hv1, hv2, hroom]
  obtain ⟨t, hrt, h⟩ := Sym.BlockSpec.reaches b80009bf8_spec hr.pc (by
    rv_eval [x9w, hr.x18, x22w, hr.sp, hE]
    and_intros <;> first
      | valid_access hv [hb]
      | exact Region.valid hRg (by addr_omega [hRb]) (by addr_omega [hRb]) (by addr_omega [hRb])
      | exact Region.valid hA.region (by addr_omega [hAb]) (by addr_omega [hAb]) (by addr_omega [hAb])
      | addr_omega [hb, hRb, heB, hwh, hAb, hAf.1, hu'])
  have kt := b80009bf8_keeps h
  have hw (a : Word) (h0 : ¬ Within a (s.getReg .x10 + 16) 8) (h1 : ¬ Within a (eNew s u w) 88) :
      t.getMem a = w.getMem a :=
    h.frame a (by
      rv_eval [x9w, hr.x18, x22w, hr.sp, hE]
      and_intros <;> addr_omega [h0, h1, hRb, hAb])
  have x19w : w.getReg .x19 = itEnd s := (hr.keep .x19 (by decide)).trans hI.x19
  have a56 : s.getReg .x2 - 240 + 56 = s.getReg .x2 - 184 := by addr_omega [hb]
  have a64 : s.getReg .x2 - 240 + 64 = s.getReg .x2 - 184 + 8 := by addr_omega [hb]
  have a72 : s.getReg .x2 - 240 + 72 = s.getReg .x2 - 184 + 16 := by addr_omega [hb]
  have a32 : s.getReg .x2 - 240 + 32 = s.getReg .x2 - 208 := by addr_omega [hb]
  have a40 : s.getReg .x2 - 240 + 40 = s.getReg .x2 - 208 + 8 := by addr_omega [hb]
  have a48 : s.getReg .x2 - 240 + 48 = s.getReg .x2 - 208 + 16 := by addr_omega [hb]
  have m1 := b80009bf8_m1 h
  have m2 := b80009bf8_m2 h
  have m3 := b80009bf8_m3 h
  have m8 := b80009bf8_m8 h
  have m9 := b80009bf8_m9 h
  have m10 := b80009bf8_m10 h
  have m11 := b80009bf8_m11 h
  have ml := b80009bf8_m_x9_16 h
  rw [x9w, hr.x18, x22w, hE, hr.sp] at m1 m2 m3 m8 m9 m10
  rw [x9w, hr.x18, x22w, hE, x24w] at m11
  rw [x9w, hr.x18] at ml
  rw [a48] at m1
  rw [a40] at m2
  rw [a32] at m3
  rw [a72] at m8
  rw [a64] at m9
  rw [a56] at m10
  refine ⟨t, hrt, fun a ha ↦ hw a (fun h' ↦ ha 0 (by decide) (Or.inl (by rwa [add_ofNat_zero])))
    (fun h' ↦ ha 0 (by decide) (Or.inr (by rwa [add_ofNat_zero]))), ml, m11, m10, m9, m8, m3, m2,
    m1, fun r hr' ↦ kt r ((by decide : [Reg.x2, .x8, .x9, .x19, .x20, .x21, .x22, .x23, .x24, .x25] ⊆ _) hr'), ?_⟩
  by_cases he : k + 1 = itCount s
  · exact Or.inl ⟨he, b80009bf8_pc_taken h (by rw [hr.x25, x19w]; exact (clAt_end hf (by omega)).mpr he)⟩
  · exact Or.inr ⟨by omega, b80009bf8_pc_not_taken h (by
      rw [hr.x25, x19w]; exact fun h' ↦ he ((clAt_end hf (by omega)).mp h'))⟩

end Rv64Verifier.Proofs.Pcs.Extend
