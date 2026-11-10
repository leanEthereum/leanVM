import Rv64Verifier.Proofs.Runtime.ForwardShift
import Rv64Verifier.Proofs.Runtime.CopyCode
import Rv64Verifier.Proofs.Runtime.BackwardShift

/-!
# `memcpy` and `memmove`

`memcpy` (`0x80011ff8`) drops `sp` by 16 and copies forward (`Forward.lean`). `memmove`
(`0x8001228c`) copies forward too when the destination is not above the source or the ranges are
apart (`dst - src ≥ n` as words), else backward (`Backward.lean`).
-/

namespace Rv64Verifier.Runtime
open RiscvZkvm.Rv64 Rv64Verifier.Sym Rv64Verifier.Runtime.Forward
open Rv64Verifier.Runtime.Memcpy (keepE keepC)

/-- **`memcpy` meets its contract.** -/
theorem memcpy_spec : MemcpySpec 0x80011ff8 := by
  intro s hpc hpre
  have hp : FwdPre s := {
    dst := hpre.dst
    src := hpre.src
    fwd := by
      have := hpre.apart
      simp only [Apart] at this
      omega
    stack := hpre.stack
    dstStack := hpre.dstStack
    srcStack := hpre.srcStack }
  obtain ⟨u, hr, hu⟩ := memcpy_sp.reaches hpc trivial
  have k := keepOf hu rfl (.x11 :: .x12 :: keepC)
  have e2 := hu.reg .x2 rfl
  blk at e2
  obtain ⟨t, ht, h⟩ := fwd_of memcpyCode_ok (shift_ok memcpyCode_ok) hp (pcC hu rfl)
    (by rw [e2, add_neg_lit, show (0 : Word) - 0xfffffffffffffff0 = 16 by decide]) k (sameOf hu rfl)
  exact ⟨t, hr.trans ht, Or.inl h⟩

/-- **`memmove` meets its contract.** -/
theorem memmove_spec : MemmoveSpec 0x8001228c := by
  intro s hpc hpre
  have hd := hpre.dst
  have hs := hpre.src
  simp only [Mapped] at hd hs
  obtain ⟨u, hr, hu⟩ := Backward.mm_entry.reaches hpc trivial
  have k := keepOf hu rfl (.x11 :: .x12 :: keepC)
  have e2 := hu.reg .x2 rfl
  blk at e2
  have hx2 : u.getReg .x2 = s.getReg .x2 - 16 := by
    rw [e2, add_neg_lit, show (0 : Word) - 0xfffffffffffffff0 = 16 by decide]
  by_cases hf : (s.getReg .x12).toNat ≤ (s.getReg .x10 - s.getReg .x11).toNat
  · have hp : FwdPre s := {
      dst := hpre.dst
      src := hpre.src
      fwd := by rw [BitVec.toNat_sub] at hf; omega
      stack := hpre.stack
      dstStack := hpre.dstStack
      srcStack := hpre.srcStack }
    obtain ⟨t, ht, h⟩ := fwd_of memmoveCode_ok (shift_ok memmoveCode_ok) hp
      (pcT hu rfl (by cond; exact hf)) hx2 k (sameOf hu rfl)
    exact ⟨t, hr.trans ht, Or.inl h⟩
  · have hp : Backward.BwdPre s := {
      dst := hpre.dst
      src := hpre.src
      bwd := by rw [BitVec.toNat_sub] at hf; omega
      stack := hpre.stack
      dstStack := hpre.dstStack
      srcStack := hpre.srcStack }
    obtain ⟨t, ht, h⟩ := Backward.bwd_of Backward.bshift_ok hp
      (pcF hu rfl (by cond; omega)) hx2 k (sameOf hu rfl)
    exact ⟨t, hr.trans ht, Or.inl h⟩

end Rv64Verifier.Runtime

/-- info: 'Rv64Verifier.Runtime.memcpy_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.memcpy_spec

/-- info: 'Rv64Verifier.Runtime.memmove_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.memmove_spec
