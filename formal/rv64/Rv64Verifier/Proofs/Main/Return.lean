import Rv64Verifier.Proofs.Main.Stages
import Rv64Verifier.Blocks.F3

/-!
# `walk`, then `main`'s epilogue

From `walk`'s entry (`AtWalk`), its contract brings `main` back to `0x80000dc8` with its frame
intact; the epilogue (`0x80000dc8`) returns `1` exactly when the result is not `Err`, which
`WalkCallSpec` and `walkRust_sound_new` turn into `verify = true` on the decoded input.
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Proofs.Bytecode Rv64Verifier.Proofs.End Rv64Verifier.Blocks.F3

theorem slot_bounds {k : Nat} {r : Reg} (h : (k, r) ∈ mainSlots) :
    472 ≤ k ∧ k + 8 ≤ 576 ∧ k % 8 = 0 := by
  simp only [mainSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  omega

theorem ult_ne {x : Word} (h : BitVec.ult x errTag = true) : x ≠ errTag := by
  rintro rfl
  simp [BitVec.ult] at h

/-- `walk` returns `Ok` only on an accepted proof; `main` then returns `1`, and only then. -/
theorem walk_return (hW : WalkCallSpec) {s : MachineState} {words : List Word}
    (hs : s.getReg .x2 = stackTop) :
    Runs (AtWalk s words) fun t ↦ t.pc = returnAddress s ∧ Preserves s t ∧ MainPost words s t := by
  intro u hu
  obtain ⟨t, hut, hout⟩ := hW u hu.pc hu.pre
  rcases hout with ⟨htpc, hpres, hpost⟩ | hd
  swap
  · exact ⟨t, hut, Or.inr hd⟩
  have husp := hu.inv.sp
  have hsp : t.getReg .x2 = msp := (hpres.reg .x2).trans husp
  have hhi := hpost.heap.hi
  have hlo := hu.pre.heap.lo
  have ha0 := hu.a0
  have keep : ∀ k r, (k, r) ∈ mainSlots → t.getMem (msp + BitVec.ofNat 64 k) = s.getReg r := by
    intro k r hk
    obtain ⟨h1, h2, -⟩ := slot_bounds hk
    rw [← hu.inv.slots (k, r) hk]
    refine hpost.frame.getMem fun i hi hw ↦ ?_
    rw [ha0] at hw
    simp only [stackLo, husp] at hw
    rcases hw with hw | hw | hw | hw <;> addr_omega [hw, h1, h2, hi, hhi, hlo]
  have hpc : t.pc = 0x80000dc8 := by rw [htpc, returnAddress, hu.ra]; decide
  obtain ⟨t', htt', hx⟩ := Sym.BlockSpec.reaches b80000dc8_spec hpc (by rv_eval [hsp, msp]; decide)
  have hx10 : t'.getReg .x10 =
      if BitVec.ult (t.getMem (t.getReg .x2 + 0x140#64)) 0xffffffffffffffff#64 then 1 else 0 :=
    hx.reg_eq .x10 rfl rfl
  refine ⟨t', hut.trans htt', Or.inl ⟨?_, ?_, ?_⟩⟩
  · rw [b80000dc8_pc hx, hsp, returnAddress]
    exact congrArg (· &&& 0xfffffffffffffffe) (keep 568 .x1 (by decide))
  · refine preserves_of ?_ ?_ ?_ ?_ ?_ ?_
    · rw [b80000dc8_x2 hx, hsp, hs]; decide
    · rw [b80000dc8_x8 hx, hsp]; exact keep 560 .x8 (by decide)
    · rw [b80000dc8_x9 hx, hsp]; exact keep 552 .x9 (by decide)
    · rw [b80000dc8_x18 hx, hsp]; exact keep 544 .x18 (by decide)
    · rw [b80000dc8_x19 hx, hsp]; exact keep 536 .x19 (by decide)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [b80000dc8_x20 hx, hsp]; exact keep 528 .x20 (by decide)
      · rw [b80000dc8_x21 hx, hsp]; exact keep 520 .x21 (by decide)
      · rw [b80000dc8_x22 hx, hsp]; exact keep 512 .x22 (by decide)
      · rw [b80000dc8_x23 hx, hsp]; exact keep 504 .x23 (by decide)
      · rw [b80000dc8_x24 hx, hsp]; exact keep 496 .x24 (by decide)
      · rw [b80000dc8_x25 hx, hsp]; exact keep 488 .x25 (by decide)
      · rw [b80000dc8_x26 hx, hsp]; exact keep 480 .x26 (by decide)
      · rw [b80000dc8_x27 hx, hsp]; exact keep 472 .x27 (by decide)
  · intro h1
    rw [hx10] at h1
    have hok : BitVec.ult (t.getMem (t.getReg .x2 + 0x140#64)) 0xffffffffffffffff#64 = true := by
      by_contra hc
      rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h1
      exact absurd h1 (by decide)
    have hne := ult_ne hok
    rw [hsp] at hne
    obtain ⟨summary, hsum⟩ := hpost.ok (by rw [ha0]; exact hne)
    obtain ⟨table, pi, proof, hdec, hlen, hnew, hpi, hproof⟩ := hu.ghost
    rw [hpi, hproof] at hsum
    exact ⟨table, pi, proof, hdec,
      Model.walkRust_sound_new table _ pi proof summary hnew hlen hsum⟩

end Rv64Verifier.Proofs.Main
