import Rv64Verifier.Proofs.Gkr.OpenLoop

/-!
# `keccak::open`

`open(transcript, shape, claim, first, count, value)` at `0x80010184`: `sumcheck` over the slot,
then per segment and lane the claim's position weights scaled into a row of 64
(`Proofs/Gkr/OpenStart.lean`, `OpenMid.lean`, `OpenLoop.lean`).
-/

namespace Rv64Verifier.Gkr.Open
open RiscvZkvm.Rv64 Rv64Verifier.Contracts Rv64Verifier.Gkr Rv64Verifier.Transcript

theorem ok_path (hEK : EqKernelSpec) (hM : MulSpec) {s m : MachineState} (hpre : OpenPre s)
    (P : P2 s m) (hok : m.getMem (s.getReg .x2 - 1688) ≠ 0xffffffffffffffff) :
    ∃ x, Reaches Image.code m x ∧ (AtFinal s m x ∨ Dead Image.code x) := by
  obtain ⟨e, hr₁, E | hd⟩ := to_ek1 hEK hpre P hok
  swap
  · exact ⟨e, hr₁, Or.inr hd⟩
  obtain ⟨u, hr₂, Z | hd⟩ := to_zero hEK hpre P hok E
  swap
  · exact ⟨u, hr₁.trans hr₂, Or.inr hd⟩
  obtain ⟨z, hr₃, D⟩ := zero_loop hpre u ⟨0, Z.pc, Z.mid, by rw [Z.x10]; simp, Z.x11, Z.x21,
    by decide, fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨q, hr₄, F | O⟩ := dispatch hpre P D
  · exact ⟨q, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inl F⟩
  obtain ⟨x, hr₅, h⟩ := outer_loop hM hpre P q ⟨0, O⟩
  exact ⟨x, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), h⟩

/-- **`open` meets its contract**, given its callees'. -/
theorem open_spec (hOF : OptFromElemSpec) (hSC : SumcheckSpec) (hEK : EqKernelSpec) (hM : MulSpec)
    (hMC : Runtime.MemcpySpec 0x800126e4) : OpenSpec := by
  intro s hpc hpre
  obtain ⟨m, hr, P | hd⟩ := to_sumcheck hOF hSC hpre hpc
  swap
  · exact ⟨m, hr, Or.inr hd⟩
  by_cases herr : m.getMem (s.getReg .x2 - 1688) = 0xffffffffffffffff
  · obtain ⟨t, hr', pc, pres, post⟩ := err hpre P herr
    exact ⟨t, hr.trans hr', Or.inl ⟨pc, pres, post⟩⟩
  obtain ⟨x, hr₁, X | hd⟩ := ok_path hEK hM hpre P herr
  swap
  · exact ⟨x, hr.trans hr₁, Or.inr hd⟩
  obtain ⟨t, hr₂, ht⟩ := final hMC hpre P herr X
  exact ⟨t, hr.trans (hr₁.trans hr₂), ht⟩

end Rv64Verifier.Gkr.Open

/-- info: 'Rv64Verifier.Gkr.Open.open_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Gkr.Open.open_spec
