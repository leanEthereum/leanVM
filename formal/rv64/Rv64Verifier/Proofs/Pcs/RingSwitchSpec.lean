import Rv64Verifier.Proofs.Pcs.RingSwitchFin

/-!
# `ring_switch` meets its contract

The pieces in order: `prologue` (`samples`), `setup2` (the coefficients' buffer), `cLoop`,
`toImages` (the images' buffer), `iStart` and `iLoop` (or nothing when `s` is empty), `fin`
(`poly_eval`, the epilogue).
-/

namespace Rv64Verifier.Proofs.Pcs.RingSwitch
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.FieldContracts

/-- **`ring_switch` meets its contract**, given `samples`', the allocator's, `try_allocate_in`'s,
`pow`'s, `mul`'s and `poly_eval`'s. -/
theorem ring_switch_spec (hS : SamplesSpec) (hA : AllocSpec) (hT : TryAllocZeroedSpec)
    (hP : PowSpec) (hM : MulSpec) (hPE : MultilinearContracts.PolyEvalSpec) : RingSwitchSpec := by
  intro s hpc hpre
  obtain ⟨B, hsB, hB⟩ := prologue hS hpc hpre
  rcases hB with hd | hB
  · exact ⟨B, hsB, Or.inr hd⟩
  obtain ⟨u, hBu, hu⟩ := setup2 hA hpre hB
  rcases hu with hd | ⟨C, hctx, hh⟩
  · exact ⟨u, hsB.trans hBu, Or.inr hd⟩
  obtain ⟨v, huv, hv⟩ := cLoop hP hM hpre hctx hh
  rcases hv with hd | hv
  · exact ⟨v, hsB.trans (hBu.trans huv), Or.inr hd⟩
  obtain ⟨B2, hvB2, hB2⟩ := toImages hT hpre hctx hv
  rcases hB2 with hd | ⟨I, hctx2, hx21, hpcs⟩
  · exact ⟨B2, hsB.trans (hBu.trans (huv.trans hvB2)), Or.inr hd⟩
  have hsB2 := hsB.trans (hBu.trans (huv.trans hvB2))
  obtain ⟨w, hw, hex⟩ : ∃ w, Reaches Image.code B2 w ∧ (Dead Image.code w ∨
      IExit s B2 w I (vecEs B (s.getReg .x2 - 408)) (B2.getMem nextAddr)) := by
    rcases hpcs with ⟨hn, hpc2⟩ | ⟨hn, hpc2⟩
    · exact ⟨B2, Reaches.refl _, Or.inr {
        ph := Ph.refl hctx2.heap _
        pc := hpc2
        x21 := by rw [hx21, hn]; rfl
        buf := fun l hl ↦ absurd hl (by omega) }⟩
    · obtain ⟨h0, hr0, hh0⟩ := iStart hpre hctx2 hpc2 hx21 hn
      obtain ⟨w, hw, hw'⟩ := iLoop hP hM hpre hctx2 hh0
      exact ⟨w, hr0.trans hw, hw'⟩
  rcases hex with hd | hex
  · exact ⟨w, hsB2.trans hw, Or.inr hd⟩
  obtain ⟨t, hwt, ht⟩ := fin hPE hpre hctx2 hex
  exact ⟨t, hsB2.trans (hw.trans hwt), ht⟩

end Rv64Verifier.Proofs.Pcs.RingSwitch

/-- info: 'Rv64Verifier.Proofs.Pcs.RingSwitch.ring_switch_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.RingSwitch.ring_switch_spec
