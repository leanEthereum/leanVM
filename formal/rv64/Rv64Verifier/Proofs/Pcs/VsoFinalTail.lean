import Rv64Verifier.Proofs.Pcs.VsoFinalCheck
import Rv64Verifier.Proofs.Transcript.Openings

/-!
# `verify_stacked_opening`'s final level: the tail, and the contract

`ToCheck` is the tail up to the terminal check: from `VsoFinalIn` (`0x8000b8ec`) through the
remaining sumcheck rounds, the checked byte, the terminal point, the basis and the glued claims to
`TC` (`0x8000bfe8`). With `check` it gives `TailSpec` (`tail_of`), and with the level loop
`verify_stacked_opening`'s contract, its openings those of `Transcript/Openings.lean`
(`vsoSpec_of`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol

/-- The tail up to the terminal check. -/
def ToCheck (OA : MachineState → Word → Model.TState → Prop) : Prop :=
  ∀ s x u Wl residual, VsoPre s → VsoFinalIn OA s x u Wl residual →
    ∃ v, Reaches Image.code u v ∧
      (FailR s v ∨ ∃ ml res tf w rt, TC OA s v ml res tf w rt)

theorem tail_of (hMle : MultilinearContracts.MleEvalSpec) (hM : MulSpec)
    {OA : MachineState → Word → Model.TState → Prop} (h : ToCheck OA) : TailSpec OA := by
  intro s x u Wl residual hpre hin
  obtain ⟨v, hv, hout⟩ := h s x u Wl residual hpre hin
  rcases hout with hf | ⟨ml, res, tf, w, rt, hc⟩
  · exact ⟨v, hv, Or.inl hf⟩
  obtain ⟨t, ht, hout⟩ := check hMle hM hpre hc
  exact ⟨t, hv.trans ht, hout⟩

/-- **`verify_stacked_opening`'s contract**, its openings `Transcript.OpeningsAt`, from the level
loop and the tail up to the terminal check. -/
theorem vsoSpec_of (hMle : MultilinearContracts.MleEvalSpec) (hM : MulSpec)
    (hL : LoopSpec Transcript.OpeningsAt) (hT : ToCheck Transcript.OpeningsAt) :
    VsoSpec Transcript.OpeningsAt :=
  vso_of hL (tail_of hMle hM hT)

end Rv64Verifier.Proofs.Pcs.Vso
