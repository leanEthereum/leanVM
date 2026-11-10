import Rv64Verifier.Proofs.Gkr.LayerR11

/-!
# `keccak::verify_layer`, assembled

The contract from its two halves: the entry to the second check (`R0..R10`, `FirstHalf`, to
`J11`), `beta` and the lane weights (`lanes`, to `J12`), and the next weights, `linear_transpose`
and the epilogue (`R12..R17`, `SecondHalf`, from `J12` to the return).
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr

/-- From the entry: `J11`, a return or a dead end. -/
def FirstHalf : Prop :=
  ∀ s, s.pc = 0x8000f04c → VerifyLayerPre s → ∃ u, Reaches Image.code s u ∧
    ((∃ mu point eqZ eqLane t, J11 s u mu point eqZ eqLane t) ∨ Ret s u ∨ Dead Image.code u)

/-- From `J12`: the return or a dead end. -/
def SecondHalf : Prop :=
  ∀ s u mu point eqZ eqLane t beta, VerifyLayerPre s → J12 s u mu point eqZ eqLane t beta →
    ∃ v, Reaches Image.code u v ∧ (Ret s v ∨ Dead Image.code v)

theorem verify_layer_spec (hFirst : FirstHalf) (hD : DuplexSpec) (hM : MulSpec)
    (hMC : Runtime.MemcpySpec 0x800126e4) (hSecond : SecondHalf) : VerifyLayerSpec := by
  intro s hpc hpre
  obtain ⟨u, hr, ⟨mu, point, eqZ, eqLane, t, J⟩ | hret | hd⟩ := hFirst s hpc hpre
  · obtain ⟨v, beta, hr', J' | hd⟩ := lanes hD hM hMC hpre J
    · obtain ⟨w, hr'', hret | hd⟩ := hSecond s v mu point eqZ eqLane t beta hpre J'
      · exact ⟨w, hr.trans (hr'.trans hr''), Or.inl hret⟩
      · exact ⟨w, hr.trans (hr'.trans hr''), Or.inr hd⟩
    · exact ⟨v, hr.trans hr', Or.inr hd⟩
  · exact ⟨u, hr, Or.inl hret⟩
  · exact ⟨u, hr, Or.inr hd⟩

end Rv64Verifier.Gkr.Layer
