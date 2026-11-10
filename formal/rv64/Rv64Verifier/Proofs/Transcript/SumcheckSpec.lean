import Rv64Verifier.Proofs.Transcript.SumcheckSetup

/-!
# `transcript::sumcheck` meets its contract

The setup, then the loop (`Reaches.loop`, the measure `s11`, `32` per round left): a round from the
loop head reaches the next one, or the exit, or the `Err` exit.
-/

namespace Rv64Verifier.Transcript.Sumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F76
  Rv64Verifier.Contracts

/-- One round, from the loop head. -/
theorem round (hRP : RoundPolySpec) (hD : DuplexSpec) (hP : PolyEvalSpec) {s u : MachineState}
    {ptr : Word} {i : Nat} (hpre : SumcheckPre s) (hpc : u.pc = 0x8001062c) (h : Inv s u ptr i) :
    ∃ v, Reaches Image.code u v ∧ (Done s v ∨
      (v.pc = 0x8001062c ∧ Inv s v ptr (i + 1))) := by
  obtain ⟨v₁, h₁, hd | ⟨hpc₁, hv₁⟩⟩ := roundPoly hRP hpre hpc h
  · exact ⟨v₁, h₁, Or.inl hd⟩
  obtain ⟨v₂, h₂, hd | ⟨hpc₂, hv₂⟩⟩ := sample hD hpre hpc₁ hv₁
  · exact ⟨v₂, h₁.trans h₂, Or.inl (Or.inr hd)⟩
  obtain ⟨v₃, h₃, hd | ⟨hn, he⟩⟩ := push hP hpre hpc₂ hv₂
  · exact ⟨v₃, h₁.trans (h₂.trans h₃), Or.inl (Or.inr hd)⟩
  have hlt := hv₂.lt
  by_cases hl : i + 1 < (s.getReg .x15).toNat
  · exact ⟨v₃, h₁.trans (h₂.trans h₃), Or.inr (hn hl)⟩
  · obtain ⟨hpc₃, hex⟩ := he (by omega)
    obtain ⟨t, h₄, ht⟩ := exitOk hpre hpc₃ hex
    exact ⟨t, h₁.trans (h₂.trans (h₃.trans h₄)), Or.inl (Or.inl ht)⟩

/-- **`transcript::sumcheck` meets its contract**, given `try_allocate_in`'s,
`sumcheck_round_poly`'s, `duplex`'s and `poly_eval`'s. -/
theorem sumcheck_spec (hT : TryAllocZeroedSpec) (hRP : RoundPolySpec) (hD : DuplexSpec)
    (hP : PolyEvalSpec) : SumcheckSpec := by
  intro s hpc hpre
  obtain ⟨v, hr, hd | ⟨ptr, ⟨hpcv, hinv⟩ | ⟨hpcv, hex⟩⟩⟩ := setup hT hpc hpre
  · exact ⟨v, hr, Or.inr hd⟩
  · obtain ⟨t, ht, hdone⟩ := Reaches.loop (code := Image.code)
      (fun u ↦ ∃ i, u.pc = 0x8001062c ∧ Inv s u ptr i)
      (fun u ↦ (s.getReg .x15).toNat - (u.getMem (s.getReg .x2 - 184)).toNat) (Done s)
      (fun u ⟨i, hpcu, hu⟩ ↦ by
        obtain ⟨w, hw, hd | ⟨hpcw, hw'⟩⟩ := round hRP hD hP hpre hpcu hu
        · exact Or.inl ⟨w, hw, hd⟩
        · refine Or.inr ⟨w, hw, ⟨i + 1, hpcw, hw'⟩, ?_⟩
          have hnl := n_lt hpre
          have hlt := hw'.lt
          rw [hu.lenM, hw'.lenM, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]
          omega) v ⟨0, hpcv, hinv⟩
    exact ⟨t, hr.trans ht, hdone⟩
  · obtain ⟨t, ht, hpct, hpres, hpost⟩ := exitOk hpre hpcv hex
    exact ⟨t, hr.trans ht, Or.inl ⟨hpct, hpres, hpost⟩⟩

end Rv64Verifier.Transcript.Sumcheck
