module

public import Qrom.Sphincs.Classify.Main

@[expose] public section

/-!
# What a run of the hidden game reaches

The public-key port reports the public key read from the data (`Qrom.Sphincs.withKey_zero`), and
every side state a run reaches has an honest log (`Qrom.Sphincs.honestLog_closed`), so the events
of the game may assume both.
-/

open OracleComp OracleSpec FORS FORS.Security Quantum

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

variable [Params]

theorem readKey_eq (A : QReg) : readKey A = OvGame.sideCall (S := Log) (P := Port) (Res := Res)
    (X := Input) (Y := HashOutput) Port.pk A (fun _ r ↦ r.1) := rfl

/-- The adversary's run, at a public key other than the game's, has no weight. -/
theorem withKey_zero (g : OvGame Input HashOutput Log Port Res) (G : Input → HashOutput)
    (pk₀ : PublicKey) (hpk : ∀ s, (g.trans .pk s).1 = pk₀) {A : QReg} (adv : Adversary A)
    (ρ : SubState A) (pk : PublicKey) (F : Forgery) (hne : pk ≠ pk₀) :
    ((g.sampled G).jointPost₂ .instruments (withKey adv) ρ (pk, F)).matrix = 0 := by
  rw [QuantumRuntime.matrix_jointPost₂, withKey, QuantumRuntime.run₂_bind,
    DSubInstrument.branch_bind_apply]
  refine (tsum_congr fun pk' ↦ ?_).trans tsum_zero
  by_cases h : pk' = pk
  · subst h
    have hz : ((g.sampled G).run₂ .instruments (readKey A)).branch pk' = 0 := by
      rw [readKey_eq]
      exact OvGame.sideCall_zero g G Port.pk A _ pk' fun _ s ↦ by
        change (g.trans .pk s).1 ≠ pk'
        rw [hpk s]
        exact Ne.symm hne
    rw [hz, LinearMap.zero_apply, map_zero]
  · rw [QuantumRuntime.run₂_map, SubInstrument.branch_map_apply]
    have : IsEmpty ((fun F' ↦ (pk', F')) ⁻¹' {(pk, F)}) :=
      ⟨fun ⟨F', hF'⟩ ↦ h (Prod.mk.inj hF').1⟩
    rw [tsum_empty]

/-- Signing keeps the log honest. -/
theorem honestLog_closed (d : Data) (j : Port) (s : Log) (hs : HonestLog d s) :
    HonestLog d ((hidGame d).trans j s).2 := by
  cases j with
  | pk => exact hs
  | sign m =>
    simp only [hidGame, presGame, portTrans]
    split_ifs
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact hs e he
      · simp only [List.mem_singleton] at he
        subst he
        rfl
    · exact hs

theorem honestLog_empty (d : Data) : HonestLog d Log.empty := fun _ he ↦ by simp [Log.empty] at he

end Qrom.Sphincs
