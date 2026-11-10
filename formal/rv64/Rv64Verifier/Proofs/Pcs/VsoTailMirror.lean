import Rv64Verifier.Proofs.Pcs.VsoTailGlueIn
import Rv64Verifier.Proofs.Pcs.VsoFinalIn
import Rv64Verifier.Proofs.Pcs.VsoOpenOA

/-!
# `verify_stacked_opening`'s level tail: the mirror through the tail

After the Merkle checks the mirror reads the intro message (`Fronted.value`, `afterWords_intro`)
and glues (`afterIntro`); a level that is not the last goes on to the next level
(`afterGlue_next`, `RunsK.toRuns` once the next root is written), the last to its tail
(`afterGlue_final`, `RunsK.toRunsF`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol

theorem cfg_folds_length (s : MachineState) : (cfgOf s).folds.length = K0 s + 2 := by
  simp [cfgOf, Model.Pcs.ladderFolds]

theorem afterGlue_next {s : MachineState} {x : LCtx} {ℓ : ℕ} {res : List E} {ml : ℕ}
    {Wl : Model.Pcs.WhirLocals} (hl : ℓ ≠ K0 s + 1) :
    Model.Pcs.afterGlue (s.getReg .x12).toNat (cfgOf s) (basisOf s x) ℓ (restOf s ℓ) res ml Wl =
      levelsFrom s x (ℓ + 1) Wl := by
  rw [Model.Pcs.afterGlue, ite_eq_right_of_eq_false _ _ (eq_false (by rw [cfg_folds_length]; omega))]
  rfl

theorem afterGlue_last {s : MachineState} {x : LCtx} {ℓ : ℕ} {res : List E} {ml : ℕ}
    {Wl : Model.Pcs.WhirLocals} (hl : ℓ = K0 s + 1) :
    Model.Pcs.afterGlue (s.getReg .x12).toNat (cfgOf s) (basisOf s x) ℓ (restOf s ℓ) res ml Wl =
      finalTailM (cfgOf s) (basisOf s x) res ml Wl :=
  afterGlue_final (by rw [cfg_folds_length]; omega)

/-- `RunsK` past a level, its next root `d` written: `Runs` at the next level. -/
theorem RunsK.toRuns {s u v : MachineState} {ℓ : ℕ} {m : Model.TM Unit} {d : Digest}
    {sh : ℕ × ℕ} (h : RunsK s u ℓ 1 m [(d, sh)]) (hsh : sh = rootShape s (ℓ + 1))
    (hd : digestAt v (s.getReg .x11) = d)
    (hT : ∀ T, TranscriptAt u (s.getReg .x10) T → TranscriptAt v (s.getReg .x10) T) :
    Runs s v (ℓ + 1) m := by
  intro T hT0 hO hr
  obtain ⟨T', R, e, hT', p, o, r, l, -, -, -⟩ := h T hT0 hO hr
  refine ⟨T', e, hT _ hT', p, by rw [o]; omega, by rw [r]; simp [l], ?_, fun h0 ↦ absurd h0 (by omega),
    fun _ ↦ ?_⟩
  · rw [r, List.getElem?_append_right (by omega), show ℓ + 1 - R.length = 0 by omega, hd]; rfl
  · rw [r, List.getElem?_append_right (by omega), show ℓ + 1 - R.length = 0 by omega, hsh]; rfl

/-- `RunsK` at the final level: `RunsF` for the transcripts whose openings `OpeningsAt` places. -/
theorem RunsK.toRunsF {s u : MachineState} {ℓ : ℕ} {m : Model.TM Unit} {nx : List (Digest × ℕ × ℕ)}
    (hpre : VsoPre s) (h : RunsK s u ℓ 1 m nx) : RunsF Transcript.OpeningsAt s u m :=
  fun T hT hO hr ↦ by
    obtain ⟨T', R, e, hT', -⟩ := h T hT (vsoOpeningsAt_of hO (vsoOpenMem_of hpre)) hr
    exact ⟨T', e, hT'⟩

/-- **The intro message read**, `afterWords` to `afterIntro`. -/
theorem RunsK.intro {s r g : MachineState} {ℓ : ℕ} {logN : ℕ} {config : Model.Pcs.WhirConfigRust}
    {basis : List E → Option E} {rest : List (ℕ × ℕ)} {S : Model.Pcs.WhirLocals} {lf res : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {lam : E} {qs : List Word}
    {words : List (List K)} {q : List E} {nx : List (Digest × ℕ × ℕ)}
    (hR : RunsK s r ℓ 1 (Model.Pcs.afterWords logN config basis ℓ rest S lf res pend lam qs words) nx)
    (hrows : eListAt r (r.getReg .x25) (r.getReg .x27).toNat =
      Model.Pcs.rowValuesRust ℓ words (Model.eqKernelRust lf))
    (hpw : eListAt r (vecPtr r (s.getReg .x2 - 488)) (r.getReg .x27).toNat =
      Verifier.powers lam qs.length)
    (hf : Fronted s r g q) :
    RunsK s g ℓ 1 (Model.Pcs.afterIntro logN config basis ℓ rest S res pend lam qs q) nx := by
  rw [Model.Pcs.afterWords] at hR
  refine hR.bind q hf.dig fun T hT ↦ ?_
  obtain ⟨T', e, hT', p, ro, o⟩ := hf.value T hT
  rw [hrows, hpw] at e
  exact ⟨T', e, hT', p, ro, o⟩

end Rv64Verifier.Proofs.Pcs.Vso
