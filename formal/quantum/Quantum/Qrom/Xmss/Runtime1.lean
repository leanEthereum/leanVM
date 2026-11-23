module

public import Quantum.Qrom.Xmss.GameReads

@[expose] public section

/-!
# leanXMSS's QROM game is runtime 1

G0 → G3 of the design for leanXMSS. The lazy table law (`qromEvalDistMap_eq_tableAvg`, at the
honest table `table S0`) writes the game in the QROM as the average over uniform table values `v`
of runtime 1 (`spongeHardwiredReadRuntime`) started with the cells of `v` hardwired, running the
lifted game. Against each function consistent with `v`, the game is its read program
`gameReads M A (v.publicKey, v.secretKey S0)` (`evalDistMap_game_eq_reads`), and runtime 1 averages
both over the same functions (`read_port_eq_classical_read`, `evalDistMap_hardwired_eq_avg`), so
runtime 1 runs the read program with the law of the lifted game (`runtime1_gameReads_eq`).

* `qrom_game_eq_runtime1`: the game's law in the QROM is the uniform average over the table
  values `v` of the law of `gameReads M A (v.publicKey, v.secretKey S0)` in runtime 1 started with
  the cells of `v` hardwired to `v`.
-/

open MeasureTheory
open scoped ENNReal

namespace Quantum.Qrom.Xmss

open LeanXmss HashSig
open Quantum.Sponge (spongeHardwiredReadRuntime overwrite evalDistMap_hardwired_eq_avg
  read_port_eq_classical_read)

variable {M : Type} [Fintype M] [DecidableEq M]

/-- **Runtime 1 runs the game's reads as the lifted game**: started with the cells of the table
`v` at `S_0` hardwired, runtime 1 gives `gameReads M A (v.publicKey, v.secretKey S0)` the law of
the game lifted to port `h`. -/
theorem runtime1_gameReads_eq (S0 : MasterSeed) (v : QTable) (m₀ : M) (A : Adversary)
    (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (spongeHardwiredReadRuntime HashOutput HashDomain ((table S0).hwOf v) m₀).evalDistMap
        .instruments (gameReads M A (v.publicKey, v.secretKey S0)) ρ f =
      (spongeHardwiredReadRuntime HashOutput HashDomain ((table S0).hwOf v) m₀).evalDistMap
        .instruments (liftH (SufCma.game xmssRom S0 A)).liftOrdinary ρ f := by
  refine (read_port_eq_classical_read _ _ _ _ _ _).trans
    ((Finset.sum_congr rfl fun t _ ↦ congrArg _ ?_).trans
      (evalDistMap_hardwired_eq_avg _ _ _ _ _ _).symm)
  exact (evalDistMap_game_eq_reads (t := t) (W := (table S0).hwOf v) (m := m₀)
    (consistent_fill S0 v t.1) A ρ f).symm.trans
    (evalDistMap_spongeFnRuntime_liftH _ _ _ _ _ _ _).symm

/-- **The game in the QROM is runtime 1 with honest reads (G0 → G3)**: its law is the uniform
average over the table values `v` of the law of `gameReads M A (v.publicKey, v.secretKey S0)` in
runtime 1 started with the cells of `v` hardwired to `v`. -/
theorem qrom_game_eq_runtime1 (S0 : MasterSeed) (m₀ : M) (A : Adversary)
    (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    qromEvalDistMap .instruments (SufCma.game xmssRom S0 A) ρ (fun _ ↦ f) =
      ∑ v : QTable, (Fintype.card QTable : ℝ≥0∞)⁻¹ •
        (spongeHardwiredReadRuntime HashOutput HashDomain ((table S0).hwOf v) m₀).evalDistMap
          .instruments (gameReads M A (v.publicKey, v.secretKey S0)) ρ f :=
  (qromEvalDistMap_eq_tableAvg (table S0) m₀ .instruments (SufCma.game xmssRom S0 A) ρ
    fun _ ↦ f).trans
    (Finset.sum_congr rfl fun v _ ↦ congrArg _ (runtime1_gameReads_eq S0 v m₀ A ρ f).symm)

end Quantum.Qrom.Xmss

end
