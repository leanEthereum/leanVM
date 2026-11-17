module

public import Quantum.Qrom.Sphincs.GameReads

@[expose] public section

/-!
# leanSPHINCS's QROM game is runtime 1

G0 → G3 of the design for leanSPHINCS. The game against a uniform `H` is its regrouped calls
against a uniform `F : HashDomain → Y × Y` (`qromEvalDistMap_regroup`), and the lazy table law at
the honest table `table S0` (`qromEvalDistMap_eq_tableAvg_regroup`) writes this as the average over
uniform table values `v` of runtime 1 over `F` (`spongeHardwiredReadRuntime`) started with the
cells of `v` hardwired, running the regrouped, lifted game. Against each function `F` consistent
with `v`, the game against `regroup hmsgRoute F` is its read program `gameReads M A
(v.publicKey, S0)` (`evalDistMap_game_eq_reads`), and runtime 1 averages both over the same
functions (`read_port_eq_classical_read`, `evalDistMap_hardwired_eq_avg`), so runtime 1 runs the
read program with the law of the regrouped, lifted game (`runtime1_gameReads_eq`).

* `qrom_game_eq_runtime1`: the game's law in the QROM is the uniform average over the table
  values `v` of the law of `gameReads M A (v.publicKey, S0)` in runtime 1 started with the cells
  of `v` hardwired to `v`.
-/

open MeasureTheory
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum.Sponge (spongeHardwiredReadRuntime overwrite evalDistMap_hardwired_eq_avg
  read_port_eq_classical_read)

variable {M : Type} [Fintype M] [DecidableEq M]

/-- **Runtime 1 runs the game's reads as the regrouped, lifted game**: started with the cells of
the table `v` at `S_0` hardwired, runtime 1 gives `gameReads M A (v.publicKey, S0)` the law of the
game with regrouped calls lifted to port `h`. -/
theorem runtime1_gameReads_eq (S0 : MasterSeed) (v : QTable) (m₀ : M)
    (A : SufCma.Adversary PublicKey Message (Option Signature) Forgery)
    (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (spongeHardwiredReadRuntime PairOut Qrom.HashDomain ((table S0).hwOf v) m₀).evalDistMap
        .instruments (gameReads M A (v.publicKey, S0)) ρ f =
      (spongeHardwiredReadRuntime PairOut Qrom.HashDomain ((table S0).hwOf v) m₀).evalDistMap
        .instruments (liftH (regroupCalls hmsgRoute (SufCma.game sphincsRom S0 A))).liftOrdinary
        ρ f := by
  refine (read_port_eq_classical_read _ _ _ _ _ _).trans
    ((Finset.sum_congr rfl fun t _ ↦ congrArg _ ?_).trans
      (evalDistMap_hardwired_eq_avg _ _ _ _ _ _).symm)
  exact (evalDistMap_game_eq_reads (t := t) (W := (table S0).hwOf v) (m := m₀)
    (consistent_fill S0 v t.1) A ρ f).symm.trans
    ((evalDistMap_regroup_eq hmsgRoute _ _ ρ f).symm.trans
      (evalDistMap_spongeFnRuntime_liftH _ _ _ _ _ _ _).symm)

/-- **The game in the QROM is runtime 1 with honest reads (G0 → G3)**: its law is the uniform
average over the table values `v` of the law of `gameReads M A (v.publicKey, S0)` in runtime 1
over the regrouped function, started with the cells of `v` hardwired to `v`. -/
theorem qrom_game_eq_runtime1 (S0 : MasterSeed) (m₀ : M)
    (A : SufCma.Adversary PublicKey Message (Option Signature) Forgery)
    (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    qromEvalDistMap .instruments (SufCma.game sphincsRom S0 A) ρ (fun _ ↦ f) =
      ∑ v : QTable, (Fintype.card QTable : ℝ≥0∞)⁻¹ •
        (spongeHardwiredReadRuntime PairOut Qrom.HashDomain ((table S0).hwOf v) m₀).evalDistMap
          .instruments (gameReads M A (v.publicKey, S0)) ρ f :=
  (qromEvalDistMap_eq_tableAvg_regroup S0 m₀ (SufCma.game sphincsRom S0 A) ρ (fun _ ↦ f)
    (fun _ ↦ f) fun _ ↦ rfl).trans
    (Finset.sum_congr rfl fun v _ ↦ congrArg _ (runtime1_gameReads_eq S0 v m₀ A ρ f).symm)

end Quantum.Qrom.Sphincs

end
