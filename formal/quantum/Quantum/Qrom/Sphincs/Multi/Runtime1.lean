module

public import Quantum.Qrom.Sphincs.Multi.GameReads

@[expose] public section

/-!
# leanSPHINCS's multi-user QROM game is runtime 1 on good tables

The `n`-user analog of `Quantum.Qrom.Sphincs.Runtime1`. The game against a uniform `H` is its
regrouped calls against a uniform `F : HashDomain → PairOut` (`qromEvalDistMap_regroup`), and the
lazy table law on the good set (`Quantum.Qrom.qromEvalDistMap_apply_le_tableAvg_good`, at the
table of `n` users `tableN S0`) bounds this by the bad fraction of tables plus the average over
good table values `w` of runtime 1 started with the cells of `w` hardwired, running the
regrouped, lifted game. Against each function overwritten at the hardwired cells, the read
program `gameReadsWithSN` has the game's law there (`evalDistMap_muGame_eq_readsSN`), so runtime 1
runs it with the regrouped, lifted game's law (`read_port_eq_classical_read`,
`evalDistMap_hardwired_eq_avg`).

* `runtime1_muGame_eq_of_forallS`: runtime 1 runs a read program as the regrouped, lifted game
  when the two agree against every overwritten function.
* `runtime1_muGame_eq_readsSN`: at a good table, runtime 1 runs `gameReadsWithSN` as the
  regrouped, lifted game.
* `qromEvalDistMap_muGame_le_tableS`: the QROM law of an event of the game is at most the bad
  fraction of tables plus the average over good table values of runtime 1 on read programs with
  the regrouped, lifted game's law; `qromEvalDistMap_muGame_le_runtime1SN` at `gameReadsWithSN`.
-/

open MeasureTheory
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Quantum.Sponge (Hw hwReadSpec spongeHardwiredReadRuntime spongeFnReadRuntime overwrite
  evalDistMap_hardwired_eq_avg read_port_eq_classical_read)
open Quantum.Qrom.SufCma.Multi (muGame)

namespace Quantum.Qrom.Sphincs.Multi

attribute [local irreducible] sphincsRom

variable {n : ℕ} {M : Type} [Fintype M] [DecidableEq M]

/-- **Runtime 1 runs a read program as the regrouped, lifted game** when, against every function
overwritten at the hardwired cells `W₀`, the read program has the law of the game against the
regrouped function. -/
theorem runtime1_muGame_eq_of_forallS (W₀ : Hw PairOut HashDomain) (m₀ : M)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (S0 : Fin n → MasterSeed)
    (A : MuAdversaryS n)
    (y : QComp (hwReadSpec PairOut HashDomain M) (QReg.of Unit) (QReg.of Unit) Bool)
    (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ)
    (h : ∀ t, (spongeFnReadRuntime PairOut HashDomain t W₀ m₀).evalDistMap .instruments y ρ f =
      (additiveOracleRuntime (regroup hmsgRoute (overwrite W₀ t).1)).evalDistMap .instruments
        (muGame sphincsRom valid S0 A) ρ f) :
    (spongeHardwiredReadRuntime PairOut HashDomain W₀ m₀).evalDistMap .instruments y ρ f =
      (spongeHardwiredReadRuntime PairOut HashDomain W₀ m₀).evalDistMap .instruments
        (liftH (regroupCalls hmsgRoute (muGame sphincsRom valid S0 A))).liftOrdinary ρ f :=
  (read_port_eq_classical_read _ _ _ _ _ _).trans
    ((Finset.sum_congr rfl fun t _ ↦ congrArg _
      ((h t).trans ((evalDistMap_regroup_eq hmsgRoute _ _ ρ f).symm.trans
        (evalDistMap_spongeFnRuntime_liftH _ _ _ _ _ _ _).symm))).trans
      (evalDistMap_hardwired_eq_avg _ _ _ _ _ _).symm)

/-- **At a good table, runtime 1 runs the game's reads as the regrouped, lifted game**: started
with the cells of the good table `w` hardwired, runtime 1 gives `gameReadsWithSN M sgn` from `w`'s
public keys the law of the regrouped, lifted game, for a signer returning `w`'s signatures and
memo answers against every overwritten function. -/
theorem runtime1_muGame_eq_readsSN (S0 : Fin n → MasterSeed) {w : QTableN n}
    (hw : (tableN S0).good w) (m₀ : M) {sgn : SignerSN M n}
    (hsgn : ∀ t, SignsSN t ((tableN S0).hwOf w) m₀ w sgn)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n)
    (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (spongeHardwiredReadRuntime PairOut HashDomain ((tableN S0).hwOf w) m₀).evalDistMap
        .instruments (gameReadsWithSN M sgn (fun i ↦ (w.user i).publicKey) valid A) ρ f =
      (spongeHardwiredReadRuntime PairOut HashDomain ((tableN S0).hwOf w) m₀).evalDistMap
        .instruments (liftH (regroupCalls hmsgRoute (muGame sphincsRom valid S0 A))).liftOrdinary
        ρ f :=
  runtime1_muGame_eq_of_forallS _ m₀ valid S0 A _ ρ f fun t ↦
    (evalDistMap_muGame_eq_readsSN t _ m₀ (fun i ↦ consistent_fillN hw t.1 i) hw.2 (hsgn t)
      valid A ρ f).symm

/-- **The QROM law of an event of the game**: at most the bad fraction of tables plus the average
over good table values `w` of runtime 1 on read programs `y w` with the regrouped, lifted game's
law. -/
theorem qromEvalDistMap_muGame_le_tableS (S0 : Fin n → MasterSeed) (m₀ : M)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n)
    (y : QTableN n → QComp (hwReadSpec PairOut HashDomain M) (QReg.of Unit) (QReg.of Unit) Bool)
    (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ)
    (hy : ∀ w, (tableN S0).good w →
      (spongeHardwiredReadRuntime PairOut HashDomain ((tableN S0).hwOf w) m₀).evalDistMap
          .instruments (y w) ρ f =
        (spongeHardwiredReadRuntime PairOut HashDomain ((tableN S0).hwOf w) m₀).evalDistMap
          .instruments (liftH (regroupCalls hmsgRoute (muGame sphincsRom valid S0 A))).liftOrdinary
          ρ f) (s : Set γ) :
    qromEvalDistMap .instruments (muGame sphincsRom valid S0 A) ρ (fun _ ↦ f) s ≤
      (Fintype.card (QTableN n) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun w ↦ ¬(tableN S0).good w).card +
        ∑ w : QTableN n, (Fintype.card (QTableN n) : ℝ≥0∞)⁻¹ *
          (if (tableN S0).good w then
            (spongeHardwiredReadRuntime PairOut HashDomain ((tableN S0).hwOf w) m₀).evalDistMap
              .instruments (y w) ρ f s
            else 0) := by
  rw [← qromEvalDistMap_regroup (τ := hmsgRoute) (muGame sphincsRom valid S0 A) ρ fun _ ↦ f]
  exact (qromEvalDistMap_apply_le_tableAvg_good (tableN S0) m₀ .instruments
    (regroupCalls hmsgRoute (muGame sphincsRom valid S0 A)) ρ (fun _ ↦ f) s).trans_eq
    (congrArg _ (Finset.sum_congr rfl fun w _ ↦ congrArg _ (by
      by_cases h : (tableN S0).good w
      · rw [ite_eq_left h, ite_eq_left h, hy w h]
      · rw [ite_eq_right h, ite_eq_right h])))

/-- **The QROM law of an event of the game, by runtime 1 on the game's reads**: at most the bad
fraction of tables plus the average over good table values `w` of runtime 1 on
`gameReadsWithSN M (sgn w)` from `w`'s public keys, for signers returning `w`'s signatures and
memo answers against every overwritten function. -/
theorem qromEvalDistMap_muGame_le_runtime1SN (S0 : Fin n → MasterSeed) (m₀ : M)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n)
    (sgn : QTableN n → SignerSN M n)
    (hsgn : ∀ w, (tableN S0).good w → ∀ t, SignsSN t ((tableN S0).hwOf w) m₀ w (sgn w))
    (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) (s : Set γ) :
    qromEvalDistMap .instruments (muGame sphincsRom valid S0 A) ρ (fun _ ↦ f) s ≤
      (Fintype.card (QTableN n) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun w ↦ ¬(tableN S0).good w).card +
        ∑ w : QTableN n, (Fintype.card (QTableN n) : ℝ≥0∞)⁻¹ *
          (if (tableN S0).good w then
            (spongeHardwiredReadRuntime PairOut HashDomain ((tableN S0).hwOf w) m₀).evalDistMap
              .instruments (gameReadsWithSN M (sgn w) (fun i ↦ (w.user i).publicKey) valid A) ρ f s
            else 0) :=
  qromEvalDistMap_muGame_le_tableS S0 m₀ valid A
    (fun w ↦ gameReadsWithSN M (sgn w) (fun i ↦ (w.user i).publicKey) valid A) ρ f
    (fun w hw ↦ runtime1_muGame_eq_readsSN S0 hw m₀ (hsgn w hw) valid A ρ f) s

end Quantum.Qrom.Sphincs.Multi

end
