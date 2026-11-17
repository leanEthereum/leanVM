module

public import Quantum.Qrom.Xmss.Multi.GameReads

@[expose] public section

/-!
# leanXMSS's multi-user QROM game is runtime 1 on good tables

The `n`-user analog of `Quantum.Qrom.Xmss.Runtime1`. The lazy table law on the good set
(`Quantum.Qrom.tableAvg_good`, at the table of `n` users `tableN S0`) writes the game in the QROM,
restricted to functions with a good table, as the average over good table values `w` of runtime 1
started with the cells of `w` hardwired, running the lifted game. Against each function
overwritten at the hardwired cells, a read program with the game's law there
(`evalDistMap_muGame_eq_readsN`) has the lifted game's law in runtime 1
(`read_port_eq_classical_read`, `evalDistMap_hardwired_eq_avg`).

* `runtime1_muGame_eq_of_forall`: runtime 1 runs a read program as the lifted game when the two
  agree against every overwritten function.
* `runtime1_muGame_eq_readsN`: at a good table, runtime 1 runs `gameReadsWithN` as the lifted game.
* `tableAvg_muGame`, `qromEvalDistMap_muGame_le`: the QROM game on good tables is the average over
  good table values of runtime 1 on read programs with the game's law; the QROM law of an event is
  at most the bad fraction of tables plus that average.
-/

open MeasureTheory
open scoped ENNReal

namespace Quantum.Qrom.Xmss.Multi

open LeanXmss HashSig
open Quantum.Sponge (Hw hwReadSpec spongeHardwiredReadRuntime spongeFnReadRuntime overwrite
  evalDistMap_hardwired_eq_avg read_port_eq_classical_read)
open Quantum.Qrom.SufCma.Multi (muGame)

variable {n : ℕ} {M : Type} [Fintype M] [DecidableEq M]

/-- **Runtime 1 runs a read program as the lifted game** when, against every function overwritten
at the hardwired cells `W₀`, the read program has the game's law. -/
theorem runtime1_muGame_eq_of_forall (W₀ : Hw HashOutput HashDomain) (m₀ : M)
    (valid : SignLog → Bool) (S0 : Fin n → MasterSeed) (A : MuAdversary n)
    (y : QComp (hwReadSpec HashOutput HashDomain M) (QReg.of Unit) (QReg.of Unit) Bool)
    (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ)
    (h : ∀ t, (spongeFnReadRuntime HashOutput HashDomain t W₀ m₀).evalDistMap .instruments y ρ f =
      (additiveOracleRuntime (overwrite W₀ t).1).evalDistMap .instruments
        (muGame xmssRom valid S0 A) ρ f) :
    (spongeHardwiredReadRuntime HashOutput HashDomain W₀ m₀).evalDistMap .instruments y ρ f =
      (spongeHardwiredReadRuntime HashOutput HashDomain W₀ m₀).evalDistMap .instruments
        (liftH (muGame xmssRom valid S0 A)).liftOrdinary ρ f :=
  (read_port_eq_classical_read _ _ _ _ _ _).trans
    ((Finset.sum_congr rfl fun t _ ↦ congrArg _
      ((h t).trans (evalDistMap_spongeFnRuntime_liftH _ _ _ _ _ _ _).symm)).trans
      (evalDistMap_hardwired_eq_avg _ _ _ _ _ _).symm)

/-- **At a good table, runtime 1 runs the game's reads as the lifted game**: started with the
cells of the good table `w` hardwired, runtime 1 gives `gameReadsWithN M sgn` from `w`'s public
keys the law of the lifted game, for a signer returning `w`'s signatures and top selections
against every overwritten function. -/
theorem runtime1_muGame_eq_readsN (S0 : Fin n → MasterSeed) {w : QTableN n}
    (hw : (tableN S0).good w) (m₀ : M) {sgn : SignerN M n}
    (hsgn : ∀ t, SignsN t ((tableN S0).hwOf w) m₀ w sgn) (valid : SignLog → Bool)
    (A : MuAdversary n) (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (spongeHardwiredReadRuntime HashOutput HashDomain ((tableN S0).hwOf w) m₀).evalDistMap
        .instruments (gameReadsWithN M sgn (fun i ↦ (w.user i).publicKey) valid A) ρ f =
      (spongeHardwiredReadRuntime HashOutput HashDomain ((tableN S0).hwOf w) m₀).evalDistMap
        .instruments (liftH (muGame xmssRom valid S0 A)).liftOrdinary ρ f :=
  runtime1_muGame_eq_of_forall _ m₀ valid S0 A _ ρ f fun t ↦
    (evalDistMap_muGame_eq_readsN t _ m₀ (fun i ↦ consistent_fillN hw t.1 i) (hsgn t) valid A ρ
      f).symm

/-- **The QROM game on good tables is runtime 1 on read programs** (G0 → G3 for `n` users): for a
family `y` of read programs with the lifted game's law at every good table, the uniform average
over functions with a good table of the game's law is the uniform average over good table values
`w` of runtime 1 on `y w`, the cells of `w` hardwired. -/
theorem tableAvg_muGame (S0 : Fin n → MasterSeed) (m₀ : M) (valid : SignLog → Bool)
    (A : MuAdversary n)
    (y : QTableN n → QComp (hwReadSpec HashOutput HashDomain M) (QReg.of Unit) (QReg.of Unit) Bool)
    (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ)
    (hy : ∀ w, (tableN S0).good w →
      (spongeHardwiredReadRuntime HashOutput HashDomain ((tableN S0).hwOf w) m₀).evalDistMap
          .instruments (y w) ρ f =
        (spongeHardwiredReadRuntime HashOutput HashDomain ((tableN S0).hwOf w) m₀).evalDistMap
          .instruments (liftH (muGame xmssRom valid S0 A)).liftOrdinary ρ f) :
    ∑ H : HashDomain → HashOutput, (Fintype.card (HashDomain → HashOutput) : ℝ≥0∞)⁻¹ •
        (if (tableN S0).good ((tableN S0).tab H) then
          (additiveOracleRuntime H).evalDistMap .instruments (muGame xmssRom valid S0 A) ρ f
          else 0) =
      ∑ w : QTableN n, (Fintype.card (QTableN n) : ℝ≥0∞)⁻¹ •
        (if (tableN S0).good w then
          (spongeHardwiredReadRuntime HashOutput HashDomain ((tableN S0).hwOf w) m₀).evalDistMap
            .instruments (y w) ρ f
          else 0) :=
  (tableAvg_good (tableN S0) m₀ .instruments (muGame xmssRom valid S0 A) ρ fun _ ↦ f).trans
    (Finset.sum_congr rfl fun w _ ↦ congrArg _ (by
      by_cases h : (tableN S0).good w
      · rw [ite_eq_left h, ite_eq_left h, hy w h]
      · rw [ite_eq_right h, ite_eq_right h]))

/-- **The QROM law of an event of the game**: at most the bad fraction of tables plus the average
over good table values `w` of runtime 1 on read programs `y w` with the lifted game's law. -/
theorem qromEvalDistMap_muGame_le (S0 : Fin n → MasterSeed) (m₀ : M) (valid : SignLog → Bool)
    (A : MuAdversary n)
    (y : QTableN n → QComp (hwReadSpec HashOutput HashDomain M) (QReg.of Unit) (QReg.of Unit) Bool)
    (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ)
    (hy : ∀ w, (tableN S0).good w →
      (spongeHardwiredReadRuntime HashOutput HashDomain ((tableN S0).hwOf w) m₀).evalDistMap
          .instruments (y w) ρ f =
        (spongeHardwiredReadRuntime HashOutput HashDomain ((tableN S0).hwOf w) m₀).evalDistMap
          .instruments (liftH (muGame xmssRom valid S0 A)).liftOrdinary ρ f) (s : Set γ) :
    qromEvalDistMap .instruments (muGame xmssRom valid S0 A) ρ (fun _ ↦ f) s ≤
      (Fintype.card (QTableN n) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun w ↦ ¬(tableN S0).good w).card +
        ∑ w : QTableN n, (Fintype.card (QTableN n) : ℝ≥0∞)⁻¹ *
          (if (tableN S0).good w then
            (spongeHardwiredReadRuntime HashOutput HashDomain ((tableN S0).hwOf w) m₀).evalDistMap
              .instruments (y w) ρ f s
            else 0) :=
  (qromEvalDistMap_apply_le_tableAvg_good (tableN S0) m₀ .instruments (muGame xmssRom valid S0 A)
    ρ (fun _ ↦ f) s).trans_eq
    (congrArg _ (Finset.sum_congr rfl fun w _ ↦ congrArg _ (by
      by_cases h : (tableN S0).good w
      · rw [ite_eq_left h, ite_eq_left h, hy w h]
      · rw [ite_eq_right h, ite_eq_right h])))

end Quantum.Qrom.Xmss.Multi

end
