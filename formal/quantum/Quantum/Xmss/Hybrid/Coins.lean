module

public import Quantum.Xmss.Hybrid.Seed

@[expose] public section

/-!
# Coin reads: the hidden-cell hybrid with the challenger's coin cells

The challenger reads some cells of hidden hash computations (the randomizer bases' paths) only to
get fresh values. In runtime 2 such a read is a database read, which records the cell in the
database at an index that depends on hidden data (the scheme seed). This file replaces those
reads by classical coins.

* **Runtime 2 with coins** (`runtime2Coins Lc`): runtime 2, except that its read ports read the
  view `hwView W Lc`. A read of a cell of the coin table `Lc` that is not hardwired returns the coin
  `Lc` holds there and leaves the database untouched; the other reads are those of runtime 2
  (`hwReadKraus1_readH_of_none` and the like).
* **No direct comparison with runtime 2.** Reading an empty compressed cell records it, and a coin
  read does not. On a state whose read cell is empty, the Kraus weight of the difference of the
  two reads is `2 - 2 / √|Y|`, not `0`, so a hybrid between runtime 2 and coin reads cannot be
  charged to the states where the cell is recorded. The cost of a coin read is the later queries
  of the cell, which the hybrid with runtime 1 charges as hidden mass.
* **Runtime 1 against runtime 2 with coins.** Runtime 1 hardwires a table `L` that contains the
  coin table (`SubTable Lc L`). The two runtimes then read the coin cells alike, so the Kraus weight
  of the difference (`krausWeight_le_coinMass`) is at most `4` times `coinMass`: the hidden mass
  of `Kraus.lean` at the sponge ports, and at the read ports only for hidden cells outside `Lc`.
  `sqrt_win_runtime1_le_coins` is the square-root hybrid `√P₁ ≤ √P_c + ∑ⱼ √(4 μⱼ)` with the masses
  of the run against runtime 2 with coins.
* **Averaged, with the coin cells split off** (`uavg_win_runtime1_le_coins`): for hidden sets
  `H ∪ C` covering `L θ`, `E P₁ ≤ (√(E P_c) + ∑ⱼ √(4 (E μⱼ + εⱼ)))²`, where `μ` bounds the masses
  at `H` and `εⱼ` bounds the averaged mass of the `j`-th call at the coin cells `C`. For the
  seed-keyed coin cells, `εⱼ` is the scheme-seed hiding bound (`2^-256` per call plus a bad
  fraction), taken here as a hypothesis.
* **Lazy sampling of the coins** (`avg_hardwired_eq_avg_hardwired_coins`): averaged over uniform
  functions, S5's runtime 1 (`spongeHardwiredReadRuntime`) with the coin cells hardwired as well
  has the law of runtime 1 without them, when the program does not depend on the coins.
-/

open Matrix
open scoped Kronecker ENNReal ComplexOrder

universe u v w

open Quantum.SufCma

namespace Quantum.Xmss.Hybrid

open Quantum Quantum.Sponge

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M]

/-! ## Coin tables -/

/-- `Lc` is a sub-table of `L`: every cell of `Lc` holds the same value in `L`. -/
def SubTable (Lc L : Hw X Z) : Prop :=
  (∀ z, Lc.1 z ≠ none → L.1 z = Lc.1 z) ∧ (∀ x, Lc.2.1 x ≠ none → L.2.1 x = Lc.2.1 x) ∧
    (∀ x, Lc.2.2 x ≠ none → L.2.2 x = Lc.2.2 x)

/-- The views over a table and over a sub-table agree except at the hidden cells that are neither
hardwired nor in the sub-table. -/
theorem or_eq_or_of_sub {A Y : Type} {w l lc : A → Option Y} {H : Set A}
    (hl : ∀ a, l a ≠ none → a ∈ H) (hc : ∀ a, lc a ≠ none → l a = lc a) {a : A}
    (ha : ¬ (a ∈ H ∧ lc a = none ∧ w a = none)) : (w a).or (l a) = (w a).or (lc a) := by
  rcases hw : w a with _ | v
  · by_cases hlc : lc a = none
    · have hlN : l a = none := by
        by_contra hne
        exact ha ⟨hl a hne, hlc, hw⟩
      simp [hlN, hlc]
    · simp [hc a hlc]
  · rfl

omit [Fintype M] in
/-- A read of `h` outside the coin table is the read of runtime 2. -/
theorem hwReadKraus1_readH_of_none (Lc : Hw X Z) {z : Z} (hz : Lc.1 z = none)
    (upd : M → Option X → M) (r : Option X × M) :
    hwReadKraus1 Lc (.readH z upd) r = hwReadKraus (.readH z upd) r := by
  ext p q
  simp only [hwReadKraus1, hwReadKraus, readKraus1H, readKrausH, kroneckerMap_apply,
    clsKraus_apply]
  rw [cellRead_congr (w := (hwView q.2.2.1 Lc).1) (w' := q.2.2.1.1) (by simp [hwView, hz])]

omit [Fintype M] in
/-- A read of `k` outside the coin table is the read of runtime 2. -/
theorem hwReadKraus1_readK_of_none (Lc : Hw X Z) {x : X} (hx : Lc.2.1 x = none)
    (upd : M → Option Z → M) (r : Option Z × M) :
    hwReadKraus1 Lc (.readK x upd) r = hwReadKraus (.readK x upd) r := by
  ext p q
  simp only [hwReadKraus1, hwReadKraus, readKraus1K, readKrausK, kroneckerMap_apply,
    clsKraus_apply]
  rw [cellRead_congr (w := (hwView q.2.2.1 Lc).2.1) (w' := q.2.2.1.2.1) (by simp [hwView, hx])]

omit [Fintype M] in
/-- A read of `k'` outside the coin table is the read of runtime 2. -/
theorem hwReadKraus1_readK'_of_none (Lc : Hw X Z) {x : X} (hx : Lc.2.2 x = none)
    (upd : M → Option Z → M) (r : Option Z × M) :
    hwReadKraus1 Lc (.readK' x upd) r = hwReadKraus (.readK' x upd) r := by
  ext p q
  simp only [hwReadKraus1, hwReadKraus, readKraus1K', readKrausK', kroneckerMap_apply,
    clsKraus_apply]
  rw [cellRead_congr (w := (hwView q.2.2.1 Lc).2.2) (w' := q.2.2.1.2.2) (by simp [hwView, hx])]

/-! ## Runtime 2 with coins -/

variable [AddCommGroup X] [AddCommGroup Z]

variable (X Z) in
/-- **Runtime 2 with coins.** The sponge and program ports of runtime 2; the read ports read the
view `hwView W Lc`, so a read of a cell of `Lc` that is not hardwired returns the coin of `Lc`
and leaves the database untouched. -/
@[reducible]
noncomputable def runtime2Coins [Nonempty X] [Nonempty Z] (Lc : Hw X Z) (m₀ : M) :
    QuantumRuntime (hwSpec X Z M) where
  D := QReg.of (HwReg X Z M)
  init := initHw X Z m₀
  step := ((((spongeHardwired X Z (hwEmpty X Z) m₀).toRuntime :
    QuantumRuntime (spongeSpec X Z)).extend (t := hwReadCmdSpec X Z M) (hwReadStep1 Lc)).extend
      (t := hwProgSpec X Z) hwProgStep).step

variable (X Z) in
/-- The Kraus operators of runtime 2 with coins. -/
noncomputable def krausCoins (Lc : Hw X Z) (m₀ : M) : ∀ i : (hwSpec X Z M).Port,
    (hwSpec X Z M).Result i →
      Matrix ((hwSpec X Z M).Out i × QReg.of (HwReg X Z M))
        ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ
  | .inl (.inl i), _ => (spongeHardwired X Z (hwEmpty X Z) m₀).U i
  | .inl (.inr c), r => hwReadKraus1 Lc c r
  | .inr c, r => hwProgKraus c r

theorem runtime2Coins_branch [Nonempty X] [Nonempty Z] (Lc : Hw X Z) (m₀ : M)
    (i : (hwSpec X Z M).Port) (r : (hwSpec X Z M).Result i) :
    ((runtime2Coins X Z Lc m₀).step i).branch r = MatrixMap.conj (krausCoins X Z Lc m₀ i r) := by
  rcases i with (i | c) | c
  · exact (spongeHardwired X Z (hwEmpty X Z) m₀).toRuntime_step_branch i r
  · rfl
  · exact hwProgStep_branch c r

/-- **Hardwiring the coin cells is lazy sampling.** Let the data `P t` and the larger data `P' t`
(for instance `P t` together with the coin cells and their values in `t`) each determine their
hardwired cells (`hw`, `hw'`, as in `evalDistMap_avg_eq_tableLaw`), and let the program read only
`P t` (`y' (P' t) = y (P t)`). Averaged over uniform `t`, runtime 1 started with the cells of
`P' t` hardwired has the law of runtime 1 started with the cells of `P t` hardwired: both are the
experiment against the classical reads of `t`. -/
theorem avg_hardwired_eq_avg_hardwired_coins {β β' : Type*} {Λ : LocalSig.{u, v}}
    {Xf : QReg → Type w} {A : QReg} {γ : Type*} [MeasurableSpace γ]
    (P : (Z → X) × (X → Z) × (X → Z) → β) (hw : β → Hw X Z)
    (hP : ∀ t t', Consistent (hw (P t)) t' ↔ P t' = P t)
    (P' : (Z → X) × (X → Z) × (X → Z) → β') (hw' : β' → Hw X Z)
    (hP' : ∀ t t', Consistent (hw' (P' t)) t' ↔ P' t' = P' t) (m₀ : M) (I : Λ.Interp)
    (y : β → QuantumComp Λ (hwReadSpec X Z M) Xf A)
    (y' : β' → QuantumComp Λ (hwReadSpec X Z M) Xf A) (hy : ∀ t, y' (P' t) = y (P t))
    (ρ : SubState A) (f : (Σ u, Xf u) → γ) :
    ∑ t, (Fintype.card ((Z → X) × (X → Z) × (X → Z)) : ℝ≥0∞)⁻¹ •
        (spongeHardwiredReadRuntime X Z (hw' (P' t)) m₀).evalDistMap I (y' (P' t)) ρ f =
      ∑ t, (Fintype.card ((Z → X) × (X → Z) × (X → Z)) : ℝ≥0∞)⁻¹ •
        (spongeHardwiredReadRuntime X Z (hw (P t)) m₀).evalDistMap I (y (P t)) ρ f := by
  rw [← evalDistMap_avg_eq_avg_runtime1 P' hw' hP' m₀ I y' ρ f,
    ← evalDistMap_avg_eq_avg_runtime1 P hw hP m₀ I y ρ f]
  simp only [hy]

variable (X Z) in
/-- The difference of the Kraus operators of runtime 2 with coins and of runtime 1. -/
noncomputable def krausDiffCoins (L Lc : Hw X Z) (m₀ : M) (i : (hwSpec X Z M).Port)
    (r : (hwSpec X Z M).Result i) :
    Matrix ((hwSpec X Z M).Out i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ :=
  krausCoins X Z Lc m₀ i r - kraus1 X Z L m₀ i r

/-! ## The Kraus weights of the differences -/

/-- **The coin mass** of the input of a call: the hidden mass (`hiddenMass`) at the sponge ports;
at a read port, the mass of the states whose read cell is hidden, outside the coin table `Lc` and
not hardwired; `0` at the program ports. -/
noncomputable def coinMass (Hh : Set Z) (Hk Hk' : Set X) (Lc : Hw X Z) :
    ∀ i : (hwSpec X Z M).Port, Matrix ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ → ℝ≥0∞
  | .inl (.inl i) => hiddenMass Hh Hk Hk' (.inl (.inl i))
  | .inl (.inr (.readH z _)) =>
      diagMass {p : Unit × HwReg X Z M | z ∈ Hh ∧ Lc.1 z = none ∧ p.2.2.1.1 z = none}
  | .inl (.inr (.readK x _)) =>
      diagMass {p : Unit × HwReg X Z M | x ∈ Hk ∧ Lc.2.1 x = none ∧ p.2.2.1.2.1 x = none}
  | .inl (.inr (.readK' x _)) =>
      diagMass {p : Unit × HwReg X Z M | x ∈ Hk' ∧ Lc.2.2 x = none ∧ p.2.2.1.2.2 x = none}
  | .inr _ => fun _ ↦ 0

omit [AddCommGroup X] [AddCommGroup Z] in
/-- The coin mass is at most the hidden mass. -/
theorem coinMass_le_hiddenMass (Hh : Set Z) (Hk Hk' : Set X) (Lc : Hw X Z)
    (i : (hwSpec X Z M).Port)
    (σ : Matrix ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ) :
    coinMass Hh Hk Hk' Lc i σ ≤ hiddenMass Hh Hk Hk' i σ := by
  rcases i with (i | (⟨z, upd⟩ | ⟨x, upd⟩ | ⟨x, upd⟩)) | c
  · exact le_rfl
  · refine diagMass_mono ?_ σ
    rintro p ⟨h1, -, h3⟩
    exact ⟨h1, h3⟩
  · refine diagMass_mono ?_ σ
    rintro p ⟨h1, -, h3⟩
    exact ⟨h1, h3⟩
  · refine diagMass_mono ?_ σ
    rintro p ⟨h1, -, h3⟩
    exact ⟨h1, h3⟩
  · exact zero_le

/-- **A program call.** The two runtimes program alike, so the difference has weight `0`. -/
theorem krausWeight_coins_program_eq_zero (L Lc : Hw X Z) (m₀ : M) (c : HwProg X Z)
    (σ : Matrix ((hwSpec X Z M).In (.inr c) × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).In (.inr c) × QReg.of (HwReg X Z M)) ℂ) :
    QuantumRuntime.krausWeight (krausDiffCoins X Z L Lc m₀) (.inr c) σ = 0 := by
  rw [QuantumRuntime.krausWeight]
  refine ENNReal.tsum_eq_zero.2 fun r ↦ ?_
  rw [MatrixMap.conj_apply, show krausDiffCoins X Z L Lc m₀ (.inr c) r = 0 from sub_self _]
  have h0 : ∀ {a b : Type} [Fintype a] [Fintype b] (τ : Matrix a a ℂ),
      ((0 : Matrix b a ℂ) * τ * (0 : Matrix b a ℂ)ᴴ).trace.re ≤ 0 := fun _ ↦ by simp
  exact ENNReal.ofReal_eq_zero.2
    (h0 (b := (hwSpec X Z M).Out (.inr c) × QReg.of (HwReg X Z M)) σ)

variable {Hh : Set Z} {Hk Hk' : Set X}

/-- **Runtime 1 against runtime 2 with coins, at one call.** If the hidden sets cover `L` and the
coin table is a sub-table of `L`, the Kraus weight of the difference at any call is at most `4`
times the coin mass of its input. -/
theorem krausWeight_le_coinMass [Nonempty X] [Nonempty Z] (L Lc : Hw X Z) (m₀ : M)
    (hL : Covers L Hh Hk Hk') (hc : SubTable Lc L) (i : (hwSpec X Z M).Port)
    {σ : Matrix ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ} (hσ : σ.PosSemidef) :
    QuantumRuntime.krausWeight (krausDiffCoins X Z L Lc m₀) i σ ≤
      4 * coinMass Hh Hk Hk' Lc i σ := by
  obtain ⟨hLh, hLk, hLk'⟩ := hL
  obtain ⟨hch, hck, hck'⟩ := hc
  rcases i with (i | c) | c
  · exact krausWeight_le_hidden L m₀ ⟨hLh, hLk, hLk'⟩ (.inl (.inl i)) hσ
  · cases c with
    | readH z upd =>
      refine tsum_ofReal_trace_conj_sub_le (hwReadKraus1 Lc (.readH z upd))
        (hwReadKraus1 L (.readH z upd)) (sum_hwReadKraus1 Lc _) (sum_hwReadKraus1 L _)
        {p : Unit × HwReg X Z M | z ∈ Hh ∧ Lc.1 z = none ∧ p.2.2.1.1 z = none}
        (fun r ↦ sub_eq_sub_mul_setProj _ _ _ fun p q hq ↦ ?_) hσ
      simp only [hwReadKraus1, readKraus1H, kroneckerMap_apply, clsKraus_apply]
      rw [cellRead_congr (w := (hwView q.2.2.1 Lc).1) (w' := (hwView q.2.2.1 L).1)
        (by simp only [hwView, or_eq_or_of_sub (w := q.2.2.1.1) (a := z) hLh hch hq])]
    | readK x upd =>
      refine tsum_ofReal_trace_conj_sub_le (hwReadKraus1 Lc (.readK x upd))
        (hwReadKraus1 L (.readK x upd)) (sum_hwReadKraus1 Lc _) (sum_hwReadKraus1 L _)
        {p : Unit × HwReg X Z M | x ∈ Hk ∧ Lc.2.1 x = none ∧ p.2.2.1.2.1 x = none}
        (fun r ↦ sub_eq_sub_mul_setProj _ _ _ fun p q hq ↦ ?_) hσ
      simp only [hwReadKraus1, readKraus1K, kroneckerMap_apply, clsKraus_apply]
      rw [cellRead_congr (w := (hwView q.2.2.1 Lc).2.1) (w' := (hwView q.2.2.1 L).2.1)
        (by simp only [hwView, or_eq_or_of_sub (w := q.2.2.1.2.1) (a := x) hLk hck hq])]
    | readK' x upd =>
      refine tsum_ofReal_trace_conj_sub_le (hwReadKraus1 Lc (.readK' x upd))
        (hwReadKraus1 L (.readK' x upd)) (sum_hwReadKraus1 Lc _) (sum_hwReadKraus1 L _)
        {p : Unit × HwReg X Z M | x ∈ Hk' ∧ Lc.2.2 x = none ∧ p.2.2.1.2.2 x = none}
        (fun r ↦ sub_eq_sub_mul_setProj _ _ _ fun p q hq ↦ ?_) hσ
      simp only [hwReadKraus1, readKraus1K', kroneckerMap_apply, clsKraus_apply]
      rw [cellRead_congr (w := (hwView q.2.2.1 Lc).2.2) (w' := (hwView q.2.2.1 L).2.2)
        (by simp only [hwView, or_eq_or_of_sub (w := q.2.2.1.2.2) (a := x) hLk' hck' hq])]
  · rw [krausWeight_coins_program_eq_zero]
    exact zero_le

/-! ## The hybrid -/

section hybrid

variable [Nonempty X] [Nonempty Z] {Λ : LocalSig.{u, v}} (I : Λ.Interp) {Xf : QReg → Type w}
  {A : QReg} {γ : Type*} [MeasurableSpace γ]

/-- **The square-root hybrid with coins**, with the Kraus weights of the differences on the inputs
of the calls of the run against runtime 2 with coins. -/
theorem sqrt_win_runtime1_le_coins_krausWeight (L Lc : Hw X Z) (m₀ : M)
    (x : QuantumComp Λ (hwSpec X Z M) Xf A) (ρ : SubState A) (f : (Σ u, Xf u) → γ) {s : Set γ}
    (hs : MeasurableSet s) :
    (runtime1 X Z L m₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) ≤
      (runtime2Coins X Z Lc m₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) +
        ∑' j, (runtime2Coins X Z Lc m₀).queryWeight I
          (QuantumRuntime.krausWeight (krausDiffCoins X Z L Lc m₀)) x
          (ρ.matrix ⊗ₖ (runtime2Coins X Z Lc m₀).init.matrix) j ^ (2⁻¹ : ℝ) :=
  QuantumRuntime.rpow_inv_two_outcomeLawWith_le' I (initHw X Z m₀)
    (runtime2Coins_branch Lc m₀) (runtime1_branch L m₀) x ρ f hs

/-- **Runtime 1 against runtime 2 with coins.** If the hidden sets cover `L`, the coin table is a
sub-table of `L`, and the coin mass of the `j`-th call of the run against runtime 2 with coins is
at most `μ j`, then `√P₁ ≤ √P_c + ∑ⱼ √(4 μ j)`. -/
theorem sqrt_win_runtime1_le_coins (L Lc : Hw X Z) (m₀ : M) (hL : Covers L Hh Hk Hk')
    (hc : SubTable Lc L) (x : QuantumComp Λ (hwSpec X Z M) Xf A) (ρ : SubState A)
    (f : (Σ u, Xf u) → γ) {s : Set γ} (hs : MeasurableSet s) {μ : ℕ → ℝ≥0∞}
    (hMass : ∀ j, (runtime2Coins X Z Lc m₀).queryWeight I (coinMass Hh Hk Hk' Lc) x
      (ρ.matrix ⊗ₖ (runtime2Coins X Z Lc m₀).init.matrix) j ≤ μ j) :
    (runtime1 X Z L m₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) ≤
      (runtime2Coins X Z Lc m₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) +
        ∑' j, (4 * μ j) ^ (2⁻¹ : ℝ) := by
  refine (sqrt_win_runtime1_le_coins_krausWeight I L Lc m₀ x ρ f hs).trans
    (add_le_add le_rfl ?_)
  refine ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)
  calc (runtime2Coins X Z Lc m₀).queryWeight I
        (QuantumRuntime.krausWeight (krausDiffCoins X Z L Lc m₀)) x
        (ρ.matrix ⊗ₖ (runtime2Coins X Z Lc m₀).init.matrix) j
      ≤ (runtime2Coins X Z Lc m₀).queryWeight I (fun i σ ↦ 4 * coinMass Hh Hk Hk' Lc i σ) x
          (ρ.matrix ⊗ₖ (runtime2Coins X Z Lc m₀).init.matrix) j :=
        (runtime2Coins X Z Lc m₀).queryWeight_mono I
          (fun i _ hσ ↦ krausWeight_le_coinMass L Lc m₀ hL hc i hσ) x
          (ρ.prod (runtime2Coins X Z Lc m₀).init).posSemidef j
    _ = 4 * (runtime2Coins X Z Lc m₀).queryWeight I (coinMass Hh Hk Hk' Lc) x
          (ρ.matrix ⊗ₖ (runtime2Coins X Z Lc m₀).init.matrix) j :=
        (runtime2Coins X Z Lc m₀).queryWeight_const_mul I 4 x _ j
    _ ≤ 4 * μ j := by gcongr; exact hMass j

/-- **Runtime 1 against runtime 2 with coins, averaged over the table, with the coin cells split
off.** For tables `L θ` covered by the hidden sets `H θ ∪ C θ` and coin tables `Lc θ` inside them,
if the masses at `H θ` of the `j`-th call of the run against runtime 2 with coins are at most
`μ θ j` and the averaged masses at the coin cells `C θ` are at most `ε j` (for seed-keyed coin
cells, the scheme-seed hiding bound), then `E P₁ ≤ (√(E P_c) + ∑ⱼ √(4 (E μⱼ + ε j)))²`. -/
theorem uavg_win_runtime1_le_coins {Θ : Type*} [Fintype Θ] (L Lc : Θ → Hw X Z)
    (Hh₀ Ch : Θ → Set Z) (Hk₀ Hk'₀ Ck Ck' : Θ → Set X)
    (hL : ∀ θ, Covers (L θ) (Hh₀ θ ∪ Ch θ) (Hk₀ θ ∪ Ck θ) (Hk'₀ θ ∪ Ck' θ))
    (hc : ∀ θ, SubTable (Lc θ) (L θ)) (m₀ : M) (x : Θ → QuantumComp Λ (hwSpec X Z M) Xf A)
    (ρ : Θ → SubState A) (f : Θ → (Σ u, Xf u) → γ) {s : Set γ} (hs : MeasurableSet s)
    (μ : Θ → ℕ → ℝ≥0∞) (ε : ℕ → ℝ≥0∞)
    (hμ : ∀ θ j, (runtime2Coins X Z (Lc θ) m₀).queryWeight I
      (hiddenMass (Hh₀ θ) (Hk₀ θ) (Hk'₀ θ)) (x θ)
      ((ρ θ).matrix ⊗ₖ (runtime2Coins X Z (Lc θ) m₀).init.matrix) j ≤ μ θ j)
    (hε : ∀ j, uavg (fun θ ↦ (runtime2Coins X Z (Lc θ) m₀).queryWeight I
      (hiddenMass (Ch θ) (Ck θ) (Ck' θ)) (x θ)
      ((ρ θ).matrix ⊗ₖ (runtime2Coins X Z (Lc θ) m₀).init.matrix) j) ≤ ε j) :
    uavg (fun θ ↦ (runtime1 X Z (L θ) m₀).evalDistMap I (x θ) (ρ θ) (f θ) s) ≤
      (uavg (fun θ ↦ (runtime2Coins X Z (Lc θ) m₀).evalDistMap I (x θ) (ρ θ) (f θ) s) ^
          (2⁻¹ : ℝ) +
        ∑' j, (4 * (uavg (fun θ ↦ μ θ j) + ε j)) ^ (2⁻¹ : ℝ)) ^ 2 := by
  set ν : Θ → ℕ → ℝ≥0∞ := fun θ j ↦ (runtime2Coins X Z (Lc θ) m₀).queryWeight I
    (hiddenMass (Ch θ) (Ck θ) (Ck' θ)) (x θ)
    ((ρ θ).matrix ⊗ₖ (runtime2Coins X Z (Lc θ) m₀).init.matrix) j
  have hMass : ∀ θ j, (runtime2Coins X Z (Lc θ) m₀).queryWeight I
      (coinMass (Hh₀ θ ∪ Ch θ) (Hk₀ θ ∪ Ck θ) (Hk'₀ θ ∪ Ck' θ) (Lc θ)) (x θ)
      ((ρ θ).matrix ⊗ₖ (runtime2Coins X Z (Lc θ) m₀).init.matrix) j ≤ μ θ j + ν θ j :=
    fun θ j ↦ by
      calc _ ≤ (runtime2Coins X Z (Lc θ) m₀).queryWeight I
            (fun i σ ↦ hiddenMass (Hh₀ θ) (Hk₀ θ) (Hk'₀ θ) i σ +
              hiddenMass (Ch θ) (Ck θ) (Ck' θ) i σ) (x θ)
            ((ρ θ).matrix ⊗ₖ (runtime2Coins X Z (Lc θ) m₀).init.matrix) j :=
            (runtime2Coins X Z (Lc θ) m₀).queryWeight_mono I
              (fun i σ _ ↦ (coinMass_le_hiddenMass _ _ _ _ i σ).trans
                (hiddenMass_union_le _ _ _ _ _ _ i σ)) (x θ)
              ((ρ θ).prod (runtime2Coins X Z (Lc θ) m₀).init).posSemidef j
        _ = _ := queryWeight_add (runtime2Coins X Z (Lc θ) m₀) I _ _ (x θ) _ j
        _ ≤ μ θ j + ν θ j := add_le_add (hμ θ j) le_rfl
  refine (uavg_le_of_hybrid _ _ (fun θ j ↦ μ θ j + ν θ j) fun θ ↦
    sqrt_win_runtime1_le_coins I (L θ) (Lc θ) m₀ (hL θ) (hc θ) (x θ) (ρ θ) (f θ) hs
      (hMass θ)).trans ?_
  gcongr with j
  rw [uavg_add]
  exact add_le_add le_rfl (hε j)

end hybrid

end Quantum.Xmss.Hybrid

end
