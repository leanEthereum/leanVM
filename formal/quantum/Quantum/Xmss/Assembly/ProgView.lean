module

public import Quantum.Xmss.Assembly.CostRun

@[expose] public section

/-!
# The program flips along the game

Security's debt `progRest` (CostRun's `progRest_of_view`) bounds the flip costs `dPof L` of the
program ports along the canonical game `gameR A L`, averaged over the good tables. A program port
`c` moves a register state `s` by FlipCost's `progMap c` (the cell discarded from the databases and
hardwired), and its flip cost is the weight of the states outside `BadR` that it moves into `BadR`
(`flipCost_prog_le`). This file splits those flips by the state's cell.

* **Reprogramming costs nothing** (`progMap_mem_badR_iff_of_holds`): a port whose cell already
  holds its value leaves the hardwired cells as they are, and the discarded database cell is
  shadowed by the hardwired one (`union_updateH_of_hw`), so `progMap c s ∈ BadR ↔ s ∈ BadR`. With
  the hardwired cells inside a table `W` that the port programs (`Quantum.Sponge.HwLe s.2.1 W`,
  Runtime1's `ProgOf W c`; for the game at `L`, GameT's `progsOf_tableHw` with `W = tableHw L`, every
  value being the `L.keys` value of its cell), a hardwired cell holds the port's value
  (`cellHolds_of_le`).
* **The `h` cells of an honest path flip nothing** (`progMap_not_mem_badR_honest`,
  `progMap_not_mem_badR_short`): Events' `not_mem_bad_programH_honest` (the final cell, whose
  head-tail is the honest tail, exempted once hardwired) and `not_mem_bad_programH_short` (an
  intermediate cell, whose head-tail is a proper prefix of a non-message honest input), for the
  register with the memory label.
* **Only fresh `k`, `k'` cells flip** (`kFlipSet`, `ProgSafe`, `PortSafe`, `safeSupp`): a port is
  safe at `s` if it flips `s` only as a `k` or `k'` port with its cell free. Sufficient conditions:
  `progSafe_of_holds`, `progSafe_programK_of_le`, `progSafe_programK'_of_le`,
  `progSafe_programH_honest`, `progSafe_programH_short`. On safe states the flip cost of a port is
  at most the flip mass `kFlip L c` of its fresh `k`, `k'` cell (`dPof_le_kFlip`); along the game,
  with every program call presented safe states (`ForallQueries` of `safeSupp L`),
  `progTot A L ≤ kTot A L` (`progTot_le_kTot`, from the generic `totalWeight_le_of_forallQueries`).
* **Fresh `k`, `k'` flips averaged over the programmed value** (`card_kFlip_programK_le`,
  `sum_kFlip_programK_le`, their `k'` forms, `uavg_kFlip_programK_le`,
  `uavg_kFlip_programK'_le`): for `PermGood π 18` and grade `progCap + dbGrade D ≤ 2^68`, at most
  CostRun's counts `capK / |Z|`, `capK' / |Z| ≤ 2^-301` per unit of trace (`div_card_Z_le_of_le`).
* **`progRest` with a bad fraction** (`uavg_progTot_le`): if on the good tables (`PermGood π 18`
  and a further condition `Gd`) the game presents its program calls safe states, then the averaged
  program flips are at most the averaged fresh `k`, `k'` flips plus `progCap` times the fraction of
  the `PermGood` tables outside `Gd` (`progTot_le_progCap` off `Gd`).

**What remains.** (1) The support invariant `hsafe` of `uavg_progTot_le`: along `gameR A L`, every
program call is presented states whose hardwired cells lie in `tableHw L` (then every `k`, `k'`
port is safe, `progSafe_programK_of_le`), and at an `h` port with a free cell, the states outside
`BadR` have the head-tail facts of `progSafe_programH_honest` (final round) or
`progSafe_programH_short` (earlier rounds) after the batch's earlier ports. (2) The fresh `k`, `k'`
flips averaged over the table (`hk`). The `k`, `k'` values the game programs are the public keys'
(`roundK`, `roundK'` read `pub.keys`), which are not hidden coordinates of Template's
reparametrization (`HPos` holds only the honest 128-bit values and the randomizer bases), so the
averages `sum_kFlip_programK_le` apply only once the keys at the honest cells are lazily sampled
(revealed at their program port). The output `h` cells do not need FlipCost's
`flipCost_programH_avg_le` (which averages over all of `X`, while only the 128-bit digest of the
output value is hidden): they flip nothing on the states of the invariant.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

universe u v w u₁ v₁

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

/-! ## Weights bounded on the presented operators -/

section forallQueries

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {Λ : LocalSig.{u, v}}
  (I : Λ.Interp) {Ω : QReg → Type w} {A : QReg}

/-- **Weights compared on the presented operators**: if every operator a call satisfying `P` is
presented has (after tracing out the rest) the property `Ok`, and `w ≤ w'` on the positive
semidefinite operators with `Ok`, the total weights compare along a program whose calls all
satisfy `P`. -/
theorem totalWeight_le_of_forallQueries
    (Ok : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → Prop)
    {P : ∀ (i : spec.Port) (E : QReg),
      Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ → Prop}
    (hP : ∀ i E σ, P i E σ → Ok i (MatrixMap.traceRight (spec.In i × R.D) E σ))
    {w w' : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}
    (hw : ∀ i σ, σ.PosSemidef → Ok i σ → w i σ ≤ w' i σ)
    (x : QuantumComp Λ spec Ω A) {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef)
    (hx : R.ForallQueries I P x ρ) :
    R.totalWeight I w x ρ ≤ R.totalWeight I w' x ρ := by
  classical
  calc R.totalWeight I w x ρ
      = R.totalWeight I (fun i σ ↦ if Ok i σ then w i σ else w' i σ) x ρ :=
        totalWeight_congr_of_forallQueries R I
          (fun i E σ hσ ↦ (ite_eq_left (hP i E σ hσ)).symm) x ρ
          hx
    _ ≤ R.totalWeight I w' x ρ :=
        totalWeight_le_totalWeight R I (fun i σ hσ ↦ by
          split_ifs with h
          · exact hw i σ hσ h
          · exact le_rfl) x hρ

end forallQueries

attribute [local instance] badRDec

/-! ## Program ports on the register with the memory label -/

section cells

/-- The cell of a program port holds the port's value. -/
def CellHolds : HwProg X Z → Hw X Z → Prop
  | .programH z v, W => W.1 z = some v
  | .programK x v, W => W.2.1 x = some v
  | .programK' x v, W => W.2.2 x = some v

/-- **A hardwired cell inside a table the port programs holds the port's value.** -/
theorem cellHolds_of_le {W W' : Hw X Z} (hle : Quantum.Sponge.HwLe W W') {c : HwProg X Z}
    (hc : ProgOf W' c) (hcell : CellHardwired c W) : CellHolds c W := by
  cases c with
  | programH z v =>
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hcell
    have h1 : W'.1 z = some u := hle.1 z u hu
    have h2 : W'.1 z = some v := hc
    rw [h1, Option.some_inj] at h2
    show W.1 z = some v
    rw [hu, h2]
  | programK x v =>
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hcell
    have h1 : W'.2.1 x = some u := hle.2.1 x u hu
    have h2 : W'.2.1 x = some v := hc
    rw [h1, Option.some_inj] at h2
    show W.2.1 x = some v
    rw [hu, h2]
  | programK' x v =>
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hcell
    have h1 : W'.2.2 x = some u := hle.2.2 x u hu
    have h2 : W'.2.2 x = some v := hc
    rw [h1, Option.some_inj] at h2
    show W.2.2 x = some v
    rw [hu, h2]

/-- **Reprogramming a cell with the value it holds keeps the event**: the hardwired cells stay and
shadow the discarded database cell. -/
theorem progMap_mem_badR_iff_of_holds (L : HonestTable) (N : ℕ) (c : HwProg X Z)
    (s : HwReg X Z Mem) (h : CellHolds c s.2.1) :
    progMap c s ∈ BadR L N ↔ s ∈ BadR L N := by
  obtain ⟨⟨dh, dk, dk'⟩, ⟨wh, wk, wk'⟩, m⟩ := s
  cases c with
  | programH z v =>
    have h' : wh z = some v := h
    have hw : Function.update wh z (some v) = wh := Function.update_eq_self_iff.mpr h'.symm
    show ((Function.update dh z none, dk, dk'), (Function.update wh z (some v), wk, wk'), m.2) ∈
        Bad L N ↔ ((dh, dk, dk'), (wh, wk, wk'), m.2) ∈ Bad L N
    rw [hw, mem_bad_iff, mem_bad_iff,
      union_updateH_of_hw (wh, wk, wk') (w := v) h' dh dk dk' none]
  | programK x v =>
    have h' : wk x = some v := h
    have hw : Function.update wk x (some v) = wk := Function.update_eq_self_iff.mpr h'.symm
    show ((dh, Function.update dk x none, dk'), (wh, Function.update wk x (some v), wk'), m.2) ∈
        Bad L N ↔ ((dh, dk, dk'), (wh, wk, wk'), m.2) ∈ Bad L N
    rw [hw, mem_bad_iff, mem_bad_iff,
      union_updateK_of_hw (wh, wk, wk') (w := v) h' dh dk dk' none]
  | programK' x v =>
    have h' : wk' x = some v := h
    have hw : Function.update wk' x (some v) = wk' := Function.update_eq_self_iff.mpr h'.symm
    show ((dh, dk, Function.update dk' x none), (wh, wk, Function.update wk' x (some v)), m.2) ∈
        Bad L N ↔ ((dh, dk, dk'), (wh, wk, wk'), m.2) ∈ Bad L N
    rw [hw, mem_bad_iff, mem_bad_iff,
      union_updateK'_of_hw (wh, wk, wk') (w := v) h' dh dk dk' none]

/-- **Programming the final `h` cell of an exempted honest path flips nothing** (Events'
`not_mem_bad_programH_honest` on the register with the memory label). -/
theorem progMap_not_mem_badR_honest {L : HonestTable} {N : ℕ} {s : HwReg X Z Mem}
    (hs : s ∉ BadR L N) {z : Z} (hW : s.2.1.1 z = none) (v : X) {sl : Slot} {t₀ : List X}
    {xi₀ : X} (ht : L.honestTail sl = some t₀)
    (hex : sl ∈ exOf L (Function.update s.2.1.1 z (some v), s.2.1.2))
    (hhead : IsHeadTail L.perm (union s.2.1 s.1) t₀ z xi₀) :
    progMap (.programH z v) s ∉ BadR L N :=
  not_mem_bad_programH_honest (D := s.1) (W := s.2.1) (m := s.2.2.2) hs hW v ht hex hhead

/-- **Programming an intermediate `h` cell of a multi-block honest path flips nothing** (Events'
`not_mem_bad_programH_short` on the register with the memory label). -/
theorem progMap_not_mem_badR_short {L : HonestTable} {N : ℕ} {s : HwReg X Z Mem}
    (hs : s ∉ BadR L N) {z : Z} (hW : s.2.1.1 z = none) (v : X) {sl : Slot} {t₀ : List X}
    {xi₀ : X} (hslot : slotOf L.param t₀ = some sl) (hmsg : ∀ l e, sl ≠ .msg l e)
    (hlen : (L.honestTail sl).map List.length ≠ some t₀.length)
    (hhead : IsHeadTail L.perm (union s.2.1 s.1) t₀ z xi₀) :
    progMap (.programH z v) s ∉ BadR L N :=
  not_mem_bad_programH_short (D := s.1) (W := s.2.1) (m := s.2.2.2) hs hW v hslot hmsg hlen hhead

end cells

/-! ## Safe states and the fresh `k`, `k'` flips -/

section safe

/-- **The states a `k`, `k'` port flips with its cell free**: outside `BadR L progCap`, the cell
not hardwired, moved into `BadR L progCap`. An `h` port has none. -/
def kFlipSet (L : HonestTable) : HwProg X Z → Set (HwReg X Z Mem)
  | .programH _ _ => ∅
  | .programK x v => {s | s ∉ BadR L progCap ∧ s.2.1.2.1 x = none ∧
      progMap (.programK x v) s ∈ BadR L progCap}
  | .programK' x v => {s | s ∉ BadR L progCap ∧ s.2.1.2.2 x = none ∧
      progMap (.programK' x v) s ∈ BadR L progCap}

/-- **A port is safe at a state** if it flips the state only as a `k`, `k'` port with its cell
free. -/
def ProgSafe (L : HonestTable) (c : HwProg X Z) (s : HwReg X Z Mem) : Prop :=
  s ∉ BadR L progCap → progMap c s ∈ BadR L progCap → s ∈ kFlipSet L c

/-- A port whose cell holds its value is safe (it flips nothing). -/
theorem progSafe_of_holds (L : HonestTable) {c : HwProg X Z} {s : HwReg X Z Mem}
    (h : CellHolds c s.2.1) : ProgSafe L c s :=
  fun hs hp ↦ absurd ((progMap_mem_badR_iff_of_holds L progCap c s h).mp hp) hs

/-- A port with its cell hardwired inside a table it programs is safe. -/
theorem progSafe_of_le_of_hardwired (L : HonestTable) {W : Hw X Z} {c : HwProg X Z}
    {s : HwReg X Z Mem} (hle : Quantum.Sponge.HwLe s.2.1 W) (hc : ProgOf W c)
    (hcell : CellHardwired c s.2.1) : ProgSafe L c s :=
  progSafe_of_holds L (cellHolds_of_le hle hc hcell)

/-- **A `k` port is safe at every state whose hardwired cells lie in a table it programs.** -/
theorem progSafe_programK_of_le (L : HonestTable) {W : Hw X Z} {x : X} {v : Z}
    {s : HwReg X Z Mem} (hle : Quantum.Sponge.HwLe s.2.1 W) (hc : ProgOf W (.programK x v)) :
    ProgSafe L (.programK x v) s := by
  by_cases hx : s.2.1.2.1 x = none
  · exact fun hs hp ↦ ⟨hs, hx, hp⟩
  · exact progSafe_of_le_of_hardwired L hle hc hx

/-- **A `k'` port is safe at every state whose hardwired cells lie in a table it programs.** -/
theorem progSafe_programK'_of_le (L : HonestTable) {W : Hw X Z} {x : X} {v : Z}
    {s : HwReg X Z Mem} (hle : Quantum.Sponge.HwLe s.2.1 W) (hc : ProgOf W (.programK' x v)) :
    ProgSafe L (.programK' x v) s := by
  by_cases hx : s.2.1.2.2 x = none
  · exact fun hs hp ↦ ⟨hs, hx, hp⟩
  · exact progSafe_of_le_of_hardwired L hle hc hx

/-- **The final `h` port of an exempted honest path is safe** at a state with its cell free whose
head-tail facts hold when the state is outside `BadR`. -/
theorem progSafe_programH_honest (L : HonestTable) {z : Z} {v : X} {s : HwReg X Z Mem}
    (hW : s.2.1.1 z = none)
    (hh : s ∉ BadR L progCap → ∃ (sl : Slot) (t₀ : List X) (xi₀ : X),
      L.honestTail sl = some t₀ ∧ sl ∈ exOf L (Function.update s.2.1.1 z (some v), s.2.1.2) ∧
        IsHeadTail L.perm (union s.2.1 s.1) t₀ z xi₀) :
    ProgSafe L (.programH z v) s := fun hs hp ↦ by
  obtain ⟨_, _, _, ht, hex, hhead⟩ := hh hs
  exact absurd hp (progMap_not_mem_badR_honest hs hW v ht hex hhead)

/-- **An intermediate `h` port of a multi-block honest path is safe** at a state with its cell
free whose head-tail facts hold when the state is outside `BadR`. -/
theorem progSafe_programH_short (L : HonestTable) {z : Z} {v : X} {s : HwReg X Z Mem}
    (hW : s.2.1.1 z = none)
    (hh : s ∉ BadR L progCap → ∃ (sl : Slot) (t₀ : List X) (xi₀ : X),
      slotOf L.param t₀ = some sl ∧ (∀ l e, sl ≠ .msg l e) ∧
        (L.honestTail sl).map List.length ≠ some t₀.length ∧
        IsHeadTail L.perm (union s.2.1 s.1) t₀ z xi₀) :
    ProgSafe L (.programH z v) s := fun hs hp ↦ by
  obtain ⟨_, _, _, hslot, hmsg, hlen, hhead⟩ := hh hs
  exact absurd hp (progMap_not_mem_badR_short hs hW v hslot hmsg hlen hhead)

/-- **The flip mass of a port's fresh `k`, `k'` cell.** -/
noncomputable def kFlip (L : HonestTable) (c : HwProg X Z)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  diagMass {q | q.2 ∈ kFlipSet L c} σ

/-- **The fresh `k`, `k'` flip masses summed along the run of the game.** -/
noncomputable def kTot (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  costTot A (fun _ _ ↦ 0) (kFlip L) L

/-- **The flip cost of a port on the states where it is safe** is at most the flip mass of its
fresh `k`, `k'` cell. -/
theorem dPof_le_kFlip (L : HonestTable) (c : HwProg X Z)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hs : ∀ q, ¬ProgSafe L c q.2 → σ q q = 0) : dPof L c σ ≤ kFlip L c σ := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  refine (flipCost_prog_le (BadR L progCap) c hσ).trans ?_
  rw [kFlip, diagMass, ENNReal.ofReal_sum_of_nonneg fun q _ ↦ by split_ifs <;> simp [hre q]]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  split_ifs with h
  · by_cases hq : σ q q = 0
    · simp [hq]
    · have hmem : q ∈ {q : Unit × HwReg X Z Mem | q.2 ∈ kFlipSet L c} := by
        by_contra hn
        exact hq (hs q fun hsafe ↦ hn (hsafe h.1 h.2))
      rw [Set.indicator_of_mem hmem]
  · simp

/-- The flip cost of a port is at most the trace. -/
theorem dPof_le_trace (L : HonestTable) (c : HwProg X Z)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef) :
    dPof L c σ ≤ ENNReal.ofReal σ.trace.re := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  refine (flipCost_prog_le (BadR L progCap) c hσ).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [Matrix.trace, Complex.re_sum]
  exact Finset.sum_le_sum fun q _ ↦ by split_ifs <;> simp [hre q]

/-- Only the program ports are constrained: a program port must be safe at the state. -/
def PortSafe (L : HonestTable) : (recHwSpec X Z HPos Selections).Port → HwReg X Z Mem → Prop
  | .inl (.inr c), s => ProgSafe L c s
  | _, _ => True

/-- **The calls are presented safe states**: the presented operator vanishes on the register states
where the port is not safe. -/
def safeSupp (L : HonestTable) (i : (recHwSpec X Z HPos Selections).Port) (E : QReg)
    (σ : Matrix (((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) × E)
      (((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) × E) ℂ) :
    Prop :=
  ∀ a, ¬PortSafe L i a.1.2 → σ a a = 0

/-- **The program flips along the game are the fresh `k`, `k'` flips** when every call is presented
safe states. -/
theorem progTot_le_kTot (A : Adversary (X × Z)) (L : HonestTable)
    (hsafe : (runtimeR m0R).ForallQueries .instruments (safeSupp L) (gameR A L) initR) :
    progTot A L ≤ kTot A L := by
  unfold progTot kTot costTot
  refine totalWeight_le_of_forallQueries (runtimeR m0R) .instruments
    (fun i τ ↦ ∀ q, ¬PortSafe L i q.2 → τ q q = 0)
    (fun i E σ hσ q hq ↦ traceRight_diag_eq_zero fun e ↦ hσ (q, e) hq) (fun i τ hτ hok ↦ ?_)
    (gameR A L) initR_posSemidef hsafe
  rcases i with ((p | c) | c) | T
  · show (0 : ℝ≥0∞) ≤ 0
    exact le_rfl
  · show (0 : ℝ≥0∞) ≤ 0
    exact le_rfl
  · exact dPof_le_kFlip L c hτ hok
  · show (0 : ℝ≥0∞) ≤ 0
    exact le_rfl

end safe

/-! ## The fresh `k`, `k'` flips averaged over the programmed value -/

section avg

/-- The program flips of the game are at most its program calls. -/
theorem progTot_le_progCap {q : ℕ} {A : Adversary (X × Z)}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
    (L : HonestTable) : progTot A L ≤ progCap := by
  unfold progTot costTot
  refine (totalWeight_le_totalWeight (runtimeR m0R) .instruments
    (w' := extWeight (hwCost (fun _ _ ↦ 0) fun _ σ ↦ ENNReal.ofReal σ.trace.re))
    (fun i σ hσ ↦ ?_) (gameR A L) initR_posSemidef).trans
    (totalWeight_progs_le (gameR A L) (progCalls_gameR hperm hsign L))
  rcases i with ((p | c) | c) | T
  · show (0 : ℝ≥0∞) ≤ 0
    exact le_rfl
  · show (0 : ℝ≥0∞) ≤ 0
    exact le_rfl
  · exact dPof_le_trace L c hσ
  · show (0 : ℝ≥0∞) ≤ 0
    exact le_rfl

/-- A count of at most `2^211` values of `Z` is a fraction at most `2^-301`. -/
theorem div_card_Z_le_of_le {C : ℕ} (hC : C ≤ 2 ^ 211) :
    (C : ℝ≥0∞) / Fintype.card Z ≤ (2 ^ 301)⁻¹ := by
  have h : (C : ℝ≥0∞) ≤ 2 ^ 211 := by exact_mod_cast hC
  rw [card_Z, Nat.cast_pow, Nat.cast_ofNat]
  calc (C : ℝ≥0∞) / 2 ^ 512 ≤ 2 ^ 211 / 2 ^ 512 := by gcongr
    _ = (2 ^ 301)⁻¹ := by
        rw [show (2 : ℝ≥0∞) ^ 512 = 2 ^ 211 * 2 ^ 301 by rw [← pow_add], ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), mul_comm ((2 : ℝ≥0∞) ^ 211)⁻¹,
          mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]

/-- A family of diagonal masses summed over a finite index: each state weighs its trace entry
times the number of indices whose set holds it; with at most `C` such indices at every state of
the support, at most `C` times the trace. -/
theorem sum_diagMass_le_card {V α : Type} [Fintype V] [Fintype α] (Cs : V → Set α) (C : ℕ)
    {σ : Matrix α α ℂ} (hσ : σ.PosSemidef)
    (hC : ∀ a, σ a a ≠ 0 → ∀ t : Finset V, (∀ v ∈ t, a ∈ Cs v) → ∀ v₀ ∈ t, t.card ≤ C) :
    ∑ v, diagMass (Cs v) σ ≤ C * ENNReal.ofReal σ.trace.re := by
  classical
  have hre : ∀ a, 0 ≤ (σ a a).re := fun a ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have htr : ENNReal.ofReal σ.trace.re = ∑ a, ENNReal.ofReal (σ a a).re := by
    rw [Matrix.trace, Complex.re_sum]
    simp only [Matrix.diag_apply]
    exact ENNReal.ofReal_sum_of_nonneg fun a _ ↦ hre a
  simp only [diagMass]
  rw [Finset.sum_comm, htr, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  simp only [Set.indicator_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  by_cases ha : σ a a = 0
  · simp [ha]
  · gcongr
    by_cases he : ∃ v₀, a ∈ Cs v₀
    · obtain ⟨v₀, hv₀⟩ := he
      exact_mod_cast hC a ha _ (fun v hv ↦ (Finset.mem_filter.1 hv).2) v₀
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hv₀⟩)
    · simp only [not_exists] at he
      rw [Finset.filter_false_of_mem fun v _ ↦ he v]
      simp

/-- **The fresh `k` flips at a state**: the values flipping it with its cell free are at most the
capacity-scale count of `card_flip_programK_bad_le`. -/
theorem card_kFlip_programK_le {L : HonestTable} {G T : ℕ} (hπ : PermGood L.perm G) (x : X)
    (s : HwReg X Z Mem) (hT : s.2.1.2.1 x = none → progCap + dbGrade s.1 ≤ T) (t : Finset Z)
    (ht : ∀ v ∈ t, s ∈ kFlipSet L (.programK x v)) (v₀ : Z) (hv₀ : v₀ ∈ t) :
    t.card ≤ (T + 1) * ((T + 1) * T + 2 * T) * G := by
  classical
  obtain ⟨hs, hx, -⟩ := ht v₀ hv₀
  exact (Finset.card_le_card fun v hv ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _,
    (ht v hv).2.2⟩).trans
    (card_flip_programK_bad_le (D := s.1) (W := s.2.1) (m := s.2.2.2) hπ hs (hT hx) hx)

/-- **The fresh `k'` flips at a state**: the values flipping it with its cell free are at most the
capacity-scale count of `card_flip_programK'_bad_le`. -/
theorem card_kFlip_programK'_le {L : HonestTable} {G T : ℕ} (hπ : PermGood L.perm G) (x : X)
    (s : HwReg X Z Mem) (hT : s.2.1.2.2 x = none → progCap + dbGrade s.1 ≤ T) (t : Finset Z)
    (ht : ∀ v ∈ t, s ∈ kFlipSet L (.programK' x v)) (v₀ : Z) (hv₀ : v₀ ∈ t) :
    t.card ≤ (T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T := by
  classical
  obtain ⟨hs, hx, -⟩ := ht v₀ hv₀
  exact (Finset.card_le_card fun v hv ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _,
    (ht v hv).2.2⟩).trans
    (card_flip_programK'_bad_le (D := s.1) (W := s.2.1) (m := s.2.2.2) hπ hs (hT hx) hx)

/-- **The fresh `k` flips summed over the programmed value**: for `PermGood π G`, on states with
`progCap + dbGrade D ≤ T` where the cell is free, at most the capacity-scale count times the
trace. -/
theorem sum_kFlip_programK_le {L : HonestTable} {G T : ℕ} (hπ : PermGood L.perm G) (x : X)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hT : ∀ q, σ q q ≠ 0 → q.2.2.1.2.1 x = none → progCap + dbGrade q.2.1 ≤ T) :
    ∑ v : Z, kFlip L (.programK x v) σ ≤
      (((T + 1) * ((T + 1) * T + 2 * T) * G : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re := by
  show ∑ v : Z, diagMass {q : Unit × HwReg X Z Mem | q.2 ∈ kFlipSet L (.programK x v)} σ ≤ _
  exact sum_diagMass_le_card (fun v : Z ↦ {q : Unit × HwReg X Z Mem |
    q.2 ∈ kFlipSet L (.programK x v)}) _ hσ fun q hq t ht v₀ hv₀ ↦
      card_kFlip_programK_le hπ x q.2 (hT q hq) t ht v₀ hv₀

/-- **The fresh `k'` flips summed over the programmed value**: for `PermGood π G`, on states with
`progCap + dbGrade D ≤ T` where the cell is free, at most the capacity-scale count times the
trace. -/
theorem sum_kFlip_programK'_le {L : HonestTable} {G T : ℕ} (hπ : PermGood L.perm G) (x : X)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hT : ∀ q, σ q q ≠ 0 → q.2.2.1.2.2 x = none → progCap + dbGrade q.2.1 ≤ T) :
    ∑ v : Z, kFlip L (.programK' x v) σ ≤
      (((T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal σ.trace.re := by
  show ∑ v : Z, diagMass {q : Unit × HwReg X Z Mem | q.2 ∈ kFlipSet L (.programK' x v)} σ ≤ _
  exact sum_diagMass_le_card (fun v : Z ↦ {q : Unit × HwReg X Z Mem |
    q.2 ∈ kFlipSet L (.programK' x v)}) _ hσ fun q hq t ht v₀ hv₀ ↦
      card_kFlip_programK'_le hπ x q.2 (hT q hq) t ht v₀ hv₀

/-- A sum over the values of `Z` bounded by `C` times a weight with `C ≤ 2^211` averages to at
most `2^-301` times the weight. -/
theorem inv_card_Z_mul_le {C : ℕ} (hC : C ≤ 2 ^ 211) {a b : ℝ≥0∞} (h : a ≤ C * b) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * a ≤ (2 ^ 301)⁻¹ * b :=
  calc (Fintype.card Z : ℝ≥0∞)⁻¹ * a ≤ (Fintype.card Z : ℝ≥0∞)⁻¹ * (C * b) := by gcongr
    _ = (C : ℝ≥0∞) / Fintype.card Z * b := by rw [ENNReal.div_eq_inv_mul, mul_assoc]
    _ ≤ (2 ^ 301)⁻¹ * b := by
        gcongr
        exact div_card_Z_le_of_le hC

/-- **The fresh `k` flips averaged over the programmed value**: for `PermGood π 18`, at grade
`progCap + dbGrade D ≤ 2^68`, at most `2^-301` per unit of trace (CostRun's `capK` count). -/
theorem uavg_kFlip_programK_le {L : HonestTable} (hπ : PermGood L.perm 18) (x : X)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hT : ∀ q, σ q q ≠ 0 → q.2.2.1.2.1 x = none → progCap + dbGrade q.2.1 ≤ 2 ^ 68) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ v : Z, kFlip L (.programK x v) σ ≤
      (2 ^ 301)⁻¹ * ENNReal.ofReal σ.trace.re :=
  inv_card_Z_mul_le (by norm_num) (sum_kFlip_programK_le hπ x hσ hT)

/-- **The fresh `k'` flips averaged over the programmed value**: for `PermGood π 18`, at grade
`progCap + dbGrade D ≤ 2^68`, at most `2^-301` per unit of trace (CostRun's `capK'` count). -/
theorem uavg_kFlip_programK'_le {L : HonestTable} (hπ : PermGood L.perm 18) (x : X)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hT : ∀ q, σ q q ≠ 0 → q.2.2.1.2.2 x = none → progCap + dbGrade q.2.1 ≤ 2 ^ 68) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ v : Z, kFlip L (.programK' x v) σ ≤
      (2 ^ 301)⁻¹ * ENNReal.ofReal σ.trace.re :=
  inv_card_Z_mul_le (by norm_num) (sum_kFlip_programK'_le hπ x hσ hT)

end avg

/-! ## `progRest` with a bad fraction -/

section progRest

/-- **The averaged program flips, from the safe states.** On the tables with `PermGood π 18` and
`Gd`, let every call of the game be presented safe states (`hsafe`), and let the fresh `k`, `k'`
flips average to at most `κ` there (`hk`). Then the averaged program flips over the `PermGood`
tables are at most `κ` plus `progCap` times the fraction of the `PermGood` tables outside `Gd`. -/
theorem uavg_progTot_le {q : ℕ} {A : Adversary (X × Z)}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
    (Gd : HonestTable → Prop) [DecidablePred Gd]
    (hsafe : ∀ L, PermGood L.perm 18 → Gd L →
      (runtimeR m0R).ForallQueries .instruments (safeSupp L) (gameR A L) initR)
    {κ : ℝ≥0∞} (hk : uavg (fun L ↦ if PermGood L.perm 18 ∧ Gd L then kTot A L else 0) ≤ κ) :
    uavg (fun L ↦ if PermGood L.perm 18 then progTot A L else 0) ≤
      κ + progCap * uavg (fun L ↦ if PermGood L.perm 18 ∧ ¬Gd L then (1 : ℝ≥0∞) else 0) := by
  calc uavg (fun L ↦ if PermGood L.perm 18 then progTot A L else 0)
      ≤ uavg (fun L ↦ (if PermGood L.perm 18 ∧ Gd L then kTot A L else 0) +
          progCap * (if PermGood L.perm 18 ∧ ¬Gd L then (1 : ℝ≥0∞) else 0)) :=
        uavg_mono fun L ↦ ?_
    _ = uavg (fun L ↦ if PermGood L.perm 18 ∧ Gd L then kTot A L else 0) +
          progCap * uavg (fun L ↦ if PermGood L.perm 18 ∧ ¬Gd L then (1 : ℝ≥0∞) else 0) := by
        rw [uavg_add, uavg_const_mul]
    _ ≤ _ := add_le_add hk le_rfl
  by_cases hπ : PermGood L.perm 18
  · by_cases hg : Gd L
    · rw [ite_eq_left hπ, ite_eq_left ⟨hπ, hg⟩, ite_eq_right fun h ↦ h.2 hg, mul_zero, add_zero]
      exact progTot_le_kTot A L (hsafe L hπ hg)
    · rw [ite_eq_left hπ, ite_eq_right fun h ↦ hg h.2, ite_eq_left ⟨hπ, hg⟩, mul_one, zero_add]
      exact progTot_le_progCap hperm hsign L
  · rw [ite_eq_right hπ]
    exact zero_le

end progRest

end Quantum.Xmss.Assembly

end
