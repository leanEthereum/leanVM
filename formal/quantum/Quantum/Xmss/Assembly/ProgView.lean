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
* **The hardwired cells stay inside `tableHw L`** (`ProgsIn`, `forallQueries_of_progsIn`,
  `progsIn_gameT`, `forallQueries_hwSupp_gameR`): every program port of the game at `L` programs a
  cell of `tableHw L` with its value (GameT's `progsOf_tableHw`), every other port keeps the
  hardwired cells, so every call is presented states with `HwLe W (tableHw L)` (GameTCalls' `HP`
  pattern). Then every `k`, `k'` port and every `h` port with its cell hardwired is safe
  (`safeSupp_of_hwSupp`), and `hsafe` reduces to the `h` ports with a free cell
  (`forallQueries_safeSupp_gameR`, `uavg_progTot_le_of_hFree` with `hFreeSupp`).
* **The head-tail of a round** (`isHeadTail_take_succ`, `isHeadTail_roundH`): a database holding
  the `k`, `k'` points of rounds `0, …, j` of a slot's input under the public keys has the tail of
  the first `j + 1` blocks heading to `roundH`'s cell of round `j`.

**What remains.** (1) `hFreeSupp` along `gameR A L`: at an `h` port of round `j` of slot `s` with
its cell free, the states outside `BadR` have the facts of `progSafe_programH_honest` (final round)
or `progSafe_programH_short` (earlier rounds). Missing pieces: the batch's earlier ports of `s` are
hardwired at the call (an `HP`-style invariant on the order of `slotPorts`), which with
`HwLe W (tableHw L)` gives `AgreesRounds` for the union and `isHeadTail_roundH`; for the final
round, `slotInput (pubOf L) s (valueAt L) = L.honestInput s` (GameT's `slotPayload_eq`) and
`HeldIn` of the programmed state (`inputReads` against the round cells); for earlier rounds,
`slotOf` of a proper prefix of the honest tail. (2) The fresh `k`, `k'` flips averaged over the
table (`hk`): the keys at a cell enter the run only through its program ports and the later rounds
of its path, so the presented operator before the first program of `x`, restricted to states with
`x` free, does not depend on `pub.keys` at `x`; averaging then gives `uavg_kFlip_programK_le`. This
lazy-sampling statement over the public keys is not proved here. The output `h` cells do not need
FlipCost's `flipCost_programH_avg_le` (which averages over all of `X`, while only the 128-bit
digest of the output value is hidden): they flip nothing on the states of the invariant.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

universe u v w w₁ u₁ v₁

open Quantum.SufCma

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

/-! ## The hardwired cells stay inside a table the game programs

`ProgsIn W v y`: every program port of the template `y`, realized at `v`, programs a cell of `W`
with its `W` value (Runtime1's `ProgOf`). Every port of `runtimeR` then keeps the hardwired cells
inside `W` (a program of a cell of `W` with its value, the other ports keep them), so the realized
program presents at every call only states with `HwLe W₀ W` (`forallQueries_of_progsIn`). For the
game at the table (`progsIn_gameT` with GameT's `progsOf_tableHw`): `forallQueries_hwSupp_gameR`. -/

section hwLeGen

variable {X₁ Z₁ : Type} [DecidableEq X₁] [DecidableEq Z₁]

/-- Programming a cell of `W` with its `W` value keeps the hardwired cells inside `W`. -/
theorem hwLe_progUpdate {W₀ W : Hw X₁ Z₁} (h : Quantum.Sponge.HwLe W₀ W) {c : HwProg X₁ Z₁}
    (hc : ProgOf W c) : Quantum.Sponge.HwLe (progUpdate c W₀) W := by
  obtain ⟨h1, h2, h3⟩ := h
  cases c with
  | programH z a =>
    refine ⟨fun z' u hu ↦ ?_, h2, h3⟩
    change Function.update W₀.1 z (some a) z' = some u at hu
    by_cases hz : z' = z
    · subst hz
      rw [Function.update_self, Option.some_inj] at hu
      subst hu
      exact hc
    · rw [Function.update_of_ne hz] at hu
      exact h1 z' u hu
  | programK x a =>
    refine ⟨h1, fun x' u hu ↦ ?_, h3⟩
    change Function.update W₀.2.1 x (some a) x' = some u at hu
    by_cases hx : x' = x
    · subst hx
      rw [Function.update_self, Option.some_inj] at hu
      subst hu
      exact hc
    · rw [Function.update_of_ne hx] at hu
      exact h2 x' u hu
  | programK' x a =>
    refine ⟨h1, h2, fun x' u hu ↦ ?_⟩
    change Function.update W₀.2.2 x (some a) x' = some u at hu
    by_cases hx : x' = x
    · subst hx
      rw [Function.update_self, Option.some_inj] at hu
      subst hu
      exact hc
    · rw [Function.update_of_ne hx] at hu
      exact h3 x' u hu

omit [DecidableEq X₁] [DecidableEq Z₁] in
/-- No hardwired cell lies outside any table. -/
theorem spongeHwLe_hwEmpty (W : Hw X₁ Z₁) : Quantum.Sponge.HwLe (hwEmpty X₁ Z₁) W := by
  refine ⟨fun z u hu ↦ ?_, fun x u hu ↦ ?_, fun x u hu ↦ ?_⟩
  · rw [show (hwEmpty X₁ Z₁).1 z = none from rfl] at hu
    cases hu
  · rw [show (hwEmpty X₁ Z₁).2.1 x = none from rfl] at hu
    cases hu
  · rw [show (hwEmpty X₁ Z₁).2.2 x = none from rfl] at hu
    cases hu

end hwLeGen

section hwLe

variable {M : Type} [Fintype M] [DecidableEq M] {Λ : LocalSig.{u, v}} {Ω : QReg → Type w}

omit [Fintype M] in
/-- A read port keeps the hardwired cells. -/
theorem hwReadKraus_ne_zero_hw (c : HwRead X Z M) (r : c.Result) {u u' : Unit}
    {s s' : HwReg X Z M} (h : hwReadKraus c r (u', s') (u, s) ≠ 0) : s'.2.1 = s.2.1 := by
  cases c with
  | readH z upd =>
    simp only [hwReadKraus, readKrausH] at h
    obtain ⟨-, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
  | readK x upd =>
    simp only [hwReadKraus, readKrausK] at h
    obtain ⟨-, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
  | readK' x upd =>
    simp only [hwReadKraus, readKrausK'] at h
    obtain ⟨-, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]

/-- A step of `runtimeR` at port `i` keeps the support on the states whose hardwired cells lie in
`W`. -/
def StepHw (m₀ : Finset HPos × M) (W : Hw X Z) (i : (recHwSpec X Z HPos M).Port) : Prop :=
  ∀ r σ, QuerySupportedOn (fun m : (recHwSpec X Z HPos M).In i × (runtimeR m₀).D ↦ m.2)
      {s : HwReg X Z (Finset HPos × M) | Quantum.Sponge.HwLe s.2.1 W} σ →
    QuerySupportedOn (fun m : (recHwSpec X Z HPos M).Out i × (runtimeR m₀).D ↦ m.2)
      {s : HwReg X Z (Finset HPos × M) | Quantum.Sponge.HwLe s.2.1 W}
      (((runtimeR m₀).step i).branch r σ)

theorem stepHw_sponge (m₀ : Finset HPos × M) (W : Hw X Z) (i : SpongePort) :
    StepHw m₀ W (.inl (.inl (.inl i))) := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inl i)))).branch r σ =
      MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U i) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m₀ i r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    have he := snd_eq_of_spongeHardwired_U_ne_zero (hwEmpty X Z) m₀ i q.1 q'.1 q.2 q'.2 hK
    show Quantum.Sponge.HwLe q'.2.2.1 W
    rw [congrArg Prod.fst he]
    exact hq

theorem stepHw_read (m₀ : Finset HPos × M) (W : Hw X Z)
    (c : {c : HwRead X Z (Finset HPos × M) // ReadMono (memLab X Z HPos M) c}) :
    StepHw m₀ W (.inl (.inl (.inr c.1))) := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inr c.1)))).branch r σ =
      MatrixMap.conj (hwReadKraus c.1 r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m₀ c.1 r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    show Quantum.Sponge.HwLe q'.2.2.1 W
    rw [hwReadKraus_ne_zero_hw c.1 r (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK]
    exact hq

theorem stepHw_prog (m₀ : Finset HPos × M) {W : Hw X Z} {c : HwProg X Z} (hc : ProgOf W c) :
    StepHw m₀ W (.inl (.inr c)) := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inr c))).branch r σ =
      MatrixMap.conj (hwProgKraus c r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m₀ c r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    show Quantum.Sponge.HwLe q'.2.2.1 W
    rw [hwProgKraus_ne_zero_snd c r (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK]
    exact hwLe_progUpdate hq hc

theorem stepHw_rec (m₀ : Finset HPos × M) (W : Hw X Z) (T : Finset HPos) :
    StepHw m₀ W (.inr T) := by
  intro r σ hσ
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    show Quantum.Sponge.HwLe q'.2.2.1 W
    rw [recKraus_ne_zero (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK]
    exact hq

variable (M) in
/-- A program port must program a cell of `W` with its `W` value; the other ports are free. -/
def PortIn (W : Hw X Z) : (recHwSpec X Z HPos M).Port → Prop
  | .inl (.inr c) => ProgOf W c
  | _ => True

variable (M) in
/-- **The calls stay inside `W`**: a called program port programs a cell of `W` with its value, and
the presented operator vanishes on the states with a hardwired cell outside `W`. -/
def hwSupp (m₀ : Finset HPos × M) (W : Hw X Z) (i : (recHwSpec X Z HPos M).Port) (E : QReg)
    (σ : Matrix (((recHwSpec X Z HPos M).In i × (runtimeR (X := X) (Z := Z) m₀).D) × E)
      (((recHwSpec X Z HPos M).In i × (runtimeR (X := X) (Z := Z) m₀).D) × E) ℂ) : Prop :=
  PortIn M W i ∧ ∀ a, ¬Quantum.Sponge.HwLe a.1.2.2.1 W → σ a a = 0

/-- An operator supported inside `W` presents, at a call, no diagonal mass outside `W`. -/
theorem relabel_diag_eq_zero_hw (m₀ : Finset HPos × M) {W : Hw X Z} {A : QReg}
    {i : (recHwSpec X Z HPos M).Port} (E : QReg) (ℓ : A ≃ (recHwSpec X Z HPos M).In i × E)
    {ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ}
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2)
      {s : HwReg X Z (Finset HPos × M) | Quantum.Sponge.HwLe s.2.1 W} ρ)
    (a : ((recHwSpec X Z HPos M).In i × (runtimeR m₀).D) × E)
    (ha : ¬Quantum.Sponge.HwLe a.1.2.2.1 W) :
    (SubInstrument.relabel (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D)).branch () ρ a a =
      0 := by
  by_contra h
  have h₁ := (hρ.branch_relabel (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D)).imp
    (q' := fun m : ((recHwSpec X Z HPos M).In i × (runtimeR m₀).D) × E ↦ m.1.2)
    (S' := {s : HwReg X Z (Finset HPos × M) | Quantum.Sponge.HwLe s.2.1 W}) fun m hm ↦ by
      obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D).surjective m
      rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm
  exact ha (h₁ a a h).1

/-- One call of a realized program staying inside `W`. -/
theorem forallQueries_queryBind_of_stepHw (m₀ : Finset HPos × M) (I : Λ.Interp) (W : Hw X Z)
    {A : QReg} (i : (recHwSpec X Z HPos M).Port) (E : QReg)
    (ℓ : A ≃ (recHwSpec X Z HPos M).In i × E)
    (k' : (recHwSpec X Z HPos M).Result i → QuantumComp Λ (recHwSpec X Z HPos M) Ω
      (QReg.of ((recHwSpec X Z HPos M).Out i × E)))
    (hpre : PortIn M W i) (hstep : StepHw m₀ W i)
    (hk : ∀ r ρ', QuerySupportedOn (fun m : QReg.of ((recHwSpec X Z HPos M).Out i × E) ×
        (runtimeR m₀).D ↦ m.2) {s : HwReg X Z (Finset HPos × M) | Quantum.Sponge.HwLe s.2.1 W}
          ρ' →
      (runtimeR m₀).ForallQueries I (hwSupp M m₀ W) (k' r) ρ')
    (ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ)
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2)
      {s : HwReg X Z (Finset HPos × M) | Quantum.Sponge.HwLe s.2.1 W} ρ) :
    (runtimeR m₀).ForallQueries I (hwSupp M m₀ W) (QuantumComp.queryBind i E ℓ k') ρ :=
  ⟨⟨hpre, fun a ha ↦ relabel_diag_eq_zero_hw m₀ E ℓ hρ a ha⟩, fun r ↦
    hk r _ (Hybrid.querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s) i r (hstep r) E ℓ hρ)⟩

variable (M) in
/-- The condition of `ProgsIn` on a command: a program port programs a cell of `W` with its
value. -/
def CmdIn (W : Hw X Z) (v : HPos → Digest) {A : QReg} : QuantumComp.Cmd Λ (XSpec M) A → Prop
  | .query (.inl (.inr p)) _ _ => ProgOf W (p.1.realize v)
  | _ => True

/-- **A template programming only cells of `W` with their values**, realized at `v`. -/
def ProgsIn (W : Hw X Z) (v : HPos → Digest) :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor Λ (XSpec M)) Ω A → Prop
  | _, .pure _ => True
  | _, .liftBind c next => CmdIn M W v c ∧ ∀ b, ProgsIn W v (next b)

variable (W : Hw X Z) (v : HPos → Digest)

omit [Fintype M] [DecidableEq M] in
theorem progsIn_cast {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor Λ (XSpec M)) Ω A) :
    ProgsIn W v (e ▸ y) ↔ ProgsIn W v y := by
  subst e
  rfl

omit [Fintype M] [DecidableEq M] in
theorem progsIn_bind {A : QReg} {Y : QReg → Type w₁}
    (x : IFreeM (QuantumComp.toIPFunctor Λ (XSpec M)) Ω A)
    (g : ∀ u, Ω u → IFreeM (QuantumComp.toIPFunctor Λ (XSpec M)) Y u)
    (hx : ProgsIn W v x) (hg : ∀ u a, ProgsIn W v (g u a)) : ProgsIn W v (x.bind g) := by
  induction x using IFreeM.inductionOn with
  | pure _ a => exact hg _ a
  | liftBind _ c next ih => exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩

omit [Fintype M] [DecidableEq M] in
theorem progsIn₂_bind {A B B' : QReg} {α : Type w} {β : Type w₁}
    (x : QuantumComp₂ Λ (XSpec M) A B α) (g : α → QuantumComp₂ Λ (XSpec M) B B' β)
    (hx : ProgsIn W v x) (hg : ∀ a, ProgsIn W v (g a)) : ProgsIn W v (x.bind g) := by
  refine progsIn_bind W v x _ hx fun u p ↦ ?_
  obtain ⟨e, a⟩ := p
  subst e
  exact hg a

omit [Fintype M] [DecidableEq M] in
theorem progsIn_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor Λ spec)
      (QuantumComp.toIPFunctor Λ (XSpec M)))
    (hσ : ∀ A c, ProgsIn W v (σ A c)) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor Λ spec) Ω A) : ProgsIn W v (x.substitute σ) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => trivial
  | liftBind s c next ih =>
    rw [IFreeM.substitute_liftBind]
    exact progsIn_bind W v _ _ (hσ s c) fun u ans ↦ (progsIn_cast W v ans.2 _).mpr (ih ans.1)

omit [Fintype M] [DecidableEq M] in
/-- Runtime 1's programs call no program port. -/
theorem progsIn_readLift {A : QReg} (y : QuantumComp Λ (hwReadSpec X Z M) Ω A) :
    ProgsIn W v (readLift goodAll y) := by
  induction y using IFreeM.inductionOn with
  | pure _ _ => trivial
  | liftBind _ c next ih =>
    show ProgsIn W v (IFreeM.mapLens (readLens goodAll) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · refine ⟨trivial, fun b ↦ ?_⟩
      dsimp only
      exact ih _
    · refine ⟨trivial, fun b ↦ ?_⟩
      dsimp only
      exact ih _
    · refine ⟨trivial, fun b ↦ ?_⟩
      dsimp only
      exact ih _

omit [Fintype M] [DecidableEq M] in
theorem progsIn_act {A B : QReg} {α : Type} (p : SubInstrument A B α) :
    ProgsIn W v (QComp.act (spec := XSpec M) p) :=
  ⟨trivial, fun _ ↦ trivial⟩

omit [Fintype M] [DecidableEq M] in
theorem progsIn_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (XSpec M) B B' α)
    (hk : ∀ r, ProgsIn W v (k r)) : ProgsIn W v (revealThen goodAll T k) :=
  ⟨trivial, fun r ↦ progsIn₂_bind W v _ _ (progsIn_act W v _) fun _ ↦ hk r.down⟩

omit [Fintype M] [DecidableEq M] in
theorem progsIn_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (XSpec M) B B' α) (hpW : ProgOf W (p.realize v)) (hk : ProgsIn W v k) :
    ProgsIn W v (progThen p hp k) :=
  ⟨hpW, fun _ ↦ progsIn₂_bind W v _ _ (progsIn_act W v _) fun _ ↦ hk⟩

omit [Fintype M] [DecidableEq M] in
theorem progsIn_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD))
    (h : ∀ p ∈ ps, ProgOf W (p.realize v)) : ProgsIn W v (progPorts M B ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact progsIn_progThen W v p trivial _ (h p List.mem_cons_self)
      (ih fun p' hp' ↦ h p' (List.mem_cons_of_mem _ hp'))

omit [Fintype M] [DecidableEq M] in
theorem progsIn_progSlots (pub : Pub) (B : QReg) (ss : List Slot)
    (h : ∀ s ∈ ss, ∀ p ∈ slotPorts pub s, ProgOf W (p.realize v)) :
    ProgsIn W v (progSlots M pub B ss) := by
  induction ss with
  | nil => trivial
  | cons s ss ih =>
    exact progsIn₂_bind W v _ _ (progsIn_progPorts W v B _ (h s List.mem_cons_self)) fun _ ↦
      ih fun s' hs' ↦ h s' (List.mem_cons_of_mem _ hs')

variable (upd : TrialUpd M) {pub : Pub} (hW : ProgsOf W pub v)
include hW

omit [Fintype M] [DecidableEq M] in
/-- **A layer signature of an in-table key programs cells of `W` with their values.** -/
theorem progsIn_signLayerT (B : QReg) (lab : RLabel) (he : lab.key.val < keyCount lab.layer) :
    ProgsIn W v (signLayerT M upd pub B lab) := by
  refine progsIn_revealThen W v _ _ fun _ ↦
    progsIn₂_bind W v _ _ (progsIn_readLift W v _) ?_
  rintro (_ | ⟨ρ, x⟩)
  · trivial
  · exact progsIn_revealThen W v _ _ fun _ ↦ progsIn₂_bind W v _ _
      (progsIn_progSlots W v pub B _ (hW lab.layer lab.key x he)) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem progsIn_signT (B : QReg) (r : SigningRequest) : ProgsIn W v (signT M upd pub B r) := by
  refine progsIn₂_bind W v _ _ (progsIn_signLayerT W v upd hW B (botLabel r)
    (keyIndexOnLayer_lt r.leafIndex bottomLayer)) ?_
  rintro (_ | ⟨bottom, f⟩)
  · trivial
  · refine progsIn₂_bind W v _ _ (progsIn_signLayerT W v upd hW B (topLabel r _)
      (keyIndexOnLayer_lt r.leafIndex topLayer)) ?_
    rintro (_ | ⟨top, _⟩) <;> trivial

omit [Fintype M] [DecidableEq M] in
theorem progsIn_challengeT (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (advSpec (X × Z)) A) :
    ProgsIn W v (challengeT M upd pub A c) := by
  rcases c with o | ⟨p | r, E, ℓ⟩
  · exact progsIn_readLift W v _
  · exact progsIn_readLift W v _
  · exact progsIn_bind W v _ _ (progsIn₂_bind W v _ _ (progsIn_act W v _) fun _ ↦
      progsIn_signT W v upd hW _ r) fun _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- **The game programs only cells of `W` with their values** (given `ProgsOf W pub v`). -/
theorem progsIn_gameT (A : Adversary (X × Z)) : ProgsIn W v (gameT M upd pub A) :=
  progsIn_revealThen W v _ _ fun _ ↦
    progsIn₂_bind W v _ _ (progsIn_substitute W v _ (progsIn_challengeT W v upd hW) _) fun _ ↦
      progsIn₂_bind W v _ _ (progsIn_readLift W v _) fun _ ↦ trivial

omit hW

/-- **The realized program of a template programming only cells of `W` presents, at every call,
only states whose hardwired cells lie in `W`**, from such a state. -/
theorem forallQueries_of_progsIn (m₀ : Finset HPos × M) (I : Λ.Interp) {A : QReg}
    (y : QuantumComp Λ (XSpec M) Ω A) :
    ProgsIn W v y → ∀ ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ,
      QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2)
        {s : HwReg X Z (Finset HPos × M) | Quantum.Sponge.HwLe s.2.1 W} ρ →
      (runtimeR m₀).ForallQueries I (hwSupp M m₀ W) (realizeT v y) ρ := by
  induction y using QuantumComp.inductionOn with
  | pure _ _ => intro _ _ _; trivial
  | primBind _ o k ih =>
    intro hy ρ hρ b
    exact ih b (hy.2 (ULift.up b)) _ (QuerySupportedOn.amplify_snd (q := fun s ↦ s) hρ _)
  | queryBind _ i E ℓ k ih =>
    intro hy ρ hρ
    rcases i with ((i | c) | ⟨p, hp⟩) | T
    · exact forallQueries_queryBind_of_stepHw m₀ I W (.inl (.inl (.inl i))) E ℓ
        (fun r ↦ realizeT v (k r)) trivial (stepHw_sponge m₀ W i)
        (fun r ↦ ih r (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepHw m₀ I W (.inl (.inl (.inr c.1))) E ℓ
        (fun r ↦ realizeT v (k r)) trivial (stepHw_read m₀ W c)
        (fun r ↦ ih r (hy.2 (ULift.up r))) ρ hρ
    · cases p with
      | programH T₀ c =>
        exact forallQueries_queryBind_of_stepHw m₀ I W
          (.inl (.inr ((LazyProg.programH T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r))
          hy.1 (stepHw_prog m₀ hy.1) (fun r ↦ ih r (hy.2 (ULift.up r))) ρ hρ
      | programK T₀ c =>
        exact forallQueries_queryBind_of_stepHw m₀ I W
          (.inl (.inr ((LazyProg.programK T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r))
          hy.1 (stepHw_prog m₀ hy.1) (fun r ↦ ih r (hy.2 (ULift.up r))) ρ hρ
      | programK' T₀ c =>
        exact forallQueries_queryBind_of_stepHw m₀ I W
          (.inl (.inr ((LazyProg.programK' T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r))
          hy.1 (stepHw_prog m₀ hy.1) (fun r ↦ ih r (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepHw m₀ I W (.inr T) E ℓ
        (fun m ↦ realizeT v (k (restrictTo T v, m))) trivial (stepHw_rec m₀ W T)
        (fun m ↦ ih (restrictTo T v, m) (hy.2 (ULift.up (restrictTo T v, m)))) ρ hρ

end hwLe

/-- The initial state has no hardwired cell. -/
theorem querySupportedOn_initR_hw (W : Hw X Z) :
    QuerySupportedOn (fun m : QReg.of Unit × (runtimeR (X := X) (Z := Z) m0R).D ↦ m.2)
      {s : HwReg X Z Mem | Quantum.Sponge.HwLe s.2.1 W} initR := by
  intro m m' hm
  change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty X Z, m0R) : HwReg X Z Mem)).matrix) m m' ≠ 0 at hm
  simp only [SubState.matrix_basis] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · show Quantum.Sponge.HwLe m.2.2.1 W ∧ Quantum.Sponge.HwLe m'.2.2.1 W
    rw [← he.1, ← he.2]
    exact ⟨spongeHwLe_hwEmpty W, spongeHwLe_hwEmpty W⟩
  · exact absurd rfl h

/-- **Along the game at `L`, the hardwired cells stay inside `tableHw L`**, and every program port
called programs a cell of `tableHw L` with its value (GameT's `progsOf_tableHw`). -/
theorem forallQueries_hwSupp_gameR (A : Adversary (X × Z)) (L : HonestTable) :
    (runtimeR m0R).ForallQueries .instruments (hwSupp Selections m0R (tableHw L)) (gameR A L)
      initR :=
  forallQueries_of_progsIn (tableHw L) (valueAt L) m0R .instruments _
    (progsIn_gameT (tableHw L) (valueAt L) cwUpd (progsOf_tableHw L) A) initR
    (querySupportedOn_initR_hw (tableHw L))

/-! ## Only the free `h` cells remain -/

section freeH

/-- Two conditions on the presented operators hold together. -/
theorem forallQueries_and {spec : QuantumOracleSpec.{u₁, v₁}} {R : QuantumRuntime spec}
    {Λ : LocalSig.{u, v}} {I : Λ.Interp} {Ω : QReg → Type w} {A : QReg}
    {P P' : ∀ (i : spec.Port) (E : QReg),
      Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ → Prop}
    {x : QuantumComp Λ spec Ω A} {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (h : R.ForallQueries I P x ρ) (h' : R.ForallQueries I P' x ρ) :
    R.ForallQueries I (fun i E σ ↦ P i E σ ∧ P' i E σ) x ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => trivial
  | primBind _ o k ih => exact fun b ↦ ih b (h b) (h' b)
  | queryBind _ i E ℓ k ih => exact ⟨⟨h.1, h'.1⟩, fun r ↦ ih r (h.2 r) (h'.2 r)⟩

/-- An `h` port with its cell free must be safe; every other port is free. -/
def FreeHSafe (L : HonestTable) : (recHwSpec X Z HPos Selections).Port → HwReg X Z Mem → Prop
  | .inl (.inr (.programH z v)), s => s.2.1.1 z = none → ProgSafe L (.programH z v) s
  | _, _ => True

/-- **The free `h` calls are presented safe states.** -/
def hFreeSupp (L : HonestTable) (i : (recHwSpec X Z HPos Selections).Port) (E : QReg)
    (σ : Matrix (((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) × E)
      (((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) × E) ℂ) :
    Prop :=
  ∀ a, ¬FreeHSafe L i a.1.2 → σ a a = 0

/-- Inside `tableHw L`, the `k`, `k'` ports and the hardwired `h` ports are safe: only the free
`h` ports remain. -/
theorem safeSupp_of_hwSupp (L : HonestTable) (i : (recHwSpec X Z HPos Selections).Port)
    (E : QReg)
    (σ : Matrix (((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) × E)
      (((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) × E) ℂ)
    (hw : hwSupp Selections m0R (tableHw L) i E σ) (hh : hFreeSupp L i E σ) :
    safeSupp L i E σ := by
  intro a ha
  by_contra hne
  have hle : Quantum.Sponge.HwLe a.1.2.2.1 (tableHw L) := by
    by_contra hn
    exact hne (hw.2 a hn)
  rcases i with ((p | c) | c) | T
  · exact ha trivial
  · exact ha trivial
  · have hc : ProgOf (tableHw L) c := hw.1
    cases c with
    | programH z v =>
      by_cases hz : a.1.2.2.1.1 z = none
      · by_contra hn'
        exact hne (hh a fun hf ↦ ha (hf hz))
      · exact ha (progSafe_of_le_of_hardwired L hle hc hz)
    | programK x v => exact ha (progSafe_programK_of_le L hle hc)
    | programK' x v => exact ha (progSafe_programK'_of_le L hle hc)
  · exact ha trivial

/-- **`hsafe` from the free `h` calls**: along the game, if every free `h` call is presented safe
states, every call is (`forallQueries_hwSupp_gameR` for the rest). -/
theorem forallQueries_safeSupp_gameR (A : Adversary (X × Z)) (L : HonestTable)
    (hh : (runtimeR m0R).ForallQueries .instruments (hFreeSupp L) (gameR A L) initR) :
    (runtimeR m0R).ForallQueries .instruments (safeSupp L) (gameR A L) initR :=
  (forallQueries_and (forallQueries_hwSupp_gameR A L) hh).mono _ fun i E σ h ↦
    safeSupp_of_hwSupp L i E σ h.1 h.2

/-- **The averaged program flips, from the free `h` calls**: `uavg_progTot_le` with `hsafe` reduced
to the free `h` program calls. -/
theorem uavg_progTot_le_of_hFree {q : ℕ} {A : Adversary (X × Z)}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
    (Gd : HonestTable → Prop) [DecidablePred Gd]
    (hh : ∀ L, PermGood L.perm 18 → Gd L →
      (runtimeR m0R).ForallQueries .instruments (hFreeSupp L) (gameR A L) initR)
    {κ : ℝ≥0∞} (hk : uavg (fun L ↦ if PermGood L.perm 18 ∧ Gd L then kTot A L else 0) ≤ κ) :
    uavg (fun L ↦ if PermGood L.perm 18 then progTot A L else 0) ≤
      κ + progCap * uavg (fun L ↦ if PermGood L.perm 18 ∧ ¬Gd L then (1 : ℝ≥0∞) else 0) :=
  uavg_progTot_le hperm hsign Gd (fun L hπ hg ↦ forallQueries_safeSupp_gameR A L (hh L hπ hg)) hk

end freeH

/-! ## The head-tail of a round of an evaluation -/

section headTail

variable {X₁ Z₁ : Type} [AddCommGroup X₁] [AddCommGroup Z₁] (π : Equiv.Perm (X₁ × Z₁))
  (h : Z₁ → X₁) (k k' : X₁ → Z₁)

/-- **A round of a sponge evaluation is a head-tail.** If `D` holds the `k`, `k'` points of rounds
`0, …, j` of absorbing `m`, the tail of the first `j + 1` blocks heads to the capacity
`zi + k' xi` after round `j`, with rate `xi`, where `(xi, zi) = π (xp, zp + k xp)`, `zp` the
capacity and `xp` the rate plus block before round `j`. -/
theorem isHeadTail_take_succ {D : Dbs X₁ Z₁} {m : List X₁} {j : ℕ} (hj : j < m.length)
    (hD : AgreesRounds π h k k' D (m.take (j + 1))) :
    IsHeadTail π D (absorbTail (spongePerm (h, k, k') π) (m.take (j + 1)))
      ((π ((absorb (spongePerm (h, k, k') π) (m.take j)).1 + m[j],
          (absorb (spongePerm (h, k, k') π) (m.take j)).2 +
            k ((absorb (spongePerm (h, k, k') π) (m.take j)).1 + m[j]))).2 +
        k' (π ((absorb (spongePerm (h, k, k') π) (m.take j)).1 + m[j],
          (absorb (spongePerm (h, k, k') π) (m.take j)).2 +
            k ((absorb (spongePerm (h, k, k') π) (m.take j)).1 + m[j]))).1)
      (π ((absorb (spongePerm (h, k, k') π) (m.take j)).1 + m[j],
        (absorb (spongePerm (h, k, k') π) (m.take j)).2 +
          k ((absorb (spongePerm (h, k, k') π) (m.take j)).1 + m[j]))).1 := by
  have hm : m.take (j + 1) = m.take j ++ [m[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
  rw [hm] at hD ⊢
  have hr := hD (m.take j).length (by rw [List.length_append, List.length_singleton]; omega)
  simp only [List.take_left', List.getElem_append_right (le_refl _), Nat.sub_self,
    List.getElem_cons_zero] at hr
  rw [absorbTail_append_singleton]
  exact ⟨_, _, _, _, _, _, rfl, isTail_absorbTail π h k k' hD.of_append, hr.1, rfl, hr.2, rfl⟩

end headTail

/-- **The cell of round `j` of a slot's honest path is a head-tail**: with the `k`, `k'` points of
rounds `0, …, j` of the slot's input under the public keys held by `D`, the tail of its first
`j + 1` blocks heads to `roundH`'s cell, with the rate after `π`. -/
theorem isHeadTail_roundH (pub : Pub) (s : Slot) (f : ValPos → Digest) {D : Dbs X Z} {j : ℕ}
    (hj : j < (blocks (slotInput pub s f)).length)
    (hD : AgreesRounds pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 D
      ((blocks (slotInput pub s f)).take (j + 1))) :
    IsHeadTail pub.perm D (absorbTail (spongePerm pub.keys pub.perm)
        ((blocks (slotInput pub s f)).take (j + 1))) (roundH pub s f j).1
      (midAt pub (stateAt pub (blocks (slotInput pub s f)) j)
        ((blocks (slotInput pub s f)).getD j 0)).1 := by
  have hg : (blocks (slotInput pub s f)).getD j 0 = (blocks (slotInput pub s f))[j] :=
    List.getD_eq_getElem _ _ hj
  have h := isHeadTail_take_succ pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 hj hD
  unfold roundH
  dsimp only
  rw [hg]
  split_ifs <;> exact h

end Quantum.Xmss.Assembly

end
