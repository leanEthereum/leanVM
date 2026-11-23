module

public import Quantum.Sphincs.Assembly.GameTCalls
public import Quantum.Xmss.Assembly.Masses
public import Quantum.Xmss.FlipCost

@[expose] public section

/-!
# The program flips along leanSPHINCS's template game

The program ports' flip costs of the event `Bad (evData pub v) N` (contract C3) along the realized
template game, as leanXMSS's `Quantum.Xmss.Assembly.ProgView`. A program port `c` moves a register
state `s` by FlipCost's `progMap c` (the cell discarded from the databases and hardwired); its flip
cost `progFlip B c` is the weight of the states outside the event `B` that it moves into `B`
(`flipCost_prog_le`). Unlike leanXMSS, the template's last-round `h` values are corrected to hidden
values (`cor128`, `cor256`), so no fixed table holds every programmed `h` value: a port may
reprogram an `h` cell with another value, and the facts below allow it.

* **Reprogramming an `h` cell** (`not_mem_hwTargetBad_setH`, `not_mem_bad_setH`): whatever the
  cell held, the programmed state is outside the event if the exempted slots stay exempted and, in
  a good union, the head-tails of the cell have no Struct, Enc or coverage target once it is
  programmed. The coverage exemption only grows (`covEx_subset_setH`). A cell holding the port's
  value flips nothing (`progMap_mem_bad_iff_of_held`, from `mem_bad_congr_union`).
* **Safe states** (`kFlipSet`, `ProgSafe`, `PortSafe`, `safeSupp`): a port is safe at a state if
  it flips the state only as a `k`, `k'` port with its cell free. A `k`, `k'` port whose hardwired
  cell holds its value is safe (`progSafe_programK`, `progSafe_programK'`). On safe states the flip
  cost is at most the flip mass `kFlip B c` of the fresh `k`, `k'` cell (`progFlip_le_kFlip`); along
  a program whose calls are presented safe states, the summed program flips `progW` are at most the
  summed fresh `k`, `k'` flips `kW` (`progW_le_kW`, from `totalWeight_le_of_forallQueries`).
* **Fresh `k`, `k'` flips averaged over the programmed value** (`card_kFlip_programK_le`,
  `sum_kFlip_programK_le`, `uavg_kFlip_programK_le` and their `k'` forms): for `PermGood π 18` and
  `N + dbGrade D ≤ 2^68`, twice the capacity-scale counts of Events' `card_flip_programK_bad_le`,
  at most `2^-301` per unit of trace.

The run facts (every program call of the game is presented safe states) are in
`Quantum.Sphincs.Assembly.ProgSafe`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

universe u v w u₁ v₁

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (diagMass totalWeight_le_totalWeight)
open Quantum.Xmss.Assembly (recHwSpec runtimeR extWeight totalWeight_congr_of_forallQueries
  traceRight_diag_eq_zero)

namespace Quantum.Sphincs.Assembly

/-! ## Weights bounded on the presented operators (leanXMSS's ProgView) -/

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
          (fun i E σ hσ ↦ (ite_eq_left (hP i E σ hσ)).symm) x ρ hx
    _ ≤ R.totalWeight I w' x ρ :=
        totalWeight_le_totalWeight R I (fun i σ hσ ↦ by
          split_ifs with h
          · exact hw i σ hσ h
          · exact le_rfl) x hρ

/-- Two conditions on the presented operators hold together. -/
theorem forallQueries_and {P P' : ∀ (i : spec.Port) (E : QReg),
      Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ → Prop}
    {x : QuantumComp Λ spec Ω A} {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (h : R.ForallQueries I P x ρ) (h' : R.ForallQueries I P' x ρ) :
    R.ForallQueries I (fun i E σ ↦ P i E σ ∧ P' i E σ) x ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => trivial
  | primBind _ o k ih => exact fun b ↦ ih b (h b) (h' b)
  | queryBind _ i E ℓ k ih => exact ⟨⟨h.1, h'.1⟩, fun r ↦ ih r (h.2 r) (h'.2 r)⟩

end forallQueries

/-! ## Reprogramming an `h` cell -/

section setH

/-- Setting a cell of a database does not lower its size. -/
theorem size_le_update_some {α β : Type} [Fintype α] [DecidableEq α] (d : Database α β) (a : α)
    (b : β) : d.size ≤ Database.size (Function.update d a (some b)) := by
  unfold Database.size
  refine Finset.card_le_card fun x hx ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  by_cases h : x = a
  · subst h
    simp
  · rwa [Function.update_of_ne h]

variable {X₁ Z₁ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
  [AddCommGroup X₁] [AddCommGroup Z₁]

omit [DecidableEq X₁] [AddCommGroup X₁] [AddCommGroup Z₁] in
/-- Programming an `h` cell does not lower the grade. -/
theorem dbGrade_le_setH (W : Hw X₁ Z₁) (z : Z₁) (a : X₁) :
    dbGrade W ≤ dbGrade (Function.update W.1 z (some a), W.2) :=
  max_le_max (size_le_update_some W.1 z a) le_rfl

variable {Y M : Type} {π : Equiv.Perm (X₁ × Z₁)} {out : X₁ → Y}
  {tgt : Hw X₁ Z₁ → M → List X₁ → Option Y} {N : ℕ}

omit [DecidableEq X₁] in
/-- **Programming an `h` cell, hardwired or not**: the programmed state is outside a target event
if, in a good union, the targets after the program are targets before, and the head-tails of the
cell have no target after the program. `h` never changes goodness. -/
theorem not_mem_hwTargetBad_setH {D : DbReg X₁ Z₁} {W : Hw X₁ Z₁} {m : M}
    (hs : (D, W, m) ∉ HwTargetBad π out tgt N) (z : Z₁) (a : X₁)
    (htgt : Good π (union W D) → ∀ t y,
      tgt (Function.update W.1 z (some a), W.2) m t = some y → tgt W m t = some y)
    (hhead : Good π (union W D) → ∀ t xi, IsHeadTail π (union W D) t z xi →
      tgt (Function.update W.1 z (some a), W.2) m t = none) :
    ((Function.update D.1 z none, D.2), (Function.update W.1 z (some a), W.2), m) ∉
      HwTargetBad π out tgt N := by
  rintro ⟨hN', h2⟩
  have hN : dbGrade W ≤ N := (dbGrade_le_setH W z a).trans hN'
  have hU := union_not_mem_of_not_mem_hwTargetBad hs hN
  have hG := (not_mem_targetBad_iff.1 hU).1
  have hU0 : ({ union W D with h := Function.update (union W D).h z none } : Dbs X₁ Z₁) ∉
      TargetBad π out (tgt W m) :=
    fun h ↦ hU (TargetBad.mono (extendsAll_eraseH _ z) h)
  have h2' : union (Function.update W.1 z (some a), W.2) (Function.update D.1 z none, D.2) ∈
      TargetBad π out (tgt (Function.update W.1 z (some a), W.2) m) := h2
  rw [union_programH] at h2'
  exact not_mem_targetBad_fillH (Q := fun _ _ ↦ False) (by simp) hU0
    (fun t y ht ↦ .inl (htgt hG t y ht)) (fun _ _ h ↦ h.elim)
    (fun t xi hi ↦ hhead hG t xi (hi.mono (extendsAll_eraseH _ z).1)) (some a) h2'

end setH

/-! ## The event under program ports -/

section bad

variable {d : EvData} {N : ℕ}

/-- **The event reads the databases only through the union.** -/
theorem mem_bad_congr_union {D D' : DbReg X Z} {W : Hw X Z} {m : Mem HPos}
    (h : union W D = union W D') : (D, W, m) ∈ Bad d N ↔ (D', W, m) ∈ Bad d N := by
  constructor
  · rintro (⟨hN, hU⟩ | ⟨hN, hU⟩)
    · refine .inl ⟨hN, ?_⟩
      show union W D' ∈ _
      rw [← h]
      exact hU
    · refine .inr ⟨hN, ?_⟩
      show union W D' ∈ _
      rw [← h]
      exact hU
  · rintro (⟨hN, hU⟩ | ⟨hN, hU⟩)
    · refine .inl ⟨hN, ?_⟩
      show union W D ∈ _
      rw [h]
      exact hU
    · refine .inr ⟨hN, ?_⟩
      show union W D ∈ _
      rw [h]
      exact hU

/-- **Reprogramming a cell with the value it holds keeps the event**: the hardwired cells stay and
shadow the discarded database cell. -/
theorem progMap_mem_bad_iff_of_held (c : HwProg X Z) (s : HwReg X Z (Mem HPos))
    (h : CellHeld c s.2.1) : progMap c s ∈ Bad d N ↔ s ∈ Bad d N := by
  obtain ⟨⟨dh, dk, dk'⟩, ⟨wh, wk, wk'⟩, m⟩ := s
  cases c with
  | programH z a =>
    have h' : wh z = some a := h
    have hw : Function.update wh z (some a) = wh := Function.update_eq_self_iff.mpr h'.symm
    show ((Function.update dh z none, dk, dk'), (Function.update wh z (some a), wk, wk'), m) ∈
        Bad d N ↔ ((dh, dk, dk'), (wh, wk, wk'), m) ∈ Bad d N
    rw [hw]
    exact mem_bad_congr_union (union_updateH_of_hw (wh, wk, wk') h' dh dk dk' none)
  | programK x a =>
    have h' : wk x = some a := h
    have hw : Function.update wk x (some a) = wk := Function.update_eq_self_iff.mpr h'.symm
    show ((dh, Function.update dk x none, dk'), (wh, Function.update wk x (some a), wk'), m) ∈
        Bad d N ↔ ((dh, dk, dk'), (wh, wk, wk'), m) ∈ Bad d N
    rw [hw]
    exact mem_bad_congr_union (union_updateK_of_hw (wh, wk, wk') h' dh dk dk' none)
  | programK' x a =>
    have h' : wk' x = some a := h
    have hw : Function.update wk' x (some a) = wk' := Function.update_eq_self_iff.mpr h'.symm
    show ((dh, dk, Function.update dk' x none), (wh, wk, Function.update wk' x (some a)), m) ∈
        Bad d N ↔ ((dh, dk, dk'), (wh, wk, wk'), m) ∈ Bad d N
    rw [hw]
    exact mem_bad_congr_union (union_updateK'_of_hw (wh, wk, wk') h' dh dk dk' none)

/-- **Programming an `h` cell keeps every coverage exemption**: the `k`, `k'` cells stay and the
cell stays hardwired. -/
theorem covEx_subset_setH (d : EvData) (W : Hw X Z) (z : Z) (a : X) :
    d.covEx W ⊆ d.covEx (Function.update W.1 z (some a), W.2) := by
  rintro p ⟨z', xi, w, hi, hw⟩
  have hz : Function.update W.1 z (some a) z = some a := Function.update_self _ _ _
  have hne : ∀ z'', z'' ≠ z → Function.update W.1 z (some a) z'' = W.1 z'' :=
    fun _ h ↦ Function.update_of_ne h _ _
  generalize Function.update W.1 z (some a) = h₁ at hz hne ⊢
  have hE : Extends (DbReg.toDbs (h₁, W.2)) W.toDbs := ⟨fun _ _ h ↦ h, fun _ _ h ↦ h⟩
  by_cases e : z' = z
  · subst e
    exact ⟨z', xi, a, hi.mono hE, hz⟩
  · exact ⟨z', xi, w, hi.mono hE, (hne z' e).trans hw⟩

/-- **Programming an `h` cell, hardwired or not, flips nothing** if the exempted structural slots
stay exempted and, in a good union, the head-tails of the cell have no Struct, Enc or coverage
target once it is programmed. -/
theorem not_mem_bad_setH {D : DbReg X Z} {W : Hw X Z} {m : Mem HPos} (hs : (D, W, m) ∉ Bad d N)
    (z : Z) (a : X)
    (hEx : Good d.perm (union W D) → d.exS W ⊆ d.exS (Function.update W.1 z (some a), W.2))
    (hhead : Good d.perm (union W D) → ∀ t xi, IsHeadTail d.perm (union W D) t z xi →
      d.sphTgt (d.exS (Function.update W.1 z (some a), W.2)) m.2 t = none ∧
        covTgt d.pk (d.covEx (Function.update W.1 z (some a), W.2)) t = none) :
    ((Function.update D.1 z none, D.2), (Function.update W.1 z (some a), W.2), m) ∉ Bad d N := by
  rintro (h | h)
  · exact not_mem_hwTargetBad_setH (tgt := d.sphTgtHw) (fun h ↦ hs (.inl h)) z a
      (fun hG _ _ ht ↦ sphTgt_mono (hEx hG) ht) (fun hG t xi hi ↦ (hhead hG t xi hi).1) h
  · exact not_mem_hwTargetBad_setH (tgt := fun W (_ : Mem HPos) ↦ covTgt d.pk (d.covEx W))
      (fun h ↦ hs (.inr h)) z a (fun _ _ _ ht ↦ covTgt_mono (covEx_subset_setH d W z a) ht)
      (fun hG t xi hi ↦ (hhead hG t xi hi).2) h

end bad

/-! ## Safe states and the fresh `k`, `k'` flips -/

section safe

variable {M : Type} [Fintype M] [DecidableEq M] (B : Set (HwReg X Z (Finset HPos × M)))

/-- **The states a `k`, `k'` port flips with its cell free**: outside `B`, the cell not hardwired,
moved into `B`. An `h` port has none. -/
def kFlipSet : HwProg X Z → Set (HwReg X Z (Finset HPos × M))
  | .programH _ _ => ∅
  | .programK x a => {s | s ∉ B ∧ s.2.1.2.1 x = none ∧ progMap (.programK x a) s ∈ B}
  | .programK' x a => {s | s ∉ B ∧ s.2.1.2.2 x = none ∧ progMap (.programK' x a) s ∈ B}

/-- **A port is safe at a state** if it flips the state only as a `k`, `k'` port with its cell
free. -/
def ProgSafe (c : HwProg X Z) (s : HwReg X Z (Finset HPos × M)) : Prop :=
  s ∉ B → progMap c s ∈ B → s ∈ kFlipSet B c

/-- Only the program ports are constrained: a program port must be safe at the state. -/
def PortSafe : (recHwSpec X Z HPos M).Port → HwReg X Z (Finset HPos × M) → Prop
  | .inl (.inr c), s => ProgSafe B c s
  | _, _ => True

/-- **The calls are presented safe states**: the presented operator vanishes on the register states
where the port is not safe. -/
def safeSupp (m₀ : Finset HPos × M) (i : (recHwSpec X Z HPos M).Port) (E : QReg)
    (σ : Matrix (((recHwSpec X Z HPos M).In i × (runtimeR (X := X) (Z := Z) m₀).D) × E)
      (((recHwSpec X Z HPos M).In i × (runtimeR (X := X) (Z := Z) m₀).D) × E) ℂ) : Prop :=
  ∀ a, ¬PortSafe B i a.1.2 → σ a a = 0

variable [DecidablePred (· ∈ B)]

/-- **The flip mass of a port's fresh `k`, `k'` cell.** -/
noncomputable def kFlip (c : HwProg X Z)
    (σ : Matrix (Unit × HwReg X Z (Finset HPos × M)) (Unit × HwReg X Z (Finset HPos × M)) ℂ) :
    ℝ≥0∞ :=
  diagMass {q | q.2 ∈ kFlipSet B c} σ

/-- **The flip cost of a program port**, relative to the projector `0`. -/
noncomputable def progFlip (c : HwProg X Z)
    (σ : Matrix (Unit × HwReg X Z (Finset HPos × M)) (Unit × HwReg X Z (Finset HPos × M)) ℂ) :
    ℝ≥0∞ :=
  flipCost B (hwProgKraus c) 0 σ

/-- **The program flips summed along a run** of `runtimeR` (the other ports cost `0`). -/
noncomputable def progW (m₀ : Finset HPos × M) {α : Type}
    (x : QComp (recHwSpec X Z HPos M) (QReg.of Unit) (QReg.of Unit) α)
    (ρ : Matrix (QReg.of Unit × (runtimeR (X := X) (Z := Z) m₀).D)
      (QReg.of Unit × (runtimeR (X := X) (Z := Z) m₀).D) ℂ) : ℝ≥0∞ :=
  (runtimeR m₀).totalWeight .instruments (extWeight (hwCost (fun _ _ ↦ 0) (progFlip B))) x ρ

/-- **The fresh `k`, `k'` flip masses summed along a run** of `runtimeR`. -/
noncomputable def kW (m₀ : Finset HPos × M) {α : Type}
    (x : QComp (recHwSpec X Z HPos M) (QReg.of Unit) (QReg.of Unit) α)
    (ρ : Matrix (QReg.of Unit × (runtimeR (X := X) (Z := Z) m₀).D)
      (QReg.of Unit × (runtimeR (X := X) (Z := Z) m₀).D) ℂ) : ℝ≥0∞ :=
  (runtimeR m₀).totalWeight .instruments (extWeight (hwCost (fun _ _ ↦ 0) (kFlip B))) x ρ

/-- **The flip cost of a port on the states where it is safe** is at most the flip mass of its
fresh `k`, `k'` cell. -/
theorem progFlip_le_kFlip (c : HwProg X Z)
    {σ : Matrix (Unit × HwReg X Z (Finset HPos × M)) (Unit × HwReg X Z (Finset HPos × M)) ℂ}
    (hσ : σ.PosSemidef) (hs : ∀ q, ¬ProgSafe B c q.2 → σ q q = 0) :
    progFlip B c σ ≤ kFlip B c σ := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  refine (flipCost_prog_le B c hσ).trans ?_
  rw [kFlip, diagMass, ENNReal.ofReal_sum_of_nonneg fun q _ ↦ by split_ifs <;> simp [hre q]]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  split_ifs with h
  · by_cases hq : σ q q = 0
    · simp [hq]
    · have hmem : q ∈ {q : Unit × HwReg X Z (Finset HPos × M) | q.2 ∈ kFlipSet B c} := by
        by_contra hn
        exact hq (hs q fun hsafe ↦ hn (hsafe h.1 h.2))
      rw [Set.indicator_of_mem hmem]
  · simp

/-- The flip cost of a port is at most the trace. -/
theorem progFlip_le_trace (c : HwProg X Z)
    {σ : Matrix (Unit × HwReg X Z (Finset HPos × M)) (Unit × HwReg X Z (Finset HPos × M)) ℂ}
    (hσ : σ.PosSemidef) : progFlip B c σ ≤ ENNReal.ofReal σ.trace.re := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  refine (flipCost_prog_le B c hσ).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [Matrix.trace, Complex.re_sum]
  exact Finset.sum_le_sum fun q _ ↦ by split_ifs <;> simp [hre q]

/-- **The program flips along a run are the fresh `k`, `k'` flips** when every call is presented
safe states. -/
theorem progW_le_kW (m₀ : Finset HPos × M) {α : Type}
    (x : QComp (recHwSpec X Z HPos M) (QReg.of Unit) (QReg.of Unit) α)
    {ρ : Matrix (QReg.of Unit × (runtimeR (X := X) (Z := Z) m₀).D)
      (QReg.of Unit × (runtimeR (X := X) (Z := Z) m₀).D) ℂ} (hρ : ρ.PosSemidef)
    (hsafe : (runtimeR m₀).ForallQueries .instruments (safeSupp B m₀) x ρ) :
    progW B m₀ x ρ ≤ kW B m₀ x ρ := by
  unfold progW kW
  refine totalWeight_le_of_forallQueries (runtimeR m₀) .instruments
    (fun i τ ↦ ∀ q, ¬PortSafe B i q.2 → τ q q = 0)
    (fun i E σ hσ q hq ↦ traceRight_diag_eq_zero fun e ↦ hσ (q, e) hq) (fun i τ hτ hok ↦ ?_)
    x hρ hsafe
  rcases i with ((p | c) | c) | T
  · show (0 : ℝ≥0∞) ≤ 0
    exact le_rfl
  · show (0 : ℝ≥0∞) ≤ 0
    exact le_rfl
  · exact progFlip_le_kFlip B c hτ hok
  · show (0 : ℝ≥0∞) ≤ 0
    exact le_rfl

end safe

/-! ## `k`, `k'` ports holding their value -/

section keys

variable {d : EvData} {N : ℕ}

/-- **A `k` port is safe** at a state whose hardwired `k` cell, if any, holds the port's value. -/
theorem progSafe_programK {x : X} {a : Z} {r : HwReg X Z (Mem HPos)}
    (hK : ∀ u, r.2.1.2.1 x = some u → u = a) : ProgSafe (Bad d N) (.programK x a) r := by
  by_cases hx : r.2.1.2.1 x = none
  · exact fun hs hp ↦ ⟨hs, hx, hp⟩
  · obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hx
    have hc : CellHeld (HwProg.programK x a) r.2.1 := by
      show r.2.1.2.1 x = some a
      rw [hu, hK u hu]
    exact fun hs hp ↦ absurd ((progMap_mem_bad_iff_of_held _ r hc).mp hp) hs

/-- **A `k'` port is safe** at a state whose hardwired `k'` cell, if any, holds the port's
value. -/
theorem progSafe_programK' {x : X} {a : Z} {r : HwReg X Z (Mem HPos)}
    (hK : ∀ u, r.2.1.2.2 x = some u → u = a) : ProgSafe (Bad d N) (.programK' x a) r := by
  by_cases hx : r.2.1.2.2 x = none
  · exact fun hs hp ↦ ⟨hs, hx, hp⟩
  · obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hx
    have hc : CellHeld (HwProg.programK' x a) r.2.1 := by
      show r.2.1.2.2 x = some a
      rw [hu, hK u hu]
    exact fun hs hp ↦ absurd ((progMap_mem_bad_iff_of_held _ r hc).mp hp) hs

end keys

/-! ## The fresh `k`, `k'` flips averaged over the programmed value -/

section avg

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

/-- A sum over the values of `Z` bounded by `C` times a weight with `C ≤ 2^211` averages to at
most `2^-301` times the weight. -/
theorem inv_card_Z_mul_le_of_le {C : ℕ} (hC : C ≤ 2 ^ 211) {a b : ℝ≥0∞} (h : a ≤ C * b) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * a ≤ (2 ^ 301)⁻¹ * b := by
  have hZ : Fintype.card Z = 2 ^ 512 := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hc : (C : ℝ≥0∞) ≤ 2 ^ 211 := by exact_mod_cast hC
  have hdiv : (C : ℝ≥0∞) / Fintype.card Z ≤ (2 ^ 301)⁻¹ := by
    rw [hZ, Nat.cast_pow, Nat.cast_ofNat]
    calc (C : ℝ≥0∞) / 2 ^ 512 ≤ 2 ^ 211 / 2 ^ 512 := by gcongr
      _ = (2 ^ 301)⁻¹ := by
          rw [show (2 : ℝ≥0∞) ^ 512 = 2 ^ 211 * 2 ^ 301 by rw [← pow_add], ENNReal.div_eq_inv_mul,
            ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), mul_comm ((2 : ℝ≥0∞) ^ 211)⁻¹,
            mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]
  calc (Fintype.card Z : ℝ≥0∞)⁻¹ * a ≤ (Fintype.card Z : ℝ≥0∞)⁻¹ * (C * b) := by gcongr
    _ = (C : ℝ≥0∞) / Fintype.card Z * b := by rw [ENNReal.div_eq_inv_mul, mul_assoc]
    _ ≤ (2 ^ 301)⁻¹ * b := by gcongr

variable {d : EvData} {N : ℕ}

open scoped Classical in
/-- **The fresh `k` flips at a state**: the values flipping it with its cell free are at most twice
the capacity-scale count of Events' `card_flip_programK_bad_le`. -/
theorem card_kFlip_programK_le {G T : ℕ} (hπ : PermGood d.perm G) (x : X)
    (s : HwReg X Z (Mem HPos)) (hT : s.2.1.2.1 x = none → N + dbGrade s.1 ≤ T) (t : Finset Z)
    (ht : ∀ a ∈ t, s ∈ kFlipSet (Bad d N) (.programK x a)) (a₀ : Z) (ha₀ : a₀ ∈ t) :
    t.card ≤ 2 * ((T + 1) * ((T + 1) * T + 2 * T) * G) := by
  obtain ⟨hs, hx, -⟩ := ht a₀ ha₀
  exact (Finset.card_le_card fun a ha ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _,
    (ht a ha).2.2⟩).trans
    (card_flip_programK_bad_le (D := s.1) (W := s.2.1) (m := s.2.2) hπ hs (hT hx) hx)

open scoped Classical in
/-- **The fresh `k'` flips at a state**: the values flipping it with its cell free are at most
twice the capacity-scale count of Events' `card_flip_programK'_bad_le`. -/
theorem card_kFlip_programK'_le {G T : ℕ} (hπ : PermGood d.perm G) (x : X)
    (s : HwReg X Z (Mem HPos)) (hT : s.2.1.2.2 x = none → N + dbGrade s.1 ≤ T) (t : Finset Z)
    (ht : ∀ a ∈ t, s ∈ kFlipSet (Bad d N) (.programK' x a)) (a₀ : Z) (ha₀ : a₀ ∈ t) :
    t.card ≤ 2 * ((T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T) := by
  obtain ⟨hs, hx, -⟩ := ht a₀ ha₀
  exact (Finset.card_le_card fun a ha ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _,
    (ht a ha).2.2⟩).trans
    (card_flip_programK'_bad_le (D := s.1) (W := s.2.1) (m := s.2.2) hπ hs (hT hx) hx)

/-- **The fresh `k` flips summed over the programmed value**: for `PermGood π G`, on states with
`N + dbGrade D ≤ T` where the cell is free, at most twice the capacity-scale count times the
trace. -/
theorem sum_kFlip_programK_le {G T : ℕ} (hπ : PermGood d.perm G) (x : X)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef)
    (hT : ∀ q, σ q q ≠ 0 → q.2.2.1.2.1 x = none → N + dbGrade q.2.1 ≤ T) :
    ∑ a : Z, kFlip (Bad d N) (.programK x a) σ ≤
      ((2 * ((T + 1) * ((T + 1) * T + 2 * T) * G) : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re := by
  show ∑ a : Z, diagMass {q : Unit × HwReg X Z (Mem HPos) |
    q.2 ∈ kFlipSet (Bad d N) (.programK x a)} σ ≤ _
  exact sum_diagMass_le_card (fun a : Z ↦ {q : Unit × HwReg X Z (Mem HPos) |
    q.2 ∈ kFlipSet (Bad d N) (.programK x a)}) _ hσ fun q hq t ht a₀ ha₀ ↦
      card_kFlip_programK_le hπ x q.2 (hT q hq) t ht a₀ ha₀

/-- **The fresh `k'` flips summed over the programmed value**: for `PermGood π G`, on states with
`N + dbGrade D ≤ T` where the cell is free, at most twice the capacity-scale count times the
trace. -/
theorem sum_kFlip_programK'_le {G T : ℕ} (hπ : PermGood d.perm G) (x : X)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef)
    (hT : ∀ q, σ q q ≠ 0 → q.2.2.1.2.2 x = none → N + dbGrade q.2.1 ≤ T) :
    ∑ a : Z, kFlip (Bad d N) (.programK' x a) σ ≤
      ((2 * ((T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal σ.trace.re := by
  show ∑ a : Z, diagMass {q : Unit × HwReg X Z (Mem HPos) |
    q.2 ∈ kFlipSet (Bad d N) (.programK' x a)} σ ≤ _
  exact sum_diagMass_le_card (fun a : Z ↦ {q : Unit × HwReg X Z (Mem HPos) |
    q.2 ∈ kFlipSet (Bad d N) (.programK' x a)}) _ hσ fun q hq t ht a₀ ha₀ ↦
      card_kFlip_programK'_le hπ x q.2 (hT q hq) t ht a₀ ha₀

/-- **The fresh `k` flips averaged over the programmed value**: for `PermGood π 18`, at grade
`N + dbGrade D ≤ 2^68`, at most `2^-301` per unit of trace. -/
theorem uavg_kFlip_programK_le (hπ : PermGood d.perm 18) (x : X)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef)
    (hT : ∀ q, σ q q ≠ 0 → q.2.2.1.2.1 x = none → N + dbGrade q.2.1 ≤ 2 ^ 68) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ a : Z, kFlip (Bad d N) (.programK x a) σ ≤
      (2 ^ 301)⁻¹ * ENNReal.ofReal σ.trace.re :=
  inv_card_Z_mul_le_of_le (by norm_num) (sum_kFlip_programK_le hπ x hσ hT)

/-- **The fresh `k'` flips averaged over the programmed value**: for `PermGood π 18`, at grade
`N + dbGrade D ≤ 2^68`, at most `2^-301` per unit of trace. -/
theorem uavg_kFlip_programK'_le (hπ : PermGood d.perm 18) (x : X)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef)
    (hT : ∀ q, σ q q ≠ 0 → q.2.2.1.2.2 x = none → N + dbGrade q.2.1 ≤ 2 ^ 68) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ a : Z, kFlip (Bad d N) (.programK' x a) σ ≤
      (2 ^ 301)⁻¹ * ENNReal.ofReal σ.trace.re :=
  inv_card_Z_mul_le_of_le (by norm_num) (sum_kFlip_programK'_le hπ x hσ hT)

end avg

end Quantum.Sphincs.Assembly

end
