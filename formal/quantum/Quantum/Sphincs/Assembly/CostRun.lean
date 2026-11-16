module

public import Quantum.Sphincs.Assembly.GameR
public import Quantum.Sphincs.Assembly.CostLift

@[expose] public section

/-!
# leanSPHINCS's event, its costs along the canonical game, and the classical calls

The quantities of the event bound on GameR's canonical game `gameR pol A p v` (contract C4: the
event side at template data `(p, v)`), and their bounds, as leanXMSS's
`Quantum.Xmss.Assembly.CostRun` (generic parts reused: `forallQueries_of_charge_step`,
`eps_readK_le`, `totalWeight_calls_le_of`, `querySupportedOn_runtimeR_step`).

* **The event and the costs**: Events' `Bad` at `evData p v` on the labelled memory (`BadR`, which
  does not read the label: `labelFree_badR`), its fresh bound (`freshBound_slice_badR`, the rate of
  GameR's `advEps v n` at `T = n + clsCap + 1`), its end weight `ewR`; the trials' read update
  `trialUpd` (Events' `cwUpd`, the label kept), the read projectors `PRm` (CostLift's `PRof`), the
  flip costs `dRof`, `dPof` and their totals along the game (`costTot`, `twR`, `encEpsTot`,
  `epsTot`, `massTot`, `progTot`, `callTot`).
* **The trace-weighted classical calls** (`totalWeight_calls_le`, `callTot_le_clsCap`): GameR's
  `callTot` is at most `clsCap`. The programs: `totalWeight_progs_le`.
* **The flip terms of a `k`, `k'` read** (`epsW_readK_le`, `epsW_readK'_le`): CostLift's `ε, ε'`
  off the empty read cell, with CostLift's capacity-scale counts for both parts of `Bad`
  (`card_flip_readK_bad_le`, `card_flip_readK'_bad_le`, twice leanXMSS's) at grade `T = 2^68` and
  `G = 18`: at most `2^-301 tr σ` each.
* **The flip terms along a run** (`totalWeight_epsW_le_add`, `totalWeight_epsW_le`): with
  `progCap + n + K ≤ 2^68`, at most `2^-300` per unit of the trace-weighted call count, plus those
  of the reads other than `k`, `k'` reads keeping the memory and the counter trials' selecting
  `h`-reads (`ReadOk`; the residual `epsRestWt`).
* **The challenge prefix calls only `ReadOk` reads** (`chgB_prefixR`, per component:
  `chgB_grindK`, `chgB_forsOpenT`, `chgB_signLayerT`, `chgB_signT`, `chgB_challengeT`,
  `chgB_prefixT`), for every digest policy. With `progCap + 6q + clsCap ≤ 2^68` for `q ≤ 2^64`
  (`progCap_add_le`): `epsTot_le_add` (the game, up to the verification's `h`-reads) and
  `epsW_prefixR_le` (the prefix, no residual).
* **The classical total of the game** (`clsTotal_of`): the per-port bound of CostLift
  (`flipCost_le_ports`) summed along the run with the cross terms optimized:
  `twR ≤ (√encEpsTot + √massTot)² + progTot`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

universe u v w

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest Message)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (LazyProg totalWeight_le_totalWeight totalWeight_add_weight
  totalWeight_const_mul_weight)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT tmplLens readLift readLens
  revealThen progThen RevealVals hashTrial rdRoundU liftRead extCls extWeight sumWeight LabelFree
  progChargeR SChg sChg_mono sChg_bind sChg_pure sChg_map sChg_foldlM chg_act chg_map
  isChargeBound_simulate isChargeBound_mono_charge isChargeBound_zero
  isChargeBound_portCharge_zero forallQueries_of_charge_step querySupportedOn_runtimeR_step
  totalWeight_calls_le_of totalWeight_progs_le_of eps_readK_le eps_readK'_le sum_cnt_le
  ofReal_add_le_of_cap totalWeight_congr_of_forallQueries traceRight_diag_eq_zero
  totalWeight_le_lin le_sq_add_of_forall_lin extWeight_hwCost_le_lin card_filter_le_of_imp)

namespace Quantum.Sphincs.Assembly

/- Instance search for `DecidableEq (Mem HPos)` (the read ports' memory) exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-! ## The event and the costs along the game -/

section quantities

/-- **Events' `Bad` at the template data `(p, v)`** on the register with the memory label (the
label is not read: `labelFree_badR`). -/
def BadR (p : Pub) (v : (s : HPos) → XD s) (N : ℕ) : Set (HwReg X Z (Mem HPos)) :=
  Bad (evData p v) N

theorem mem_badR_iff {p : Pub} {v : (s : HPos) → XD s} {N : ℕ} {r : HwReg X Z (Mem HPos)} :
    r ∈ BadR p v N ↔ r ∈ Bad (evData p v) N :=
  Iff.rfl

/-- Membership in `BadR`, decided classically. -/
noncomputable instance badRDec (p : Pub) (v : (s : HPos) → XD s) (N : ℕ) :
    DecidablePred (· ∈ BadR p v N) :=
  fun _ ↦ Classical.propDecidable _

/-- `BadR` does not read the memory label. -/
theorem labelFree_badR (p : Pub) (v : (s : HPos) → XD s) (N : ℕ) :
    LabelFree X Z HPos Selections (BadR p v N) :=
  fun _ _ _ _ _ ↦ Iff.rfl

/-- **The fresh bound of the slices of `BadR`** below `T` database entries (Events'
`freshBound_slice_bad` at `progCap` hardwired cells): at `T = n + clsCap + 1` the rate is GameR's
`advEps v n`. -/
theorem freshBound_slice_badR (p : Pub) (v : (s : HPos) → XD s) (hπ : PermGood p.perm 18)
    (T : ℕ) (W : Hw X Z) (m : Mem HPos) :
    FreshBound (slice (BadR p v progCap) W m) T
      (preimageRateBound (X := X) (Z := Z) (progCap + T) 18 (2 ^ 960) +
        preimageRateBound (X := X) (Z := Z) (progCap + T) 18
          (2 ^ 838 * coverMass (coverOf v))) :=
  @freshBound_slice_bad HPos (evData p v) progCap (badRDec p v progCap) 18 hπ T W m

/-- The weight of the event `BadR p v progCap` at the end of the run of `x` in `runtimeR`
(canonically the game `gameR pol A p v`). -/
noncomputable def ewR {α : Type} (p : Pub) (v : (s : HPos) → XD s)
    (x : QComp (recHwSpec X Z HPos Selections) (QReg.of Unit) (QReg.of Unit) α) : ℝ≥0∞ :=
  (runtimeR m0R).eventWeight .instruments (hwProjector (BadR p v progCap)) x initR

/-- The memory update of a counter trial's `h`-read on the labelled memory: Events' `cwUpd`, the
label kept (Template's `liftRead`). -/
noncomputable def trialUpd (t : TrialPt) : Mem HPos → Option X → Mem HPos :=
  fun m o ↦ (m.1, cwUpd t.K t.x t.xi m.2 o)

/-- The trial updates keep the memory or record a codeword selection. -/
theorem trialUpd_some (t : TrialPt) (m : Mem HPos) (y : X) :
    trialUpd t m (some y) = m ∨ trialUpd t m (some y) = (m.1, cwSel m.2 t.K t.x t.xi y) :=
  lift_cwUpd_some t.K t.x t.xi m y

/-- The read projectors of the flip costs (CostLift's `PRof`): off the selection reads of each
trial's `h`-read, off the empty read cell on the other read ports. -/
noncomputable def PRm (p : Pub) (v : (s : HPos) → XD s) (c : HwRead X Z (Mem HPos)) :
    Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ :=
  PRof Prod.snd trialUpd (evData p v) c

/-- The flip cost of the read ports, relative to the projectors `PRm p v`. -/
noncomputable def dRof (p : Pub) (v : (s : HPos) → XD s) (c : HwRead X Z (Mem HPos))
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) : ℝ≥0∞ :=
  flipCost (BadR p v progCap) (hwReadKraus c) (PRm p v c) σ

/-- The flip cost of the program ports, relative to the projector `0`. -/
noncomputable def dPof (p : Pub) (v : (s : HPos) → XD s) (c : HwProg X Z)
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) : ℝ≥0∞ :=
  flipCost (BadR p v progCap) (hwProgKraus c) 0 σ

/-- A cost summed along the run of the canonical game `gameR pol A p v` in `runtimeR` (record
ports: `0`). -/
noncomputable def costTot (pol : DigestPolicy) (A : SAdversary)
    (dR : HwRead X Z (Mem HPos) →
      Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ → ℝ≥0∞)
    (dP : HwProg X Z →
      Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ → ℝ≥0∞)
    (p : Pub) (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost dR dP)) (gameR pol A p v) initR

/-- The total classical (flip) cost of the run of the game. -/
noncomputable def twR (pol : DigestPolicy) (A : SAdversary) (p : Pub) (v : (s : HPos) → XD s) :
    ℝ≥0∞ :=
  costTot pol A (dRof p v) (dPof p v) p v

/-- The codeword flips of the selecting reads with the flip terms `ε, ε'` of the other reads,
summed along the run (`encW + epsW`). -/
noncomputable def encEpsTot (pol : DigestPolicy) (A : SAdversary) (p : Pub)
    (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  costTot pol A (fun c σ ↦ encW Prod.snd trialUpd (BadR p v progCap) (evData p v) c σ +
    epsW Prod.snd trialUpd (BadR p v progCap) (evData p v) c σ) (fun _ _ ↦ 0) p v

/-- The flip terms `ε, ε'` of the reads other than the selecting reads, summed along the run. -/
noncomputable def epsTot (pol : DigestPolicy) (A : SAdversary) (p : Pub)
    (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  costTot pol A (epsW Prod.snd trialUpd (BadR p v progCap) (evData p v)) (fun _ _ ↦ 0) p v

/-- The recorded mass of the reads (the read cell recorded or hardwired), summed along the run
(`massW`). -/
noncomputable def massTot (pol : DigestPolicy) (A : SAdversary) (p : Pub)
    (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  costTot pol A (massW Prod.snd trialUpd (evData p v)) (fun _ _ ↦ 0) p v

/-- The flip costs of the program ports, summed along the run. -/
noncomputable def progTot (pol : DigestPolicy) (A : SAdversary) (p : Pub)
    (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  costTot pol A (fun _ _ ↦ 0) (dPof p v) p v

/-- **The trace-weighted classical-call count**: the weight of the inputs of the read and program
calls, summed along the run. -/
noncomputable def callTot (pol : DigestPolicy) (A : SAdversary) (p : Pub)
    (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  costTot pol A (fun _ σ ↦ ENNReal.ofReal σ.trace.re) (fun _ σ ↦ ENNReal.ofReal σ.trace.re) p v

end quantities

/-! ## The calls -/

section calls

/-- The initial state of `runtimeR m0R` beside the trivial register has trace at most one. -/
theorem ofReal_trace_initR_le_one : ENNReal.ofReal initR.trace.re ≤ 1 :=
  ENNReal.ofReal_le_one.mpr
    ((SubState.basis ()).prod (runtimeR (X := X) (Z := Z) m0R).init).trace_re_le_one

/-- **The trace-weighted classical calls of a program** (`totalWeight_calls_le_of`): with at most
`K` classical calls on every path, at most `K`. -/
theorem totalWeight_calls_le {Ω : QReg → Type}
    (x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))
    {K : ℕ} (hK : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 1 else 0) K) :
    (runtimeR m0R).totalWeight .instruments (extWeight (hwCost
      (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re)) x initR ≤ K :=
  totalWeight_calls_le_of m0R initR_posSemidef ofReal_trace_initR_le_one x hK

/-- **The trace-weighted program calls of a program** (`totalWeight_progs_le_of`): with at most `K`
program calls on every path, at most `K`. -/
theorem totalWeight_progs_le {Ω : QReg → Type}
    (x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))
    {K : ℕ} (hK : IFreeM.IsChargeBound x (progChargeR HPos Selections) K) :
    (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (fun _ _ ↦ 0)
      fun _ σ ↦ ENNReal.ofReal σ.trace.re)) x initR ≤ K :=
  totalWeight_progs_le_of m0R initR_posSemidef ofReal_trace_initR_le_one x hK

/-- The initial state has empty databases. -/
theorem querySupportedOn_initR :
    QuerySupportedOn (fun m : QReg.of Unit × (runtimeR (X := X) (Z := Z) m0R).D ↦ dbGrade m.2.1)
      (Set.Iic 0) initR := by
  intro m m' hm
  change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty X Z, m0R) : HwReg X Z (Mem HPos))).matrix) m m' ≠ 0 at hm
  simp only [SubState.matrix_basis] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · constructor <;> simp [← he.1, ← he.2, dbGrade, Database.size_empty]
  · exact False.elim (h rfl)

end calls

/-! ## The flip terms of the `k`, `k'` reads for `BadR` -/

section epsW

/-- The capacity-scale count of a filled `k` cell at grade `2^68` (`card_flip_readK_bad_le`: both
parts of `Bad`). -/
def capK : ℕ := 2 * ((2 ^ 68 + 1) * ((2 ^ 68 + 1) * 2 ^ 68 + 2 * 2 ^ 68) * 18)

/-- The capacity-scale count of a filled `k'` cell at grade `2^68` (`card_flip_readK'_bad_le`). -/
def capK' : ℕ := 2 * ((2 ^ 68 + 1) + 2 ^ 68 * ((2 ^ 68 + 1) * 2 ^ 68 + 2 ^ 68 + 1) * 18 +
  2 ^ 68 * 2 ^ 68 * 18 + 2 ^ 68)

theorem capK_le : capK ≤ 2 ^ 211 := by
  unfold capK
  norm_num

theorem capK'_le : capK' ≤ 2 ^ 211 := by
  unfold capK'
  norm_num

/-- The `k`-read port of the template (`rdK`), on the labelled memory. -/
abbrev readKPort (x : X) : HwRead X Z (Mem HPos) :=
  liftRead (S := HPos) (.readK x (keepMem (M := Selections)))

/-- The `k'`-read port of the template (`rdK'`), on the labelled memory. -/
abbrev readK'Port (x : X) : HwRead X Z (Mem HPos) :=
  liftRead (S := HPos) (.readK' x (keepMem (M := Selections)))

/-- **The flip terms of a `k` read for `BadR`**: on states with at most `2^68 - progCap` database
entries per function, `ε + ε' ≤ 2^-300 tr σ` (`PermGood π 18`). -/
theorem epsW_readK_le (p : Pub) (v : (s : HPos) → XD s) (hπ : PermGood p.perm 18) (x : X)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) (hsupp : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ 2 ^ 68) :
    epsW Prod.snd trialUpd (BadR p v progCap) (evData p v) (readKPort x) σ ≤
      (2 ^ 300 : ℝ≥0∞)⁻¹ * ENNReal.ofReal σ.trace.re := by
  have ht : ¬IsTrial trialUpd (readKPort x) := by
    rintro ⟨zt, h⟩
    cases h
  set SR := trialSR Prod.snd trialUpd (evData p v) (readKPort x)
  have hSR : ∀ s, SR s → s.1.2.1 x = none ∧ s.2.1.2.1 x = none := fun s hs ↦ by
    rcases hs with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h ht
    · exact h
  set cnt : HwReg X Z (Mem HPos) → ℕ := fun s ↦
    if progCap + dbGrade s.1 ≤ 2 ^ 68 then capK else Fintype.card Z
  have hcnt : ∀ s, SR s → s ∉ BadR p v progCap → (Finset.univ.filter fun b : Z ↦
      ((s.1.1, Function.update s.1.2.1 x (some b), s.1.2.2), s.2.1, s.2.2) ∈
        BadR p v progCap).card ≤ cnt s := fun s hs hB ↦ by
    by_cases hT : progCap + dbGrade s.1 ≤ 2 ^ 68
    · simp only [cnt, ite_eq_left hT]
      exact card_filter_le_of_imp (card_flip_readK_bad_le (d := evData p v) (N := progCap)
        (T := 2 ^ 68) (D := s.1) (W := s.2.1) (m := s.2.2) hπ hB hT (hSR s hs).1 (hSR s hs).2)
        fun _ hb ↦ hb
    · simp only [cnt, ite_eq_right hT]
      exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ
  have hmono : ∀ s b, SR s → s ∈ BadR p v progCap →
      ((s.1.1, Function.update s.1.2.1 x (some b), s.1.2.2), s.2.1, s.2.2) ∈ BadR p v progCap :=
    fun s b hs hB ↦ mem_bad_fillK hB (hSR s hs).1 b
  obtain ⟨hε, hε'⟩ := eps_readK_le (BadR p v progCap) x (fun m o ↦ (m.1, keepMem m.2 o))
    (fun _ _ ↦ rfl) SR cnt hSR hcnt hmono hσ
  have hE := sum_cnt_le (BadR p v progCap) SR cnt capK hσ fun q hq ↦ by
    simp only [cnt, ite_eq_left (hsupp q hq), le_refl]
  unfold epsW flipF
  rw [ite_eq_right ht, one_kronecker_hwProjector]
  exact ofReal_add_le_of_cap capK_le hσ hε hε' hE

/-- **The flip terms of a `k'` read for `BadR`** (as `epsW_readK_le`). -/
theorem epsW_readK'_le (p : Pub) (v : (s : HPos) → XD s) (hπ : PermGood p.perm 18) (x : X)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) (hsupp : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ 2 ^ 68) :
    epsW Prod.snd trialUpd (BadR p v progCap) (evData p v) (readK'Port x) σ ≤
      (2 ^ 300 : ℝ≥0∞)⁻¹ * ENNReal.ofReal σ.trace.re := by
  have ht : ¬IsTrial trialUpd (readK'Port x) := by
    rintro ⟨zt, h⟩
    cases h
  set SR := trialSR Prod.snd trialUpd (evData p v) (readK'Port x)
  have hSR : ∀ s, SR s → s.1.2.2 x = none ∧ s.2.1.2.2 x = none := fun s hs ↦ by
    rcases hs with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h ht
    · exact h
  set cnt : HwReg X Z (Mem HPos) → ℕ := fun s ↦
    if progCap + dbGrade s.1 ≤ 2 ^ 68 then capK' else Fintype.card Z
  have hcnt : ∀ s, SR s → s ∉ BadR p v progCap → (Finset.univ.filter fun b : Z ↦
      ((s.1.1, s.1.2.1, Function.update s.1.2.2 x (some b)), s.2.1, s.2.2) ∈
        BadR p v progCap).card ≤ cnt s := fun s hs hB ↦ by
    by_cases hT : progCap + dbGrade s.1 ≤ 2 ^ 68
    · simp only [cnt, ite_eq_left hT]
      exact card_filter_le_of_imp (card_flip_readK'_bad_le (d := evData p v) (N := progCap)
        (T := 2 ^ 68) (D := s.1) (W := s.2.1) (m := s.2.2) hπ hB hT (hSR s hs).1 (hSR s hs).2)
        fun _ hb ↦ hb
    · simp only [cnt, ite_eq_right hT]
      exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ
  have hmono : ∀ s b, SR s → s ∈ BadR p v progCap →
      ((s.1.1, s.1.2.1, Function.update s.1.2.2 x (some b)), s.2.1, s.2.2) ∈ BadR p v progCap :=
    fun s b hs hB ↦ mem_bad_fillK' hB (hSR s hs).1 b
  obtain ⟨hε, hε'⟩ := eps_readK'_le (BadR p v progCap) x (fun m o ↦ (m.1, keepMem m.2 o))
    (fun _ _ ↦ rfl) SR cnt hSR hcnt hmono hσ
  have hE := sum_cnt_le (BadR p v progCap) SR cnt capK' hσ fun q hq ↦ by
    simp only [cnt, ite_eq_left (hsupp q hq), le_refl]
  unfold epsW flipF
  rw [ite_eq_right ht, one_kronecker_hwProjector]
  exact ofReal_add_le_of_cap capK'_le hσ hε hε' hE

end epsW

/-! ## The reads of a run -/

section readOk

/-- **The reads whose flip terms are priced here**: a `k` or `k'` read keeping the memory, or a
counter trial's selecting `h`-read (no `ε` term). -/
def ReadOk (c : HwRead X Z (Mem HPos)) : Prop :=
  (∃ x, c = readKPort x) ∨ (∃ x, c = readK'Port x) ∨ IsTrial trialUpd c

open scoped Classical in
/-- The charge of a read port: `0` on `ReadOk` reads, `1` otherwise. -/
noncomputable def okCharge (c : HwRead X Z (Mem HPos)) : ℕ := if ReadOk c then 0 else 1

theorem okCharge_eq_zero {c : HwRead X Z (Mem HPos)} (h : ReadOk c) : okCharge c = 0 :=
  ite_eq_left h

theorem readOk_of_okCharge {c : HwRead X Z (Mem HPos)} (h : okCharge c = 0) : ReadOk c := by
  by_contra hc
  rw [okCharge, ite_eq_right hc] at h
  exact one_ne_zero h

/-- The charge of `runtimeR`'s ports: the read ports by `okCharge`, the others free. -/
noncomputable def bR : (recHwSpec X Z HPos Selections).Port → ℕ
  | .inl (.inl (.inl _)) => 0
  | .inl (.inl (.inr c)) => okCharge c
  | .inl (.inr _) => 0
  | .inr _ => 0

/-- The same charge on the template ports. -/
noncomputable def bT : (SSpec Selections).Port → ℕ
  | .inl (.inl (.inl _)) => 0
  | .inl (.inl (.inr c)) => okCharge c.1
  | .inl (.inr _) => 0
  | .inr _ => 0

/-- The same charge on runtime 1's ports (inner memory `Selections`), through `liftRead`. -/
noncomputable def bD : (hwReadSpec X Z Selections).Port → ℕ
  | .inl _ => 0
  | .inr c => okCharge (liftRead (S := HPos) c)

end readOk

/-! ## The flip terms along a run -/

section run

/-- The flip-term weight of the read ports. -/
noncomputable abbrev epsWt (p : Pub) (v : (s : HPos) → XD s) :
    ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ → ℝ≥0∞ :=
  extWeight (hwCost (epsW Prod.snd trialUpd (BadR p v progCap) (evData p v)) fun _ _ ↦ 0)

/-- The trace weight of the read and program ports (`callTot`'s weight). -/
noncomputable abbrev callWt :
    ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ → ℝ≥0∞ :=
  extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re)

open scoped Classical in
/-- **The residual flip terms**: those of the read ports that are not `ReadOk` (for the whole game,
the verification's `h`-reads). -/
noncomputable def epsRestWt (p : Pub) (v : (s : HPos) → XD s) :
    ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ → ℝ≥0∞ :=
  fun i σ ↦ if bR i = 0 then 0 else epsWt p v i σ

/-- **The flip terms of the reads along a run.** A program of `runtimeR m0R` with at most `n`
sponge and `K` classical calls, `progCap + n + K ≤ 2^68`: the flip terms `ε + ε'` of its reads
(`epsW`) add up to at most `2^-300` per unit of the trace-weighted call count plus the flip terms
of the reads that are not `ReadOk` (`epsRestWt`), at data with `PermGood π 18`. -/
theorem totalWeight_epsW_le_add (p : Pub) (v : (s : HPos) → XD s) (hπ : PermGood p.perm 18)
    {Ω : QReg → Type}
    (x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))
    {n K : ℕ}
    (hn : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 0 else 1) n)
    (hK : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 1 else 0) K)
    (hT : progCap + (n + K) ≤ 2 ^ 68) :
    (runtimeR m0R).totalWeight .instruments (epsWt p v) x initR ≤
      (2 ^ 300 : ℝ≥0∞)⁻¹ * (runtimeR m0R).totalWeight .instruments callWt x initR +
        (runtimeR m0R).totalWeight .instruments (epsRestWt p v) x initR := by
  set κ : (recHwSpec X Z HPos Selections).Port → ℕ := fun i ↦
    (if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 0 else 1) +
      (if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 1 else 0) with hκ
  have hκ1 : ∀ i, κ i = 1 := fun i ↦ by
    rw [hκ]
    by_cases h : extCls X Z (Mem HPos) (recSpec HPos Selections) i = true <;> simp [h]
  have hx : IFreeM.IsChargeBound x (portCharge κ) (n + K) :=
    isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl) (hn.add hK)
  have hfq := forallQueries_of_charge_step (runtimeR m0R) (fun s ↦ dbGrade s.1) κ (fun _ ↦ 0)
    (fun i r t σ hσ ↦ (querySupportedOn_runtimeR_step m0R i r t σ hσ).mono
      (Set.Iic_subset_Iic.2 (by rw [hκ1]))) .instruments x hx (isChargeBound_portCharge_zero x)
    querySupportedOn_initR
  classical
  set wm : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
        ℝ≥0∞ := fun i σ ↦
    if ∀ a, σ a a ≠ 0 → dbGrade a.2.1 ≤ n + K then epsWt p v i σ else 0
  have hcongr := totalWeight_congr_of_forallQueries (runtimeR m0R) .instruments
    (w := epsWt p v) (w' := wm) (fun i E σ hP ↦ by
      have hc : ∀ a, MatrixMap.traceRight
          ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) E σ a a ≠
            0 → dbGrade a.2.1 ≤ n + K := fun a ha ↦ by
        obtain ⟨e, he⟩ : ∃ e, σ (a, e) (a, e) ≠ 0 := by
          by_contra h
          exact ha (traceRight_diag_eq_zero fun e ↦ not_not.1 fun he ↦ h ⟨e, he⟩)
        have h := (hP.2 (a, e) (a, e) he).1
        rw [Set.mem_Iic, Nat.zero_add] at h
        exact h
      exact (ite_eq_left hc).symm) x initR hfq
  refine hcongr.trans_le ((totalWeight_le_totalWeight (runtimeR m0R) .instruments
    (w' := fun i σ ↦ (2 ^ 300 : ℝ≥0∞)⁻¹ * callWt i σ + epsRestWt p v i σ) (fun i σ hσ ↦ ?_) x
    initR_posSemidef).trans_eq ((totalWeight_add_weight (runtimeR m0R) .instruments _ _ x
      initR).trans (congrArg (· + _) (totalWeight_const_mul_weight (runtimeR m0R) .instruments _
        _ x initR))))
  by_cases hg : ∀ a, σ a a ≠ 0 → dbGrade a.2.1 ≤ n + K
  swap
  · rw [show wm i σ = 0 from ite_eq_right hg]
    exact zero_le
  rw [show wm i σ = epsWt p v i σ from ite_eq_left hg]
  by_cases hb0 : bR i = 0
  swap
  · rw [show epsRestWt p v i σ = epsWt p v i σ from ite_eq_right hb0]
    exact le_add_self
  refine le_add_right ?_
  rcases i with ((q | c) | c) | T
  · simp [epsWt, extWeight, sumWeight, hwCost]
  · have hok : ReadOk c := readOk_of_okCharge hb0
    have hsupp : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ 2 ^ 68 := fun q hq ↦ by
      have := hg q hq
      omega
    rcases hok with ⟨y, rfl⟩ | ⟨y, rfl⟩ | ht
    · exact epsW_readK_le p v hπ y hσ hsupp
    · exact epsW_readK'_le p v hπ y hσ hsupp
    · show epsW Prod.snd trialUpd (BadR p v progCap) (evData p v) c σ ≤ _
      unfold epsW
      rw [ite_eq_left ht]
      exact zero_le
  · simp [epsWt, extWeight, sumWeight, hwCost]
  · simp [epsWt, extWeight, sumWeight]

/-- **No residual for a program calling only `ReadOk` reads.** -/
theorem totalWeight_epsRestWt_eq_zero (p : Pub) (v : (s : HPos) → XD s) {Ω : QReg → Type}
    (x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))
    (hb : IFreeM.IsChargeBound x (portCharge bR) 0) :
    (runtimeR m0R).totalWeight .instruments (epsRestWt p v) x initR = 0 := by
  have hfq := forallQueries_of_charge_step (runtimeR m0R) (fun _ ↦ 0) (fun _ ↦ 0) bR
    (fun _ _ _ _ _ _ _ _ ↦ ⟨Set.mem_Iic.2 (Nat.zero_le _), Set.mem_Iic.2 (Nat.zero_le _)⟩)
    .instruments x (isChargeBound_portCharge_zero x) hb
    (t := 0) (ρ := initR) fun _ _ _ ↦ ⟨Set.mem_Iic.2 le_rfl, Set.mem_Iic.2 le_rfl⟩
  exact (totalWeight_congr_of_forallQueries (runtimeR m0R) .instruments (w := epsRestWt p v)
    (w' := fun i σ ↦ 0 * callWt i σ) (fun i E σ hP ↦ by
      rw [zero_mul]
      exact ite_eq_left hP.1) x initR hfq).trans
    ((totalWeight_const_mul_weight (runtimeR m0R) .instruments 0 callWt x initR).trans
      (zero_mul _))

/-- **The flip terms of the reads along a run calling only `ReadOk` reads**: at most `2^-300` per
unit of the trace-weighted call count. -/
theorem totalWeight_epsW_le (p : Pub) (v : (s : HPos) → XD s) (hπ : PermGood p.perm 18)
    {Ω : QReg → Type}
    (x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))
    {n K : ℕ}
    (hn : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 0 else 1) n)
    (hK : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 1 else 0) K)
    (hT : progCap + (n + K) ≤ 2 ^ 68) (hb : IFreeM.IsChargeBound x (portCharge bR) 0) :
    (runtimeR m0R).totalWeight .instruments (epsWt p v) x initR ≤
      (2 ^ 300 : ℝ≥0∞)⁻¹ * (runtimeR m0R).totalWeight .instruments callWt x initR := by
  have h := totalWeight_epsW_le_add p v hπ x hn hK hT
  rwa [totalWeight_epsRestWt_eq_zero p v x hb, add_zero] at h

end run

/-! ## The challenge prefix calls only `ReadOk` reads -/

section prefixReads

variable {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- Realizing keeps the read charge. -/
theorem chgB_realizeT (v : (s : HPos) → XD s) {A : QReg}
    {y : QuantumComp L (SSpec Selections) Ω A} {n : ℕ}
    (h : IFreeM.IsChargeBound y (portCharge bT) n) :
    IFreeM.IsChargeBound (realizeT v y) (portCharge bR) n := by
  refine IFreeM.IsChargeBound.mapLens (tmplLens v) ?_
  have he : (fun s cmd ↦ portCharge (L := L) bR s ((tmplLens v).toFunA s cmd)) =
      portCharge bT := by
    funext s cmd
    rcases cmd with o | ⟨((i | c) | p) | T, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

/-- Lifting runtime 1's programs keeps the read charge. -/
theorem chgB_readLift {A : QReg} {y : QuantumComp L (hwReadSpec X Z Selections) Ω A} {n : ℕ}
    (h : IFreeM.IsChargeBound y (portCharge bD) n) :
    IFreeM.IsChargeBound (readLift goodAll y) (portCharge bT) n := by
  refine IFreeM.IsChargeBound.mapLens (readLens goodAll) ?_
  have he : (fun s cmd ↦ portCharge (L := L) bT s ((readLens goodAll).toFunA s cmd)) =
      portCharge bD := by
    funext s cmd
    rcases cmd with o | ⟨i | c, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

/-- A simulated permutation program makes no read calls. -/
theorem chgB_simulate (π : Equiv.Perm (X × Z)) {A : QReg}
    {x : QuantumComp LocalSig.instruments.{0} (qrpmSpec (X × Z)) Ω A} {q : ℕ}
    (hx : x.IsTotalQueryBound q) :
    IFreeM.IsChargeBound ((simulate LocalSig.Interp.instruments π x).liftOrdinary
      (t := hwReadCmdSpec X Z Selections)) (portCharge bD) 0 := by
  refine (isChargeBound_mono_charge (fun s a ↦ ?_)
    (isChargeBound_simulate (M := Selections) 0 1 π hx)).mono (le_of_eq (zero_mul _))
  rcases a with o | ⟨i | c, E, ℓ⟩
  · exact le_rfl
  · exact le_rfl
  · show okCharge _ ≤ 1
    unfold okCharge
    split <;> omega

/-- A read call of a `ReadOk` read. -/
theorem chgB_readCall (c : HwRead X Z Selections) (hc : ReadOk (liftRead (S := HPos) c))
    (B : QReg) : IFreeM.IsChargeBound (readCall c B) (portCharge bD) 0 := by
  unfold readCall
  exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    ((IFreeM.isChargeBound_liftBind_iff _ _ _).mpr
      ⟨Nat.le_of_eq (okCharge_eq_zero hc), fun _ ↦ trivial⟩) fun _ ↦
    FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ trivial

theorem sChgB_readCall (c : HwRead X Z Selections) (hc : ReadOk (liftRead (S := HPos) c))
    (B : QReg) {β : Type}
    (g : c.Result → List (SpongeRead X Z) → β × List (SpongeRead X Z)) :
    SChg bD (fun log ↦ (readCall c B).bind fun r ↦ QuantumComp₂.pure (g r log) :
      StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z Selections) B B) β) 0 := by
  intro log
  show IFreeM.IsChargeBound ((readCall c B).bind fun r ↦ QuantumComp₂.pure (g r log)) _ _
  exact FreeM₂.isChargeBound_bind (n₂ := 0) (chgB_readCall c hc B) fun _ ↦ trivial

/-- A trial's round of reads: a `k` read, a `k'` read and the selecting `h`-read. -/
theorem sChgB_rdRoundU (K : Key) (π : Equiv.Perm (X × Z)) (B : QReg) (s : X × Z) (blk : X) :
    SChg bD (rdRoundU Selections (cwUpd K) π B s blk) 0 := by
  refine sChg_mono _ (sChg_bind _ (sChgB_readCall (.readK _ keepMem) (Or.inl ⟨_, rfl⟩) B _)
    fun _ ↦ sChg_bind _ (sChgB_readCall (.readK' _ keepMem) (Or.inr (Or.inl ⟨_, rfl⟩)) B _)
      fun _ ↦ sChg_bind _ (sChgB_readCall (.readH _ (cwUpd K blk _))
        (Or.inr (Or.inr ⟨(_, ⟨K, blk, _⟩), rfl⟩)) B _) fun _ ↦ sChg_pure _ _ 0) (by omega)

/-- **A counter trial's hash** calls only `ReadOk` reads. -/
theorem chgB_hashTrial (K : Key) (π : Equiv.Perm (X × Z)) (B : QReg) (input : HashSig.HashInput) :
    IFreeM.IsChargeBound (hashTrial Selections (cwUpd K) π B input) (portCharge bD) 0 := by
  unfold hashTrial
  rw [StateT.run'_eq]
  exact (chg_map _ _ (sChg_map _ _ (sChg_map _ _
    (sChg_foldlM _ _ _ (sChgB_rdRoundU K π B) (Quantum.Xmss.blocks input) (0, 0))) [])).mono
    (le_of_eq (zero_mul _))

/-- **The counter search** calls only `ReadOk` reads. -/
theorem chgB_grindK (pub : Pub) (B : QReg) (K : Key) (m : Digest) :
    ∀ n c, IFreeM.IsChargeBound (grindK Selections cwUpd pub B K m n c) (portCharge bD) 0
  | 0, _ => trivial
  | n + 1, c => by
    rw [grindK]
    refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgB_hashTrial K pub.perm B _)
      fun out ↦ ?_
    split
    · trivial
    · exact chgB_grindK pub B K m n (c + 1)

theorem chgB_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × Selections) → QComp (SSpec Selections) B B' α)
    (hk : ∀ r, IFreeM.IsChargeBound (k r) (portCharge bT) 0) :
    IFreeM.IsChargeBound (revealThen goodAll T k) (portCharge bT) 0 :=
  (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨le_rfl, fun r ↦
    FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ hk r⟩

theorem chgB_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (SSpec Selections) B B' α) (hk : IFreeM.IsChargeBound k (portCharge bT) 0) :
    IFreeM.IsChargeBound (progThen p hp k) (portCharge bT) 0 :=
  (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨le_rfl, fun _ ↦
    FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ hk⟩

theorem chgB_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) :
    IFreeM.IsChargeBound (progPorts Selections B ps) (portCharge bT) 0 := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact chgB_progThen p trivial _ ih

theorem chgB_progSlots (pub : Pub) (B : QReg) (ss : List Slot) :
    IFreeM.IsChargeBound (progSlots Selections pub B ss) (portCharge bT) 0 := by
  induction ss with
  | nil => trivial
  | cons s ss ih =>
    exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgB_progPorts B _) fun _ ↦ ih

/-- **A FORS opening** calls no read. -/
theorem chgB_forsOpenT (pub : Pub) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) :
    IFreeM.IsChargeBound (forsOpenT Selections pub B idx lv) (portCharge bT) 0 := by
  unfold forsOpenT
  exact chgB_revealThen _ _ fun _ ↦
    FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgB_progSlots pub B _) fun _ ↦ trivial

/-- **A layer signature** calls only `ReadOk` reads. -/
theorem chgB_signLayerT (pub : Pub) (B : QReg) (K : Key) :
    IFreeM.IsChargeBound (signLayerT Selections cwUpd pub B K) (portCharge bT) 0 := by
  unfold signLayerT
  refine chgB_revealThen _ _ fun _ ↦ ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    (chgB_readLift (chgB_grindK pub B _ _ _ _)) fun g ↦ ?_
  rcases g with _ | ⟨c, x⟩
  · trivial
  · exact chgB_revealThen _ _ fun _ ↦
      FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgB_progSlots pub B _) fun _ ↦ trivial

/-- **A signature** calls only `ReadOk` reads, for every digest policy. -/
theorem chgB_signT (pol : DigestPolicy) (pub : Pub) (B : QReg) (msg : Message) :
    IFreeM.IsChargeBound (signT Selections cwUpd pol pub B msg) (portCharge bT) 0 := by
  unfold signT
  refine chgB_revealThen _ _ fun _ ↦ chgB_revealThen _ _ fun _ ↦ ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgB_progPorts B _) fun _ ↦ ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgB_forsOpenT pub B _ _) fun _ ↦ ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgB_signLayerT pub B _) fun s₀ ↦ ?_
  rcases s₀ with _ | bottom
  · trivial
  · refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgB_signLayerT pub B _) fun s₁ ↦ ?_
    rcases s₁ with _ | middle
    · trivial
    · refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgB_signLayerT pub B _)
        fun s₂ ↦ ?_
      rcases s₂ with _ | top <;> trivial

/-- **The challenger** calls only `ReadOk` reads. -/
theorem chgB_challengeT (pol : DigestPolicy) (pub : Pub) (A : QReg)
    (cmd : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    IFreeM.IsChargeBound (challengeT Selections cwUpd pol pub A cmd) (portCharge bT) 0 := by
  rcases cmd with o | ⟨q | msg, E, ℓ⟩
  · exact chgB_readLift (chgB_simulate _ (q := 0)
      ((QuantumComp.isTotalQueryBound_primBind_iff _ _ _).mpr fun _ ↦ trivial))
  · exact chgB_readLift (chgB_simulate _ (q := 1)
      ((QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr
        ⟨Nat.one_pos, fun _ ↦ trivial⟩))
  · exact IFreeM.isChargeBound_bind (n₁ := 0) (n₂ := 0) (FreeM₂.isChargeBound_bind
      (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ chgB_signT pol pub _ msg) fun _ _ ↦
        IFreeM.isChargeBound_pure _ 0

/-- **The challenge prefix** calls only `ReadOk` reads. -/
theorem chgB_prefixT (pol : DigestPolicy) (pub : Pub) (A : SAdversary) :
    IFreeM.IsChargeBound (prefixT Selections cwUpd pol pub A) (portCharge bT) 0 := by
  unfold prefixT challengedT
  refine chgB_revealThen _ _ fun _ ↦ ?_
  exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    (IFreeM.IsChargeBound.substitute (challengeT Selections cwUpd pol pub) (c := fun _ _ ↦ 0)
      (fun s cmd ↦ chgB_challengeT pol pub s cmd) (isChargeBound_zero _)) fun _ ↦ trivial

/-- **The realized challenge prefix** calls only `ReadOk` reads, for every digest policy and
template data. -/
theorem chgB_prefixR (pol : DigestPolicy) (A : SAdversary) (p : Pub) (v : (s : HPos) → XD s) :
    IFreeM.IsChargeBound (prefixR pol A p v) (portCharge bR) 0 :=
  chgB_realizeT v (chgB_prefixT pol p A)

end prefixReads

/-! ## The flip terms and the calls of the game -/

section readEps

/-- `progCap + 6q + clsCap ≤ 2^68` for `q ≤ 2^64`. -/
theorem progCap_add_le {q : ℕ} (hq : q ≤ 2 ^ 64) : progCap + (6 * q + clsCap) ≤ 2 ^ 68 := by
  have hc : progCap + clsCap ≤ 2 ^ 68 - 6 * 2 ^ 64 := by
    rw [clsCap_eq, progCap_eq]
    norm_num [signatureLimit]
  omega

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **GameR's `callTot`**: at most `clsCap` (`clsCalls_gameR`), for every digest policy and
template data. -/
theorem callTot_le_clsCap (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s) :
    callTot pol A p v ≤ clsCap :=
  totalWeight_calls_le (gameR pol A p v) (clsCalls_gameR hperm hsign pol p v)

/-- **The flip terms `ε, ε'` over the game, up to the residual reads**: for `q ≤ 2^64`, at data with
`PermGood π 18`, `epsTot ≤ 2^-300 callTot` plus the flip terms of the game's reads that are not
`ReadOk` (the verification's `h`-reads). -/
theorem epsTot_le_add (hq : q ≤ 2 ^ 64) (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)
    (hπ : PermGood p.perm 18) :
    epsTot pol A p v ≤ (2 ^ 300 : ℝ≥0∞)⁻¹ * callTot pol A p v +
      (runtimeR m0R).totalWeight .instruments (epsRestWt p v) (gameR pol A p v) initR :=
  totalWeight_epsW_le_add p v hπ (gameR pol A p v) (advCalls_gameR hperm hsign pol p v)
    (clsCalls_gameR hperm hsign pol p v) (progCap_add_le hq)

/-- **The flip terms `ε, ε'` on the challenge prefix** (no residual: the prefix calls only
`ReadOk` reads), for `q ≤ 2^64` at data with `PermGood π 18`. -/
theorem epsW_prefixR_le (hq : q ≤ 2 ^ 64) (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)
    (hπ : PermGood p.perm 18) :
    (runtimeR m0R).totalWeight .instruments (epsWt p v) (prefixR pol A p v) initR ≤
      (2 ^ 300 : ℝ≥0∞)⁻¹ *
        (runtimeR m0R).totalWeight .instruments callWt (prefixR pol A p v) initR :=
  totalWeight_epsW_le p v hπ (prefixR pol A p v) (advCalls_prefixR hperm hsign pol p v)
    (clsCalls_prefixR hperm hsign pol p v) (progCap_add_le hq) (chgB_prefixR pol A p v)

end readEps

/-! ## The classical total of the game -/

/-- **The classical total of the game** (CostLift's `flipCost_le_ports` summed along the run, the
cross terms optimized): `twR ≤ (√encEpsTot + √massTot)² + progTot`, for every digest policy,
adversary and template data. -/
theorem clsTotal_of (pol : DigestPolicy) (A : SAdversary) (p : Pub) (v : (s : HPos) → XD s) :
    twR pol A p v ≤ (encEpsTot pol A p v ^ (2⁻¹ : ℝ) + massTot pol A p v ^ (2⁻¹ : ℝ)) ^ 2 +
      progTot pol A p v :=
  le_sq_add_of_forall_lin fun _ hs ↦ totalWeight_le_lin (runtimeR m0R) .instruments _ _ _ _ _ _
    (extWeight_hwCost_le_lin (dRof p v)
      (fun c σ ↦ encW Prod.snd trialUpd (BadR p v progCap) (evData p v) c σ +
        epsW Prod.snd trialUpd (BadR p v progCap) (evData p v) c σ)
      (massW Prod.snd trialUpd (evData p v)) (fun _ _ ↦ 0) (dPof p v) _ _
      fun c _ hσ ↦ (flipCost_le_ports trialUpd (BadR p v progCap) (fun _ ↦ Iff.rfl)
        trialUpd_some c hs hσ).trans_eq (add_zero _).symm)
    (gameR pol A p v) initR_posSemidef

end Quantum.Sphincs.Assembly

end
