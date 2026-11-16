module

public import Quantum.Xmss.Assembly.PrefixFacts
public import Quantum.Xmss.Assembly.ProgView
public import Quantum.Xmss.Assembly.TrialsOff

@[expose] public section

/-!
# The trial-hit mass

PrefixFacts' `trialHitMass m₀ A L`: the weight, at the end of the canonical game, of the
decompressed registers where some top trial, read against the register's view, reads a cell of
`tableHw L`. Here it is bounded on the tables with `TrialsOff L` and `PermGood L.perm 18`.

* **A database event on the reachable registers** (`trialHitMass_le_eventMassDec`): along the
  game the hardwired cells stay inside `tableHw L` (ProgView's `ProgsIn`; the program ports outside
  are cut, `cutR`, which changes no run of the game, `run_cutR`), so on the reachable registers the
  view agrees with the databases off `tableHw L` and the trial-hit event is the database event
  `HitView L D.fill` (`hitView_of_trialHit`), which depends only on the cells off `tableHw L`
  (`hitView_congr`).
* **The uniform databases** (`DecUniformHyp`, open, agent DecUniform): the decompressed weight of
  an event of the databases determined off `tableHw L` is at most its fraction of the total tables.
* **Counting** (`card_mul_card_filter_le_of_blocks`, over abstract types): a one-block trial at a
  block `x` hits a `k'` cell of a set `K'` for at most `G |K'|` of `|Z|` values of `k x`, and an `h`
  cell of `H` for at most `|H|` of `|Z|` values of the fresh `k'` cell; over the trial blocks `Bl`,
  at most `|Bl| (G |K'| + |H|) / |Z|`. A `k` cell is never hit (`TrialsOff`).
* **leanXMSS** (`trialHitMass_le_frac`, `trialHitMass_le_keccak`, `uavg_trialHitMass_le`): at most
  `2^64` trial blocks, at most `8 · 498 · 2^32` cells of each kind in `tableHw L`, hence `2^-399`.
-/

open Matrix
open scoped ENNReal Kronecker ComplexOrder

universe u v

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid
open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma LeanXmss.RandomPermutationModel

/-! ## Diagonal events in a conjugated basis -/

section linalg

variable {I H : Type} [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]

omit [Fintype I] [Fintype H] in
theorem one_kronecker_diagonal_eq (g : H → ℂ) :
    (1 : Matrix I I ℂ) ⊗ₖ diagonal g = diagonal fun m : I × H ↦ g m.2 := by
  rw [← diagonal_one, diagonal_kronecker_diagonal]
  simp only [one_mul]

/-- The weight of a diagonal event `g` in the basis conjugated by `C`: the diagonal of the
conjugated operator weighted by `g`. -/
theorem trace_conj_kron_proj (C : Matrix H H ℂ) (hC : C * C = 1) (hCh : Cᴴ = C) (g : H → ℂ)
    (hg : ∀ s, g s * g s = g s) (hgs : ∀ s, star (g s) = g s) (σ : Matrix (I × H) (I × H) ℂ) :
    (MatrixMap.conj ((1 : Matrix I I ℂ) ⊗ₖ (C * diagonal g * C)) σ).trace =
      ∑ m, g m.2 * MatrixMap.conj ((1 : Matrix I I ℂ) ⊗ₖ C) σ m m := by
  have hgg : diagonal g * diagonal g = diagonal g := by
    rw [diagonal_mul_diagonal]
    exact congrArg diagonal (funext hg)
  have hgh : (diagonal g)ᴴ = diagonal g := by
    rw [diagonal_conjTranspose]
    exact congrArg diagonal (funext hgs)
  have hQ : (C * diagonal g * C)ᴴ = C * diagonal g * C := by
    rw [conjTranspose_mul, conjTranspose_mul, hCh, hgh, Matrix.mul_assoc]
  have hQQ : C * diagonal g * C * (C * diagonal g * C) = C * diagonal g * C := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc C C, hC, Matrix.one_mul, ← Matrix.mul_assoc (diagonal g) (diagonal g),
      hgg]
  have hCi : ((1 : Matrix I I ℂ) ⊗ₖ C)ᴴ = (1 : Matrix I I ℂ) ⊗ₖ C := by
    rw [conjTranspose_kronecker, conjTranspose_one, hCh]
  have hsplit : (1 : Matrix I I ℂ) ⊗ₖ (C * diagonal g * C) =
      ((1 : Matrix I I ℂ) ⊗ₖ C) * diagonal (fun m : I × H ↦ g m.2) *
        ((1 : Matrix I I ℂ) ⊗ₖ C) := by
    rw [← one_kronecker_diagonal_eq g, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul,
      Matrix.one_mul]
  rw [MatrixMap.trace_conj_apply, conjTranspose_kronecker, conjTranspose_one, hQ,
    ← mul_kronecker_mul, Matrix.one_mul, hQQ, hsplit, MatrixMap.conj_apply, hCi]
  calc (((1 : Matrix I I ℂ) ⊗ₖ C) * diagonal (fun m : I × H ↦ g m.2) *
        ((1 : Matrix I I ℂ) ⊗ₖ C) * σ).trace
      = (((1 : Matrix I I ℂ) ⊗ₖ C) * (diagonal (fun m : I × H ↦ g m.2) *
          (((1 : Matrix I I ℂ) ⊗ₖ C) * σ))).trace := by simp only [Matrix.mul_assoc]
    _ = (diagonal (fun m : I × H ↦ g m.2) * (((1 : Matrix I I ℂ) ⊗ₖ C) * σ) *
          ((1 : Matrix I I ℂ) ⊗ₖ C)).trace := Matrix.trace_mul_comm _ _
    _ = ∑ m, g m.2 * (((1 : Matrix I I ℂ) ⊗ₖ C) * σ * ((1 : Matrix I I ℂ) ⊗ₖ C)) m m := by
        simp only [Matrix.mul_assoc, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]

/-- **Comparing two diagonal events** in the basis conjugated by `C`: if the conjugated operator is
supported on `S` and `f₁ ⊆ f₂` on `S`, the weight of `f₁` is at most that of `f₂`. -/
theorem re_trace_conj_kron_proj_le (C : Matrix H H ℂ) (hC : C * C = 1) (hCh : Cᴴ = C)
    (f₁ f₂ : H → Prop) {d₁ : DecidablePred f₁} {d₂ : DecidablePred f₂} (S : Set H)
    {σ : Matrix (I × H) (I × H) ℂ} (hσ : σ.PosSemidef)
    (hS : QuerySupportedOn (fun m : I × H ↦ m.2) S
      (MatrixMap.conj ((1 : Matrix I I ℂ) ⊗ₖ C) σ))
    (h12 : ∀ s ∈ S, f₁ s → f₂ s) :
    (MatrixMap.conj ((1 : Matrix I I ℂ) ⊗ₖ
        (C * diagonal (fun s ↦ if f₁ s then (1 : ℂ) else 0) * C)) σ).trace.re ≤
      (MatrixMap.conj ((1 : Matrix I I ℂ) ⊗ₖ
        (C * diagonal (fun s ↦ if f₂ s then (1 : ℂ) else 0) * C)) σ).trace.re := by
  have hg : ∀ (f : H → Prop) (d : DecidablePred f) (s : H),
      (@ite ℂ (f s) (d s) 1 0) * (@ite ℂ (f s) (d s) 1 0) = @ite ℂ (f s) (d s) 1 0 := by
    intro f d s
    split_ifs <;> simp
  have hgs : ∀ (f : H → Prop) (d : DecidablePred f) (s : H),
      star (@ite ℂ (f s) (d s) 1 0) = @ite ℂ (f s) (d s) 1 0 := by
    intro f d s
    split_ifs <;> simp
  rw [trace_conj_kron_proj C hC hCh _ (hg f₁ d₁) (hgs f₁ d₁),
    trace_conj_kron_proj C hC hCh _ (hg f₂ d₂) (hgs f₂ d₂), Complex.re_sum, Complex.re_sum]
  have hP : (MatrixMap.conj ((1 : Matrix I I ℂ) ⊗ₖ C) σ).PosSemidef :=
    hσ.mul_mul_conjTranspose_same _
  refine Finset.sum_le_sum fun m _ ↦ ?_
  have hd : 0 ≤ (MatrixMap.conj ((1 : Matrix I I ℂ) ⊗ₖ C) σ m m).re :=
    (Complex.nonneg_iff.mp hP.diag_nonneg).1
  by_cases h1 : f₁ m.2
  · by_cases h0 : MatrixMap.conj ((1 : Matrix I I ℂ) ⊗ₖ C) σ m m = 0
    · simp [h0]
    · have h2 := h12 _ (hS m m h0).1 h1
      simp [h1, h2]
  · by_cases h2 : f₂ m.2
    · rw [ite_eq_right h1, ite_eq_left h2, zero_mul, one_mul, Complex.zero_re]
      exact hd
    · simp [h1, h2]

end linalg

/-! ## The reachable registers keep their hardwired cells inside `tableHw L` -/

section reach

/-- Runtime 2 with record ports, with the program ports that program a cell outside `W` (or with
another value) cut to the failing subinstrument. -/
noncomputable def cutStep (m₀ : Finset HPos × Selections) (W : Hw X Z)
    (i : (recHwSpec X Z HPos Selections).Port) :
    SubInstrument ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m₀).D)
      ((recHwSpec X Z HPos Selections).Out i × (runtimeR (X := X) (Z := Z) m₀).D)
      ((recHwSpec X Z HPos Selections).Result i) :=
  open Classical in
  if PortIn Selections W i then (runtimeR m₀).step i else DSubInstrument.fail

/-- The cut runtime. -/
noncomputable def cutR (m₀ : Finset HPos × Selections) (W : Hw X Z) :
    QuantumRuntime (recHwSpec X Z HPos Selections) :=
  ⟨(runtimeR (X := X) (Z := Z) m₀).D, (runtimeR (X := X) (Z := Z) m₀).init, cutStep m₀ W⟩

/-- A read port keeps the hardwired cells (ProgView's `stepHw_read` for any read). -/
theorem stepHw_read_any (m₀ : Finset HPos × Selections) (W : Hw X Z)
    (c : HwRead X Z (Finset HPos × Selections)) : StepHw m₀ W (.inl (.inl (.inr c))) := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inr c)))).branch r σ =
      MatrixMap.conj (hwReadKraus c r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m₀ c r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    show Quantum.Sponge.HwLe q'.2.2.1 W
    rw [hwReadKraus_ne_zero_hw c r (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK]
    exact hq

/-- Every step of the cut runtime keeps the hardwired cells inside `W`. -/
theorem cutStep_hw (m₀ : Finset HPos × Selections) (W : Hw X Z)
    (i : (recHwSpec X Z HPos Selections).Port) (r : (recHwSpec X Z HPos Selections).Result i)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m₀).D)
      ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m₀).D) ℂ)
    (hσ : QuerySupportedOn
      (fun m : (recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m₀).D ↦ m.2)
      {s : HwReg X Z (Finset HPos × Selections) | Quantum.Sponge.HwLe s.2.1 W} σ) :
    QuerySupportedOn
      (fun m : (recHwSpec X Z HPos Selections).Out i × (runtimeR (X := X) (Z := Z) m₀).D ↦ m.2)
      {s : HwReg X Z (Finset HPos × Selections) | Quantum.Sponge.HwLe s.2.1 W}
      ((cutStep m₀ W i).branch r σ) := by
  unfold cutStep
  split_ifs with hi
  · rcases i with ((i | c) | c) | T
    · exact stepHw_sponge m₀ W i r σ hσ
    · exact stepHw_read_any m₀ W c r σ hσ
    · exact stepHw_prog m₀ (W := W) (c := c) hi r σ hσ
    · exact stepHw_rec m₀ W T r σ hσ
  · rw [DSubInstrument.branch_fail]
    exact querySupportedOn_zero _ _

/-- **Cutting changes no run** whose calls satisfy `hwSupp` (the program ports called program cells
of `W`). -/
theorem run_cutR (m₀ : Finset HPos × Selections) (W : Hw X Z) {Λ : LocalSig.{u, v}}
    (I : Λ.Interp) {Ω : QReg → Type} {A : QReg}
    (x : QuantumComp Λ (recHwSpec X Z HPos Selections) Ω A)
    (ρ : Matrix (A × (runtimeR (X := X) (Z := Z) m₀).D) (A × (runtimeR (X := X) (Z := Z) m₀).D) ℂ)
    (hx : (runtimeR m₀).ForallQueries I (hwSupp Selections m₀ W) x ρ) (p : Σ u, Ω u) :
    ((runtimeR m₀).run I x).branch p ρ = ((cutR m₀ W).run I x).branch p ρ :=
  run_branch_apply_eq_of_forallQueries (σ₁ := (runtimeR (X := X) (Z := Z) m₀).init)
    (s₁ := (runtimeR (X := X) (Z := Z) m₀).step) (σ₂ := (runtimeR (X := X) (Z := Z) m₀).init)
    (s₂ := cutStep m₀ W) I (fun i E σ hσ r ↦ by rw [cutStep, ite_eq_left hσ.1]) hx p

/-- Every branch of every run of the cut runtime keeps the hardwired cells inside `W`. -/
theorem supp_run_cutR (m₀ : Finset HPos × Selections) (W : Hw X Z) {Λ : LocalSig.{u, v}}
    (I : Λ.Interp) {Ω : QReg → Type} {A : QReg}
    (x : QuantumComp Λ (recHwSpec X Z HPos Selections) Ω A)
    {ρ : Matrix (A × (runtimeR (X := X) (Z := Z) m₀).D) (A × (runtimeR (X := X) (Z := Z) m₀).D) ℂ}
    (hρ : QuerySupportedOn (fun m : A × (runtimeR (X := X) (Z := Z) m₀).D ↦ m.2)
      {s : HwReg X Z (Finset HPos × Selections) | Quantum.Sponge.HwLe s.2.1 W} ρ)
    (p : Σ u, Ω u) :
    QuerySupportedOn (fun m : p.1 × (runtimeR (X := X) (Z := Z) m₀).D ↦ m.2)
      {s : HwReg X Z (Finset HPos × Selections) | Quantum.Sponge.HwLe s.2.1 W}
      (((cutR m₀ W).run I x).branch p ρ) :=
  querySupportedOn_run (cutR m₀ W)
    {s : HwReg X Z (Finset HPos × Selections) | Quantum.Sponge.HwLe s.2.1 W}
    (fun i r σ hσ ↦ cutStep_hw m₀ W i r σ hσ) I x hρ p

/-- The initial state has no hardwired cell. -/
theorem supp_init_hw (m₀ : Finset HPos × Selections) (W : Hw X Z) :
    QuerySupportedOn (fun m : QReg.of Unit × (runtimeR (X := X) (Z := Z) m₀).D ↦ m.2)
      {s : HwReg X Z (Finset HPos × Selections) | Quantum.Sponge.HwLe s.2.1 W}
      ((SubState.basis ()).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) := by
  intro m m' hm
  change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty X Z, m₀) : HwReg X Z (Finset HPos × Selections))).matrix) m m' ≠ 0
    at hm
  simp only [SubState.matrix_basis] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · show Quantum.Sponge.HwLe m.2.2.1 W ∧ Quantum.Sponge.HwLe m'.2.2.1 W
    rw [← he.1, ← he.2]
    exact ⟨spongeHwLe_hwEmpty W, spongeHwLe_hwEmpty W⟩
  · exact absurd rfl h

/-- The decompression keeps a support condition on the classical part, beside any register. -/
theorem supp_conj_compressReg {A M' : Type} [Fintype A] [DecidableEq A] [Fintype M']
    [DecidableEq M'] {P : Hw X Z × M' → Prop}
    {σ : Matrix (A × HwReg X Z M') (A × HwReg X Z M') ℂ}
    (h : QuerySupportedOn (fun p : A × HwReg X Z M' ↦ p.2) {s | P s.2} σ) :
    QuerySupportedOn (fun p : A × HwReg X Z M' ↦ p.2) {s | P s.2}
      (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ compressReg X Z M') σ) :=
  QuerySupportedOn.conj h fun m' m hK hm ↦ by
    have h' := (one_kronecker_ne_zero (a := m.1) (a' := m'.1) (b := m.2) (b' := m'.2) hK).2
    rw [compressReg, kroneckerMap_apply] at h'
    have h₂ := right_ne_zero_of_mul h'
    rw [Matrix.one_apply] at h₂
    split_ifs at h₂ with he
    · show P m'.2.2
      rw [he]
      exact hm
    · exact absurd rfl h₂

end reach

/-! ## The trial hit as a database event -/

section dbEvent

/-- Some top trial, read against the view `t`, reads a cell of `tableHw L` (`TrialHit L` is this
event of the register's view `regFns s`). -/
def HitView (L : HonestTable) (t : SpongeKeys X Z) : Prop :=
  ∃ e : KeyIndex, e.val < keyCount topLayer ∧ ∃ n < randomizerAttemptLimit,
    ∃ rd ∈ inputReads t L.perm (topTrial L e n), InHw (tableHw L) rd.point

theorem hitView_of_offAgree {L : HonestTable} {t t' : SpongeKeys X Z}
    (h : OffAgree (tableHw L) t t') (ht : HitView L t') : HitView L t := by
  obtain ⟨e, he, n, hn, rd, hrd, hin⟩ := ht
  by_contra hs
  have hav : ∀ rd ∈ inputReads t L.perm (topTrial L e n), ¬InHw (tableHw L) rd.point :=
    fun rd hrd hin ↦ hs ⟨e, he, n, hn, rd, hrd, hin⟩
  rw [(inputReads_eq_of_offAgree h L.perm _ hav).1] at hrd
  exact hav rd hrd hin

/-- Two database triples agree off the cells of `W`. -/
def OffCells (W : Hw X Z) (D D' : DbReg X Z) : Prop :=
  (∀ z, W.1 z = none → D.1 z = D'.1 z) ∧ (∀ x, W.2.1 x = none → D.2.1 x = D'.2.1 x) ∧
    ∀ x, W.2.2 x = none → D.2.2 x = D'.2.2 x

/-- **The database event depends only on the cells off `tableHw L`.** -/
theorem hitView_congr (L : HonestTable) (D D' : DbReg X Z) (h : OffCells (tableHw L) D D') :
    HitView L D.toDbs.fill ↔ HitView L D'.toDbs.fill := by
  have hO : OffAgree (tableHw L) D.toDbs.fill D'.toDbs.fill :=
    ⟨fun z hz ↦ congrArg (fun o ↦ Option.getD o 0) (h.1 z hz),
      fun x hx ↦ congrArg (fun o ↦ Option.getD o 0) (h.2.1 x hx),
      fun x hx ↦ congrArg (fun o ↦ Option.getD o 0) (h.2.2 x hx)⟩
  exact ⟨hitView_of_offAgree hO.symm, hitView_of_offAgree hO⟩

/-- **On a register whose hardwired cells lie in `tableHw L`, the trial hit is the database
event**: the view agrees with the databases off `tableHw L`. -/
theorem hitView_of_trialHit {L : HonestTable} {s : HwReg X Z (Finset HPos × Selections)}
    (hle : Quantum.Sponge.HwLe s.2.1 (tableHw L)) (hs : s ∈ TrialHit L) :
    HitView L s.1.toDbs.fill := by
  refine hitView_of_offAgree (t' := regFns s) ⟨fun z hz ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩ hs
  · have hW : s.2.1.1 z = none := by
      rcases hw : s.2.1.1 z with _ | a
      · rfl
      · rw [hle.1 z a hw] at hz
        cases hz
    show (s.1.1 z).getD 0 = ((s.2.1.1 z).or (s.1.1 z)).getD 0
    rw [hW]
    rfl
  · have hW : s.2.1.2.1 x = none := by
      rcases hw : s.2.1.2.1 x with _ | a
      · rfl
      · rw [hle.2.1 x a hw] at hx
        cases hx
    show (s.1.2.1 x).getD 0 = ((s.2.1.2.1 x).or (s.1.2.1 x)).getD 0
    rw [hW]
    rfl
  · have hW : s.2.1.2.2 x = none := by
      rcases hw : s.2.1.2.2 x with _ | a
      · rfl
      · rw [hle.2.2 x a hw] at hx
        cases hx
    show (s.1.2.2 x).getD 0 = ((s.2.1.2.2 x).or (s.1.2.2 x)).getD 0
    rw [hW]
    rfl

/-- The registers whose databases hit a trial. -/
def trialEvent (L : HonestTable) : Set (HwReg X Z (Finset HPos × Selections)) :=
  {s | HitView L s.1.toDbs.fill}

/-- **The trial-hit mass is at most the mass of the database event.** -/
theorem trialHitMass_le_eventMassDec (m₀ : Finset HPos × Selections) (A : Adversary (X × Z))
    (L : HonestTable) :
    trialHitMass m₀ A L ≤ @eventMassDec m₀ A L (trialEvent L) (Classical.decPred _) := by
  have hρ := supp_init_hw m₀ (tableHw L)
  have hx := forallQueries_of_progsIn (tableHw L) (valueAt L) m₀ .instruments
    (gameT Selections cwUpd (pubOf L) A)
    (progsIn_gameT (tableHw L) (valueAt L) cwUpd (progsOf_tableHw L) A) _ hρ
  unfold trialHitMass eventMassDec QuantumRuntime.eventWeight decProj
  refine ENNReal.tsum_le_tsum fun p ↦ ENNReal.ofReal_le_ofReal ?_
  have hsupp := supp_run_cutR m₀ (tableHw L) .instruments (wGame A L) hρ p
  rw [← run_cutR m₀ (tableHw L) .instruments (wGame A L) _ hx p] at hsupp
  exact re_trace_conj_kron_proj_le (compressReg X Z (Finset HPos × Selections))
    compressReg_mul_self conjTranspose_compressReg (· ∈ TrialHit L) (· ∈ trialEvent L)
    {s | Quantum.Sponge.HwLe s.2.1 (tableHw L)}
    (((runtimeR m₀).run .instruments (wGame A L)).posSemidef_branch_apply p
      (initU_posSemidef (X := X) (Z := Z) m₀))
    (supp_conj_compressReg (P := fun b ↦ Quantum.Sponge.HwLe b.1 (tableHw L)) hsupp)
    fun _ hs ht ↦ hitView_of_trialHit hs ht

open Classical in
/-- **The decompressed uniformity of the databases** (open; agent DecUniform): along the game, an
event of the databases determined by their cells off `tableHw L` has decompressed weight at most
its fraction of the total tables. -/
def DecUniformHyp (m₀ : Finset HPos × Selections) (A : Adversary (X × Z)) (L : HonestTable) :
    Prop :=
  ∀ F : DbReg X Z → Prop, (∀ D D', OffCells (tableHw L) D D' → (F D ↔ F D')) →
    @eventMassDec m₀ A L {s | F s.1} (Classical.decPred _) ≤
      ((Finset.univ.filter fun t : (Z → X) × (X → Z) × (X → Z) ↦ F (ofFunDbs t)).card : ℝ≥0∞) /
        Fintype.card ((Z → X) × (X → Z) × (X → Z))

end dbEvent

/-! ## Counting over the total tables -/

section count

variable {X₁ Z₁ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
  [AddCommGroup X₁] [AddCommGroup Z₁]

/-- A one-block trial at block `x` hits a `k'` cell of `K'` or an `h` cell of `H`. -/
def BadBlk (π : Equiv.Perm (X₁ × Z₁)) (K' : Finset X₁) (H : Finset Z₁) (x : X₁)
    (t : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁)) : Prop :=
  (π (x, t.2.1 x)).1 ∈ K' ∨ (π (x, t.2.1 x)).2 + t.2.2 (π (x, t.2.1 x)).1 ∈ H

instance instDecidableBadBlk (π : Equiv.Perm (X₁ × Z₁)) (K' : Finset X₁) (H : Finset Z₁)
    (x : X₁) : DecidablePred (BadBlk π K' H x) := fun t ↦ by
  unfold BadBlk
  infer_instance

omit [Fintype X₁] [DecidableEq Z₁] [AddCommGroup X₁] in
theorem sum_rate_mem_le {π : Equiv.Perm (X₁ × Z₁)} {G : ℕ} (hπ : PermGood π G) (x : X₁)
    (K' : Finset X₁) : ∑ b : Z₁, (if (π (x, b)).1 ∈ K' then 1 else 0) ≤ G * K'.card := by
  have e : ∀ b : Z₁, (if (π (x, b)).1 ∈ K' then (1 : ℕ) else 0) =
      ∑ x2 ∈ K', if (π (x, b)).1 = x2 then 1 else 0 :=
    fun b ↦ (Finset.sum_ite_eq K' _ fun _ ↦ (1 : ℕ)).symm
  rw [Finset.sum_congr rfl fun b _ ↦ e b, Finset.sum_comm]
  calc ∑ x2 ∈ K', ∑ b : Z₁, (if (π (x, b)).1 = x2 then 1 else 0) ≤ ∑ _x2 ∈ K', G :=
        Finset.sum_le_sum fun x2 _ ↦ by
          rw [← Finset.card_filter]
          exact hπ.rate x x2
    _ = G * K'.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

omit [Fintype X₁] [DecidableEq X₁] [AddCommGroup X₁] in
theorem sum_add_mem_le (c : Z₁) (H : Finset Z₁) :
    ∑ b : Z₁, (if c + b ∈ H then 1 else 0) ≤ H.card := by
  rw [← Finset.card_filter]
  exact Finset.card_le_card_of_injOn (fun b ↦ c + b)
    (fun b hb ↦ Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2)
    fun b₁ _ b₂ _ e ↦ add_left_cancel e

/-- A value at a fixed point in a set of at most `D` values: at most `D / |B|` of the functions. -/
theorem card_mul_sum_apply_le {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] (a : A)
    (P : B → Prop) [DecidablePred P] {D : ℕ} (hD : ∑ b, (if P b then 1 else 0) ≤ D) :
    Fintype.card B * ∑ f : A → B, (if P (f a) then 1 else 0) ≤ Fintype.card (A → B) * D :=
  card_mul_sum_le_of_moving (fun f ↦ P (f a)) (fun _ ↦ True) (fun f ↦ P (f a)) (fun _ ↦ a) D
    (fun _ hf ↦ ⟨trivial, hf⟩) (fun _ _ _ ↦ ⟨trivial, rfl⟩)
    (fun _ _ ↦ by simp only [Function.update_self]; exact hD)

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [AddCommGroup X₁]
  [AddCommGroup Z₁] in
/-- A sum over three coordinates of a term in the last two. -/
theorem sum_triple_eq {α β : Type} [Fintype α] [Fintype β] (a : β → ℕ) (b : β → β → ℕ) :
    ∑ t : α × β × β, (a t.2.1 + b t.2.1 t.2.2) =
      Fintype.card α * (Fintype.card β * ∑ k, a k + ∑ k, ∑ k', b k k') := by
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.sum_prod_type]
  dsimp only
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Finset.mul_sum]

omit [AddCommGroup X₁] in
/-- **One trial block**: at most `(G |K'| + |H|) / |Z|` of the total tables. -/
theorem card_mul_sum_badBlk_le {π : Equiv.Perm (X₁ × Z₁)} {G : ℕ} (hπ : PermGood π G)
    (K' : Finset X₁) (H : Finset Z₁) (x : X₁) :
    Fintype.card Z₁ * ∑ t : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁),
        (if BadBlk π K' H x t then 1 else 0) ≤
      Fintype.card ((Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁)) * (G * K'.card + H.card) := by
  have hA := card_mul_sum_apply_le x (fun b ↦ (π (x, b)).1 ∈ K') (sum_rate_mem_le hπ x K')
  have hB : ∀ k : X₁ → Z₁, Fintype.card Z₁ * ∑ k' : X₁ → Z₁,
      (if (π (x, k x)).2 + k' (π (x, k x)).1 ∈ H then 1 else 0) ≤
        Fintype.card (X₁ → Z₁) * H.card := fun k ↦
    card_mul_sum_apply_le (π (x, k x)).1 (fun b ↦ (π (x, k x)).2 + b ∈ H) (sum_add_mem_le _ H)
  have hle : ∀ t : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁), (if BadBlk π K' H x t then 1 else 0) ≤
      (if (π (x, t.2.1 x)).1 ∈ K' then 1 else 0) +
        (if (π (x, t.2.1 x)).2 + t.2.2 (π (x, t.2.1 x)).1 ∈ H then 1 else 0) := fun t ↦ by
    unfold BadBlk
    split_ifs <;> simp_all
  calc Fintype.card Z₁ * ∑ t : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁),
        (if BadBlk π K' H x t then 1 else 0)
      ≤ Fintype.card Z₁ * ∑ t : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁),
          ((if (π (x, t.2.1 x)).1 ∈ K' then 1 else 0) +
            (if (π (x, t.2.1 x)).2 + t.2.2 (π (x, t.2.1 x)).1 ∈ H then 1 else 0)) :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum fun t _ ↦ hle t)
    _ = Fintype.card Z₁ * (Fintype.card (Z₁ → X₁) * (Fintype.card (X₁ → Z₁) *
          ∑ k : X₁ → Z₁, (if (π (x, k x)).1 ∈ K' then 1 else 0) +
          ∑ k : X₁ → Z₁, ∑ k' : X₁ → Z₁,
            (if (π (x, k x)).2 + k' (π (x, k x)).1 ∈ H then 1 else 0))) :=
        congrArg (Fintype.card Z₁ * ·)
          (sum_triple_eq (fun k : X₁ → Z₁ ↦ if (π (x, k x)).1 ∈ K' then 1 else 0)
            fun k k' : X₁ → Z₁ ↦ if (π (x, k x)).2 + k' (π (x, k x)).1 ∈ H then 1 else 0)
    _ = Fintype.card (Z₁ → X₁) * (Fintype.card (X₁ → Z₁) * (Fintype.card Z₁ *
          ∑ k : X₁ → Z₁, (if (π (x, k x)).1 ∈ K' then 1 else 0))) +
        Fintype.card (Z₁ → X₁) * (Fintype.card Z₁ * ∑ k : X₁ → Z₁, ∑ k' : X₁ → Z₁,
          (if (π (x, k x)).2 + k' (π (x, k x)).1 ∈ H then 1 else 0)) := by ring
    _ ≤ Fintype.card (Z₁ → X₁) * (Fintype.card (X₁ → Z₁) *
          (Fintype.card (X₁ → Z₁) * (G * K'.card))) +
        Fintype.card (Z₁ → X₁) * ∑ _k : X₁ → Z₁, Fintype.card (X₁ → Z₁) * H.card :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hA))
          (Nat.mul_le_mul_left _ (by
            rw [Finset.mul_sum]
            exact Finset.sum_le_sum fun k _ ↦ hB k))
    _ = Fintype.card ((Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁)) * (G * K'.card + H.card) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_prod, Fintype.card_prod]
        ring

omit [AddCommGroup X₁] in
/-- **The union over the trial blocks.** -/
theorem card_mul_card_filter_le_of_blocks {π : Equiv.Perm (X₁ × Z₁)} {G : ℕ}
    (hπ : PermGood π G) (K' : Finset X₁) (H : Finset Z₁) (Bl : Finset X₁)
    (F : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁) → Prop) [DecidablePred F]
    (hF : ∀ t, F t → ∃ x ∈ Bl, BadBlk π K' H x t) :
    Fintype.card Z₁ * (Finset.univ.filter F).card ≤
      Fintype.card ((Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁)) * (Bl.card * (G * K'.card + H.card)) := by
  have h1 : (Finset.univ.filter F).card ≤
      ∑ x ∈ Bl, ∑ t, (if BadBlk π K' H x t then 1 else 0) := by
    rw [Finset.card_filter, Finset.sum_comm]
    refine Finset.sum_le_sum fun t _ ↦ ?_
    split_ifs with ht
    · obtain ⟨x, hx, hb⟩ := hF t ht
      exact le_trans (by rw [ite_eq_left hb])
        (Finset.single_le_sum (f := fun x ↦ if BadBlk π K' H x t then 1 else 0)
          (fun _ _ ↦ Nat.zero_le _) hx)
    · exact Nat.zero_le _
  calc Fintype.card Z₁ * (Finset.univ.filter F).card
      ≤ Fintype.card Z₁ * ∑ x ∈ Bl, ∑ t, (if BadBlk π K' H x t then 1 else 0) :=
        Nat.mul_le_mul_left _ h1
    _ = ∑ x ∈ Bl, Fintype.card Z₁ * ∑ t, (if BadBlk π K' H x t then 1 else 0) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ _x ∈ Bl, Fintype.card ((Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁)) *
          (G * K'.card + H.card) :=
        Finset.sum_le_sum fun x _ ↦ card_mul_sum_badBlk_le hπ K' H x
    _ = _ := by
        rw [Finset.sum_const, smul_eq_mul]
        ring

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] in
/-- The reads of a one-block evaluation: its `k`, `k'` and `h` points. -/
theorem point_of_mem_spongeReads_single (π : Equiv.Perm (X₁ × Z₁)) (h : Z₁ → X₁)
    (k k' : X₁ → Z₁) (x : X₁) {rd : SpongeRead X₁ Z₁} (hrd : rd ∈ spongeReads π h k k' [x]) :
    rd.point = .k x ∨ rd.point = .k' (π (x, k x)).1 ∨
      rd.point = .h ((π (x, k x)).2 + k' (π (x, k x)).1) := by
  have e : spongeReads π h k k' [x] = [] ++ roundReads π h k k' (0, 0) x := rfl
  rw [e, List.nil_append] at hrd
  simp only [roundReads, zero_add, List.mem_cons, List.not_mem_nil, or_false] at hrd
  rcases hrd with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- From the fraction count to the `ℝ≥0∞` fractions. -/
theorem natCast_div_le_div_of_mul_le {a b c d : ℕ} (ha : 0 < a) (hc : 0 < c)
    (h : a * b ≤ c * d) : (b : ℝ≥0∞) / c ≤ (d : ℝ≥0∞) / a := by
  have ha' : (a : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha.ne'
  have hc' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  calc (b : ℝ≥0∞) / c = ((a * b : ℕ) : ℝ≥0∞) / ((a * c : ℕ) : ℝ≥0∞) := by
        push_cast
        rw [ENNReal.mul_div_mul_left _ _ ha' (ENNReal.natCast_ne_top a)]
    _ ≤ ((c * d : ℕ) : ℝ≥0∞) / ((a * c : ℕ) : ℝ≥0∞) := by
        gcongr
    _ = (d : ℝ≥0∞) / a := by
        push_cast
        rw [mul_comm (a : ℝ≥0∞), ENNReal.mul_div_mul_left _ _ hc' (ENNReal.natCast_ne_top c)]

end count

/-! ## leanXMSS: the trial blocks and the cells of `tableHw L` -/

section xmss

/-- The values a slot's ports are realized at. -/
noncomputable def slotVals (L : HonestTable) (s : Slot) : ValPos → Digest :=
  extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))

/-- The `k'` cells of the in-table paths (by output position and round). -/
noncomputable def k'Cells (L : HonestTable) : Finset X :=
  Finset.univ.image fun q : ValPos × Fin 8 ↦
    (roundK' (pubOf L) (outSlot q.1) (slotVals L (outSlot q.1)) q.2).1

/-- The `h` cells of the in-table paths. -/
noncomputable def hCells (L : HonestTable) : Finset Z :=
  Finset.univ.image fun q : ValPos × Fin 8 ↦
    (roundH (pubOf L) (outSlot q.1) (slotVals L (outSlot q.1)) q.2).1

/-- The blocks of the top trials. -/
noncomputable def trialBlocks (L : HonestTable) : Finset X :=
  Finset.univ.image fun q : KeyIndex × Fin randomizerAttemptLimit ↦
    (blocks (topTrial L q.1 q.2)).headD 0

theorem mem_k'Cells_of (L : HonestTable) (q : ValPos × Fin 8) :
    (roundK' (pubOf L) (outSlot q.1) (slotVals L (outSlot q.1)) q.2).1 ∈ k'Cells L := by
  simp only [k'Cells, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨q, rfl⟩

theorem mem_hCells_of (L : HonestTable) (q : ValPos × Fin 8) :
    (roundH (pubOf L) (outSlot q.1) (slotVals L (outSlot q.1)) q.2).1 ∈ hCells L := by
  simp only [hCells, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨q, rfl⟩

theorem mem_trialBlocks_of (L : HonestTable) (q : KeyIndex × Fin randomizerAttemptLimit) :
    (blocks (topTrial L q.1 q.2)).headD 0 ∈ trialBlocks L := by
  simp only [trialBlocks, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨q, rfl⟩

theorem card_k'Cells_le (L : HonestTable) : (k'Cells L).card ≤ 8 * (498 * 2 ^ 32) :=
  Finset.card_image_le.trans (by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    exact (Nat.mul_le_mul_right 8 card_valPos_le).trans_eq (by ring))

theorem card_hCells_le (L : HonestTable) : (hCells L).card ≤ 8 * (498 * 2 ^ 32) :=
  Finset.card_image_le.trans (by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    exact (Nat.mul_le_mul_right 8 card_valPos_le).trans_eq (by ring))

theorem card_trialBlocks_le (L : HonestTable) : (trialBlocks L).card ≤ 2 ^ 64 :=
  Finset.card_image_le.trans (by
    rw [Finset.card_univ, Fintype.card_prod, card_keyIndex, Fintype.card_fin]
    unfold randomizerAttemptLimit
    norm_num)

attribute [irreducible] k'Cells hCells trialBlocks

theorem nBlocks_le_eight {s : Slot} (hs : InTable s) (pub : Pub) : nBlocks pub s ≤ 8 := by
  cases s with
  | chain l e step i => rw [nBlocks_chain]; omega
  | leaf l e => rw [nBlocks_leaf]
  | node l level index => rw [nBlocks_node]; omega
  | msg => exact hs.elim
  | prf => exact hs.elim
  | rnd => exact hs.elim
  | param => exact hs.elim
  | seed => exact hs.elim

/-- A realized program port of a slot programs a `k`, `k'` or `h` cell of a round of its path. -/
theorem realize_of_mem_slotPorts {L : HonestTable} {s : Slot} {p : LazyProg X Z HPos XD}
    (hp : p ∈ slotPorts (pubOf L) s) : ∃ j < nBlocks (pubOf L) s,
      p.realize (valueAt L) = .programK (roundK (pubOf L) s (slotVals L s) j).1
        (roundK (pubOf L) s (slotVals L s) j).2 ∨
      p.realize (valueAt L) = .programK' (roundK' (pubOf L) s (slotVals L s) j).1
        (roundK' (pubOf L) s (slotVals L s) j).2 ∨
      p.realize (valueAt L) = .programH (roundH (pubOf L) s (slotVals L s) j).1
        (roundH (pubOf L) s (slotVals L s) j).2 := by
  simp only [slotPorts, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  obtain ⟨j, hj, rfl | rfl | rfl⟩ := hp
  · exact ⟨j, hj, Or.inl rfl⟩
  · exact ⟨j, hj, Or.inr (Or.inl rfl)⟩
  · exact ⟨j, hj, Or.inr (Or.inr rfl)⟩

/-- The cells of `tableHw L` are those of the realized ports of the in-table slots. -/
theorem exists_of_mem_progSet {L : HonestTable} {c : HwProg X Z} (h : c ∈ progSet L) :
    ∃ s, InTable s ∧ ∃ j < nBlocks (pubOf L) s,
      c = .programK (roundK (pubOf L) s (slotVals L s) j).1
        (roundK (pubOf L) s (slotVals L s) j).2 ∨
      c = .programK' (roundK' (pubOf L) s (slotVals L s) j).1
        (roundK' (pubOf L) s (slotVals L s) j).2 ∨
      c = .programH (roundH (pubOf L) s (slotVals L s) j).1
        (roundH (pubOf L) s (slotVals L s) j).2 := by
  simp only [progSet, Set.mem_ofPred_eq] at h
  obtain ⟨l, e, w, s, he, hs, p, hp, hpc⟩ := h
  obtain ⟨j, hj, hr⟩ := realize_of_mem_slotPorts hp
  rw [hpc] at hr
  exact ⟨s, inTable_of_mem_layerSlots he hs, j, hj, hr⟩

theorem exists_programK'_of_tableHw {L : HonestTable} {y : X} (h : (tableHw L).2.2 y ≠ none) :
    ∃ a, HwProg.programK' y a ∈ progSet L := by
  by_contra hne
  apply h
  unfold tableHw
  dsimp only
  exact ite_eq_right hne

theorem exists_programH_of_tableHw {L : HonestTable} {z : Z} (h : (tableHw L).1 z ≠ none) :
    ∃ a, HwProg.programH z a ∈ progSet L := by
  by_contra hne
  apply h
  unfold tableHw
  dsimp only
  exact ite_eq_right hne

theorem mem_k'Cells {L : HonestTable} {y : X} (h : (tableHw L).2.2 y ≠ none) :
    y ∈ k'Cells L := by
  obtain ⟨a, ha⟩ := exists_programK'_of_tableHw h
  obtain ⟨s, hin, j, hj, hr⟩ := exists_of_mem_progSet ha
  rcases hr with hr | hr | hr
  · cases hr
  · injection hr with hy _
    have hm := mem_k'Cells_of L (slotOutPos s, ⟨j, hj.trans_le (nBlocks_le_eight hin _)⟩)
    dsimp only at hm
    rw [outSlot_slotOutPos hin] at hm
    rw [hy]
    exact hm
  · cases hr

theorem mem_hCells {L : HonestTable} {z : Z} (h : (tableHw L).1 z ≠ none) : z ∈ hCells L := by
  obtain ⟨a, ha⟩ := exists_programH_of_tableHw h
  obtain ⟨s, hin, j, hj, hr⟩ := exists_of_mem_progSet ha
  rcases hr with hr | hr | hr
  · cases hr
  · cases hr
  · injection hr with hy _
    have hm := mem_hCells_of L (slotOutPos s, ⟨j, hj.trans_le (nBlocks_le_eight hin _)⟩)
    dsimp only at hm
    rw [outSlot_slotOutPos hin] at hm
    rw [hy]
    exact hm

/-- A top trial is one top trial block. -/
theorem exists_blocks_topTrial (L : HonestTable) (e : KeyIndex) (n : ℕ) :
    ∃ x, blocks (topTrial L e n) = [x] ∧ TopTrialBlock x := by
  have hm : (topMsg L e).length ≤ 32 := by
    show (littleEndianBytes 16 _).length ≤ 32
    rw [length_le16]
    omega
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp
    (length_blocks_msgInput L.param topLayer e hm (topBase L e + BitVec.ofNat digestBits n))
  exact ⟨x, hx, L.param, e, L.treeValue bottomLayer layerHeight e.val, _, hx⟩

/-- **A trial hit of the tables is a hit of a `k'` or `h` cell at a trial block** (`TrialsOff`: no
trial block is a `k` cell of `tableHw L`). -/
theorem badBlk_of_hitView {L : HonestTable} (hoff : TrialsOff L) {t : SpongeKeys X Z}
    (h : HitView L t) : ∃ x ∈ trialBlocks L, BadBlk L.perm (k'Cells L) (hCells L) x t := by
  obtain ⟨e, -, n, hn, rd, hrd, hin⟩ := h
  obtain ⟨x, hx, hT⟩ := exists_blocks_topTrial L e n
  have hmem : x ∈ trialBlocks L := by
    have h := mem_trialBlocks_of L (e, ⟨n, hn⟩)
    dsimp only at h
    rw [hx] at h
    exact h
  refine ⟨x, hmem, ?_⟩
  have hrd' : rd ∈ spongeReads L.perm t.1 t.2.1 t.2.2 [x] := by
    have he : inputReads t L.perm (topTrial L e n) =
        spongeReads L.perm t.1 t.2.1 t.2.2 (blocks (topTrial L e n)) := rfl
    rw [he, hx] at hrd
    exact hrd
  rcases point_of_mem_spongeReads_single L.perm t.1 t.2.1 t.2.2 x hrd' with hp | hp | hp <;>
    rw [hp] at hin
  · exact absurd (hoff x hT) hin
  · exact Or.inl (mem_k'Cells hin)
  · exact Or.inr (mem_hCells hin)

variable {m₀ : Finset HPos × Selections} {A : Adversary (X × Z)} {L : HonestTable}

open Classical in
/-- **The trial-hit mass, counted**: at most `|trialBlocks| (18 |k'Cells| + |hCells|) / |Z|`. -/
theorem trialHitMass_le_frac (hU : DecUniformHyp m₀ A L) (hoff : TrialsOff L)
    (hπ : PermGood L.perm 18) :
    trialHitMass m₀ A L ≤ (((trialBlocks L).card * (18 * (k'Cells L).card + (hCells L).card) :
      ℕ) : ℝ≥0∞) / Fintype.card Z := by
  unfold DecUniformHyp at hU
  refine (trialHitMass_le_eventMassDec m₀ A L).trans
    ((hU (fun D ↦ HitView L D.toDbs.fill) (hitView_congr L)).trans ?_)
  exact natCast_div_le_div_of_mul_le Fintype.card_pos Fintype.card_pos
    (card_mul_card_filter_le_of_blocks hπ (k'Cells L) (hCells L) (trialBlocks L)
      (fun t ↦ HitView L (ofFunDbs t).toDbs.fill) fun _ ht ↦ badBlk_of_hitView hoff ht)

set_option exponentiation.threshold 4096 in
/-- The count at Keccak's sizes: `2^113 / 2^512`. -/
theorem trialHitTerm_le {b k h cZ : ℕ} (hb : b ≤ 2 ^ 64) (hk : k ≤ 8 * (498 * 2 ^ 32))
    (hh : h ≤ 8 * (498 * 2 ^ 32)) (hZ : cZ = 2 ^ 512) :
    ((b * (18 * k + h) : ℕ) : ℝ≥0∞) / cZ ≤ ENNReal.ofReal (1 / 2 ^ 399) := by
  subst hZ
  have hK : b * (18 * k + h) ≤ 2 ^ 113 :=
    calc b * (18 * k + h) ≤ 2 ^ 64 * (18 * (8 * (498 * 2 ^ 32)) + 8 * (498 * 2 ^ 32)) := by
          gcongr
      _ ≤ 2 ^ 113 := by norm_num
  rw [natCast_div_eq_ofReal _ (2 ^ 512) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc ((b * (18 * k + h) : ℕ) : ℝ) / ((2 ^ 512 : ℕ) : ℝ) ≤ 2 ^ 113 / 2 ^ 512 := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hK) (by positivity)
    _ ≤ 1 / 2 ^ 399 := by norm_num

/-- **The trial-hit mass at Keccak's sizes**: at most `2^-399` on a table with `TrialsOff L` and
`PermGood L.perm 18`, given the decompressed uniformity. -/
theorem trialHitMass_le_keccak (hU : DecUniformHyp m₀ A L) (hoff : TrialsOff L)
    (hπ : PermGood L.perm 18) : trialHitMass m₀ A L ≤ ENNReal.ofReal (1 / 2 ^ 399) :=
  (trialHitMass_le_frac hU hoff hπ).trans
    (trialHitTerm_le (card_trialBlocks_le L) (card_k'Cells_le L) (card_hCells_le L) rnCard_Z)

/-- **The averaged trial-hit mass**: at most `2^-399` over the tables of a set on which the
hypotheses hold. -/
theorem uavg_trialHitMass_le (good : HonestTable → Prop) [DecidablePred good]
    (hg : ∀ L, good L → DecUniformHyp m₀ A L ∧ TrialsOff L ∧ PermGood L.perm 18) :
    uavg (fun L ↦ if good L then trialHitMass m₀ A L else 0) ≤ ENNReal.ofReal (1 / 2 ^ 399) :=
  (uavg_mono fun L ↦ by
    split_ifs with h
    · exact trialHitMass_le_keccak (hg L h).1 (hg L h).2.1 (hg L h).2.2
    · exact zero_le).trans (uavg_const _).le

end xmss

end Quantum.Xmss.Assembly

end
