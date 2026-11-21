module

public import Quantum.Xmss.Hybrid.Coins
public import Quantum.Xmss.Hybrid.ViewBy

@[expose] public section

/-!
# Hiding the scheme seed inside runtime 2 with coins

`uavg_win_runtime1_le_coins` (`Quantum.Xmss.Hybrid.Coins`) takes the averaged mass of the coin
cells in the run against `runtime2Coins (Lc θ)` as a hypothesis. The coin table `Lc θ` sits at
cells that depend on the scheme seed (the randomizer bases' paths), so the runtime itself depends
on the hidden value and View's averaged view lemma (one runtime for all tables) does not apply.
This file discharges that hypothesis.

* `avg_queryWeight_le_fam` (**the view lemma for a family of runtimes**): `avg_queryWeight_le`
  with a runtime `R p` that depends on the public part `p`.
* **Coin reads as public classical steps.** At a coin cell that is not hardwired, the read of
  `runtime2Coins Lc` returns the coin and leaves the database alone: its Kraus entries depend on
  the cell only through the coin value (`hwReadKraus1_readH_apply_eq` and its `k`, `k'` forms). A
  template program over `coinSpec` names coins `u` instead of cells (`CoinRead`); a placement
  (`CoinPlacement`) puts them at cells (`placeCoins`). Two placements whose coin tables hold the
  same coins (`CoinsMatch`) run the template alike (`queryWeight_coinMass_placeCoins_eq`), as long
  as every call is presented an operator on which the coin cells are not hardwired and the ordinary
  reads avoid the coin cells (`CoinsOK`, a `ForallQueries` hypothesis). `forallQueries_coinsOK`
  derives it from a condition on the ports alone (`CoinsPortOK`: ordinary reads off both coin
  tables, program ports off both placements' coin cells), by a support invariant of the register
  (`forallQueries_suppOn`). Placing the coins at reference cells chosen from the public part, with
  their values public coins, makes the run a function of the public part.
* `uavg_coinMass_le` (**the coin-cell mass**): with the coin hidden sets each containing a cell for
  at most `κ` hidden values, the averaged coin mass of the `j`-th call is at most `κ / |V|` plus
  the fraction of tables outside the good set. `uavg_coinMass_seed_le`: hidden value the scheme
  seed, `κ / 2^256`; `uavg_coinMass_schemeSeed_le`: the seed-keyed `k`-cells (`seedKeyCells`, the
  randomizer bases' first blocks among them), `2^-256`.
* **The coin mass, not the hidden mass, at the coin cells.** At a read of a coin cell that is not
  hardwired, the hidden mass of `Coins`' hypothesis `hε` is the whole trace, so `hε` fails for the
  coin cells the challenger reads. `uavg_win_runtime1_le_coins_coinMass` is
  `uavg_win_runtime1_le_coins` with `hε` on `coinMass`, which vanishes at the reads of the coin
  table; `uavg_coinMass_le` is in that form.
-/

open Matrix
open scoped Kronecker ENNReal ComplexOrder

universe u v w u₁ v₁

namespace Quantum.Xmss.Hybrid

open Quantum QuantumRuntime Quantum.Sponge

/-! ## The view lemma for a family of runtimes -/

section family

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} (I : L.Interp)
  {Ω : QReg → Type w} {A : QReg}

/-- **The view lemma, averaged, for runtimes depending on the public data.** As
`avg_queryWeight_le`, with the run of the public data `p` against its own runtime `R p`: if on `G`
the weight of the `j`-th call is at most the weight `w p v` of the run of `x p` from `ρ p` against
`R p`, and the weights `w p v` add up over the hidden values to at most `c` times the trace, the
average is at most `c / |V|` plus the fraction of tables outside `G`. -/
theorem avg_queryWeight_le_fam {Θ P V : Type*} [Fintype Θ] [Fintype P] [Fintype V]
    (e : Θ ≃ P × V) (f : Θ → ℝ≥0∞) (R : P → QuantumRuntime spec)
    (x : P → QuantumComp L spec Ω A) (ρ : ∀ p, Matrix (A × (R p).D) (A × (R p).D) ℂ)
    (hρ : ∀ p, (ρ p).PosSemidef) (hρ₁ : ∀ p, ENNReal.ofReal (ρ p).trace.re ≤ 1)
    (w : ∀ p, V → ∀ i, Matrix (spec.In i × (R p).D) (spec.In i × (R p).D) ℂ → ℝ≥0∞)
    (c : ℝ≥0∞) (hw : ∀ p i σ, σ.PosSemidef → ∑ v, w p v i σ ≤ c * ENNReal.ofReal σ.trace.re)
    (j : ℕ) (G : Finset Θ)
    (hG : ∀ θ ∈ G, f θ ≤
      (R (e θ).1).queryWeight I (w (e θ).1 (e θ).2) (x (e θ).1) (ρ (e θ).1) j)
    (hB : ∀ θ ∉ G, f θ ≤ 1) :
    (Fintype.card Θ : ℝ≥0∞)⁻¹ * ∑ θ, f θ ≤
      c * (Fintype.card V : ℝ≥0∞)⁻¹ +
        (Fintype.card Θ : ℝ≥0∞)⁻¹ * ((Fintype.card Θ - G.card : ℕ) : ℝ≥0∞) := by
  classical
  rw [← Finset.card_compl G]
  set g : P × V → ℝ≥0∞ := fun q ↦ (R q.1).queryWeight I (w q.1 q.2) (x q.1) (ρ q.1) j
  have hsum : ∑ θ, g (e θ) ≤ Fintype.card P * c := by
    rw [e.sum_comp g, Fintype.sum_prod_type]
    calc ∑ p, ∑ v, g (p, v) ≤ ∑ _p : P, c * 1 := Finset.sum_le_sum fun p _ ↦
          (sum_queryWeight_le (R p) I (w p) c (hw p) (x p) (hρ p) j).trans
            (by gcongr; exact hρ₁ p)
      _ = Fintype.card P * c := by simp [Finset.card_univ]
  have hf : ∑ θ, f θ ≤ Fintype.card P * c + Gᶜ.card := by
    rw [← Finset.sum_add_sum_compl G f]
    refine add_le_add ((Finset.sum_le_sum hG).trans
      ((Finset.sum_le_sum_of_subset (Finset.subset_univ G)).trans hsum)) ?_
    calc ∑ θ ∈ Gᶜ, f θ ≤ ∑ _θ ∈ Gᶜ, (1 : ℝ≥0∞) :=
          Finset.sum_le_sum fun θ hθ ↦ hB θ (Finset.mem_compl.mp hθ)
      _ = Gᶜ.card := by simp
  rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul]
  calc ((Fintype.card P : ℝ≥0∞) * Fintype.card V)⁻¹ * ∑ θ, f θ
      ≤ ((Fintype.card P : ℝ≥0∞) * Fintype.card V)⁻¹ * (Fintype.card P * c + Gᶜ.card) := by
        gcongr
    _ = ((Fintype.card P : ℝ≥0∞) * Fintype.card V)⁻¹ * (Fintype.card P * c) +
          ((Fintype.card P : ℝ≥0∞) * Fintype.card V)⁻¹ * Gᶜ.card := mul_add _ _ _
    _ ≤ c * (Fintype.card V : ℝ≥0∞)⁻¹ +
          ((Fintype.card P : ℝ≥0∞) * Fintype.card V)⁻¹ * Gᶜ.card := by
        refine add_le_add ?_ le_rfl
        rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
          (Or.inl (ENNReal.natCast_ne_top _))]
        by_cases hP : (Fintype.card P : ℝ≥0∞) = 0
        · simp [hP]
        · refine le_of_eq ?_
          rw [show (Fintype.card P : ℝ≥0∞)⁻¹ * (Fintype.card V : ℝ≥0∞)⁻¹ * (Fintype.card P * c) =
              ((Fintype.card P : ℝ≥0∞)⁻¹ * Fintype.card P) *
                (c * (Fintype.card V : ℝ≥0∞)⁻¹) by ring,
            ENNReal.inv_mul_cancel hP (ENNReal.natCast_ne_top _), one_mul]

/-- **Only the presented operators matter, for query weights.** Two runtimes on one register whose
framed steps agree on the operators satisfying `P`, and whose weights agree on the inputs of calls
presented such operators, give the same `j`-th call weights to a program every call of whose run
against the first runtime is presented an operator satisfying `P`. -/
theorem queryWeight_eq_of_forallQueries {D : QReg} {σ₁ σ₂ : SubState D}
    {s₁ s₂ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
    {P : ∀ (i : spec.Port) (E : QReg), Matrix ((spec.In i × D) × E) ((spec.In i × D) × E) ℂ → Prop}
    (hs : ∀ i E σ, P i E σ → ∀ r, ((s₁ i).frame E).branch r σ = ((s₂ i).frame E).branch r σ)
    {w₁ w₂ : ∀ i, Matrix (spec.In i × D) (spec.In i × D) ℂ → ℝ≥0∞}
    (hw : ∀ i E σ, P i E σ →
      w₁ i (MatrixMap.traceRight (spec.In i × D) E σ) =
        w₂ i (MatrixMap.traceRight (spec.In i × D) E σ))
    {x : QuantumComp L spec Ω A} {ρ : Matrix (A × D) (A × D) ℂ}
    (hx : (QuantumRuntime.mk D σ₁ s₁).ForallQueries I P x ρ) (j : ℕ) :
    (QuantumRuntime.mk D σ₁ s₁).queryWeight I w₁ x ρ j =
      (QuantumRuntime.mk D σ₂ s₂).queryWeight I w₂ x ρ j := by
  induction x using QuantumComp.inductionOn generalizing j with
  | pure _ _ => rw [queryWeight_pure, queryWeight_pure]
  | primBind _ o k ih =>
    rw [queryWeight_primBind, queryWeight_primBind]
    exact tsum_congr fun b ↦ ih b ((forallQueries_primBind_iff I o k _).mp hx b) j
  | queryBind _ i E ℓ k ih =>
    have hx' := (forallQueries_queryBind_iff I i E ℓ k _).mp hx
    cases j with
    | zero =>
      rw [queryWeight_queryBind_zero, queryWeight_queryBind_zero]
      exact hw i E _ hx'.1
    | succ j =>
      rw [queryWeight_queryBind_succ, queryWeight_queryBind_succ]
      refine tsum_congr fun r ↦ ?_
      have hq : ((QuantumRuntime.mk D σ₁ s₁).queryStep i E ℓ).branch r ρ =
          ((QuantumRuntime.mk D σ₂ s₂).queryStep i E ℓ).branch r ρ := by
        rw [queryStep_branch_apply, queryStep_branch_apply]
        exact congrArg _ (hs i E _ hx'.1 r)
      rw [← hq]
      exact ih r (hx'.2 r) j

end family

/-! ## Kraus maps agreeing on a support -/

section support

/-- Two Kraus maps whose operators agree on the columns in `G` agree on operators supported on
`G`. -/
theorem conj_eq_of_supp {α β : Type*} [Fintype α] (K K' : Matrix β α ℂ) (G : Set α)
    (hK : ∀ b a, a ∈ G → K b a = K' b a) {τ : Matrix α α ℂ}
    (hτ : ∀ a a', τ a a' ≠ 0 → a ∈ G ∧ a' ∈ G) : MatrixMap.conj K τ = MatrixMap.conj K' τ := by
  have hl : K * τ = K' * τ := by
    ext b a'
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    by_cases h : τ a a' = 0
    · simp [h]
    · rw [hK b a (hτ a a' h).1]
  have hr : τ * Kᴴ = τ * K'ᴴ := by
    ext a b
    simp only [Matrix.mul_apply, conjTranspose_apply]
    refine Finset.sum_congr rfl fun a' _ ↦ ?_
    by_cases h : τ a a' = 0
    · simp [h]
    · rw [hK b a' (hτ a a' h).2]
  rw [MatrixMap.conj_apply, MatrixMap.conj_apply, hl, Matrix.mul_assoc, hr, ← Matrix.mul_assoc]

/-- The same, framed by an ancilla. -/
theorem amplify_conj_eq_of_supp {α β E : Type*} [Fintype α] (K K' : Matrix β α ℂ) (G : Set α)
    (hK : ∀ b a, a ∈ G → K b a = K' b a) {σ : Matrix (α × E) (α × E) ℂ}
    (hσ : ∀ a a', σ a a' ≠ 0 → a.1 ∈ G ∧ a'.1 ∈ G) :
    (MatrixMap.conj K).amplify E σ = (MatrixMap.conj K').amplify E σ := by
  ext x y
  rw [MatrixMap.amplify_apply, MatrixMap.amplify_apply,
    conj_eq_of_supp K K' G hK (τ := σ.submatrix (·, x.2) (·, y.2))
      fun a a' h ↦ hσ (a, x.2) (a', y.2) h]

/-- A framed branch of a Kraus step. -/
theorem frame_branch_eq_amplify_conj {α β ι : Type} [Fintype α] [DecidableEq α] [Fintype β]
    (s : SubInstrument α β ι) (K : ι → Matrix β α ℂ) (h : ∀ r, s.branch r = MatrixMap.conj (K r))
    (E : QReg) (r : ι) (σ : Matrix (α × E) (α × E) ℂ) :
    (s.frame E).branch r σ = (MatrixMap.conj (K r)).amplify E σ := by
  rw [show (s.frame E).branch r = (s.branch r).amplify E from rfl, h r]

/-- An operator supported on the basis states satisfying `f`. -/
def SuppOn {α : Type*} (f : α → Prop) (σ : Matrix α α ℂ) : Prop :=
  ∀ a b, σ a b ≠ 0 → f a ∧ f b

/-- A Kraus map whose nonzero entries send states satisfying `f` to states satisfying `f'`
preserves the supports. -/
theorem suppOn_conj {α β : Type*} [Fintype α] {f : α → Prop} {f' : β → Prop}
    (K : Matrix β α ℂ) (hK : ∀ b a, K b a ≠ 0 → f a → f' b) {τ : Matrix α α ℂ}
    (hτ : SuppOn f τ) : SuppOn f' (MatrixMap.conj K τ) := by
  intro b b' h
  rw [MatrixMap.conj_apply, Matrix.mul_apply] at h
  obtain ⟨a', -, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h2 := left_ne_zero_of_mul h1
  have h3 := right_ne_zero_of_mul h1
  rw [Matrix.mul_apply] at h2
  obtain ⟨a, -, h4⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
  rw [conjTranspose_apply, star_ne_zero] at h3
  exact ⟨hK b a (left_ne_zero_of_mul h4) (hτ a a' (right_ne_zero_of_mul h4)).1,
    hK b' a' h3 (hτ a a' (right_ne_zero_of_mul h4)).2⟩

/-- A map preserving supports, framed by an ancilla on the right, preserves them. -/
theorem suppOn_amplify {α β E : Type*} {f : α → Prop} {f' : β → Prop} (Φ : MatrixMap α β)
    (hΦ : ∀ τ, SuppOn f τ → SuppOn f' (Φ τ)) {σ : Matrix (α × E) (α × E) ℂ}
    (hσ : SuppOn (fun p ↦ f p.1) σ) : SuppOn (fun p ↦ f' p.1) (Φ.amplify E σ) := by
  intro x y h
  rw [MatrixMap.amplify_apply] at h
  exact hΦ _ (fun a a' ha ↦ hσ (a, x.2) (a', y.2) ha) x.1 y.1 h

/-- Any map on the left factor preserves supports on the right factor. -/
theorem suppOn_amplify_right {α β R : Type*} {g : R → Prop} (Φ : MatrixMap α β)
    {σ : Matrix (α × R) (α × R) ℂ} (hσ : SuppOn (fun p ↦ g p.2) σ) :
    SuppOn (fun p ↦ g p.2) (Φ.amplify R σ) := by
  intro x y h
  rw [MatrixMap.amplify_apply] at h
  by_contra hn
  have h0 : σ.submatrix (·, x.2) (·, y.2) = 0 := by
    ext a a'
    rw [submatrix_apply, Matrix.zero_apply]
    by_contra ha
    exact hn ⟨(hσ _ _ ha).1, (hσ _ _ ha).2⟩
  rw [h0, map_zero] at h
  exact h rfl

/-- A relabelling carries supports along. -/
theorem suppOn_relabel {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) {f : α → Prop} {f' : β → Prop} (he : ∀ b, f (e.symm b) → f' b)
    {ρ : Matrix α α ℂ} (hρ : SuppOn f ρ) : SuppOn f' ((SubInstrument.relabel e).branch () ρ) := by
  intro a b h
  simp only [SubInstrument.relabel_branch_apply, submatrix_apply] at h
  exact ⟨he a (hρ _ _ h).1, he b (hρ _ _ h).2⟩

end support

/-! ## Support invariants of runs -/

section invariant

theorem queryEquivIn_symm_snd {A J E : Type*} (ℓ : A ≃ J × E) (D : Type*) (p : (J × D) × E) :
    ((queryEquivIn ℓ D).symm p).2 = p.1.2 := by
  obtain ⟨q, rfl⟩ := (queryEquivIn ℓ D).surjective p
  rw [Equiv.symm_apply_apply]
  rfl

theorem queryEquivOut_symm_fst_snd (O D E : Type*) (p : (O × E) × D) :
    ((queryEquivOut O D E).symm p).1.2 = p.2 := by
  obtain ⟨q, rfl⟩ := (queryEquivOut O D E).surjective p
  rw [Equiv.symm_apply_apply]
  rfl

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} (I : L.Interp)
  {Ω : QReg → Type w} {A : QReg}

/-- **A support invariant of the runtime register.** If every allowed port's steps keep operators
supported on the register states satisfying `g`, and every call of the run of `x` is of an
allowed port, then every call is presented an operator supported on such states, when the run
starts from one. -/
theorem forallQueries_suppOn (R : QuantumRuntime spec) (g : R.D → Prop)
    (Pp : spec.Port → Prop)
    (hstep : ∀ i, Pp i → ∀ r (τ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      SuppOn (fun p ↦ g p.2) τ → SuppOn (fun p ↦ g p.2) ((R.step i).branch r τ))
    {x : QuantumComp L spec Ω A} {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (hports : R.ForallQueries I (fun i _ _ ↦ Pp i) x ρ) (hρ : SuppOn (fun p ↦ g p.2) ρ) :
    R.ForallQueries I (fun i _ σ ↦ Pp i ∧ SuppOn (fun p ↦ g p.1.2) σ) x ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => trivial
  | primBind _ o k ih =>
    exact (forallQueries_primBind_iff I o k _).mpr fun b ↦
      ih b ((forallQueries_primBind_iff I o k _).mp hports b) (suppOn_amplify_right _ hρ)
  | queryBind _ i E ℓ k ih =>
    have hp := (forallQueries_queryBind_iff I i E ℓ k _).mp hports
    have hin : SuppOn (fun p : (spec.In i × R.D) × E ↦ g p.1.2)
        ((SubInstrument.relabel (queryEquivIn ℓ R.D)).branch () ρ) :=
      suppOn_relabel _ (fun q h ↦ by rwa [queryEquivIn_symm_snd] at h) hρ
    refine (forallQueries_queryBind_iff I i E ℓ k _).mpr ⟨⟨hp.1, hin⟩, fun r ↦ ih r (hp.2 r) ?_⟩
    rw [queryStep_branch_apply]
    exact suppOn_relabel _ (fun q h ↦ by rwa [queryEquivOut_symm_fst_snd] at h)
      (suppOn_amplify ((R.step i).branch r) (hstep i hp.1 r) hin)

end invariant

/-! ## Coin reads -/

section reads

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M]

/-- A hardwired read depends on the hardwired data only through the value at the cell read. -/
theorem cellRead_eq_of_some {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]
    {w w' : Database A Y} {a a' : A} {c : Y} (h : w a = some c) (h' : w' a' = some c)
    (o : Option Y) : cellRead w a o = cellRead w' a' o := by
  unfold cellRead
  rw [h, h']

omit [Fintype M] in
/-- **A coin read of `h` is a classical step.** At a column whose hardwired cells leave the read
cells free, the Kraus entries of the reads of two coin tables at two cells holding the same coin
agree: the read returns the coin and leaves the database alone. -/
theorem hwReadKraus1_readH_apply_eq {Lc Lc' : Hw X Z} {z z' : Z} {c : X}
    (hz : Lc.1 z = some c) (hz' : Lc'.1 z' = some c) (upd : M → Option X → M)
    (r : Option X × M) (b a : Unit × HwReg X Z M) (ha : a.2.2.1.1 z = none)
    (ha' : a.2.2.1.1 z' = none) :
    hwReadKraus1 Lc (.readH z upd) r b a = hwReadKraus1 Lc' (.readH z' upd) r b a := by
  simp only [hwReadKraus1, readKraus1H, kroneckerMap_apply, clsKraus_apply]
  rw [cellRead_eq_of_some (w := (hwView a.2.2.1 Lc).1) (w' := (hwView a.2.2.1 Lc').1) (a := z)
    (a' := z') (c := c) (by simp [hwView, ha, hz]) (by simp [hwView, ha', hz'])]

omit [Fintype M] in
/-- **A coin read of `k` is a classical step.** -/
theorem hwReadKraus1_readK_apply_eq {Lc Lc' : Hw X Z} {x x' : X} {c : Z}
    (hx : Lc.2.1 x = some c) (hx' : Lc'.2.1 x' = some c) (upd : M → Option Z → M)
    (r : Option Z × M) (b a : Unit × HwReg X Z M) (ha : a.2.2.1.2.1 x = none)
    (ha' : a.2.2.1.2.1 x' = none) :
    hwReadKraus1 Lc (.readK x upd) r b a = hwReadKraus1 Lc' (.readK x' upd) r b a := by
  simp only [hwReadKraus1, readKraus1K, kroneckerMap_apply, clsKraus_apply]
  rw [cellRead_eq_of_some (w := (hwView a.2.2.1 Lc).2.1) (w' := (hwView a.2.2.1 Lc').2.1)
    (a := x) (a' := x') (c := c) (by simp [hwView, ha, hx]) (by simp [hwView, ha', hx'])]

omit [Fintype M] in
/-- **A coin read of `k'` is a classical step.** -/
theorem hwReadKraus1_readK'_apply_eq {Lc Lc' : Hw X Z} {x x' : X} {c : Z}
    (hx : Lc.2.2 x = some c) (hx' : Lc'.2.2 x' = some c) (upd : M → Option Z → M)
    (r : Option Z × M) (b a : Unit × HwReg X Z M) (ha : a.2.2.1.2.2 x = none)
    (ha' : a.2.2.1.2.2 x' = none) :
    hwReadKraus1 Lc (.readK' x upd) r b a = hwReadKraus1 Lc' (.readK' x' upd) r b a := by
  simp only [hwReadKraus1, readKraus1K', kroneckerMap_apply, clsKraus_apply]
  rw [cellRead_eq_of_some (w := (hwView a.2.2.1 Lc).2.2) (w' := (hwView a.2.2.1 Lc').2.2)
    (a := x) (a' := x') (c := c) (by simp [hwView, ha, hx]) (by simp [hwView, ha', hx'])]

/-- The cell of a read port is not a cell of the table `Lc`. -/
def readOff (Lc : Hw X Z) : HwRead X Z M → Prop
  | .readH z _ => Lc.1 z = none
  | .readK x _ => Lc.2.1 x = none
  | .readK' x _ => Lc.2.2 x = none

omit [Fintype M] in
/-- Off the coin tables, the reads of two coin tables are equal. -/
theorem hwReadKraus1_eq_of_readOff {Lc Lc' : Hw X Z} (c : HwRead X Z M) (h : readOff Lc c)
    (h' : readOff Lc' c) : hwReadKraus1 Lc c = hwReadKraus1 Lc' c := by
  cases c with
  | readH z upd =>
    funext r
    rw [hwReadKraus1_readH_of_none Lc h, hwReadKraus1_readH_of_none Lc' h']
  | readK x upd =>
    funext r
    rw [hwReadKraus1_readK_of_none Lc h, hwReadKraus1_readK_of_none Lc' h']
  | readK' x upd =>
    funext r
    rw [hwReadKraus1_readK'_of_none Lc h, hwReadKraus1_readK'_of_none Lc' h']

omit [Fintype M] in
/-- A read leaves the hardwired cells alone. -/
theorem hwReadKraus1_ne_zero_hw (Lc : Hw X Z) (c : HwRead X Z M) (r : c.Result) {u u' : Unit}
    {s s' : HwReg X Z M} (h : hwReadKraus1 Lc c r (u', s') (u, s) ≠ 0) : s'.2.1 = s.2.1 := by
  cases c with
  | readH z upd =>
    simp only [hwReadKraus1, readKraus1H] at h
    obtain ⟨-, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
  | readK x upd =>
    simp only [hwReadKraus1, readKraus1K] at h
    obtain ⟨-, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
  | readK' x upd =>
    simp only [hwReadKraus1, readKraus1K'] at h
    obtain ⟨-, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]

/-- At a read off the coin table, the coin mass is the hidden mass. -/
theorem coinMass_read_of_readOff (Hh : Set Z) (Hk Hk' : Set X) {Lc : Hw X Z} (c : HwRead X Z M)
    (h : readOff Lc c)
    (τ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) :
    coinMass Hh Hk Hk' Lc (.inl (.inr c)) τ = hiddenMass Hh Hk Hk' (.inl (.inr c)) τ := by
  cases c with
  | readH z upd =>
    show diagMass {p : Unit × HwReg X Z M | z ∈ Hh ∧ Lc.1 z = none ∧ p.2.2.1.1 z = none} τ =
      diagMass {p : Unit × HwReg X Z M | z ∈ Hh ∧ p.2.2.1.1 z = none} τ
    congr 1
    ext p
    have h' : Lc.1 z = none := h
    simp [h']
  | readK x upd =>
    show diagMass {p : Unit × HwReg X Z M | x ∈ Hk ∧ Lc.2.1 x = none ∧ p.2.2.1.2.1 x = none} τ =
      diagMass {p : Unit × HwReg X Z M | x ∈ Hk ∧ p.2.2.1.2.1 x = none} τ
    congr 1
    ext p
    have h' : Lc.2.1 x = none := h
    simp [h']
  | readK' x upd =>
    show diagMass {p : Unit × HwReg X Z M | x ∈ Hk' ∧ Lc.2.2 x = none ∧ p.2.2.1.2.2 x = none} τ =
      diagMass {p : Unit × HwReg X Z M | x ∈ Hk' ∧ p.2.2.1.2.2 x = none} τ
    congr 1
    ext p
    have h' : Lc.2.2 x = none := h
    simp [h']

/-- The coin mass is subadditive in the hidden sets. -/
theorem coinMass_union_le (Hh₁ Hh₂ : Set Z) (Hk₁ Hk₂ Hk'₁ Hk'₂ : Set X) (Lc : Hw X Z)
    (i : (hwSpec X Z M).Port)
    (σ : Matrix ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ) :
    coinMass (Hh₁ ∪ Hh₂) (Hk₁ ∪ Hk₂) (Hk'₁ ∪ Hk'₂) Lc i σ ≤
      coinMass Hh₁ Hk₁ Hk'₁ Lc i σ + coinMass Hh₂ Hk₂ Hk'₂ Lc i σ := by
  rcases i with (i | (⟨z, upd⟩ | ⟨x, upd⟩ | ⟨x, upd⟩)) | c
  · exact hiddenMass_union_le _ _ _ _ _ _ (.inl (.inl i)) σ
  · refine (diagMass_mono ?_ σ).trans (diagMass_union_le _ _ σ)
    rintro p ⟨hp | hp, hL, hW⟩
    · exact Or.inl ⟨hp, hL, hW⟩
    · exact Or.inr ⟨hp, hL, hW⟩
  · refine (diagMass_mono ?_ σ).trans (diagMass_union_le _ _ σ)
    rintro p ⟨hp | hp, hL, hW⟩
    · exact Or.inl ⟨hp, hL, hW⟩
    · exact Or.inr ⟨hp, hL, hW⟩
  · refine (diagMass_mono ?_ σ).trans (diagMass_union_le _ _ σ)
    rintro p ⟨hp | hp, hL, hW⟩
    · exact Or.inl ⟨hp, hL, hW⟩
    · exact Or.inr ⟨hp, hL, hW⟩
  · exact zero_le

end reads

/-! ## Template programs with coins -/

section template

variable (X Z : Type)

/-- A coin read of a template program: coin `u` of `h`, `k` or `k'`, read with the memory update
`upd`. A placement puts it at a cell. -/
inductive CoinRead (U M : Type) where
  /-- Read coin `u` of `h`. -/
  | coinH (u : U) (upd : M → Option X → M)
  /-- Read coin `u` of `k`. -/
  | coinK (u : U) (upd : M → Option Z → M)
  /-- Read coin `u` of `k'`. -/
  | coinK' (u : U) (upd : M → Option Z → M)

/-- The cells at which the coins of `h`, `k` and `k'` are read. -/
structure CoinPlacement (U : Type) where
  /-- The cells of the coins of `h`. -/
  h : U → Z
  /-- The cells of the coins of `k`. -/
  k : U → X
  /-- The cells of the coins of `k'`. -/
  k' : U → X

end template

namespace CoinRead

variable {X Z U M : Type}

/-- The classical result of a coin read: that of the read port it is placed at. -/
@[reducible]
def Result : CoinRead X Z U M → Type
  | coinH .. => Option X × M
  | coinK .. => Option Z × M
  | coinK' .. => Option Z × M

/-- The read port at which a placement puts a coin read. -/
def place (pl : CoinPlacement X Z U) : CoinRead X Z U M → HwRead X Z M
  | coinH u upd => .readH (pl.h u) upd
  | coinK u upd => .readK (pl.k u) upd
  | coinK' u upd => .readK' (pl.k' u) upd

/-- The coin's cell is not hardwired in `W`. -/
def Free (pl : CoinPlacement X Z U) (W : Hw X Z) : CoinRead X Z U M → Prop
  | coinH u _ => W.1 (pl.h u) = none
  | coinK u _ => W.2.1 (pl.k u) = none
  | coinK' u _ => W.2.2 (pl.k' u) = none

end CoinRead

section coinsMatch

variable {X Z U : Type}

/-- The coins of `Lc` at the placement `pl` are those of `Lc'` at `pl'`, and every coin cell is in
its table. -/
def CoinsMatch (Lc : Hw X Z) (pl : CoinPlacement X Z U) (Lc' : Hw X Z)
    (pl' : CoinPlacement X Z U) : Prop :=
  (∀ u, ∃ c, Lc.1 (pl.h u) = some c ∧ Lc'.1 (pl'.h u) = some c) ∧
    (∀ u, ∃ c, Lc.2.1 (pl.k u) = some c ∧ Lc'.2.1 (pl'.k u) = some c) ∧
    (∀ u, ∃ c, Lc.2.2 (pl.k' u) = some c ∧ Lc'.2.2 (pl'.k' u) = some c)

/-- A coin match read the other way. -/
theorem CoinsMatch.symm {Lc Lc' : Hw X Z} {pl pl' : CoinPlacement X Z U}
    (hm : CoinsMatch Lc pl Lc' pl') : CoinsMatch Lc' pl' Lc pl := by
  obtain ⟨hmh, hmk, hmk'⟩ := hm
  exact ⟨fun u ↦ (hmh u).imp fun _ h ↦ h.symm, fun u ↦ (hmk u).imp fun _ h ↦ h.symm,
    fun u ↦ (hmk' u).imp fun _ h ↦ h.symm⟩

/-- No coin cell of the two placements is hardwired in `W`. -/
def CoinsFree (pl pl' : CoinPlacement X Z U) (W : Hw X Z) : Prop :=
  ∀ u, (W.1 (pl.h u) = none ∧ W.1 (pl'.h u) = none) ∧
    (W.2.1 (pl.k u) = none ∧ W.2.1 (pl'.k u) = none) ∧
    (W.2.2 (pl.k' u) = none ∧ W.2.2 (pl'.k' u) = none)

/-- The cell a program port hardwires is not a coin cell of the placement. -/
def progOff (pl : CoinPlacement X Z U) : HwProg X Z → Prop
  | .programH z _ => ∀ u, pl.h u ≠ z
  | .programK x _ => ∀ u, pl.k u ≠ x
  | .programK' x _ => ∀ u, pl.k' u ≠ x

/-- Nothing is hardwired at the start. -/
theorem coinsFree_hwEmpty (pl pl' : CoinPlacement X Z U) : CoinsFree pl pl' (hwEmpty X Z) :=
  fun _ ↦ ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- Hardwiring a cell off the coin cells keeps them free. -/
theorem coinsFree_progUpdate [DecidableEq X] [DecidableEq Z] {pl pl' : CoinPlacement X Z U}
    {c : HwProg X Z} (h : progOff pl c) (h' : progOff pl' c) {W : Hw X Z}
    (hW : CoinsFree pl pl' W) : CoinsFree pl pl' (progUpdate c W) := by
  intro u
  obtain ⟨⟨hh, hh'⟩, ⟨hk, hk'⟩, ⟨hk₂, hk₂'⟩⟩ := hW u
  cases c with
  | programH z v =>
    refine ⟨⟨?_, ?_⟩, ⟨hk, hk'⟩, ⟨hk₂, hk₂'⟩⟩
    · simp only [progUpdate]
      rw [Function.update_of_ne (h u)]
      exact hh
    · simp only [progUpdate]
      rw [Function.update_of_ne (h' u)]
      exact hh'
  | programK x v =>
    refine ⟨⟨hh, hh'⟩, ⟨?_, ?_⟩, ⟨hk₂, hk₂'⟩⟩
    · simp only [progUpdate]
      rw [Function.update_of_ne (h u)]
      exact hk
    · simp only [progUpdate]
      rw [Function.update_of_ne (h' u)]
      exact hk'
  | programK' x v =>
    refine ⟨⟨hh, hh'⟩, ⟨hk, hk'⟩, ⟨?_, ?_⟩⟩
    · simp only [progUpdate]
      rw [Function.update_of_ne (h u)]
      exact hk₂
    · simp only [progUpdate]
      rw [Function.update_of_ne (h' u)]
      exact hk₂'

end coinsMatch

section coins

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {U M : Type} [Fintype M] [DecidableEq M]

variable (X Z) in
/-- The signature of the coin reads: trivial public registers, classical results. -/
@[reducible]
def coinCmdSpec (U M : Type) : QuantumOracleSpec.{0, 0} where
  Port := CoinRead X Z U M
  In _ := QReg.of Unit
  Out _ := QReg.of Unit
  Result := CoinRead.Result

variable (X Z) in
/-- **The template signature with coins**: the ports of runtime 2, then the coin reads. -/
@[reducible]
def coinSpec (U M : Type) : QuantumOracleSpec.{0, 0} :=
  (hwSpec X Z M).sum (coinCmdSpec X Z U M)

/-- The placement of a template, as a lens: the ports of runtime 2 stay, a coin read becomes the
read port its placement gives. -/
def placeLens {L : LocalSig.{u, v}} (pl : CoinPlacement X Z U) :
    IPFunctor.Lens (QuantumComp.toIPFunctor L (coinSpec X Z U M))
      (QuantumComp.toIPFunctor L (hwSpec X Z M)) where
  toFunA _
    | .prim o => .prim o
    | .query (.inl i) E ℓ => .query i E ℓ
    | .query (.inr c) E ℓ => .query (.inl (.inr (c.place pl))) E ℓ
  toFunB _ c := by
    rcases c with o | ⟨i | c, E, ℓ⟩
    · exact id
    · exact id
    · cases c <;> exact id
  src_eq _ c _ := by
    rcases c with o | ⟨i | c, E, ℓ⟩
    · rfl
    · rfl
    · cases c <;> rfl

/-- **The program of a placement**: every coin read of the template reads the cell its placement
gives. -/
def placeCoins {L : LocalSig.{u, v}} {Ω : QReg → Type w} {A : QReg} (pl : CoinPlacement X Z U)
    (y : QuantumComp L (coinSpec X Z U M) Ω A) : QuantumComp L (hwSpec X Z M) Ω A :=
  IPFunctor.IFreeM.mapLens (placeLens pl) y

/-- A weight of runtime 2 read on the template ports at a placement. -/
def placeWeight (pl : CoinPlacement X Z U)
    (wt : ∀ i, Matrix ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ → ℝ≥0∞) :
    ∀ i : (coinSpec X Z U M).Port,
      Matrix ((coinSpec X Z U M).In i × QReg.of (HwReg X Z M))
        ((coinSpec X Z U M).In i × QReg.of (HwReg X Z M)) ℂ → ℝ≥0∞
  | .inl i => wt i
  | .inr c => wt (.inl (.inr (c.place pl)))

/-! ## Two placements of the coins -/

/-- **The calls on which two placements run alike**: an ordinary read avoids both coin tables;
a coin read is presented an operator supported on the states in which its cells in both
placements are not hardwired. -/
def CoinsOK (Lc Lc' : Hw X Z) (pl pl' : CoinPlacement X Z U) :
    ∀ (i : (coinSpec X Z U M).Port) (E : QReg),
      Matrix (((coinSpec X Z U M).In i × QReg.of (HwReg X Z M)) × E)
        (((coinSpec X Z U M).In i × QReg.of (HwReg X Z M)) × E) ℂ → Prop
  | .inl (.inl (.inl _)), _, _ => True
  | .inl (.inl (.inr c)), _, _ => readOff Lc c ∧ readOff Lc' c
  | .inl (.inr _), _, _ => True
  | .inr c, E, σ => ∀ a b : (Unit × HwReg X Z M) × E, σ a b ≠ 0 →
      (c.Free pl a.1.2.2.1 ∧ c.Free pl' a.1.2.2.1) ∧ (c.Free pl b.1.2.2.1 ∧ c.Free pl' b.1.2.2.1)

/-- **The ports on which two placements are safe**: an ordinary read off both coin tables, a
program port hardwiring a cell off both placements' coin cells. -/
def CoinsPortOK (Lc Lc' : Hw X Z) (pl pl' : CoinPlacement X Z U) :
    (coinSpec X Z U M).Port → Prop
  | .inl (.inl (.inl _)) => True
  | .inl (.inl (.inr c)) => readOff Lc c ∧ readOff Lc' c
  | .inl (.inr c) => progOff pl c ∧ progOff pl' c
  | .inr _ => True

/-- At a coin read, the coin mass vanishes: the cell is in the coin table. -/
theorem placeWeight_coinMass_coin (Hh : Set Z) (Hk Hk' : Set X) {Lc Lc' : Hw X Z}
    {pl pl' : CoinPlacement X Z U} (hm : CoinsMatch Lc pl Lc' pl') (c : CoinRead X Z U M)
    (τ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) :
    placeWeight pl (coinMass Hh Hk Hk' Lc) (.inr c) τ = 0 := by
  obtain ⟨hmh, hmk, hmk'⟩ := hm
  cases c with
  | coinH u upd =>
    obtain ⟨v, hv, -⟩ := hmh u
    show diagMass {p : Unit × HwReg X Z M |
      pl.h u ∈ Hh ∧ Lc.1 (pl.h u) = none ∧ p.2.2.1.1 (pl.h u) = none} τ = 0
    refine Finset.sum_eq_zero fun a _ ↦ Set.indicator_of_notMem (fun ha ↦ ?_) _
    have h : Lc.1 (pl.h u) = none := ha.2.1
    rw [hv] at h
    exact Option.some_ne_none v h
  | coinK u upd =>
    obtain ⟨v, hv, -⟩ := hmk u
    show diagMass {p : Unit × HwReg X Z M |
      pl.k u ∈ Hk ∧ Lc.2.1 (pl.k u) = none ∧ p.2.2.1.2.1 (pl.k u) = none} τ = 0
    refine Finset.sum_eq_zero fun a _ ↦ Set.indicator_of_notMem (fun ha ↦ ?_) _
    have h : Lc.2.1 (pl.k u) = none := ha.2.1
    rw [hv] at h
    exact Option.some_ne_none v h
  | coinK' u upd =>
    obtain ⟨v, hv, -⟩ := hmk' u
    show diagMass {p : Unit × HwReg X Z M |
      pl.k' u ∈ Hk' ∧ Lc.2.2 (pl.k' u) = none ∧ p.2.2.1.2.2 (pl.k' u) = none} τ = 0
    refine Finset.sum_eq_zero fun a _ ↦ Set.indicator_of_notMem (fun ha ↦ ?_) _
    have h : Lc.2.2 (pl.k' u) = none := ha.2.1
    rw [hv] at h
    exact Option.some_ne_none v h

/-- **The coin masses of two placements agree on the presented operators**, for the same hidden
sets: equal at the sponge and program ports, the hidden mass at an ordinary read off both coin
tables, and `0` at a coin read. -/
theorem placeWeight_coinMass_eq (Hh : Set Z) (Hk Hk' : Set X) {Lc Lc' : Hw X Z}
    {pl pl' : CoinPlacement X Z U} (hm : CoinsMatch Lc pl Lc' pl') (i : (coinSpec X Z U M).Port)
    (E : QReg)
    (σ : Matrix (((coinSpec X Z U M).In i × QReg.of (HwReg X Z M)) × E)
      (((coinSpec X Z U M).In i × QReg.of (HwReg X Z M)) × E) ℂ)
    (hσ : CoinsOK Lc Lc' pl pl' i E σ)
    (τ : Matrix ((coinSpec X Z U M).In i × QReg.of (HwReg X Z M))
      ((coinSpec X Z U M).In i × QReg.of (HwReg X Z M)) ℂ) :
    placeWeight pl (coinMass Hh Hk Hk' Lc) i τ = placeWeight pl' (coinMass Hh Hk Hk' Lc') i τ := by
  rcases i with ((i | c) | c) | c
  · rfl
  · obtain ⟨h₁, h₂⟩ := hσ
    exact (coinMass_read_of_readOff Hh Hk Hk' c h₁ τ).trans
      (coinMass_read_of_readOff Hh Hk Hk' c h₂ τ).symm
  · rfl
  · rw [placeWeight_coinMass_coin Hh Hk Hk' hm c τ,
      placeWeight_coinMass_coin Hh Hk Hk' hm.symm c τ]

variable [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]

/-- The steps of a template against runtime 2 with the coin table `Lc`, its coins placed by
`pl`. -/
noncomputable def coinsStep (Lc : Hw X Z) (pl : CoinPlacement X Z U) (m₀ : M) :
    ∀ i : (coinSpec X Z U M).Port,
      SubInstrument ((coinSpec X Z U M).In i × QReg.of (HwReg X Z M))
        ((coinSpec X Z U M).Out i × QReg.of (HwReg X Z M)) ((coinSpec X Z U M).Result i)
  | .inl i => (runtime2Coins X Z Lc m₀).step i
  | .inr (.coinH u upd) => (runtime2Coins X Z Lc m₀).step (.inl (.inr (.readH (pl.h u) upd)))
  | .inr (.coinK u upd) => (runtime2Coins X Z Lc m₀).step (.inl (.inr (.readK (pl.k u) upd)))
  | .inr (.coinK' u upd) =>
      (runtime2Coins X Z Lc m₀).step (.inl (.inr (.readK' (pl.k' u) upd)))

/-- The template runtime of runtime 2 with the coin table `Lc` and the placement `pl`. -/
@[reducible]
noncomputable def coinsRuntime (Lc : Hw X Z) (pl : CoinPlacement X Z U) (m₀ : M) :
    QuantumRuntime (coinSpec X Z U M) where
  D := QReg.of (HwReg X Z M)
  init := initHw X Z m₀
  step := coinsStep Lc pl m₀

/-- The Kraus operators of the template runtime. -/
noncomputable def coinsKraus (Lc : Hw X Z) (pl : CoinPlacement X Z U) (m₀ : M) :
    ∀ i : (coinSpec X Z U M).Port, (coinSpec X Z U M).Result i →
      Matrix ((coinSpec X Z U M).Out i × QReg.of (HwReg X Z M))
        ((coinSpec X Z U M).In i × QReg.of (HwReg X Z M)) ℂ
  | .inl i, r => krausCoins X Z Lc m₀ i r
  | .inr (.coinH u upd), r => hwReadKraus1 Lc (.readH (pl.h u) upd) r
  | .inr (.coinK u upd), r => hwReadKraus1 Lc (.readK (pl.k u) upd) r
  | .inr (.coinK' u upd), r => hwReadKraus1 Lc (.readK' (pl.k' u) upd) r

theorem coinsStep_branch (Lc : Hw X Z) (pl : CoinPlacement X Z U) (m₀ : M)
    (i : (coinSpec X Z U M).Port) (r : (coinSpec X Z U M).Result i) :
    (coinsStep Lc pl m₀ i).branch r = MatrixMap.conj (coinsKraus Lc pl m₀ i r) := by
  rcases i with i | c
  · exact runtime2Coins_branch Lc m₀ i r
  · cases c with
    | coinH u upd => exact runtime2Coins_branch Lc m₀ (.inl (.inr (.readH (pl.h u) upd))) r
    | coinK u upd => exact runtime2Coins_branch Lc m₀ (.inl (.inr (.readK (pl.k u) upd))) r
    | coinK' u upd => exact runtime2Coins_branch Lc m₀ (.inl (.inr (.readK' (pl.k' u) upd))) r

section run

variable {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w} {A : QReg}

/-- **Running the placed program.** The weights of runtime 2 with coins running a placement of a
template are those of the template runtime running the template. -/
theorem queryWeight_placeCoins (Lc : Hw X Z) (pl : CoinPlacement X Z U) (m₀ : M)
    (wt : ∀ i, Matrix ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ → ℝ≥0∞)
    (y : QuantumComp L (coinSpec X Z U M) Ω A)
    (ρ : Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ) (j : ℕ) :
    (runtime2Coins X Z Lc m₀).queryWeight I wt (placeCoins pl y) ρ j =
      (coinsRuntime Lc pl m₀).queryWeight I (placeWeight pl wt) y ρ j := by
  induction y using QuantumComp.inductionOn generalizing j with
  | pure _ _ => rfl
  | primBind _ o k ih => exact tsum_congr fun b ↦ ih b _ j
  | queryBind _ i E ℓ k ih =>
    rcases i with i | c
    · cases j with
      | zero => rfl
      | succ j => exact tsum_congr fun r ↦ ih r _ j
    · cases c <;> cases j <;> first | rfl | exact tsum_congr fun r ↦ ih r _ _

end run

/-- **The template steps of two placements agree on the presented operators.** -/
theorem coinsStep_frame_eq {Lc Lc' : Hw X Z} {pl pl' : CoinPlacement X Z U} (m₀ : M)
    (hm : CoinsMatch Lc pl Lc' pl') (i : (coinSpec X Z U M).Port) (E : QReg)
    (σ : Matrix (((coinSpec X Z U M).In i × QReg.of (HwReg X Z M)) × E)
      (((coinSpec X Z U M).In i × QReg.of (HwReg X Z M)) × E) ℂ)
    (hσ : CoinsOK Lc Lc' pl pl' i E σ) (r : (coinSpec X Z U M).Result i) :
    ((coinsStep Lc pl m₀ i).frame E).branch r σ = ((coinsStep Lc' pl' m₀ i).frame E).branch r σ := by
  rw [frame_branch_eq_amplify_conj _ _ (coinsStep_branch Lc pl m₀ i),
    frame_branch_eq_amplify_conj _ _ (coinsStep_branch Lc' pl' m₀ i)]
  obtain ⟨hmh, hmk, hmk'⟩ := hm
  rcases i with ((i | c) | c) | c
  · rfl
  · show (MatrixMap.conj (hwReadKraus1 Lc c r)).amplify E σ =
      (MatrixMap.conj (hwReadKraus1 Lc' c r)).amplify E σ
    obtain ⟨h₁, h₂⟩ := hσ
    rw [hwReadKraus1_eq_of_readOff c h₁ h₂]
  · rfl
  · cases c with
    | coinH u upd =>
      obtain ⟨v, hv, hv'⟩ := hmh u
      exact amplify_conj_eq_of_supp _ _
        {a : Unit × HwReg X Z M | a.2.2.1.1 (pl.h u) = none ∧ a.2.2.1.1 (pl'.h u) = none}
        (fun b a ha ↦ hwReadKraus1_readH_apply_eq hv hv' upd r b a ha.1 ha.2)
        fun a a' h ↦ hσ a a' h
    | coinK u upd =>
      obtain ⟨v, hv, hv'⟩ := hmk u
      exact amplify_conj_eq_of_supp _ _
        {a : Unit × HwReg X Z M | a.2.2.1.2.1 (pl.k u) = none ∧ a.2.2.1.2.1 (pl'.k u) = none}
        (fun b a ha ↦ hwReadKraus1_readK_apply_eq hv hv' upd r b a ha.1 ha.2)
        fun a a' h ↦ hσ a a' h
    | coinK' u upd =>
      obtain ⟨v, hv, hv'⟩ := hmk' u
      exact amplify_conj_eq_of_supp _ _
        {a : Unit × HwReg X Z M | a.2.2.1.2.2 (pl.k' u) = none ∧ a.2.2.1.2.2 (pl'.k' u) = none}
        (fun b a ha ↦ hwReadKraus1_readK'_apply_eq hv hv' upd r b a ha.1 ha.2)
        fun a a' h ↦ hσ a a' h

omit [Nonempty X] [Nonempty Z] in
/-- The template steps never hardwire a coin cell on the safe ports. -/
theorem coinsKraus_ne_zero_free {Lc Lc' : Hw X Z} {pl pl' : CoinPlacement X Z U} (m₀ : M)
    (i : (coinSpec X Z U M).Port) (hi : CoinsPortOK Lc Lc' pl pl' i)
    (r : (coinSpec X Z U M).Result i) (b : (coinSpec X Z U M).Out i × QReg.of (HwReg X Z M))
    (a : (coinSpec X Z U M).In i × QReg.of (HwReg X Z M)) (h : coinsKraus Lc pl m₀ i r b a ≠ 0)
    (ha : CoinsFree pl pl' a.2.2.1) : CoinsFree pl pl' b.2.2.1 := by
  rcases i with ((i | c) | c) | c
  · have hs := spongeHardwired_U_ne_zero_snd (hwEmpty X Z) m₀ i (a := a.1) (a' := b.1)
      (s := a.2) (s' := b.2) h
    rw [show b.2.2.1 = a.2.2.1 from congrArg Prod.fst hs]
    exact ha
  · rw [show b.2.2.1 = a.2.2.1 from
      hwReadKraus1_ne_zero_hw Lc c r (u := a.1) (u' := b.1) (s := a.2) (s' := b.2) h]
    exact ha
  · obtain ⟨h₁, h₂⟩ := hi
    have hs := hwProgKraus_ne_zero_snd c r (u := a.1) (u' := b.1) (s := a.2) (s' := b.2) h
    rw [show b.2.2.1 = progUpdate c a.2.2.1 from congrArg Prod.fst hs]
    exact coinsFree_progUpdate h₁ h₂ ha
  · cases c with
    | coinH u upd =>
      rw [show b.2.2.1 = a.2.2.1 from hwReadKraus1_ne_zero_hw Lc (.readH (pl.h u) upd) r
        (u := a.1) (u' := b.1) (s := a.2) (s' := b.2) h]
      exact ha
    | coinK u upd =>
      rw [show b.2.2.1 = a.2.2.1 from hwReadKraus1_ne_zero_hw Lc (.readK (pl.k u) upd) r
        (u := a.1) (u' := b.1) (s := a.2) (s' := b.2) h]
      exact ha
    | coinK' u upd =>
      rw [show b.2.2.1 = a.2.2.1 from hwReadKraus1_ne_zero_hw Lc (.readK' (pl.k' u) upd) r
        (u := a.1) (u' := b.1) (s := a.2) (s' := b.2) h]
      exact ha

section run

variable {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w} {A : QReg}

/-- **The coin cells stay free.** If every call of the template run is of a safe port
(`CoinsPortOK`: ordinary reads off both coin tables, program ports off both placements' coin
cells), every call of the run from `ρ₀ ⊗ (∅, ∅, m₀)` is presented an operator on which the two
placements run alike (`CoinsOK`). -/
theorem forallQueries_coinsOK {Lc Lc' : Hw X Z} {pl pl' : CoinPlacement X Z U} (m₀ : M)
    (y : QuantumComp L (coinSpec X Z U M) Ω A) (ρ₀ : SubState A)
    (hports : (coinsRuntime Lc pl m₀).ForallQueries I (fun i _ _ ↦ CoinsPortOK Lc Lc' pl pl' i) y
      (ρ₀.matrix ⊗ₖ (initHw X Z m₀).matrix)) :
    (coinsRuntime Lc pl m₀).ForallQueries I (CoinsOK Lc Lc' pl pl') y
      (ρ₀.matrix ⊗ₖ (initHw X Z m₀).matrix) := by
  have hρ : SuppOn (fun p : A × HwReg X Z M ↦ CoinsFree pl pl' p.2.2.1)
      (ρ₀.matrix ⊗ₖ (initHw X Z m₀).matrix) := by
    intro a b hab
    rw [kroneckerMap_apply] at hab
    have hd := right_ne_zero_of_mul hab
    rw [initHw, SubState.matrix_basis, Matrix.single_apply] at hd
    split_ifs at hd with hs
    · obtain ⟨h₁, h₂⟩ := hs
      show CoinsFree pl pl' a.2.2.1 ∧ CoinsFree pl pl' b.2.2.1
      rw [← h₁, ← h₂]
      exact ⟨coinsFree_hwEmpty pl pl', coinsFree_hwEmpty pl pl'⟩
    · exact absurd rfl hd
  refine QuantumRuntime.ForallQueries.mono I (fun i E σ h ↦ ?_)
    (forallQueries_suppOn I (coinsRuntime Lc pl m₀) (fun s : HwReg X Z M ↦ CoinsFree pl pl' s.2.1)
      (CoinsPortOK Lc Lc' pl pl') (fun i hi r τ hτ ↦ ?_) hports hρ)
  · obtain ⟨hp, hs⟩ := h
    rcases i with ((i | c) | c) | c
    · trivial
    · exact hp
    · trivial
    · intro a b hab
      obtain ⟨ha, hb⟩ := hs a b hab
      cases c with
      | coinH u upd => exact ⟨(ha u).1, (hb u).1⟩
      | coinK u upd => exact ⟨(ha u).2.1, (hb u).2.1⟩
      | coinK' u upd => exact ⟨(ha u).2.2, (hb u).2.2⟩
  · rw [show ((coinsRuntime Lc pl m₀).step i).branch r = MatrixMap.conj (coinsKraus Lc pl m₀ i r)
      from coinsStep_branch Lc pl m₀ i r]
    exact suppOn_conj _ (fun b a h ha ↦ coinsKraus_ne_zero_free m₀ i hi r b a h ha) hτ

/-- **Moving the coins.** If the coins of `Lc` at `pl` are those of `Lc'` at `pl'`, and every call
of the run of the template against the first placement is presented an operator on which the two
placements run alike (`CoinsOK`), the coin masses of the two placed programs, against runtime 2
with the two coin tables, agree at every call. -/
theorem queryWeight_coinMass_placeCoins_eq (Hh : Set Z) (Hk Hk' : Set X) {Lc Lc' : Hw X Z}
    {pl pl' : CoinPlacement X Z U} (m₀ : M) (hm : CoinsMatch Lc pl Lc' pl')
    (y : QuantumComp L (coinSpec X Z U M) Ω A)
    (ρ : Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hy : (coinsRuntime Lc pl m₀).ForallQueries I (CoinsOK Lc Lc' pl pl') y ρ) (j : ℕ) :
    (runtime2Coins X Z Lc m₀).queryWeight I (coinMass Hh Hk Hk' Lc) (placeCoins pl y) ρ j =
      (runtime2Coins X Z Lc' m₀).queryWeight I (coinMass Hh Hk Hk' Lc') (placeCoins pl' y) ρ j := by
  rw [queryWeight_placeCoins, queryWeight_placeCoins]
  exact queryWeight_eq_of_forallQueries I
    (fun i E σ hσ r ↦ coinsStep_frame_eq m₀ hm i E σ hσ r)
    (fun i E σ hσ ↦ placeWeight_coinMass_eq Hh Hk Hk' hm i E σ hσ _) hy j

/-! ## The coin-cell mass -/

/-- **The coin-cell mass, averaged.** Reparametrize the tables by `e : Θ ≃ P × V` into public data
and a hidden value. The table `θ` has the coin table `Lc θ` at the placement `pos θ` (cells that
may depend on the hidden value); the public data `p` has the coin table `Lp p` at the reference
placement `ref p`. Let the coin hidden sets `C p v` contain each cell for at most `κ` hidden
values. On `G`, let the program be the placement at `pos θ` of a template `y p` of the public data,
started from `ρ p`, with the coins of `Lc θ` at `pos θ` those of `Lp p` at `ref p` (the coins are
public), and every call of the template run of a safe port (`CoinsPortOK`). Then the coin mass of
the `j`-th call against `runtime2Coins (Lc θ)`, averaged over the
tables, is at most `κ / |V|` plus the fraction of tables outside `G`. -/
theorem uavg_coinMass_le {Θ P V : Type} [Fintype Θ] [Fintype P] [Fintype V]
    (e : Θ ≃ P × V) (m₀ : M) (Lc : Θ → Hw X Z) (pos : Θ → CoinPlacement X Z U)
    (Lp : P → Hw X Z) (ref : P → CoinPlacement X Z U) (Ch : P → V → Set Z)
    (Ck Ck' : P → V → Set X) (κ : ℝ≥0∞)
    (hh : ∀ p z, ∑ v, (Ch p v).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤ κ)
    (hk : ∀ p x, ∑ v, (Ck p v).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤ κ)
    (hk' : ∀ p x, ∑ v, (Ck' p v).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤ κ)
    (xθ : Θ → QuantumComp L (hwSpec X Z M) Ω A) (ρθ : Θ → SubState A)
    (y : P → QuantumComp L (coinSpec X Z U M) Ω A) (ρ : P → SubState A) (G : Finset Θ)
    (hG : ∀ θ ∈ G, xθ θ = placeCoins (pos θ) (y (e θ).1) ∧ ρθ θ = ρ (e θ).1 ∧
      CoinsMatch (Lc θ) (pos θ) (Lp (e θ).1) (ref (e θ).1) ∧
      (coinsRuntime (Lc θ) (pos θ) m₀).ForallQueries I
        (fun i _ _ ↦ CoinsPortOK (Lc θ) (Lp (e θ).1) (pos θ) (ref (e θ).1) i) (y (e θ).1)
        ((ρ (e θ).1).matrix ⊗ₖ (initHw X Z m₀).matrix))
    (j : ℕ) :
    uavg (fun θ ↦ (runtime2Coins X Z (Lc θ) m₀).queryWeight I
        (coinMass (Ch (e θ).1 (e θ).2) (Ck (e θ).1 (e θ).2) (Ck' (e θ).1 (e θ).2) (Lc θ)) (xθ θ)
        ((ρθ θ).matrix ⊗ₖ (runtime2Coins X Z (Lc θ) m₀).init.matrix) j) ≤
      κ * (Fintype.card V : ℝ≥0∞)⁻¹ +
        (Fintype.card Θ : ℝ≥0∞)⁻¹ * ((Fintype.card Θ - G.card : ℕ) : ℝ≥0∞) := by
  have hw : ∀ (p : P) (i : (hwSpec X Z M).Port)
      (σ : Matrix ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
        ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ), σ.PosSemidef →
      ∑ v, coinMass (Ch p v) (Ck p v) (Ck' p v) (Lp p) i σ ≤ κ * ENNReal.ofReal σ.trace.re :=
    fun p i σ hσ ↦ (Finset.sum_le_sum fun v _ ↦ coinMass_le_hiddenMass _ _ _ _ i σ).trans
      (sum_hiddenMass_le (Ch p) (Ck p) (Ck' p) κ (hh p) (hk p) (hk' p) i hσ)
  exact avg_queryWeight_le_fam I e
    (fun θ ↦ (runtime2Coins X Z (Lc θ) m₀).queryWeight I
      (coinMass (Ch (e θ).1 (e θ).2) (Ck (e θ).1 (e θ).2) (Ck' (e θ).1 (e θ).2) (Lc θ)) (xθ θ)
      ((ρθ θ).matrix ⊗ₖ (runtime2Coins X Z (Lc θ) m₀).init.matrix) j)
    (fun p ↦ runtime2Coins X Z (Lp p) m₀) (fun p ↦ placeCoins (ref p) (y p))
    (fun p ↦ (ρ p).matrix ⊗ₖ (initHw X Z m₀).matrix)
    (fun p ↦ ((ρ p).prod (initHw X Z m₀)).posSemidef)
    (fun p ↦ ENNReal.ofReal_le_one.mpr ((ρ p).prod (initHw X Z m₀)).trace_re_le_one)
    (fun p v ↦ coinMass (Ch p v) (Ck p v) (Ck' p v) (Lp p)) κ hw j G
    (fun θ hθ ↦ by
      obtain ⟨hx, hρ, hm, hq⟩ := hG θ hθ
      rw [hx, hρ]
      exact (queryWeight_coinMass_placeCoins_eq I _ _ _ m₀ hm (y (e θ).1) _
        (forallQueries_coinsOK I m₀ _ _ hq) j).le)
    fun θ _ ↦ ((runtime2Coins X Z (Lc θ) m₀).queryWeight_le_ofReal_trace I
      (fun i σ hσ ↦ (coinMass_le_hiddenMass _ _ _ _ i σ).trans (hiddenMass_le _ _ _ i hσ)) _
      ((ρθ θ).prod (initHw X Z m₀)).posSemidef j).trans
      (ENNReal.ofReal_le_one.mpr ((ρθ θ).prod (initHw X Z m₀)).trace_re_le_one)

end run

/-! ## The hybrid with the coin mass at the coin cells -/

section hybrid

variable {Λ : LocalSig.{u, v}} (I : Λ.Interp) {Xf : QReg → Type w} {A : QReg} {γ : Type*}
  [MeasurableSpace γ]

/-- **Runtime 1 against runtime 2 with coins, averaged, with the coin mass at the coin cells.**
`uavg_win_runtime1_le_coins` with its coin-cell hypothesis on the coin mass, which vanishes at the
reads of the coin table (the hidden mass there is the whole trace): if the masses at `H θ` are at
most `μ θ j` and the averaged coin masses at `C θ` at most `ε j`, then
`E P₁ ≤ (√(E P_c) + ∑ⱼ √(4 (E μⱼ + ε j)))²`. -/
theorem uavg_win_runtime1_le_coins_coinMass {Θ : Type*} [Fintype Θ] (L Lc : Θ → Hw X Z)
    (Hh₀ Ch : Θ → Set Z) (Hk₀ Hk'₀ Ck Ck' : Θ → Set X)
    (hL : ∀ θ, Covers (L θ) (Hh₀ θ ∪ Ch θ) (Hk₀ θ ∪ Ck θ) (Hk'₀ θ ∪ Ck' θ))
    (hc : ∀ θ, SubTable (Lc θ) (L θ)) (m₀ : M) (x : Θ → QuantumComp Λ (hwSpec X Z M) Xf A)
    (ρ : Θ → SubState A) (f : Θ → (Σ u, Xf u) → γ) {s : Set γ} (hs : MeasurableSet s)
    (μ : Θ → ℕ → ℝ≥0∞) (ε : ℕ → ℝ≥0∞)
    (hμ : ∀ θ j, (runtime2Coins X Z (Lc θ) m₀).queryWeight I
      (hiddenMass (Hh₀ θ) (Hk₀ θ) (Hk'₀ θ)) (x θ)
      ((ρ θ).matrix ⊗ₖ (runtime2Coins X Z (Lc θ) m₀).init.matrix) j ≤ μ θ j)
    (hε : ∀ j, uavg (fun θ ↦ (runtime2Coins X Z (Lc θ) m₀).queryWeight I
      (coinMass (Ch θ) (Ck θ) (Ck' θ) (Lc θ)) (x θ)
      ((ρ θ).matrix ⊗ₖ (runtime2Coins X Z (Lc θ) m₀).init.matrix) j) ≤ ε j) :
    uavg (fun θ ↦ (runtime1 X Z (L θ) m₀).evalDistMap I (x θ) (ρ θ) (f θ) s) ≤
      (uavg (fun θ ↦ (runtime2Coins X Z (Lc θ) m₀).evalDistMap I (x θ) (ρ θ) (f θ) s) ^
          (2⁻¹ : ℝ) +
        ∑' j, (4 * (uavg (fun θ ↦ μ θ j) + ε j)) ^ (2⁻¹ : ℝ)) ^ 2 := by
  set ν : Θ → ℕ → ℝ≥0∞ := fun θ j ↦ (runtime2Coins X Z (Lc θ) m₀).queryWeight I
    (coinMass (Ch θ) (Ck θ) (Ck' θ) (Lc θ)) (x θ)
    ((ρ θ).matrix ⊗ₖ (runtime2Coins X Z (Lc θ) m₀).init.matrix) j
  have hMass : ∀ θ j, (runtime2Coins X Z (Lc θ) m₀).queryWeight I
      (coinMass (Hh₀ θ ∪ Ch θ) (Hk₀ θ ∪ Ck θ) (Hk'₀ θ ∪ Ck' θ) (Lc θ)) (x θ)
      ((ρ θ).matrix ⊗ₖ (runtime2Coins X Z (Lc θ) m₀).init.matrix) j ≤ μ θ j + ν θ j :=
    fun θ j ↦ by
      calc _ ≤ (runtime2Coins X Z (Lc θ) m₀).queryWeight I
            (fun i σ ↦ hiddenMass (Hh₀ θ) (Hk₀ θ) (Hk'₀ θ) i σ +
              coinMass (Ch θ) (Ck θ) (Ck' θ) (Lc θ) i σ) (x θ)
            ((ρ θ).matrix ⊗ₖ (runtime2Coins X Z (Lc θ) m₀).init.matrix) j :=
            (runtime2Coins X Z (Lc θ) m₀).queryWeight_mono I
              (fun i σ _ ↦ (coinMass_union_le _ _ _ _ _ _ _ i σ).trans
                (add_le_add (coinMass_le_hiddenMass _ _ _ _ i σ) le_rfl)) (x θ)
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

end coins

/-! ## Seed-keyed coin cells -/

section seed

open HashSig LeanXmss

variable {M U : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} (I : L.Interp)
  {Ω : QReg → Type w} {A : QReg}

/-- **The coin-cell mass hidden by the scheme seed.** `uavg_coinMass_le` with the scheme seed as
the hidden value: coin hidden sets containing each cell for at most `κ` seeds have averaged coin
mass at most `κ / 2^256` per call, plus the fraction of tables outside `G`. -/
theorem uavg_coinMass_seed_le {Θ P : Type} [Fintype Θ] [Fintype P] (e : Θ ≃ P × MasterSeed)
    (m₀ : M) (Lc : Θ → Hw X Z) (pos : Θ → CoinPlacement X Z U) (Lp : P → Hw X Z)
    (ref : P → CoinPlacement X Z U) (Ch : P → MasterSeed → Set Z)
    (Ck Ck' : P → MasterSeed → Set X) (κ : ℝ≥0∞)
    (hh : ∀ p z, ∑ S, (Ch p S).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤ κ)
    (hk : ∀ p x, ∑ S, (Ck p S).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤ κ)
    (hk' : ∀ p x, ∑ S, (Ck' p S).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤ κ)
    (xθ : Θ → QuantumComp L (hwSpec X Z M) Ω A) (ρθ : Θ → SubState A)
    (y : P → QuantumComp L (coinSpec X Z U M) Ω A) (ρ : P → SubState A) (G : Finset Θ)
    (hG : ∀ θ ∈ G, xθ θ = placeCoins (pos θ) (y (e θ).1) ∧ ρθ θ = ρ (e θ).1 ∧
      CoinsMatch (Lc θ) (pos θ) (Lp (e θ).1) (ref (e θ).1) ∧
      (coinsRuntime (Lc θ) (pos θ) m₀).ForallQueries I
        (fun i _ _ ↦ CoinsPortOK (Lc θ) (Lp (e θ).1) (pos θ) (ref (e θ).1) i) (y (e θ).1)
        ((ρ (e θ).1).matrix ⊗ₖ (initHw X Z m₀).matrix))
    (j : ℕ) :
    uavg (fun θ ↦ (runtime2Coins X Z (Lc θ) m₀).queryWeight I
        (coinMass (Ch (e θ).1 (e θ).2) (Ck (e θ).1 (e θ).2) (Ck' (e θ).1 (e θ).2) (Lc θ)) (xθ θ)
        ((ρθ θ).matrix ⊗ₖ (runtime2Coins X Z (Lc θ) m₀).init.matrix) j) ≤
      κ * (2 ^ 256 : ℝ≥0∞)⁻¹ +
        (Fintype.card Θ : ℝ≥0∞)⁻¹ * ((Fintype.card Θ - G.card : ℕ) : ℝ≥0∞) := by
  have h := uavg_coinMass_le I e m₀ Lc pos Lp ref Ch Ck Ck' κ hh hk hk' xθ ρθ y ρ G hG j
  rwa [card_masterSeed, Nat.cast_pow, Nat.cast_ofNat] at h

/-- **The seed-keyed coin cells.** The `k`-cells `seedKeyCells S` of the scheme seed (among them
the first blocks of the randomizer bases' derivations, the challenger's seed-keyed coin cells)
have averaged coin mass at most `2^-256` per call in the run against `runtime2Coins (Lc θ)`, plus
the fraction of tables outside `G`. -/
theorem uavg_coinMass_schemeSeed_le {Θ P : Type} [Fintype Θ] [Fintype P]
    (e : Θ ≃ P × MasterSeed) (m₀ : M) (Lc : Θ → Hw X Z) (pos : Θ → CoinPlacement X Z U)
    (Lp : P → Hw X Z) (ref : P → CoinPlacement X Z U)
    (xθ : Θ → QuantumComp L (hwSpec X Z M) Ω A) (ρθ : Θ → SubState A)
    (y : P → QuantumComp L (coinSpec X Z U M) Ω A) (ρ : P → SubState A) (G : Finset Θ)
    (hG : ∀ θ ∈ G, xθ θ = placeCoins (pos θ) (y (e θ).1) ∧ ρθ θ = ρ (e θ).1 ∧
      CoinsMatch (Lc θ) (pos θ) (Lp (e θ).1) (ref (e θ).1) ∧
      (coinsRuntime (Lc θ) (pos θ) m₀).ForallQueries I
        (fun i _ _ ↦ CoinsPortOK (Lc θ) (Lp (e θ).1) (pos θ) (ref (e θ).1) i) (y (e θ).1)
        ((ρ (e θ).1).matrix ⊗ₖ (initHw X Z m₀).matrix))
    (j : ℕ) :
    uavg (fun θ ↦ (runtime2Coins X Z (Lc θ) m₀).queryWeight I
        (coinMass ∅ (seedKeyCells (e θ).2) ∅ (Lc θ)) (xθ θ)
        ((ρθ θ).matrix ⊗ₖ (runtime2Coins X Z (Lc θ) m₀).init.matrix) j) ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ +
        (Fintype.card Θ : ℝ≥0∞)⁻¹ * ((Fintype.card Θ - G.card : ℕ) : ℝ≥0∞) := by
  have h := uavg_coinMass_seed_le I e m₀ Lc pos Lp ref (fun _ _ ↦ ∅) (fun _ S ↦ seedKeyCells S)
    (fun _ _ ↦ ∅) 1 (fun _ _ ↦ by simp) (fun _ x ↦ (sum_indicator_seedKeyCells x).le)
    (fun _ _ ↦ by simp) xθ ρθ y ρ G hG j
  rwa [one_mul] at h

end seed

end Quantum.Xmss.Hybrid

end
