module

public import Quantum.Xmss.Assembly.Security
public import Quantum.Xmss.Assembly.GameTCalls

@[expose] public section

/-!
# Classical calls and the flip terms of the `k`, `k'` reads along a run

Security's classical-cost totals for a generic event-bound program `x` of `runtimeR m0R` with its
charge bounds as hypotheses (the canonical instances are the challenge prefix `prefixR A L` and the
whole game `gameR A L`).

* **The trace-weighted classical calls** (`totalWeight_calls_le`): with at most `K` classical
  calls (reads, programs, records) on every path, the traces of the inputs of the read and
  program calls add up to at most `K` (Mismatch's `totalWeight_chargeTrace_le`). Security's
  `callTot` is at most `clsCap` (`callTot_le_clsCap`).
* **The database grade at the calls** (`forallQueries_of_charge_step`,
  `querySupportedOn_runtimeR_step`): every port of `runtimeR` raises the largest database by at
  most one, so with at most `n` sponge and `K` classical calls every call is presented an
  operator supported on databases of grade at most `n + K`.
* **The flip terms of a `k`, `k'` read** (`eps_readK_le`, `eps_readK'_le`, `epsW_readK_le`,
  `epsW_readK'_le`): CostLift's `ε, ε'` off the empty read cell, bounded by FlipCost's cell-read
  certificate with CostLift's capacity-scale counts (`card_flip_readK_bad_le`,
  `card_flip_readK'_bad_le`) at grade `T = 2^68` and `G = 18`: at most `2^-301 tr σ` each.
* **The flip terms along a run** (`totalWeight_epsW_le_add`): with `progCap + n + K ≤ 2^68`, the
  flip terms of the reads add up to at most `2^-300` per unit of the trace-weighted call count,
  plus those of the reads other than `k`, `k'` reads keeping the memory and the randomizer trials'
  selecting `h`-reads (`ReadOk`; the residual `epsRestWt`). The trial reads have no `ε` term.
  A program calling only `ReadOk` reads (zero charge `bR`) has no residual
  (`totalWeight_epsW_le`).
* **The challenge prefix calls only `ReadOk` reads** (`chgB_prefixR`, per component:
  `chgB_grindR`, `chgB_signLayerT`, `chgB_signT`, `chgB_challengeT`, `chgB_prefixT`). The
  verification's `h`-reads (`readsProgram`) are the game's residual (`epsTot_le_add`).
* **The programs** (`totalWeight_progs_le`, `uavg_progs_le_of_view`): the trace-weighted program
  calls are at most `progCap`, so `2^-128` per unit of them is `progTerm`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

universe u v w u₁ v₁

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

/-! ## Charge bounds: monotonicity in the charge, the zero charge -/

section charge

/-- A charge bound holds for every smaller charge. -/
theorem isChargeBound_mono_charge {I : Type*} {P : IPFunctor.Endo I} {F : I → Type*}
    {c c' : (s : I) → P.A s → ℕ} (hc : ∀ s a, c' s a ≤ c s a) {s : I} {x : IFreeM P F s}
    {n : ℕ} (h : x.IsChargeBound c n) : x.IsChargeBound c' n := by
  induction x using IFreeM.inductionOn generalizing n with
  | pure _ _ => trivial
  | liftBind s a next ih =>
    rw [IFreeM.isChargeBound_liftBind_iff] at h ⊢
    exact ⟨(hc s a).trans h.1, fun b ↦ ih b ((h.2 b).mono (Nat.sub_le_sub_left (hc s a) n))⟩

/-- Every program is within budget `0` of the zero charge. -/
theorem isChargeBound_zero {I : Type*} {P : IPFunctor.Endo I} {F : I → Type*} {s : I}
    (x : IFreeM P F s) : x.IsChargeBound (fun _ _ ↦ 0) 0 := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => trivial
  | liftBind s a next ih => exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨le_rfl, ih⟩

end charge

/-! ## The trace-weighted classical calls -/

section calls

/-- The initial state of `runtimeR m0R` beside the trivial register has trace at most one. -/
theorem ofReal_trace_initR_le_one : ENNReal.ofReal initR.trace.re ≤ 1 :=
  ENNReal.ofReal_le_one.mpr
    ((SubState.basis ()).prod (runtimeR (X := X) (Z := Z) m0R).init).trace_re_le_one

/-- **The trace-weighted classical calls of a program**: with at most `K` classical calls (reads,
programs, records) on every path, the traces of the inputs of the read and program calls add up to
at most `K`. -/
theorem totalWeight_calls_le {Ω : QReg → Type}
    (x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))
    {K : ℕ} (hK : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z Mem (recSpec HPos Selections) i then 1 else 0) K) :
    (runtimeR m0R).totalWeight .instruments (extWeight (hwCost
      (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re)) x initR ≤ K := by
  refine (totalWeight_le_totalWeight (runtimeR m0R) .instruments
    (w' := fun i σ ↦ ((if extCls X Z Mem (recSpec HPos Selections) i then 1 else 0 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal σ.trace.re) (fun i σ _ ↦ ?_) x initR_posSemidef).trans ?_
  · rcases i with ((p | c) | c) | T <;> simp [extWeight, sumWeight, hwCost, extCls, hwCls]
    all_goals exact le_of_eq rfl
  · refine (totalWeight_chargeTrace_le (runtimeR m0R) .instruments _ x hK
      initR_posSemidef).trans ?_
    calc (K : ℝ≥0∞) * ENNReal.ofReal initR.trace.re ≤ K * 1 := by
          gcongr
          exact ofReal_trace_initR_le_one
      _ = K := mul_one _

end calls

/-! ## The database grade at the calls -/

section grade

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) (g : R.D → ℕ)
  (κ κb : spec.Port → ℕ)

/-- **The grade at every call, and the calls of zero charge.** If port `i` raises the grade of the
support by at most `κ i`, a program of charge at most `n` from support on grades at most `t`
presents every call an operator supported on grades at most `t + n`; with a second charge `κb` of
budget `0`, every port called has `κb i = 0`. -/
theorem forallQueries_of_charge_step
    (hR : ∀ i r t (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t) σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ g m.2) (Set.Iic (t + κ i))
          ((R.step i).branch r σ))
    {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w} {A : QReg}
    (x : QuantumComp L spec Ω A) {n : ℕ} (hx : IFreeM.IsChargeBound x (portCharge κ) n)
    (hb : IFreeM.IsChargeBound x (portCharge κb) 0) {t : ℕ} {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (hρ : QuerySupportedOn (fun m : A × R.D ↦ g m.2) (Set.Iic t) ρ) :
    R.ForallQueries I (fun i E σ ↦ κb i = 0 ∧
      QuerySupportedOn (fun m : (spec.In i × R.D) × E ↦ g m.1.2) (Set.Iic (t + n)) σ) x ρ := by
  induction x using QuantumComp.inductionOn generalizing n t with
  | pure _ _ => trivial
  | primBind _ o k ih =>
    rw [isChargeBound_portCharge_primBind_iff] at hx hb
    rw [QuantumRuntime.forallQueries_primBind_iff]
    exact fun b ↦ ih b (hx b) (hb b) (QuerySupportedOn.amplify_snd (q := g) hρ _)
  | queryBind _ i E ℓ k ih =>
    obtain ⟨hq, hk⟩ := (isChargeBound_portCharge_queryBind_iff κ i E ℓ k n).mp hx
    obtain ⟨hqb, hkb⟩ := (isChargeBound_portCharge_queryBind_iff κb i E ℓ k 0).mp hb
    rw [QuantumRuntime.forallQueries_queryBind_iff]
    refine ⟨⟨Nat.le_zero.mp hqb, ?_⟩, fun r ↦ ?_⟩
    · have h₁ := (hρ.branch_relabel (QuantumRuntime.queryEquivIn ℓ R.D)).imp
        (q' := fun m : (spec.In i × R.D) × E ↦ g m.1.2) (S' := Set.Iic t) fun m hm ↦ by
          obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ R.D).surjective m
          rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm
      exact h₁.mono (Set.Iic_subset_Iic.2 (Nat.le_add_right t n))
    · have hb' := hkb r
      rw [Nat.zero_sub] at hb'
      have he : t + κ i + (n - κ i) = t + n := by omega
      exact (ih r (hk r) hb'
        (QuerySupportedOn.queryStep_of_charge_step R g κ hR i E ℓ r hρ)).mono I
          fun _ _ _ h ↦ ⟨h.1, he ▸ h.2⟩

end grade

/-- **Every port of `runtimeR` raises the database grade by at most one**: those of runtime 2
(`querySupportedOn_spongeHardwiredRuntime_step`), and the record ports, which keep the databases. -/
theorem querySupportedOn_runtimeR_step (m₀ : Mem) (i : (recHwSpec X Z HPos Selections).Port)
    (r : (recHwSpec X Z HPos Selections).Result i) (t : ℕ)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m₀).D)
      ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m₀).D) ℂ)
    (hσ : QuerySupportedOn (fun q : (recHwSpec X Z HPos Selections).In i ×
      (runtimeR (X := X) (Z := Z) m₀).D ↦ dbGrade q.2.1) (Set.Iic t) σ) :
    QuerySupportedOn (fun q : (recHwSpec X Z HPos Selections).Out i ×
      (runtimeR (X := X) (Z := Z) m₀).D ↦ dbGrade q.2.1) (Set.Iic (t + 1))
        (((runtimeR (X := X) (Z := Z) m₀).step i).branch r σ) := by
  rcases i with i | j
  · exact querySupportedOn_spongeHardwiredRuntime_step (hwEmpty X Z) m₀ i r t σ hσ
  · exact querySupportedOn_recStep j r t σ hσ

/-- The initial state has empty databases. -/
theorem querySupportedOn_initR :
    QuerySupportedOn (fun m : QReg.of Unit × (runtimeR (X := X) (Z := Z) m0R).D ↦ dbGrade m.2.1)
      (Set.Iic 0) initR := by
  intro m m' hm
  change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty X Z, m0R) : HwReg X Z Mem)).matrix) m m' ≠ 0 at hm
  simp only [SubState.matrix_basis] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · constructor <;> simp [← he.1, ← he.2, dbGrade, Database.size_empty]
  · exact False.elim (h rfl)

/-! ## The flip terms of a `k`, `k'` read -/

section readKGen

variable {X₁ Z₁ M : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
  [Fintype M] [DecidableEq M]

/-- **The flip terms of a read of a `k` cell that keeps the memory** (the `ε, ε'` part of
CostLift's `flipCost_readK_le`): with `P = readPs SR`, `SR` states whose cell `x` is neither
recorded nor hardwired, both are at most `E = ∑_{SR, ∉ B} c / |Z| · σ_ss`. -/
theorem eps_readK_le [Nonempty Z₁] (B : Set (HwReg X₁ Z₁ M)) [DecidablePred (· ∈ B)] (x : X₁)
    (upd : M → Option Z₁ → M) (hupd : ∀ m o, upd m o = m) (SR : HwReg X₁ Z₁ M → Prop)
    [DecidablePred SR] (c : HwReg X₁ Z₁ M → ℕ)
    (hSR : ∀ s, SR s → s.1.2.1 x = none ∧ s.2.1.2.1 x = none)
    (hcnt : ∀ s, SR s → s ∉ B → (Finset.univ.filter fun b : Z₁ ↦
      ((s.1.1, Function.update s.1.2.1 x (some b), s.1.2.2), s.2.1, s.2.2) ∈ B).card ≤ c s)
    (hmono : ∀ s b, SR s → s ∈ B →
      ((s.1.1, Function.update s.1.2.1 x (some b), s.1.2.2), s.2.1, s.2.2) ∈ B)
    {σ : Matrix (Unit × HwReg X₁ Z₁ M) (Unit × HwReg X₁ Z₁ M) ℂ} (hσ : σ.PosSemidef) :
    ((1 - readPs SR) * (∑ r : (HwRead.readK x upd : HwRead X₁ Z₁ M).Result,
      (hwReadKraus (.readK x upd) r)ᴴ * indProj (liftSet B) * hwReadKraus (.readK x upd) r -
        indProj (liftSet B)) * (1 - readPs SR) * σ).trace.re ≤
        ∑ q, (if SR q.2 ∧ q.2 ∉ B then (c q.2 : ℝ) / Fintype.card Z₁ * (σ q q).re else 0) ∧
      ((1 - readPs SR) * (∑ r : (HwRead.readK x upd : HwRead X₁ Z₁ M).Result,
      (hwReadKraus (.readK x upd) r)ᴴ * indProj (liftSet B) * hwReadKraus (.readK x upd) r -
        indProj (liftSet B)) * readPs SR * (∑ r : (HwRead.readK x upd : HwRead X₁ Z₁ M).Result,
      (hwReadKraus (.readK x upd) r)ᴴ * indProj (liftSet B) * hwReadKraus (.readK x upd) r -
        indProj (liftSet B)) * (1 - readPs SR) * σ).trace.re ≤
        ∑ q, (if SR q.2 ∧ q.2 ∉ B then (c q.2 : ℝ) / Fintype.card Z₁ * (σ q q).re else 0) := by
  set gd : RestK X₁ Z₁ M x → Prop := fun r ↦ SR ((splitK x).symm (none, r)).2
  have : DecidablePred gd := fun r ↦ inferInstanceAs (Decidable (SR _))
  have hgd_iff : ∀ q, (gd (splitK x q).2 ∧ (splitK x q).1 = none) ↔ SR q.2 := fun q ↦ by
    constructor
    · rintro ⟨h1, h2⟩
      have h0 : q.2.1.2.1 x = none := h2
      simpa only [gd, splitK_symm_none x q h0] using h1
    · intro hq
      have h0 := (hSR _ hq).1
      exact ⟨by simpa only [gd, splitK_symm_none x q h0] using hq, h0⟩
  have hP : readPs SR = readP (splitK x) gd := by
    unfold readPs readP pp
    congr 1
    funext q
    exact ite_cond_congr (propext (hgd_iff q)).symm
  have hgdact : ∀ r, gd r → actK x r := fun r h ↦ (hSR _ h).2
  have hcell := cellRead_readK (M := M) x upd
  have hF : (∑ r : (HwRead.readK x upd : HwRead X₁ Z₁ M).Result,
      (hwReadKraus (.readK x upd) r)ᴴ * indProj (liftSet B) * hwReadKraus (.readK x upd) r -
        indProj (liftSet B)) =
      flipOp (fun r : Option Z₁ × M ↦ hwReadKraus (.readK x upd) r) (liftSet B) := by
    rw [flipOp]
  have hN : (0 : ℝ) < Fintype.card Z₁ := Nat.cast_pos.2 Fintype.card_pos
  have hτ : ∀ (r : RestK X₁ Z₁ M x) (y : Z₁), tauK x upd (some y) r = r := fun r y ↦ by
    simp only [tauK, hupd]
  have hchw : ∀ q : Unit × HwReg X₁ Z₁ M, SR q.2 →
      chw (splitK x) (tauK x upd) (liftSet B) (splitK x q).2 ≤
        if q.2 ∈ B then 0 else (c q.2 : ℝ) := by
    intro q hq
    refine (chw_le_card_of_keep (liftSet B) _ fun y ↦ hτ _ y).trans ?_
    have hq0 : q0 (splitK x) (liftSet B) (splitK x q).2 = if q.2 ∈ B then 1 else 0 := by
      rw [q0, splitK_symm_none x q (hSR _ hq).1]
      rfl
    have hy : ∀ b : Z₁, ind (liftSet B) ((splitK x).symm (some b, (splitK x q).2)) =
        if ((q.2.1.1, Function.update q.2.1.2.1 x (some b), q.2.1.2.2), q.2.2.1, q.2.2.2) ∈ B
          then 1 else 0 := fun b ↦ by
      rw [splitK_symm_fill]
      rfl
    simp only [hq0, hy]
    by_cases hS : q.2 ∈ B
    · simp only [hS, ↓reduceIte]
      rw [Nat.cast_nonpos, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro b _ hb
      exact hb (ite_eq_left (hmono q.2 b hq hS))
    · simp only [hS, ↓reduceIte]
      rw [Nat.cast_le]
      refine (Finset.card_le_card fun b hb ↦ ?_).trans (hcnt q.2 hq hS)
      have hb' := (Finset.mem_filter.1 hb).2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      by_contra hn
      exact hb' (ite_eq_right hn)
  have hE : (∑ q, if gd (splitK x q).2 ∧ (splitK x q).1 = none then
        chw (splitK x) (tauK x upd) (liftSet B) (splitK x q).2 / Fintype.card Z₁ * (σ q q).re
          else 0) ≤
      ∑ q, if SR q.2 ∧ q.2 ∉ B then (c q.2 : ℝ) / Fintype.card Z₁ * (σ q q).re else 0 := by
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [ite_cond_congr (propext (hgd_iff q))]
    have hre : 0 ≤ (σ q q).re := (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    by_cases hq : SR q.2
    · have hc := hchw q hq
      by_cases hS : q.2 ∈ B
      · rw [ite_eq_left hS] at hc
        rw [ite_eq_left hq, ite_eq_right fun h ↦ h.2 hS]
        exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hc hN.le) hre
      · rw [ite_eq_right hS] at hc
        rw [ite_eq_left hq, ite_eq_left ⟨hq, hS⟩]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hc hN.le) hre
    · rw [ite_eq_right hq, ite_eq_right fun h ↦ hq h.1]
  refine ⟨?_, ?_⟩
  · rw [hF, hP]
    exact (re_trace_eps_le (liftSet B) gd hcell hgdact hσ).trans hE
  · rw [hF, hP]
    exact (re_trace_eps'_le (liftSet B) gd hcell hgdact hσ).trans hE

/-- **The flip terms of a read of a `k'` cell that keeps the memory** (as `eps_readK_le`). -/
theorem eps_readK'_le [Nonempty Z₁] (B : Set (HwReg X₁ Z₁ M)) [DecidablePred (· ∈ B)] (x : X₁)
    (upd : M → Option Z₁ → M) (hupd : ∀ m o, upd m o = m) (SR : HwReg X₁ Z₁ M → Prop)
    [DecidablePred SR] (c : HwReg X₁ Z₁ M → ℕ)
    (hSR : ∀ s, SR s → s.1.2.2 x = none ∧ s.2.1.2.2 x = none)
    (hcnt : ∀ s, SR s → s ∉ B → (Finset.univ.filter fun b : Z₁ ↦
      ((s.1.1, s.1.2.1, Function.update s.1.2.2 x (some b)), s.2.1, s.2.2) ∈ B).card ≤ c s)
    (hmono : ∀ s b, SR s → s ∈ B →
      ((s.1.1, s.1.2.1, Function.update s.1.2.2 x (some b)), s.2.1, s.2.2) ∈ B)
    {σ : Matrix (Unit × HwReg X₁ Z₁ M) (Unit × HwReg X₁ Z₁ M) ℂ} (hσ : σ.PosSemidef) :
    ((1 - readPs SR) * (∑ r : (HwRead.readK' x upd : HwRead X₁ Z₁ M).Result,
      (hwReadKraus (.readK' x upd) r)ᴴ * indProj (liftSet B) * hwReadKraus (.readK' x upd) r -
        indProj (liftSet B)) * (1 - readPs SR) * σ).trace.re ≤
        ∑ q, (if SR q.2 ∧ q.2 ∉ B then (c q.2 : ℝ) / Fintype.card Z₁ * (σ q q).re else 0) ∧
      ((1 - readPs SR) * (∑ r : (HwRead.readK' x upd : HwRead X₁ Z₁ M).Result,
      (hwReadKraus (.readK' x upd) r)ᴴ * indProj (liftSet B) * hwReadKraus (.readK' x upd) r -
        indProj (liftSet B)) * readPs SR * (∑ r : (HwRead.readK' x upd : HwRead X₁ Z₁ M).Result,
      (hwReadKraus (.readK' x upd) r)ᴴ * indProj (liftSet B) * hwReadKraus (.readK' x upd) r -
        indProj (liftSet B)) * (1 - readPs SR) * σ).trace.re ≤
        ∑ q, (if SR q.2 ∧ q.2 ∉ B then (c q.2 : ℝ) / Fintype.card Z₁ * (σ q q).re else 0) := by
  set gd : RestK X₁ Z₁ M x → Prop := fun r ↦ SR ((splitK' x).symm (none, r)).2
  have : DecidablePred gd := fun r ↦ inferInstanceAs (Decidable (SR _))
  have hgd_iff : ∀ q, (gd (splitK' x q).2 ∧ (splitK' x q).1 = none) ↔ SR q.2 := fun q ↦ by
    constructor
    · rintro ⟨h1, h2⟩
      have h0 : q.2.1.2.2 x = none := h2
      simpa only [gd, splitK'_symm_none x q h0] using h1
    · intro hq
      have h0 := (hSR _ hq).1
      exact ⟨by simpa only [gd, splitK'_symm_none x q h0] using hq, h0⟩
  have hP : readPs SR = readP (splitK' x) gd := by
    unfold readPs readP pp
    congr 1
    funext q
    exact ite_cond_congr (propext (hgd_iff q)).symm
  have hgdact : ∀ r, gd r → actK' x r := fun r h ↦ (hSR _ h).2
  have hcell := cellRead_readK' (M := M) x upd
  have hF : (∑ r : (HwRead.readK' x upd : HwRead X₁ Z₁ M).Result,
      (hwReadKraus (.readK' x upd) r)ᴴ * indProj (liftSet B) * hwReadKraus (.readK' x upd) r -
        indProj (liftSet B)) =
      flipOp (fun r : Option Z₁ × M ↦ hwReadKraus (.readK' x upd) r) (liftSet B) := by
    rw [flipOp]
  have hN : (0 : ℝ) < Fintype.card Z₁ := Nat.cast_pos.2 Fintype.card_pos
  have hτ : ∀ (r : RestK X₁ Z₁ M x) (y : Z₁), tauK x upd (some y) r = r := fun r y ↦ by
    simp only [tauK, hupd]
  have hchw : ∀ q : Unit × HwReg X₁ Z₁ M, SR q.2 →
      chw (splitK' x) (tauK x upd) (liftSet B) (splitK' x q).2 ≤
        if q.2 ∈ B then 0 else (c q.2 : ℝ) := by
    intro q hq
    refine (chw_le_card_of_keep (liftSet B) _ fun y ↦ hτ _ y).trans ?_
    have hq0 : q0 (splitK' x) (liftSet B) (splitK' x q).2 = if q.2 ∈ B then 1 else 0 := by
      rw [q0, splitK'_symm_none x q (hSR _ hq).1]
      rfl
    have hy : ∀ b : Z₁, ind (liftSet B) ((splitK' x).symm (some b, (splitK' x q).2)) =
        if ((q.2.1.1, q.2.1.2.1, Function.update q.2.1.2.2 x (some b)), q.2.2.1, q.2.2.2) ∈ B
          then 1 else 0 := fun b ↦ by
      rw [splitK'_symm_fill]
      rfl
    simp only [hq0, hy]
    by_cases hS : q.2 ∈ B
    · simp only [hS, ↓reduceIte]
      rw [Nat.cast_nonpos, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro b _ hb
      exact hb (ite_eq_left (hmono q.2 b hq hS))
    · simp only [hS, ↓reduceIte]
      rw [Nat.cast_le]
      refine (Finset.card_le_card fun b hb ↦ ?_).trans (hcnt q.2 hq hS)
      have hb' := (Finset.mem_filter.1 hb).2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      by_contra hn
      exact hb' (ite_eq_right hn)
  have hE : (∑ q, if gd (splitK' x q).2 ∧ (splitK' x q).1 = none then
        chw (splitK' x) (tauK x upd) (liftSet B) (splitK' x q).2 / Fintype.card Z₁ * (σ q q).re
          else 0) ≤
      ∑ q, if SR q.2 ∧ q.2 ∉ B then (c q.2 : ℝ) / Fintype.card Z₁ * (σ q q).re else 0 := by
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [ite_cond_congr (propext (hgd_iff q))]
    have hre : 0 ≤ (σ q q).re := (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    by_cases hq : SR q.2
    · have hc := hchw q hq
      by_cases hS : q.2 ∈ B
      · rw [ite_eq_left hS] at hc
        rw [ite_eq_left hq, ite_eq_right fun h ↦ h.2 hS]
        exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hc hN.le) hre
      · rw [ite_eq_right hS] at hc
        rw [ite_eq_left hq, ite_eq_left ⟨hq, hS⟩]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hc hN.le) hre
    · rw [ite_eq_right hq, ite_eq_right fun h ↦ hq h.1]
  refine ⟨?_, ?_⟩
  · rw [hF, hP]
    exact (re_trace_eps_le (liftSet B) gd hcell hgdact hσ).trans hE
  · rw [hF, hP]
    exact (re_trace_eps'_le (liftSet B) gd hcell hgdact hσ).trans hE

omit [DecidableEq M] in
/-- The weighted count `E` with `c ≤ C` on the support is at most `C / |Z| · tr σ`. -/
theorem sum_cnt_le (B : Set (HwReg X₁ Z₁ M)) [DecidablePred (· ∈ B)] (SR : HwReg X₁ Z₁ M → Prop)
    [DecidablePred SR] (c : HwReg X₁ Z₁ M → ℕ) (C : ℕ)
    {σ : Matrix (Unit × HwReg X₁ Z₁ M) (Unit × HwReg X₁ Z₁ M) ℂ} (hσ : σ.PosSemidef)
    (hC : ∀ q, σ q q ≠ 0 → c q.2 ≤ C) :
    (∑ q, if SR q.2 ∧ q.2 ∉ B then (c q.2 : ℝ) / Fintype.card Z₁ * (σ q q).re else 0) ≤
      C / Fintype.card Z₁ * σ.trace.re := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hN : (0 : ℝ) ≤ Fintype.card Z₁ := Nat.cast_nonneg _
  rw [Matrix.trace, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  split_ifs
  · by_cases hσq : σ q q = 0
    · simp [hσq]
    · exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (Nat.cast_le.2 (hC q hσq)) hN) (hre q)
  · exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) hN) (hre q)

omit [DecidableEq Z₁] [Fintype M] [DecidableEq M] in
/-- **Filling an empty `k` cell keeps a target event.** -/
theorem mem_hwTargetBad_fillK [AddCommGroup X₁] [AddCommGroup Z₁] {Y : Type}
    {π : Equiv.Perm (X₁ × Z₁)} {out : X₁ → Y} {tgt : Hw X₁ Z₁ → M → List X₁ → Option Y} {N : ℕ}
    {s : HwReg X₁ Z₁ M} (hs : s ∈ HwTargetBad π out tgt N) {x : X₁} (hx : s.1.2.1 x = none)
    (b : Z₁) :
    ((s.1.1, Function.update s.1.2.1 x (some b), s.1.2.2), s.2.1, s.2.2) ∈
      HwTargetBad π out tgt N :=
  ⟨hs.1, TargetBad.mono (extendsAll_union s.2.1 (D := s.1)
    (D' := (s.1.1, Function.update s.1.2.1 x (some b), s.1.2.2)) (fun _ _ h ↦ h)
    (fun _ _ h ↦ update_some_of_none hx h) fun _ _ h ↦ h) hs.2⟩

omit [DecidableEq Z₁] [Fintype M] [DecidableEq M] in
/-- **Filling an empty `k'` cell keeps a target event.** -/
theorem mem_hwTargetBad_fillK' [AddCommGroup X₁] [AddCommGroup Z₁] {Y : Type}
    {π : Equiv.Perm (X₁ × Z₁)} {out : X₁ → Y} {tgt : Hw X₁ Z₁ → M → List X₁ → Option Y} {N : ℕ}
    {s : HwReg X₁ Z₁ M} (hs : s ∈ HwTargetBad π out tgt N) {x : X₁} (hx : s.1.2.2 x = none)
    (b : Z₁) :
    ((s.1.1, s.1.2.1, Function.update s.1.2.2 x (some b)), s.2.1, s.2.2) ∈
      HwTargetBad π out tgt N :=
  ⟨hs.1, TargetBad.mono (extendsAll_union s.2.1 (D := s.1)
    (D' := (s.1.1, s.1.2.1, Function.update s.1.2.2 x (some b))) (fun _ _ h ↦ h)
    (fun _ _ h ↦ h) fun _ _ h ↦ update_some_of_none hx h) hs.2⟩

end readKGen

/-! ## The flip terms of the `k`, `k'` reads for `BadR` -/

section epsW

attribute [local instance] badRDec

/-- The capacity-scale count of a filled `k` cell at grade `2^68` (`card_flip_readK_bad_le`). -/
def capK : ℕ := (2 ^ 68 + 1) * ((2 ^ 68 + 1) * 2 ^ 68 + 2 * 2 ^ 68) * 18

/-- The capacity-scale count of a filled `k'` cell at grade `2^68` (`card_flip_readK'_bad_le`). -/
def capK' : ℕ := (2 ^ 68 + 1) + 2 ^ 68 * ((2 ^ 68 + 1) * 2 ^ 68 + 2 ^ 68 + 1) * 18 +
  2 ^ 68 * 2 ^ 68 * 18 + 2 ^ 68

theorem capK_le : capK ≤ 2 ^ 211 := by
  unfold capK
  norm_num

theorem capK'_le : capK' ≤ 2 ^ 211 := by
  unfold capK'
  norm_num

/-- Two flip terms below `C / |Z| · tr σ` with `C ≤ 2^211` sum to at most `2^-300 tr σ`. -/
theorem ofReal_add_le_of_cap {a a' E : ℝ} {C : ℕ} (hC : C ≤ 2 ^ 211)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (ha : a ≤ E) (ha' : a' ≤ E) (hE : E ≤ C / Fintype.card Z * σ.trace.re) :
    ENNReal.ofReal a + ENNReal.ofReal a' ≤ (2 ^ 300 : ℝ≥0∞)⁻¹ * ENNReal.ofReal σ.trace.re := by
  have htr : 0 ≤ σ.trace.re := (Complex.nonneg_iff.1 hσ.trace_nonneg).1
  have hc : (C : ℝ) / Fintype.card Z ≤ (2 ^ 301 : ℝ)⁻¹ := by
    rw [card_Z, Nat.cast_pow, Nat.cast_ofNat,
      show (2 : ℝ) ^ 512 = 2 ^ 211 * 2 ^ 301 by rw [← pow_add], div_le_iff₀ (by positivity),
      mul_comm ((2 : ℝ) ^ 211), ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    exact_mod_cast hC
  have hb : E ≤ (2 ^ 301 : ℝ)⁻¹ * σ.trace.re := hE.trans (mul_le_mul_of_nonneg_right hc htr)
  have hsum : (2 ^ 301 : ℝ)⁻¹ * σ.trace.re + (2 ^ 301 : ℝ)⁻¹ * σ.trace.re =
      (2 ^ 300 : ℝ)⁻¹ * σ.trace.re := by
    rw [show (2 : ℝ) ^ 301 = 2 ^ 300 * 2 from pow_succ 2 300, mul_inv]
    generalize ((2 : ℝ) ^ 300)⁻¹ = u
    ring
  calc ENNReal.ofReal a + ENNReal.ofReal a'
      ≤ ENNReal.ofReal ((2 ^ 301 : ℝ)⁻¹ * σ.trace.re) +
          ENNReal.ofReal ((2 ^ 301 : ℝ)⁻¹ * σ.trace.re) :=
        add_le_add (ENNReal.ofReal_le_ofReal (ha.trans hb))
          (ENNReal.ofReal_le_ofReal (ha'.trans hb))
    _ = (2 ^ 300 : ℝ≥0∞)⁻¹ * ENNReal.ofReal σ.trace.re := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), hsum,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

/-- The `k`-read port of the template (`rdK`), on the labelled memory. -/
abbrev readKPort (x : X) : HwRead X Z Mem :=
  liftRead (S := HPos) (.readK x (keepMem (M := Selections)))

/-- The `k'`-read port of the template (`rdK'`), on the labelled memory. -/
abbrev readK'Port (x : X) : HwRead X Z Mem :=
  liftRead (S := HPos) (.readK' x (keepMem (M := Selections)))

/-- **The flip terms of a `k` read for `BadR`**: on states with at most `2^68 - progCap` database
entries per function, `ε + ε' ≤ 2^-300 tr σ` (`PermGood π 18`). -/
theorem epsW_readK_le (L : HonestTable) (hπ : PermGood L.perm 18) (x : X)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hsupp : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ 2 ^ 68) :
    epsW Prod.snd trialUpd (BadR L progCap) L (readKPort x) σ ≤
      (2 ^ 300 : ℝ≥0∞)⁻¹ * ENNReal.ofReal σ.trace.re := by
  have ht : ¬IsTrial trialUpd (readKPort x) := by
    rintro ⟨zt, h⟩
    cases h
  set SR := trialSR Prod.snd trialUpd L (readKPort x)
  have hSR : ∀ s, SR s → s.1.2.1 x = none ∧ s.2.1.2.1 x = none := fun s hs ↦ by
    rcases hs with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h ht
    · exact h
  set cnt : HwReg X Z Mem → ℕ := fun s ↦
    if progCap + dbGrade s.1 ≤ 2 ^ 68 then capK else Fintype.card Z
  have hcnt : ∀ s, SR s → s ∉ BadR L progCap → (Finset.univ.filter fun b : Z ↦
      ((s.1.1, Function.update s.1.2.1 x (some b), s.1.2.2), s.2.1, s.2.2) ∈
        BadR L progCap).card ≤ cnt s := fun s hs hB ↦ by
    by_cases hT : progCap + dbGrade s.1 ≤ 2 ^ 68
    · simp only [cnt, ite_eq_left hT]
      exact card_filter_le_of_imp (card_flip_readK_bad_le (L := L) (N := progCap) (T := 2 ^ 68)
        (D := s.1) (W := s.2.1) (m := s.2.2.2) hπ hB hT (hSR s hs).1 (hSR s hs).2) fun _ hb ↦ hb
    · simp only [cnt, ite_eq_right hT]
      exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ
  have hmono : ∀ s b, SR s → s ∈ BadR L progCap →
      ((s.1.1, Function.update s.1.2.1 x (some b), s.1.2.2), s.2.1, s.2.2) ∈ BadR L progCap :=
    fun s b hs hB ↦ mem_hwTargetBad_fillK (s := (s.1, s.2.1, s.2.2.2)) hB (hSR s hs).1 b
  obtain ⟨hε, hε'⟩ := eps_readK_le (BadR L progCap) x (fun m o ↦ (m.1, keepMem m.2 o))
    (fun _ _ ↦ rfl) SR cnt hSR hcnt hmono hσ
  have hE := sum_cnt_le (BadR L progCap) SR cnt capK hσ fun q hq ↦ by
    simp only [cnt, ite_eq_left (hsupp q hq), le_refl]
  unfold epsW flipF
  rw [ite_eq_right ht, one_kronecker_hwProjector]
  exact ofReal_add_le_of_cap capK_le hσ hε hε' hE

/-- **The flip terms of a `k'` read for `BadR`** (as `epsW_readK_le`). -/
theorem epsW_readK'_le (L : HonestTable) (hπ : PermGood L.perm 18) (x : X)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hsupp : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ 2 ^ 68) :
    epsW Prod.snd trialUpd (BadR L progCap) L (readK'Port x) σ ≤
      (2 ^ 300 : ℝ≥0∞)⁻¹ * ENNReal.ofReal σ.trace.re := by
  have ht : ¬IsTrial trialUpd (readK'Port x) := by
    rintro ⟨zt, h⟩
    cases h
  set SR := trialSR Prod.snd trialUpd L (readK'Port x)
  have hSR : ∀ s, SR s → s.1.2.2 x = none ∧ s.2.1.2.2 x = none := fun s hs ↦ by
    rcases hs with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h ht
    · exact h
  set cnt : HwReg X Z Mem → ℕ := fun s ↦
    if progCap + dbGrade s.1 ≤ 2 ^ 68 then capK' else Fintype.card Z
  have hcnt : ∀ s, SR s → s ∉ BadR L progCap → (Finset.univ.filter fun b : Z ↦
      ((s.1.1, s.1.2.1, Function.update s.1.2.2 x (some b)), s.2.1, s.2.2) ∈
        BadR L progCap).card ≤ cnt s := fun s hs hB ↦ by
    by_cases hT : progCap + dbGrade s.1 ≤ 2 ^ 68
    · simp only [cnt, ite_eq_left hT]
      exact card_filter_le_of_imp (card_flip_readK'_bad_le (L := L) (N := progCap) (T := 2 ^ 68)
        (D := s.1) (W := s.2.1) (m := s.2.2.2) hπ hB hT (hSR s hs).1 (hSR s hs).2) fun _ hb ↦ hb
    · simp only [cnt, ite_eq_right hT]
      exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ
  have hmono : ∀ s b, SR s → s ∈ BadR L progCap →
      ((s.1.1, s.1.2.1, Function.update s.1.2.2 x (some b)), s.2.1, s.2.2) ∈ BadR L progCap :=
    fun s b hs hB ↦ mem_hwTargetBad_fillK' (s := (s.1, s.2.1, s.2.2.2)) hB (hSR s hs).1 b
  obtain ⟨hε, hε'⟩ := eps_readK'_le (BadR L progCap) x (fun m o ↦ (m.1, keepMem m.2 o))
    (fun _ _ ↦ rfl) SR cnt hSR hcnt hmono hσ
  have hE := sum_cnt_le (BadR L progCap) SR cnt capK' hσ fun q hq ↦ by
    simp only [cnt, ite_eq_left (hsupp q hq), le_refl]
  unfold epsW flipF
  rw [ite_eq_right ht, one_kronecker_hwProjector]
  exact ofReal_add_le_of_cap capK'_le hσ hε hε' hE

end epsW

/-! ## The reads of a run -/

section readOk

/-- **The reads whose flip terms are priced here**: a `k` or `k'` read keeping the memory, or a
randomizer trial's selecting `h`-read (no `ε` term). -/
def ReadOk (c : HwRead X Z Mem) : Prop :=
  (∃ x, c = readKPort x) ∨ (∃ x, c = readK'Port x) ∨ IsTrial trialUpd c

open scoped Classical in
/-- The charge of a read port: `0` on `ReadOk` reads, `1` otherwise. -/
noncomputable def okCharge (c : HwRead X Z Mem) : ℕ := if ReadOk c then 0 else 1

theorem okCharge_eq_zero {c : HwRead X Z Mem} (h : ReadOk c) : okCharge c = 0 := ite_eq_left h

theorem readOk_of_okCharge {c : HwRead X Z Mem} (h : okCharge c = 0) : ReadOk c := by
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
noncomputable def bT : (XSpec Selections).Port → ℕ
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

attribute [local instance] badRDec

/-- The flip-term weight of the read ports. -/
noncomputable abbrev epsWt (L : HonestTable) :
    ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ → ℝ≥0∞ :=
  extWeight (hwCost (epsW Prod.snd trialUpd (BadR L progCap) L) fun _ _ ↦ 0)

/-- The trace weight of the read and program ports (Security's `callTot` weight). -/
noncomputable abbrev callWt :
    ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ → ℝ≥0∞ :=
  extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re)

open scoped Classical in
/-- **The residual flip terms**: those of the read ports that are not `ReadOk` (for the whole game,
the verification's `h`-reads). -/
noncomputable def epsRestWt (L : HonestTable) :
    ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ → ℝ≥0∞ :=
  fun i σ ↦ if bR i = 0 then 0 else epsWt L i σ

/-- Every program is within budget `0` of the zero port charge. -/
theorem isChargeBound_portCharge_zero {Ω : QReg → Type}
    (x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit)) :
    IFreeM.IsChargeBound x (portCharge fun _ : (recHwSpec X Z HPos Selections).Port ↦ 0) 0 :=
  isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl) (isChargeBound_zero x)

/-- **The flip terms of the reads along a run.** A program of `runtimeR m0R` with at most `n`
sponge and `K` classical calls, `progCap + n + K ≤ 2^68`: the flip terms `ε + ε'` of its reads
(`epsW`) add up to at most `2^-300` per unit of the trace-weighted call count plus the flip terms
of the reads that are not `ReadOk` (`epsRestWt`), at a table with `PermGood π 18`. -/
theorem totalWeight_epsW_le_add (L : HonestTable) (hπ : PermGood L.perm 18) {Ω : QReg → Type}
    (x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))
    {n K : ℕ}
    (hn : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z Mem (recSpec HPos Selections) i then 0 else 1) n)
    (hK : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z Mem (recSpec HPos Selections) i then 1 else 0) K)
    (hT : progCap + (n + K) ≤ 2 ^ 68) :
    (runtimeR m0R).totalWeight .instruments (epsWt L) x initR ≤
      (2 ^ 300 : ℝ≥0∞)⁻¹ * (runtimeR m0R).totalWeight .instruments callWt x initR +
        (runtimeR m0R).totalWeight .instruments (epsRestWt L) x initR := by
  set κ : (recHwSpec X Z HPos Selections).Port → ℕ := fun i ↦
    (if extCls X Z Mem (recSpec HPos Selections) i then 0 else 1) +
      (if extCls X Z Mem (recSpec HPos Selections) i then 1 else 0) with hκ
  have hκ1 : ∀ i, κ i = 1 := fun i ↦ by
    rw [hκ]
    by_cases h : extCls X Z Mem (recSpec HPos Selections) i = true <;> simp [h]
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
    if ∀ a, σ a a ≠ 0 → dbGrade a.2.1 ≤ n + K then epsWt L i σ else 0
  have hcongr := totalWeight_congr_of_forallQueries (runtimeR m0R) .instruments
    (w := epsWt L) (w' := wm) (fun i E σ hP ↦ by
      have hc : ∀ a, MatrixMap.traceRight
          ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) E σ a a ≠ 0 →
            dbGrade a.2.1 ≤ n + K := fun a ha ↦ by
        obtain ⟨e, he⟩ : ∃ e, σ (a, e) (a, e) ≠ 0 := by
          by_contra h
          exact ha (traceRight_diag_eq_zero fun e ↦ not_not.1 fun he ↦ h ⟨e, he⟩)
        have h := (hP.2 (a, e) (a, e) he).1
        rw [Set.mem_Iic, Nat.zero_add] at h
        exact h
      exact (ite_eq_left hc).symm) x initR hfq
  refine hcongr.trans_le ((totalWeight_le_totalWeight (runtimeR m0R) .instruments
    (w' := fun i σ ↦ (2 ^ 300 : ℝ≥0∞)⁻¹ * callWt i σ + epsRestWt L i σ) (fun i σ hσ ↦ ?_) x
    initR_posSemidef).trans_eq ((totalWeight_add_weight (runtimeR m0R) .instruments _ _ x
      initR).trans (congrArg (· + _) (totalWeight_const_mul_weight (runtimeR m0R) .instruments _
        _ x initR))))
  by_cases hg : ∀ a, σ a a ≠ 0 → dbGrade a.2.1 ≤ n + K
  swap
  · rw [show wm i σ = 0 from ite_eq_right hg]
    exact zero_le
  rw [show wm i σ = epsWt L i σ from ite_eq_left hg]
  by_cases hb0 : bR i = 0
  swap
  · rw [show epsRestWt L i σ = epsWt L i σ from ite_eq_right hb0]
    exact le_add_self
  refine le_add_right ?_
  rcases i with ((p | c) | c) | T
  · simp [epsWt, extWeight, sumWeight, hwCost]
  · have hok : ReadOk c := readOk_of_okCharge hb0
    have hsupp : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ 2 ^ 68 := fun q hq ↦ by
      have := hg q hq
      omega
    rcases hok with ⟨y, rfl⟩ | ⟨y, rfl⟩ | ht
    · exact epsW_readK_le L hπ y hσ hsupp
    · exact epsW_readK'_le L hπ y hσ hsupp
    · show epsW Prod.snd trialUpd (BadR L progCap) L c σ ≤ _
      unfold epsW
      rw [ite_eq_left ht]
      exact zero_le
  · simp [epsWt, extWeight, sumWeight, hwCost]
  · simp [epsWt, extWeight, sumWeight]

/-- **No residual for a program calling only `ReadOk` reads.** -/
theorem totalWeight_epsRestWt_eq_zero (L : HonestTable) {Ω : QReg → Type}
    (x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))
    (hb : IFreeM.IsChargeBound x (portCharge bR) 0) :
    (runtimeR m0R).totalWeight .instruments (epsRestWt L) x initR = 0 := by
  have hfq := forallQueries_of_charge_step (runtimeR m0R) (fun _ ↦ 0) (fun _ ↦ 0) bR
    (fun _ _ _ _ _ _ _ _ ↦ ⟨Set.mem_Iic.2 (Nat.zero_le _), Set.mem_Iic.2 (Nat.zero_le _)⟩)
    .instruments x (isChargeBound_portCharge_zero x) hb
    (t := 0) (ρ := initR) fun _ _ _ ↦ ⟨Set.mem_Iic.2 le_rfl, Set.mem_Iic.2 le_rfl⟩
  exact (totalWeight_congr_of_forallQueries (runtimeR m0R) .instruments (w := epsRestWt L)
    (w' := fun i σ ↦ 0 * callWt i σ) (fun i E σ hP ↦ by
      rw [zero_mul]
      exact ite_eq_left hP.1) x initR hfq).trans
    ((totalWeight_const_mul_weight (runtimeR m0R) .instruments 0 callWt x initR).trans
      (zero_mul _))

/-- **The flip terms of the reads along a run calling only `ReadOk` reads**: at most `2^-300` per
unit of the trace-weighted call count. -/
theorem totalWeight_epsW_le (L : HonestTable) (hπ : PermGood L.perm 18) {Ω : QReg → Type}
    (x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))
    {n K : ℕ}
    (hn : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z Mem (recSpec HPos Selections) i then 0 else 1) n)
    (hK : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z Mem (recSpec HPos Selections) i then 1 else 0) K)
    (hT : progCap + (n + K) ≤ 2 ^ 68) (hb : IFreeM.IsChargeBound x (portCharge bR) 0) :
    (runtimeR m0R).totalWeight .instruments (epsWt L) x initR ≤
      (2 ^ 300 : ℝ≥0∞)⁻¹ * (runtimeR m0R).totalWeight .instruments callWt x initR := by
  have h := totalWeight_epsW_le_add L hπ x hn hK hT
  rwa [totalWeight_epsRestWt_eq_zero L x hb, add_zero] at h

end run

/-! ## The challenge prefix calls only `ReadOk` reads -/

section prefixReads

variable {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- Realizing keeps the read charge. -/
theorem chgB_realizeT (v : HPos → Digest) {A : QReg} {y : QuantumComp L (XSpec Selections) Ω A}
    {n : ℕ} (h : IFreeM.IsChargeBound y (portCharge bT) n) :
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
theorem sChgB_rdRoundU (l : Layer) (e : KeyIndex) (π : Equiv.Perm (X × Z)) (B : QReg)
    (s : X × Z) (blk : X) : SChg bD (rdRoundU Selections (cwUpd l e) π B s blk) 0 := by
  refine sChg_mono _ (sChg_bind _ (sChgB_readCall (.readK _ keepMem) (Or.inl ⟨_, rfl⟩) B _)
    fun _ ↦ sChg_bind _ (sChgB_readCall (.readK' _ keepMem) (Or.inr (Or.inl ⟨_, rfl⟩)) B _)
      fun _ ↦ sChg_bind _ (sChgB_readCall (.readH _ (cwUpd l e blk _))
        (Or.inr (Or.inr ⟨(_, ⟨l, e, blk, _⟩), rfl⟩)) B _) fun _ ↦ sChg_pure _ _ 0) (by omega)

/-- **A randomizer trial's hash** calls only `ReadOk` reads. -/
theorem chgB_hashTrial (l : Layer) (e : KeyIndex) (π : Equiv.Perm (X × Z)) (B : QReg)
    (input : HashInput) :
    IFreeM.IsChargeBound (hashTrial Selections (cwUpd l e) π B input) (portCharge bD) 0 := by
  unfold hashTrial
  rw [StateT.run'_eq]
  exact (chg_map _ _ (sChg_map _ _ (sChg_map _ _
    (sChg_foldlM _ _ _ (sChgB_rdRoundU l e π B) (blocks input) (0, 0))) [])).mono
    (le_of_eq (zero_mul _))

/-- **The randomizer search** calls only `ReadOk` reads. -/
theorem chgB_grindR (pub : Pub) (B : QReg) (l : Layer) (e : KeyIndex) (message : HashInput)
    (base : Randomizer) : ∀ n trial, IFreeM.IsChargeBound
      (grindR Selections cwUpd pub B l e message base n trial) (portCharge bD) 0
  | 0, _ => trivial
  | n + 1, trial => by
    rw [grindR]
    refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgB_hashTrial l e pub.perm B _)
      fun out ↦ ?_
    show IFreeM.IsChargeBound (match Codeword.decode (truncateHash out) with
      | some x => QuantumComp₂.pure (some (base + BitVec.ofNat digestBits trial, x))
      | none => grindR Selections cwUpd pub B l e message base n (trial + 1)) _ _
    split
    · trivial
    · exact chgB_grindR pub B l e message base n (trial + 1)

theorem chgB_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × Selections) → QComp (XSpec Selections) B B' α)
    (hk : ∀ r, IFreeM.IsChargeBound (k r) (portCharge bT) 0) :
    IFreeM.IsChargeBound (revealThen goodAll T k) (portCharge bT) 0 :=
  (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨le_rfl, fun r ↦
    FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ hk r⟩

theorem chgB_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (XSpec Selections) B B' α) (hk : IFreeM.IsChargeBound k (portCharge bT) 0) :
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

/-- **A layer signature** calls only `ReadOk` reads. -/
theorem chgB_signLayerT (pub : Pub) (B : QReg) (lab : RLabel) :
    IFreeM.IsChargeBound (signLayerT Selections cwUpd pub B lab) (portCharge bT) 0 := by
  unfold signLayerT
  refine chgB_revealThen _ _ fun _ ↦ ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    (chgB_readLift (chgB_grindR pub B _ _ _ _ _ _)) fun g ↦ ?_
  rcases g with _ | ⟨ρ, x⟩
  · trivial
  · exact chgB_revealThen _ _ fun _ ↦
      FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgB_progSlots pub B _) fun _ ↦ trivial

/-- **A signature** calls only `ReadOk` reads. -/
theorem chgB_signT (pub : Pub) (B : QReg) (r : SigningRequest) :
    IFreeM.IsChargeBound (signT Selections cwUpd pub B r) (portCharge bT) 0 := by
  unfold signT
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgB_signLayerT pub B _) fun t ↦ ?_
  rcases t with _ | ⟨bottom, f⟩
  · trivial
  · refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgB_signLayerT pub B _) fun t ↦ ?_
    rcases t with _ | ⟨top, _⟩ <;> trivial

/-- **The challenger** calls only `ReadOk` reads. -/
theorem chgB_challengeT (pub : Pub) (A : QReg)
    (cmd : QuantumComp.Cmd LocalSig.instruments.{0} (advSpec (X × Z)) A) :
    IFreeM.IsChargeBound (challengeT Selections cwUpd pub A cmd) (portCharge bT) 0 := by
  rcases cmd with o | ⟨p | r, E, ℓ⟩
  · exact chgB_readLift (chgB_simulate _ (q := 0)
      ((QuantumComp.isTotalQueryBound_primBind_iff _ _ _).mpr fun _ ↦ trivial))
  · exact chgB_readLift (chgB_simulate _ (q := 1)
      ((QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr
        ⟨Nat.one_pos, fun _ ↦ trivial⟩))
  · exact IFreeM.isChargeBound_bind (n₁ := 0) (n₂ := 0) (FreeM₂.isChargeBound_bind
      (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ chgB_signT pub _ r) fun _ _ ↦
        IFreeM.isChargeBound_pure _ 0

/-- **The challenge prefix** calls only `ReadOk` reads. -/
theorem chgB_prefixT (pub : Pub) (A : Adversary (X × Z)) :
    IFreeM.IsChargeBound (prefixT Selections cwUpd pub A) (portCharge bT) 0 := by
  unfold prefixT
  refine chgB_revealThen _ _ fun _ ↦ ?_
  exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    (IFreeM.IsChargeBound.substitute (challengeT Selections cwUpd pub) (c := fun _ _ ↦ 0)
      (fun s cmd ↦ chgB_challengeT pub s cmd) (isChargeBound_zero _)) fun _ ↦ trivial

/-- **The realized challenge prefix** calls only `ReadOk` reads. -/
theorem chgB_prefixR (A : Adversary (X × Z)) (L : HonestTable) :
    IFreeM.IsChargeBound (prefixR A L) (portCharge bR) 0 :=
  chgB_realizeT _ (chgB_prefixT _ A)

end prefixReads

/-! ## Security's `readEps` -/

section readEps

attribute [local instance] badRDec

/-- `progCap + 6q + clsCap ≤ 2^68` for `q ≤ 2^64`. -/
theorem progCap_add_le {q : ℕ} (hq : q ≤ 2 ^ 64) : progCap + (6 * q + clsCap) ≤ 2 ^ 68 := by
  have hc : progCap + clsCap ≤ 2 ^ 68 - 6 * 2 ^ 64 := by
    simp only [clsCap, signBlocks_eq, verifyBlocks_eq, progCap_eq]
    norm_num [lifetime, layerCount, layerHeight]
  omega

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **Security's `callTot`** (over the game): at most `clsCap` (`clsCalls_gameR`). -/
theorem callTot_le_clsCap (L : HonestTable) : callTot A L ≤ clsCap :=
  totalWeight_calls_le (gameR A L) (clsCalls_gameR hperm hsign L)

/-- **Security's `readEps` over the game, up to the residual reads**: for `q ≤ 2^64`, at a table
with `PermGood π 18`, `epsTot ≤ 2^-300 callTot` plus the flip terms of the game's reads that are
not `ReadOk` (the verification's `h`-reads, priced by the refined read cost). -/
theorem epsTot_le_add (hq : q ≤ 2 ^ 64) (L : HonestTable) (hπ : PermGood L.perm 18) :
    epsTot A L ≤ (2 ^ 300 : ℝ≥0∞)⁻¹ * callTot A L +
      (runtimeR m0R).totalWeight .instruments (epsRestWt L) (gameR A L) initR :=
  totalWeight_epsW_le_add L hπ (gameR A L) (advCalls_gameR hperm hsign L)
    (clsCalls_gameR hperm hsign L) (progCap_add_le hq)

/-- **`readEps` on the challenge prefix** (no residual: the prefix calls only `ReadOk` reads), for
`q ≤ 2^64` at a table with `PermGood π 18`. -/
theorem epsW_prefixR_le (hq : q ≤ 2 ^ 64) (L : HonestTable) (hπ : PermGood L.perm 18) :
    (runtimeR m0R).totalWeight .instruments (epsWt L) (prefixR A L) initR ≤
      (2 ^ 300 : ℝ≥0∞)⁻¹ * (runtimeR m0R).totalWeight .instruments callWt (prefixR A L) initR :=
  totalWeight_epsW_le L hπ (prefixR A L) (advCalls_prefixR hperm hsign L)
    (clsCalls_prefixR hperm hsign L) (progCap_add_le hq) (chgB_prefixR A L)

end readEps

/-! ## The programs: the count and the remaining view bound -/

section progs

/-- **The trace-weighted program calls of a program**: with at most `K` program calls on every
path, the traces of the inputs of the program calls add up to at most `K`. -/
theorem totalWeight_progs_le {Ω : QReg → Type}
    (x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))
    {K : ℕ} (hK : IFreeM.IsChargeBound x (progChargeR HPos Selections) K) :
    (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (fun _ _ ↦ 0)
      fun _ σ ↦ ENNReal.ofReal σ.trace.re)) x initR ≤ K := by
  refine (totalWeight_le_totalWeight (runtimeR m0R) .instruments
    (w' := fun i σ ↦ (extProgCharge X Z Mem (recSpec HPos Selections) i : ℝ≥0∞) *
      ENNReal.ofReal σ.trace.re) (fun i σ _ ↦ ?_) x initR_posSemidef).trans ?_
  · rcases i with ((p | c) | c) | T <;> simp [extWeight, sumWeight, hwCost, extProgCharge,
      progCharge]
    exact le_of_eq rfl
  · refine (totalWeight_chargeTrace_le (runtimeR m0R) .instruments _ x hK
      initR_posSemidef).trans ?_
    calc (K : ℝ≥0∞) * ENNReal.ofReal initR.trace.re ≤ K * 1 := by
          gcongr
          exact ofReal_trace_initR_le_one
      _ = K := mul_one _

/-- **`progRest` from the view bound of the programs.** For event-bound programs `x L` with at
most `progCap` program calls, if the averaged program flip costs `f` are at most `2^-128` per unit
of the averaged trace-weighted program count (the remaining view bound: the programmed honest
value is hidden before its reveal), then they are at most `progTerm`. -/
theorem uavg_progs_le_of_view {Ω : QReg → Type}
    (x : HonestTable →
      QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))
    (hK : ∀ L, IFreeM.IsChargeBound (x L) (progChargeR HPos Selections) progCap)
    (f : HonestTable → ℝ≥0∞)
    (hview : uavg f ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ * uavg (fun L ↦ (runtimeR m0R).totalWeight
      .instruments (extWeight (hwCost (fun _ _ ↦ 0) fun _ σ ↦ ENNReal.ofReal σ.trace.re))
        (x L) initR)) :
    uavg f ≤ progTerm := by
  refine hview.trans ?_
  rw [progTerm, mul_comm]
  gcongr
  calc uavg (fun L ↦ (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (fun _ _ ↦ 0)
        fun _ σ ↦ ENNReal.ofReal σ.trace.re)) (x L) initR)
      ≤ uavg (fun _ : HonestTable ↦ (progCap : ℝ≥0∞)) :=
        uavg_mono fun L ↦ totalWeight_progs_le (x L) (hK L)
    _ = progCap := uavg_const _

/-- **Security's `progRest` from the view bound of the game's programs** (`progCalls_gameR`): the
remaining hypothesis `hview` is the per-program `2^-128` of `flipCost_programH_avg_le` (capacity
scale for `k`, `k'` cells, `0` for intermediate `h` cells), summed along the game and averaged
over the good tables. -/
theorem progRest_of_view {q : ℕ} {A : Adversary (X × Z)}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
    (hview : uavg (fun L ↦ if PermGood L.perm 18 then progTot A L else 0) ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * uavg (fun L ↦ (runtimeR m0R).totalWeight .instruments
        (extWeight (hwCost (fun _ _ ↦ 0) fun _ σ ↦ ENNReal.ofReal σ.trace.re)) (gameR A L)
          initR)) :
    uavg (fun L ↦ if PermGood L.perm 18 then progTot A L else 0) ≤ progTerm :=
  uavg_progs_le_of_view (gameR A) (progCalls_gameR hperm hsign) _ hview

end progs

end Quantum.Xmss.Assembly

end
