module

public import Quantum.StdModel.Fixed
public import Quantum.Qrom.Classical
public import Quantum.StdModel.Props.Basic

@[expose] public section

/-!
# Decisions, lazy sampling and classical prefixes at a fixed table

* **Lazy sampling behind a classical challenger.** A challenger that answers with the help of a
  random function `X → U`, sampled lazily (`Qrom.lazyFunOracles`, the cache in the state), and the
  same challenger with the function sampled up front (`Qrom.eagerFunOracles`) give the adversary
  the same run: `card_smul_branch_kRun_lazy` (the run from a cache `c` is the average over `H` of
  the runs against `H` overlaid with `c`). Classically: `tsum_lazy_mul_sum`, the weighted form of
  `Qrom.card_mul_prEvent_lazyFun`, and `tsum_lazy_smul_sum`, its form with vector values.
* **Decisions at a fixed table.** The probability of a final classical decision is the weight of
  the leaves it accepts (`probAt_map`), so a decision implied by one of finitely many others is
  at most the sum of their probabilities (`probAt_map_le_sum`, the union bound); a random
  classical prefix averages (`probAt_bind_classicalOn`).
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal

namespace Quantum.StdModel

open Common Qrom

/-! ## Lazy and eager sampling, classically -/

section LazyClassical

variable {X Y α : Type} [Fintype X] [DecidableEq X] [Fintype Y] [SampleableType Y]

omit [Fintype X] [DecidableEq X] [Fintype Y] [SampleableType Y] in
/-- Weighting by the law of a pure computation evaluates at its value. -/
theorem tsum_prEvent_pure_mul {β : Type} (b : β) (f : β → ℝ≥0∞) :
    ∑' p, Pr{let z ← (pure b : ProbComp β)}[z = p] * f p = f b := by
  classical
  rw [tsum_eq_single b fun p hp ↦ by simp [Ne.symm hp]]
  simp

omit [Fintype X] [DecidableEq X] [Fintype Y] [SampleableType Y] in
/-- Weighting by the law of a bind weights by the prefix, then by the continuation. -/
theorem tsum_prEvent_bind_mul {β γ : Type} (mx : ProbComp β) (k : β → ProbComp γ)
    (f : γ → ℝ≥0∞) :
    ∑' p, Pr{let z ← mx >>= k}[z = p] * f p =
      ∑' b, Pr{let z ← mx}[z = b] * ∑' p, Pr{let z ← k b}[z = p] * f p := by
  simp_rw [prEvent_bind_eq_tsum, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun b ↦ ?_
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun p ↦ (mul_assoc _ _ _)

/-- **Lazy sampling from a cache, weighted.** Run from the cache `c`, the lazily sampled random
function weights each output `a` and final cache `c'` by the sum over all `H` of `Φ a` at `H`
overlaid with `c'`; this is the sum over all `H` of the outputs' weights against `H` overlaid with
`c`. -/
theorem tsum_lazy_mul_sum (oa : OracleComp (unifSpec + (X →ₒ Y)) α)
    (c : (X →ₒ Y).QueryCache) (Φ : α → (X → Y) → ℝ≥0∞) :
    ∑' p, Pr{let z ← (simulateQ (lazyFunOracles X Y) oa).run c}[z = p] *
        ∑ H : X → Y, Φ p.1 (tableExtending p.2 H) =
      ∑ H : X → Y, ∑' a,
        Pr{let z ← simulateQ (eagerFunOracles (tableExtending c H)) oa}[z = a] *
          Φ a (tableExtending c H) := by
  classical
  induction oa using OracleComp.inductionOn generalizing c with
  | pure b =>
    simp only [simulateQ_pure, StateT.run_pure]
    rw [tsum_prEvent_pure_mul]
    exact Finset.sum_congr rfl fun H _ ↦
      (tsum_prEvent_pure_mul b fun a ↦ Φ a (tableExtending c H)).symm
  | query_bind t k ih =>
    have hlazy : (simulateQ (lazyFunOracles X Y)
        (liftM ((unifSpec + (X →ₒ Y)).query t) >>= k)).run c =
          (lazyFunOracles X Y t).run c >>= fun p ↦
            (simulateQ (lazyFunOracles X Y) (k p.1)).run p.2 := by
      simp [simulateQ_bind, StateT.run_bind]
    have heager (H : X → Y) :
        simulateQ (eagerFunOracles H) (liftM ((unifSpec + (X →ₒ Y)).query t) >>= k) =
          eagerFunOracles H t >>= fun u ↦ simulateQ (eagerFunOracles H) (k u) := by
      simp [simulateQ_bind]
    change ∑' p, Pr{let z ← ((simulateQ (lazyFunOracles X Y)
        (liftM ((unifSpec + (X →ₒ Y)).query t) >>= k)).run c)}[z = p] * _ =
      ∑ H, ∑' a, Pr{let z ← (simulateQ (eagerFunOracles (tableExtending c H))
        (liftM ((unifSpec + (X →ₒ Y)).query t) >>= k))}[z = a] * _
    simp only [hlazy, heager, tsum_prEvent_bind_mul, ih]
    rcases t with n | x
    · have hrun : (lazyFunOracles X Y (.inl n)).run c =
          ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun u ↦ pure (u, c)) := rfl
      have he (H : X → Y) : eagerFunOracles H (.inl n) =
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := rfl
      simp only [hrun, he, tsum_prEvent_bind_mul, tsum_prEvent_pure_mul]
      simp only [Finset.mul_sum]
      rw [Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
      rfl
    · cases hc : c x with
      | some y =>
        have hrun : (lazyFunOracles X Y (.inr x)).run c = pure (y, c) := by
          rw [lazyFunOracles, randomOracle.run_eq, hc]
        have he (H : X → Y) : eagerFunOracles (tableExtending c H) (.inr x) = pure y := by
          simp [eagerFunOracles, tableExtending, hc]
        simp only [hrun, he, tsum_prEvent_pure_mul]
      | none =>
        have hrun : (lazyFunOracles X Y (.inr x)).run c =
            ($ᵗ Y) >>= fun u ↦ pure (u, c.cacheQuery x u) := by
          rw [lazyFunOracles, randomOracle.run_eq, hc]
        have he (H : X → Y) : eagerFunOracles (tableExtending c H) (.inr x) = pure (H x) := by
          simp [eagerFunOracles, tableExtending, hc]
        simp only [hrun, he, tsum_prEvent_bind_mul, tsum_prEvent_pure_mul]
        have hY : (Fintype.card Y : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
        let g : (X → Y) → Y → ℝ≥0∞ := fun H u ↦ ∑' a,
          Pr{let z ← simulateQ (eagerFunOracles (tableExtending c H)) (k u)}[z = a] *
            Φ a (tableExtending c H)
        calc
          _ = ∑ u : Y, (Fintype.card Y : ℝ≥0∞)⁻¹ * ∑ H : X → Y, g (Function.update H x u) u := by
            rw [tsum_fintype]
            refine Finset.sum_congr rfl fun u _ ↦ ?_
            rw [SampleableType.prEvent_uniformSample_eq_singleton]
            refine congrArg _ (Finset.sum_congr rfl fun H _ ↦ ?_)
            simp only [g, tableExtending_cacheQuery, tableExtending_update_of_none c H hc]
          _ = ∑ H : X → Y, g H (H x) := by
            rw [← Finset.mul_sum, Qrom.sum_sum_update_eq_card_smul x g, nsmul_eq_mul,
              ← mul_assoc, ENNReal.inv_mul_cancel hY (ENNReal.natCast_ne_top _), one_mul]

open Classical in
/-- **Lazy sampling, pointwise**: the weight of the output `a` with a final cache overlaying to
`G`, against the number of tables overlaying `c` to `G` times the output's weight against `G`. -/
theorem tsum_lazy_ite (oa : OracleComp (unifSpec + (X →ₒ Y)) α) (c : (X →ₒ Y).QueryCache)
    (a : α) (G : X → Y) :
    ∑' p, Pr{let z ← (simulateQ (lazyFunOracles X Y) oa).run c}[z = p] *
        ∑ H : X → Y, (if p.1 = a ∧ tableExtending p.2 H = G then 1 else 0) =
      ∑ H : X → Y, if tableExtending c H = G then
        Pr{let z ← simulateQ (eagerFunOracles G) oa}[z = a] else 0 := by
  classical
  rw [tsum_lazy_mul_sum oa c fun a' G' ↦ if a' = a ∧ G' = G then 1 else 0]
  refine Finset.sum_congr rfl fun H _ ↦ ?_
  by_cases hG : tableExtending c H = G
  · subst hG
    rw [tsum_eq_single a fun b hb ↦ by simp [hb]]
    simp
  · simp [hG]

/-- A probability as a complex number. -/
noncomputable def ofE (x : ℝ≥0∞) : ℂ :=
  (x.toReal : ℂ)

omit [Fintype X] [DecidableEq X] [Fintype Y] [SampleableType Y] in
theorem ofE_mul (x y : ℝ≥0∞) : ofE (x * y) = ofE x * ofE y := by
  simp [ofE, ENNReal.toReal_mul]

omit [Fintype X] [DecidableEq X] [Fintype Y] [SampleableType Y] in
theorem ofE_sum {ι : Type} (s : Finset ι) (f : ι → ℝ≥0∞) (hf : ∀ i ∈ s, f i ≠ ∞) :
    ofE (∑ i ∈ s, f i) = ∑ i ∈ s, ofE (f i) := by
  simp [ofE, ENNReal.toReal_sum hf]

omit [Fintype X] [DecidableEq X] [Fintype Y] [SampleableType Y] in
theorem ofE_ite (p : Prop) [Decidable p] : ofE (if p then 1 else 0) = if p then 1 else 0 := by
  split_ifs <;> simp [ofE]

omit [SampleableType Y] in
/-- Summing over tables through a map is summing over the values with their fiber counts. -/
theorem sum_comp_fiber {M : Type*} [AddCommGroup M] [Module ℂ M] (g : (X → Y) → (X → Y))
    (f : (X → Y) → M) [DecidableEq (X → Y)] :
    ∑ H, f (g H) = ∑ G, (∑ H, if g H = G then (1 : ℂ) else 0) • f G := by
  simp only [Finset.sum_smul, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun H _ ↦ by simp

/-- **Lazy sampling from a cache, with vector values**: the form of `tsum_lazy_mul_sum` with
complex weights and values in a module, as a run's branches need it. -/
theorem tsum_lazy_smul_sum {M : Type*} [AddCommGroup M] [Module ℂ M] [TopologicalSpace M]
    (oa : OracleComp (unifSpec + (X →ₒ Y)) α) (c : (X →ₒ Y).QueryCache)
    (T : (X → Y) → α → M) :
    ∑' p, ofE (Pr{let z ← (simulateQ (lazyFunOracles X Y) oa).run c}[z = p]) •
        ∑ H : X → Y, T (tableExtending p.2 H) p.1 =
      ∑ H : X → Y, ∑' a,
        ofE (Pr{let z ← simulateQ (eagerFunOracles (tableExtending c H)) oa}[z = a]) •
          T (tableExtending c H) a := by
  classical
  set L := (simulateQ (lazyFunOracles X Y) oa).run c with hLdef
  let E : (X → Y) → ProbComp α := fun G ↦ simulateQ (eagerFunOracles G) oa
  have hL : (support L).Finite := support_finite L
  have hE (G : X → Y) : (support (E G)).Finite := support_finite (E G)
  let FL : Finset (α × (X →ₒ Y).QueryCache) := hL.toFinset
  let Z : Finset α := FL.image Prod.fst ∪ Finset.univ.biUnion fun G ↦ (hE G).toFinset
  have hzL (p : α × (X →ₒ Y).QueryCache) (hp : p ∉ FL) : Pr{let z ← L}[z = p] = 0 :=
    prEvent_eq_zero_of_not_mem_support L (by simpa [FL] using hp)
  have hzE (G : X → Y) (a : α) (ha : a ∉ Z) : Pr{let z ← E G}[z = a] = 0 := by
    refine prEvent_eq_zero_of_not_mem_support (E G) fun h ↦ ha ?_
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨G, Finset.mem_univ _, by simpa⟩)
  have hN (x : (X →ₒ Y).QueryCache) (G : X → Y) :
      ofE (∑ H : X → Y, if tableExtending x H = G then 1 else 0) =
        ∑ H : X → Y, if tableExtending x H = G then (1 : ℂ) else 0 := by
    rw [ofE_sum _ _ fun H _ ↦ by split_ifs <;> simp]
    exact Finset.sum_congr rfl fun H _ ↦ ofE_ite _
  rw [tsum_eq_sum (s := FL) fun p hp ↦ by rw [hzL p hp, ofE, ENNReal.toReal_zero,
    Complex.ofReal_zero, zero_smul]]
  have hR (H : X → Y) : ∑' a, ofE (Pr{let z ← E (tableExtending c H)}[z = a]) •
      T (tableExtending c H) a =
        ∑ a ∈ Z, ofE (Pr{let z ← E (tableExtending c H)}[z = a]) • T (tableExtending c H) a :=
    tsum_eq_sum fun a ha ↦ by rw [hzE _ a ha, ofE, ENNReal.toReal_zero, Complex.ofReal_zero,
      zero_smul]
  change _ = ∑ H : X → Y, ∑' a, ofE (Pr{let z ← E (tableExtending c H)}[z = a]) •
    T (tableExtending c H) a
  simp only [hR]
  rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := Z)
    fun p hp ↦ Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp), Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  have hl : ∑ p ∈ FL with p.1 = a, ofE (Pr{let z ← L}[z = p]) •
      ∑ H : X → Y, T (tableExtending p.2 H) p.1 =
        ∑ G, (∑ p ∈ FL with p.1 = a, ofE (Pr{let z ← L}[z = p]) *
          ∑ H : X → Y, if tableExtending p.2 H = G then (1 : ℂ) else 0) • T G a := by
    simp only [Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [(Finset.mem_filter.mp hp).2, sum_comp_fiber (fun H ↦ tableExtending p.2 H)
      (fun G ↦ T G a), Finset.smul_sum]
    exact Finset.sum_congr rfl fun G _ ↦ by rw [smul_smul]
  have hr : ∑ H : X → Y, ofE (Pr{let z ← E (tableExtending c H)}[z = a]) •
      T (tableExtending c H) a =
        ∑ G, ((∑ H : X → Y, if tableExtending c H = G then (1 : ℂ) else 0) *
          ofE (Pr{let z ← E G}[z = a])) • T G a := by
    rw [sum_comp_fiber (fun H ↦ tableExtending c H)
      (fun G ↦ ofE (Pr{let z ← E G}[z = a]) • T G a)]
    exact Finset.sum_congr rfl fun G _ ↦ by rw [smul_smul]
  rw [hl, hr]
  refine Finset.sum_congr rfl fun G _ ↦ congrArg (· • T G a) ?_
  have hs' : ∑ p ∈ FL with p.1 = a, Pr{let z ← L}[z = p] *
      ∑ H : X → Y, (if tableExtending p.2 H = G then (1 : ℝ≥0∞) else 0) =
        (∑ H : X → Y, if tableExtending c H = G then (1 : ℝ≥0∞) else 0) *
          Pr{let z ← E G}[z = a] := by
    calc
      _ = ∑ p ∈ FL, Pr{let z ← L}[z = p] *
          ∑ H : X → Y, (if p.1 = a ∧ tableExtending p.2 H = G then (1 : ℝ≥0∞) else 0) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        by_cases hpa : p.1 = a <;> simp [hpa]
      _ = ∑' p, Pr{let z ← L}[z = p] *
          ∑ H : X → Y, (if p.1 = a ∧ tableExtending p.2 H = G then (1 : ℝ≥0∞) else 0) :=
        (tsum_eq_sum fun p hp ↦ by rw [hzL p hp, zero_mul]).symm
      _ = _ := tsum_lazy_ite oa c a G
      _ = _ := by
        rw [Finset.sum_mul]
        simp only [ite_mul, one_mul, zero_mul]
        exact Finset.sum_congr rfl fun H _ ↦ by congr
  have hfin (p : α × (X →ₒ Y).QueryCache) : Pr{let z ← L}[z = p] *
      ∑ H : X → Y, (if tableExtending p.2 H = G then (1 : ℝ≥0∞) else 0) ≠ ∞ :=
    ENNReal.mul_ne_top (prEvent_ne_top _) (ENNReal.sum_ne_top.mpr fun H _ ↦ by
      split_ifs <;> simp)
  have h := congrArg ofE hs'
  rw [ofE_sum _ _ fun p _ ↦ hfin p, ofE_mul, hN] at h
  simp only [ofE_mul, hN] at h
  exact h

end LazyClassical

/-! ## Lazy and eager sampling behind a classical challenger -/

section LazyQuantum

/-- **Mixing continuations commutes with a first stage**: if `a` times each continuation's
branch is the sum of the mixed continuations' branches, the same holds after the first stage. -/
theorem branch_bind_smul_sum {A : Type*} [Fintype A] {ι κ : Type*} {B : ι → Type*}
    [∀ i, Fintype (B i)] {C : κ → Type*} [∀ c, Fintype (C c)] {Θ : Type*} [Fintype Θ]
    (p : DSubInstrument A ι B) (kL : (i : ι) → DSubInstrument (B i) κ C)
    (kE : Θ → (i : ι) → DSubInstrument (B i) κ C) (a : ℂ) (y : κ)
    (h : ∀ i σ, a • (kL i).branch y σ = ∑ θ, (kE θ i).branch y σ) (ρ : Matrix A A ℂ) :
    a • (p.bind kL).branch y ρ = ∑ θ, (p.bind (kE θ)).branch y ρ := by
  simp only [DSubInstrument.branch_bind_apply]
  rw [← tsum_const_smul'']
  simp only [h]
  exact Summable.tsum_finsetSum fun θ _ ↦
    (p.isCPTNIFamily.comp_eval (fun i ↦ (kE θ i).isCPTNIFamily) y).summable_apply ρ

variable {spec : QuantumOracleSpec.{0, 0}} (Rt : QuantumRuntime spec)

/-- Mixing continuations commutes with a command. -/
theorem branch_liftBind_smul_sum {A : QReg} {Xf : QReg → Type} {Θ : Type} [Fintype Θ]
    (c : QuantumComp.Cmd LocalSig.instruments.{0} spec A)
    (f : (b : c.Resp) →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec) Xf (c.next b))
    (g : Θ → (b : c.Resp) →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec) Xf (c.next b))
    (a : ℂ) (y : Σ u, Xf u) (h : ∀ b σ, a • (Rt.run .instruments (f b)).branch y σ =
      ∑ θ, (Rt.run .instruments (g θ b)).branch y σ)
    (ρ : Matrix (A × Rt.D) (A × Rt.D) ℂ) :
    a • (Rt.run .instruments (IFreeM.liftBind (P := QuantumComp.toIPFunctor _ spec) c f)).branch
        y ρ =
      ∑ θ, (Rt.run .instruments
        (IFreeM.liftBind (P := QuantumComp.toIPFunctor _ spec) c (g θ))).branch y ρ := by
  rcases c with o | ⟨i, E, ℓ⟩
  · have e₁ := QuantumRuntime.run_primBind Rt LocalSig.Interp.instruments o
      fun b ↦ f (ULift.up b)
    have e₂ (θ : Θ) := QuantumRuntime.run_primBind Rt LocalSig.Interp.instruments o
      fun b ↦ g θ (ULift.up b)
    change a • (Rt.run .instruments (QuantumComp.primBind o fun b ↦ f (ULift.up b))).branch y ρ =
      ∑ θ, (Rt.run .instruments (QuantumComp.primBind o fun b ↦ g θ (ULift.up b))).branch y ρ
    simp only [e₁, e₂]
    exact branch_bind_smul_sum _ _ _ a y (fun b σ ↦ h (ULift.up b) σ) ρ
  · have e₁ := QuantumRuntime.run_queryBind Rt LocalSig.Interp.instruments i E ℓ
      fun b ↦ f (ULift.up b)
    have e₂ (θ : Θ) := QuantumRuntime.run_queryBind Rt LocalSig.Interp.instruments i E ℓ
      fun b ↦ g θ (ULift.up b)
    change a • (Rt.run .instruments (QuantumComp.queryBind i E ℓ fun b ↦ f (ULift.up b))).branch
        y ρ =
      ∑ θ, (Rt.run .instruments (QuantumComp.queryBind i E ℓ fun b ↦ g θ (ULift.up b))).branch
        y ρ
    simp only [e₁, e₂]
    exact branch_bind_smul_sum _ _ _ a y (fun b σ ↦ h (ULift.up b) σ) ρ

variable (W : OracleWorld) {Q : Type} {R : OracleSpec.{0, 0} Q} {St : Type}

/-- **A classical call in the canonical run**: the kernel's law weights the continuation after
the framed relabelling. -/
theorem branch_run_kRun_call (Rt : QuantumRuntime W.spec) {X Y : QReg → Type}
    (K : Kernel R St) (leaf : ∀ u, X u → St → Y u) (q : Q) (E : QReg) {A : QReg}
    (ℓ : A ≃ (advSpec W.spec R).In (.call q) × E)
    (next : (b : ULift (R.Range q)) →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec W.spec R)) X
        (QReg.of ((advSpec W.spec R).Out (.call q) × E))) (s : St) (y : Σ u, Y u)
    (ρ : Matrix (A × Rt.D) (A × Rt.D) ℂ) :
    (Rt.run .instruments (kRun W K leaf (IFreeM.liftBind
        (P := QuantumComp.toIPFunctor _ (advSpec W.spec R)) (.query (.call q) E ℓ) next) s)).branch
        y ρ =
      ∑' a : R.Range q × St, ofE (Pr{let z ← K s q}[z = a]) •
        (Rt.run .instruments (kRun W K leaf (next ⟨a.1⟩) a.2)).branch y
          (relabelMap Rt (B' := QReg.of ((advSpec W.spec R).Out (.call q) × E)) ℓ ρ) := by
  rw [kRun_call]
  refine (congrArg (fun d ↦ DSubInstrument.branch d y ρ) (QuantumRuntime.run_bind Rt
    LocalSig.Interp.instruments (kTree W K s q E ℓ) fun _ l ↦
      l.1 ▸ kRun W K leaf (next ⟨l.2.1⟩) l.2.2)).trans ?_
  rw [DSubInstrument.branch_bind_apply, ← (QuantumComp₂.leafEquiv _ _).tsum_eq]
  refine tsum_congr fun a ↦ ?_
  have h := classicalOn_kTree W Rt K s q E ℓ a
  change (Rt.run .instruments _).branch y
    ((Rt.run₂ .instruments (kTree W K s q E ℓ)).branch a ρ) = _
  rw [h, LinearMap.smul_apply, map_smul]
  rfl

variable {D U : Type} [Fintype D] [DecidableEq D] [Fintype U] [SampleableType U]

/-- **The lazily sampled kernel**: the classical answer `k s q` over coins and a random function,
the function sampled lazily from the cache kept beside the state. -/
noncomputable def lazyKernel
    (k : St → (q : Q) → OracleComp (unifSpec + (D →ₒ U)) (R.Range q × St)) :
    Kernel R (St × (D →ₒ U).QueryCache) := fun sc q ↦
  (fun p ↦ (p.1.1, (p.1.2, p.2))) <$> (simulateQ (lazyFunOracles D U) (k sc.1 q)).run sc.2

/-- **The eagerly sampled kernel**: the same answers against the fixed function `H`. -/
noncomputable def eagerKernel
    (k : St → (q : Q) → OracleComp (unifSpec + (D →ₒ U)) (R.Range q × St)) (H : D → U) :
    Kernel R St := fun s q ↦
  simulateQ (eagerFunOracles H) (k s q)

/-- **Lazy sampling behind a classical challenger.** Against any runtime, the canonical run with
the lazily sampled kernel from the cache `c`, times the number of functions, is the sum over all
`H` of the runs with the eagerly sampled kernel at `H` overlaid with `c`, when the final leaves
agree (the lazy leaf reads only the cache). -/
theorem card_smul_branch_kRun_lazy (Rt : QuantumRuntime W.spec) {X Y : QReg → Type}
    (k : St → (q : Q) → OracleComp (unifSpec + (D →ₒ U)) (R.Range q × St))
    (leafL : ∀ u, X u → St × (D →ₒ U).QueryCache → Y u)
    (leafE : (D → U) → ∀ u, X u → St → Y u)
    (hleaf : ∀ c H u l s, leafL u l (s, c) = leafE (tableExtending c H) u l s) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec W.spec R)) X A)
    (s : St) (c : (D →ₒ U).QueryCache) (y : Σ u, Y u) (ρ : Matrix (A × Rt.D) (A × Rt.D) ℂ) :
    (Fintype.card (D → U) : ℂ) •
        (Rt.run .instruments (kRun W (lazyKernel k) leafL x (s, c))).branch y ρ =
      ∑ H : D → U, (Rt.run .instruments (kRun W (eagerKernel k (tableExtending c H))
        (leafE (tableExtending c H)) x s)).branch y ρ := by
  induction x using IFreeM.inductionOn generalizing s c with
  | pure A l =>
    change _ • (Rt.run .instruments (QuantumComp.pure (L := LocalSig.instruments.{0})
        (leafL A l (s, c)))).branch y ρ =
      ∑ H : D → U, (Rt.run .instruments (QuantumComp.pure (L := LocalSig.instruments.{0})
        (leafE (tableExtending c H) A l s))).branch y ρ
    have hH (H : D → U) : (Rt.run .instruments (QuantumComp.pure (L := LocalSig.instruments.{0})
        (leafE (tableExtending c H) A l s))).branch y ρ =
        (Rt.run .instruments (QuantumComp.pure (L := LocalSig.instruments.{0})
          (leafL A l (s, c)))).branch y ρ := by
      rw [hleaf c H]
    rw [Finset.sum_congr rfl fun H _ ↦ hH H, Finset.sum_const, Finset.card_univ,
      Nat.cast_smul_eq_nsmul]
  | liftBind A cmd next ih =>
    rcases cmd with o | ⟨p | q, E, ℓ⟩
    · exact branch_liftBind_smul_sum Rt (.prim o) _ _ _ y (fun b σ ↦ ih b s c σ) ρ
    · exact branch_liftBind_smul_sum Rt (.query p E ℓ) _ _ _ y (fun b σ ↦ ih b s c σ) ρ
    · refine (congrArg ((Fintype.card (D → U) : ℂ) • ·)
        (branch_run_kRun_call W Rt (lazyKernel k) leafL q E ℓ next (s, c) y ρ)).trans ?_
      refine Eq.trans ?_ (Finset.sum_congr rfl fun H _ ↦ (branch_run_kRun_call W Rt
        (eagerKernel k (tableExtending c H)) (leafE (tableExtending c H)) q E ℓ next s y ρ).symm)
      rw [← tsum_const_smul'']
      have hstep (a : R.Range q × St × (D →ₒ U).QueryCache) :
          (Fintype.card (D → U) : ℂ) • (ofE (Pr{let z ← lazyKernel k (s, c) q}[z = a]) •
            (Rt.run .instruments (kRun W (lazyKernel k) leafL (next ⟨a.1⟩) a.2)).branch y
              (relabelMap Rt (B' := QReg.of ((advSpec W.spec R).Out (.call q) × E)) ℓ ρ)) =
          ofE (Pr{let z ← lazyKernel k (s, c) q}[z = a]) • ∑ H : D → U,
            (Rt.run .instruments (kRun W (eagerKernel k (tableExtending a.2.2 H))
              (leafE (tableExtending a.2.2 H)) (next ⟨a.1⟩) a.2.1)).branch y
              (relabelMap Rt (B' := QReg.of ((advSpec W.spec R).Out (.call q) × E)) ℓ ρ) := by
        obtain ⟨r, s', c'⟩ := a
        dsimp only
        rw [smul_comm]
        exact congrArg _ (ih ⟨r⟩ s' c' _)
      refine (tsum_congr hstep).trans ?_
      let e : (R.Range q × St) × (D →ₒ U).QueryCache ≃ R.Range q × St × (D →ₒ U).QueryCache :=
        Equiv.prodAssoc _ _ _
      have hpr (p : (R.Range q × St) × (D →ₒ U).QueryCache) :
          Pr{let z ← lazyKernel k (s, c) q}[z = e p] =
            Pr{let z ← (simulateQ (lazyFunOracles D U) (k s q)).run c}[z = p] :=
        prEvent_map_injective _ e.injective p
      rw [← e.tsum_eq]
      simp only [hpr]
      exact tsum_lazy_smul_sum (k s q) c fun G z ↦
        (Rt.run .instruments (kRun W (eagerKernel k G) (leafE G) (next ⟨z.1⟩) z.2)).branch y
          (relabelMap Rt (B' := QReg.of ((advSpec W.spec R).Out (.call q) × E)) ℓ ρ)

end LazyQuantum

/-! ## Deterministic prefixes -/

section Prefix

variable {spec : QuantumOracleSpec.{0, 0}} (Rt : QuantumRuntime spec)

/-- **A deterministic classical prefix**: a program that runs as the sampler returning `a`,
followed by `k`, runs as `k a`. -/
theorem run₂_bind_of_classicalOn_pure {B C : QReg} {α β : Type} {x : QComp spec B B α}
    {a : α} (hx : ClassicalOn Rt x (pure a) LinearMap.id) (k : α → QComp spec B C β) :
    Rt.run₂ .instruments (x.bind k) = Rt.run₂ .instruments (k a) := by
  classical
  rw [QuantumRuntime.run₂_bind]
  refine DSubInstrument.ext (funext fun c ↦ LinearMap.ext fun ρ ↦ ?_)
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply,
    tsum_eq_single a fun b hb ↦ by rw [hx b]; simp [Ne.symm hb]]
  rw [hx a]
  simp

end Prefix

/-! ## Decisions at a fixed table -/

section Decisions

variable (W : OracleWorld) (tab : W.Tab)

/-- The probability at a table depends only on the fixed-register run. -/
theorem probAt_eq_of_run₂ {x y : QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool}
    (h : (W.runtime tab).run₂ .instruments x = (W.runtime tab).run₂ .instruments y) :
    W.probAt tab x = W.probAt tab y :=
  probAt_congr (run_eq_of_run₂_eq h)

/-- **The probability as a trace**: the trace of the run's branch at `true` from the start. -/
theorem probAt_eq_ofReal_trace (x : QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool) :
    W.probAt tab x = ENNReal.ofReal (((W.runtime tab).run₂ .instruments x).branch true
      ((SubState.basis ()).prod (W.runtime tab).init).matrix).trace.re := by
  change (W.runtime tab).evalDistMap .instruments x (SubState.basis ())
    (QuantumComp₂.leafEquiv (QReg.of Unit) Bool).symm {true} = _
  rw [← QuantumRuntime.evalDist₂_eq_evalDistMap, QuantumRuntime.evalDist₂,
    DSubInstrument.outcomeMeasure_apply_singleton]

/-- **A final decision**: the probability that `d` holds of the value. -/
theorem probAt_map {γ : Type} (x : QComp W.spec (QReg.of Unit) (QReg.of Unit) γ)
    (d : γ → Bool) :
    W.probAt tab (x.map d) = (W.runtime tab).evalDistMap .instruments x (SubState.basis ())
      (fun p ↦ d p.2.2) {true} := by
  change (W.runtime tab).evalDistMap .instruments (x.map d) (SubState.basis ())
    (QuantumComp₂.leafEquiv (QReg.of Unit) Bool).symm {true} = _
  rw [← QuantumRuntime.evalDist₂_eq_evalDistMap, QuantumRuntime.evalDist₂_map_eq_evalDistMap]
  rfl

/-- **The union bound on a final decision**: if `d` implies one of the decisions `ds i`,
`i ∈ s`, its probability is at most the sum of theirs. -/
theorem probAt_map_le_sum {γ ι : Type} (x : QComp W.spec (QReg.of Unit) (QReg.of Unit) γ)
    (d : γ → Bool) (s : Finset ι) (ds : ι → γ → Bool)
    (h : ∀ g, d g = true → ∃ i ∈ s, ds i g = true) :
    W.probAt tab (x.map d) ≤ ∑ i ∈ s, W.probAt tab (x.map (ds i)) := by
  classical
  have e (f : γ → Bool) := QuantumRuntime.evalDistMap_apply (W.runtime tab)
    LocalSig.Interp.instruments x (SubState.basis ()) (fun p ↦ f p.2.2)
    (measurableSet_singleton true)
  simp only [probAt_map]
  rw [e d, Finset.sum_congr rfl fun i _ ↦ e (ds i),
    ← Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
  refine ENNReal.tsum_le_tsum fun p ↦ ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul' le_rfl ?_
  by_cases hd : d p.2.2 = true
  · obtain ⟨i, hi, hdi⟩ := h _ hd
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun i ↦
      ({true} : Set Bool).indicator (1 : Bool → ℝ≥0∞) (ds i p.2.2)) (fun _ _ ↦ zero_le) hi)
    simp [hd, hdi]
  · simp [hd]

/-- **A random classical prefix**: a program that runs as the sampler `pa`, followed by `k`,
wins with the average over `pa` of the winning probabilities of `k`. -/
theorem probAt_bind_classicalOn {α : Type}
    {x : QComp W.spec (QReg.of Unit) (QReg.of Unit) α} {pa : ProbComp α}
    (hx : ClassicalOn (W.runtime tab) x pa LinearMap.id)
    (k : α → QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool) :
    W.probAt tab (x.bind k) = ∑' a, Pr{let z ← pa}[z = a] * W.probAt tab (k a) := by
  set Rt := W.runtime tab
  set ρ := (SubState.basis ()).prod Rt.init
  have hfam : Summable fun a ↦ (Rt.run₂ .instruments (k a)).branch true
      ((Rt.run₂ .instruments x).branch a ρ.matrix) :=
    ((Rt.run₂ .instruments x).isCPTNIFamily.comp_eval
      (fun a ↦ (Rt.run₂ .instruments (k a)).isCPTNIFamily) true).summable_apply ρ.matrix
  have hbr : (Rt.run₂ .instruments (x.bind k)).branch true ρ.matrix =
      ∑' a, (Rt.run₂ .instruments (k a)).branch true
        ((Rt.run₂ .instruments x).branch a ρ.matrix) := by
    rw [QuantumRuntime.run₂_bind]
    exact DSubInstrument.branch_bind_apply _ _ _ _
  have hpt (a : α) : (Rt.run₂ .instruments (k a)).branch true
      ((Rt.run₂ .instruments x).branch a ρ.matrix) =
        ((Pr{let z ← pa}[z = a]).toReal : ℂ) •
          (Rt.run₂ .instruments (k a)).branch true ρ.matrix := by
    rw [hx a, LinearMap.smul_apply, LinearMap.id_apply, map_smul]
  have hnn (a : α) : 0 ≤ ((Rt.run₂ .instruments (k a)).branch true ρ.matrix).trace.re :=
    DSubInstrument.trace_re_branch_apply_nonneg _ _ ρ.posSemidef
  rw [probAt_eq_ofReal_trace, hbr, Matrix.trace_tsum hfam, Complex.re_tsum
    (Matrix.summable_trace hfam)]
  simp only [hpt, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have hsum : Summable fun a ↦ (Pr{let z ← pa}[z = a]).toReal *
      ((Rt.run₂ .instruments (k a)).branch true ρ.matrix).trace.re := by
    have h := Complex.reCLM.summable (Matrix.summable_trace hfam)
    simp only [Complex.reCLM_apply, hpt, Matrix.trace_smul, smul_eq_mul,
      Complex.re_ofReal_mul] at h
    exact h
  rw [ENNReal.ofReal_tsum_of_nonneg (fun a ↦ mul_nonneg ENNReal.toReal_nonneg (hnn a)) hsum]
  refine tsum_congr fun a ↦ ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (prEvent_ne_top _),
    probAt_eq_ofReal_trace]

end Decisions

/-! ## Fair coins -/

section Coins

/-- **The world's coins are fair at every table**: a coin query is answered by a uniform coin.
Every world of `Quantum.StdModel.World` has fair coins. -/
def OracleWorld.CoinsFair (W : OracleWorld) : Prop :=
  ∀ tab n, W.eager tab (.inl n) = (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))

/-- Under fair coins, a classical sampler lifted to the world's oracles runs as itself. -/
theorem OracleWorld.simulateQ_liftComp {W : OracleWorld} (hW : W.CoinsFair) (tab : W.Tab)
    {α : Type} (oa : ProbComp α) : simulateQ (W.eager tab) (liftComp oa W.Oracles) = oa :=
  (QueryImpl.simulateQ_liftComp_left_eq_of_apply (W.eager tab) (QueryImpl.id' unifSpec)
    (fun n ↦ hW tab n) oa).trans (simulateQ_id' oa)

/-- Under fair coins, the challenger's uniform sample is uniform. -/
theorem OracleWorld.simulateQ_sample {W : OracleWorld} (hW : W.CoinsFair) (tab : W.Tab)
    (α : Type) [SampleableType α] :
    simulateQ (W.eager tab) (Props.sample W α) = $ᵗ α :=
  W.simulateQ_liftComp hW tab _

theorem keccakWorld_coinsFair : keccakWorld.CoinsFair := fun _ _ ↦ rfl

theorem romWorld_coinsFair : romWorld.CoinsFair := fun _ _ ↦ rfl

end Coins

end Quantum.StdModel

end
