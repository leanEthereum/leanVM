module

public import VCVio.ProgramLogic.Relational.Basic
public import VCVio.OracleComp.EvalDist.Sum
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import ToMathlib.MeasureTheory.Measure.Coupling.Maximal

@[expose] public section

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

section GeneralFiberCoupling

variable {α β γ : Type} [DecidableEq γ]

noncomputable def generalFiberMass
    (p : PMF α) (f : α → γ) (value : γ) : ENNReal :=
  ∑' candidate, if f candidate = value then p candidate else 0

theorem generalFiberMass_eq_map_apply
    (p : PMF α) (f : α → γ) (value : γ) :
    generalFiberMass p f value = p.map f value := by
  rw [generalFiberMass, PMF.map_apply]
  apply tsum_congr
  intro candidate
  by_cases heq : f candidate = value
  · simp [heq]
  · simp [heq, Ne.symm heq]

noncomputable def generalFiberCouplingWeight
    (p : PMF α) (q : PMF β)
    (f : α → γ) (g : β → γ) (pair : α × β) : ENNReal :=
  if f pair.1 = g pair.2 then
    p pair.1 * q pair.2 * (generalFiberMass p f (f pair.1))⁻¹
  else
    0

theorem generalFiberMass_ne_zero_of_apply_ne_zero
    (p : PMF α) (f : α → γ) (value : α) (hvalue : p value ≠ 0) :
    generalFiberMass p f (f value) ≠ 0 := by
  unfold generalFiberMass
  intro hzero
  rw [ENNReal.tsum_eq_zero] at hzero
  exact hvalue (by simpa using hzero value)

theorem generalFiberMass_ne_top
    (p : PMF α) (f : α → γ) (value : γ) :
    generalFiberMass p f value ≠ ∞ := by
  apply ne_top_of_le_ne_top one_ne_top
  rw [generalFiberMass_eq_map_apply]
  exact PMF.coe_le_one (p.map f) value

set_option maxHeartbeats 1600000 in
theorem generalFiberCouplingWeight_sum_right
    (p : PMF α) (q : PMF β) (f : α → γ) (g : β → γ)
    (hmap : p.map f = q.map g) (left : α) :
    ∑' right, generalFiberCouplingWeight p q f g (left, right) =
      p left := by
  simp only [generalFiberCouplingWeight]
  calc
    (∑' right,
        if f left = g right then
          p left * q right * (generalFiberMass p f (f left))⁻¹
        else 0) =
      p left * ((∑' right,
          if g right = f left then q right else 0) *
        (generalFiberMass p f (f left))⁻¹) := by
          calc
            (∑' right,
                if f left = g right then
                  p left * q right * (generalFiberMass p f (f left))⁻¹
                else 0) =
              ∑' right, p left *
                ((if g right = f left then q right else 0) *
                  (generalFiberMass p f (f left))⁻¹) := by
                    apply tsum_congr
                    intro right
                    by_cases heq : f left = g right
                    · rw [ite_eq_left heq, ite_eq_left heq.symm]
                      ac_rfl
                    · rw [ite_eq_right heq, ite_eq_right (Ne.symm heq)]
                      simp
            _ = p left * ∑' right,
                (if g right = f left then q right else 0) *
                  (generalFiberMass p f (f left))⁻¹ :=
              ENNReal.tsum_mul_left
            _ = p left * ((∑' right,
                if g right = f left then q right else 0) *
                  (generalFiberMass p f (f left))⁻¹) := by
              rw [ENNReal.tsum_mul_right]
    _ = p left * (generalFiberMass p f (f left) *
        (generalFiberMass p f (f left))⁻¹) := by
      congr 2
      calc
        (∑' right, if g right = f left then q right else 0) =
            generalFiberMass q g (f left) := rfl
        _ = q.map g (f left) := generalFiberMass_eq_map_apply q g (f left)
        _ = p.map f (f left) := by rw [hmap]
        _ = generalFiberMass p f (f left) :=
          (generalFiberMass_eq_map_apply p f (f left)).symm
    _ = p left := by
      by_cases hleft : p left = 0
      · simp [hleft]
      · rw [ENNReal.mul_inv_cancel
          (generalFiberMass_ne_zero_of_apply_ne_zero p f left hleft)
          (generalFiberMass_ne_top p f (f left)), mul_one]

set_option maxHeartbeats 1600000 in
theorem generalFiberCouplingWeight_sum_left
    (p : PMF α) (q : PMF β) (f : α → γ) (g : β → γ)
    (hmap : p.map f = q.map g) (right : β) :
    ∑' left, generalFiberCouplingWeight p q f g (left, right) =
      q right := by
  simp only [generalFiberCouplingWeight]
  calc
    (∑' left,
        if f left = g right then
          p left * q right * (generalFiberMass p f (f left))⁻¹
        else 0) =
      q right * ((∑' left,
          if f left = g right then p left else 0) *
        (generalFiberMass p f (g right))⁻¹) := by
          calc
            (∑' left,
                if f left = g right then
                  p left * q right * (generalFiberMass p f (f left))⁻¹
                else 0) =
              ∑' left, q right *
                ((if f left = g right then p left else 0) *
                  (generalFiberMass p f (g right))⁻¹) := by
                    apply tsum_congr
                    intro left
                    by_cases heq : f left = g right
                    · rw [ite_eq_left heq, ite_eq_left heq, heq]
                      ac_rfl
                    · simp [heq]
            _ = q right * ∑' left,
                (if f left = g right then p left else 0) *
                  (generalFiberMass p f (g right))⁻¹ :=
              ENNReal.tsum_mul_left
            _ = q right * ((∑' left,
                if f left = g right then p left else 0) *
                  (generalFiberMass p f (g right))⁻¹) := by
              rw [ENNReal.tsum_mul_right]
    _ = q right * (generalFiberMass q g (g right) *
        (generalFiberMass q g (g right))⁻¹) := by
      have hmass : generalFiberMass p f (g right) =
          generalFiberMass q g (g right) :=
        (generalFiberMass_eq_map_apply p f (g right)).trans
          ((by rw [hmap]) : p.map f (g right) = q.map g (g right)) |>.trans
            (generalFiberMass_eq_map_apply q g (g right)).symm
      rw [show (∑' left, if f left = g right then p left else 0) =
          generalFiberMass p f (g right) from rfl, hmass]
    _ = q right := by
      by_cases hright : q right = 0
      · simp [hright]
      · rw [ENNReal.mul_inv_cancel
          (generalFiberMass_ne_zero_of_apply_ne_zero q g right hright)
          (generalFiberMass_ne_top q g (g right)), mul_one]

set_option maxHeartbeats 1600000 in
theorem generalFiberCouplingWeight_sum_eq_one
    (p : PMF α) (q : PMF β) (f : α → γ) (g : β → γ)
    (hmap : p.map f = q.map g) :
    ∑' pair, generalFiberCouplingWeight p q f g pair = 1 := by
  calc
    (∑' pair : α × β, generalFiberCouplingWeight p q f g pair) =
        ∑' left, ∑' right,
          generalFiberCouplingWeight p q f g (left, right) :=
      by
        rw [← ENNReal.tsum_prod]
    _ = ∑' left, p left := by
      simp_rw [generalFiberCouplingWeight_sum_right p q f g hmap]
    _ = 1 := p.tsum_coe

noncomputable def generalFiberCoupling
    (p : PMF α) (q : PMF β) (f : α → γ) (g : β → γ)
    (hmap : p.map f = q.map g) : PMF (α × β) :=
  PMF.normalize (generalFiberCouplingWeight p q f g)
    (by rw [generalFiberCouplingWeight_sum_eq_one p q f g hmap]; exact one_ne_zero)
    (by rw [generalFiberCouplingWeight_sum_eq_one p q f g hmap]; exact one_ne_top)

@[simp]
theorem generalFiberCoupling_apply
    (p : PMF α) (q : PMF β) (f : α → γ) (g : β → γ)
    (hmap : p.map f = q.map g) (pair : α × β) :
    generalFiberCoupling p q f g hmap pair =
      generalFiberCouplingWeight p q f g pair := by
  unfold generalFiberCoupling
  rw [PMF.normalize_apply,
    generalFiberCouplingWeight_sum_eq_one p q f g hmap]
  simp

theorem generalFiberCoupling_isCoupling
    (p : PMF α) (q : PMF β) (f : α → γ) (g : β → γ)
    (hmap : p.map f = q.map g) :
    (generalFiberCoupling p q f g hmap).map Prod.fst = p ∧
      (generalFiberCoupling p q f g hmap).map Prod.snd = q := by
  classical
  constructor
  · ext left
    rw [PMF.map_apply]
    change (∑' pair : α × β,
      (fun candidate right => if left = candidate then
        generalFiberCoupling p q f g hmap (candidate, right) else 0)
          pair.1 pair.2) = p left
    calc
      (∑' pair : α × β,
          (fun candidate right => if left = candidate then
            generalFiberCoupling p q f g hmap (candidate, right) else 0)
              pair.1 pair.2) =
        ∑' candidate, ∑' right,
          if left = candidate then
            generalFiberCoupling p q f g hmap (candidate, right) else 0 := by
          rw [← ENNReal.tsum_prod]
      _ = (∑' candidate, ∑' right,
          if left = candidate then
            generalFiberCouplingWeight p q f g (candidate, right) else 0) := by
          simp only [generalFiberCoupling_apply]
      _ =
        ∑' right, generalFiberCouplingWeight p q f g (left, right) := by
          calc
            (∑' candidate, ∑' right,
                if left = candidate then
                  generalFiberCouplingWeight p q f g (candidate, right) else 0) =
              ∑' candidate, if candidate = left then
                (∑' right,
                  generalFiberCouplingWeight p q f g (candidate, right)) else 0 := by
                    apply tsum_congr
                    intro candidate
                    by_cases heq : candidate = left
                    · subst candidate
                      simp
                    · simp [heq, Ne.symm heq]
            _ = ∑' right,
                generalFiberCouplingWeight p q f g (left, right) :=
              tsum_ite_eq left _
      _ = p left := generalFiberCouplingWeight_sum_right p q f g hmap left
  · ext right
    rw [PMF.map_apply]
    change (∑' pair : α × β,
      (fun left candidate => if right = candidate then
        generalFiberCoupling p q f g hmap (left, candidate) else 0)
          pair.1 pair.2) = q right
    calc
      (∑' pair : α × β,
          (fun left candidate => if right = candidate then
            generalFiberCoupling p q f g hmap (left, candidate) else 0)
              pair.1 pair.2) =
        ∑' left, ∑' candidate,
          if right = candidate then
            generalFiberCoupling p q f g hmap (left, candidate) else 0 := by
          rw [← ENNReal.tsum_prod]
      _ = (∑' left, ∑' candidate,
          if right = candidate then
            generalFiberCouplingWeight p q f g (left, candidate) else 0) := by
          simp only [generalFiberCoupling_apply]
      _ =
        ∑' left, generalFiberCouplingWeight p q f g (left, right) := by
          apply tsum_congr
          intro left
          convert tsum_ite_eq right
            (fun candidate => generalFiberCouplingWeight p q f g (left, candidate))
            using 1
          apply tsum_congr
          intro candidate
          by_cases heq : candidate = right
          · simp [heq]
          · simp [heq, Ne.symm heq]
      _ = q right := generalFiberCouplingWeight_sum_left p q f g hmap right

theorem generalFiberCoupling_support
    (p : PMF α) (q : PMF β) (f : α → γ) (g : β → γ)
    (hmap : p.map f = q.map g) {pair : α × β}
    (hpair : pair ∈ (generalFiberCoupling p q f g hmap).support) :
    f pair.1 = g pair.2 := by
  have hweight := (PMF.mem_support_iff _ _).mp hpair
  rw [generalFiberCoupling_apply] at hweight
  unfold generalFiberCouplingWeight at hweight
  split at hweight
  · assumption
  · exact (hweight rfl).elim

end GeneralFiberCoupling

/-- A pair in the support of a mass function has each coordinate in the support of the
corresponding marginal. -/
theorem PMF.fst_mem_support_map {α β : Type} {c : PMF (α × β)} {pair : α × β}
    (hpair : pair ∈ c.support) : pair.1 ∈ (c.map Prod.fst).support :=
  (PMF.mem_support_map_iff _ _ _).2 ⟨pair, hpair, rfl⟩

theorem PMF.snd_mem_support_map {α β : Type} {c : PMF (α × β)} {pair : α × β}
    (hpair : pair ∈ c.support) : pair.2 ∈ (c.map Prod.snd).support :=
  (PMF.mem_support_map_iff _ _ _).2 ⟨pair, hpair, rfl⟩

section GeneralRelTriple

open MeasureTheory

instance finiteRangeOfUniform {ι : Type} {spec : OracleSpec ι}
    [OracleSpec.UniformAnswerMeasure spec] (t : spec.Domain) : Finite (spec.Range t) :=
  OracleSpec.UniformAnswerMeasure.finite_range t

/-- The output distribution of an oracle computation with finite answers, as a mass function:
each output's mass is the probability of drawing it. -/
noncomputable def outputPMF {α ι : Type} {spec : OracleSpec ι}
    [OracleSpec.UniformAnswerMeasure spec] (oa : OracleComp spec α) : PMF α :=
  ⟨fun x => Pr{let y ← oa}[y = x], by
    exact ENNReal.summable.hasSum_iff.mpr (OracleComp.tsum_prEvent_eq_one oa)⟩

variable {ι ι₁ ι₂ : Type} {spec : OracleSpec ι} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  [OracleSpec.UniformAnswerMeasure spec]
  [OracleSpec.UniformAnswerMeasure spec₁] [OracleSpec.UniformAnswerMeasure spec₂]
  {α β γ : Type}

theorem outputPMF_apply (oa : OracleComp spec α) (x : α) :
    outputPMF oa x = Pr{let y ← oa}[y = x] := rfl

theorem outputPMF_toMeasure (oa : OracleComp spec α) :
    letI : MeasurableSpace α := ⊤
    (outputPMF oa).toMeasure = 𝒟[oa] := by
  let : MeasurableSpace α := ⊤
  classical
  ext s hs
  rw [PMF.toMeasure_apply _ hs]
  change _ = 𝒟[oa] {x | x ∈ s}
  rw [← prEvent_eq_evalDist_of_discrete, OracleComp.prEvent_eq_tsum_ite]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ s <;> simp [hx, outputPMF_apply]

theorem outputPMF_map (oa : OracleComp spec α) (f : α → β) :
    (outputPMF oa).map f = outputPMF (f <$> oa) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (hf := Measurable.of_discrete), outputPMF_toMeasure, outputPMF_toMeasure,
    evalDist_map_of_discrete]

theorem outputPMF_congr {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α} (h : oa =ᵈ ob) :
    outputPMF oa = outputPMF ob :=
  PMF.ext fun x => h.prEvent_eq (· = x)

theorem mem_support_of_mem_support_outputPMF {oa : OracleComp spec α} {x : α}
    (hx : x ∈ (outputPMF oa).support) : x ∈ support oa :=
  (OracleComp.mem_support_iff_prEvent_ne_zero oa x).2 ((PMF.mem_support_iff _ _).1 hx)

/-- A mass function on pairs with the two output distributions as marginals, concentrated on a
relation, gives a relational triple. -/
theorem relTriple_of_pmf (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    {R : α → β → Prop} (c : PMF (α × β))
    (hfst : c.map Prod.fst = outputPMF oa) (hsnd : c.map Prod.snd = outputPMF ob)
    (hR : ∀ pair ∈ c.support, R pair.1 pair.2) :
    RelTriple oa ob R := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  rw [relTriple_iff_relWP, relWP_iff_couplingPost]
  refine ⟨⟨c.toMeasure, ⟨?_, ?_⟩⟩, ?_⟩
  · rw [Measure.fst, PMF.toMeasure_map (hf := measurable_fst), hfst, outputPMF_toMeasure]
  · rw [Measure.snd, PMF.toMeasure_map (hf := measurable_snd), hsnd, outputPMF_toMeasure]
  · rw [ae_iff, PMF.toMeasure_apply_eq_toOuterMeasure, PMF.toOuterMeasure_apply_eq_zero_iff]
    exact Set.disjoint_left.mpr fun pair hpair hnot => hnot (hR pair hpair)

/-- A relational triple between oracle computations with finite answers has a coupling mass
function concentrated on its relation. -/
theorem exists_pmf_of_relTriple {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R : α → β → Prop} (h : RelTriple oa ob R) :
    ∃ c : PMF (α × β), c.map Prod.fst = outputPMF oa ∧ c.map Prod.snd = outputPMF ob ∧
      ∀ pair ∈ c.support, R pair.1 pair.2 := by
  classical
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  rw [relTriple_iff_relWP, relWP_iff_couplingPost] at h
  obtain ⟨cm, hR⟩ := h
  have hprob : IsProbabilityMeasure cm.joint := by
    constructor
    rw [cm.isCoupling.joint_apply_univ_eq_left, ← prEvent_true_eq_evalDist_apply_univ]
    exact OracleComp.prEvent_true_eq_one oa
  let F : Finset (α × β) :=
    (OracleComp.support_finite oa).toFinset ×ˢ (OracleComp.support_finite ob).toFinset
  have hF : cm.joint (↑F)ᶜ = 0 := by
    refine measure_mono_null (fun pair hpair => ?_)
      (ae_iff.mp (OracleComp.ProgramLogic.Relational.ae_mem_support_prod cm))
    simpa [F] using hpair
  have hw0 : ∀ pair ∉ F, cm.joint {pair} = 0 := fun pair hpair =>
    measure_mono_null (Set.singleton_subset_iff.mpr hpair) hF
  have hsum : ∑' pair, cm.joint {pair} = 1 := by
    rw [tsum_eq_sum (s := F) hw0]
    exact Measure.sum_apply_singleton_eq_one hF
  let c : PMF (α × β) := ⟨fun pair => cm.joint {pair}, ENNReal.summable.hasSum_iff.mpr hsum⟩
  have hc : c.toMeasure = cm.joint := by
    refine Measure.ext_of_compl_eq_zero (F := F) ?_ hF fun pair _ =>
      PMF.toMeasure_apply_singleton c pair (measurableSet_singleton pair)
    rw [PMF.toMeasure_apply_eq_toOuterMeasure, PMF.toOuterMeasure_apply_eq_zero_iff]
    exact Set.disjoint_left.mpr fun pair hpair hpairF =>
      (PMF.mem_support_iff _ _).1 hpair (hw0 pair hpairF)
  refine ⟨c, ?_, ?_, ?_⟩
  · apply PMF.toMeasure_injective
    rw [← PMF.toMeasure_map (hf := measurable_fst), hc, outputPMF_toMeasure]
    exact cm.isCoupling.fst_eq
  · apply PMF.toMeasure_injective
    rw [← PMF.toMeasure_map (hf := measurable_snd), hc, outputPMF_toMeasure]
    exact cm.isCoupling.snd_eq
  · intro pair hpair
    by_contra hnot
    exact (PMF.mem_support_iff _ _).1 hpair
      (measure_mono_null (Set.singleton_subset_iff.mpr hnot) (ae_iff.mp hR))

theorem relTriple_of_evalDist_map_eq_general [DecidableEq γ]
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (f : α → γ) (g : β → γ)
    (hmap : (f <$> oa) =ᵈ (g <$> ob)) :
    RelTriple oa ob (fun left right => f left = g right) := by
  have hPMFMap : (outputPMF oa).map f = (outputPMF ob).map g := by
    rw [outputPMF_map, outputPMF_map, outputPMF_congr hmap]
  obtain ⟨hfst, hsnd⟩ := generalFiberCoupling_isCoupling _ _ f g hPMFMap
  exact relTriple_of_pmf oa ob _ hfst hsnd fun pair hpair =>
    generalFiberCoupling_support _ _ f g hPMFMap hpair

theorem relTriple_of_evalDist_map_eq_with_support_general [DecidableEq γ]
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (f : α → γ) (g : β → γ)
    (hmap : (f <$> oa) =ᵈ (g <$> ob)) :
    RelTriple oa ob (fun left right =>
      f left = g right ∧ left ∈ support oa ∧ right ∈ support ob) := by
  have hPMFMap : (outputPMF oa).map f = (outputPMF ob).map g := by
    rw [outputPMF_map, outputPMF_map, outputPMF_congr hmap]
  obtain ⟨hfst, hsnd⟩ := generalFiberCoupling_isCoupling _ _ f g hPMFMap
  refine relTriple_of_pmf oa ob _ hfst hsnd fun pair hpair =>
    ⟨generalFiberCoupling_support _ _ f g hPMFMap hpair, ?_, ?_⟩
  · exact mem_support_of_mem_support_outputPMF (hfst ▸ PMF.fst_mem_support_map hpair)
  · exact mem_support_of_mem_support_outputPMF (hsnd ▸ PMF.snd_mem_support_map hpair)

theorem relTriple_trans_exists
    {ι₃ : Type} {spec₃ : OracleSpec ι₃} [OracleSpec.UniformAnswerMeasure spec₃]
    {δ : Type} {oc : OracleComp spec₃ δ}
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R : α → β → Prop} {S : β → δ → Prop}
    (hab : RelTriple oa ob R) (hbc : RelTriple ob oc S) :
    RelTriple oa oc (fun a c => ∃ b, R a b ∧ S b c) := by
  classical
  obtain ⟨cab, hab₁, hab₂, hR⟩ := exists_pmf_of_relTriple hab
  obtain ⟨cbc, hbc₁, hbc₂, hS⟩ := exists_pmf_of_relTriple hbc
  have hmiddle : cab.map Prod.snd = cbc.map Prod.fst := hab₂.trans hbc₁.symm
  let d := generalFiberCoupling cab cbc Prod.snd Prod.fst hmiddle
  obtain ⟨hd₁, hd₂⟩ := generalFiberCoupling_isCoupling cab cbc Prod.snd Prod.fst hmiddle
  let project : (α × β) × (β × δ) → α × δ := fun pair => (pair.1.1, pair.2.2)
  refine relTriple_of_pmf oa oc (d.map project) ?_ ?_ ?_
  · rw [PMF.map_comp, show Prod.fst ∘ project = Prod.fst ∘ Prod.fst from rfl,
      ← PMF.map_comp, hd₁, hab₁]
  · rw [PMF.map_comp, show Prod.snd ∘ project = Prod.snd ∘ Prod.snd from rfl,
      ← PMF.map_comp, hd₂, hbc₂]
  · intro pair hpair
    obtain ⟨z, hz, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hpair
    have heq : z.1.2 = z.2.1 := generalFiberCoupling_support cab cbc _ _ hmiddle hz
    have hz₁ : z.1 ∈ cab.support := hd₁ ▸ PMF.fst_mem_support_map hz
    have hz₂ : z.2 ∈ cbc.support := hd₂ ▸ PMF.snd_mem_support_map hz
    exact ⟨z.1.2, hR z.1 hz₁, heq ▸ hS z.2 hz₂⟩

end GeneralRelTriple

end XmssSecurity
